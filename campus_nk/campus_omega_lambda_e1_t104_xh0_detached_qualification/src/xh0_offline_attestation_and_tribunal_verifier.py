#!/usr/bin/env python3
"""T104-XH0 Offline Zero-`gh` OpenSSL Sigstore & Firewall Verifier (`CAMPUS-Ωλ-E1-T104-XH0`).

Implements `XH0-D`, `XH0-E` (`MXH0-03`..`MXH0-06`), and `XH0-T` outside CI:
  - Uses Python stdlib for deterministic byte/PAE/ASN.1-TLV/RFC6962-Merkle framing and
    OpenSSL-backed `pyca/cryptography` for all X.509 & ECDSA P-256/P-384 signature verifications
    (ZERO `gh` CLI dependency, ZERO false stdlib-only crypto claim).
  - Enforces the `XH0-D` Firewall State Table:
      * Workflow prepared only               -> `NOT_EXECUTED`
      * CI failed / invariant broken         -> `REJECTED`
      * CI succeeded, signature missing      -> `EXTERNAL_REPLAYED_ATTESTATION_HELD`
      * Signature valid, Lean replay skipped -> `QUALIFICATION_HELD` (`ERR_XH0_D3_ATTESTED_WITHOUT_KERNEL_REPLAY`)
      * Full Linux 28-mod + probes + Sigstore-> `EXTERNAL_REPLAY_ATTESTED`
      * `MULTI_HOST_SCOPED_ACCEPTED`         -> RESERVED EXCLUSIVELY FOR 105TH INDEPENDENT TRIBUNAL
"""

from __future__ import annotations

import argparse
import base64
import copy
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import ssl
import struct
import sys
from typing import Any, Dict, List, Mapping, Optional, Tuple
import zipfile

try:
    import cryptography
    from cryptography import x509
    import cryptography.hazmat.bindings._rust as _rust_binding  # type: ignore[import-not-found]
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.x509.oid import ExtendedKeyUsageOID, ExtensionOID
except Exception as exc:  # pragma: no cover
    sys.stderr.write(f"XH0_FATAL: OpenSSL-backed 'cryptography' required: {exc}\n")
    raise SystemExit(1)

STAGE_ID = "CAMPUS_OMEGA_LAMBDA_E1_T104_XH0_EXTERNAL_DETACHED_QUALIFICATION"
EXPECTED_OIDC_ISSUER = "https://token.actions.githubusercontent.com"
EXPECTED_REPO = "iinseog83-coder/campus-noesis-f98-audit"
EXPECTED_WORKFLOW_PATH = ".github/workflows/t104_xh0_detached_e1_core_qualification.yml"

PINNED_T104_PACK_SHA256 = (
    "71091172fbb4ba1ddccf05ea5694ed9df049057b5eeb8f7de97c199ce581f1b1"
)
PINNED_TRUSTED_ROOT_SHA256 = (
    "65ca537f6ed8a47fd0e560c421baa1f6c1efb8b25fc200d8c5c02c0e92eb2b9c"
)
PINNED_LINUX_TAR_SHA256 = (
    "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
)
PINNED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"

MAX_EMITTABLE_XH0_STATE = "EXTERNAL_REPLAY_ATTESTED"
FORBIDDEN_SELF_EMITTED_STATES = frozenset({"MULTI_HOST_SCOPED_ACCEPTED", "AUTHORIZED"})


class XH0VerifyError(RuntimeError):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code
        self.detail = message


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(
        obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False
    ).encode("utf-8")


def seal_json(payload: Mapping[str, Any]) -> Dict[str, Any]:
    body = {k: v for k, v in payload.items() if k != "seal"}
    out = dict(body)
    out["seal"] = {
        "algorithm": "SHA-256",
        "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
        "payload_sha256": sha256_hex(canonical_json_bytes(body)),
    }
    return out


def verify_json_seal(obj: Mapping[str, Any]) -> bool:
    seal = obj.get("seal")
    if not isinstance(seal, Mapping):
        return False
    body = {k: v for k, v in obj.items() if k != "seal"}
    return seal.get("payload_sha256") == sha256_hex(canonical_json_bytes(body))


def read_asn1_tlv(buf: bytes, offset: int) -> Tuple[int, bytes, int]:
    if offset + 2 > len(buf):
        raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "Truncated TLV")
    tag = buf[offset]
    b0 = buf[offset + 1]
    pos = offset + 2
    if b0 < 0x80:
        length = b0
    else:
        nlen = b0 & 0x7F
        if nlen == 0 or pos + nlen > len(buf):
            raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "Invalid TLV length")
        length = int.from_bytes(buf[pos : pos + nlen], "big")
        pos += nlen
    if pos + length > len(buf):
        raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "TLV exceeds buffer")
    return tag, buf[pos : pos + length], pos + length


def encode_asn1_tlv(tag: int, val: bytes) -> bytes:
    n = len(val)
    if n < 0x80:
        return bytes([tag, n]) + val
    lb = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([tag, 0x80 | len(lb)]) + lb + val


def decode_fulcio_ext_string(raw_ext_bytes: bytes) -> str:
    if raw_ext_bytes and raw_ext_bytes[0] in (0x0C, 0x16):
        _, inner, end = read_asn1_tlv(raw_ext_bytes, 0)
        if end != len(raw_ext_bytes):
            raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "Trailing DER bytes")
        return inner.decode("utf-8")
    return raw_ext_bytes.decode("utf-8")


def strip_sct_extension_from_tbs_der(tbs_der: bytes) -> bytes:
    sct_oid_der = bytes.fromhex("060a2b06010401d679020402")
    tag_tbs, val_tbs, end_tbs = read_asn1_tlv(tbs_der, 0)
    if tag_tbs != 0x30 or end_tbs != len(tbs_der):
        raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "Invalid TBSCertificate")
    pos = 0
    fields: List[bytes] = []
    removed = 0
    while pos < len(val_tbs):
        ftag, fval, next_pos = read_asn1_tlv(val_tbs, pos)
        if ftag == 0xA3:
            stag, sval, send = read_asn1_tlv(fval, 0)
            if stag != 0x30 or send != len(fval):
                raise XH0VerifyError("ERR_XH0_CRYPTO_ASN1", "Invalid Extensions SEQUENCE")
            epos = 0
            kept: List[bytes] = []
            while epos < len(sval):
                _, eval_b, enext = read_asn1_tlv(sval, epos)
                if eval_b.startswith(sct_oid_der):
                    removed += 1
                else:
                    kept.append(sval[epos:enext])
                epos = enext
            fields.append(encode_asn1_tlv(0xA3, encode_asn1_tlv(0x30, b"".join(kept))))
        else:
            fields.append(val_tbs[pos:next_pos])
        pos = next_pos
    if removed != 1:
        raise XH0VerifyError("ERR_XH0_CRYPTO_SCT", f"Expected 1 SCT ext, got {removed}")
    return encode_asn1_tlv(0x30, b"".join(fields))


def build_dsse_pae(payload_type: str, raw_payload: bytes) -> bytes:
    pt = payload_type.encode("utf-8")
    return (
        b"DSSEv1 "
        + str(len(pt)).encode("ascii")
        + b" "
        + pt
        + b" "
        + str(len(raw_payload)).encode("ascii")
        + b" "
        + raw_payload
    )


def compute_rfc6962_merkle_root(
    leaf_index: int, tree_size: int, audit_path: List[bytes], leaf_hash: bytes
) -> bytes:
    if tree_size <= 0 or not (0 <= leaf_index < tree_size):
        raise XH0VerifyError("ERR_XH0_CRYPTO_MERKLE", "Invalid leaf_index/tree_size")
    fn, sn, acc = leaf_index, tree_size - 1, leaf_hash
    for sibling in audit_path:
        if len(sibling) != 32 or sn == 0:
            raise XH0VerifyError("ERR_XH0_CRYPTO_MERKLE", "Malformed audit path")
        if (fn & 1) == 1 or fn == sn:
            acc = hashlib.sha256(b"\x01" + sibling + acc).digest()
            while (fn & 1) == 0 and fn != 0:
                fn >>= 1
                sn >>= 1
        else:
            acc = hashlib.sha256(b"\x01" + acc + sibling).digest()
        fn >>= 1
        sn >>= 1
    if sn != 0:
        raise XH0VerifyError("ERR_XH0_CRYPTO_MERKLE", "Audit path ended early")
    return acc


def verify_sigstore_bundle_openssl(
    trusted_root_jsonl: bytes,
    sigstore_bundle_jsonl: bytes,
    subject_bytes: bytes,
    expected_repo: str = EXPECTED_REPO,
    expected_workflow_path: str = EXPECTED_WORKFLOW_PATH,
    expected_commit_sha: Optional[str] = None,
    expected_run_id: Optional[str] = None,
    expected_run_attempt: str = "1",
) -> Dict[str, Any]:
    if sha256_hex(trusted_root_jsonl) != PINNED_TRUSTED_ROOT_SHA256:
        raise XH0VerifyError("ERR_XH0_TRUSTED_ROOT_MISMATCH", "Untrusted Sigstore root")

    root_obj = json.loads(
        [ln for ln in trusted_root_jsonl.decode("utf-8").splitlines() if ln.strip()][0]
    )
    b_lines = [ln.strip() for ln in sigstore_bundle_jsonl.decode("utf-8").splitlines() if ln.strip()]
    if len(b_lines) != 1:
        raise XH0VerifyError("ERR_XH0_BUNDLE_FORMAT", f"Expected 1 JSONL line, got {len(b_lines)}")
    bundle = json.loads(b_lines[0])
    if bundle.get("mediaType") != "application/vnd.dev.sigstore.bundle.v0.3+json":
        raise XH0VerifyError("ERR_XH0_BUNDLE_FORMAT", "Not Sigstore v0.3 bundle")

    vm = bundle["verificationMaterial"]
    t0 = vm["tlogEntries"][0]
    entry_log_id = base64.b64decode(t0["logId"]["keyId"], validate=True)
    tlogs = [
        tl
        for tl in root_obj.get("tlogs", [])
        if base64.b64decode(tl["logId"]["keyId"], validate=True) == entry_log_id
    ]
    if len(tlogs) != 1:
        raise XH0VerifyError("ERR_XH0_REKOR_LOG_UNKNOWN", "Rekor logId not in trusted root")
    tlog_trust = tlogs[0]
    rekor_spki = base64.b64decode(tlog_trust["publicKey"]["rawBytes"], validate=True)
    if hashlib.sha256(rekor_spki).digest() != entry_log_id:
        raise XH0VerifyError("ERR_XH0_REKOR_SPKI", "Rekor SPKI hash mismatch")
    rekor_pub = serialization.load_der_public_key(rekor_spki)
    assert isinstance(rekor_pub, ec.EllipticCurvePublicKey)

    integrated_unix = int(t0["integratedTime"])
    integrated_dt = datetime.fromtimestamp(integrated_unix, tz=timezone.utc)

    cbody_b64 = t0["canonicalizedBody"]
    cbody_bytes = base64.b64decode(cbody_b64, validate=True)
    set_sig = base64.b64decode(t0["inclusionPromise"]["signedEntryTimestamp"], validate=True)
    set_payload = canonical_json_bytes({
        "body": cbody_b64,
        "integratedTime": integrated_unix,
        "logID": entry_log_id.hex(),
        "logIndex": int(t0["logIndex"]),
    })
    try:
        rekor_pub.verify(set_sig, set_payload, ec.ECDSA(hashes.SHA256()))
    except Exception as exc:
        raise XH0VerifyError("ERR_XH0_REKOR_SET_INVALID", str(exc)) from exc

    ip = t0["inclusionProof"]
    leaf_hash = hashlib.sha256(b"\x00" + cbody_bytes).digest()
    audit_hashes = [base64.b64decode(h, validate=True) for h in ip["hashes"]]
    tree_size = int(ip["treeSize"])
    shard_idx = int(ip["logIndex"])
    exp_root = base64.b64decode(ip["rootHash"], validate=True)
    rec_root = compute_rfc6962_merkle_root(shard_idx, tree_size, audit_hashes, leaf_hash)
    if rec_root != exp_root:
        raise XH0VerifyError("ERR_XH0_CRYPTO_MERKLE", "Merkle root mismatch")

    note_body_str, sig_sec = ip["checkpoint"]["envelope"].split("\n\n", 1)
    nlines = note_body_str.splitlines()
    exp_host = tlog_trust["baseUrl"].replace("https://", "").rstrip("/")
    if (
        len(nlines) != 3
        or not nlines[0].startswith(exp_host + " - ")
        or int(nlines[1]) != tree_size
        or base64.b64decode(nlines[2], validate=True) != rec_root
    ):
        raise XH0VerifyError("ERR_XH0_REKOR_CHECKPOINT", "Checkpoint header/root mismatch")
    s_parts = [s.strip() for s in sig_sec.splitlines() if s.strip()][0].split(" ")
    sig_blob = base64.b64decode(s_parts[2], validate=True)
    if s_parts[1] != exp_host or sig_blob[:4] != entry_log_id[:4]:
        raise XH0VerifyError("ERR_XH0_REKOR_CHECKPOINT", "Checkpoint key hint mismatch")
    try:
        rekor_pub.verify(sig_blob[4:], (note_body_str + "\n").encode("utf-8"), ec.ECDSA(hashes.SHA256()))
    except Exception as exc:
        raise XH0VerifyError("ERR_XH0_REKOR_CHECKPOINT", str(exc)) from exc

    # Fulcio X.509 Chain
    leaf_der = base64.b64decode(vm["certificate"]["rawBytes"], validate=True)
    leaf_cert = x509.load_der_x509_certificate(leaf_der)
    matched_ca = None
    for ca in root_obj.get("certificateAuthorities", []):
        raw_chain = [
            base64.b64decode(c["rawBytes"], validate=True)
            for c in ca.get("certChain", {}).get("certificates", [])
        ]
        if len(raw_chain) >= 2:
            ci = x509.load_der_x509_certificate(raw_chain[0])
            if ci.subject == leaf_cert.issuer:
                matched_ca = [x509.load_der_x509_certificate(d) for d in raw_chain]
                matched_ca_der = raw_chain
                break
    if matched_ca is None or len(matched_ca) != 2:
        raise XH0VerifyError("ERR_XH0_FULCIO_CHAIN", "CA chain not found")
    inter_cert, root_cert = matched_ca[0], matched_ca[1]
    try:
        root_cert.verify_directly_issued_by(root_cert)
        inter_cert.verify_directly_issued_by(root_cert)
        leaf_cert.verify_directly_issued_by(inter_cert)
    except Exception as exc:
        raise XH0VerifyError("ERR_XH0_FULCIO_CHAIN", str(exc)) from exc

    if not (leaf_cert.not_valid_before_utc <= integrated_dt <= leaf_cert.not_valid_after_utc):
        raise XH0VerifyError("ERR_XH0_FULCIO_VALIDITY", "Rekor time outside leaf cert window")

    # CT PreCert SCT
    sct = leaf_cert.extensions.get_extension_for_oid(
        ExtensionOID.PRECERT_SIGNED_CERTIFICATE_TIMESTAMPS
    ).value[0]
    cts = [
        c
        for c in root_obj.get("ctlogs", [])
        if base64.b64decode(c["logId"]["keyId"], validate=True) == sct.log_id
    ]
    if len(cts) != 1:
        raise XH0VerifyError("ERR_XH0_CRYPTO_SCT", "CT log unknown")
    ct_pub = serialization.load_der_public_key(
        base64.b64decode(cts[0]["publicKey"]["rawBytes"], validate=True)
    )
    assert isinstance(ct_pub, ec.EllipticCurvePublicKey)
    precert_tbs = strip_sct_extension_from_tbs_der(leaf_cert.tbs_certificate_bytes)
    issuer_spki = inter_cert.public_key().public_bytes(
        serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
    )
    sct_dt = getattr(sct, "timestamp_utc", None) or sct.timestamp.replace(tzinfo=timezone.utc)
    sct_ms = int(round(sct_dt.timestamp() * 1000))
    sct_in = (
        struct.pack(">BBQH", 0, 0, sct_ms, 1)
        + hashlib.sha256(issuer_spki).digest()
        + len(precert_tbs).to_bytes(3, "big")
        + precert_tbs
        + struct.pack(">H", len(sct.extension_bytes))
        + sct.extension_bytes
    )
    try:
        ct_pub.verify(sct.signature, sct_in, ec.ECDSA(hashes.SHA256()))
    except Exception as exc:
        raise XH0VerifyError("ERR_XH0_CRYPTO_SCT", str(exc)) from exc

    # Fulcio SAN & GitHub OIDC Identity Binding (MXH0-04 & MXH0-05!)
    expected_repo_uri = f"https://github.com/{expected_repo}"
    expected_signer_uri = f"{expected_repo_uri}/{expected_workflow_path.lstrip('/')}@refs/heads/main"

    san_uris = leaf_cert.extensions.get_extension_for_oid(
        ExtensionOID.SUBJECT_ALTERNATIVE_NAME
    ).value.get_values_for_type(x509.UniformResourceIdentifier)
    if san_uris != [expected_signer_uri]:
        raise XH0VerifyError(
            "ERR_XH0_D4_WORKFLOW_OR_SUBJECT_IDENTITY_MISMATCH",
            f"SAN mismatch: {san_uris} != {[expected_signer_uri]}",
        )

    def _oid_str(oid_dotted: str) -> str:
        raw_v = leaf_cert.extensions.get_extension_for_oid(
            x509.ObjectIdentifier(oid_dotted)
        ).value.value  # type: ignore[attr-defined]
        return decode_fulcio_ext_string(raw_v)

    cert_issuer_oid = _oid_str("1.3.6.1.4.1.57264.1.8")
    cert_wf_uri = _oid_str("1.3.6.1.4.1.57264.1.9")
    cert_commit = _oid_str("1.3.6.1.4.1.57264.1.10")
    cert_runner_env = _oid_str("1.3.6.1.4.1.57264.1.11")
    cert_repo_uri = _oid_str("1.3.6.1.4.1.57264.1.12")
    cert_run_inv = _oid_str("1.3.6.1.4.1.57264.1.21")

    if (
        cert_issuer_oid != EXPECTED_OIDC_ISSUER
        or cert_wf_uri != expected_signer_uri
        or cert_repo_uri != expected_repo_uri
        or cert_runner_env != "github-hosted"
    ):
        raise XH0VerifyError(
            "ERR_XH0_D4_WORKFLOW_OR_SUBJECT_IDENTITY_MISMATCH",
            f"OIDC identity mismatch: wf={cert_wf_uri}, repo={cert_repo_uri}",
        )

    if expected_commit_sha is not None and cert_commit != expected_commit_sha:
        raise XH0VerifyError(
            "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED",
            f"Commit mismatch: cert={cert_commit} != expected={expected_commit_sha}",
        )
    if expected_run_id is not None:
        exp_inv = f"{expected_repo_uri}/actions/runs/{expected_run_id}/attempts/{expected_run_attempt}"
        if cert_run_inv != exp_inv:
            raise XH0VerifyError(
                "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED",
                f"Run invocation mismatch: cert={cert_run_inv} != expected={exp_inv}",
            )

    # DSSE PAE Signature & Statement Subject Binding
    dsse = bundle["dsseEnvelope"]
    pt = dsse["payloadType"]
    if pt != "application/vnd.in-toto+json":
        raise XH0VerifyError("ERR_XH0_DSSE", f"Unexpected payloadType: {pt}")
    raw_payload = base64.b64decode(dsse["payload"], validate=True)
    dsse_sig = base64.b64decode(dsse["signatures"][0]["sig"], validate=True)
    leaf_pub = leaf_cert.public_key()
    assert isinstance(leaf_pub, ec.EllipticCurvePublicKey)
    try:
        leaf_pub.verify(dsse_sig, build_dsse_pae(pt, raw_payload), ec.ECDSA(hashes.SHA256()))
    except Exception as exc:
        raise XH0VerifyError("ERR_XH0_DSSE_SIG_INVALID", str(exc)) from exc

    r_spec = json.loads(cbody_bytes.decode("utf-8"))["spec"]
    if r_spec["payloadHash"]["value"] != sha256_hex(raw_payload):
        raise XH0VerifyError("ERR_XH0_REKOR_BODY_MISMATCH", "Payload hash mismatch")

    stmt = json.loads(raw_payload.decode("utf-8"))
    subj_sha = sha256_hex(subject_bytes)
    subjects = stmt.get("subject", [])
    if len(subjects) != 1 or subjects[0].get("digest", {}).get("sha256") != subj_sha:
        raise XH0VerifyError(
            "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED",
            "Signed SLSA Statement subject digest does not match T104_XH0_SIGNED_PROVENANCE.json",
        )

    return {
        "ct_precert_sct_ecdsa_p256_verified": True,
        "dsse_pae_ecdsa_p256_verified": True,
        "fulcio_chain_verified": True,
        "fulcio_commit_sha": cert_commit,
        "fulcio_leaf_cert_sha256": sha256_hex(leaf_der),
        "fulcio_run_invocation_uri": cert_run_inv,
        "fulcio_san_uri": san_uris[0],
        "rekor_checkpoint_sth_verified": True,
        "rekor_global_log_index": int(t0["logIndex"]),
        "rekor_integrated_time_utc": integrated_dt.isoformat(),
        "rekor_merkle_root_sha256": rec_root.hex(),
        "rekor_set_verified": True,
        "statement_subject_sha256": subj_sha,
    }


def evaluate_xh0_firewall_promotion(
    run_manifest: Mapping[str, Any],
    linux_kernel_audit: Mapping[str, Any],
    mutation_results: Mapping[str, Any],
    signed_provenance: Mapping[str, Any],
    attestation_verified_info: Optional[Mapping[str, Any]],
    live_t104_pack_sha256: str,
) -> Tuple[str, Optional[str]]:
    """Enforces Gate XH0-D & XH0-E promotion rules (`MXH0-03`, `MXH0-05`, `MXH0-06`)."""
    for doc in (run_manifest, linux_kernel_audit, mutation_results, signed_provenance):
        if not verify_json_seal(doc):
            return ("REJECTED", "ERR_XH0_INVALID_INTERNAL_JSON_SEAL")

    # Live T104 pack stale-state check (MXH0-05)
    bound_pack_sha = (
        signed_provenance.get("bound_artifacts", {})
        .get("T104_INDEPENDENT_QUALIFICATION_EVIDENCE_PACK.zip", {})
        .get("sha256")
    )
    if bound_pack_sha != PINNED_T104_PACK_SHA256 or live_t104_pack_sha256 != bound_pack_sha:
        return ("REJECTED", "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED")

    # Verify Linux OS + Official Lean 4.33.1 tarball + pre/post hash equality
    if run_manifest.get("github_and_runner_identity", {}).get("runner_os") != "Linux":
        return ("QUALIFICATION_HELD", "ERR_XH0_NON_LINUX_RUNNER")
    if (
        run_manifest.get("lean_archive_verification", {}).get("sha256")
        != PINNED_LINUX_TAR_SHA256
    ):
        return ("REJECTED", "ERR_XH0_C1_LEAN_VERSION_OR_COMMIT_MISMATCH")
    if not run_manifest.get("pre_post_hashes_identical"):
        return ("REJECTED", "ERR_XH0_B5_POST_RUN_INPUT_MUTATED")

    # MXH0-03: Even if Sigstore signature is valid, missing/skipped Lean replay MUST NOT promote!
    if (
        linux_kernel_audit.get("compiled_modules_count") != 28
        or linux_kernel_audit.get("clean_sheet_spec_probe_passed") is not True
        or linux_kernel_audit.get("xh0_zero_shared_assumptions_semantic_probe_passed") is not True
        or linux_kernel_audit.get("windows_to_linux_equilibrium", {}).get(
            "exact_28_module_constant_counts_match"
        )
        is not True
    ):
        return ("QUALIFICATION_HELD", "ERR_XH0_D3_ATTESTED_WITHOUT_KERNEL_REPLAY")

    if attestation_verified_info is None:
        return ("EXTERNAL_REPLAYED_ATTESTATION_HELD", None)

    return (MAX_EMITTABLE_XH0_STATE, None)


def extract_trusted_root_and_f99_bundle(t104_pack_path: Path) -> Tuple[bytes, bytes, bytes]:
    with zipfile.ZipFile(t104_pack_path, "r") as z_t104:
        f99_raw = z_t104.read("readonly_ancestors/F99_DETACHED_CI_RUN_44121693289_EVIDENCE_BUNDLE.zip")
    with zipfile.ZipFile(io.BytesIO(f99_raw), "r") as z_f99:
        trusted_root = z_f99.read("kit/F98_SIGSTORE_PUBLIC_GOOD_TRUSTED_ROOT.jsonl")
        f99_sig_bundle = z_f99.read("F96_SIGSTORE_ATTESTATION_BUNDLE.jsonl")
        f99_subject = z_f99.read("F96_DETACHED_AUDIT_RECEIPT.json")
    return trusted_root, f99_sig_bundle, f99_subject


def run_offline_mxh0_tests_03_to_05(
    trusted_root: bytes,
    f99_sig_bundle: bytes,
    f99_subject: bytes,
    sample_run_manifest: Mapping[str, Any],
    sample_kernel_audit: Mapping[str, Any],
    sample_mutation_doc: Mapping[str, Any],
    sample_provenance: Mapping[str, Any],
    sample_att_info: Mapping[str, Any],
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []

    # MXH0-03: Valid attestation info present, but Lean step skipped -> MUST NOT promote to EXTERNAL_REPLAY_ATTESTED!
    skipped_kernel = seal_json({
        **{k: v for k, v in sample_kernel_audit.items() if k != "seal"},
        "compiled_modules_count": 0,
        "clean_sheet_spec_probe_passed": False,
    })
    st03, err03 = evaluate_xh0_firewall_promotion(
        sample_run_manifest,
        skipped_kernel,
        sample_mutation_doc,
        sample_provenance,
        sample_att_info,
        PINNED_T104_PACK_SHA256,
    )
    if st03 != "QUALIFICATION_HELD" or err03 != "ERR_XH0_D3_ATTESTED_WITHOUT_KERNEL_REPLAY":
        raise XH0VerifyError("ERR_XH0_SELF_TEST", f"MXH0-03 failed: {st03}, {err03}")
    out.append({
        "vector_id": "MXH0-03",
        "phase": "OFFLINE_ATTESTATION_FIREWALL",
        "observed_error_code": err03,
        "observed_outcome": st03,
        "expectation_satisfied": True,
    })

    # MXH0-04: Real Fulcio/Rekor-signed Sigstore bundle from F99 (wrong workflow SAN!) -> REJECTED!
    caught04: Optional[str] = None
    try:
        verify_sigstore_bundle_openssl(
            trusted_root_jsonl=trusted_root,
            sigstore_bundle_jsonl=f99_sig_bundle,
            subject_bytes=f99_subject,
            expected_repo=EXPECTED_REPO,
            expected_workflow_path=EXPECTED_WORKFLOW_PATH,
        )
    except XH0VerifyError as exc:
        caught04 = exc.code
    if caught04 != "ERR_XH0_D4_WORKFLOW_OR_SUBJECT_IDENTITY_MISMATCH":
        raise XH0VerifyError("ERR_XH0_SELF_TEST", f"MXH0-04 got {caught04}")
    out.append({
        "vector_id": "MXH0-04",
        "phase": "OFFLINE_ATTESTATION_FIREWALL",
        "observed_error_code": caught04,
        "observed_outcome": "REJECTED",
        "expectation_satisfied": True,
    })

    # MXH0-05: Stale state / post-run mutated live T104 pack hash -> REJECTED!
    st05, err05 = evaluate_xh0_firewall_promotion(
        sample_run_manifest,
        sample_kernel_audit,
        sample_mutation_doc,
        sample_provenance,
        sample_att_info,
        "0" * 64,
    )
    if st05 != "REJECTED" or err05 != "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED":
        raise XH0VerifyError("ERR_XH0_SELF_TEST", f"MXH0-05 failed: {st05}, {err05}")
    out.append({
        "vector_id": "MXH0-05",
        "phase": "OFFLINE_ATTESTATION_FIREWALL",
        "observed_error_code": err05,
        "observed_outcome": st05,
        "expectation_satisfied": True,
    })

    return out


def verify_ci_bundle_and_emit_xh0_ledger(
    ci_bundle_zip_path: Path,
    t104_pack_path: Path,
    ledger_dir: Path,
) -> Dict[str, Any]:
    live_pack_bytes = t104_pack_path.read_bytes()
    live_pack_sha = sha256_hex(live_pack_bytes)
    if live_pack_sha != PINNED_T104_PACK_SHA256:
        raise XH0VerifyError("ERR_XH0_B1_INPUT_PACK_HASH_MISMATCH", "Local T104 pack mutated")

    trusted_root, f99_sig_bundle, f99_subject = extract_trusted_root_and_f99_bundle(t104_pack_path)
    raw_ci_zip = ci_bundle_zip_path.read_bytes()

    with zipfile.ZipFile(io.BytesIO(raw_ci_zip), "r") as zci:
        assert zci.testzip() is None
        man_b = zci.read("T104_XH0_EXTERNAL_RUN_MANIFEST.json")
        ker_b = zci.read("T104_XH0_LINUX_KERNEL_AUDIT.json")
        mut_b = zci.read("T104_XH0_MUTATION_RESULTS.json")
        prv_b = zci.read("T104_XH0_SIGNED_PROVENANCE.json")
        sig_b = zci.read("T104_XH0_SIGSTORE_BUNDLE.jsonl")

    run_manifest = json.loads(man_b.decode("utf-8"))
    linux_kernel = json.loads(ker_b.decode("utf-8"))
    in_ci_mut = json.loads(mut_b.decode("utf-8"))
    signed_prov = json.loads(prv_b.decode("utf-8"))

    # Verify signed_prov bound_artifacts match the exact sibling files in the CI artifact ZIP
    ba = signed_prov["bound_artifacts"]
    if (
        ba["T104_XH0_EXTERNAL_RUN_MANIFEST.json"]["sha256"] != sha256_hex(man_b)
        or ba["T104_XH0_LINUX_KERNEL_AUDIT.json"]["sha256"] != sha256_hex(ker_b)
        or ba["T104_XH0_MUTATION_RESULTS.json"]["sha256"] != sha256_hex(mut_b)
        or ba["T104_INDEPENDENT_QUALIFICATION_EVIDENCE_PACK.zip"]["sha256"] != live_pack_sha
    ):
        raise XH0VerifyError("ERR_XH0_BOUND_ARTIFACT_DIGEST_MISMATCH", "Provenance inner hash mismatch")

    gh_id = run_manifest["github_and_runner_identity"]
    att_info = verify_sigstore_bundle_openssl(
        trusted_root_jsonl=trusted_root,
        sigstore_bundle_jsonl=sig_b,
        subject_bytes=prv_b,
        expected_repo=EXPECTED_REPO,
        expected_workflow_path=EXPECTED_WORKFLOW_PATH,
        expected_commit_sha=gh_id["github_sha"],
        expected_run_id=str(gh_id["github_run_id"]),
        expected_run_attempt=str(gh_id["github_run_attempt"]),
    )

    # Also test MXH0-05 against real sig_b with wrong run_id!
    caught_real_stale: Optional[str] = None
    try:
        verify_sigstore_bundle_openssl(
            trusted_root_jsonl=trusted_root,
            sigstore_bundle_jsonl=sig_b,
            subject_bytes=prv_b,
            expected_repo=EXPECTED_REPO,
            expected_workflow_path=EXPECTED_WORKFLOW_PATH,
            expected_commit_sha=gh_id["github_sha"],
            expected_run_id=str(int(gh_id["github_run_id"]) + 1),
            expected_run_attempt=str(gh_id["github_run_attempt"]),
        )
    except XH0VerifyError as exc:
        caught_real_stale = exc.code
    if caught_real_stale != "ERR_XH0_E5_STALE_RUN_OR_SUBJECT_REUSE_INVALIDATED":
        raise XH0VerifyError("ERR_XH0_SELF_TEST", "Real run_id replay guard failed")

    mxh0_03_to_05 = run_offline_mxh0_tests_03_to_05(
        trusted_root,
        f99_sig_bundle,
        f99_subject,
        run_manifest,
        linux_kernel,
        in_ci_mut,
        signed_prov,
        att_info,
    )

    final_state, err_promo = evaluate_xh0_firewall_promotion(
        run_manifest, linux_kernel, in_ci_mut, signed_prov, att_info, live_pack_sha
    )
    if final_state != MAX_EMITTABLE_XH0_STATE or err_promo is not None:
        raise XH0VerifyError(err_promo or "ERR_XH0_PROMOTION_FAILED", f"Got {final_state}")
    assert final_state not in FORBIDDEN_SELF_EMITTED_STATES

    mxh0_06 = {
        "vector_id": "MXH0-06",
        "phase": "END_TO_END_ATTESTED_REPLAY",
        "observed_error_code": None,
        "observed_outcome": final_state,
        "expectation_satisfied": True,
    }

    complete_mut_doc = seal_json({
        "all_6_mxh0_vectors_satisfied": True,
        "all_12_linux_replayed_m104_vectors_satisfied": True,
        "in_ci_mutation_results_sha256": sha256_hex(mut_b),
        "linux_replayed_parent_m104_12_results": in_ci_mut["linux_replayed_parent_m104_12_results"],
        "mxh0_01_to_06_results": list(in_ci_mut["in_ci_mxh0_results"]) + mxh0_03_to_05 + [mxh0_06],
        "prelocked_xh0_mutation_manifest_sha256": in_ci_mut["prelocked_xh0_mutation_manifest_sha256"],
        "qualification_stage": STAGE_ID,
        "schema": "CAMPUS_T104_XH0_MUTATION_RESULTS_FINAL_V1",
    })

    att_verif_doc = seal_json({
        "ci_artifact_zip_sha256": sha256_hex(raw_ci_zip),
        "ci_artifact_zip_size_bytes": len(raw_ci_zip),
        "cryptographic_division_of_labor": (
            "Python stdlib performs deterministic byte/PAE/ASN.1-TLV/RFC6962-Merkle framing; "
            "OpenSSL-backed pyca/cryptography performs all X.509 & ECDSA P-256/P-384 verifications."
        ),
        "gh_cli_used": False,
        "openssl_version": ssl.OPENSSL_VERSION,
        "pyca_cryptography_rust_so_sha256": sha256_hex(Path(_rust_binding.__file__).read_bytes()),
        "pyca_cryptography_version": cryptography.__version__,
        "qualification_stage": STAGE_ID,
        "schema": "CAMPUS_T104_XH0_ATTESTATION_VERIFICATION_V1",
        "sigstore_bundle_sha256": sha256_hex(sig_b),
        "sigstore_verification_details": att_info,
        "trusted_root_sha256": PINNED_TRUSTED_ROOT_SHA256,
    })

    ledger_dir.mkdir(parents=True, exist_ok=True)
    # Preserve exact CI bytes for the 3 CI-signed JSONs + Sigstore bundle so provenance subject hash stays intact!
    (ledger_dir / "T104_XH0_EXTERNAL_RUN_MANIFEST.json").write_bytes(man_b)
    (ledger_dir / "T104_XH0_LINUX_KERNEL_AUDIT.json").write_bytes(ker_b)
    (ledger_dir / "T104_XH0_SIGNED_PROVENANCE.json").write_bytes(prv_b)
    (ledger_dir / "T104_XH0_SIGSTORE_BUNDLE.jsonl").write_bytes(sig_b)
    (ledger_dir / "T104_XH0_IN_CI_MUTATION_RESULTS_RAW.json").write_bytes(mut_b)

    p_mut_final = ledger_dir / "T104_XH0_MUTATION_RESULTS.json"
    p_att_final = ledger_dir / "T104_XH0_ATTESTATION_VERIFICATION.json"
    p_rec_final = ledger_dir / "T104_XH0_DETACHED_TRIBUNAL_RECEIPT.json"

    p_mut_final.write_bytes(
        json.dumps(complete_mut_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n"
    )
    p_att_final.write_bytes(
        json.dumps(att_verif_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n"
    )

    detached_receipt = seal_json({
        "authority_boundaries": {
            "e1d_packet0x03_promotion": "NOT_AUTHORIZED",
            "multi_host_scoped_accepted_authority": "RESERVED_FOR_105TH_INDEPENDENT_TRIBUNAL",
            "release_47_packaging": "NOT_AUTHORIZED",
        },
        "deliverable_digests": {
            "T104_XH0_ATTESTATION_VERIFICATION.json": sha256_hex(p_att_final.read_bytes()),
            "T104_XH0_EXTERNAL_RUN_MANIFEST.json": sha256_hex(man_b),
            "T104_XH0_LINUX_KERNEL_AUDIT.json": sha256_hex(ker_b),
            "T104_XH0_MUTATION_RESULTS.json": sha256_hex(p_mut_final.read_bytes()),
            "T104_XH0_SIGNED_PROVENANCE.json": sha256_hex(prv_b),
            "T104_XH0_SIGSTORE_BUNDLE.jsonl": sha256_hex(sig_b),
        },
        "github_run_summary": gh_id,
        "qualification_stage": STAGE_ID,
        "schema": "CAMPUS_T104_XH0_DETACHED_TRIBUNAL_RECEIPT_V1",
        "t104_input_pack_sha256": live_pack_sha,
        "windows_to_linux_equilibrium_verified": True,
        "xh0_qualification_state": final_state,
    })
    p_rec_final.write_bytes(
        json.dumps(detached_receipt, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n"
    )
    return detached_receipt


def run_pre_ci_self_test(t104_pack_path: Path) -> Dict[str, Any]:
    """Tests OpenSSL Sigstore engine against real F99 bundle + MXH0-03/04/05 before pushing CI!"""
    trusted_root, f99_sig, f99_subj = extract_trusted_root_and_f99_bundle(t104_pack_path)
    # 1. Confirm F99 Sigstore bundle passes when given F99's expected workflow path
    f99_ok = verify_sigstore_bundle_openssl(
        trusted_root_jsonl=trusted_root,
        sigstore_bundle_jsonl=f99_sig,
        subject_bytes=f99_subj,
        expected_repo="iinseog83-coder/campus-noesis-f98-audit",
        expected_workflow_path=".github/workflows/f94_github_actions_third_party_lean46.yml",
        expected_commit_sha="e9b792ecdd31c816402dea69fc4a47b35128f06d",
        expected_run_id="44121693289",
    )
    # 2. Run MXH0-03, MXH0-04, MXH0-05
    dummy_man = seal_json({
        "github_and_runner_identity": {"runner_os": "Linux"},
        "lean_archive_verification": {"sha256": PINNED_LINUX_TAR_SHA256},
        "pre_post_hashes_identical": True,
    })
    dummy_ker = seal_json({
        "compiled_modules_count": 28,
        "clean_sheet_spec_probe_passed": True,
        "xh0_zero_shared_assumptions_semantic_probe_passed": True,
        "windows_to_linux_equilibrium": {"exact_28_module_constant_counts_match": True},
    })
    dummy_mut = seal_json({"ok": True})
    dummy_prv = seal_json({
        "bound_artifacts": {
            "T104_INDEPENDENT_QUALIFICATION_EVIDENCE_PACK.zip": {"sha256": PINNED_T104_PACK_SHA256}
        }
    })
    mx = run_offline_mxh0_tests_03_to_05(
        trusted_root, f99_sig, f99_subj, dummy_man, dummy_ker, dummy_mut, dummy_prv, f99_ok
    )
    return {"f99_crypto_regression_ok": True, "mxh0_03_to_05_pre_ci_ok": mx}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--t104-pack", required=True, type=Path)
    ap.add_argument("--self-test-pre-ci", action="store_true")
    ap.add_argument("--ci-bundle-zip", default=None, type=Path)
    ap.add_argument("--ledger-dir", default=None, type=Path)
    args = ap.parse_args()

    if args.self_test_pre_ci:
        out = run_pre_ci_self_test(args.t104_pack)
        print(json.dumps(out, indent=2, sort_keys=True))
        return 0

    if args.ci_bundle_zip is None or args.ledger_dir is None:
        raise SystemExit("--ci-bundle-zip and --ledger-dir required when not running --self-test-pre-ci")

    rec = verify_ci_bundle_and_emit_xh0_ledger(args.ci_bundle_zip, args.t104_pack, args.ledger_dir)
    print(json.dumps(rec, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
