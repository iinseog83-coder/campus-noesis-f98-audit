#!/usr/bin/env python3
"""Effectful Evidence & Cryptographic Observation Harness (`H_IO`) for `PCT0-XH0 v3` (`F-PCT0-XH0-06`).

Responsibilities:
  1. Reads the downloaded raw CI artifact ZIP (`pct0-xh0-detached-qualification-bundle.zip`),
     pinned `F98_SIGSTORE_PUBLIC_GOOD_TRUSTED_ROOT.jsonl`, frozen `PCT-S1/S2` ZIP, and
     real cross-workflow `P0-XH0` Sigstore bundle.
  2. Executes OpenSSL-backed X.509 / Fulcio SAN / OIDC OID / CT PreCert SCT / Rekor SET /
     RFC 6962 Merkle / Checkpoint STH / DSSE PAE verification, returning ONLY raw observation
     fields inside `CoreObservation` (never emitting `"PASS"` strings).
  3. Executes the 6 adversarial perturbations (`MXH0_PCT0_01`..`06`) inside isolated temporary
     directory copies (`tempfile.TemporaryDirectory`), verifying byte-exact non-mutation of the
     original CI bundle (`bundle_pre_sha256 == bundle_post_sha256`).
  4. Invokes the zero-I/O `pure_adjudicator.adjudicate_pct0_xh0_pure` morphism to obtain the
     deterministic 3-valued lattice decision (`FAIL < HELD_OR_UNKNOWN < PASS`), seals the
     append-only `PCT0_XH0_DETACHED_QUALIFICATION_RECEIPT.json`, and builds the single
     standalone Tribunal bundle `CAMPUS_PROOFSPACE_OMEGA_PCT0_XH0_COMPLETE_EVIDENCE_BUNDLE.zip`.
"""

from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import platform
import shutil
import ssl
import struct
import sys
import tempfile
from typing import Any, Dict, List, Mapping, Optional, Tuple
import zipfile

try:
    import cryptography
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.x509.oid import ExtensionOID

    CRYPTO_AVAILABLE = True
except Exception:  # pragma: no cover
    CRYPTO_AVAILABLE = False

THIS_DIR = Path(__file__).resolve().parent
if str(THIS_DIR) not in sys.path:
    sys.path.insert(0, str(THIS_DIR))

from pure_adjudicator import (  # noqa: E402
    AdjudicationDecision,
    AdversarialCaseObservation,
    CoreObservation,
    MutationSpanObservation,
    MutationSpanSpec,
    ObsBundle,
    PinnedSpec,
    VAL_PASS,
    adjudicate_pct0_xh0_pure,
)

STAGE_ID = "CAMPUS_PROOFSPACE_OMEGA_PCT0_XH0_EXTERNAL_MULTI_HOST_QUALIFICATION_V3"
EXPECTED_OIDC_ISSUER = "https://token.actions.githubusercontent.com"
EXPECTED_REPO = "iinseog83-coder/campus-noesis-f98-audit"
EXPECTED_REPO_URI = f"https://github.com/{EXPECTED_REPO}"
EXPECTED_WORKFLOW_PATH = ".github/workflows/pct0_xh0_detached_s1s2_qualification.yml"
EXPECTED_WORKFLOW_SAN_URI = f"{EXPECTED_REPO_URI}/{EXPECTED_WORKFLOW_PATH}@refs/heads/main"

PINNED_TRUSTED_ROOT_SHA256 = "65ca537f6ed8a47fd0e560c421baa1f6c1efb8b25fc200d8c5c02c0e92eb2b9c"
PINNED_S1S2_ZIP_SHA256 = "0700fd1cf3225b1b791d5d3dc35cc05ef925acf1ebc443bab8b73d5a4884025e"
PINNED_S1S2_ZIP_SIZE = 45265
PINNED_S1S2_ZIP_ENTRIES = 15


class SigstoreObsError(RuntimeError):
    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode("utf-8")


def read_asn1_tlv(buf: bytes, offset: int) -> Tuple[int, bytes, int]:
    if offset + 2 > len(buf):
        raise SigstoreObsError("ERR_ASN1", "Truncated TLV")
    tag = buf[offset]
    b0 = buf[offset + 1]
    pos = offset + 2
    if b0 < 0x80:
        length = b0
    else:
        nlen = b0 & 0x7F
        if nlen == 0 or pos + nlen > len(buf):
            raise SigstoreObsError("ERR_ASN1", "Invalid TLV length")
        length = int.from_bytes(buf[pos : pos + nlen], "big")
        pos += nlen
    if pos + length > len(buf):
        raise SigstoreObsError("ERR_ASN1", "TLV exceeds buffer")
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
            raise SigstoreObsError("ERR_ASN1", "Trailing DER bytes")
        return inner.decode("utf-8")
    return raw_ext_bytes.decode("utf-8")


def strip_sct_extension_from_tbs_der(tbs_der: bytes) -> bytes:
    sct_oid_der = bytes.fromhex("060a2b06010401d679020402")
    tag_tbs, val_tbs, end_tbs = read_asn1_tlv(tbs_der, 0)
    if tag_tbs != 0x30 or end_tbs != len(tbs_der):
        raise SigstoreObsError("ERR_ASN1", "Invalid TBSCertificate")
    pos = 0
    fields: List[bytes] = []
    removed = 0
    while pos < len(val_tbs):
        ftag, fval, next_pos = read_asn1_tlv(val_tbs, pos)
        if ftag == 0xA3:
            stag, sval, send = read_asn1_tlv(fval, 0)
            if stag != 0x30 or send != len(fval):
                raise SigstoreObsError("ERR_ASN1", "Invalid Extensions SEQUENCE")
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
        raise SigstoreObsError("ERR_SCT", f"Expected 1 SCT ext, got {removed}")
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
        raise SigstoreObsError("ERR_MERKLE", "Invalid leaf_index/tree_size")
    fn, sn, acc = leaf_index, tree_size - 1, leaf_hash
    for sibling in audit_path:
        if len(sibling) != 32 or sn == 0:
            raise SigstoreObsError("ERR_MERKLE", "Malformed audit path")
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
        raise SigstoreObsError("ERR_MERKLE", "Audit path ended early")
    return acc


def observe_sigstore_bundle_openssl(
    trusted_root_jsonl: bytes,
    sigstore_bundle_jsonl: bytes,
    subject_bytes: bytes,
) -> Dict[str, Any]:
    if not CRYPTO_AVAILABLE:
        return {"executed": False, "error_code": None}

    root_sha = sha256_hex(trusted_root_jsonl)
    subj_sha = sha256_hex(subject_bytes)
    try:
        root_obj = json.loads([ln for ln in trusted_root_jsonl.decode("utf-8").splitlines() if ln.strip()][0])
        b_lines = [ln.strip() for ln in sigstore_bundle_jsonl.decode("utf-8").splitlines() if ln.strip()]
        if len(b_lines) != 1:
            raise SigstoreObsError("ERR_BUNDLE_FORMAT", f"Expected 1 JSONL line, got {len(b_lines)}")
        bundle = json.loads(b_lines[0])
        if bundle.get("mediaType") != "application/vnd.dev.sigstore.bundle.v0.3+json":
            raise SigstoreObsError("ERR_BUNDLE_MEDIA_TYPE", str(bundle.get("mediaType")))

        vm = bundle["verificationMaterial"]
        t0 = vm["tlogEntries"][0]
        entry_log_id = base64.b64decode(t0["logId"]["keyId"], validate=True)
        tlogs = [
            tl
            for tl in root_obj.get("tlogs", [])
            if base64.b64decode(tl["logId"]["keyId"], validate=True) == entry_log_id
        ]
        if len(tlogs) != 1:
            raise SigstoreObsError("ERR_REKOR_LOG_UNKNOWN", "Rekor logId not in pinned root")
        tlog_trust = tlogs[0]
        rekor_spki = base64.b64decode(tlog_trust["publicKey"]["rawBytes"], validate=True)
        if hashlib.sha256(rekor_spki).digest() != entry_log_id:
            raise SigstoreObsError("ERR_REKOR_SPKI", "SPKI hash mismatch")
        rekor_pub = serialization.load_der_public_key(rekor_spki)
        assert isinstance(rekor_pub, ec.EllipticCurvePublicKey)

        integrated_unix = int(t0["integratedTime"])
        integrated_dt = datetime.fromtimestamp(integrated_unix, tz=timezone.utc)
        cbody_b64 = t0["canonicalizedBody"]
        cbody_bytes = base64.b64decode(cbody_b64, validate=True)
        set_sig = base64.b64decode(t0["inclusionPromise"]["signedEntryTimestamp"], validate=True)
        set_payload = canonical_json_bytes(
            {
                "body": cbody_b64,
                "integratedTime": integrated_unix,
                "logID": entry_log_id.hex(),
                "logIndex": int(t0["logIndex"]),
            }
        )
        rekor_pub.verify(set_sig, set_payload, ec.ECDSA(hashes.SHA256()))
        rekor_set_ok = True

        ip = t0["inclusionProof"]
        leaf_hash = hashlib.sha256(b"\x00" + cbody_bytes).digest()
        audit_hashes = [base64.b64decode(h, validate=True) for h in ip["hashes"]]
        tree_size = int(ip["treeSize"])
        shard_idx = int(ip["logIndex"])
        exp_root = base64.b64decode(ip["rootHash"], validate=True)
        rec_root = compute_rfc6962_merkle_root(shard_idx, tree_size, audit_hashes, leaf_hash)
        rekor_merkle_ok = rec_root == exp_root
        if not rekor_merkle_ok:
            raise SigstoreObsError("ERR_REKOR_MERKLE", "Merkle root mismatch")

        note_body_str, sig_sec = ip["checkpoint"]["envelope"].split("\n\n", 1)
        nlines = note_body_str.splitlines()
        exp_host = tlog_trust["baseUrl"].replace("https://", "").rstrip("/")
        if (
            len(nlines) != 3
            or not nlines[0].startswith(exp_host + " - ")
            or int(nlines[1]) != tree_size
            or base64.b64decode(nlines[2], validate=True) != rec_root
        ):
            raise SigstoreObsError("ERR_REKOR_CHECKPOINT", "Checkpoint header mismatch")
        s_parts = [s.strip() for s in sig_sec.splitlines() if s.strip()][0].split(" ")
        sig_blob = base64.b64decode(s_parts[2], validate=True)
        if s_parts[1] != exp_host or sig_blob[:4] != entry_log_id[:4]:
            raise SigstoreObsError("ERR_REKOR_CHECKPOINT_HINT", "Key hint mismatch")
        rekor_pub.verify(sig_blob[4:], (note_body_str + "\n").encode("utf-8"), ec.ECDSA(hashes.SHA256()))
        rekor_checkpoint_ok = True

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
                    break
        if matched_ca is None or len(matched_ca) != 2:
            raise SigstoreObsError("ERR_FULCIO_CHAIN", "Issuer CA not found")
        inter_cert, root_cert = matched_ca[0], matched_ca[1]
        root_cert.verify_directly_issued_by(root_cert)
        inter_cert.verify_directly_issued_by(root_cert)
        leaf_cert.verify_directly_issued_by(inter_cert)
        if not (leaf_cert.not_valid_before_utc <= integrated_dt <= leaf_cert.not_valid_after_utc):
            raise SigstoreObsError("ERR_FULCIO_WINDOW", "Integrated time outside cert window")
        fulcio_chain_ok = True

        sct = leaf_cert.extensions.get_extension_for_oid(
            ExtensionOID.PRECERT_SIGNED_CERTIFICATE_TIMESTAMPS
        ).value[0]
        cts = [
            c
            for c in root_obj.get("ctlogs", [])
            if base64.b64decode(c["logId"]["keyId"], validate=True) == sct.log_id
        ]
        if len(cts) != 1:
            raise SigstoreObsError("ERR_SCT_LOG", "Unknown CT log")
        ct_pub = serialization.load_der_public_key(base64.b64decode(cts[0]["publicKey"]["rawBytes"], validate=True))
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
        ct_pub.verify(sct.signature, sct_in, ec.ECDSA(hashes.SHA256()))
        ct_sct_ok = True

        san_uris = leaf_cert.extensions.get_extension_for_oid(
            ExtensionOID.SUBJECT_ALTERNATIVE_NAME
        ).value.get_values_for_type(x509.UniformResourceIdentifier)
        san_uri = san_uris[0] if len(san_uris) == 1 else ""

        def _oid_str(oid_dotted: str) -> str:
            raw_v = leaf_cert.extensions.get_extension_for_oid(
                x509.ObjectIdentifier(oid_dotted)
            ).value.value  # type: ignore[attr-defined]
            return decode_fulcio_ext_string(raw_v)

        cert_issuer = _oid_str("1.3.6.1.4.1.57264.1.8")
        cert_commit = _oid_str("1.3.6.1.4.1.57264.1.10")
        cert_env = _oid_str("1.3.6.1.4.1.57264.1.11")
        cert_repo = _oid_str("1.3.6.1.4.1.57264.1.12")
        cert_run_inv = _oid_str("1.3.6.1.4.1.57264.1.21")

        dsse = bundle["dsseEnvelope"]
        pt = dsse["payloadType"]
        if pt != "application/vnd.in-toto+json":
            raise SigstoreObsError("ERR_DSSE_TYPE", pt)
        raw_payload = base64.b64decode(dsse["payload"], validate=True)
        dsse_sig = base64.b64decode(dsse["signatures"][0]["sig"], validate=True)
        leaf_pub = leaf_cert.public_key()
        assert isinstance(leaf_pub, ec.EllipticCurvePublicKey)
        leaf_pub.verify(dsse_sig, build_dsse_pae(pt, raw_payload), ec.ECDSA(hashes.SHA256()))
        dsse_sig_ok = True

        r_spec = json.loads(cbody_bytes.decode("utf-8"))["spec"]
        if r_spec["payloadHash"]["value"] != sha256_hex(raw_payload):
            raise SigstoreObsError("ERR_REKOR_PAYLOAD_HASH", "Rekor payload hash mismatch")

        stmt = json.loads(raw_payload.decode("utf-8"))
        subjects = stmt.get("subject", [])
        stmt_subj_sha = subjects[0].get("digest", {}).get("sha256", "") if len(subjects) == 1 else ""

        return {
            "executed": True,
            "error_code": None,
            "trusted_root_sha256": root_sha,
            "provenance_subject_sha256": subj_sha,
            "dsse_statement_subject_sha256": stmt_subj_sha,
            "fulcio_chain_ok": fulcio_chain_ok,
            "fulcio_leaf_cert_sha256": sha256_hex(leaf_der),
            "fulcio_san_uri": san_uri,
            "fulcio_oidc_issuer": cert_issuer,
            "fulcio_repo_uri": cert_repo,
            "fulcio_runner_env": cert_env,
            "fulcio_commit_sha": cert_commit,
            "fulcio_run_invocation_uri": cert_run_inv,
            "ct_precert_sct_ok": ct_sct_ok,
            "rekor_set_ok": rekor_set_ok,
            "rekor_merkle_ok": rekor_merkle_ok,
            "rekor_checkpoint_ok": rekor_checkpoint_ok,
            "rekor_global_log_index": int(t0["logIndex"]),
            "rekor_integrated_time_utc": integrated_dt.isoformat(),
            "rekor_merkle_root_sha256": rec_root.hex(),
            "dsse_pae_sig_ok": dsse_sig_ok,
        }
    except SigstoreObsError as se:
        return {
            "executed": True,
            "error_code": se.code,
            "trusted_root_sha256": root_sha,
            "provenance_subject_sha256": subj_sha,
        }
    except Exception as exc:
        return {
            "executed": True,
            "error_code": f"ERR_CRYPTO_VERIFY:{type(exc).__name__}",
            "trusted_root_sha256": root_sha,
            "provenance_subject_sha256": subj_sha,
        }


def build_pinned_spec_from_frozen_s1s2(s1s2_zip_bytes: bytes) -> PinnedSpec:
    """Derives the immutable reference PinnedSpec from the frozen PCT-S1/S2 ZIP (`0700fd1c…`)."""
    if sha256_hex(s1s2_zip_bytes) != PINNED_S1S2_ZIP_SHA256 or len(s1s2_zip_bytes) != PINNED_S1S2_ZIP_SIZE:
        raise RuntimeError("Frozen PCT-S1/S2 reference ZIP digest mismatch")

    with zipfile.ZipFile(io.BytesIO(s1s2_zip_bytes), "r") as zf:
        s1s2_rec = json.loads(zf.read("ledger/PCT0_S1S2_MINIMAL_FORMALIZATION_RECEIPT.json").decode("utf-8"))
        genh_bytes = zf.read("lean_pct0/ProofspaceOmegaPCT0/GenH.lean")
        ctrl_bytes = zf.read("lean_pct0/ProofspaceOmegaPCT0/ControlsAndCounterexamples.lean")
        auth_bytes = zf.read("lean_pct0/ProofspaceOmegaPCT0/AuthorityAndAdmission.lean")

    from pct0_xh0_linux_runner import COUNTERMODEL_PROBES, split_causal_prefix_span

    _, q0_m1, _ = split_causal_prefix_span(genh_bytes, None, "end ProofspaceOmegaPCT0.GenH")
    _, q0_m2, _ = split_causal_prefix_span(ctrl_bytes, "pct0_s1s2_dissip_transport", "end ProofspaceOmegaPCT0.Controls")
    _, q0_m3, _ = split_causal_prefix_span(ctrl_bytes, "pct0_s1s2_canonical_admissible", "end ProofspaceOmegaPCT0.Controls")
    _, q0_m4, _ = split_causal_prefix_span(auth_bytes, "f15_canonical_admissible_iff_three_gates", "end ProofspaceOmegaPCT0")

    lean_sha_map = tuple(sorted(s1s2_rec["self_contained_offline_audit"]["pct0_source_sha256"].items()))
    frozen_recs = tuple(
        sorted(
            (v["filename"], v["sha256"], int(v["size_bytes"]))
            for v in s1s2_rec["self_contained_offline_audit"]["embedded_frozen_receipts"].values()
        )
    )
    ax_map = tuple(
        sorted(
            (k, tuple(sorted(v)))
            for k, v in s1s2_rec["lean_cleanroom_audit"]["theorem_axiom_footprints"].items()
        )
    )

    mut_specs = (
        MutationSpanSpec(
            mut_id="M_PCT0_LEAN_01",
            expected_orig_s0_sha256=sha256_hex(genh_bytes),
            expected_q0_sha256=sha256_hex(q0_m1),
            expected_rfl_rhs_spec_sha256=sha256_hex(COUNTERMODEL_PROBES["M_PCT0_LEAN_01"][1].encode("utf-8")),
            target_span_start=79,
            target_span_end=98,
            expected_failure_class="OMEGA_UNSOLVED_LINEAR_GOAL",
        ),
        MutationSpanSpec(
            mut_id="M_PCT0_LEAN_02",
            expected_orig_s0_sha256=sha256_hex(ctrl_bytes),
            expected_q0_sha256=sha256_hex(q0_m2),
            expected_rfl_rhs_spec_sha256=sha256_hex(COUNTERMODEL_PROBES["M_PCT0_LEAN_02"][1].encode("utf-8")),
            target_span_start=79,
            target_span_end=98,
            expected_failure_class="OMEGA_UNSOLVED_LINEAR_GOAL",
        ),
        MutationSpanSpec(
            mut_id="M_PCT0_LEAN_03",
            expected_orig_s0_sha256=sha256_hex(ctrl_bytes),
            expected_q0_sha256=sha256_hex(q0_m3),
            expected_rfl_rhs_spec_sha256=sha256_hex(COUNTERMODEL_PROBES["M_PCT0_LEAN_03"][1].encode("utf-8")),
            target_span_start=230,
            target_span_end=267,
            expected_failure_class="DECIDABLE_SYNTHESIS_FAILURE",
        ),
        MutationSpanSpec(
            mut_id="M_PCT0_LEAN_04",
            expected_orig_s0_sha256=sha256_hex(auth_bytes),
            expected_q0_sha256=sha256_hex(q0_m4),
            expected_rfl_rhs_spec_sha256=sha256_hex(COUNTERMODEL_PROBES["M_PCT0_LEAN_04"][1].encode("utf-8")),
            target_span_start=171,
            target_span_end=186,
            expected_failure_class="DECIDE_EVALUATED_FALSE",
        ),
        MutationSpanSpec(
            mut_id="M_PCT0_LEAN_05",
            expected_orig_s0_sha256=sha256_hex(auth_bytes),
            expected_q0_sha256=sha256_hex(q0_m4),
            expected_rfl_rhs_spec_sha256=sha256_hex(COUNTERMODEL_PROBES["M_PCT0_LEAN_05"][1].encode("utf-8")),
            target_span_start=171,
            target_span_end=186,
            expected_failure_class="DECIDE_EVALUATED_FALSE",
        ),
    )

    return PinnedSpec(
        s1s2_zip_sha256=PINNED_S1S2_ZIP_SHA256,
        s1s2_zip_size=PINNED_S1S2_ZIP_SIZE,
        s1s2_zip_entries=PINNED_S1S2_ZIP_ENTRIES,
        expected_lean_sha256s=lean_sha_map,
        expected_frozen_receipts=frozen_recs,
        lean_linux_tar_sha256="890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235",
        lean_linux_tar_size=570405234,
        lean_commit="819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
        expected_module_names=(
            "ProofspaceOmegaPCT0.GenG",
            "ProofspaceOmegaPCT0.GenH",
            "ProofspaceOmegaPCT0.TransportCore",
            "ProofspaceOmegaPCT0.AuthorityAndAdmission",
            "ProofspaceOmegaPCT0.ControlsAndCounterexamples",
            "ProofspaceOmegaPCT0.PCT0AxiomAudit",
            "ProofspaceOmegaPCT0",
            "pct0_independent_clean_sheet_probe",
        ),
        zero_import_target_modules=(
            "ProofspaceOmegaPCT0.GenG",
            "ProofspaceOmegaPCT0.GenH",
            "pct0_independent_clean_sheet_probe",
        ),
        expected_smap_constants=585,
        expected_smap_theorems=208,
        expected_closure_g=1659,
        expected_closure_h=1681,
        expected_transport_consts=348,
        expected_axiom_footprints=ax_map,
        mutation_specs=mut_specs,
        trusted_root_sha256=PINNED_TRUSTED_ROOT_SHA256,
        expected_oidc_issuer=EXPECTED_OIDC_ISSUER,
        expected_repo_uri=EXPECTED_REPO_URI,
        expected_workflow_san_uri=EXPECTED_WORKFLOW_SAN_URI,
        expected_adv_ids=(
            ("MXH0_PCT0_01", 0),
            ("MXH0_PCT0_02", 3),
            ("MXH0_PCT0_03", 2),
            ("MXH0_PCT0_04", 5),
            ("MXH0_PCT0_05", 5),
            ("MXH0_PCT0_06", 5),
        ),
    )


def parse_ci_directory_to_core_obs(
    ci_dir: Path,
    trusted_root_bytes: bytes,
    expected_commit_override: Optional[str] = None,
) -> Tuple[CoreObservation, Dict[str, Any]]:
    g1 = json.loads((ci_dir / "G1_SOURCE_LINEAGE_MANIFEST.json").read_text(encoding="utf-8"))
    g2 = json.loads((ci_dir / "G2_LINUX_KERNEL_COMPILE_AND_SMAP.json").read_text(encoding="utf-8"))
    g3 = json.loads((ci_dir / "G3_TRANSDEPS_AND_AXIOM_AUDIT.json").read_text(encoding="utf-8"))
    g4 = json.loads((ci_dir / "G4_SEMANTIC_MUTATION_RAW_DIAGNOSTICS.json").read_text(encoding="utf-8"))
    g5 = json.loads((ci_dir / "G5_BOUNDARY_SEPARATION_LEDGER.json").read_text(encoding="utf-8"))
    prov_bytes = (ci_dir / "PCT0_XH0_SIGNED_PROVENANCE.json").read_bytes()
    prov = json.loads(prov_bytes.decode("utf-8"))

    # Verify every raw evidence file SHA-256 listed in PCT0_XH0_SIGNED_PROVENANCE.json
    raw_map = prov.get("raw_evidence_files", {})
    all_raw_bound = len(raw_map) == 6
    for fname, meta in raw_map.items():
        fp = ci_dir / fname
        if not fp.is_file():
            all_raw_bound = False
            break
        fb = fp.read_bytes()
        if sha256_hex(fb) != meta.get("sha256") or len(fb) != int(meta.get("size_bytes", -1)):
            all_raw_bound = False
            break

    meta_kv: Dict[str, str] = {}
    meta_fp = ci_dir / "PCT0_XH0_ATTESTATION_METADATA.txt"
    if meta_fp.is_file():
        for ln in meta_fp.read_text(encoding="utf-8").splitlines():
            if "=" in ln:
                k, v = ln.split("=", 1)
                meta_kv[k.strip()] = v.strip()

    gh_id = prov["github_and_runner_identity"]
    exp_commit = expected_commit_override or meta_kv.get("expected_commit_sha") or gh_id["github_sha"]
    exp_run_inv = (
        f"{EXPECTED_REPO_URI}/actions/runs/{gh_id['github_run_id']}/attempts/{gh_id['github_run_attempt']}"
    )

    sig_fp = ci_dir / "PCT0_XH0_SIGSTORE_BUNDLE.jsonl"
    if sig_fp.is_file():
        sig_obs = observe_sigstore_bundle_openssl(trusted_root_bytes, sig_fp.read_bytes(), prov_bytes)
    else:
        sig_obs = {"executed": False, "error_code": None}

    mut_obs_list: List[MutationSpanObservation] = []
    for mr in g4["mutations"]:
        cs = mr["causal_span_hashes"]
        pb = mr["proof_break_observation"]
        cm = mr["countermodel_refutation_witness"]
        mut_obs_list.append(
            MutationSpanObservation(
                mut_id=mr["mut_id"],
                unmutated_baseline_exit_zero=bool(mr["unmutated_baseline_exit_zero"]),
                orig_s0_sha256=cs["orig_s0_sha256"],
                reconstructed_s0_sha256=cs["reconstructed_s0_sha256"],
                p0_sha256=cs["p0_sha256"],
                pm_sha256=cs["pm_sha256"],
                q0_sha256=cs["q0_sha256"],
                qm_sha256=cs["qm_sha256"],
                sm_sha256=cs["sm_sha256"],
                span_sm_sha256=cs["span_sm_sha256"],
                dm_sha256=cs["dm_sha256"],
                span_dm_sha256=cs["span_dm_sha256"],
                prereq_all_exit_zero=bool(pb["prereq_all_exit_zero"]),
                break_exit_code=int(pb["exit_code"]),
                break_zero_syntax_errors=bool(pb["zero_syntax_errors"]),
                break_first_error_line=int(pb["first_error_line"]),
                break_error_class=str(pb["error_class"]),
                dm_compile_exit_code=int(cm["dm_compile_exit_code"]),
                dm_olean_sha256=str(cm["dm_olean_sha256"]),
                rfl_rhs_spec_sha256=str(cm["rfl_rhs_spec_sha256"]),
                probe_compile_exit_code=int(cm["probe_compile_exit_code"]),
                probe_sorry_count=int(cm["probe_sorry_count"]),
                probe_user_axioms_count=int(cm["probe_user_axioms_count"]),
            )
        )

    smap = g2["smap_metrics"]
    td = g3["transdeps_metrics"]
    sbx_sim = g5["isolated_no_lean_simulation"]

    core_obs = CoreObservation(
        zip_sha256=g1["s1s2_bundle_sha256"],
        zip_size_bytes=int(g1["s1s2_bundle_size_bytes"]),
        zip_entries_count=int(g1["s1s2_bundle_entries_count"]),
        zip_crc_ok=bool(g1["s1s2_bundle_crc_ok"]),
        lean_source_sha256s=tuple(sorted(g1["lean_source_sha256_map"].items())),
        frozen_receipt_sha256s=tuple(
            sorted((r["filename"], r["sha256"], int(r["size_bytes"])) for r in g1["embedded_frozen_receipts"])
        ),
        pre_post_input_hashes_identical=bool(g1["pre_post_input_hashes_identical"]),
        auxiliary_text_prescreen_clean=bool(g1["auxiliary_text_prescreen"]["clean"]),
        require_linux_tar_binding=bool(g2["require_linux_tar_binding"]),
        lean_tar_sha256=g2["lean_archive_sha256"],
        lean_tar_size=int(g2["lean_archive_size_bytes"]) if g2["lean_archive_size_bytes"] is not None else None,
        lean_version_banner=g2["lean_version_banner"],
        compiled_modules=tuple(
            (r["module"], int(r["exit_code"]), str(r["olean_sha256"])) for r in g2["compiled_modules"]
        ),
        calibration_imports=tuple(g2["zero_import_calibration_imports"]),
        target_module_imports=tuple(
            (r["module"], str(r["olean_sha256"]), tuple(r["imports"])) for r in g2["target_module_olean_imports"]
        ),
        smap_constants=int(smap["constants"]),
        smap_theorems=int(smap["theorems"]),
        smap_sorry=int(smap["sorry"]),
        smap_user_axioms=int(smap["userAxioms"]),
        smap_opaque=int(smap["opaque"]),
        smap_reduce_bool=int(smap["reduceBool"]),
        smap_classical_choice=int(smap["classicalChoice"]),
        transdeps_sat_g=int(td["satG"]),
        transdeps_sat_h=int(td["satH"]),
        transdeps_inter_g_transport=int(td["interGTransport"]),
        transdeps_inter_g_h=int(td["interGH"]),
        transdeps_inter_h_transport=int(td["interHTransport"]),
        transdeps_inter_h_g=int(td["interHG"]),
        transdeps_shared_user_gh=int(td["sharedUserGH"]),
        transdeps_closure_g=int(td["closureG"]),
        transdeps_closure_h=int(td["closureH"]),
        transdeps_transport_consts=int(td["transportConsts"]),
        axiom_footprints=tuple(sorted((k, tuple(sorted(v))) for k, v in g3["axiom_footprints"].items())),
        mutations=tuple(mut_obs_list),
        ci_unit_tests_passed=int(g4["context_a_ci_unit_tests"]["passed"]),
        ci_unit_tests_skipped=int(g4["context_a_ci_unit_tests"]["skipped"]),
        ci_unit_tests_failed=int(g4["context_a_ci_unit_tests"]["failed"]),
        self_contained_offline_verdict=g5["self_contained_offline_verdict"],
        isolated_sim_overall_verdict=sbx_sim["overall_poset_verdict"],
        isolated_sim_passed=int(sbx_sim["passed"]),
        isolated_sim_intended_skips=int(sbx_sim["intended_skips"]),
        isolated_sim_unexpected_skips=int(sbx_sim["unexpected_skips"]),
        isolated_sim_failed=int(sbx_sim["failed"]),
        empirical_status=g5["held_boundaries"]["empirical_status"],
        f_pct0_17_status=g5["held_boundaries"]["f_pct0_17_status"],
        sigstore_executed=bool(sig_obs.get("executed", False)),
        sigstore_error_code=sig_obs.get("error_code"),
        trusted_root_sha256=sig_obs.get("trusted_root_sha256"),
        provenance_subject_sha256=sig_obs.get("provenance_subject_sha256"),
        dsse_statement_subject_sha256=sig_obs.get("dsse_statement_subject_sha256"),
        provenance_s1s2_zip_sha256=prov["frozen_s1s2_input_bundle"]["sha256"],
        provenance_raw_files_all_hash_bound=all_raw_bound,
        fulcio_chain_ok=sig_obs.get("fulcio_chain_ok"),
        fulcio_san_uri=sig_obs.get("fulcio_san_uri"),
        fulcio_oidc_issuer=sig_obs.get("fulcio_oidc_issuer"),
        fulcio_repo_uri=sig_obs.get("fulcio_repo_uri"),
        fulcio_runner_env=sig_obs.get("fulcio_runner_env"),
        fulcio_commit_sha=sig_obs.get("fulcio_commit_sha"),
        expected_commit_sha=exp_commit,
        fulcio_run_invocation_uri=sig_obs.get("fulcio_run_invocation_uri"),
        expected_run_invocation_uri=exp_run_inv,
        ct_precert_sct_ok=sig_obs.get("ct_precert_sct_ok"),
        rekor_set_ok=sig_obs.get("rekor_set_ok"),
        rekor_merkle_ok=sig_obs.get("rekor_merkle_ok"),
        rekor_checkpoint_ok=sig_obs.get("rekor_checkpoint_ok"),
        dsse_pae_sig_ok=sig_obs.get("dsse_pae_sig_ok"),
    )
    return (core_obs, {"provenance": prov, "sigstore_details": sig_obs})


def directory_tree_digest(d: Path) -> str:
    acc = hashlib.sha256()
    for p in sorted(d.rglob("*")):
        if p.is_file():
            acc.update(p.relative_to(d).as_posix().encode("utf-8"))
            acc.update(b"\x00")
            acc.update(hashlib.sha256(p.read_bytes()).digest())
    return acc.hexdigest()


def run_six_isolated_adversarial_experiments(
    clean_ci_dir: Path,
    trusted_root_bytes: bytes,
    cross_workflow_p0_sigstore_bytes: bytes,
) -> Tuple[AdversarialCaseObservation, ...]:
    orig_tree_pre = directory_tree_digest(clean_ci_dir)
    cases: List[AdversarialCaseObservation] = []

    def _run_case(adv_id: str, gate_idx: int, mutate_fn: Any) -> None:
        pre_d = directory_tree_digest(clean_ci_dir)
        with tempfile.TemporaryDirectory(prefix=f"pct0_adv_{adv_id}_") as td:
            cp = Path(td) / "ci_copy"
            shutil.copytree(clean_ci_dir, cp)
            mutate_fn(cp)
            mut_d = directory_tree_digest(cp)
            pert_obs, _ = parse_ci_directory_to_core_obs(cp, trusted_root_bytes)
        post_d = directory_tree_digest(clean_ci_dir)
        cases.append(
            AdversarialCaseObservation(
                adv_id=adv_id,
                target_gate_index=gate_idx,
                pre_orig_sha256=pre_d,
                mutated_copy_sha256=mut_d,
                post_orig_sha256=post_d,
                perturbed_obs=pert_obs,
            )
        )

    # MXH0_PCT0_01: Source hash drift in G1
    def _m01(cp: Path) -> None:
        fp = cp / "G1_SOURCE_LINEAGE_MANIFEST.json"
        doc = json.loads(fp.read_text(encoding="utf-8"))
        orig_h = doc["lean_source_sha256_map"]["ProofspaceOmegaPCT0.GenG"]
        doc["lean_source_sha256_map"]["ProofspaceOmegaPCT0.GenG"] = ("0" if orig_h[0] != "0" else "f") + orig_h[1:]
        fp.write_text(json.dumps(doc, indent=2), encoding="utf-8")

    # MXH0_PCT0_02: Non-semantic parser error & missing countermodel in G4 (F-XH0-01 / F-PCT0-XH0-01/05)
    def _m02(cp: Path) -> None:
        fp = cp / "G4_SEMANTIC_MUTATION_RAW_DIAGNOSTICS.json"
        doc = json.loads(fp.read_text(encoding="utf-8"))
        doc["mutations"][2]["proof_break_observation"]["zero_syntax_errors"] = False
        doc["mutations"][2]["proof_break_observation"]["first_error_line"] = 10
        doc["mutations"][2]["countermodel_refutation_witness"]["probe_compile_exit_code"] = 1
        fp.write_text(json.dumps(doc, indent=2), encoding="utf-8")

    # MXH0_PCT0_03: Shared user constant smuggling in TransDeps (G3)
    def _m03(cp: Path) -> None:
        fp = cp / "G3_TRANSDEPS_AND_AXIOM_AUDIT.json"
        doc = json.loads(fp.read_text(encoding="utf-8"))
        doc["transdeps_metrics"]["sharedUserGH"] = 1
        fp.write_text(json.dumps(doc, indent=2), encoding="utf-8")

    # MXH0_PCT0_04: Real cross-workflow Sigstore bundle replay (P0-XH0 SAN p0_xh0_detached_r2_qualification.yml)
    def _m04(cp: Path) -> None:
        (cp / "PCT0_XH0_SIGSTORE_BUNDLE.jsonl").write_bytes(cross_workflow_p0_sigstore_bytes)

    # MXH0_PCT0_05: Stale commit SHA OID mismatch (0b74a4ce... vs actual PCT0-XH0 commit)
    def _m05(cp: Path) -> None:
        meta_fp = cp / "PCT0_XH0_ATTESTATION_METADATA.txt"
        existing = meta_fp.read_text(encoding="utf-8") if meta_fp.is_file() else ""
        meta_fp.write_text(
            existing + "\nexpected_commit_sha=0b74a4ce1ed4e34dd252ef6d474c03be0748f615\n",
            encoding="utf-8",
        )

    # MXH0_PCT0_06: Post-signing 1-byte tamper of PCT0_XH0_SIGNED_PROVENANCE.json
    def _m06(cp: Path) -> None:
        fp = cp / "PCT0_XH0_SIGNED_PROVENANCE.json"
        raw = bytearray(fp.read_bytes())
        raw[0] = ord(" ") if raw[0] != ord(" ") else ord("\n")
        fp.write_bytes(bytes(raw))

    _run_case("MXH0_PCT0_01", 0, _m01)
    _run_case("MXH0_PCT0_02", 3, _m02)
    _run_case("MXH0_PCT0_03", 2, _m03)
    _run_case("MXH0_PCT0_04", 5, _m04)
    _run_case("MXH0_PCT0_05", 5, _m05)
    _run_case("MXH0_PCT0_06", 5, _m06)

    assert directory_tree_digest(clean_ci_dir) == orig_tree_pre
    return tuple(cases)


def verify_and_seal_downloaded_ci_artifact(
    xh0_root: Path,
    ci_artifact_zip_path: Path,
    write_receipt_and_bundle: bool = True,
) -> Tuple[AdjudicationDecision, Dict[str, Any]]:
    s1s2_zip_path = xh0_root / "readonly_s1s2_input" / "CAMPUS_PROOFSPACE_OMEGA_PCT0_S1S2_MINIMAL_FORMALIZATION_BUNDLE.zip"
    trusted_root_path = xh0_root / "readonly_trust_root" / "F98_SIGSTORE_PUBLIC_GOOD_TRUSTED_ROOT.jsonl"
    cross_wf_sig_path = xh0_root / "readonly_trust_root" / "CROSS_WORKFLOW_P0_XH0_SIGSTORE_BUNDLE.jsonl"

    s1s2_bytes = s1s2_zip_path.read_bytes()
    trusted_root_bytes = trusted_root_path.read_bytes()
    cross_wf_bytes = cross_wf_sig_path.read_bytes()
    spec = build_pinned_spec_from_frozen_s1s2(s1s2_bytes)

    ci_zip_pre_bytes = ci_artifact_zip_path.read_bytes()
    ci_zip_pre_sha = sha256_hex(ci_zip_pre_bytes)

    with tempfile.TemporaryDirectory(prefix="pct0_xh0_verify_") as td:
        ci_dir = Path(td) / "ci_raw"
        ci_dir.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(io.BytesIO(ci_zip_pre_bytes), "r") as zf:
            if zf.testzip() is not None:
                raise RuntimeError("Corrupt CI artifact ZIP CRC")
            zf.extractall(ci_dir)

        core_obs, aux_meta = parse_ci_directory_to_core_obs(ci_dir, trusted_root_bytes)
        adv_obs = run_six_isolated_adversarial_experiments(ci_dir, trusted_root_bytes, cross_wf_bytes)

        if write_receipt_and_bundle:
            ledger_dir = xh0_root / "ledger"
            ledger_dir.mkdir(parents=True, exist_ok=True)
            for p in sorted(ci_dir.iterdir()):
                if p.is_file():
                    shutil.copy2(p, ledger_dir / p.name)

    ci_zip_post_sha = sha256_hex(ci_artifact_zip_path.read_bytes())
    obs_bundle = ObsBundle(
        core=core_obs,
        adversarial_cases=adv_obs,
        bundle_pre_sha256=ci_zip_pre_sha,
        bundle_post_sha256=ci_zip_post_sha,
    )
    decision = adjudicate_pct0_xh0_pure(obs_bundle, spec)

    prov = aux_meta["provenance"]
    sig_det = aux_meta["sigstore_details"]
    qual_verdict = (
        "EXTERNAL_REPLAY_ATTESTED"
        if decision.g7_master_tribunal_gate == VAL_PASS
        else f"NOT_ATTESTED__{decision.g7_master_tribunal_gate}"
    )

    payload = {
        "schema": "CAMPUS_PCT0_XH0_DETACHED_QUALIFICATION_RECEIPT_V3",
        "stage_id": STAGE_ID,
        "qualification_verdict": qual_verdict,
        "tribunal_acceptance_reserved": True,
        "ci_raw_artifact_zip_sha256": ci_zip_pre_sha,
        "ci_raw_artifact_zip_size_bytes": len(ci_zip_pre_bytes),
        "frozen_s1s2_bundle_sha256": PINNED_S1S2_ZIP_SHA256,
        "signed_provenance_sha256": core_obs.provenance_subject_sha256,
        "github_and_runner_identity": prov["github_and_runner_identity"],
        "sigstore_verification_summary": {
            "fulcio_leaf_cert_sha256": sig_det.get("fulcio_leaf_cert_sha256"),
            "fulcio_san_uri": sig_det.get("fulcio_san_uri"),
            "rekor_global_log_index": sig_det.get("rekor_global_log_index"),
            "rekor_integrated_time_utc": sig_det.get("rekor_integrated_time_utc"),
            "rekor_merkle_root_sha256": sig_det.get("rekor_merkle_root_sha256"),
            "trusted_root_sha256": PINNED_TRUSTED_ROOT_SHA256,
            "trusted_root_scope": "VERIFIED_WITH_PINNED_F98_BASELINE_ROOT__NOT_INDEPENDENT_NEW_ROOT_BOOTSTRAP",
        },
        "gates_xh0_g1_to_g7": {
            "XH0-G1": decision.g1_source_lineage,
            "XH0-G2": decision.g2_lean_replay,
            "XH0-G3": decision.g3_transdeps_and_axioms,
            "XH0-G3-DefinitionalIndependence": decision.g3_definitional_independence_subverdict,
            "XH0-G3-ClosureCountParity": decision.g3_count_parity_subverdict,
            "XH0-G4": decision.g4_semantic_mutations,
            "XH0-G5": decision.g5_boundary_separation,
            "XH0-G6": decision.g6_sigstore_provenance,
            "XH0-G7": decision.g7_master_tribunal_gate,
            "DetachedRecheck": decision.detached_recheck_verdict,
            "ArtifactImmutability": decision.artifact_immutability_verdict,
            "AdversarialControls": dict(decision.adversarial_case_verdicts),
        },
        "harness_tcb_and_provenance_boundary": {
            "effectful_harness_sha256": sha256_hex(Path(__file__).read_bytes()),
            "pure_adjudicator_sha256": sha256_hex((THIS_DIR / "pure_adjudicator.py").read_bytes()),
            "openssl_version": ssl.OPENSSL_VERSION,
            "cryptography_version": cryptography.__version__ if CRYPTO_AVAILABLE else "UNAVAILABLE",
            "host_platform": f"{platform.system()}-{platform.release()}-{platform.machine()}",
            "boundary_statement": (
                "PureAdjudicationCorrect != CryptographicObservationAuthentic: "
                "pure_adjudicator.py guarantees side-effect-free 3-valued lattice valuation over ObsBundle, "
                "while OpenSSL/cryptography execution and filesystem hashing belong to the documented EffectfulHarness TCB."
            ),
        },
        "explicit_epistemic_and_authority_holds": {
            "f_pct0_17_external_commit_issuer_authenticity": "HELD",
            "concurrent_commit_atomicity": "HELD",
            "empirical_scientific_validity": "UNASSESSED",
            "f_xh0_01_and_f_r2_01_03_lineage_holds": "HELD",
            "pct_s3_s4_holonomy_and_obstruction": "HELD",
            "p1_e1d_and_release_47": "NOT_AUTHORIZED",
        },
    }
    receipt = {
        **payload,
        "seal": {
            "algorithm": "SHA-256",
            "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
            "payload_sha256": sha256_hex(canonical_json_bytes(payload)),
        },
    }

    if write_receipt_and_bundle:
        rec_path = xh0_root / "ledger" / "PCT0_XH0_DETACHED_QUALIFICATION_RECEIPT.json"
        rec_path.write_bytes(json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n")
        bundle_info = build_complete_evidence_bundle_zip(xh0_root)
        receipt["complete_bundle_summary"] = bundle_info

    return (decision, receipt)


def build_complete_evidence_bundle_zip(xh0_root: Path) -> Dict[str, Any]:
    out_zip = xh0_root / "CAMPUS_PROOFSPACE_OMEGA_PCT0_XH0_COMPLETE_EVIDENCE_BUNDLE.zip"
    rels: List[Path] = []
    for sub in ("ci_artifact", "ledger", "readonly_s1s2_input", "readonly_trust_root", "src", "tests"):
        d = xh0_root / sub
        if d.is_dir():
            for p in sorted(d.rglob("*")):
                if p.is_file() and "__pycache__" not in p.parts and not p.name.endswith(".pyc"):
                    rels.append(p.relative_to(xh0_root))
    readme = xh0_root / "README.md"
    if readme.is_file():
        rels.append(Path("README.md"))
    rels = sorted(rels, key=lambda p: p.as_posix())

    fixed_dt = (2026, 11, 19, 0, 0, 0)
    with zipfile.ZipFile(out_zip, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for rel in rels:
            zi = zipfile.ZipInfo(rel.as_posix(), date_time=fixed_dt)
            zi.compress_type = zipfile.ZIP_DEFLATED
            zi.external_attr = 0o644 << 16
            zf.writestr(zi, (xh0_root / rel).read_bytes())

    raw = out_zip.read_bytes()
    return {
        "bundle_path": str(out_zip),
        "size_bytes": len(raw),
        "sha256": sha256_hex(raw),
        "entry_count": len(rels),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ci-artifact-zip", required=True, type=Path)
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args()

    xh0_root = THIS_DIR.parent
    decision, receipt = verify_and_seal_downloaded_ci_artifact(
        xh0_root=xh0_root,
        ci_artifact_zip_path=args.ci_artifact_zip,
        write_receipt_and_bundle=not args.no_write,
    )
    print(
        json.dumps(
            {
                "qualification_verdict": receipt["qualification_verdict"],
                "gates": receipt["gates_xh0_g1_to_g7"],
                "payload_sha256": receipt["seal"]["payload_sha256"],
                "complete_bundle_summary": receipt.get("complete_bundle_summary"),
            },
            indent=2,
            ensure_ascii=False,
        )
    )
    return 0 if decision.g7_master_tribunal_gate == VAL_PASS else 1


if __name__ == "__main__":
    raise SystemExit(main())
