#!/usr/bin/env python3
"""Separate Post-Execution Sigstore/SLSA Provenance Bundle Verifier (`F96-02` + `F97-01` + `F98-01/02`).

96th, 97th & 98th Independent Static & Physical Tribunal Compliance:
  - Runs OUTSIDE CI AFTER `actions/attest-build-provenance` signs the artifact bundle.
  - Enforces `F97-01` single-object verified Statement identity binding:

      SignatureVerified_gh(A)
        /\ EnvelopeInternalConsistent(A)
        /\ BundleIdentityBound(A, B_i)
        /\ SubjectDigest(A) = SHA256(R)
        /\ ExpectedSLSAClaims(A)
        /\ ExpectedFulcioCertClaims(A)
      ==> AuthenticatedProvenance(R)

  - Enforces `F98-01` pre-pinned upstream GitHub CLI (`cli/cli` `v2.67.0`) binary SHA-256 baseline:
      By default (`allow_unpinned_gh_binary=False`), `gh` MUST match either an immutable pre-pinned
      official `cli/cli` `v2.67.0` binary SHA-256 in `PINNED_OFFICIAL_GH_V2_67_0_BINARIES` or an
      independently pinned `--expected-gh-sha256` baseline (eliminating tautological self-hashing).
  - Provides `--run-f98-02-real-sigstore-integration` to qualify real `gh 2.67.0` JSON schema,
    Fulcio/Rekor verification, split-brain/sidecar rejection, multi-attestation selection, and
    failure state-promotion blocking against real GitHub Actions Sigstore v0.3 bundles.
  - Maximum emitted state is `DETACHED_EXECUTION_EVIDENCED`; `THIRD_PARTY_SCOPED_VERIFIED`
    remains reserved exclusively for independent human/Tribunal review.
"""

from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

PINNED_ZIP_46_SHA256 = "4c42f12b605083d13228c02c84e12b4689cdf32be0f507041b6a36360eec4608"
PINNED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
PINNED_KERNEL_LEDGER_SHA256 = "ebf560d74638c99861db866fc326b3accec556ca4f64efab774890030df484b0"
PINNED_AUTHOR_HOST_FP = "20d3b7d9128cdf243cad418974465a5323086c48141170d76426e63643ab394f"
PINNED_GH_VERIFY_JSON_SCHEMA = "CLI_CLI_ATTESTATION_PROCESSING_RESULT_LIST_V1"
PINNED_GITHUB_OIDC_ISSUER = "https://token.actions.githubusercontent.com"

# F98-01: Pre-pinned immutable official `cli/cli` v2.67.0 (2025-02-11, git commit 6899fe21dd80873893dd1a3bf3bdd4d33b1b2338)
# binary SHA-256 baseline, verified against `gh_2.67.0_checksums.txt` AND its own GitHub Actions Sigstore bundle.
PINNED_OFFICIAL_GH_RELEASE_TAG = "v2.67.0"
PINNED_OFFICIAL_GH_V2_67_0_BINARIES: dict[str, dict[str, object]] = {
    "32ca129895be5c9843d059d0e6923325bf239efe18c415799ecde566b366af75": {
        "platform": "linux_amd64",
        "binary_size_bytes": 43704472,
        "official_archive": "gh_2.67.0_linux_amd64.tar.gz",
        "official_archive_sha256": "d77623479bec017ef8eebadfefc785bafd4658343b3eb6d3f3e26fd5e11368d5",
    },
    "b6a8b56fbaf641669c8b27bf1992924fc9d0bbf315ce664799e17d1d89575e30": {
        "platform": "linux_arm64",
        "binary_size_bytes": 43384984,
        "official_archive": "gh_2.67.0_linux_arm64.tar.gz",
        "official_archive_sha256": "d286ed158b629cefe4732b4b6865a7e0f763164477e42b91ea4494c1bb241ae0",
    },
    "bca73e6632495fab9857c63c477649d033650e38b7286c6c4ab30f9252c0e8b3": {
        "platform": "macOS_arm64",
        "binary_size_bytes": 44244240,
        "official_archive": "gh_2.67.0_macOS_arm64.zip",
        "official_archive_sha256": "0c2524c2b002fda89f8b766c7d3dd8e6ac1de183556728a83182c6137f19643d",
    },
    "865a278bdd91926228c26559fdd25f7c11107b5b46a862d0c7c134c8b3a2b755": {
        "platform": "macOS_amd64",
        "binary_size_bytes": 44640336,
        "official_archive": "gh_2.67.0_macOS_amd64.zip",
        "official_archive_sha256": "eb8f57371aeccc06f847992bb69e4e84f83b13e080708dd55239f6f8fc14300c",
    },
    "edd3626605c40866f74a3056f681479f7339254f607c0276993a8e0c77dab0c2": {
        "platform": "windows_amd64",
        "binary_size_bytes": 44162688,
        "official_archive": "gh_2.67.0_windows_amd64.zip",
        "official_archive_sha256": "3a52a68a95d007d0c97f3a0a27f7302872eb31010e69312d20c59e90e0ba1e9f",
    },
}

HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
HEX64_RE = re.compile(r"^[0-9a-f]{64}$")


def canonical_json_sha256(obj: object) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def canonical_dsse_signatures_sha256(sigs: list) -> str:
    """Hash decoded DSSE signature bytes + normalized keyid (empty string default across Node/Go protojson)."""
    norm: list[dict[str, str]] = []
    for idx, s in enumerate(sigs):
        if not isinstance(s, dict) or not isinstance(s.get("sig"), str) or not s["sig"]:
            raise RuntimeError(f"Invalid DSSE signature object at index {idx}")
        raw_sig = base64.b64decode(s["sig"], validate=True)
        norm.append({
            "keyid": s.get("keyid") or "",
            "sig_sha256": hashlib.sha256(raw_sig).hexdigest(),
        })
    return canonical_json_sha256(norm)


def canonical_payload_sha256(obj: dict) -> str:
    body = {k: v for k, v in obj.items() if k != "seal"}
    return canonical_json_sha256(body)


def seal_bundle_verdict(payload: dict) -> dict:
    body = {k: v for k, v in payload.items() if k != "seal"}
    out = dict(body)
    out["seal"] = {
        "algorithm": "SHA-256",
        "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
        "payload_sha256": canonical_payload_sha256(body),
    }
    return out


def validate_caller_expected_params(
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
) -> None:
    if "/" not in expected_repo or expected_repo.startswith("/") or expected_repo.endswith("/"):
        raise ValueError(f"expected_repo must be 'owner/repo', got {expected_repo!r}")
    if not expected_workflow_path or not expected_workflow_path.strip():
        raise ValueError("expected_workflow_path must be non-empty")
    if not HEX40_RE.match(expected_commit_sha):
        raise ValueError(f"expected_commit_sha must be 40-char lowercase hex, got {expected_commit_sha!r}")
    if not expected_run_id.isdigit():
        raise ValueError(f"expected_run_id must be numeric digits, got {expected_run_id!r}")


def validate_candidate_receipt_bytes(receipt_bytes: bytes) -> tuple[str, dict]:
    """Verify internal seal and Stage A candidate invariants of `F96_DETACHED_AUDIT_RECEIPT.json`."""
    receipt_sha256 = hashlib.sha256(receipt_bytes).hexdigest()
    receipt_obj = json.loads(receipt_bytes.decode("utf-8"))
    if canonical_payload_sha256(receipt_obj) != receipt_obj.get("seal", {}).get("payload_sha256"):
        raise RuntimeError("Receipt canonical seal invalid")
    if receipt_obj.get("live_lean_reexecuted") is not True:
        raise RuntimeError("Receipt does not record live_lean_reexecuted == True")
    if receipt_obj.get("target_zip_sha256") != PINNED_ZIP_46_SHA256:
        raise RuntimeError("Receipt target_zip_sha256 does not match frozen Release #46")
    if (
        receipt_obj.get("reproducibility_ledger_check_distinct_from_semantic_spec", {}).get(
            "combined_kernel_ledger_sha256"
        )
        != PINNED_KERNEL_LEDGER_SHA256
    ):
        raise RuntimeError("Receipt combined_kernel_ledger_sha256 mismatch")

    prov = receipt_obj.get("f95_02_toolchain_and_runtime_provenance", {})
    if prov.get("lean_commit_enforced") != PINNED_LEAN_COMMIT:
        raise RuntimeError("Receipt Lean commit mismatch")
    if (
        prov.get("runtime_host_fingerprint_sha256") == PINNED_AUTHOR_HOST_FP
        or receipt_obj.get("f96_01_in_process_evidence_state") != "DETACHED_HOST_CANDIDATE"
    ):
        raise RuntimeError(
            "Receipt came from author host or non-candidate run; cannot promote to DETACHED_EXECUTION_EVIDENCED"
        )
    return receipt_sha256, receipt_obj


def parse_sigstore_bundle_envelopes(sigstore_bundle_jsonl_bytes: bytes) -> list[dict]:
    """Parse all DSSE envelopes in a `.jsonl` Sigstore bundle without trusting their signatures yet."""
    lines = [ln.strip() for ln in sigstore_bundle_jsonl_bytes.decode("utf-8").splitlines() if ln.strip()]
    if not lines:
        raise RuntimeError("Empty Sigstore bundle")

    parsed_entries: list[dict] = []
    for idx, ln in enumerate(lines):
        b_obj = json.loads(ln)
        if not isinstance(b_obj, dict):
            raise RuntimeError(f"Bundle line {idx} is not a JSON object")
        dsse = b_obj.get("dsseEnvelope")
        if dsse is None and isinstance(b_obj.get("bundle"), dict):
            dsse = b_obj["bundle"].get("dsseEnvelope")
        if not isinstance(dsse, dict):
            raise RuntimeError(f"Bundle line {idx} missing dsseEnvelope object")
        if dsse.get("payloadType") != "application/vnd.in-toto+json":
            raise RuntimeError(
                f"Bundle line {idx} unsupported dsseEnvelope.payloadType: {dsse.get('payloadType')!r}"
            )
        payload_b64 = dsse.get("payload")
        if not isinstance(payload_b64, str) or not payload_b64:
            raise RuntimeError(f"Bundle line {idx} missing base64 dsseEnvelope.payload")
        raw_payload = base64.b64decode(payload_b64, validate=True)
        stmt = json.loads(raw_payload.decode("utf-8"))
        if not isinstance(stmt, dict) or stmt.get("_type") != "https://in-toto.io/Statement/v1":
            raise RuntimeError(f"Bundle line {idx} decoded payload is not an in-toto Statement/v1")
        sigs = dsse.get("signatures")
        if not isinstance(sigs, list):
            raise RuntimeError(f"Bundle line {idx} dsseEnvelope.signatures must be a list")

        parsed_entries.append({
            "bundle_line_index": idx,
            "bundle_line_sha256": hashlib.sha256(ln.encode("utf-8")).hexdigest(),
            "dsse_payload_raw_sha256": hashlib.sha256(raw_payload).hexdigest(),
            "canonical_statement_sha256": canonical_json_sha256(stmt),
            "dsse_signatures_sha256": canonical_dsse_signatures_sha256(sigs),
            "statement": stmt,
        })
    return parsed_entries


def evaluate_statement_and_cert_claims(
    statement: dict,
    certificate: dict | None,
    receipt_sha256: str,
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
    require_certificate_claims: bool,
) -> dict:
    """Check Subject SHA-256, SLSA v1 claims, and X.509 Fulcio OIDC claims (including `runInvocationURI`)
    on ONE exact Statement/Certificate pair `A`."""
    if not isinstance(statement, dict) or statement.get("_type") != "https://in-toto.io/Statement/v1":
        raise RuntimeError("Statement _type is not https://in-toto.io/Statement/v1")
    if statement.get("predicateType") != "https://slsa.dev/provenance/v1":
        raise RuntimeError(f"Unexpected SLSA predicateType: {statement.get('predicateType')!r}")

    subjects = statement.get("subject", [])
    if not isinstance(subjects, list) or not any(
        isinstance(s, dict) and s.get("digest", {}).get("sha256") == receipt_sha256 for s in subjects
    ):
        raise RuntimeError(
            f"SubjectDigestMismatch: receipt sha256 {receipt_sha256} not present in statement.subject"
        )

    pred = statement.get("predicate", {})
    build_def = pred.get("buildDefinition", {}) if isinstance(pred, dict) else {}
    ext_params = build_def.get("externalParameters", {}) if isinstance(build_def, dict) else {}
    wf = ext_params.get("workflow", {}) if isinstance(ext_params, dict) else {}
    resolved_deps = build_def.get("resolvedDependencies", []) if isinstance(build_def, dict) else []
    run_meta = (
        pred.get("runDetails", {}).get("metadata", {})
        if isinstance(pred, dict) and isinstance(pred.get("runDetails"), dict)
        else {}
    )

    expected_repo_uri = f"https://github.com/{expected_repo}"
    if wf.get("repository") != expected_repo_uri:
        raise RuntimeError(f"SLSA repository mismatch: {wf.get('repository')!r} != {expected_repo_uri!r}")
    if wf.get("path") != expected_workflow_path:
        raise RuntimeError(f"SLSA workflow path mismatch: {wf.get('path')!r} != {expected_workflow_path!r}")

    commit_matched = isinstance(resolved_deps, list) and any(
        isinstance(d, dict) and d.get("digest", {}).get("gitCommit") == expected_commit_sha
        for d in resolved_deps
    )
    if not commit_matched:
        raise RuntimeError(f"SLSA gitCommit digest {expected_commit_sha} not found in resolvedDependencies")

    inv_id = run_meta.get("invocationId", "")
    if not isinstance(inv_id, str):
        raise RuntimeError("SLSA runDetails.metadata.invocationId must be a string")
    inv_re = re.compile(
        rf"^https://github\.com/{re.escape(expected_repo)}/actions/runs/{re.escape(expected_run_id)}(?:/attempts/[0-9]+)?$"
    )
    if not inv_re.match(inv_id):
        raise RuntimeError(
            f"SLSA invocationId {inv_id!r} does not match expected run {expected_repo}#{expected_run_id}"
        )

    cert_summary = None
    if require_certificate_claims:
        if not isinstance(certificate, dict):
            raise RuntimeError(
                "GHVerifySchemaError: verificationResult.signature.certificate missing or not an object"
            )
        issuer = certificate.get("issuer")
        if issuer != PINNED_GITHUB_OIDC_ISSUER:
            raise RuntimeError(
                f"Fulcio certificate OIDC issuer mismatch: {issuer!r} != {PINNED_GITHUB_OIDC_ISSUER!r}"
            )
        cert_repo_uri = certificate.get("sourceRepositoryURI") or certificate.get("sourceRepositoryUri")
        if cert_repo_uri != expected_repo_uri:
            raise RuntimeError(
                f"Fulcio certificate sourceRepositoryURI mismatch: {cert_repo_uri!r} != {expected_repo_uri!r}"
            )
        cert_repo_digest = certificate.get("sourceRepositoryDigest")
        if cert_repo_digest != expected_commit_sha:
            raise RuntimeError(
                f"Fulcio certificate sourceRepositoryDigest mismatch: {cert_repo_digest!r} != {expected_commit_sha!r}"
            )
        signer_uri = certificate.get("buildSignerURI") or certificate.get("buildSignerUri")
        expected_signer_prefix = f"https://github.com/{expected_repo}/{expected_workflow_path.lstrip('/')}@"
        if signer_uri is not None and (
            not isinstance(signer_uri, str) or not signer_uri.startswith(expected_signer_prefix)
        ):
            raise RuntimeError(
                f"Fulcio certificate buildSignerURI mismatch: {signer_uri!r} does not start with {expected_signer_prefix!r}"
            )
        cert_run_inv = certificate.get("runInvocationURI") or certificate.get("runInvocationUri")
        if cert_run_inv is not None and (not isinstance(cert_run_inv, str) or not inv_re.match(cert_run_inv)):
            raise RuntimeError(
                f"Fulcio certificate runInvocationURI mismatch: {cert_run_inv!r} does not match {expected_repo}#{expected_run_id}"
            )
        cert_summary = {
            "issuer": issuer,
            "source_repository_uri": cert_repo_uri,
            "source_repository_digest": cert_repo_digest,
            "build_signer_uri": signer_uri,
            "run_invocation_uri": cert_run_inv,
            "runner_environment": certificate.get("runnerEnvironment"),
        }

    return {
        "receipt_sha256_matched_in_dsse_subject": receipt_sha256,
        "slsa_repository": wf.get("repository"),
        "slsa_workflow_path": wf.get("path"),
        "slsa_git_commit_sha": expected_commit_sha,
        "slsa_invocation_id": inv_id,
        "fulcio_certificate_claims": cert_summary,
    }


def parse_and_match_dsse_statement(
    receipt_bytes: bytes,
    sigstore_bundle_jsonl_bytes: bytes,
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
) -> dict:
    """Offline/parse-only inspection helper (NEVER sufficient on its own for DETACHED_EXECUTION_EVIDENCED)."""
    validate_caller_expected_params(
        expected_repo, expected_workflow_path, expected_commit_sha, expected_run_id
    )
    receipt_sha256, _ = validate_candidate_receipt_bytes(receipt_bytes)
    bundle_entries = parse_sigstore_bundle_envelopes(sigstore_bundle_jsonl_bytes)

    errors: list[str] = []
    for entry in bundle_entries:
        try:
            claims = evaluate_statement_and_cert_claims(
                statement=entry["statement"],
                certificate=None,
                receipt_sha256=receipt_sha256,
                expected_repo=expected_repo,
                expected_workflow_path=expected_workflow_path,
                expected_commit_sha=expected_commit_sha,
                expected_run_id=expected_run_id,
                require_certificate_claims=False,
            )
            claims["matched_bundle_line_index"] = entry["bundle_line_index"]
            claims["dsse_payload_raw_sha256"] = entry["dsse_payload_raw_sha256"]
            claims["canonical_statement_sha256"] = entry["canonical_statement_sha256"]
            return claims
        except RuntimeError as exc:
            errors.append(f"line[{entry['bundle_line_index']}]: {exc}")

    raise RuntimeError("No DSSE statement in bundle matched expected claims: " + "; ".join(errors))


def bind_and_verify_gh_attestation_results(
    gh_json_stdout: str,
    parsed_bundle_entries: list[dict],
    receipt_sha256: str,
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
    allow_extra_unverified_bundle_lines: bool = False,
) -> dict:
    """Enforce `F97-01`: extract cryptographically verified Statement(s) directly from
    `gh attestation verify --format json`, bind each verified entry to its exact `.jsonl` DSSE
    envelope by raw payload digest + canonical statement digest + signatures digest, reject any
    unverified `.jsonl` sidecar entry by default, and evaluate Subject + SLSA + Fulcio claims
    ONLY on that single verified Statement `A`."""
    try:
        parsed_gh = json.loads(gh_json_stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"GHVerifySchemaError: invalid JSON from gh attestation verify: {exc}") from exc

    if not isinstance(parsed_gh, list) or len(parsed_gh) == 0:
        raise RuntimeError(
            f"GHVerifySchemaError: expected non-empty JSON array ({PINNED_GH_VERIFY_JSON_SCHEMA})"
        )

    bundle_by_identity: dict[tuple[str, str, str], list[dict]] = {}
    for b_entry in parsed_bundle_entries:
        ident = (
            b_entry["dsse_payload_raw_sha256"],
            b_entry["canonical_statement_sha256"],
            b_entry["dsse_signatures_sha256"],
        )
        bundle_by_identity.setdefault(ident, []).append(b_entry)

    verified_bundle_line_indices: set[int] = set()
    matched_verified_records: list[dict] = []
    rejected_verified_records: list[dict] = []

    for v_idx, item in enumerate(parsed_gh):
        if not isinstance(item, dict):
            raise RuntimeError(f"GHVerifySchemaError: result[{v_idx}] is not a JSON object")

        vr = item.get("verificationResult")
        if not isinstance(vr, dict):
            raise RuntimeError(f"GHVerifySchemaError: result[{v_idx}] missing verificationResult object")

        stmt_v = vr.get("statement")
        if not isinstance(stmt_v, dict):
            raise RuntimeError(
                f"GHVerifySchemaError: result[{v_idx}] missing verificationResult.statement object"
            )
        sig_block = vr.get("signature")
        if not isinstance(sig_block, dict):
            raise RuntimeError(
                f"GHVerifySchemaError: result[{v_idx}] missing verificationResult.signature object"
            )
        cert_v = sig_block.get("certificate")

        att = item.get("attestation")
        if not isinstance(att, dict) or not isinstance(att.get("bundle"), dict):
            raise RuntimeError(
                f"GHVerifySchemaError: result[{v_idx}] missing attestation.bundle object"
            )
        dsse_v = att["bundle"].get("dsseEnvelope")
        if not isinstance(dsse_v, dict) or dsse_v.get("payloadType") != "application/vnd.in-toto+json":
            raise RuntimeError(
                f"GHVerifySchemaError: result[{v_idx}] missing attestation.bundle.dsseEnvelope (in-toto+json)"
            )
        payload_b64_v = dsse_v.get("payload")
        sigs_v = dsse_v.get("signatures")
        if not isinstance(payload_b64_v, str) or not payload_b64_v or not isinstance(sigs_v, list) or not sigs_v:
            raise RuntimeError(
                f"GHVerifySchemaError: result[{v_idx}] dsseEnvelope missing non-empty payload or signatures"
            )

        raw_payload_v = base64.b64decode(payload_b64_v, validate=True)
        decoded_env_stmt_v = json.loads(raw_payload_v.decode("utf-8"))

        stmt_v_canon_sha = canonical_json_sha256(stmt_v)
        env_stmt_v_canon_sha = canonical_json_sha256(decoded_env_stmt_v)
        if stmt_v_canon_sha != env_stmt_v_canon_sha:
            raise RuntimeError(
                f"GHInternalEnvelopeStatementMismatchError: result[{v_idx}] verificationResult.statement "
                f"({stmt_v_canon_sha}) != decoded attestation.bundle.dsseEnvelope.payload ({env_stmt_v_canon_sha})"
            )

        raw_payload_v_sha = hashlib.sha256(raw_payload_v).hexdigest()
        sigs_v_sha = canonical_dsse_signatures_sha256(sigs_v)
        ident_v = (raw_payload_v_sha, stmt_v_canon_sha, sigs_v_sha)

        matching_bundle_lines = bundle_by_identity.get(ident_v)
        if not matching_bundle_lines:
            raise RuntimeError(
                f"VerifiedStatementBundleMismatchError: gh verified result[{v_idx}] "
                f"(payload_sha256={raw_payload_v_sha}, stmt_sha256={stmt_v_canon_sha}) "
                f"does not match any parsed DSSE envelope in --sigstore-bundle"
            )

        for b_line in matching_bundle_lines:
            verified_bundle_line_indices.add(b_line["bundle_line_index"])

        bound_bundle_line = matching_bundle_lines[0]

        try:
            verified_claims = evaluate_statement_and_cert_claims(
                statement=stmt_v,
                certificate=cert_v,
                receipt_sha256=receipt_sha256,
                expected_repo=expected_repo,
                expected_workflow_path=expected_workflow_path,
                expected_commit_sha=expected_commit_sha,
                expected_run_id=expected_run_id,
                require_certificate_claims=True,
            )
            matched_verified_records.append({
                "matched_gh_verified_result_index": v_idx,
                "matched_bundle_line_index": bound_bundle_line["bundle_line_index"],
                "matched_bundle_line_sha256": bound_bundle_line["bundle_line_sha256"],
                "verified_dsse_payload_raw_sha256": raw_payload_v_sha,
                "verified_canonical_statement_sha256": stmt_v_canon_sha,
                "verified_dsse_signatures_sha256": sigs_v_sha,
                "claims_verified_on_same_statement": verified_claims,
            })
        except RuntimeError as exc:
            rejected_verified_records.append({
                "gh_verified_result_index": v_idx,
                "bound_bundle_line_index": bound_bundle_line["bundle_line_index"],
                "verified_canonical_statement_sha256": stmt_v_canon_sha,
                "rejection_reason": str(exc),
            })

    unverified_bundle_indices = sorted(
        b["bundle_line_index"]
        for b in parsed_bundle_entries
        if b["bundle_line_index"] not in verified_bundle_line_indices
    )
    if unverified_bundle_indices and not allow_extra_unverified_bundle_lines:
        raise RuntimeError(
            f"UnverifiedBundleEntryError: --sigstore-bundle contains DSSE line(s) {unverified_bundle_indices} "
            f"that were NOT cryptographically verified by gh attestation verify"
        )

    if not matched_verified_records:
        raise RuntimeError(
            "NoVerifiedStatementMatchedClaimsError: zero cryptographically verified DSSE statements "
            f"satisfied all expected Subject/SLSA/Fulcio claims; rejections={rejected_verified_records}"
        )

    primary = matched_verified_records[0]
    return {
        "pinned_gh_verify_json_schema": PINNED_GH_VERIFY_JSON_SCHEMA,
        "f97_01_statement_identity_bound": True,
        "total_bundle_dsse_lines": len(parsed_bundle_entries),
        "total_gh_verified_results": len(parsed_gh),
        "unverified_bundle_line_indices": unverified_bundle_indices,
        "matched_verified_statement_count": len(matched_verified_records),
        "rejected_verified_entries_count": len(rejected_verified_records),
        "rejected_verified_entries": rejected_verified_records,
        "bound_verified_attestation": primary,
    }


def inspect_gh_binary_tcb(
    gh_bin: str,
    expected_gh_sha256: str | None,
    custom_trusted_root: Path | None,
    allow_unpinned_gh_binary: bool = False,
) -> dict:
    """Enforce `F98-01` pre-pinned `gh` binary SHA-256 baseline and record external verifier TCB."""
    gh_path = Path(gh_bin).resolve()
    if not gh_path.is_file():
        raise RuntimeError(f"Resolved gh binary does not exist: {gh_path}")
    gh_bytes = gh_path.read_bytes()
    gh_sha256 = hashlib.sha256(gh_bytes).hexdigest()

    pin_source: str
    official_meta = PINNED_OFFICIAL_GH_V2_67_0_BINARIES.get(gh_sha256)
    if expected_gh_sha256 is not None:
        norm_expected = expected_gh_sha256.strip().lower()
        if not HEX64_RE.match(norm_expected):
            raise ValueError(f"expected_gh_sha256 must be 64-char lowercase hex, got {expected_gh_sha256!r}")
        if gh_sha256 != norm_expected:
            raise RuntimeError(
                f"GHBinaryHashMismatch: {gh_path} sha256 {gh_sha256} != expected {norm_expected}"
            )
        pin_source = (
            f"PINNED_OFFICIAL_GH_{PINNED_OFFICIAL_GH_RELEASE_TAG}_AND_EXPLICIT_BASELINE"
            if official_meta is not None
            else "EXPLICIT_CALLER_PINNED_BASELINE"
        )
        tcb_qualified = True
    elif official_meta is not None:
        if len(gh_bytes) != official_meta["binary_size_bytes"]:
            raise RuntimeError("Pinned gh binary size mismatch")
        pin_source = f"PINNED_OFFICIAL_GH_{PINNED_OFFICIAL_GH_RELEASE_TAG}_{official_meta['platform']}"
        tcb_qualified = True
    elif allow_unpinned_gh_binary:
        pin_source = "UNPINNED_SYSTEM_GH_BINARY_NOT_QUALIFIED"
        tcb_qualified = False
    else:
        raise RuntimeError(
            f"UnpinnedGHBinaryError (F98-01): {gh_path} (sha256={gh_sha256}) is not in "
            f"PINNED_OFFICIAL_GH_V2_67_0_BINARIES and no reviewer-approved --expected-gh-sha256 was provided."
        )

    ver_proc = subprocess.run([str(gh_path), "--version"], capture_output=True, text=True)
    if ver_proc.returncode != 0:
        raise RuntimeError(f"Failed to query gh --version: {ver_proc.stderr}")
    ver_first_line = (ver_proc.stdout.strip().splitlines() or ["unknown"])[0]

    trusted_root_info: dict[str, object]
    if custom_trusted_root is not None:
        tr_path = custom_trusted_root.resolve()
        trusted_root_info = {
            "mode": "CUSTOM_TRUSTED_ROOT_FILE",
            "path": str(tr_path),
            "sha256": hashlib.sha256(tr_path.read_bytes()).hexdigest(),
        }
    else:
        trusted_root_info = {
            "mode": "GH_CLI_EMBEDDED_SIGSTORE_PUBLIC_GOOD_TUF_ROOT",
            "path": None,
            "sha256": None,
        }

    return {
        "tcb_note": (
            "Cryptographic Sigstore Fulcio/Rekor verification relies on the external verifier host's "
            "Python 3 runtime, pre-pinned GitHub CLI ('gh') binary, and Sigstore TUF trusted root."
        ),
        "python_version": sys.version.split()[0],
        "gh_binary_resolved_path": str(gh_path),
        "gh_binary_size_bytes": len(gh_bytes),
        "gh_binary_sha256": gh_sha256,
        "gh_binary_pin_source": pin_source,
        "f98_01_gh_binary_baseline_qualified": tcb_qualified,
        "official_release_metadata": official_meta,
        "gh_version_header": ver_first_line,
        "sigstore_trusted_root": trusted_root_info,
    }


def verify_bundle_end_to_end(
    receipt_path: Path,
    sigstore_bundle_path: Path,
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
    require_cryptographic_gh_verify: bool = True,
    custom_trusted_root: Path | None = None,
    gh_bin_override: Path | None = None,
    expected_gh_sha256: str | None = None,
    allow_extra_unverified_bundle_lines: bool = False,
    allow_unpinned_gh_binary: bool = False,
) -> dict:
    validate_caller_expected_params(
        expected_repo, expected_workflow_path, expected_commit_sha, expected_run_id
    )
    receipt_bytes = receipt_path.read_bytes()
    bundle_bytes = sigstore_bundle_path.read_bytes()

    receipt_sha256, _ = validate_candidate_receipt_bytes(receipt_bytes)
    parsed_bundle_entries = parse_sigstore_bundle_envelopes(bundle_bytes)

    resolved_gh = str(gh_bin_override) if gh_bin_override is not None else shutil.which("gh")
    crypto_verified = False
    f97_bound_verification = None
    verifier_tcb = None
    unverified_parse_preview = None

    if resolved_gh is not None:
        verifier_tcb = inspect_gh_binary_tcb(
            gh_bin=resolved_gh,
            expected_gh_sha256=expected_gh_sha256,
            custom_trusted_root=custom_trusted_root,
            allow_unpinned_gh_binary=allow_unpinned_gh_binary,
        )
        signer_wf = f"{expected_repo}/{expected_workflow_path.lstrip('/')}"
        cmd = [
            str(Path(resolved_gh).resolve()),
            "attestation",
            "verify",
            str(receipt_path),
            "--bundle",
            str(sigstore_bundle_path),
            "--repo",
            expected_repo,
            "--signer-workflow",
            signer_wf,
            "--format",
            "json",
        ]
        if custom_trusted_root is not None:
            cmd.extend(["--custom-trusted-root", str(custom_trusted_root)])
        proc = subprocess.run(cmd, capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(f"Cryptographic gh attestation verify FAILED: {proc.stderr}\n{proc.stdout}")

        f97_bound_verification = bind_and_verify_gh_attestation_results(
            gh_json_stdout=proc.stdout,
            parsed_bundle_entries=parsed_bundle_entries,
            receipt_sha256=receipt_sha256,
            expected_repo=expected_repo,
            expected_workflow_path=expected_workflow_path,
            expected_commit_sha=expected_commit_sha,
            expected_run_id=expected_run_id,
            allow_extra_unverified_bundle_lines=allow_extra_unverified_bundle_lines,
        )
        crypto_verified = True
    elif require_cryptographic_gh_verify:
        raise RuntimeError(
            "F96-02/F97-01 BLOCK: GitHub CLI ('gh') not installed for cryptographic Sigstore bundle "
            "verification; unverified DSSE JSON claims alone CANNOT grant DETACHED_EXECUTION_EVIDENCED."
        )
    else:
        unverified_parse_preview = parse_and_match_dsse_statement(
            receipt_bytes=receipt_bytes,
            sigstore_bundle_jsonl_bytes=bundle_bytes,
            expected_repo=expected_repo,
            expected_workflow_path=expected_workflow_path,
            expected_commit_sha=expected_commit_sha,
            expected_run_id=expected_run_id,
        )

    tcb_ok = bool(verifier_tcb and verifier_tcb.get("f98_01_gh_binary_baseline_qualified"))
    if crypto_verified and f97_bound_verification is not None and tcb_ok:
        emitted_state = "DETACHED_EXECUTION_EVIDENCED"
    elif crypto_verified and f97_bound_verification is not None and not tcb_ok:
        emitted_state = "SIGNATURE_VERIFIED_WITH_UNPINNED_GH_TCB_NOT_QUALIFIED"
    else:
        emitted_state = "DSSE_CLAIMS_PARSED_SIGNATURE_UNVERIFIED_NOT_EVIDENCED"

    verified_claims_out = (
        f97_bound_verification["bound_verified_attestation"]["claims_verified_on_same_statement"]
        if f97_bound_verification is not None
        else unverified_parse_preview
    )

    return seal_bundle_verdict({
        "schema_version": "CAMPUS_NOESIS_F98_PROVENANCE_BUNDLE_VERIFICATION_RECEIPT_V3",
        "verified_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "f96_02_evidence_state": emitted_state,
        "cryptographic_sigstore_signature_verified": crypto_verified,
        "f97_01_verified_statement_identity_bound": bool(
            f97_bound_verification and f97_bound_verification["f97_01_statement_identity_bound"]
        ),
        "f98_01_gh_binary_baseline_qualified": tcb_ok,
        "verifier_can_emit_third_party_scoped_verified": False,
        "tribunal_human_review_required_for_third_party_scoped_verified": True,
        "dsse_subject_and_slsa_claims": verified_claims_out,
        "f97_01_bound_gh_verification": f97_bound_verification,
        "verifier_execution_tcb_disclosure": verifier_tcb,
    })


def run_f98_02_real_sigstore_integration(
    gh_bin_path: Path,
    real_artifact_path: Path,
    real_bundle_path: Path,
    secondary_real_bundle_path: Path | None,
    custom_trusted_root: Path,
    expected_repo: str,
    expected_workflow_path: str,
    expected_commit_sha: str,
    expected_run_id: str,
) -> dict:
    """Execute `F98-02` live cryptographic integration regression suite using a pre-pinned official
    `gh v2.67.0` binary, Sigstore TUF trusted root, and real Fulcio/Rekor-signed GitHub Actions bundle(s)."""
    tcb = inspect_gh_binary_tcb(
        gh_bin=str(gh_bin_path),
        expected_gh_sha256=None,
        custom_trusted_root=custom_trusted_root,
        allow_unpinned_gh_binary=False,
    )
    assert tcb["f98_01_gh_binary_baseline_qualified"] is True

    art_sha = hashlib.sha256(real_artifact_path.read_bytes()).hexdigest()
    real_bundle_bytes = real_bundle_path.read_bytes()
    parsed_real = parse_sigstore_bundle_envelopes(real_bundle_bytes)
    signer_wf = f"{expected_repo}/{expected_workflow_path.lstrip('/')}"
    gh_resolved = str(gh_bin_path.resolve())

    def _run_real_gh(target_art: Path, bundle_p: Path, wf_arg: str = signer_wf) -> subprocess.CompletedProcess:
        return subprocess.run(
            [
                gh_resolved,
                "attestation",
                "verify",
                str(target_art),
                "--bundle",
                str(bundle_p),
                "--repo",
                expected_repo,
                "--signer-workflow",
                wf_arg,
                "--custom-trusted-root",
                str(custom_trusted_root.resolve()),
                "--format",
                "json",
            ],
            capture_output=True,
            text=True,
        )

    # 1. Clean genuine Sigstore v0.3 bundle verification & triple-digest identity binding
    p_clean = _run_real_gh(real_artifact_path, real_bundle_path)
    if p_clean.returncode != 0:
        raise RuntimeError(f"Real Sigstore clean verification failed: {p_clean.stderr}")
    bound_clean = bind_and_verify_gh_attestation_results(
        gh_json_stdout=p_clean.stdout,
        parsed_bundle_entries=parsed_real,
        receipt_sha256=art_sha,
        expected_repo=expected_repo,
        expected_workflow_path=expected_workflow_path,
        expected_commit_sha=expected_commit_sha,
        expected_run_id=expected_run_id,
        allow_extra_unverified_bundle_lines=False,
    )

    with tempfile.TemporaryDirectory() as td:
        td_p = Path(td)
        real_b_obj = json.loads(real_bundle_bytes.decode("utf-8").strip())
        forged_b_obj = json.loads(json.dumps(real_b_obj))
        forged_stmt = json.loads(base64.b64decode(forged_b_obj["dsseEnvelope"]["payload"]).decode("utf-8"))
        forged_stmt["predicate"]["runDetails"]["metadata"]["invocationId"] = (
            f"https://github.com/{expected_repo}/actions/runs/99999999999/attempts/1"
        )
        forged_b_obj["dsseEnvelope"]["payload"] = base64.b64encode(
            json.dumps(forged_stmt).encode("utf-8")
        ).decode("ascii")
        forged_line = (json.dumps(forged_b_obj, separators=(",", ":")) + "\n").encode("utf-8")

        # 2. Live Split-Brain Attack on REAL gh: [Line 0: forged run_id=99999999999, Line 1: real signed bundle]
        #    Empirically `gh attestation verify` returns RC=0 (verifying Line 1), and F97-01 blocks BOTH modes!
        mixed_p = td_p / "mixed_forged_and_real.jsonl"
        mixed_p.write_bytes(forged_line + real_bundle_bytes)
        p_mixed = _run_real_gh(real_artifact_path, mixed_p)
        gh_accepted_partial_bundle = p_mixed.returncode == 0
        if p_mixed.returncode == 0:
            parsed_mixed = parse_sigstore_bundle_envelopes(mixed_p.read_bytes())
            for allow_extra in (False, True):
                try:
                    bind_and_verify_gh_attestation_results(
                        gh_json_stdout=p_mixed.stdout,
                        parsed_bundle_entries=parsed_mixed,
                        receipt_sha256=art_sha,
                        expected_repo=expected_repo,
                        expected_workflow_path=expected_workflow_path,
                        expected_commit_sha=expected_commit_sha,
                        expected_run_id="99999999999",
                        allow_extra_unverified_bundle_lines=allow_extra,
                    )
                    raise AssertionError("Failed to block live split-brain bundle")
                except RuntimeError:
                    pass

        # 3. Live Unverified Sidecar Rejection in default strict mode even when valid run_id is queried
        if p_mixed.returncode == 0:
            parsed_mixed = parse_sigstore_bundle_envelopes(mixed_p.read_bytes())
            try:
                bind_and_verify_gh_attestation_results(
                    gh_json_stdout=p_mixed.stdout,
                    parsed_bundle_entries=parsed_mixed,
                    receipt_sha256=art_sha,
                    expected_repo=expected_repo,
                    expected_workflow_path=expected_workflow_path,
                    expected_commit_sha=expected_commit_sha,
                    expected_run_id=expected_run_id,
                    allow_extra_unverified_bundle_lines=False,
                )
                raise AssertionError("Failed to reject live unverified sidecar in default strict mode")
            except RuntimeError:
                pass

        # 4. Multi-attestation bundle with two real signed Sigstore bundles (when secondary bundle provided)
        multi_real_verified = False
        if secondary_real_bundle_path is not None and secondary_real_bundle_path.is_file():
            two_real_p = td_p / "two_real_signed.jsonl"
            two_real_p.write_bytes(secondary_real_bundle_path.read_bytes() + real_bundle_bytes)
            p_two = _run_real_gh(real_artifact_path, two_real_p)
            assert p_two.returncode == 0, p_two.stderr
            parsed_two = parse_sigstore_bundle_envelopes(two_real_p.read_bytes())
            # Strict mode blocks extra bundle entry for another release; multi-bundle mode selects Line 1 cleanly
            try:
                bind_and_verify_gh_attestation_results(
                    gh_json_stdout=p_two.stdout,
                    parsed_bundle_entries=parsed_two,
                    receipt_sha256=art_sha,
                    expected_repo=expected_repo,
                    expected_workflow_path=expected_workflow_path,
                    expected_commit_sha=expected_commit_sha,
                    expected_run_id=expected_run_id,
                    allow_extra_unverified_bundle_lines=False,
                )
                raise AssertionError("Expected strict single-artifact bundle check to flag unrelated Line 0")
            except RuntimeError:
                pass
            bound_two = bind_and_verify_gh_attestation_results(
                gh_json_stdout=p_two.stdout,
                parsed_bundle_entries=parsed_two,
                receipt_sha256=art_sha,
                expected_repo=expected_repo,
                expected_workflow_path=expected_workflow_path,
                expected_commit_sha=expected_commit_sha,
                expected_run_id=expected_run_id,
                allow_extra_unverified_bundle_lines=True,
            )
            assert bound_two["bound_verified_attestation"]["matched_bundle_line_index"] == 1
            multi_real_verified = True

        # 5. Live cryptographic failure checks: tampered artifact & wrong signer-workflow -> RC != 0
        tampered_art = td_p / "tampered_artifact.bin"
        b_art = bytearray(real_artifact_path.read_bytes()[:4096])
        b_art[0] ^= 0xFF
        tampered_art.write_bytes(bytes(b_art))
        p_tampered = _run_real_gh(tampered_art, real_bundle_path)
        assert p_tampered.returncode != 0, "Expected gh attestation verify to fail on tampered artifact"

        p_wrong_wf = _run_real_gh(
            real_artifact_path, real_bundle_path, wf_arg=f"{expected_repo}/.github/workflows/nonexistent.yml"
        )
        assert p_wrong_wf.returncode != 0, "Expected gh attestation verify to fail on wrong signer workflow"

        # 6. Valid signature (`p_clean.stdout`), wrong expected commit or run_id -> blocked by Stage B
        for bad_c, bad_r in (("0" * 40, expected_run_id), (expected_commit_sha, "111111111")):
            try:
                bind_and_verify_gh_attestation_results(
                    gh_json_stdout=p_clean.stdout,
                    parsed_bundle_entries=parsed_real,
                    receipt_sha256=art_sha,
                    expected_repo=expected_repo,
                    expected_workflow_path=expected_workflow_path,
                    expected_commit_sha=bad_c,
                    expected_run_id=bad_r,
                    allow_extra_unverified_bundle_lines=False,
                )
                raise AssertionError("Failed to block mismatched commit/run_id on real verified bundle")
            except RuntimeError:
                pass

    return seal_bundle_verdict({
        "schema_version": "CAMPUS_NOESIS_F98_02_REAL_SIGSTORE_INTEGRATION_RECEIPT_V1",
        "executed_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "qualification_scope": (
            "STAGE_B_VERIFIER_AND_PINNED_GH_2_67_0_SIGSTORE_INTEGRATION_QUALIFICATION_ONLY__"
            "NOT_FROZEN46_EXTERNAL_CI_EXECUTION"
        ),
        "frozen46_detached_ci_execution_claimed": False,
        "f98_01_pinned_gh_tcb": tcb,
        "real_attested_artifact_name": real_artifact_path.name,
        "real_attested_artifact_sha256": art_sha,
        "real_sigstore_bundle_sha256": hashlib.sha256(real_bundle_bytes).hexdigest(),
        "f98_02_checks": {
            "real_verification_result_statement_schema_verified": True,
            "real_dsse_envelope_payload_equals_verified_statement": True,
            "real_fulcio_cert_issuer_repo_commit_workflow_run_bound": True,
            "real_gh_accepts_partial_mixed_bundle_empirically_confirmed": gh_accepted_partial_bundle,
            "f97_01_blocks_real_gh_split_brain_and_unverified_sidecar": True,
            "two_real_signed_bundles_selection_and_strict_guard_verified": multi_real_verified,
            "tampered_artifact_and_wrong_workflow_promotion_blocked": True,
        },
        "bound_clean_verification_summary": bound_clean,
    })


def _make_mock_gh_executable(td_path: Path, response_json_path: Path) -> Path:
    """Create a cross-platform mock `gh` executable for deterministic subprocess negative/positive tests."""
    helper_py = td_path / "mock_gh_impl.py"
    helper_py.write_text(
        "import pathlib, sys\n"
        "if '--version' in sys.argv:\n"
        "    print('gh version 2.67.0 (mock-f98-self-test)')\n"
        "    sys.exit(0)\n"
        f"data = pathlib.Path({str(response_json_path)!r}).read_text(encoding='utf-8')\n"
        "sys.stdout.write(data)\n"
        "sys.exit(0)\n",
        encoding="utf-8",
    )
    if os.name == "nt":
        wrapper = td_path / "mock_gh.cmd"
        wrapper.write_text(f'@echo off\r\n"{sys.executable}" "{helper_py}" %*\r\n', encoding="utf-8")
        return wrapper
    wrapper = td_path / "mock_gh"
    wrapper.write_text(f"#!{sys.executable}\n" + helper_py.read_text(encoding="utf-8"), encoding="utf-8")
    wrapper.chmod(0o755)
    return wrapper


def run_f97_bundle_self_tests() -> dict:
    """Deterministic unit & subprocess self-tests proving `F96-02` + `F97-01` + `F98-01` invariants."""
    sample_receipt = {
        "schema_version": "CAMPUS_NOESIS_F96_DETACHED_THIRD_PARTY_AUDIT_RECEIPT_V1",
        "live_lean_reexecuted": True,
        "target_zip_sha256": PINNED_ZIP_46_SHA256,
        "f96_01_in_process_evidence_state": "DETACHED_HOST_CANDIDATE",
        "f95_02_toolchain_and_runtime_provenance": {
            "lean_commit_enforced": PINNED_LEAN_COMMIT,
            "runtime_host_fingerprint_sha256": "33333333" * 8,
        },
        "reproducibility_ledger_check_distinct_from_semantic_spec": {
            "combined_kernel_ledger_sha256": PINNED_KERNEL_LEDGER_SHA256,
        },
    }
    sample_receipt["seal"] = {
        "algorithm": "SHA-256",
        "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
        "payload_sha256": canonical_payload_sha256(sample_receipt),
    }
    rec_bytes = (json.dumps(sample_receipt, sort_keys=True) + "\n").encode("utf-8")
    rec_sha = hashlib.sha256(rec_bytes).hexdigest()

    good_repo = "trusted-org/campus-audit"
    good_wf = ".github/workflows/f94_github_actions_third_party_lean46.yml"
    good_commit = "b" * 40
    good_run_id = "987654321"

    def _mk_stmt_and_env(
        subj_sha: str,
        repo: str,
        wf_path: str,
        commit_sha: str,
        run_id: str,
        sig_tag: str = "sig-valid-1",
        extra_note: str | None = None,
    ) -> tuple[dict, dict, bytes]:
        stmt: dict[str, object] = {
            "_type": "https://in-toto.io/Statement/v1",
            "subject": [{"name": "F96_DETACHED_AUDIT_RECEIPT.json", "digest": {"sha256": subj_sha}}],
            "predicateType": "https://slsa.dev/provenance/v1",
            "predicate": {
                "buildDefinition": {
                    "externalParameters": {
                        "workflow": {"repository": f"https://github.com/{repo}", "path": wf_path}
                    },
                    "resolvedDependencies": [{"digest": {"gitCommit": commit_sha}}],
                },
                "runDetails": {
                    "metadata": {
                        "invocationId": f"https://github.com/{repo}/actions/runs/{run_id}/attempts/1"
                    }
                },
            },
        }
        if extra_note is not None:
            stmt["predicate"]["runDetails"]["extraNote"] = extra_note  # type: ignore[index]
        dsse_env = {
            "payloadType": "application/vnd.in-toto+json",
            "payload": base64.b64encode(json.dumps(stmt).encode("utf-8")).decode("ascii"),
            "signatures": [{"keyid": "", "sig": base64.b64encode(sig_tag.encode("utf-8")).decode("ascii")}],
        }
        line_bytes = (json.dumps({"dsseEnvelope": dsse_env}) + "\n").encode("utf-8")
        return stmt, dsse_env, line_bytes

    def _mk_gh_entry(
        stmt: dict,
        dsse_env: dict,
        cert_repo: str | None = None,
        cert_commit: str | None = None,
        cert_wf: str | None = None,
        cert_run_inv: str | None = None,
    ) -> dict:
        wf_obj = stmt["predicate"]["buildDefinition"]["externalParameters"]["workflow"]  # type: ignore[index]
        repo_uri = f"https://github.com/{cert_repo}" if cert_repo else wf_obj["repository"]
        c_sha = cert_commit or stmt["predicate"]["buildDefinition"]["resolvedDependencies"][0]["digest"]["gitCommit"]  # type: ignore[index]
        w_path = cert_wf or wf_obj["path"]
        inv_uri = cert_run_inv or stmt["predicate"]["runDetails"]["metadata"]["invocationId"]  # type: ignore[index]
        return {
            "attestation": {"bundle": {"dsseEnvelope": dsse_env}},
            "verificationResult": {
                "statement": stmt,
                "signature": {
                    "certificate": {
                        "issuer": PINNED_GITHUB_OIDC_ISSUER,
                        "sourceRepositoryURI": repo_uri,
                        "sourceRepositoryDigest": c_sha,
                        "buildSignerURI": f"{repo_uri}/{w_path.lstrip('/')}@refs/heads/main",
                        "runInvocationURI": inv_uri,
                        "runnerEnvironment": "github-hosted",
                    }
                },
            },
        }

    stmt_good, env_good, bundle_good = _mk_stmt_and_env(
        rec_sha, good_repo, good_wf, good_commit, good_run_id, sig_tag="sig-good"
    )

    with tempfile.TemporaryDirectory() as td:
        td_p = Path(td)
        rp = td_p / "F96_DETACHED_AUDIT_RECEIPT.json"
        bp = td_p / "bundle.jsonl"
        gh_out_p = td_p / "gh_verify_out.json"
        rp.write_bytes(rec_bytes)
        bp.write_bytes(bundle_good)
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_good)]), encoding="utf-8")
        mock_gh = _make_mock_gh_executable(td_p, gh_out_p)
        mock_gh_sha = hashlib.sha256(mock_gh.read_bytes()).hexdigest()

        def _v(
            r_arg: Path = rp,
            b_arg: Path = bp,
            repo_arg: str = good_repo,
            wf_arg: str = good_wf,
            c_arg: str = good_commit,
            run_arg: str = good_run_id,
            exp_gh: str | None = mock_gh_sha,
            allow_extra: bool = False,
            allow_unpinned: bool = False,
        ) -> dict:
            return verify_bundle_end_to_end(
                r_arg,
                b_arg,
                repo_arg,
                wf_arg,
                c_arg,
                run_arg,
                gh_bin_override=mock_gh,
                expected_gh_sha256=exp_gh,
                allow_extra_unverified_bundle_lines=allow_extra,
                allow_unpinned_gh_binary=allow_unpinned,
            )

        # 1. Valid end-to-end bound verification + pinned gh binary SHA-256 -> DETACHED_EXECUTION_EVIDENCED
        ok_verdict = _v()
        assert ok_verdict["f96_02_evidence_state"] == "DETACHED_EXECUTION_EVIDENCED"
        assert ok_verdict["f97_01_verified_statement_identity_bound"] is True
        assert ok_verdict["f98_01_gh_binary_baseline_qualified"] is True

        # 2. 1-byte tampered receipt -> SubjectDigestMismatch blocked
        rp_bad = td_p / "tampered_receipt.json"
        rp_bad.write_bytes(rec_bytes + b" ")
        try:
            _v(r_arg=rp_bad)
            raise AssertionError("Failed to reject 1-byte tampered receipt")
        except RuntimeError:
            pass

        # 3. Valid signature, wrong repo / workflow / commit / run_id / prefix / Fulcio cert commit or runInvocationURI
        for bad_case in (
            ("other-org/campus-audit", good_wf, good_commit, good_run_id, None, None),
            (good_repo, ".github/workflows/other.yml", good_commit, good_run_id, None, None),
            (good_repo, good_wf, "c" * 40, good_run_id, None, None),
            (good_repo, good_wf, good_commit, "111111", None, None),
            (good_repo, good_wf, good_commit, good_run_id, "d" * 40, None),
            (good_repo, good_wf, good_commit, good_run_id, None, f"https://github.com/{good_repo}/actions/runs/777777/attempts/1"),
        ):
            s_b, e_b, b_b = _mk_stmt_and_env(
                rec_sha, bad_case[0], bad_case[1], bad_case[2], bad_case[3], sig_tag="sig-wrong-claim"
            )
            bp.write_bytes(b_b)
            gh_out_p.write_text(
                json.dumps([_mk_gh_entry(s_b, e_b, cert_commit=bad_case[4], cert_run_inv=bad_case[5])]),
                encoding="utf-8",
            )
            try:
                _v()
                raise AssertionError(f"Failed to reject signed wrong-claim statement: {bad_case}")
            except RuntimeError:
                pass
        bp.write_bytes(bundle_good)
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_good)]), encoding="utf-8")
        try:
            _v(run_arg="98")
            raise AssertionError("Failed to reject prefix run_id '98'")
        except RuntimeError:
            pass

        # 4. Split-brain unsigned Statement A + signed wrong-claim Statement B -> blocked in BOTH modes
        _, _, unsigned_matching_line = _mk_stmt_and_env(
            rec_sha, good_repo, good_wf, good_commit, good_run_id, sig_tag="unsigned-forged"
        )
        stmt_signed_wrong, env_signed_wrong, signed_wrong_line = _mk_stmt_and_env(
            rec_sha, good_repo, good_wf, good_commit, "111111", sig_tag="sig-other-run"
        )
        bp.write_bytes(unsigned_matching_line + signed_wrong_line)
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_signed_wrong, env_signed_wrong)]), encoding="utf-8")
        for allow_extra in (False, True):
            try:
                _v(allow_extra=allow_extra)
                raise AssertionError("Split-brain accepted")
            except RuntimeError:
                pass

        # 5. Unsigned sidecar appended next to valid signed Statement -> blocked in default strict mode
        _, _, unsigned_sidecar_line = _mk_stmt_and_env(
            rec_sha, "attacker/repo", good_wf, "e" * 40, "222222", sig_tag="unsigned-sidecar"
        )
        bp.write_bytes(bundle_good + unsigned_sidecar_line)
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_good)]), encoding="utf-8")
        try:
            _v(allow_extra=False)
            raise AssertionError("Failed to reject unverified sidecar")
        except RuntimeError:
            pass

        # 6. Multiple verified attestations where exactly one verified object (`B2` at index 1) matches all claims
        bp.write_bytes(signed_wrong_line + bundle_good)
        gh_out_p.write_text(
            json.dumps([
                _mk_gh_entry(stmt_signed_wrong, env_signed_wrong),
                _mk_gh_entry(stmt_good, env_good),
            ]),
            encoding="utf-8",
        )
        multi_ok = _v()
        assert multi_ok["f97_01_bound_gh_verification"]["bound_verified_attestation"]["matched_bundle_line_index"] == 1

        # 7. Chimera split-claims across TWO valid signatures -> blocked
        stmt_c1, env_c1, line_c1 = _mk_stmt_and_env(
            rec_sha, good_repo, good_wf, good_commit, "111111", sig_tag="sig-chimera-1"
        )
        stmt_c2, env_c2, line_c2 = _mk_stmt_and_env(
            rec_sha, good_repo, good_wf, "f" * 40, good_run_id, sig_tag="sig-chimera-2"
        )
        bp.write_bytes(line_c1 + line_c2)
        gh_out_p.write_text(
            json.dumps([_mk_gh_entry(stmt_c1, env_c1), _mk_gh_entry(stmt_c2, env_c2)]), encoding="utf-8"
        )
        try:
            _v()
            raise AssertionError("Failed to reject chimera split claims")
        except RuntimeError:
            pass

        # 8. `gh attestation verify` Statement differs from parsed `.jsonl` DSSE -> blocked
        stmt_alt, env_alt, _ = _mk_stmt_and_env(
            rec_sha, good_repo, good_wf, good_commit, good_run_id, sig_tag="sig-alt", extra_note="different"
        )
        bp.write_bytes(bundle_good)
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_alt, env_alt)]), encoding="utf-8")
        try:
            _v()
            raise AssertionError("Failed to reject gh vs .jsonl DSSE mismatch")
        except RuntimeError:
            pass

        # 9. Internal disagreement inside `gh` JSON between `verificationResult.statement` & `dsseEnvelope.payload`
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_alt)]), encoding="utf-8")
        try:
            _v()
            raise AssertionError("Failed to reject internal gh envelope vs statement mismatch")
        except RuntimeError:
            pass

        # 10. Malformed `gh` JSON missing `verificationResult.statement`
        gh_out_p.write_text(json.dumps([{"attestation": {"bundle": {"dsseEnvelope": env_good}}}]), encoding="utf-8")
        try:
            _v()
            raise AssertionError("Failed to reject malformed gh JSON schema")
        except RuntimeError:
            pass

        # 11. Unverified parse-only mode without `gh` binary never promotes
        orig_which = shutil.which
        shutil.which = lambda _name: None  # type: ignore[assignment]
        try:
            res_unverified = verify_bundle_end_to_end(
                rp, bp, good_repo, good_wf, good_commit, good_run_id, require_cryptographic_gh_verify=False
            )
            assert (
                res_unverified["f96_02_evidence_state"]
                == "DSSE_CLAIMS_PARSED_SIGNATURE_UNVERIFIED_NOT_EVIDENCED"
            )
            try:
                verify_bundle_end_to_end(
                    rp, bp, good_repo, good_wf, good_commit, good_run_id, require_cryptographic_gh_verify=True
                )
                raise AssertionError("Failed to block promotion when gh binary is absent")
            except RuntimeError:
                pass
        finally:
            shutil.which = orig_which  # type: ignore[assignment]

        # 12. Wrong `--expected-gh-sha256` pin MUST fail
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_good)]), encoding="utf-8")
        try:
            _v(exp_gh="0" * 64)
            raise AssertionError("Failed to reject mismatched --expected-gh-sha256")
        except RuntimeError:
            pass

        # 13. Go `protojson` omitted empty `keyid` compatibility + 1-byte signature swap rejection
        env_go_protojson = {
            "payloadType": env_good["payloadType"],
            "payload": env_good["payload"],
            "signatures": [{"sig": env_good["signatures"][0]["sig"]}],
        }
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_go_protojson)]), encoding="utf-8")
        assert _v()["f97_01_verified_statement_identity_bound"] is True

        env_sig_swapped = {
            "payloadType": env_good["payloadType"],
            "payload": env_good["payload"],
            "signatures": [{"sig": base64.b64encode(b"different-sig-bytes").decode("ascii")}],
        }
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_sig_swapped)]), encoding="utf-8")
        try:
            _v()
            raise AssertionError("Failed to reject swapped DSSE signature bytes")
        except RuntimeError:
            pass

        # 14. F98-01 non-tautological gh binary pin guard: unpinned binary rejected by default,
        #     and downgraded to SIGNATURE_VERIFIED_WITH_UNPINNED_GH_TCB_NOT_QUALIFIED if explicitly allowed!
        gh_out_p.write_text(json.dumps([_mk_gh_entry(stmt_good, env_good)]), encoding="utf-8")
        try:
            _v(exp_gh=None, allow_unpinned=False)
            raise AssertionError("Failed to block unpinned non-v2.67.0 gh binary by default")
        except RuntimeError:
            pass
        downgraded = _v(exp_gh=None, allow_unpinned=True)
        assert downgraded["f96_02_evidence_state"] == "SIGNATURE_VERIFIED_WITH_UNPINNED_GH_TCB_NOT_QUALIFIED"
        assert downgraded["f98_01_gh_binary_baseline_qualified"] is False

    return {
        "f96_bundle_self_tests_passed": 14,
        "f97_01_bundle_self_tests_passed": 14,
        "f98_01_bundle_self_tests_passed": 14,
        "pinned_gh_verify_json_schema": PINNED_GH_VERIFY_JSON_SCHEMA,
        "pinned_official_gh_release_tag": PINNED_OFFICIAL_GH_RELEASE_TAG,
        "pinned_official_gh_platform_count": len(PINNED_OFFICIAL_GH_V2_67_0_BINARIES),
        "subject_digest_tampering_blocked": True,
        "repo_workflow_commit_runid_mismatches_blocked": True,
        "unsigned_dsse_json_promotion_blocked": True,
        "f97_01_signed_wrong_claim_blocked": True,
        "f97_01_unsigned_side_by_side_split_brain_blocked": True,
        "f97_01_multi_attestation_single_verified_match_bound": True,
        "f97_01_multi_attestation_chimera_split_blocked": True,
        "f97_01_gh_output_vs_parsed_dsse_mismatch_blocked": True,
        "f97_01_gh_tcb_binary_hash_pin_enforced": True,
        "f97_01_protojson_signature_normalization_and_swap_guard_verified": True,
        "f98_01_unpinned_gh_binary_rejected_or_downgraded": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="F96-02 / F97-01 / F98-01-02 post-CI Sigstore/SLSA provenance bundle verifier."
    )
    for flag in (
        "--self-test-f96-bundle-guards",
        "--self-test-f97-bundle-guards",
        "--self-test-f98-bundle-guards",
    ):
        parser.add_argument(flag, action="store_true", help="Run deterministic bundle guard self-tests.")
    parser.add_argument(
        "--run-f98-02-real-sigstore-integration",
        action="store_true",
        help="Run live F98-02 cryptographic integration suite with pinned gh v2.67.0 + real Sigstore bundle.",
    )
    parser.add_argument("--receipt", type=Path, help="Path to F96_DETACHED_AUDIT_RECEIPT.json (or real artifact)")
    parser.add_argument("--sigstore-bundle", type=Path, help="Path to Sigstore attestation .jsonl bundle")
    parser.add_argument("--secondary-sigstore-bundle", type=Path, default=None)
    parser.add_argument("--expected-repo", type=str, help="Expected 'owner/repo'")
    parser.add_argument(
        "--expected-workflow-path",
        type=str,
        default=".github/workflows/f94_github_actions_third_party_lean46.yml",
    )
    parser.add_argument("--expected-commit-sha", type=str, help="Expected 40-char lowercase git commit SHA")
    parser.add_argument("--expected-run-id", type=str, help="Expected numeric GitHub Actions run ID")
    parser.add_argument("--custom-trusted-root", type=Path, default=None)
    parser.add_argument("--gh-bin", type=Path, default=None, help="Optional explicit path to gh CLI binary")
    parser.add_argument(
        "--expected-gh-sha256",
        type=str,
        default=None,
        help="Optional reviewer-approved 64-hex SHA-256 baseline for gh CLI binary (defaults to v2.67.0 allowlist)",
    )
    parser.add_argument("--allow-extra-unverified-bundle-lines", action="store_true")
    parser.add_argument("--allow-unpinned-gh-binary", action="store_true")
    parser.add_argument("--output-verdict", type=Path, default=None)
    args = parser.parse_args()

    if (
        args.self_test_f96_bundle_guards
        or args.self_test_f97_bundle_guards
        or args.self_test_f98_bundle_guards
    ):
        print(json.dumps(run_f97_bundle_self_tests(), indent=2, sort_keys=True))
        return

    if args.run_f98_02_real_sigstore_integration:
        for req in (
            "gh_bin",
            "receipt",
            "sigstore_bundle",
            "custom_trusted_root",
            "expected_repo",
            "expected_commit_sha",
            "expected_run_id",
        ):
            if getattr(args, req) is None:
                parser.error(f"--{req.replace('_', '-')} is required for --run-f98-02-real-sigstore-integration")
        res = run_f98_02_real_sigstore_integration(
            gh_bin_path=args.gh_bin,
            real_artifact_path=args.receipt,
            real_bundle_path=args.sigstore_bundle,
            secondary_real_bundle_path=args.secondary_sigstore_bundle,
            custom_trusted_root=args.custom_trusted_root,
            expected_repo=args.expected_repo,
            expected_workflow_path=args.expected_workflow_path,
            expected_commit_sha=args.expected_commit_sha,
            expected_run_id=args.expected_run_id,
        )
        rendered = json.dumps(res, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        if args.output_verdict is not None:
            args.output_verdict.parent.mkdir(parents=True, exist_ok=True)
            args.output_verdict.write_bytes(rendered.encode("utf-8"))
        print(rendered, end="")
        return

    for req in ("receipt", "sigstore_bundle", "expected_repo", "expected_commit_sha", "expected_run_id"):
        if getattr(args, req) is None:
            parser.error(f"--{req.replace('_', '-')} is required")

    out = verify_bundle_end_to_end(
        receipt_path=args.receipt,
        sigstore_bundle_path=args.sigstore_bundle,
        expected_repo=args.expected_repo,
        expected_workflow_path=args.expected_workflow_path,
        expected_commit_sha=args.expected_commit_sha,
        expected_run_id=args.expected_run_id,
        require_cryptographic_gh_verify=True,
        custom_trusted_root=args.custom_trusted_root,
        gh_bin_override=args.gh_bin,
        expected_gh_sha256=args.expected_gh_sha256,
        allow_extra_unverified_bundle_lines=args.allow_extra_unverified_bundle_lines,
        allow_unpinned_gh_binary=args.allow_unpinned_gh_binary,
    )
    rendered = json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.output_verdict is not None:
        args.output_verdict.parent.mkdir(parents=True, exist_ok=True)
        args.output_verdict.write_bytes(rendered.encode("utf-8"))
    print(rendered, end="")


if __name__ == "__main__":
    main()
