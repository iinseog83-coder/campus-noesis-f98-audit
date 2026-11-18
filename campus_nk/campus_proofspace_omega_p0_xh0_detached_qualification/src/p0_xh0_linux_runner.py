#!/usr/bin/env python3
"""P0-XH0 External Detached Multi-Host Linux Runner (`CAMPUS-PROOFSPACE-Ω-P0-XH0`).

Authorization Token:
  `CAMPUS_PROOFSPACE_OMEGA_P0_XH0_SCOPED_EXTERNAL_REPLAY_AUTHORIZED__R2_SOURCE_FROZEN__LEAN4331_AND_FOUR_MUTATIONS_ONLY__SIGSTORE_AND_SOURCE_BOUND_ATTESTATION_REQUIRED__F_R2_01_03_HELD__P1_E1D_RELEASE47_NOT_AUTHORIZED`

Implements Gates `XH0-G1`..`XH0-G5` on GitHub Actions `ubuntu-24.04` with official
`Lean 4.33.1` (`lean-4.33.1-linux.tar.zst`, `SHA-256 = 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`),
producing `P0_XH0_SIGNED_PROVENANCE.json` for Sigstore OIDC / Fulcio / Rekor attestation (`XH0-G6`).
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Dict, List, Mapping, Optional, Tuple
import zipfile

STAGE_ID = "CAMPUS_PROOFSPACE_OMEGA_P0_XH0_EXTERNAL_MULTI_HOST_QUALIFICATION"
IN_CI_STATE_CEILING = "EXTERNAL_REPLAYED_ATTESTATION_HELD"

PINNED_R2_BUNDLE_SHA256 = "f3a07777e9a067b0fa369fdddeacdca7df553c4a33ac4df8b387d02bd1f97a6b"
PINNED_R2_BUNDLE_SIZE = 183199
PINNED_R2_RECEIPT_SHA256 = "a0e64bbd706cb7e0c917f2a69860368fab4b99164fa17edb0ddbece8d6bfb3eb"
PINNED_R2_RECEIPT_PAYLOAD_SHA256 = "1e22db4c2baba4ba43b345c1282fff6c87ab48bb224cf37523921b40ae22ab3c"

PINNED_P0_V1_SHA256 = "2d5076cd60f3e22b912d8e236880a472298336ebbde452486ca4556844e3da1f"
PINNED_P0_V1_SIZE = 55616
PINNED_P0_T1_R1_SHA256 = "e17f719d761cd02d813fd778a723c5f934b837734c3c2cad1bfc13ca68c4a643"
PINNED_P0_T1_R1_SIZE = 96081

PINNED_T104_PACK_SHA256 = "71091172fbb4ba1ddccf05ea5694ed9df049057b5eeb8f7de97c199ce581f1b1"
PINNED_T104_PACK_SIZE = 650086
PINNED_T105_RECEIPT_SHA256 = "cb03ec9ee02eb2fe666a918bd874fa0d1258191f5c3103e9ed29969129339dcb"
PINNED_T105_RECEIPT_SIZE = 6489

PINNED_ANCESTORS_IN_T104_PACK: Dict[str, Tuple[int, str]] = {
    "readonly_ancestors/CAMPUS_NOESIS_OMEGA_KAPPA_STAGE1_0_PURE_TRUSTED_CHECKER_PACKAGE.zip": (
        100029,
        "93d9a02a84d6d91a36140de2c96cb362e26aa1b2c595ca3ac9562ddf8e3426bb",
    ),
    "readonly_ancestors/CAMPUS_NOESIS_OMEGA_LAMBDA_W2_OUTER_PACKET_AND_SNAPSHOT_REFINEMENT_PACKAGE.zip": (
        236214,
        "4c42f12b605083d13228c02c84e12b4689cdf32be0f507041b6a36360eec4608",
    ),
    "readonly_ancestors/OMEGA_LAMBDA_E1_CORE_AUX_BUNDLE.zip": (
        190589,
        "38a055f39e259cac333b469bfb4602ed8b3859cb5f6bfa3e096a75be0200da39",
    ),
    "readonly_ancestors/F99_DETACHED_CI_RUN_44121693289_EVIDENCE_BUNDLE.zip": (
        75053,
        "26310ec2154d760a77fb2c8a764ba2fbc5c0ede092e4616e0b840f1db8ac311f",
    ),
    "readonly_ancestors/F100_TRIBUNAL_100TH_INDEPENDENT_REPLAY_RECEIPT.json": (
        5453,
        "e7cfb738c45071f67e7a56e39c87613197a5e65c9abf95368f2b47b9d7477298",
    ),
}

PINNED_LINUX_TAR_SHA256 = "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
PINNED_LINUX_TAR_SIZE = 570405234
PINNED_LEAN_VERSION = "4.33.1"
PINNED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"

ORDERED_R2_MODULES: Tuple[Tuple[str, str], ...] = (
    ("ProofspaceOmegaP0R2.CoreInheritedR1", "ProofspaceOmegaP0R2/CoreInheritedR1.lean"),
    ("ProofspaceOmegaP0R2.ProofCarryingEvidenceR2", "ProofspaceOmegaP0R2/ProofCarryingEvidenceR2.lean"),
    ("ProofspaceOmegaP0R2.BoundResurrectionStateR2", "ProofspaceOmegaP0R2/BoundResurrectionStateR2.lean"),
    ("ProofspaceOmegaP0R2.R2ControlsAndCounterexamples", "ProofspaceOmegaP0R2/R2ControlsAndCounterexamples.lean"),
    ("ProofspaceOmegaP0R2.P0R2AxiomAudit", "ProofspaceOmegaP0R2/P0R2AxiomAudit.lean"),
    ("ProofspaceOmegaP0R2", "ProofspaceOmegaP0R2.lean"),
)

SMAP_R2_INSPECTOR = r"""import ProofspaceOmegaP0R2
import r2_independent_clean_sheet_probe
import Lean

open Lean

def isR2Target : Name → Bool
  | .anonymous => false
  | .str .anonymous s => s == "ProofspaceOmegaP0R2" || s == "P0R2IndependentCleanSheetProbe"
  | .str p _ => isR2Target p
  | .num p _ => isR2Target p

#eval show MetaM Unit from do
  let env ← getEnv
  let mut consts : Nat := 0
  let mut thms : Nat := 0
  let mut sorryCnt : Nat := 0
  let mut userAxCnt : Nat := 0
  let mut opaqueCnt : Nat := 0
  let mut reduceBoolCnt : Nat := 0
  for (nm, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if isR2Target nm then
      consts := consts + 1
      match ci with
      | .thmInfo _ => thms := thms + 1
      | .axiomInfo _ => userAxCnt := userAxCnt + 1
      | .opaqueInfo _ => opaqueCnt := opaqueCnt + 1
      | _ => pure ()
      for u in ci.getUsedConstantsAsSet.toList do
        if u == ``sorryAx then sorryCnt := sorryCnt + 1
        if u == ``Lean.ofReduceBool || u == ``Lean.trustCompiler then
          reduceBoolCnt := reduceBoolCnt + 1
  IO.println s!"P0_XH0_SMAP|constants={consts}|theorems={thms}|sorry={sorryCnt}|userAxioms={userAxCnt}|opaque={opaqueCnt}|reduceBool={reduceBoolCnt}"
"""


class P0XH0Error(RuntimeError):
    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode("utf-8")


def seal_json(payload: Mapping[str, Any]) -> Dict[str, Any]:
    body = {k: v for k, v in payload.items() if k != "seal"}
    out = dict(body)
    out["seal"] = {
        "algorithm": "SHA-256",
        "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
        "payload_sha256": sha256_hex(canonical_json_bytes(body)),
    }
    return out


def find_lean_bin(explicit: Optional[str] = None) -> Optional[Path]:
    if explicit:
        p = Path(explicit)
        return p if p.is_file() else None
    w = shutil.which("lean")
    if w:
        return Path(w)
    cand = Path.home() / ".elan" / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    return cand if cand.is_file() else None


def validate_lean_version_string(ver_text: str) -> bool:
    return (PINNED_LEAN_VERSION in ver_text) and (PINNED_LEAN_COMMIT in ver_text)


def verify_r2_bundle_bytes(raw_r2_zip: bytes) -> Tuple[Dict[str, bytes], Dict[str, Any]]:
    if len(raw_r2_zip) != PINNED_R2_BUNDLE_SIZE or sha256_hex(raw_r2_zip) != PINNED_R2_BUNDLE_SHA256:
        raise P0XH0Error(
            "ERR_P0_XH0_G1_R2_BUNDLE_HASH_MISMATCH",
            f"Expected {PINNED_R2_BUNDLE_SIZE}/{PINNED_R2_BUNDLE_SHA256}, got {len(raw_r2_zip)}/{sha256_hex(raw_r2_zip)}",
        )
    with zipfile.ZipFile(io.BytesIO(raw_r2_zip), "r") as zf:
        bad = zf.testzip()
        if bad is not None:
            raise P0XH0Error("ERR_P0_XH0_G1_CORRUPT_ZIP", f"CRC failure on {bad}")
        entries = {inf.filename: zf.read(inf.filename) for inf in zf.infolist()}
    if len(entries) != 13:
        raise P0XH0Error("ERR_P0_XH0_G1_ENTRY_COUNT", f"Expected 13 entries, got {len(entries)}")

    # Check embedded P0 v1 and P0-T1/R1
    v1_raw = entries["readonly_p0_lineage/CAMPUS_PROOFSPACE_OMEGA_P0_STATIC_FOUNDATION_BUNDLE.zip"]
    r1_raw = entries["readonly_p0_lineage/CAMPUS_PROOFSPACE_OMEGA_P0_T1_AND_R1_COMPLETE_BUNDLE.zip"]
    if len(v1_raw) != PINNED_P0_V1_SIZE or sha256_hex(v1_raw) != PINNED_P0_V1_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G1_P0_V1_MISMATCH", "Embedded P0 v1 mismatch")
    if len(r1_raw) != PINNED_P0_T1_R1_SIZE or sha256_hex(r1_raw) != PINNED_P0_T1_R1_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G1_P0_R1_MISMATCH", "Embedded P0-T1/R1 mismatch")

    rcpt_raw = entries["ledger/P0_R2_SCOPED_REMEDIATION_RECEIPT.json"]
    if sha256_hex(rcpt_raw) != PINNED_R2_RECEIPT_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G1_RECEIPT_HASH_MISMATCH", "Embedded R2 receipt hash mismatch")
    rcpt_obj = json.loads(rcpt_raw.decode("utf-8"))
    body = {k: v for k, v in rcpt_obj.items() if k != "seal"}
    if sha256_hex(canonical_json_bytes(body)) != PINNED_R2_RECEIPT_PAYLOAD_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G1_RECEIPT_PAYLOAD_MISMATCH", "Embedded R2 payload hash mismatch")

    # Source Binding: verify every Lean module and probe byte-for-byte against Windows R2 receipt
    expected_src_hashes = rcpt_obj["self_contained_offline_audit"]["r2_source_sha256"]
    for mod_name, rel in ORDERED_R2_MODULES:
        actual_h = sha256_hex(entries[f"lean_r2/{rel}"])
        if actual_h != expected_src_hashes[mod_name]:
            raise P0XH0Error("ERR_P0_XH0_G1_SOURCE_BINDING_MISMATCH", f"Mismatch on {mod_name}")
    probe_h = sha256_hex(entries["probes/r2_independent_clean_sheet_probe.lean"])
    if probe_h != expected_src_hashes["P0R2IndependentCleanSheetProbe"]:
        raise P0XH0Error("ERR_P0_XH0_G1_PROBE_BINDING_MISMATCH", "Mismatch on clean-sheet probe")

    return entries, rcpt_obj


def verify_ancestor_lineage(
    t104_pack_path: Optional[Path],
    t105_receipt_path: Optional[Path],
) -> Dict[str, Any]:
    if t104_pack_path is None or t105_receipt_path is None or (not t104_pack_path.is_file()) or (not t105_receipt_path.is_file()):
        return {
            "verdict": "EVIDENCE_UNAVAILABLE",
            "reason": "Ancestor archives not mounted in this invocation",
            "records": {},
        }
    t104_raw = t104_pack_path.read_bytes()
    if len(t104_raw) != PINNED_T104_PACK_SIZE or sha256_hex(t104_raw) != PINNED_T104_PACK_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G5_T104_MISMATCH", "T104 pack digest mismatch")
    t105_raw = t105_receipt_path.read_bytes()
    if len(t105_raw) != PINNED_T105_RECEIPT_SIZE or sha256_hex(t105_raw) != PINNED_T105_RECEIPT_SHA256:
        raise P0XH0Error("ERR_P0_XH0_G5_T105_MISMATCH", "T105 closure receipt digest mismatch")

    records: Dict[str, Any] = {
        "t104_pack": {"size_bytes": len(t104_raw), "sha256": sha256_hex(t104_raw)},
        "t105_closure_receipt": {"size_bytes": len(t105_raw), "sha256": sha256_hex(t105_raw)},
    }
    with zipfile.ZipFile(io.BytesIO(t104_raw), "r") as zf:
        if zf.testzip() is not None:
            raise P0XH0Error("ERR_P0_XH0_G5_T104_CRC", "Corrupt T104 pack")
        for zpath, (exp_sz, exp_sha) in PINNED_ANCESTORS_IN_T104_PACK.items():
            blob = zf.read(zpath)
            if len(blob) != exp_sz or sha256_hex(blob) != exp_sha:
                raise P0XH0Error("ERR_P0_XH0_G5_ANCESTOR_MISMATCH", f"Mismatch on {zpath}")
            records[zpath] = {"size_bytes": len(blob), "sha256": sha256_hex(blob)}

    return {
        "verdict": "ANCESTOR_LINEAGE_HASH_VERIFIED",
        "records": records,
    }


def _run_mutation(
    lean_bin: Path,
    extracted_lean_r2: Path,
    rel_target: str,
    old_s: str,
    new_s: str,
) -> Tuple[bool, int]:
    with tempfile.TemporaryDirectory(prefix="p0_xh0_mut_") as td:
        tp = Path(td)
        scp = tp / "lean_r2"
        bld = tp / "bld"
        shutil.copytree(extracted_lean_r2, scp)
        (bld / "ProofspaceOmegaP0R2").mkdir(parents=True, exist_ok=True)
        tf = scp / rel_target
        orig = tf.read_text(encoding="utf-8")
        mut = orig.replace(old_s, new_s, 1)
        if mut == orig:
            raise P0XH0Error("ERR_P0_XH0_G4_MUTATION_TARGET", f"Target snippet missing in {rel_target}")
        tf.write_text(mut, encoding="utf-8")
        env = dict(os.environ)
        env["LEAN_PATH"] = str(bld)
        for _, rel in ORDERED_R2_MODULES[:4]:
            p = subprocess.run(
                [str(lean_bin), "-o", str(bld / Path(rel).with_suffix(".olean")), rel],
                cwd=str(scp),
                capture_output=True,
                text=True,
                env=env,
                check=False,
            )
            if p.returncode != 0:
                return (True, p.returncode)
        return (False, 0)


def run_xh0_qualification(
    r2_bundle_path: Path,
    out_dir: Path,
    t104_pack_path: Optional[Path] = None,
    t105_receipt_path: Optional[Path] = None,
    lean_archive_path: Optional[Path] = None,
    require_lean_archive: bool = False,
    explicit_lean_bin: Optional[str] = None,
) -> Dict[str, Any]:
    runner_self_path = Path(__file__).resolve()
    pre_hashes: Dict[str, Any] = {
        "r2_bundle": {"size_bytes": r2_bundle_path.stat().st_size, "sha256": sha256_hex(r2_bundle_path.read_bytes())},
        "p0_xh0_linux_runner_py": {"size_bytes": runner_self_path.stat().st_size, "sha256": sha256_hex(runner_self_path.read_bytes())},
    }
    if t104_pack_path and t104_pack_path.is_file():
        pre_hashes["t104_pack"] = {"size_bytes": t104_pack_path.stat().st_size, "sha256": sha256_hex(t104_pack_path.read_bytes())}
    if t105_receipt_path and t105_receipt_path.is_file():
        pre_hashes["t105_closure_receipt"] = {
            "size_bytes": t105_receipt_path.stat().st_size,
            "sha256": sha256_hex(t105_receipt_path.read_bytes()),
        }

    # Gate XH0-G1: Source & Bundle Binding
    raw_r2_zip = r2_bundle_path.read_bytes()
    r2_entries, windows_r2_receipt = verify_r2_bundle_bytes(raw_r2_zip)

    # Gate XH0-G2: Toolchain & Archive Verification
    lean_archive_doc: Dict[str, Any] = {"status": "NOT_PROVIDED"}
    if lean_archive_path is not None and lean_archive_path.is_file():
        arch_sz = lean_archive_path.stat().st_size
        arch_h = hashlib.sha256()
        with lean_archive_path.open("rb") as fh:
            while True:
                chunk = fh.read(1024 * 1024)
                if not chunk:
                    break
                arch_h.update(chunk)
        arch_sha = arch_h.hexdigest()
        if arch_sz != PINNED_LINUX_TAR_SIZE or arch_sha != PINNED_LINUX_TAR_SHA256:
            raise P0XH0Error("ERR_P0_XH0_G2_LEAN_TAR_MISMATCH", f"Got {arch_sz}/{arch_sha}")
        lean_archive_doc = {
            "archive_name": lean_archive_path.name,
            "size_bytes": arch_sz,
            "sha256": arch_sha,
            "status": "VERIFIED_OFFICIAL_RELEASE_TARBALL",
        }
    elif require_lean_archive:
        raise P0XH0Error("ERR_P0_XH0_G2_LEAN_TAR_MISSING", "Official Lean tarball required")

    lean_bin = find_lean_bin(explicit_lean_bin)
    if lean_bin is None:
        raise P0XH0Error("ERR_P0_XH0_G2_LEAN_BIN_MISSING", "Lean binary not found")
    ver_proc = subprocess.run([str(lean_bin), "--version"], capture_output=True, text=True, check=False)
    ver_full = (ver_proc.stdout + "\n" + ver_proc.stderr).strip()
    if not validate_lean_version_string(ver_full):
        raise P0XH0Error("ERR_P0_XH0_G2_LEAN_VERSION_MISMATCH", ver_full)
    lean_bin_sha256 = sha256_hex(lean_bin.read_bytes())

    # Extract P0-R2 into isolated temp directory, compile 7/7 modules, run SMap & Axiom Parity (XH0-G2 & G3),
    # run 4/4 live mutations (XH0-G4), and run extracted unit tests
    with tempfile.TemporaryDirectory(prefix="p0_xh0_exec_") as td:
        tp = Path(td)
        ext_root = tp / "r2_extracted"
        with zipfile.ZipFile(io.BytesIO(raw_r2_zip), "r") as zf:
            zf.extractall(ext_root)

        src_cp = tp / "clean_compile"
        bld = tp / "build"
        shutil.copytree(ext_root / "lean_r2", src_cp)
        shutil.copy2(ext_root / "probes" / "r2_independent_clean_sheet_probe.lean", src_cp / "r2_independent_clean_sheet_probe.lean")
        (bld / "ProofspaceOmegaP0R2").mkdir(parents=True, exist_ok=True)
        env = dict(os.environ)
        env["LEAN_PATH"] = str(bld)

        axiom_stdout = ""
        compiled_olean_digests: Dict[str, str] = {}
        for mod_name, rel in ORDERED_R2_MODULES:
            out_ol = bld / Path(rel).with_suffix(".olean")
            p = subprocess.run(
                [str(lean_bin), "-o", str(out_ol), rel],
                cwd=str(src_cp),
                capture_output=True,
                text=True,
                env=env,
                check=False,
            )
            if p.returncode != 0:
                raise P0XH0Error("ERR_P0_XH0_G2_COMPILE_FAIL", f"{mod_name}: {p.stdout} {p.stderr}")
            compiled_olean_digests[mod_name] = sha256_hex(out_ol.read_bytes())
            if mod_name == "ProofspaceOmegaP0R2.P0R2AxiomAudit":
                axiom_stdout = p.stdout

        p_probe = subprocess.run(
            [str(lean_bin), "-o", str(bld / "r2_independent_clean_sheet_probe.olean"), "r2_independent_clean_sheet_probe.lean"],
            cwd=str(src_cp),
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        if p_probe.returncode != 0:
            raise P0XH0Error("ERR_P0_XH0_G2_PROBE_FAIL", p_probe.stdout + p_probe.stderr)
        compiled_olean_digests["P0R2IndependentCleanSheetProbe"] = sha256_hex(
            (bld / "r2_independent_clean_sheet_probe.olean").read_bytes()
        )

        # Gate XH0-G3: 15/15 Core Theorem Axiom Parity against frozen Windows receipt
        linux_axioms: Dict[str, List[str]] = {}
        for m in re.finditer(
            r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]+)\])",
            axiom_stdout,
            flags=re.DOTALL,
        ):
            tnm = m.group(1).strip()
            if m.group(2) is not None:
                linux_axioms[tnm] = []
            else:
                linux_axioms[tnm] = sorted(
                    a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip()
                )

        win_axioms_raw = windows_r2_receipt["lean_cleanroom_and_mutation_audit"]["theorem_axiom_footprints"]
        win_axioms = {k: sorted(v) for k, v in win_axioms_raw.items()}
        if linux_axioms != win_axioms or len(linux_axioms) != 15:
            raise P0XH0Error(
                "ERR_P0_XH0_G3_AXIOM_PARITY_MISMATCH",
                f"Linux {linux_axioms} != Windows {win_axioms}",
            )

        # SMap parity check
        insp_f = src_cp / "XH0SMapInspector.lean"
        insp_f.write_text(SMAP_R2_INSPECTOR, encoding="utf-8")
        p_insp = subprocess.run(
            [str(lean_bin), "XH0SMapInspector.lean"],
            cwd=str(src_cp),
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        if p_insp.returncode != 0:
            raise P0XH0Error("ERR_P0_XH0_G2_SMAP_FAIL", p_insp.stdout + p_insp.stderr)
        smap_ln = next((ln.strip() for ln in p_insp.stdout.splitlines() if ln.startswith("P0_XH0_SMAP|")), "")
        if not smap_ln:
            raise P0XH0Error("ERR_P0_XH0_G2_SMAP_MISSING", p_insp.stdout)
        linux_smap = {k: int(v) for k, v in (seg.split("=", 1) for seg in smap_ln.split("|")[1:])}
        win_smap = windows_r2_receipt["lean_cleanroom_and_mutation_audit"]["smap_metrics"]
        if linux_smap != win_smap:
            raise P0XH0Error("ERR_P0_XH0_G2_SMAP_PARITY_MISMATCH", f"Linux {linux_smap} != Windows {win_smap}")

        # Gate XH0-G4: 4/4 Pre-Locked Lean Source Mutations + Unit Tests + 2 In-CI Guard Probes
        lean_r2_extracted = ext_root / "lean_r2"
        c1, rc1 = _run_mutation(
            lean_bin,
            lean_r2_extracted,
            "ProofspaceOmegaP0R2/BoundResurrectionStateR2.lean",
            "(cand.targetSeedId == seed.seedId) &&",
            "true &&",
        )
        c2, rc2 = _run_mutation(
            lean_bin,
            lean_r2_extracted,
            "ProofspaceOmegaP0R2/BoundResurrectionStateR2.lean",
            "!(P.consumedReceipts.any (fun rid => rid == raw.receiptId))",
            "true",
        )
        c3, rc3 = _run_mutation(
            lean_bin,
            lean_r2_extracted,
            "ProofspaceOmegaP0R2/ProofCarryingEvidenceR2.lean",
            "reg.issuers.any (verifyIssuerRecordBool raw)",
            "raw.untrustedClaimedSourceOk",
        )
        c4, rc4 = _run_mutation(
            lean_bin,
            lean_r2_extracted,
            "ProofspaceOmegaP0R2/BoundResurrectionStateR2.lean",
            "| none =>\n        { positiveTruthCredit := 0, prioritizesSearchOnly := true, boundSpecHash := spec.specHash }",
            "| none =>\n        { positiveTruthCredit := if _untrustedClaimedKernelAccepted then 1 else 0, prioritizesSearchOnly := true, boundSpecHash := spec.specHash }",
        )
        mutations_g4 = [
            {"id": "M_R2_LEAN_11A", "caught": c1, "exit_code": rc1},
            {"id": "M_R2_LEAN_11B", "caught": c2, "exit_code": rc2},
            {"id": "M_R2_LEAN_12A", "caught": c3, "exit_code": rc3},
            {"id": "M_R2_LEAN_12B", "caught": c4, "exit_code": rc4},
        ]
        if not all(m["caught"] for m in mutations_g4):
            raise P0XH0Error("ERR_P0_XH0_G4_MUTATION_ESCAPED", str(mutations_g4))

        # Run extracted P0-R2 unit test suite with P0_R2_LEAN_BIN pointed to lean_bin
        ut_env = dict(os.environ)
        ut_env["P0_R2_LEAN_BIN"] = str(lean_bin)
        ut_proc = subprocess.run(
            [sys.executable, "-m", "unittest", "discover", "-s", str(ext_root / "tests"), "-v"],
            capture_output=True,
            text=True,
            env=ut_env,
            check=False,
        )
        if ut_proc.returncode != 0:
            raise P0XH0Error("ERR_P0_XH0_G4_UNITTEST_FAIL", ut_proc.stdout + ut_proc.stderr)

        # In-CI negative guard probes (non-canonical Lean version string & 1-byte tampered R2 bundle)
        bad_ver_rejected = not validate_lean_version_string("Lean (version 4.34.0, commit deadbeef)")
        tampered_rejected = False
        try:
            verify_r2_bundle_bytes(raw_r2_zip[:-1] + bytes([raw_r2_zip[-1] ^ 0xFF]))
        except P0XH0Error:
            tampered_rejected = True
        if not (bad_ver_rejected and tampered_rejected):
            raise P0XH0Error("ERR_P0_XH0_G4_GUARD_PROBE_FAIL", "Guard probe failed")

    # Gate XH0-G5: Separate Verdicts for Self-Contained Audit vs Ancestor Lineage Audit
    ancestor_mounted_doc = verify_ancestor_lineage(t104_pack_path, t105_receipt_path)
    ancestor_unmounted_probe = verify_ancestor_lineage(None, None)
    if ancestor_unmounted_probe["verdict"] != "EVIDENCE_UNAVAILABLE":
        raise P0XH0Error("ERR_P0_XH0_G5_FIREWALL_BREACH", "Unmounted ancestor probe must stay EVIDENCE_UNAVAILABLE")

    post_hashes: Dict[str, Any] = {
        "r2_bundle": {"size_bytes": r2_bundle_path.stat().st_size, "sha256": sha256_hex(r2_bundle_path.read_bytes())},
        "p0_xh0_linux_runner_py": {"size_bytes": runner_self_path.stat().st_size, "sha256": sha256_hex(runner_self_path.read_bytes())},
    }
    if t104_pack_path and t104_pack_path.is_file():
        post_hashes["t104_pack"] = {"size_bytes": t104_pack_path.stat().st_size, "sha256": sha256_hex(t104_pack_path.read_bytes())}
    if t105_receipt_path and t105_receipt_path.is_file():
        post_hashes["t105_closure_receipt"] = {
            "size_bytes": t105_receipt_path.stat().st_size,
            "sha256": sha256_hex(t105_receipt_path.read_bytes()),
        }
    if pre_hashes != post_hashes:
        raise P0XH0Error("ERR_P0_XH0_G1_INPUT_MUTATED", "Input hashes changed during execution")

    os_release = ""
    if Path("/etc/os-release").is_file():
        os_release = Path("/etc/os-release").read_text(encoding="utf-8", errors="replace").strip()

    gh_identity = {
        "github_repository": os.environ.get("GITHUB_REPOSITORY", "LOCAL_DRY_RUN"),
        "github_workflow_ref": os.environ.get("GITHUB_WORKFLOW_REF", "LOCAL_DRY_RUN"),
        "github_sha": os.environ.get("GITHUB_SHA", "LOCAL_DRY_RUN"),
        "github_run_id": os.environ.get("GITHUB_RUN_ID", "LOCAL_DRY_RUN"),
        "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT", "1"),
        "runner_os": os.environ.get("RUNNER_OS", platform.system()),
        "runner_arch": os.environ.get("RUNNER_ARCH", platform.machine()),
    }

    run_manifest = seal_json(
        {
            "schema": "CAMPUS_P0_XH0_EXTERNAL_RUN_MANIFEST_V1",
            "stage_id": STAGE_ID,
            "in_ci_state_ceiling": IN_CI_STATE_CEILING,
            "authority_and_semantic_holds": {
                "f_r2_01_reactivate_vs_reassess_split": "HELD_SPEC_LOCKED_ONLY",
                "f_r2_02_external_crypto_and_lineage_independence": "HELD_SPEC_LOCKED_ONLY",
                "f_r2_03_lifecycle_bound_3way_novelty_reward": "HELD_SPEC_LOCKED_ONLY",
                "p1_e1d_and_release_47": "NOT_AUTHORIZED",
            },
            "github_and_runner_identity": gh_identity,
            "os_platform": platform.platform(),
            "os_release_excerpt": os_release,
            "python_version": platform.python_version(),
            "lean_archive_verification": lean_archive_doc,
            "lean_toolchain": {
                "lean_binary_path": str(lean_bin),
                "lean_binary_sha256": lean_bin_sha256,
                "lean_version_full": ver_full,
            },
            "pre_execution_input_hashes": pre_hashes,
            "post_execution_input_hashes": post_hashes,
            "pre_post_hashes_identical": True,
        }
    )

    kernel_parity = seal_json(
        {
            "schema": "CAMPUS_P0_XH0_LINUX_KERNEL_AND_AXIOM_PARITY_V1",
            "stage_id": STAGE_ID,
            "gate_xh0_g2_modules_compiled": "7/7 PASS",
            "gate_xh0_g2_windows_linux_smap_parity": True,
            "smap_metrics": linux_smap,
            "gate_xh0_g3_windows_linux_15_theorem_axiom_parity": True,
            "audited_15_theorem_axioms": linux_axioms,
            "compiled_olean_sha256": compiled_olean_digests,
        }
    )

    mutation_and_split = seal_json(
        {
            "schema": "CAMPUS_P0_XH0_MUTATION_AND_SPLIT_AUDIT_V1",
            "stage_id": STAGE_ID,
            "gate_xh0_g4_prelocked_mutations": mutations_g4,
            "gate_xh0_g4_all_4_caught": True,
            "gate_xh0_g4_r2_unittest_suite_passed": True,
            "gate_xh0_g4_in_ci_guard_probes": {
                "bad_lean_version_rejected": bad_ver_rejected,
                "tampered_r2_bundle_rejected": tampered_rejected,
            },
            "gate_xh0_g5_separated_verdicts": {
                "self_contained_p0_r2_audit_verdict": "SELF_CONTAINED_REPLAY_VERIFIED",
                "ancestor_lineage_relock_verdict": ancestor_mounted_doc["verdict"],
                "unmounted_ancestor_firewall_probe_verdict": ancestor_unmounted_probe["verdict"],
            },
            "ancestor_lineage_details": ancestor_mounted_doc,
        }
    )

    out_dir.mkdir(parents=True, exist_ok=True)
    p_man = out_dir / "P0_XH0_EXTERNAL_RUN_MANIFEST.json"
    p_ker = out_dir / "P0_XH0_LINUX_KERNEL_AND_AXIOM_PARITY.json"
    p_mut = out_dir / "P0_XH0_MUTATION_AND_SPLIT_AUDIT.json"

    p_man.write_bytes(json.dumps(run_manifest, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n")
    p_ker.write_bytes(json.dumps(kernel_parity, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n")
    p_mut.write_bytes(json.dumps(mutation_and_split, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n")

    signed_provenance = seal_json(
        {
            "schema": "CAMPUS_P0_XH0_SIGNED_PROVENANCE_SUBJECT_V1",
            "stage_id": STAGE_ID,
            "in_ci_state_ceiling": IN_CI_STATE_CEILING,
            "github_and_runner_identity": gh_identity,
            "bound_inputs": {
                "p0_r2_bundle_sha256": PINNED_R2_BUNDLE_SHA256,
                "p0_r2_bundle_size_bytes": PINNED_R2_BUNDLE_SIZE,
                "p0_r2_receipt_sha256": PINNED_R2_RECEIPT_SHA256,
                "p0_v1_bundle_sha256": PINNED_P0_V1_SHA256,
                "p0_t1_r1_bundle_sha256": PINNED_P0_T1_R1_SHA256,
                "lean_linux_tarball_sha256": lean_archive_doc.get("sha256", "LOCAL_DRY_RUN"),
                "lean_commit": PINNED_LEAN_COMMIT,
            },
            "bound_outputs": {
                "external_run_manifest_sha256": sha256_hex(p_man.read_bytes()),
                "linux_kernel_and_axiom_parity_sha256": sha256_hex(p_ker.read_bytes()),
                "mutation_and_split_audit_sha256": sha256_hex(p_mut.read_bytes()),
            },
            "explicit_non_claims": {
                "f_r2_01_to_03_semantic_holds": "HELD",
                "universal_soundness_and_empirical_truth": "HELD",
                "p1_e1d_release47": "NOT_AUTHORIZED",
            },
        }
    )
    p_prov = out_dir / "P0_XH0_SIGNED_PROVENANCE.json"
    p_prov.write_bytes(json.dumps(signed_provenance, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n")
    return signed_provenance


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--r2-bundle", required=True, type=Path)
    ap.add_argument("--out-dir", required=True, type=Path)
    ap.add_argument("--t104-pack", default=None, type=Path)
    ap.add_argument("--t105-receipt", default=None, type=Path)
    ap.add_argument("--lean-archive", default=None, type=Path)
    ap.add_argument("--require-lean-archive", action="store_true")
    ap.add_argument("--lean-bin", default=None, type=str)
    args = ap.parse_args()

    prov = run_xh0_qualification(
        r2_bundle_path=args.r2_bundle,
        out_dir=args.out_dir,
        t104_pack_path=args.t104_pack,
        t105_receipt_path=args.t105_receipt,
        lean_archive_path=args.lean_archive,
        require_lean_archive=args.require_lean_archive,
        explicit_lean_bin=args.lean_bin,
    )
    print(json.dumps({"status": prov["in_ci_state_ceiling"], "provenance_payload_sha256": prov["seal"]["payload_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
