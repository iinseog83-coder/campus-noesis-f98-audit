#!/usr/bin/env python3
"""PCT0-XH0 External Detached Linux CI Raw Evidence Runner (`XH0-G1`..`XH0-G5`, `v3` Spec).

Important Governance & Architectural Rules:
  - Does NOT trust `PCT0_S1S2_MINIMAL_FORMALIZATION_RECEIPT.json` as ground truth; recomputes
    all compilations, `.olean` AST import calibrations, `SMap` metrics, `TransDeps` closures,
    23-theorem `#print axioms` footprints, and 5 `Proof-Break × Countermodel` causal-prefix span
    verifications from scratch using the host `Lean 4.33.1` kernel.
  - NEVER emits `XH0-G6 = PASS` or `XH0-G7 = PASS`; emits ONLY raw `G1`..`G5` JSON artifacts,
    raw `LINUX_LEAN_RAW_TRANSCRIPT.log`, and `PCT0_XH0_SIGNED_PROVENANCE.json` (whose SHA-256
    binds all raw artifacts for Sigstore OIDC Fulcio + Rekor signing).
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

STAGE_ID = "CAMPUS_PROOFSPACE_OMEGA_PCT0_XH0_DETACHED_EXTERNAL_REPLAY_V3"

PINNED_S1S2_ZIP_SHA256 = "0700fd1cf3225b1b791d5d3dc35cc05ef925acf1ebc443bab8b73d5a4884025e"
PINNED_S1S2_ZIP_SIZE = 45265
PINNED_S1S2_ZIP_ENTRIES = 15

PINNED_LINUX_TAR_SHA256 = "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
PINNED_LINUX_TAR_SIZE = 570405234
PINNED_LEAN_VERSION = "4.33.1"
PINNED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"

ORDERED_MODULES: Tuple[Tuple[str, str], ...] = (
    ("ProofspaceOmegaPCT0.GenG", "ProofspaceOmegaPCT0/GenG.lean"),
    ("ProofspaceOmegaPCT0.GenH", "ProofspaceOmegaPCT0/GenH.lean"),
    ("ProofspaceOmegaPCT0.TransportCore", "ProofspaceOmegaPCT0/TransportCore.lean"),
    ("ProofspaceOmegaPCT0.AuthorityAndAdmission", "ProofspaceOmegaPCT0/AuthorityAndAdmission.lean"),
    ("ProofspaceOmegaPCT0.ControlsAndCounterexamples", "ProofspaceOmegaPCT0/ControlsAndCounterexamples.lean"),
    ("ProofspaceOmegaPCT0.PCT0AxiomAudit", "ProofspaceOmegaPCT0/PCT0AxiomAudit.lean"),
    ("ProofspaceOmegaPCT0", "ProofspaceOmegaPCT0.lean"),
)

FORBIDDEN_PATTERNS = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\s+"),
    re.compile(r"(?m)^\s*opaque\s+"),
    re.compile(r"\bnative_decide\b"),
    re.compile(r"\bofReduceBool\b"),
    re.compile(r"\btrustCompiler\b"),
    re.compile(r"\bimplemented_by\b"),
    re.compile(r"@\[[^\]]*\bextern\b"),
    re.compile(r"\bunsafe\b"),
    re.compile(r"(?m)^\s*partial\s+def\b"),
)

SYNTAX_ERROR_MARKERS = (
    "unexpected token",
    "expected token",
    "unknown identifier",
    "unterminated comment",
    "invalid syntax",
)

ENV_CALIBRATION_AND_TRANSDEPS_INSPECTOR = r"""import ZeroImportCalibration
import ProofspaceOmegaPCT0
import pct0_independent_clean_sheet_probe
import Lean

open Lean

def isPCT0Target : Name → Bool
  | .anonymous => false
  | .str .anonymous s => s == "ProofspaceOmegaPCT0" || s == "PCT0IndependentCleanSheetProbe"
  | .str p _ => isPCT0Target p
  | .num p _ => isPCT0Target p

def isPurePCT0Namespace : Name → Bool
  | .anonymous => false
  | .str .anonymous s => s == "ProofspaceOmegaPCT0"
  | .str p _ => isPurePCT0Namespace p
  | .num p _ => isPurePCT0Namespace p

def hasPrefix2 (a b : String) : Name → Bool
  | .str (.str .anonymous s1) s2 => s1 == a && s2 == b
  | .str p _ => hasPrefix2 a b p
  | .num p _ => hasPrefix2 a b p
  | _ => false

def isGenGConst (nm : Name) : Bool := hasPrefix2 "ProofspaceOmegaPCT0" "GenG" nm
def isGenHConst (nm : Name) : Bool := hasPrefix2 "ProofspaceOmegaPCT0" "GenH" nm
def isTransportOrAdmissionConst (nm : Name) : Bool :=
  isPurePCT0Namespace nm && !(isGenGConst nm) && !(isGenHConst nm)

def computeTransDeps (env : Environment) (seeds : List Name) : List Name × NameSet × Bool := Id.run do
  let mut enqueued : NameSet := {}
  let mut queue : Array Name := #[]
  for s in seeds do
    if !enqueued.contains s then
      enqueued := enqueued.insert s
      queue := queue.push s
  let mut idx : Nat := 0
  for _ in [0 : 150000] do
    if h : idx < queue.size then
      let cur := queue[idx]
      idx := idx + 1
      if let some ci := env.find? cur then
        for dep in ci.getUsedConstantsAsSet.toList do
          if !enqueued.contains dep then
            enqueued := enqueued.insert dep
            queue := queue.push dep
    else
      break
  return (queue.toList, enqueued, decide (queue.size ≤ idx))

#eval show MetaM Unit from do
  let env ← getEnv
  for i in [0 : env.header.moduleNames.size] do
    let mname := env.header.moduleNames[i]!
    let mstr := mname.toString
    if mstr == "ZeroImportCalibration" ||
       mstr == "ProofspaceOmegaPCT0.GenG" ||
       mstr == "ProofspaceOmegaPCT0.GenH" ||
       mstr == "pct0_independent_clean_sheet_probe" then
      let mdata := env.header.moduleData[i]!
      let imps := String.intercalate "," (mdata.imports.toList.map (fun imp => imp.module.toString))
      IO.println s!"PCT0_MODIMPORTS|module={mstr}|imports={imps}"

  let allEntries := env.constants.map₁.toList ++ env.constants.map₂.toList
  let mut consts : Nat := 0
  let mut thms : Nat := 0
  let mut sorryCnt : Nat := 0
  let mut userAxCnt : Nat := 0
  let mut opaqueCnt : Nat := 0
  let mut reduceBoolCnt : Nat := 0
  let mut choiceCnt : Nat := 0
  let mut seedsG : List Name := []
  let mut seedsH : List Name := []
  let mut transportCnt : Nat := 0

  for (nm, ci) in allEntries do
    if isGenGConst nm then seedsG := nm :: seedsG
    if isGenHConst nm then seedsH := nm :: seedsH
    if isTransportOrAdmissionConst nm then transportCnt := transportCnt + 1
    if isPCT0Target nm then
      consts := consts + 1
      match ci with
      | .thmInfo _ => thms := thms + 1
      | .axiomInfo _ => userAxCnt := userAxCnt + 1
      | .opaqueInfo _ => opaqueCnt := opaqueCnt + 1
      | _ => pure ()
      for u in ci.getUsedConstantsAsSet.toList do
        if u == ``sorryAx then sorryCnt := sorryCnt + 1
        if u == ``Classical.choice then choiceCnt := choiceCnt + 1
        if u == ``Lean.ofReduceBool || u == ``Lean.trustCompiler then
          reduceBoolCnt := reduceBoolCnt + 1

  let (listG, _setG, satG) := computeTransDeps env seedsG
  let (listH, setH, satH) := computeTransDeps env seedsH

  let gTransInter := (listG.filter isTransportOrAdmissionConst).length
  let gHInter := (listG.filter isGenHConst).length
  let hTransInter := (listH.filter isTransportOrAdmissionConst).length
  let hGInter := (listH.filter isGenGConst).length
  let sharedUserGH := (listG.filter (fun n => isPurePCT0Namespace n && setH.contains n)).length

  IO.println s!"PCT0_SMAP|constants={consts}|theorems={thms}|sorry={sorryCnt}|userAxioms={userAxCnt}|opaque={opaqueCnt}|reduceBool={reduceBoolCnt}|classicalChoice={choiceCnt}"
  IO.println s!"PCT0_TRANSDEPS|seedsG={seedsG.length}|seedsH={seedsH.length}|transportConsts={transportCnt}|closureG={listG.length}|closureH={listH.length}|satG={(if satG then 1 else 0)}|satH={(if satH then 1 else 0)}|interGTransport={gTransInter}|interGH={gHInter}|interHTransport={hTransInter}|interHG={hGInter}|sharedUserGH={sharedUserGH}"
"""

PROBE_AUDIT_SNIPPET_TEMPLATE = r"""
section PCT0ProbeAudit
open Lean
#eval show MetaM Unit from do
  let env ← getEnv
  let mut sCnt : Nat := 0
  let mut axCnt : Nat := 0
  for (nm, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if nm.toString.startsWith "__PROBE_NS__" then
      match ci with
      | .axiomInfo _ => axCnt := axCnt + 1
      | _ => pure ()
      for u in ci.getUsedConstantsAsSet.toList do
        if u == ``sorryAx then sCnt := sCnt + 1
  IO.println s!"PROBE_AUDIT|ns=__PROBE_NS__|sorry={sCnt}|userAxioms={axCnt}"
end PCT0ProbeAudit
"""

COUNTERMODEL_PROBES: Dict[str, Tuple[str, str, str]] = {
    "M_PCT0_LEAN_01": (
        "PCT0XH0Countermodel01",
        "(0 ≤ M.alphaH ∧ 0 ≤ M.betaH ∧ 0 ≤ M.delta2a ∧ 0 ≤ M.delta2b ∧ M.xiExt ≤ 5 ∧ 12 ≤ M.capH)",
        r"""import ProofspaceOmegaPCT0.TransportCore
import Lean
namespace PCT0XH0Countermodel01
open ProofspaceOmegaPCT0 ProofspaceOmegaPCT0.GenG ProofspaceOmegaPCT0.GenH

theorem def_eq_witness_01 (M : ModelH) :
    AdmissibleH M = (0 ≤ M.alphaH ∧ 0 ≤ M.betaH ∧ 0 ≤ M.delta2a ∧ 0 ≤ M.delta2b ∧ M.xiExt ≤ 5 ∧ 12 ≤ M.capH) := rfl

theorem refute_mut_01 :
    let Mh : ModelH := ⟨1, 1, 1, 1, 5, 15⟩
    let xh : CtxH := ⟨2, 2, 2⟩
    RealizableH Mh xh ∧ pullbackRegion Bg xh ∧
    ¬ T1RealObligation (pullbackRegion Bg) ∧
    ¬ ValidOnH (pullbackRegion Bg) (.dissipStepSlack 0) := by
  dsimp
  have hReal : RealizableH ⟨1, 1, 1, 1, 5, 15⟩ ⟨2, 2, 2⟩ := by
    dsimp [RealizableH, AdmissibleH, StepFeasibleH, NonnegCtxH, massH]; decide
  have hPb : pullbackRegion Bg ⟨2, 2, 2⟩ := by
    dsimp [pullbackRegion, Bg, NonnegCtxG, massG, reduceCtx]; decide
  have hNotG : ¬ RealizableG (reduceModel ⟨1, 1, 1, 1, 5, 15⟩) (reduceCtx ⟨2, 2, 2⟩) := by
    dsimp [RealizableG, AdmissibleG, StepFeasibleG, NonnegCtxG, massG, reduceModel, reduceCtx]; decide
  have hNotSatH : ¬ SatisfiesH ⟨1, 1, 1, 1, 5, 15⟩ ⟨2, 2, 2⟩ (.dissipStepSlack 0) := by
    dsimp [SatisfiesH, stepH, massH]; decide
  exact ⟨hReal, hPb, fun hT1 => hNotG (hT1 _ _ hReal hPb), fun hVal => hNotSatH (hVal _ _ hReal hPb)⟩

end PCT0XH0Countermodel01
""",
    ),
    "M_PCT0_LEAN_02": (
        "PCT0XH0Countermodel02",
        "ClaimH.sub2bStepNonIncrease",
        r"""import ProofspaceOmegaPCT0.ControlsAndCounterexamples
import Lean
namespace PCT0XH0Countermodel02
open ProofspaceOmegaPCT0 ProofspaceOmegaPCT0.GenG ProofspaceOmegaPCT0.GenH ProofspaceOmegaPCT0.Controls

theorem def_eq_witness_02 :
    tauExact .dissipStep = ClaimH.sub2bStepNonIncrease := rfl

theorem refute_mut_02 :
    let Mh : ModelH := ⟨1, 3, 1, 1, 0, 15⟩
    let xh : CtxH := ⟨2, 4, 1⟩
    RealizableH Mh xh ∧ pullbackRegion Bg xh ∧
    SatisfiesG (reduceModel Mh) (reduceCtx xh) .dissipStep ∧
    ¬ T3PullbackObligation (pullbackRegion Bg) .dissipStep tauExact ∧
    ¬ ValidOnH (pullbackRegion Bg) (tauExact .dissipStep) := by
  dsimp
  have hReal : RealizableH ⟨1, 3, 1, 1, 0, 15⟩ ⟨2, 4, 1⟩ := by
    dsimp [RealizableH, AdmissibleH, StepFeasibleH, NonnegCtxH, massH]; decide
  have hPb : pullbackRegion Bg ⟨2, 4, 1⟩ := by
    dsimp [pullbackRegion, Bg, NonnegCtxG, massG, reduceCtx]; decide
  have hSatG : SatisfiesG (reduceModel ⟨1, 3, 1, 1, 0, 15⟩) (reduceCtx ⟨2, 4, 1⟩) .dissipStep := by
    dsimp [SatisfiesG, stepG, massG, reduceModel, reduceCtx]; decide
  have hNotSatH : ¬ SatisfiesH ⟨1, 3, 1, 1, 0, 15⟩ ⟨2, 4, 1⟩ (tauExact .dissipStep) := by
    dsimp [tauExact, SatisfiesH, stepH]; decide
  exact ⟨hReal, hPb, hSatG, fun hT3 => hNotSatH (hT3 _ _ hReal hPb hSatG), fun hVal => hNotSatH (hVal _ _ hReal hPb)⟩

end PCT0XH0Countermodel02
""",
    ),
    "M_PCT0_LEAN_03": (
        "PCT0XH0Countermodel03",
        "(pullbackRegion BgGe10 x ∧ massH x ≤ 8)",
        r"""import ProofspaceOmegaPCT0.ControlsAndCounterexamples
import Lean
namespace PCT0XH0Countermodel03
open ProofspaceOmegaPCT0 ProofspaceOmegaPCT0.GenG ProofspaceOmegaPCT0.GenH ProofspaceOmegaPCT0.Controls

theorem def_eq_witness_03 (x : CtxH) :
    canonicalTargetRegion x = (pullbackRegion BgGe10 x ∧ massH x ≤ 8) := rfl

theorem refute_mut_03 :
    (∃ x, pullbackRegion BgGe10 x) ∧
    (∃ x, NonnegCtxH x ∧ massH x ≤ 8) ∧
    (∀ w : JointWitness Bg canonicalTargetRegion, False) := by
  refine ⟨⟨⟨4, 3, 3⟩, by dsimp [pullbackRegion, BgGe10, Bg, NonnegCtxG, massG, reduceCtx]; decide⟩,
          ⟨⟨2, 2, 2⟩, by dsimp [NonnegCtxH, massH]; decide⟩, ?_⟩
  intro w
  have hBh := w.hBh
  dsimp [canonicalTargetRegion, pullbackRegion, BgGe10] at hBh
  rcases hBh with ⟨⟨_, hGe10⟩, hLe8⟩
  rw [mass_commutes] at hGe10
  omega

end PCT0XH0Countermodel03
""",
    ),
    "M_PCT0_LEAN_04": (
        "PCT0XH0Countermodel04",
        "(PCICPolicySatisfied Ph K' && CommitAuthorized Ph g K')",
        r"""import ProofspaceOmegaPCT0.AuthorityAndAdmission
import Lean
namespace PCT0XH0Countermodel04
open ProofspaceOmegaPCT0 ProofspaceOmegaPCT0.GenG ProofspaceOmegaPCT0.GenH

theorem def_eq_witness_04 (Ph : LedgerStateH) (c : Option VerifiedTransportCertificate) (g : Option CommitAuthGrant) (K' : TransportCandidateK) :
    CanonicalAdmissible Ph c g K' = (PCICPolicySatisfied Ph K' && CommitAuthorized Ph g K') := rfl

theorem refute_mut_04 :
    let Ph : LedgerStateH := ⟨2, 20261119, 7, 900, 778899, false, [], []⟩
    let g : CommitAuthGrant := ⟨5001, 900, 778899, 101, 2, 20261119, 7⟩
    let K' : TransportCandidateK := ⟨101, 1, 2, 20261119, .dissipStep, .dissipStepSlack 0, .ELIGIBLE_CANDIDATE, .FORMAL_WITNESS_VERIFIED, .UNASSESSED, false⟩
    VerifiedProof none K' = false ∧
    CanonicalAdmissible Ph none (some g) K' = true ∧
    ¬ (CanonicalAdmissible Ph none (some g) K' = true ↔
       (VerifiedProof none K' = true ∧ PCICPolicySatisfied Ph K' = true ∧ CommitAuthorized Ph (some g) K' = true)) := by
  decide

end PCT0XH0Countermodel04
""",
    ),
    "M_PCT0_LEAN_05": (
        "PCT0XH0Countermodel05",
        "(VerifiedProof c K' && PCICPolicySatisfied Ph K')",
        r"""import ProofspaceOmegaPCT0.AuthorityAndAdmission
import Lean
namespace PCT0XH0Countermodel05
open ProofspaceOmegaPCT0 ProofspaceOmegaPCT0.GenG ProofspaceOmegaPCT0.GenH

theorem def_eq_witness_05 (Ph : LedgerStateH) (c : Option VerifiedTransportCertificate) (g : Option CommitAuthGrant) (K' : TransportCandidateK) :
    CanonicalAdmissible Ph c g K' = (VerifiedProof c K' && PCICPolicySatisfied Ph K') := rfl

theorem refute_mut_05 :
    ∃ cert : VerifiedTransportCertificate,
      let Ph : LedgerStateH := ⟨2, 20261119, 7, 900, 778899, false, [], []⟩
      CommitAuthorized Ph none cert.cand = false ∧
      CanonicalAdmissible Ph (some cert) none cert.cand = true ∧
      ¬ (CanonicalAdmissible Ph (some cert) none cert.cand = true ↔
         (VerifiedProof (some cert) cert.cand = true ∧ PCICPolicySatisfied Ph cert.cand = true ∧ CommitAuthorized Ph none cert.cand = true)) := by
  let K0 : TransportCandidateK := ⟨101, 1, 2, 20261119, .dissipStep, .dissipStepSlack 0, .ELIGIBLE_CANDIDATE, .FORMAL_WITNESS_VERIFIED, .UNASSESSED, false⟩
  let tau0 : ClaimG → ClaimH | .dissipStep => .dissipStepSlack 0 | .massAtMost b => .massAtMost b
  let w0 : JointWitness Bg (pullbackRegion Bg) :=
    { mh := ⟨1, 1, 1, 1, 0, 15⟩, xh := ⟨4, 2, 2⟩
    , hRealH := by dsimp [RealizableH, AdmissibleH, StepFeasibleH, NonnegCtxH, massH]; decide
    , hBh := by dsimp [pullbackRegion, Bg, NonnegCtxG, massG, reduceCtx]; decide
    , hRealG := by dsimp [RealizableG, AdmissibleG, StepFeasibleG, NonnegCtxG, massG, reduceModel, reduceCtx]; decide
    , hBgSrc := by dsimp [Bg, NonnegCtxG, massG, reduceCtx]; decide }
  let cert0 : VerifiedTransportCertificate :=
    { cand := K0, BgSrc := Bg, Bh := pullbackRegion Bg, tau := tau0
    , hTranslatedEq := rfl, hEligibility := rfl, hFormalVerified := rfl
    , hSrcValid := g_dissip_valid_on_Bg, hT0 := ⟨w0⟩
    , hT1 := by
        intro M x hRH _
        rcases hRH with ⟨⟨ha, hb, hd2a, hd2b, hxi, hcap⟩, ⟨⟨hv1, hv2a, hv2b⟩, hs1, hs2, hs3, hsm⟩⟩
        dsimp [RealizableG, AdmissibleG, StepFeasibleG, NonnegCtxG, massG, reduceModel, reduceCtx]
        dsimp [massH] at hsm
        refine ⟨⟨ha, ?_, hcap⟩, ⟨⟨hv1, ?_⟩, hs1, ?_, ?_⟩⟩ <;> omega
    , hT2 := pullback_satisfies_t2_ctx Bg
    , hT3 := by
        intro M x _ _ hSG
        dsimp [K0, SatisfiesG] at hSG
        rw [step_mass_commutes, mass_commutes] at hSG
        dsimp [K0, tau0, SatisfiesH]
        omega }
  refine ⟨cert0, ?_⟩
  decide

end PCT0XH0Countermodel05
""",
    ),
}


def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode("utf-8")


def strip_lean_comments(src: str) -> str:
    out: List[str] = []
    i, n, depth, in_str = 0, len(src), 0, False
    while i < n:
        if depth == 0 and not in_str:
            if src.startswith("/-", i):
                depth = 1
                i += 2
                continue
            if src.startswith("--", i):
                while i < n and src[i] != "\n":
                    i += 1
                continue
            if src[i] == '"':
                in_str = True
                out.append('""')
                i += 1
                continue
            out.append(src[i])
            i += 1
        elif in_str:
            if src[i] == "\\" and i + 1 < n:
                i += 2
                continue
            if src[i] == '"':
                in_str = False
            i += 1
        else:
            if src.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if src[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def find_lean_exe() -> Path:
    w = shutil.which("lean")
    if w:
        return Path(w)
    cand = Path.home() / ".elan" / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    if cand.is_file():
        return cand
    raise RuntimeError("Lean 4.33.1 executable not found")


def split_causal_prefix_span(raw_bytes: bytes, split_theorem_decl: Optional[str], end_ns_line: str) -> Tuple[bytes, bytes, bytes]:
    text = raw_bytes.decode("utf-8")
    idx_end = text.rfind(end_ns_line)
    if idx_end == -1:
        raise ValueError(f"Namespace terminator `{end_ns_line}` not found")
    body = text[:idx_end]
    e_ns = text[idx_end:]
    if split_theorem_decl is None:
        return (body.encode("utf-8"), b"", e_ns.encode("utf-8"))
    m = re.search(rf"(?m)^theorem\s+{re.escape(split_theorem_decl)}\b", body)
    if m is None:
        raise ValueError(f"Split theorem `{split_theorem_decl}` not found")
    cut_pos = m.start()
    # Keep any immediately preceding `/-- ... -/` doc-comment attached to `q0` so `D_m` has no dangling docstring before `end`
    prefix_trimmed = body[:cut_pos].rstrip()
    if prefix_trimmed.endswith("-/"):
        doc_start = prefix_trimmed.rfind("/--")
        if doc_start != -1 and "-/" not in prefix_trimmed[doc_start + 3 : -2]:
            cut_pos = doc_start
    p0 = body[:cut_pos]
    q0 = body[cut_pos:]
    return (p0.encode("utf-8"), q0.encode("utf-8"), e_ns.encode("utf-8"))


def classify_lean_failure(diag_text: str) -> str:
    low = diag_text.lower()
    if "omega could not prove the goal" in low:
        return "OMEGA_UNSOLVED_LINEAR_GOAL"
    if "proved that the proposition" in low and "is false" in low:
        return "DECIDE_EVALUATED_FALSE"
    if "failed to synthesize" in low and "decidable" in low:
        return "DECIDABLE_SYNTHESIS_FAILURE"
    if "type mismatch" in low:
        return "KERNEL_TYPE_MISMATCH"
    if "unsolved goals" in low:
        return "UNSOLVED_GOALS"
    return "OTHER_ERROR"


def find_decl_span(src_text: str, decl_name: str) -> Tuple[int, int]:
    lines = src_text.splitlines()
    start_ln = -1
    decl_re = re.compile(rf"^\s*(?:theorem|def)\s+{re.escape(decl_name)}\b")
    stop_re = re.compile(r"^\s*(?:theorem|def|structure|inductive|end)\s+")
    for idx, ln in enumerate(lines, start=1):
        if start_ln == -1:
            if decl_re.match(ln):
                start_ln = idx
        else:
            if stop_re.match(ln):
                return (start_ln, idx - 1)
    if start_ln == -1:
        raise ValueError(f"Declaration `{decl_name}` not found")
    return (start_ln, len(lines))


def run_single_causal_span_mutation(
    lean_bin: Path,
    clean_lean_dir: Path,
    mut_id: str,
    rel_mut_file: str,
    split_thm_in_mut_file: Optional[str],
    end_ns_line: str,
    old_str: str,
    new_str: str,
    failing_mod_idx: int,
    dm_mod_idx: int,
    target_thm_name: str,
) -> Dict[str, Any]:
    orig_bytes = (clean_lean_dir / rel_mut_file).read_bytes()
    p0_b, q0_b, ens_b = split_causal_prefix_span(orig_bytes, split_thm_in_mut_file, end_ns_line)
    reconstructed_s0 = p0_b + q0_b + ens_b

    p0_str = p0_b.decode("utf-8")
    nl = "\r\n" if "\r\n" in p0_str else "\n"
    old_norm = old_str.replace("\n", nl)
    new_norm = new_str.replace("\n", nl)
    if p0_str.count(old_norm) != 1:
        raise RuntimeError(f"[{mut_id}] expected unique `{old_str}` inside causal prefix P0")
    pm_b = p0_str.replace(old_norm, new_norm, 1).encode("utf-8")

    # Categorical Span Pushout from shared mutated prefix buffer pm_b:
    sm_b = pm_b + q0_b + ens_b
    dm_b = pm_b + ens_b

    # Path A: Isolated Proof-Break build root
    with tempfile.TemporaryDirectory(prefix=f"pct0_xh0_brk_{mut_id}_") as tmp_a:
        tpa = Path(tmp_a)
        scpa = tpa / "src"
        blda = tpa / "bld"
        shutil.copytree(clean_lean_dir, scpa)
        (blda / "ProofspaceOmegaPCT0").mkdir(parents=True, exist_ok=True)
        (scpa / rel_mut_file).write_bytes(sm_b)
        actual_sm_sha = sha256_hex((scpa / rel_mut_file).read_bytes())

        env_a = dict(os.environ)
        env_a["LEAN_PATH"] = str(blda)

        prereq_ok = True
        for idx in range(failing_mod_idx):
            _, rel = ORDERED_MODULES[idx]
            pr = subprocess.run(
                [str(lean_bin), "-o", str(blda / Path(rel).with_suffix(".olean")), rel],
                cwd=str(scpa),
                capture_output=True,
                text=True,
                env=env_a,
                check=False,
            )
            if pr.returncode != 0:
                prereq_ok = False
                break

        fail_mod_nm, fail_rel = ORDERED_MODULES[failing_mod_idx]
        span_s, span_e = find_decl_span((scpa / fail_rel).read_text(encoding="utf-8"), target_thm_name)
        brk_proc = subprocess.run(
            [str(lean_bin), "-o", str(blda / Path(fail_rel).with_suffix(".olean")), fail_rel],
            cwd=str(scpa),
            capture_output=True,
            text=True,
            env=env_a,
            check=False,
        )
        brk_out = (brk_proc.stdout or "") + (brk_proc.stderr or "")
        has_syntax = any(mk in brk_out.lower() for mk in SYNTAX_ERROR_MARKERS)
        err_lines = [int(m.group(1)) for m in re.finditer(r":(\d+):\d+:\s*error:", brk_out)]
        first_err_ln = err_lines[0] if err_lines else -1
        err_cls = classify_lean_failure(brk_out)

    # Path B: Isolated Prefix Module D_m.olean + Constructive Countermodel Probe build root
    probe_ns, rfl_rhs_str, probe_src = COUNTERMODEL_PROBES[mut_id]
    full_probe_src = probe_src + PROBE_AUDIT_SNIPPET_TEMPLATE.replace("__PROBE_NS__", probe_ns)
    with tempfile.TemporaryDirectory(prefix=f"pct0_xh0_cm_{mut_id}_") as tmp_b:
        tpb = Path(tmp_b)
        scpb = tpb / "src"
        bldb = tpb / "bld"
        shutil.copytree(clean_lean_dir, scpb)
        (bldb / "ProofspaceOmegaPCT0").mkdir(parents=True, exist_ok=True)
        (scpb / rel_mut_file).write_bytes(dm_b)
        actual_dm_sha = sha256_hex((scpb / rel_mut_file).read_bytes())

        env_b = dict(os.environ)
        env_b["LEAN_PATH"] = str(bldb)

        dm_rc = 0
        dm_olean_sha = ""
        # Compile up through max(dm_mod_idx, 2) so TransportCore is available when GenH is mutated in M_01
        compile_through = max(dm_mod_idx, 2) if mut_id == "M_PCT0_LEAN_01" else dm_mod_idx
        for idx in range(compile_through + 1):
            _, rel = ORDERED_MODULES[idx]
            out_olean = bldb / Path(rel).with_suffix(".olean")
            pr = subprocess.run(
                [str(lean_bin), "-o", str(out_olean), rel],
                cwd=str(scpb),
                capture_output=True,
                text=True,
                env=env_b,
                check=False,
            )
            if pr.returncode != 0:
                dm_rc = pr.returncode
                break
            if idx == dm_mod_idx:
                dm_olean_sha = sha256_hex(out_olean.read_bytes())

        probe_rc = -1
        probe_sorry = 999
        probe_uax = 999
        probe_out = ""
        if dm_rc == 0:
            probe_file = scpb / f"{probe_ns}.lean"
            probe_file.write_text(full_probe_src, encoding="utf-8")
            p_pr = subprocess.run(
                [str(lean_bin), "-o", str(bldb / f"{probe_ns}.olean"), f"{probe_ns}.lean"],
                cwd=str(scpb),
                capture_output=True,
                text=True,
                env=env_b,
                check=False,
            )
            probe_rc = p_pr.returncode
            probe_out = (p_pr.stdout or "") + (p_pr.stderr or "")
            aud_ln = next((ln.strip() for ln in probe_out.splitlines() if ln.startswith("PROBE_AUDIT|")), "")
            if aud_ln:
                kv = dict(seg.split("=", 1) for seg in aud_ln.split("|")[1:])
                probe_sorry = int(kv["sorry"])
                probe_uax = int(kv["userAxioms"])

    return {
        "mut_id": mut_id,
        "mutated_file": rel_mut_file,
        "expected_target_theorem": target_thm_name,
        "target_theorem_line_span": [span_s, span_e],
        "causal_span_hashes": {
            "orig_s0_sha256": sha256_hex(orig_bytes),
            "reconstructed_s0_sha256": sha256_hex(reconstructed_s0),
            "p0_sha256": sha256_hex(p0_b),
            "pm_sha256": sha256_hex(pm_b),
            "q0_sha256": sha256_hex(q0_b),
            "qm_sha256": sha256_hex(q0_b),
            "sm_sha256": actual_sm_sha,
            "span_sm_sha256": sha256_hex(pm_b + q0_b + ens_b),
            "dm_sha256": actual_dm_sha,
            "span_dm_sha256": sha256_hex(pm_b + ens_b),
        },
        "proof_break_observation": {
            "failing_module": fail_mod_nm,
            "prereq_all_exit_zero": prereq_ok,
            "exit_code": brk_proc.returncode,
            "zero_syntax_errors": not has_syntax,
            "first_error_line": first_err_ln,
            "error_class": err_cls,
            "raw_diagnostic_excerpt": brk_out[:1800],
        },
        "countermodel_refutation_witness": {
            "dm_compile_exit_code": dm_rc,
            "dm_olean_sha256": dm_olean_sha,
            "rfl_rhs_spec_string": rfl_rhs_str,
            "rfl_rhs_spec_sha256": sha256_hex(rfl_rhs_str.encode("utf-8")),
            "probe_namespace": probe_ns,
            "probe_source_sha256": sha256_hex(probe_src.encode("utf-8")),
            "probe_compile_exit_code": probe_rc,
            "probe_sorry_count": probe_sorry,
            "probe_user_axioms_count": probe_uax,
            "probe_raw_stdout": probe_out[:800],
        },
    }


def parse_unittest_counts(stderr_text: str, returncode: int) -> Tuple[int, int, int]:
    m_ran = re.search(r"Ran\s+(\d+)\s+tests?", stderr_text)
    total = int(m_ran.group(1)) if m_ran else 0
    m_sk = re.search(r"skipped=(\d+)", stderr_text)
    skipped = int(m_sk.group(1)) if m_sk else 0
    if returncode == 0:
        return (total - skipped, skipped, 0)
    m_fl = re.search(r"failures=(\d+)", stderr_text)
    m_er = re.search(r"errors=(\d+)", stderr_text)
    failed = (int(m_fl.group(1)) if m_fl else 0) + (int(m_er.group(1)) if m_er else 0)
    if failed == 0:
        failed = 1
    return (max(0, total - skipped - failed), skipped, failed)


def execute_ci_raw_replay(
    s1s2_bundle_path: Path,
    out_dir: Path,
    lean_archive_path: Optional[Path],
    require_lean_archive: bool,
) -> Dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    raw_zip_bytes = s1s2_bundle_path.read_bytes()
    zip_sha_pre = sha256_hex(raw_zip_bytes)
    zip_size = len(raw_zip_bytes)

    lean_bin = find_lean_exe()
    lean_bin_sha = sha256_hex(lean_bin.read_bytes())
    ver_proc = subprocess.run([str(lean_bin), "--version"], capture_output=True, text=True, check=True)
    lean_banner = ((ver_proc.stdout or "") + (ver_proc.stderr or "")).strip()

    tar_sha: Optional[str] = None
    tar_size: Optional[int] = None
    if lean_archive_path is not None and lean_archive_path.is_file():
        tb = lean_archive_path.read_bytes()
        tar_sha = sha256_hex(tb)
        tar_size = len(tb)
    elif require_lean_archive:
        raise RuntimeError("Required official Lean 4.33.1 Linux tarball missing")

    transcript_chunks: List[str] = [f"=== LEAN VERSION ===\n{lean_banner}\n"]

    with tempfile.TemporaryDirectory(prefix="pct0_xh0_unpack_") as tmp_u:
        unpacked = Path(tmp_u) / "s1s2"
        unpacked.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(io.BytesIO(raw_zip_bytes), "r") as zf:
            crc_ok = zf.testzip() is None
            entry_cnt = len(zf.infolist())
            zf.extractall(unpacked)

        # Pre-execution snapshot of all unpacked files
        pre_tree_hashes = {
            p.relative_to(unpacked).as_posix(): sha256_hex(p.read_bytes())
            for p in sorted(unpacked.rglob("*"))
            if p.is_file()
        }

        lean_src_dir = unpacked / "lean_pct0"
        probe_fp = unpacked / "probes" / "pct0_independent_clean_sheet_probe.lean"
        ro_rec_dir = unpacked / "readonly_frozen_receipts"

        lean_sha_map: Dict[str, str] = {}
        aux_prescreen_ok = True
        for mod_nm, rel in ORDERED_MODULES:
            fp = lean_src_dir / rel
            lean_sha_map[mod_nm] = sha256_hex(fp.read_bytes())
            st = strip_lean_comments(fp.read_text(encoding="utf-8"))
            if any(p.search(st) for p in FORBIDDEN_PATTERNS):
                aux_prescreen_ok = False
        lean_sha_map["PCT0IndependentCleanSheetProbe"] = sha256_hex(probe_fp.read_bytes())
        if any(p.search(strip_lean_comments(probe_fp.read_text(encoding="utf-8"))) for p in FORBIDDEN_PATTERNS):
            aux_prescreen_ok = False

        frozen_rec_list: List[Dict[str, Any]] = []
        for rfp in sorted(ro_rec_dir.glob("*.json")):
            rb = rfp.read_bytes()
            frozen_rec_list.append(
                {"filename": rfp.name, "sha256": sha256_hex(rb), "size_bytes": len(rb)}
            )

        # G2 & G3: Cleanroom Lean 4.33.1 Compilation + Calibration Module + Env Inspector
        with tempfile.TemporaryDirectory(prefix="pct0_xh0_g2g3_") as tmp_c:
            tpc = Path(tmp_c)
            scpc = tpc / "src"
            bldc = tpc / "bld"
            shutil.copytree(lean_src_dir, scpc)
            shutil.copy2(probe_fp, scpc / "pct0_independent_clean_sheet_probe.lean")
            (scpc / "ZeroImportCalibration.lean").write_text("def calibUnit : Unit := ()\n", encoding="utf-8")
            (bldc / "ProofspaceOmegaPCT0").mkdir(parents=True, exist_ok=True)
            env_c = dict(os.environ)
            env_c["LEAN_PATH"] = str(bldc)

            cal_pr = subprocess.run(
                [str(lean_bin), "-o", str(bldc / "ZeroImportCalibration.olean"), "ZeroImportCalibration.lean"],
                cwd=str(scpc),
                capture_output=True,
                text=True,
                env=env_c,
                check=True,
            )
            _ = cal_pr

            compiled_records: List[Dict[str, Any]] = []
            olean_by_mod: Dict[str, str] = {}
            axiom_stdout = ""
            for mod_nm, rel in ORDERED_MODULES + (
                ("pct0_independent_clean_sheet_probe", "pct0_independent_clean_sheet_probe.lean"),
            ):
                out_olean = bldc / Path(rel).with_suffix(".olean")
                pr = subprocess.run(
                    [str(lean_bin), "-o", str(out_olean), rel],
                    cwd=str(scpc),
                    capture_output=True,
                    text=True,
                    env=env_c,
                    check=False,
                )
                comb = (pr.stdout or "") + (pr.stderr or "")
                transcript_chunks.append(f"=== COMPILE {mod_nm} (rc={pr.returncode}) ===\n{comb}\n")
                osha = sha256_hex(out_olean.read_bytes()) if out_olean.is_file() else ""
                compiled_records.append({"module": mod_nm, "exit_code": pr.returncode, "olean_sha256": osha})
                olean_by_mod[mod_nm] = osha
                if mod_nm == "ProofspaceOmegaPCT0.PCT0AxiomAudit":
                    axiom_stdout = pr.stdout or ""

            insp_fp = scpc / "PCT0XH0EnvInspector.lean"
            insp_fp.write_text(ENV_CALIBRATION_AND_TRANSDEPS_INSPECTOR, encoding="utf-8")
            insp_pr = subprocess.run(
                [str(lean_bin), "PCT0XH0EnvInspector.lean"],
                cwd=str(scpc),
                capture_output=True,
                text=True,
                env=env_c,
                check=True,
            )
            insp_out = (insp_pr.stdout or "") + (insp_pr.stderr or "")
            transcript_chunks.append(f"=== ENV INSPECTOR ===\n{insp_out}\n")

            mod_imports_raw: Dict[str, List[str]] = {}
            smap_dict: Dict[str, int] = {}
            tdeps_dict: Dict[str, int] = {}
            for ln in insp_out.splitlines():
                ln = ln.strip()
                if ln.startswith("PCT0_MODIMPORTS|"):
                    kv = dict(seg.split("=", 1) for seg in ln.split("|")[1:])
                    imps = [x for x in kv["imports"].split(",") if x]
                    mod_imports_raw[kv["module"]] = imps
                elif ln.startswith("PCT0_SMAP|"):
                    smap_dict = {k: int(v) for k, v in (seg.split("=", 1) for seg in ln.split("|")[1:])}
                elif ln.startswith("PCT0_TRANSDEPS|"):
                    tdeps_dict = {k: int(v) for k, v in (seg.split("=", 1) for seg in ln.split("|")[1:])}

            thm_axioms: Dict[str, List[str]] = {}
            for m in re.finditer(
                r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]+)\])",
                axiom_stdout,
                flags=re.DOTALL,
            ):
                tnm = m.group(1).strip()
                if m.group(2) is not None:
                    thm_axioms[tnm] = []
                else:
                    thm_axioms[tnm] = [a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip()]

        # G4: 5 Causal-Prefix Span Proof-Break × Countermodel Verifications
        m_specs = [
            (
                "M_PCT0_LEAN_01",
                "ProofspaceOmegaPCT0/GenH.lean",
                None,
                "end ProofspaceOmegaPCT0.GenH",
                "  M.xiExt ≤ 0 ∧\n  12 ≤ M.capH",
                "  M.xiExt ≤ 5 ∧\n  12 ≤ M.capH",
                4,
                1,
                "pct0_s1s2_dissip_transport",
            ),
            (
                "M_PCT0_LEAN_02",
                "ProofspaceOmegaPCT0/ControlsAndCounterexamples.lean",
                "pct0_s1s2_dissip_transport",
                "end ProofspaceOmegaPCT0.Controls",
                "def tauExact : ClaimG → ClaimH\n  | .dissipStep   => .dissipStepSlack 0",
                "def tauExact : ClaimG → ClaimH\n  | .dissipStep   => .sub2bStepNonIncrease",
                4,
                4,
                "pct0_s1s2_dissip_transport",
            ),
            (
                "M_PCT0_LEAN_03",
                "ProofspaceOmegaPCT0/ControlsAndCounterexamples.lean",
                "pct0_s1s2_canonical_admissible",
                "end ProofspaceOmegaPCT0.Controls",
                "def canonicalTargetRegion : CtxH → Prop :=\n  pullbackRegion Bg",
                "def canonicalTargetRegion : CtxH → Prop :=\n  fun x => pullbackRegion BgGe10 x ∧ massH x ≤ 8",
                4,
                4,
                "pct0_s1s2_canonical_admissible",
            ),
            (
                "M_PCT0_LEAN_04",
                "ProofspaceOmegaPCT0/AuthorityAndAdmission.lean",
                "f15_canonical_admissible_iff_three_gates",
                "end ProofspaceOmegaPCT0",
                "  VerifiedProof certOpt K' &&\n  PCICPolicySatisfied Ph K' &&\n  CommitAuthorized Ph grantOpt K'",
                "  PCICPolicySatisfied Ph K' &&\n  CommitAuthorized Ph grantOpt K'",
                3,
                3,
                "f15_canonical_admissible_iff_three_gates",
            ),
            (
                "M_PCT0_LEAN_05",
                "ProofspaceOmegaPCT0/AuthorityAndAdmission.lean",
                "f15_canonical_admissible_iff_three_gates",
                "end ProofspaceOmegaPCT0",
                "  VerifiedProof certOpt K' &&\n  PCICPolicySatisfied Ph K' &&\n  CommitAuthorized Ph grantOpt K'",
                "  VerifiedProof certOpt K' &&\n  PCICPolicySatisfied Ph K'",
                3,
                3,
                "f15_canonical_admissible_iff_three_gates",
            ),
        ]

        mut_records: List[Dict[str, Any]] = []
        unmutated_exit_map = {r["module"]: (r["exit_code"] == 0) for r in compiled_records}
        for args_m in m_specs:
            mrec = run_single_causal_span_mutation(lean_bin, lean_src_dir, *args_m)
            fail_mod_nm = mrec["proof_break_observation"]["failing_module"]
            mrec["unmutated_baseline_exit_zero"] = bool(unmutated_exit_map.get(fail_mod_nm, False))
            mut_records.append(mrec)
            transcript_chunks.append(
                f"=== MUTATION {mrec['mut_id']} ===\n"
                f"Break(rc={mrec['proof_break_observation']['exit_code']}, line={mrec['proof_break_observation']['first_error_line']}):\n"
                f"{mrec['proof_break_observation']['raw_diagnostic_excerpt']}\n"
                f"Countermodel(dm_rc={mrec['countermodel_refutation_witness']['dm_compile_exit_code']}, "
                f"probe_rc={mrec['countermodel_refutation_witness']['probe_compile_exit_code']}):\n"
                f"{mrec['countermodel_refutation_witness']['probe_raw_stdout']}\n"
            )

        # Run Context A & Context B unit tests inside a separate disposable copy so `unpacked` never gains `__pycache__`
        with tempfile.TemporaryDirectory(prefix="pct0_xh0_utcopy_") as tmp_ut:
            ut_copy = Path(tmp_ut) / "s1s2_ut"
            shutil.copytree(unpacked, ut_copy)

            # Context A: Run extracted unit tests WITH Lean enabled (zero skips allowed!)
            ut_env = dict(os.environ)
            ut_env["PCT0_LEAN_BIN"] = str(lean_bin)
            ut_env["PYTHONDONTWRITEBYTECODE"] = "1"
            ut_pr = subprocess.run(
                [sys.executable, str(ut_copy / "tests" / "test_pct0_s1s2_isolated_and_full.py")],
                cwd=str(ut_copy),
                capture_output=True,
                text=True,
                env=ut_env,
                check=False,
            )
            ci_passed, ci_skipped, ci_failed = parse_unittest_counts((ut_pr.stdout or "") + (ut_pr.stderr or ""), ut_pr.returncode)
            transcript_chunks.append(f"=== CONTEXT A UNIT TESTS (rc={ut_pr.returncode}) ===\n{ut_pr.stderr}\n")

            # Context B (G5): Run extracted unit tests + verifier WITH Lean disabled & parent search disabled
            sbx_env = dict(os.environ)
            sbx_env["PCT0_LEAN_BIN"] = "DISABLED_FOR_G5_SIMULATION"
            sbx_env["PYTHONDONTWRITEBYTECODE"] = "1"
            ut_sbx = subprocess.run(
                [sys.executable, str(ut_copy / "tests" / "test_pct0_s1s2_isolated_and_full.py")],
                cwd=str(ut_copy),
                capture_output=True,
                text=True,
                env=sbx_env,
                check=False,
            )
            sbx_out = (ut_sbx.stdout or "") + (ut_sbx.stderr or "")
            sbx_passed, sbx_skipped, sbx_failed = parse_unittest_counts(sbx_out, ut_sbx.returncode)
            intended_test04_skip = (
                1
                if (
                    sbx_skipped == 1
                    and "test_04_lean_4331_cleanroom_transdeps_and_semantic_mutations" in sbx_out
                    and "Lean 4.33.1 binary not installed" in sbx_out
                )
                else 0
            )
            unexpected_skips = sbx_skipped - intended_test04_skip

            ver_sbx = subprocess.run(
                [sys.executable, str(ut_copy / "src" / "verify_pct0_s1s2_formalization.py"), "--no-write"],
                cwd=str(ut_copy),
                capture_output=True,
                text=True,
                env=sbx_env,
                check=False,
            )
            ver_sbx_json = json.loads(ver_sbx.stdout)

        # Post-execution tree hash re-verification
        post_tree_hashes = {
            p.relative_to(unpacked).as_posix(): sha256_hex(p.read_bytes())
            for p in sorted(unpacked.rglob("*"))
            if p.is_file()
        }

    zip_sha_post = sha256_hex(s1s2_bundle_path.read_bytes())
    pre_post_identical = (zip_sha_pre == zip_sha_post) and (pre_tree_hashes == post_tree_hashes)

    g1_doc = {
        "schema": "PCT0_XH0_G1_SOURCE_LINEAGE_MANIFEST_V3",
        "s1s2_bundle_sha256": zip_sha_pre,
        "s1s2_bundle_size_bytes": zip_size,
        "s1s2_bundle_entries_count": entry_cnt,
        "s1s2_bundle_crc_ok": crc_ok,
        "lean_source_sha256_map": lean_sha_map,
        "embedded_frozen_receipts": frozen_rec_list,
        "pre_post_input_hashes_identical": pre_post_identical,
        "auxiliary_text_prescreen": {
            "clean": aux_prescreen_ok,
            "is_authoritative_ast_proof": False,
            "note": "Auxiliary defense-in-depth only; primary authority is byte SHA-256 + compiled ModuleData.",
        },
    }

    target_mod_imports = []
    for zm in (
        "ProofspaceOmegaPCT0.GenG",
        "ProofspaceOmegaPCT0.GenH",
        "pct0_independent_clean_sheet_probe",
    ):
        target_mod_imports.append(
            {
                "module": zm,
                "olean_sha256": olean_by_mod.get(zm, ""),
                "imports": mod_imports_raw.get(zm, []),
            }
        )

    g2_doc = {
        "schema": "PCT0_XH0_G2_LINUX_KERNEL_COMPILE_AND_SMAP_V3",
        "require_linux_tar_binding": require_lean_archive,
        "lean_archive_sha256": tar_sha,
        "lean_archive_size_bytes": tar_size,
        "lean_binary_sha256": lean_bin_sha,
        "lean_version_banner": lean_banner,
        "zero_import_calibration_imports": mod_imports_raw.get("ZeroImportCalibration", []),
        "target_module_olean_imports": target_mod_imports,
        "compiled_modules": compiled_records,
        "smap_metrics": smap_dict,
    }

    g3_doc = {
        "schema": "PCT0_XH0_G3_TRANSDEPS_AND_AXIOM_AUDIT_V3",
        "transdeps_metrics": tdeps_dict,
        "axiom_footprints": thm_axioms,
        "explicit_epistemic_scope": {
            "axiom_audit_meaning": "Environment-internal transitive axiom reference set inside Lean 4.33.1 (819816b2...); does not prove TCB bug-freedom or empirical scientific truth.",
            "transdeps_meaning": "Kernel constant-closure definitional non-coupling; does not claim cognitive independence against symmetric modeling errors.",
        },
    }

    g4_doc = {
        "schema": "PCT0_XH0_G4_SEMANTIC_MUTATION_RAW_DIAGNOSTICS_V3",
        "mutations": mut_records,
        "context_a_ci_unit_tests": {
            "passed": ci_passed,
            "skipped": ci_skipped,
            "failed": ci_failed,
        },
    }

    g5_doc = {
        "schema": "PCT0_XH0_G5_BOUNDARY_SEPARATION_LEDGER_V3",
        "self_contained_offline_verdict": ver_sbx_json["verdicts"]["self_contained_offline_verdict"],
        "isolated_no_lean_simulation": {
            "overall_poset_verdict": ver_sbx_json["verdicts"]["overall_poset_verdict"],
            "passed": sbx_passed,
            "intended_skips": intended_test04_skip,
            "unexpected_skips": unexpected_skips,
            "failed": sbx_failed,
        },
        "held_boundaries": {
            "empirical_status": "UNASSESSED",
            "f_pct0_17_status": "EXTERNAL_COMMIT_ISSUER_AUTHENTICITY_HELD",
            "concurrent_commit_atomicity": "HELD",
            "pct_s3_s4": "HELD",
            "p1_e1d_release47": "NOT_AUTHORIZED",
        },
    }

    raw_files_to_write: Dict[str, bytes] = {
        "G1_SOURCE_LINEAGE_MANIFEST.json": json.dumps(g1_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n",
        "G2_LINUX_KERNEL_COMPILE_AND_SMAP.json": json.dumps(g2_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n",
        "G3_TRANSDEPS_AND_AXIOM_AUDIT.json": json.dumps(g3_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n",
        "G4_SEMANTIC_MUTATION_RAW_DIAGNOSTICS.json": json.dumps(g4_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n",
        "G5_BOUNDARY_SEPARATION_LEDGER.json": json.dumps(g5_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n",
        "LINUX_LEAN_RAW_TRANSCRIPT.log": ("\n".join(transcript_chunks)).encode("utf-8"),
    }

    bound_file_digests: Dict[str, Dict[str, Any]] = {}
    for fname, fbytes in sorted(raw_files_to_write.items()):
        (out_dir / fname).write_bytes(fbytes)
        bound_file_digests[fname] = {"sha256": sha256_hex(fbytes), "size_bytes": len(fbytes)}

    provenance_doc = {
        "schema": "CAMPUS_PCT0_XH0_SIGNED_PROVENANCE_SUBJECT_V3",
        "stage_id": STAGE_ID,
        "in_ci_verdict_ceiling": "RAW_G1_TO_G5_EVIDENCE_EMITTED__G6_G7_RESERVED_FOR_DETACHED_OFFLINE_EVALUATOR",
        "frozen_s1s2_input_bundle": {
            "filename": s1s2_bundle_path.name,
            "sha256": zip_sha_pre,
            "size_bytes": zip_size,
        },
        "github_and_runner_identity": {
            "github_repository": os.environ.get("GITHUB_REPOSITORY", "LOCAL_PREFLIGHT"),
            "github_workflow_ref": os.environ.get("GITHUB_WORKFLOW_REF", "LOCAL_PREFLIGHT"),
            "github_sha": os.environ.get("GITHUB_SHA", "LOCAL_PREFLIGHT"),
            "github_run_id": os.environ.get("GITHUB_RUN_ID", "LOCAL_PREFLIGHT"),
            "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT", "1"),
            "runner_os": os.environ.get("RUNNER_OS", platform.system()),
            "runner_arch": os.environ.get("RUNNER_ARCH", platform.machine()),
            "host_platform": platform.platform(),
            "python_version": platform.python_version(),
        },
        "raw_evidence_files": bound_file_digests,
    }
    prov_bytes = json.dumps(provenance_doc, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8") + b"\n"
    (out_dir / "PCT0_XH0_SIGNED_PROVENANCE.json").write_bytes(prov_bytes)
    return {
        "provenance_sha256": sha256_hex(prov_bytes),
        "raw_evidence_files": bound_file_digests,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--s1s2-bundle", required=True, type=Path)
    ap.add_argument("--out-dir", required=True, type=Path)
    ap.add_argument("--lean-archive", default=None, type=Path)
    ap.add_argument("--require-lean-archive", action="store_true")
    args = ap.parse_args()

    res = execute_ci_raw_replay(
        s1s2_bundle_path=args.s1s2_bundle,
        out_dir=args.out_dir,
        lean_archive_path=args.lean_archive,
        require_lean_archive=args.require_lean_archive,
    )
    print(json.dumps(res, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
