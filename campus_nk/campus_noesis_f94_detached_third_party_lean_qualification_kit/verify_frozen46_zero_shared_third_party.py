#!/usr/bin/env python3
"""External Zero-Shared-Code Lean 4.33.1 Qualification Auditor for Frozen #46 (`Ωλ-W2`).

96th Independent Static & Physical Tribunal Relock (`F96-01`, `F96-02`, `F96-03`):
  - `F96-01` (`ValidCIEnvironmentVariables !=> AuthenticCIProvenance`):
    Process environment variables (`GITHUB_ACTIONS`, `GITHUB_RUN_ID`, `GITHUB_SHA`, etc.) are
    UNAUTHENTICATED self-reported strings and NEVER elevate independence status!
    This in-process auditor hard-caps its maximum attainable state at:
      * `AUTHOR_HOST_REHEARSAL` (when runtime host fingerprint matches pinned author host), or
      * `DETACHED_HOST_CANDIDATE` with `provenance_status = LIVE_LEAN_REEXECUTED_PROVENANCE_UNVERIFIED`
        (on any non-author host, even if all `GITHUB_*` variables are present).
    Both `DETACHED_EXECUTION_EVIDENCED` and `THIRD_PARTY_SCOPED_VERIFIED` are MECHANICALLY
    FORBIDDEN to this script (`PermissionError` if requested via `--force-state`).
  - `F96-02` (`Post-Execution Cryptographic Attestation Verification Separation`):
    `DETACHED_EXECUTION_EVIDENCED` can ONLY be emitted post-execution by the separate verifier
    `verify_f96_provenance_bundle.py` AFTER verifying a signed Sigstore/OIDC DSSE bundle's
    subject SHA-256, repository, signer workflow, commit SHA, and run ID.
  - `F96-03` (`Clean-Sheet Specification Independence vs Proof-Transport Dependency Disclosure`):
    Explicitly separates:
      1. Auditor-authored proposition independence (`F95CleanSheetAudit.AuditorIndependentSpecification`,
         zero `#46` soundness wrapper defs),
      2. Proof-transport reliance on `#46` theorems (`w2d_packet_sound_relative_to_registry`,
         `ClaimCertSourceSoundRelativeTo`, `f93_03_packet0x03_requires_original_wire_b1_b5`,
         `f93_01_arbitrary_reg_does_not_imply_trusted_a1`, `W2Examples.*`), while independent
         from-scratch re-proof of raw semantics remains `HELD`, and
      3. Lean mock-hash non-vacuity (`W2Examples.mockSelfloopHash256`) vs external empirical
         `hashlib.sha256` verification of the 436-byte `SNAP-PHI-EPLUS-SELFLOOP-A1` `0x05` packet.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import zipfile

# =============================================================================
# 1. Pinned Frozen `#46` (`Ωλ-W2`) & Official `Lean 4.33.1` Release Digests
# =============================================================================

PINNED_ZIP_46_NAME = "CAMPUS_NOESIS_OMEGA_LAMBDA_W2_OUTER_PACKET_AND_SNAPSHOT_REFINEMENT_PACKAGE.zip"
PINNED_ZIP_46_SIZE = 236_214
PINNED_ZIP_46_ENTRIES = 47
PINNED_ZIP_46_CRC32_XOR = "034e36a7"
PINNED_ZIP_46_SHA256 = "4c42f12b605083d13228c02c84e12b4689cdf32be0f507041b6a36360eec4608"

PINNED_MANIFEST_46_PAYLOAD_SHA256 = "06fcd3adee209d3dd29b8826dfa10361480ca5ff1c77a894bb35cece0e1a5acd"
PINNED_MASTER_46_PAYLOAD_SHA256 = "4fe03ce979f076cfb6934e1722d5c73b7e953618846ffd9ce0f9789002367bec"
PINNED_QUALIFICATION_46_PAYLOAD_SHA256 = "ba6d97a57326b93aeccc8b2f92f405930e6c734b966fb15699d981192a9e5af4"

PINNED_COMBINED_DECL_SHA256 = "452f5188bd88d890648c13dbc344de318cae199327c545e9f6138bc1eda8cc6e"
PINNED_W2_NEW_DECL_SHA256 = "1d35cdb7fed127bc6d8345420206839c1d514b22c68e09eb568a5363dccaf9d7"
PINNED_COMBINED_KERNEL_LEDGER_SHA256 = "ebf560d74638c99861db866fc326b3accec556ca4f64efab774890030df484b0"

PINNED_LEAN_VERSION_SUBSTR = "4.33.1"
PINNED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
PINNED_W2D_SCOPE = (
    "SCOPED_CNP2_OUTER_RESILIENCE_PACKETS_0X03_0X05_WITH_CANONICAL_SNAPSHOT_DECODE_EVASION_0X00_A1"
)

PINNED_OFFICIAL_LEAN_4_33_1_ARCHIVES = {
    "lean-4.33.1-linux.tar.zst": {
        "size_bytes": 570_405_234,
        "sha256": "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235",
    },
    "lean-4.33.1-linux.zip": {
        "size_bytes": 896_280_645,
        "sha256": "0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f",
    },
    "lean-4.33.1-darwin_aarch64.zip": {
        "size_bytes": 789_387_245,
        "sha256": "557e9976f853138716ac82b645aab9d75e2bf9ea893113b5a438e4eeb78ed47d",
    },
    "lean-4.33.1-windows.zip": {
        "size_bytes": 842_456_015,
        "sha256": "c39360867edfff6b090f20c16e18581c969ce839b71e813d76022ec04ec73e4d",
    },
}

PINNED_AUTHOR_HOST_FINGERPRINT_SHA256 = (
    "20d3b7d9128cdf243cad418974465a5323086c48141170d76426e63643ab394f"
)

# `F96-01` Hardened Ceiling: In-process script can NEVER emit `DETACHED_EXECUTION_EVIDENCED`
# or `THIRD_PARTY_SCOPED_VERIFIED`!
IN_PROCESS_ATTAINABLE_STATES = (
    "AUTHOR_HOST_REHEARSAL",
    "DETACHED_HOST_CANDIDATE",
)
FORBIDDEN_IN_PROCESS_STATES = (
    "DETACHED_EXECUTION_EVIDENCED",
    "THIRD_PARTY_SCOPED_VERIFIED",
)

# Canonical 436-byte `CNP-v2` `0x05` packet on `#40`'s `SNAP-PHI-EPLUS-SELFLOOP-A1` (`F96-03` empirical witness)
PINNED_REAL_SHA256_0X05_PACKET_HEX = (
    "434e503200020500000001a800000110434e423100010201010000000001ff3300000cf299cb5bee9923ae0d547f48ec"
    "4d60abe582fb05db25c4e5a36a32392e465f00000070001a534e41502d5048492d45504c55532d53454c464c4f4f502d"
    "4131000200024c3000024c310000000000000000000302000949522d4445542d30310000000001000100010200094952"
    "2d4445542d303200010000010000000102000a49522d4c4f4f502d303100000000010000000100000024000000030000"
    "0000000000010001000000000004000000000000000100010000000100010000003e0000000400000000000000010000"
    "000000010000000100010001000000000001000000010001000000020000000200000002000000010001000200000001"
    "000000040000000000000001000100000000000100000001000100010001000000000001000100000001000100000002"
    "000100000000000100000cf299cb5bee9923ae0d547f48ec4d60abe582fb05db25c4e5a36a32392e465fc1600592c86a"
    "c63f9a3384e992bd15dade4a7a5e3b9f6cebebdbe6e05803d08002020000000102000100010001000000010100000000"
    "00010000"
)

F96_03_PROOF_TRANSPORT_DEPENDENCIES = (
    "OmegaLambda.w2d_packet_sound_relative_to_registry",
    "OmegaLambda.ClaimCertSourceSoundRelativeTo",
    "OmegaLambda.f93_03_packet0x03_requires_original_wire_b1_b5",
    "OmegaLambda.f93_01_arbitrary_reg_does_not_imply_trusted_a1",
    "OmegaLambda.W2Examples.w2_ex1_pinned_a1_0x05_gate_ok",
    "OmegaLambda.W2Examples.w2_adv1_f93_03_rank_laundering_rejected",
)

PINNED_ALL_24_LEAN_SHA256 = {
    "lean/OmegaLambda/PointedLTS.lean": "9db60c65b9011eda413e6b2532dc1f2ce9c52fb858494b868f4d47ced2ca2fa0",
    "lean/OmegaLambda/GraphBase.lean": "6a3ae61980e6c055b976cd3336b74d0e7fc3a23b21b808eff6be751f83f97682",
    "lean/OmegaLambda/CarrierLocalGlobal.lean": "dc9e485a9040f0181e1b69030aa4bad28c02653e3d4b4b8f9149a88ed0f8b0db",
    "lean/OmegaLambda/CarrierGeodesic.lean": "cfbba3666c55359d3d6ce0a273a979a12a6bbd3edd3285b3517071d4661cb0c3",
    "lean/OmegaLambda/CheckerSoundness.lean": "37bd33d40f38cac38c4154841549ee75c8e2dcba712394390a66dc95f5345d5b",
    "lean/OmegaLambda/KernelEvalExamples.lean": "66c7a10b28c58b50cd8a14d836aeea5721b9c1a2c3db02b1f7cccfd5987afedb",
    "lean/OmegaLambda/AxiomAudit.lean": "571e36d97bb7ad146031568bce5681e4ed20cd7bf83457108a5b596e9ccc6d3d",
    "lean/OmegaLambda.lean": "49e5182121792e921f85d1dd751efd9e214bed557ea16473f65ce407e1c143cd",
    "lean/OmegaLambda/SourceIRRefinement.lean": "0ff97275bcf9fcfde16490ce40ce98b88f3e0b4a8afc0dfd812cc5f382bfc827",
    "lean/OmegaLambda/SourceIRRefinementExamples.lean": "cd6f2d776a577d128e788a40a67ff1435b73d4ef5743664f2070eca591ce5f6a",
    "lean/OmegaLambda/R1AxiomAudit.lean": "5f97dbd7d627897278000512a302dfb2974220c75db425dce7140dcd059a57fa",
    "lean/OmegaLambdaR1.lean": "6bb6fb95406a7b11a8cbc9c57e9d12b506a8a113ab1dd7b6e85ef1e11ea94dcb",
    "lean/OmegaLambda/CertRefinement.lean": "64c829c969584a83e6e89342e76dee95f7a0f28e3243bf35ef74f2977d855748",
    "lean/OmegaLambda/CertRefinementExamples.lean": "b3a80eb22c6ff3204a172bf3f227462010bf541fb113aadeb170411becf42ab9",
    "lean/OmegaLambda/R2AxiomAudit.lean": "b17c0f4729f39b654692aa45b10d1a6055b3595f296d707412cd40e9b249ca12",
    "lean/OmegaLambdaR2.lean": "488d919bc98bf81b156eb3f0f924b61cfce5c5ee180b88485c67da86c180770d",
    "lean/OmegaLambda/WireRefinement.lean": "04e45dfd11f78e56d6751c2018ce003aa2705e36643ead22895a7393d31a1b0c",
    "lean/OmegaLambda/WireRefinementExamples.lean": "77ccb4510cd290fd574a610ad8c68fe5a0f3021eaaf6586db2c330fc3c024e92",
    "lean/OmegaLambda/W1AxiomAudit.lean": "40610eea2c9a875545f6be5c584ce9faf01b279053fd3b90d80702e174ef71e4",
    "lean/OmegaLambdaW1.lean": "4fd60360ecb6db9db8a7d323264fca8f298a76590e495188a80d8307dea2779c",
    "lean/OmegaLambda/PacketRefinement.lean": "984ac9395607046b76fe0e7b14404fa284678bfbe6ae82fff44273074f2b9c6d",
    "lean/OmegaLambda/PacketRefinementExamples.lean": "5cababe9fb7a3c5bf678f9aed1e96983e1385cc43843646ac1580b5ea4784533",
    "lean/OmegaLambda/W2AxiomAudit.lean": "659f2f840890e0e1c69fa28f011cf61537cec96d55721b5d0a1063e6899fc967",
    "lean/OmegaLambdaW2.lean": "205c48ce111f75c231b501a4e7e335bceb4ea2caf45770d6db068256fbc2d54d",
}

ORDERED_24_MODULES = (
    ("OmegaLambda.PointedLTS", "OmegaLambda/PointedLTS.lean"),
    ("OmegaLambda.GraphBase", "OmegaLambda/GraphBase.lean"),
    ("OmegaLambda.CarrierLocalGlobal", "OmegaLambda/CarrierLocalGlobal.lean"),
    ("OmegaLambda.CarrierGeodesic", "OmegaLambda/CarrierGeodesic.lean"),
    ("OmegaLambda.CheckerSoundness", "OmegaLambda/CheckerSoundness.lean"),
    ("OmegaLambda.KernelEvalExamples", "OmegaLambda/KernelEvalExamples.lean"),
    ("OmegaLambda.AxiomAudit", "OmegaLambda/AxiomAudit.lean"),
    ("OmegaLambda", "OmegaLambda.lean"),
    ("OmegaLambda.SourceIRRefinement", "OmegaLambda/SourceIRRefinement.lean"),
    ("OmegaLambda.SourceIRRefinementExamples", "OmegaLambda/SourceIRRefinementExamples.lean"),
    ("OmegaLambda.R1AxiomAudit", "OmegaLambda/R1AxiomAudit.lean"),
    ("OmegaLambdaR1", "OmegaLambdaR1.lean"),
    ("OmegaLambda.CertRefinement", "OmegaLambda/CertRefinement.lean"),
    ("OmegaLambda.CertRefinementExamples", "OmegaLambda/CertRefinementExamples.lean"),
    ("OmegaLambda.R2AxiomAudit", "OmegaLambda/R2AxiomAudit.lean"),
    ("OmegaLambdaR2", "OmegaLambdaR2.lean"),
    ("OmegaLambda.WireRefinement", "OmegaLambda/WireRefinement.lean"),
    ("OmegaLambda.WireRefinementExamples", "OmegaLambda/WireRefinementExamples.lean"),
    ("OmegaLambda.W1AxiomAudit", "OmegaLambda/W1AxiomAudit.lean"),
    ("OmegaLambdaW1", "OmegaLambdaW1.lean"),
    ("OmegaLambda.PacketRefinement", "OmegaLambda/PacketRefinement.lean"),
    ("OmegaLambda.PacketRefinementExamples", "OmegaLambda/PacketRefinementExamples.lean"),
    ("OmegaLambda.W2AxiomAudit", "OmegaLambda/W2AxiomAudit.lean"),
    ("OmegaLambdaW2", "OmegaLambdaW2.lean"),
)

FORBIDDEN_REGEXES = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\s+"),
    re.compile(r"(?m)^\s*opaque\s+"),
    re.compile(r"(?m)^\s*constant\s+"),
    re.compile(r"\bnative_decide\b"),
    re.compile(r"\bofReduceBool\b"),
    re.compile(r"\btrustCompiler\b"),
    re.compile(r"\bimplemented_by\b"),
    re.compile(r"@\[[^\]]*\bextern\b"),
    re.compile(r"\bunsafe\b"),
    re.compile(r"(?m)^\s*partial\s+def\b"),
)

DECL_HEAD_RE = re.compile(r"^(theorem|def)\s+([A-Za-z_][A-Za-z0-9_'?.]*)")
NS_OPEN_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'?.]*)")
NS_END_RE = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_'?.]*)")
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


# =============================================================================
# 2. `F95-03` / `F96-03` Clean-Sheet Specification (`S_ext`) + Proof Transport
#    - Specification `AuditorIndependentSpecification` uses ZERO `#46` soundness
#      wrappers (`PinnedA1SourceSoundness`, `SourceSoundnessRelativeTo`, etc.).
#    - Proof `f95_clean_sheet_specification_verified` transports `#46`'s existing
#      theorems (`F96_03_PROOF_TRANSPORT_DEPENDENCIES`) across the Lean kernel;
#      from-scratch independent re-proof of raw semantics remains `HELD`.
# =============================================================================

F95_CLEAN_SHEET_SPEC_LEAN = r"""import OmegaLambdaW2

namespace F95CleanSheetAudit

open OmegaLambda

/-- Auditor-authored literal 15-row A1 anchor table (`(snapshotId, gen, rootHex, constIds)`). -/
def auditorLiteralA1Table15 : List (String × Nat × String × List String) :=
  [ ("SNAP-KAPPA-F78-NONPRES-V1-A1", 1, "eabf4d6fdc3108a23b75b82016cdd7b888a07f849cd440f622c518e035aa09fc", []),
    ("SNAP-KAPPA-F78-NONPRES-V2-A1", 2, "5c725ca262b23e67a74e716bc6bf4ba796713c2e13bfaf4ff7c3239c15eab18f", []),
    ("SNAP-KAPPA-F78-SIGMA1-A1", 1, "d98c8af02b46cf8d3e1f953308320b7b95341e95337f26b5cbd80e2c513c5eda", []),
    ("SNAP-KAPPA-F78-SIGMA2-PROMOTE-A1", 2, "6304003f79db330ee67841d22cde03346049db826618a0e0f5e876fb29fcab40", ["IR-00-CONST-K"]),
    ("SNAP-PHI-ABC-V1-A1", 1, "dace9001d106fbe91d011fe24eefd80ba5a2d413223c0c31d2ecfec2279e74df", []),
    ("SNAP-PHI-ABC-V2-A1", 2, "831a99beff076fde0739591566c52716f702d23a3cabc3039973f76e453c6d53", []),
    ("SNAP-PHI-BUDGET-14-A1", 1, "556b6c3427f058b9b99988b69b496ede00a38a5c6a0be99c46421ff6171f1b5f", []),
    ("SNAP-PHI-EPLUS-SELFLOOP-A1", 1, "0cf299cb5bee9923ae0d547f48ec4d60abe582fb05db25c4e5a36a32392e465f", []),
    ("SNAP-PHI-K3-EXACT3-SERIES-A1", 1, "fcfc41e39d7e424241f21ce3bf7198e76842c0abe6efd31e7b28e47d1edb968e", ["IR-CONST-S"]),
    ("SNAP-PHI-K3-PARALLEL-MIXED-A1", 1, "9fb25ac0777f10a8d1cd0dc0bdd7a4fc70ecfa549d8550c92c872ea0d4d6d85b", ["IR-CONST-K1", "IR-CONST-K2", "IR-CONST-K3", "IR-CONST-M1", "IR-CONST-M2"]),
    ("SNAP-PHI-K3-SERIES-A1", 1, "a1e355aae21f67e9f9ab43b0d608c4f43cb591f57b297d1c1fe9a513bb920fe0", []),
    ("SNAP-PHI-PRIMARY-V2-A1", 2, "88c2360342bcaa4542e1e2eb7fecab9b17953aea81a76d79f1ed21898442fa7b", []),
    ("SNAP-PHI-RESILIENCE-DIAMOND-A1", 1, "1dfda8adb25f331a29d8105c6c9fb54637c6831a33937c1b10c6b4fedc25f1a7", ["IR-CONST-00"]),
    ("SNAP-R2-CYCLIC-A1", 1, "589dc2d810175c6550a944c8ce28f8e6dc2e98bc998d8e8736f4edf7fbc75891", []),
    ("SNAP-R2-PRIMARY-DAG-A1", 1, "345bc1f820bcd1ed50ab18d41eacd243bb2864a4e2862e7ad5361400fdd1554f", []) ]

/-- Auditor-authored first-order string-retraction resilience predicate (`0` W2/W1/R2 wrappers). -/
def AuditorUnfoldedStringResilience
    (snap : SourceSnapshot) (pinnedConstIds : List String)
    (κ : ClosureKind) (qS qT : Nat) (cSpec : CarrierSpec)
    (modeTag claimedL claimedU : Nat) : Prop :=
  let remIds := sourceRemRecordIds snap pinnedConstIds
  (modeTag = 1 ∧ claimedL = 0 ∧ claimedU = 0 ∧
    ∀ D_str : List String,
      (∀ rid ∈ D_str, rid ∈ remIds) →
      SourceCarrierSurvivesStr snap κ qS qT cSpec D_str) ∨
  (modeTag = 2 ∧ 1 ≤ claimedL ∧ claimedL ≤ claimedU ∧
    (∀ D_str : List String,
      NodupList D_str →
      (∀ rid ∈ D_str, rid ∈ remIds) →
      ¬ SourceCarrierSurvivesStr snap κ qS qT cSpec D_str →
      claimedL ≤ D_str.length) ∧
    (∃ D_str_star : List String,
      NodupList D_str_star ∧
      (∀ rid ∈ D_str_star, rid ∈ remIds) ∧
      D_str_star.length ≤ claimedU ∧
      ¬ SourceCarrierSurvivesStr snap κ qS qT cSpec D_str_star))

/-- **`F95-03` Clean-Sheet Independent Specification (`S_ext`)**:
    Note (`F96-03`): Conjunct (2) proves gate non-vacuity under an abstract `H : ByteArray → ByteArray`
    oracle (`W2Examples.mockSelfloopHash256`), NOT internal FIPS 180-4 SHA-256 execution. -/
def AuditorIndependentSpecification : Prop :=
  -- (1) Universal Soundness from Raw Bytes to Unfolded String-Record Retractions
  (∀ (H : ByteArray → ByteArray) (rawPacket : ByteArray),
    checkCnp2ResiliencePacketPinnedA1_0x00 H rawPacket = true →
    ∃ pkt : RawCnp2ResiliencePacket0x00,
      decodeCnp2ResiliencePacket0x00 rawPacket = some pkt ∧
      encodeCnp2ResiliencePacket0x00 pkt = some rawPacket ∧
      match pkt with
      | .kind0x03 base qS qT cIdxs locPaths _locBh locCert _globBh globCert =>
          let snap := projectRawToSourceSnapshot H base.hdr base.rawSnap
          let κ := if base.hdr.closureTag = 1 then ClosureKind.eStar else ClosureKind.ePlus
          ∃ (pinnedGen : Nat) (pinnedConstIds : List String) (bSnap : ByteArray),
            (snap.snapshotId, pinnedGen, snap.computedRootHex, pinnedConstIds) ∈ auditorLiteralA1Table15 ∧
            snap.authTierTag = 1 ∧
            snap.policyMask = 0xFF33 ∧
            encodeSnapshotSection base.rawSnap = some bSnap ∧
            decodeSnapshotSection bSnap = some base.rawSnap ∧
            checkCNB1B1Bool H pinnedOmegaKappaA1Registry15 base cIdxs = true ∧
            checkCNB1B2Bool H base = true ∧
            checkCNB1B3Bool base = true ∧
            checkCNB1B4Bool base = true ∧
            checkCNB1B5Bool base = true ∧
            (qS, qT) ∈ base.candidateRelations ∧
            locCert.evasionModeTag = 0 ∧
            globCert.evasionModeTag = 0 ∧
            AuditorUnfoldedStringResilience snap pinnedConstIds κ qS qT (.localPacket locPaths)
              locCert.modeTag locCert.claimedL locCert.claimedU ∧
            AuditorUnfoldedStringResilience snap pinnedConstIds κ qS qT .globalGraph
              globCert.modeTag globCert.claimedL globCert.claimedU
      | .kind0x05 base hopEntries qS qT _cIdxs _geoBh geoCert =>
          let snap := projectRawToSourceSnapshot H base.hdr base.rawSnap
          let κ := if base.hdr.closureTag = 1 then ClosureKind.eStar else ClosureKind.ePlus
          ∃ (pinnedGen : Nat) (pinnedConstIds : List String) (bSnap : ByteArray),
            (snap.snapshotId, pinnedGen, snap.computedRootHex, pinnedConstIds) ∈ auditorLiteralA1Table15 ∧
            snap.authTierTag = 1 ∧
            snap.policyMask = 0xFF33 ∧
            encodeSnapshotSection base.rawSnap = some bSnap ∧
            decodeSnapshotSection bSnap = some base.rawSnap ∧
            checkCNB1B6Bool base hopEntries = true ∧
            geoCert.evasionModeTag = 0 ∧
            AuditorUnfoldedStringResilience snap pinnedConstIds κ qS qT .geodesicBundle
              geoCert.modeTag geoCert.claimedL geoCert.claimedU) ∧
  -- (2) Abstract-Oracle Non-Vacuity Canary (`F96-03`: mock oracle `H`, not FIPS SHA-256)
  (∃ (H : ByteArray → ByteArray) (rawPkt : ByteArray),
    checkCnp2ResiliencePacketPinnedA1_0x00 H rawPkt = true) ∧
  -- (3) F93-01 Canary: Relative registry acceptance does NOT imply Pinned A1 acceptance
  (∃ (H : ByteArray → ByteArray) (regForged : List PinnedA1Entry) (rawPkt : ByteArray),
    checkCnp2ResiliencePacket0x00 H regForged rawPkt = true ∧
    checkCnp2ResiliencePacketPinnedA1_0x00 H rawPkt = false) ∧
  -- (4) F93-03 Canary: Decodable 0x03 packet with laundered wire witness rank is rejected
  (∃ (H : ByteArray → ByteArray) (reg : List PinnedA1Entry) (rawPkt03 : ByteArray),
    (decodeCnp2ResiliencePacket0x00 rawPkt03).isSome = true ∧
    checkCnp2ResiliencePacket0x00 H reg rawPkt03 = false)

theorem lookupPinnedA1_mem_and_id {sid : String} {reg : List PinnedA1Entry} {ent : PinnedA1Entry}
    (h : lookupPinnedA1 sid reg = some ent) :
    ent ∈ reg ∧ ent.snapshotId = sid := by
  induction reg with
  | nil => cases h
  | cons hd tl ih =>
    unfold lookupPinnedA1 at h
    split at h
    · next heq =>
      injection h with hEqEnt
      subst hEqEnt
      exact ⟨List.Mem.head tl, heq⟩
    · exact ⟨List.Mem.tail hd (ih h).1, (ih h).2⟩

theorem auditor_table_eq_pinned15 :
    pinnedOmegaKappaA1Registry15.map (fun e => (e.snapshotId, e.pinnedGen, e.pinnedRootHex, e.pinnedConstIds)) =
      auditorLiteralA1Table15 := rfl

theorem unfold_claimCert_to_auditor
    {reg : List PinnedA1Entry} {snap : SourceSnapshot} {ent : PinnedA1Entry}
    {κ : ClosureKind} {qS qT : VertexId} {cSpec : CarrierSpec} {T : SourceCertTerm}
    (hlk : lookupPinnedA1 snap.snapshotId reg = some ent)
    (h : ClaimCertSourceSoundRelativeTo reg snap κ qS qT cSpec T) :
    T.evasionModeTag = 0 ∧
    snap.authTierTag = 1 ∧
    snap.policyMask = 0xFF33 ∧
    snap.computedRootHex = ent.pinnedRootHex ∧
    AuditorUnfoldedStringResilience snap ent.pinnedConstIds κ qS qT cSpec T.modeTag T.claimedL T.claimedU := by
  rcases h with ⟨hev0, hbranch⟩
  cases hbranch with
  | inl h1 =>
    rcases h1 with ⟨hm1, hL0, hU0, ent', hlk', htier, hmask, hroot, _, _, hcl⟩
    rw [hlk] at hlk'
    injection hlk' with heq
    subst heq
    exact ⟨hev0, htier, hmask, hroot, Or.inl ⟨hm1, hL0, hU0, hcl⟩⟩
  | inr h2 =>
    rcases h2 with ⟨hm2, hL1, hLU, ent', hlk', htier, hmask, hroot, _, _, hcl⟩
    rw [hlk] at hlk'
    injection hlk' with heq
    subst heq
    rcases hcl with ⟨_, hlow, hup⟩
    exact ⟨hev0, htier, hmask, hroot, Or.inr ⟨hm2, hL1, hLU, hlow, hup⟩⟩

/-- Proof-transport theorem `P : S_ext` (`F96-03`: transports Release #46 theorems to `S_ext`). -/
theorem f95_clean_sheet_specification_verified : AuditorIndependentSpecification := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H rawPacket hPinOk
    have hRel := w2d_packet_sound_relative_to_registry H pinnedOmegaKappaA1Registry15 rawPacket hPinOk
    rcases hRel with ⟨pkt, hdec, henc, hbody⟩
    refine ⟨pkt, hdec, henc, ?_⟩
    cases pkt with
    | kind0x03 base qS qT cIdxs locPaths locBh locCert globBh globCert =>
      dsimp only at hbody ⊢
      rcases hbody with ⟨ent, bSnap, _bLoc, _bGlob, hlk, hencS, hdecS, _hG1, _dL, _dG, hSLoc, hSGlob⟩
      rcases f93_03_packet0x03_requires_original_wire_b1_b5
          H pinnedOmegaKappaA1Registry15 rawPacket base qS qT cIdxs locPaths locBh locCert globBh globCert
          hdec hPinOk with
        ⟨hb1, hb2, hb3, hb4, hb5, hrel⟩
      rcases lookupPinnedA1_mem_and_id hlk with ⟨hmemReg, hsidEq⟩
      rcases unfold_claimCert_to_auditor hlk hSLoc with ⟨hevL, htier, hmask, hrootEq, hAudLoc⟩
      rcases unfold_claimCert_to_auditor hlk hSGlob with ⟨hevG, _, _, _, hAudGlob⟩
      have hmemTbl :
          (ent.snapshotId, ent.pinnedGen, ent.pinnedRootHex, ent.pinnedConstIds) ∈ auditorLiteralA1Table15 := by
        rw [← auditor_table_eq_pinned15]
        exact List.mem_map_of_mem
          (f := fun e : PinnedA1Entry => (e.snapshotId, e.pinnedGen, e.pinnedRootHex, e.pinnedConstIds)) hmemReg
      rw [hsidEq, ← hrootEq] at hmemTbl
      exact ⟨ent.pinnedGen, ent.pinnedConstIds, bSnap, hmemTbl, htier, hmask, hencS, hdecS,
             hb1, hb2, hb3, hb4, hb5, hrel, hevL, hevG, hAudLoc, hAudGlob⟩
    | kind0x05 base hopEntries qS qT _cIdxs _geoBh geoCert =>
      dsimp only at hbody ⊢
      rcases hbody with ⟨ent, bSnap, _bGeo, hlk, hencS, hdecS, hb6, _dGeo, hSGeo⟩
      rcases lookupPinnedA1_mem_and_id hlk with ⟨hmemReg, hsidEq⟩
      rcases unfold_claimCert_to_auditor hlk hSGeo with ⟨hevGeo, htier, hmask, hrootEq, hAudGeo⟩
      have hmemTbl :
          (ent.snapshotId, ent.pinnedGen, ent.pinnedRootHex, ent.pinnedConstIds) ∈ auditorLiteralA1Table15 := by
        rw [← auditor_table_eq_pinned15]
        exact List.mem_map_of_mem
          (f := fun e : PinnedA1Entry => (e.snapshotId, e.pinnedGen, e.pinnedRootHex, e.pinnedConstIds)) hmemReg
      rw [hsidEq, ← hrootEq] at hmemTbl
      exact ⟨ent.pinnedGen, ent.pinnedConstIds, bSnap, hmemTbl, htier, hmask, hencS, hdecS,
             hb6, hevGeo, hAudGeo⟩
  · exact ⟨W2Examples.mockSelfloopHash256, W2Examples.ex1Packet0x05Bytes,
           W2Examples.w2_ex1_pinned_a1_0x05_gate_ok⟩
  · rcases f93_01_arbitrary_reg_does_not_imply_trusted_a1 with ⟨H, regF, pktF, h1, _, h3⟩
    exact ⟨H, regF, pktF, h1, h3⟩
  · rcases W2Examples.w2_adv1_f93_03_rank_laundering_rejected with ⟨hdec03, _, hrej03⟩
    refine ⟨constZeroHash32, W2Examples.ex2Reg03, W2Examples.adv1BadRank0x03Bytes, ?_, hrej03⟩
    rw [hdec03]; rfl

#print axioms F95CleanSheetAudit.f95_clean_sheet_specification_verified

end F95CleanSheetAudit
"""

F95_DETACHED_INSPECTOR_LEAN = r"""import OmegaLambdaW2
import Lean

open Lean

def cinfoVariant : ConstantInfo → String
  | .axiomInfo _ => "axiomInfo"
  | .defnInfo _ => "defnInfo"
  | .thmInfo _ => "thmInfo"
  | .opaqueInfo _ => "opaqueInfo"
  | .quotInfo _ => "quotInfo"
  | .inductInfo _ => "inductInfo"
  | .ctorInfo _ => "ctorInfo"
  | .recInfo _ => "recInfo"

def isProjectPrefix : Name → Bool
  | .anonymous => false
  | .str .anonymous s =>
      s == "OmegaLambda" || s == "OmegaLambdaR1" || s == "OmegaLambdaR2" || s == "OmegaLambdaW1" || s == "OmegaLambdaW2"
  | .str p _ => isProjectPrefix p
  | .num p _ => isProjectPrefix p

def targetMods : Array Name := #[
  `OmegaLambda.PointedLTS, `OmegaLambda.GraphBase, `OmegaLambda.CarrierLocalGlobal,
  `OmegaLambda.CarrierGeodesic, `OmegaLambda.CheckerSoundness, `OmegaLambda.KernelEvalExamples,
  `OmegaLambda.AxiomAudit, `OmegaLambda,
  `OmegaLambda.SourceIRRefinement, `OmegaLambda.SourceIRRefinementExamples,
  `OmegaLambda.R1AxiomAudit, `OmegaLambdaR1,
  `OmegaLambda.CertRefinement, `OmegaLambda.CertRefinementExamples,
  `OmegaLambda.R2AxiomAudit, `OmegaLambdaR2,
  `OmegaLambda.WireRefinement, `OmegaLambda.WireRefinementExamples,
  `OmegaLambda.W1AxiomAudit, `OmegaLambdaW1,
  `OmegaLambda.PacketRefinement, `OmegaLambda.PacketRefinementExamples,
  `OmegaLambda.W2AxiomAudit, `OmegaLambdaW2
]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut idxPairs : Array (Nat × String) := #[]
  for m in targetMods do
    match env.getModuleIdx? m with
    | some idx => idxPairs := idxPairs.push (idx.toNat, m.toString)
    | none => throwError s!"FATAL: Missing module {m}"
  let allowed : List Name := [`propext, `Quot.sound, `Classical.choice]
  for (name, cinfo) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    let inProj := isProjectPrefix name
    match env.getModuleIdxFor? name with
    | some midx =>
      match idxPairs.find? (fun (i, _) => i == midx.toNat) with
      | some (_, modStr) =>
        let kindStr := cinfoVariant cinfo
        if kindStr == "axiomInfo" || kindStr == "opaqueInfo" then
          throwError s!"FATAL: Forbidden {kindStr} constant {name} in {modStr}"
        let axs ← collectAxioms name
        for ax in axs do
          let s := ax.toString
          if !(allowed.contains ax) || (s.splitOn "sorry").length > 1 || (s.splitOn "._native.").length > 1 then
            throwError s!"FATAL: Disallowed axiom {ax} in {name}"
        let axCsv := String.intercalate "," (axs.toList.map Name.toString)
        IO.println s!"CONST_ROW|{modStr}|{kindStr}|{name}|{axCsv}"
      | none =>
        if inProj then
          throwError s!"FATAL: Orphan project constant outside target modules: {name}"
    | none =>
      if inProj then
        throwError s!"FATAL: Unattributed local constant in project namespace: {name}"
"""


# =============================================================================
# 3. `F96-01`, `F96-02`, `F96-03` Hardened Classification & Witness Checks
# =============================================================================

def canonical_payload_sha256(obj: dict) -> str:
    body = {k: v for k, v in obj.items() if k != "seal"}
    raw = json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def seal_external_receipt(payload: dict) -> dict:
    body = {k: v for k, v in payload.items() if k != "seal"}
    out = dict(body)
    out["seal"] = {
        "algorithm": "SHA-256",
        "canonicalization": "CAMPUS_CANONICAL_JSON_UTF8_SORTED_KEYS_V1",
        "payload_sha256": canonical_payload_sha256(body),
    }
    return out


def compute_anonymized_host_fingerprint() -> str:
    raw = f"{platform.node()}|{platform.system()}|{platform.machine()}".encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def collect_environment_telemetry(env_map: dict[str, str]) -> dict:
    """Record process environment as UNAUTHENTICATED telemetry only (`F96-01`)."""
    dockerenv = Path("/.dockerenv").exists()
    wsl_detected = False
    osrel_path = Path("/proc/sys/kernel/osrelease")
    if osrel_path.is_file():
        try:
            txt = osrel_path.read_text(encoding="utf-8", errors="ignore").lower()
            wsl_detected = ("microsoft" in txt) or ("wsl" in txt)
        except OSError:
            pass
    unauthenticated_ci_env = {
        "github_actions": env_map.get("GITHUB_ACTIONS", ""),
        "github_run_id": env_map.get("GITHUB_RUN_ID", ""),
        "github_run_attempt": env_map.get("GITHUB_RUN_ATTEMPT", ""),
        "github_sha": env_map.get("GITHUB_SHA", ""),
        "github_repository": env_map.get("GITHUB_REPOSITORY", ""),
        "runner_os": env_map.get("RUNNER_OS", ""),
        "runner_arch": env_map.get("RUNNER_ARCH", ""),
    }
    return {
        "docker_container_detected": dockerenv,
        "wsl_kernel_detected": wsl_detected,
        "cryptographically_authenticated_in_process": False,
        "unauthenticated_self_reported_ci_env": unauthenticated_ci_env,
    }


def classify_f96_01_in_process_state(
    runtime_host_fp: str,
    _telemetry: dict,
    requested_max_state: str | None = None,
) -> str:
    """`F96-01` Spoof-Resistant In-Process Classifier.

    - `_telemetry` (including `GITHUB_*` env vars) is NEVER used to elevate state!
    - Requesting `DETACHED_EXECUTION_EVIDENCED` or `THIRD_PARTY_SCOPED_VERIFIED` ALWAYS raises
      `PermissionError` (only post-execution cryptographic bundle verification in
      `verify_f96_provenance_bundle.py` can emit `DETACHED_EXECUTION_EVIDENCED`, and only the
      Tribunal can emit `THIRD_PARTY_SCOPED_VERIFIED`).
    """
    if requested_max_state in FORBIDDEN_IN_PROCESS_STATES:
        raise PermissionError(
            f"F96-01 VIOLATION: {requested_max_state} CANNOT be emitted by an in-process execution "
            "script because process environment variables are unauthenticated. Use "
            "verify_f96_provenance_bundle.py on a signed Sigstore bundle after CI finishes."
        )
    if requested_max_state is not None and requested_max_state not in IN_PROCESS_ATTAINABLE_STATES:
        raise ValueError(f"Unknown F96-01 state: {requested_max_state!r}")

    if runtime_host_fp == PINNED_AUTHOR_HOST_FINGERPRINT_SHA256:
        return "AUTHOR_HOST_REHEARSAL"
    if requested_max_state == "AUTHOR_HOST_REHEARSAL":
        return "AUTHOR_HOST_REHEARSAL"
    return "DETACHED_HOST_CANDIDATE"


def verify_empirical_real_sha256_0x05_witness() -> dict:
    """`F96-03` Empirical FIPS `SHA-256` Check on 436-Byte `SNAP-PHI-EPLUS-SELFLOOP-A1` `0x05` Packet.

    Distinct from Lean's `mockSelfloopHash256` non-vacuity canary: verifies using stdlib
    `hashlib.sha256` that a concrete 436-byte `0x05` wire packet satisfies exact `CNB-v1`
    `Snapshot` (`0cf299cb...465f`) and `CNP-v2` `C2` `Carrier` (`c1600592...080`) digests.
    """
    pkt = bytes.fromhex(PINNED_REAL_SHA256_0X05_PACKET_HEX)
    if len(pkt) != 436:
        raise RuntimeError("Empirical 0x05 packet length mismatch")
    magic, ver, pkind, ev_mode, body_len = struct.unpack_from(">4sHBBI", pkt, 0)
    if (magic, ver, pkind, ev_mode, 12 + body_len) != (b"CNP2", 2, 5, 0, 436):
        raise RuntimeError("Empirical 0x05 outer header mismatch")
    (cnb_len,) = struct.unpack_from(">I", pkt, 12)
    cnb = pkt[16 : 16 + cnb_len]
    (snap_len,) = struct.unpack_from(">I", cnb, 50)
    snap_slice = cnb[54 : 54 + snap_len]
    snap_pre = b"CAMPUS_NOESIS_CNB1_SNAPSHOT_V1\x00" + struct.pack(">IH", 1, 0xFF33) + snap_slice
    h_sigma = hashlib.sha256(snap_pre).digest()
    if h_sigma.hex() != "0cf299cb5bee9923ae0d547f48ec4d60abe582fb05db25c4e5a36a32392e465f":
        raise RuntimeError("Empirical 0x05 FIPS SHA-256 snapshot root mismatch")
    if cnb[18:50] != h_sigma:
        raise RuntimeError("Empirical 0x05 CNB-v1 header root mismatch")

    geo_off = 16 + cnb_len
    # Geodesic carrier payload is 52 bytes (`4` entries), followed by 6B query/const (`0, 1, 0`) and 70B bind header
    car_slice = pkt[geo_off : geo_off + 52]
    q_s, q_t, c_cnt = struct.unpack_from(">HHH", pkt, geo_off + 52)
    if (q_s, q_t, c_cnt) != (0, 1, 0):
        raise RuntimeError("Empirical 0x05 query/const tuple mismatch")
    bh_off = geo_off + 58
    bh_hsig, bh_hcar, bh_clo, bh_ctag, bh_qs, bh_qt = struct.unpack_from(">32s32sBBHH", pkt, bh_off)
    car_pre = (
        b"CAMPUS_NOESIS_CNP2_CARRIER_V1\x00"
        + struct.pack(">B", 2)
        + h_sigma
        + struct.pack(">BHH", 2, 0, 1)
        + car_slice
    )
    h_car = hashlib.sha256(car_pre).digest()
    if (bh_hsig, bh_hcar, bh_clo, bh_ctag, bh_qs, bh_qt) != (h_sigma, h_car, 2, 2, 0, 1):
        raise RuntimeError("Empirical 0x05 FIPS SHA-256 carrier bind header mismatch")
    return {
        "packet_size_bytes": 436,
        "packet_sha256": hashlib.sha256(pkt).hexdigest(),
        "snapshot_fips_sha256": h_sigma.hex(),
        "carrier_fips_sha256": h_car.hex(),
        "scope_note": "EMPIRICAL_PYTHON_STDLIB_SHA256_WITNESS_ONLY_NOT_LEAN_KERNEL_SHA256_PROOF",
    }


def verify_optional_lean_archive(archive_path: Path) -> dict:
    spec = PINNED_OFFICIAL_LEAN_4_33_1_ARCHIVES.get(archive_path.name)
    if spec is None:
        raise ValueError(
            f"F95-02 VIOLATION: Unrecognized archive name {archive_path.name!r}; "
            f"expected one of {sorted(PINNED_OFFICIAL_LEAN_4_33_1_ARCHIVES)}"
        )
    raw = archive_path.read_bytes()
    act_sha = hashlib.sha256(raw).hexdigest()
    if len(raw) != spec["size_bytes"] or act_sha != spec["sha256"]:
        raise RuntimeError(
            f"F95-02 VIOLATION: Official Lean 4.33.1 archive mismatch on {archive_path.name}: "
            f"size={len(raw)} (exp {spec['size_bytes']}), sha256={act_sha} (exp {spec['sha256']})"
        )
    return {"archive_name": archive_path.name, "size_bytes": len(raw), "sha256": act_sha}


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        if depth == 0 and not in_str:
            if text.startswith("/-", i):
                depth = 1
                i += 2
                continue
            if text.startswith("--", i):
                while i < n and text[i] != "\n":
                    i += 1
                continue
            if text[i] == '"':
                in_str = True
                out.append('""')
                i += 1
                continue
            out.append(text[i])
            i += 1
        elif in_str:
            if text[i] == "\\" and i + 1 < n:
                i += 2
                continue
            if text[i] == '"':
                in_str = False
            i += 1
        else:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def audit_declarations(lean_dir: Path, modules: tuple[tuple[str, str], ...]) -> tuple[int, int, str]:
    decls: list[tuple[str, str]] = []
    for _, rel_path in modules:
        raw_bytes = (lean_dir / rel_path).read_bytes()
        if b"\r" in raw_bytes:
            raise RuntimeError(f"CR byte detected in {rel_path}")
        cleaned = strip_lean_comments_and_strings(raw_bytes.decode("utf-8"))
        for rx in FORBIDDEN_REGEXES:
            if rx.search(cleaned):
                raise RuntimeError(f"Forbidden token {rx.pattern} in {rel_path}")
        ns_stack: list[str] = []
        for line in cleaned.splitlines():
            sline = line.strip()
            m_open = NS_OPEN_RE.match(sline)
            if m_open:
                ns_stack.append(m_open.group(1))
                continue
            m_end = NS_END_RE.match(sline)
            if m_end and ns_stack:
                ns_stack.pop()
                continue
            if line and not line[0].isspace():
                m_decl = DECL_HEAD_RE.match(line)
                if m_decl:
                    kind, short = m_decl.group(1), m_decl.group(2)
                    prefix = ".".join(ns_stack)
                    fqn = f"{prefix}.{short}" if prefix else short
                    decls.append((kind, fqn))
    thm_c = sum(1 for k, _ in decls if k == "theorem")
    def_c = sum(1 for k, _ in decls if k == "def")
    canon_lines = "\n".join(sorted(f"{k}:{nm}" for k, nm in decls)) + "\n"
    d_sha = hashlib.sha256(canon_lines.encode("utf-8")).hexdigest()
    return thm_c, def_c, d_sha


def find_lean() -> Path | None:
    env_bin = os.environ.get("LEAN_BIN")
    if env_bin is not None:
        return Path(env_bin) if (env_bin.strip() and Path(env_bin).is_file()) else None
    which_p = shutil.which("lean")
    if which_p:
        return Path(which_p)
    exe = "lean.exe" if os.name == "nt" else "lean"
    for cand in (
        Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.33.1" / "bin" / exe,
        Path.home() / ".elan" / "bin" / exe,
    ):
        if cand.is_file():
            return cand
    return None


def parse_clean_sheet_axioms(stdout_text: str) -> list[str]:
    joined = " ".join(ln.strip() for ln in stdout_text.splitlines() if ln.strip())
    m_dep = re.match(
        r"^'F95CleanSheetAudit\.f95_clean_sheet_specification_verified' depends on axioms: \[([^\]]*)\]$",
        joined,
    )
    if m_dep:
        axs = sorted(x.strip() for x in m_dep.group(1).split(",") if x.strip())
        if not set(axs).issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"Disallowed axioms on Clean-Sheet Spec: {axs}")
        return axs
    if joined == "'F95CleanSheetAudit.f95_clean_sheet_specification_verified' does not depend on any axioms":
        return []
    raise RuntimeError(f"Unexpected #print axioms output on Clean-Sheet Spec: {stdout_text!r}")


def run_f96_guard_self_tests() -> dict:
    """8 deterministic guard self-tests, including the 96th Tribunal's exact `attacker/repo` counterexample."""
    # 1. Forcing `THIRD_PARTY_SCOPED_VERIFIED` MUST raise PermissionError
    try:
        classify_f96_01_in_process_state("ffffffff" * 8, {}, requested_max_state="THIRD_PARTY_SCOPED_VERIFIED")
        raise AssertionError("Failed to reject THIRD_PARTY_SCOPED_VERIFIED")
    except PermissionError:
        pass

    # 2. Forcing `DETACHED_EXECUTION_EVIDENCED` in-process MUST raise PermissionError (`F96-01`)
    try:
        classify_f96_01_in_process_state("ffffffff" * 8, {}, requested_max_state="DETACHED_EXECUTION_EVIDENCED")
        raise AssertionError("Failed to reject in-process DETACHED_EXECUTION_EVIDENCED")
    except PermissionError:
        pass

    # 3. 96th Tribunal §2 Exact Counterexample:
    #    Distinct host fingerprint + forged `attacker/repo` `GITHUB_*` env vars MUST NEVER reach
    #    `DETACHED_EXECUTION_EVIDENCED`; it MUST stay `DETACHED_HOST_CANDIDATE`!
    tribunal_96_counterexample_env = collect_environment_telemetry({
        "GITHUB_ACTIONS": "true",
        "GITHUB_RUN_ID": "12345",
        "GITHUB_SHA": "a" * 40,
        "GITHUB_REPOSITORY": "attacker/repo",
        "RUNNER_OS": "Linux",
    })
    if tribunal_96_counterexample_env["cryptographically_authenticated_in_process"] is not False:
        raise AssertionError("Process env telemetry falsely marked authenticated")
    st_f96 = classify_f96_01_in_process_state("22222222" * 8, tribunal_96_counterexample_env)
    if st_f96 != "DETACHED_HOST_CANDIDATE":
        raise AssertionError(f"F96-01 COUNTEREXAMPLE FAILED: got {st_f96!r} instead of DETACHED_HOST_CANDIDATE")

    # 4. Author host fingerprint + forged CI env vars MUST stay `AUTHOR_HOST_REHEARSAL`
    st_author = classify_f96_01_in_process_state(
        PINNED_AUTHOR_HOST_FINGERPRINT_SHA256, tribunal_96_counterexample_env
    )
    if st_author != "AUTHOR_HOST_REHEARSAL":
        raise AssertionError(f"Author host spoof promoted to {st_author!r}")

    # 5. Distinct host fingerprint with empty env stays `DETACHED_HOST_CANDIDATE`
    st_cand = classify_f96_01_in_process_state("11111111" * 8, collect_environment_telemetry({}))
    if st_cand != "DETACHED_HOST_CANDIDATE":
        raise AssertionError(f"Expected DETACHED_HOST_CANDIDATE, got {st_cand!r}")

    # 6. Tampered Lean 4.33.1 release tarball MUST be rejected (`F95-02`)
    with tempfile.TemporaryDirectory() as td:
        fake_tar = Path(td) / "lean-4.33.1-linux.tar.zst"
        fake_tar.write_bytes(b"corrupted")
        try:
            verify_optional_lean_archive(fake_tar)
            raise AssertionError("Failed to reject corrupted Lean release archive")
        except RuntimeError:
            pass

    # 7. Unrecognized Lean archive filename MUST be rejected (`F95-02`)
    with tempfile.TemporaryDirectory() as td:
        unk_tar = Path(td) / "lean-master-unpinned.tar.zst"
        unk_tar.write_bytes(b"unpinned")
        try:
            verify_optional_lean_archive(unk_tar)
            raise AssertionError("Failed to reject unpinned Lean archive name")
        except ValueError:
            pass

    # 8. Empirical FIPS `SHA-256` 436B `0x05` witness check (`F96-03`)
    emp = verify_empirical_real_sha256_0x05_witness()
    if emp["snapshot_fips_sha256"] != "0cf299cb5bee9923ae0d547f48ec4d60abe582fb05db25c4e5a36a32392e465f":
        raise AssertionError("Empirical snapshot SHA-256 mismatch")

    return {
        "f96_guard_self_tests_passed": 8,
        "tribunal_96_ci_env_spoof_counterexample_blocked": True,
        "in_process_detached_execution_evidenced_blocked": True,
        "self_promotion_to_third_party_scoped_verified_blocked": True,
        "author_host_ci_spoof_blocked": True,
        "corrupted_and_unpinned_lean_archive_blocked": True,
        "empirical_fips_sha256_436b_witness_verified": True,
    }


# =============================================================================
# 4. Main Clean-Room Frozen `#46` Qualification Auditor
# =============================================================================

def verify_frozen46_detached(
    zip_path: Path,
    requested_max_state: str | None = None,
    verify_lean_archive_path: Path | None = None,
    require_live_lean: bool = True,
) -> dict:
    guard_report = run_f96_guard_self_tests()
    empirical_sha256_witness = verify_empirical_real_sha256_0x05_witness()
    archive_report = (
        verify_optional_lean_archive(verify_lean_archive_path)
        if verify_lean_archive_path is not None
        else None
    )

    raw = zip_path.read_bytes()
    if len(raw) != PINNED_ZIP_46_SIZE:
        raise RuntimeError(f"ZIP size mismatch: {len(raw)} != {PINNED_ZIP_46_SIZE}")
    z_sha = hashlib.sha256(raw).hexdigest()
    if z_sha != PINNED_ZIP_46_SHA256:
        raise RuntimeError(f"ZIP SHA-256 mismatch: {z_sha} != {PINNED_ZIP_46_SHA256}")

    with zipfile.ZipFile(zip_path, "r") as zf:
        if zf.testzip() is not None:
            raise RuntimeError("Corrupt ZIP member")
        infos = zf.infolist()
        if len(infos) != PINNED_ZIP_46_ENTRIES:
            raise RuntimeError(f"Entry count mismatch: {len(infos)} != {PINNED_ZIP_46_ENTRIES}")
        crc_xor = 0
        for inf in infos:
            crc_xor ^= inf.CRC & 0xFFFFFFFF
        crc_hex = f"{crc_xor:08x}"
        if crc_hex != PINNED_ZIP_46_CRC32_XOR:
            raise RuntimeError(f"CRC32 XOR mismatch: {crc_hex} != {PINNED_ZIP_46_CRC32_XOR}")

        # Phase 1: Physical & cryptographic seal check of #46 archive (#235-#237)
        with tempfile.TemporaryDirectory() as meta_td:
            mroot = Path(meta_td)
            zf.extractall(mroot)
            manifest = json.loads((mroot / "MANIFEST.json").read_text(encoding="utf-8"))
            if canonical_payload_sha256(manifest) != manifest["seal"]["payload_sha256"]:
                raise RuntimeError("MANIFEST seal invalid")
            if manifest["seal"]["payload_sha256"] != PINNED_MANIFEST_46_PAYLOAD_SHA256:
                raise RuntimeError("MANIFEST payload SHA-256 mismatch")
            if len(manifest["files"]) != 46:
                raise RuntimeError("Expected 46 registered files in MANIFEST.json")
            for entry in manifest["files"]:
                fb = (mroot / entry["path"]).read_bytes()
                if b"\r" in fb:
                    raise RuntimeError(f"CR byte in {entry['path']}")
                if len(fb) != entry["size_bytes"] or hashlib.sha256(fb).hexdigest() != entry["sha256"]:
                    raise RuntimeError(f"File hash/size mismatch: {entry['path']}")

            master = json.loads((mroot / "receipts" / "OMEGA_LAMBDA_W2_MASTER_RECEIPT.json").read_text("utf-8"))
            qual = json.loads((mroot / "receipts" / "OMEGA_LAMBDA_W2_QUALIFICATION_RECEIPT.json").read_text("utf-8"))
            if canonical_payload_sha256(master) != PINNED_MASTER_46_PAYLOAD_SHA256:
                raise RuntimeError("Master receipt payload SHA-256 mismatch")
            if canonical_payload_sha256(qual) != PINNED_QUALIFICATION_46_PAYLOAD_SHA256:
                raise RuntimeError("Qualification receipt payload SHA-256 mismatch")

        # Phase 2: Clean-room Lean-ONLY workspace (ZERO #46 receipts or Python scripts extracted)
        with tempfile.TemporaryDirectory() as clean_td:
            cws = Path(clean_td)
            for rel_lean, exp_sha in PINNED_ALL_24_LEAN_SHA256.items():
                data = zf.read(rel_lean)
                act_sha = hashlib.sha256(data).hexdigest()
                if act_sha != exp_sha:
                    raise RuntimeError(f"Pinned Lean file SHA-256 mismatch on {rel_lean}")
                dst = cws / rel_lean
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(data)

            c_thm, c_def, c_sha = audit_declarations(cws / "lean", ORDERED_24_MODULES)
            w2_thm, w2_def, w2_sha = audit_declarations(cws / "lean", ORDERED_24_MODULES[20:])
            if (c_thm, c_def, c_sha) != (486, 492, PINNED_COMBINED_DECL_SHA256):
                raise RuntimeError(f"Combined declaration table mismatch: {(c_thm, c_def, c_sha)}")
            if (w2_thm, w2_def, w2_sha) != (127, 158, PINNED_W2_NEW_DECL_SHA256):
                raise RuntimeError(f"W2 new declaration table mismatch: {(w2_thm, w2_def, w2_sha)}")

            host_fp = compute_anonymized_host_fingerprint()
            telemetry = collect_environment_telemetry(dict(os.environ))
            in_process_state = classify_f96_01_in_process_state(
                host_fp, telemetry, requested_max_state=requested_max_state
            )

            lean_bin = find_lean()
            if lean_bin is None:
                if require_live_lean:
                    raise RuntimeError("Lean 4.33.1 binary not found on PATH / LEAN_BIN")
                return seal_external_receipt({
                    "schema_version": "CAMPUS_NOESIS_F96_DETACHED_THIRD_PARTY_AUDIT_RECEIPT_V1",
                    "target_release": "RELEASE_46_OMEGA_LAMBDA_W2",
                    "target_zip_sha256": z_sha,
                    "target_zip_crc32_xor": crc_hex,
                    "w2d_composition_scope": PINNED_W2D_SCOPE,
                    "f96_01_in_process_evidence_state": "OFFLINE_STATIC_ONLY_LIVE_LEAN_NOT_EXECUTED",
                    "provenance_authentication_status": "PROVENANCE_UNVERIFIED_OFFLINE_ONLY",
                    "script_can_emit_detached_execution_evidenced": False,
                    "script_can_emit_third_party_scoped_verified": False,
                    "live_lean_reexecuted": False,
                    "f96_guard_self_tests": guard_report,
                    "empirical_fips_sha256_0x05_witness": empirical_sha256_witness,
                    "environment_telemetry": telemetry,
                })

            ver_out = subprocess.run(
                [str(lean_bin), "--version"], capture_output=True, text=True, check=True
            ).stdout.strip()
            if PINNED_LEAN_VERSION_SUBSTR not in ver_out or PINNED_LEAN_COMMIT not in ver_out:
                raise RuntimeError(f"F95-02 VIOLATION: Lean 4.33.1 commit mismatch: {ver_out}")
            lean_bin_sha256 = hashlib.sha256(lean_bin.read_bytes()).hexdigest()

            olean_dir = cws / "_olean"
            (olean_dir / "OmegaLambda").mkdir(parents=True, exist_ok=True)
            env = dict(os.environ)
            env["LEAN_PATH"] = str(olean_dir)

            olean_digests: dict[str, str] = {}
            for mod_name, rel_p in ORDERED_24_MODULES:
                out_ol = olean_dir / Path(rel_p).with_suffix(".olean")
                pr = subprocess.run(
                    [str(lean_bin), "-DwarningAsError=true", "-o", str(out_ol), f"lean/{rel_p}"],
                    cwd=str(cws),
                    env=env,
                    capture_output=True,
                    text=True,
                )
                if pr.returncode != 0 or pr.stderr.strip():
                    raise RuntimeError(f"Compile failed on {mod_name}: {pr.stdout}\n{pr.stderr}")
                olean_digests[mod_name] = hashlib.sha256(out_ol.read_bytes()).hexdigest()

            # Phase 3 (`F95-03` & `F96-03`): Compile Clean-Sheet Specification (`S_ext`)
            spec_bytes = F95_CLEAN_SHEET_SPEC_LEAN.encode("utf-8")
            spec_sha256 = hashlib.sha256(spec_bytes).hexdigest()
            spec_file = cws / "F95CleanSheetSpec.lean"
            spec_file.write_bytes(spec_bytes)
            spr = subprocess.run(
                [str(lean_bin), "-DwarningAsError=true", "F95CleanSheetSpec.lean"],
                cwd=str(cws),
                env=env,
                capture_output=True,
                text=True,
            )
            if spr.returncode != 0 or spr.stderr.strip():
                raise RuntimeError(f"F95-03 Clean-Sheet Spec check failed: {spr.stdout}\n{spr.stderr}")
            clean_sheet_axioms = parse_clean_sheet_axioms(spr.stdout)

            # Phase 4: Reproducibility SMap ConstantInfo Inspector
            insp_file = cws / "F95DetachedInspector.lean"
            insp_file.write_text(F95_DETACHED_INSPECTOR_LEAN, encoding="utf-8", newline="\n")
            ipr = subprocess.run(
                [str(lean_bin), "F95DetachedInspector.lean"],
                cwd=str(cws),
                env=env,
                capture_output=True,
                text=True,
            )
            if ipr.returncode != 0 or ipr.stderr.strip():
                raise RuntimeError(f"Detached SMap inspector failed: {ipr.stdout}\n{ipr.stderr}")

            m1_mods = {m for m, _ in ORDERED_24_MODULES[:8]}
            r1_mods = {m for m, _ in ORDERED_24_MODULES[8:12]}
            r2_mods = {m for m, _ in ORDERED_24_MODULES[12:16]}
            w1_mods = {m for m, _ in ORDERED_24_MODULES[16:20]}
            w2_mods = {m for m, _ in ORDERED_24_MODULES[20:]}
            counts = {"m1": 0, "r1": 0, "r2": 0, "w1": 0, "w2": 0}
            rows: list[str] = []

            for ln in ipr.stdout.splitlines():
                s = ln.strip()
                if not s:
                    continue
                tag, mod_s, kind_s, name_s, ax_csv = s.split("|", 4)
                if tag != "CONST_ROW":
                    raise RuntimeError(f"Unexpected inspector line: {s}")
                axs = sorted(a for a in ax_csv.split(",") if a)
                if not set(axs).issubset(ALLOWED_AXIOMS):
                    raise RuntimeError(f"Disallowed axioms on {name_s}: {axs}")
                rows.append(f"{mod_s}|{kind_s}|{name_s}|{','.join(axs)}")
                if mod_s in m1_mods:
                    counts["m1"] += 1
                elif mod_s in r1_mods:
                    counts["r1"] += 1
                elif mod_s in r2_mods:
                    counts["r2"] += 1
                elif mod_s in w1_mods:
                    counts["w1"] += 1
                elif mod_s in w2_mods:
                    counts["w2"] += 1

            ledger_sha = hashlib.sha256(("\n".join(sorted(rows)) + "\n").encode("utf-8")).hexdigest()
            if (
                counts["m1"],
                counts["r1"],
                counts["r2"],
                counts["w1"],
                counts["w2"],
                len(rows),
                ledger_sha,
            ) != (1316, 457, 441, 589, 772, 3575, PINNED_COMBINED_KERNEL_LEDGER_SHA256):
                raise RuntimeError(f"Kernel ledger mismatch: counts={counts} total={len(rows)} sha={ledger_sha}")

            return seal_external_receipt({
                "schema_version": "CAMPUS_NOESIS_F96_DETACHED_THIRD_PARTY_AUDIT_RECEIPT_V1",
                "executed_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "auditor_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "target_release": "RELEASE_46_OMEGA_LAMBDA_W2",
                "target_zip_name": PINNED_ZIP_46_NAME,
                "target_zip_size_bytes": len(raw),
                "target_zip_entries": PINNED_ZIP_46_ENTRIES,
                "target_zip_crc32_xor": crc_hex,
                "target_zip_sha256": z_sha,
                "w2d_composition_scope": PINNED_W2D_SCOPE,
                "f96_01_in_process_evidence_state": in_process_state,
                "provenance_authentication_status": "LIVE_LEAN_REEXECUTED_PROVENANCE_UNVERIFIED",
                "script_can_emit_detached_execution_evidenced": False,
                "script_can_emit_third_party_scoped_verified": False,
                "post_ci_sigstore_verifier_required_for_detached_execution_evidenced": (
                    "verify_f96_provenance_bundle.py"
                ),
                "tribunal_review_required_for_third_party_scoped_verified": True,
                "zero_shared_code_external_auditor": True,
                "clean_room_lean_only_workspace": True,
                "live_lean_reexecuted": True,
                "f95_02_toolchain_and_runtime_provenance": {
                    "lean_version": ver_out,
                    "lean_commit_enforced": PINNED_LEAN_COMMIT,
                    "lean_binary_sha256": lean_bin_sha256,
                    "verified_official_lean_archive": archive_report,
                    "host_os_platform": f"{platform.system()}-{platform.release()}-{platform.machine()}",
                    "runtime_host_fingerprint_sha256": host_fp,
                    "pinned_author_host_fingerprint_sha256": PINNED_AUTHOR_HOST_FINGERPRINT_SHA256,
                    "runtime_host_matches_author_host": (host_fp == PINNED_AUTHOR_HOST_FINGERPRINT_SHA256),
                    "environment_telemetry": telemetry,
                    "compiled_24_olean_sha256_digest": hashlib.sha256(
                        json.dumps(olean_digests, sort_keys=True).encode("utf-8")
                    ).hexdigest(),
                },
                "f96_03_clean_sheet_spec_and_proof_transport_disclosure": {
                    "clean_sheet_spec_lean_sha256": spec_sha256,
                    "clean_sheet_proposition": "F95CleanSheetAudit.AuditorIndependentSpecification",
                    "specification_definition_independence": (
                        "INDEPENDENT_AUDITOR_PROPOSITION_ZERO_W2_WRAPPER_DEFS"
                    ),
                    "kernel_proof_term": "F95CleanSheetAudit.f95_clean_sheet_specification_verified",
                    "proof_derivation_mode": "PROOF_TRANSPORTED_FROM_RELEASE_46_THEOREMS",
                    "proof_transport_dependencies_from_release_46": list(
                        F96_03_PROOF_TRANSPORT_DEPENDENCIES
                    ),
                    "independent_from_scratch_reproof_of_raw_semantics_status": "HELD",
                    "lean_positive_canary_hash_scope": (
                        "MOCK_HASH_ORACLE_NON_VACUITY_ONLY_NOT_FIPS_SHA256_PROOF"
                    ),
                    "empirical_python_fips_sha256_witness": empirical_sha256_witness,
                    "kernel_axioms_used": clean_sheet_axioms,
                },
                "reproducibility_ledger_check_distinct_from_semantic_spec": {
                    "modules_compiled_from_source": 24,
                    "combined_declarations_verified": 978,
                    "w2_new_declarations_verified": 285,
                    "layer_kernel_constant_counts": counts,
                    "combined_kernel_constants_verified": 3575,
                    "combined_kernel_ledger_sha256": ledger_sha,
                },
                "f96_guard_self_tests": guard_report,
                "five_assurance_planes_separation_f96": {
                    "plane_1_clean_sheet_spec_with_transported_lean_proof": (
                        "KERNEL_CHECKED_SPEC_INDEPENDENT_PROOF_TRANSPORTED"
                    ),
                    "plane_2_reproducibility_against_author_ledger": "MATCHED_3575_CONSTANTS",
                    "plane_3_in_process_independence_ceiling": in_process_state,
                    "plane_4_external_sha256_implementation_fidelity": (
                        "HELD_IN_LEAN__EMPIRICAL_436B_WITNESS_VERIFIED_IN_PYTHON"
                    ),
                    "plane_5_real_world_origin_truth_and_a2_a3": "HELD",
                },
            })


def main() -> None:
    parser = argparse.ArgumentParser(
        description="F96-relocked zero-shared-code Lean 4.33.1 auditor for frozen Release #46 (Ωλ-W2)."
    )
    parser.add_argument(
        "zip_path",
        nargs="?",
        type=Path,
        default=None,
        help="Path to CAMPUS_NOESIS_OMEGA_LAMBDA_W2_OUTER_PACKET_AND_SNAPSHOT_REFINEMENT_PACKAGE.zip",
    )
    parser.add_argument(
        "--self-test-f96-guards",
        "--self-test-f95-guards",
        dest="self_test_guards",
        action="store_true",
        help="Run 8 deterministic negative/counterexample self-tests of F96-01..03 guards and exit.",
    )
    parser.add_argument(
        "--force-state",
        type=str,
        default=None,
        help="Optional state ceiling (DETACHED_EXECUTION_EVIDENCED and THIRD_PARTY_SCOPED_VERIFIED raise PermissionError).",
    )
    parser.add_argument(
        "--verify-lean-archive",
        type=Path,
        default=None,
        help="Optional path to official lean-4.33.1-* release archive to SHA-256 verify (F95-02).",
    )
    parser.add_argument(
        "--allow-offline",
        action="store_true",
        help="Allow offline physical/static check when Lean 4.33.1 is absent.",
    )
    parser.add_argument(
        "--output-receipt",
        type=Path,
        default=None,
        help="Optional output path to write the sealed JSON execution receipt.",
    )
    args = parser.parse_args()
    if args.self_test_guards:
        res = run_f96_guard_self_tests()
        print(json.dumps(res, indent=2, sort_keys=True))
        return
    if args.zip_path is None:
        parser.error("zip_path is required unless --self-test-f96-guards is set")

    result = verify_frozen46_detached(
        zip_path=args.zip_path,
        requested_max_state=args.force_state,
        verify_lean_archive_path=args.verify_lean_archive,
        require_live_lean=(not args.allow_offline),
    )
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.output_receipt is not None:
        args.output_receipt.parent.mkdir(parents=True, exist_ok=True)
        args.output_receipt.write_bytes(rendered.encode("utf-8"))
    print(rendered, end="")


if __name__ == "__main__":
    main()
