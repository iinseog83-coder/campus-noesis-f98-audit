/-
  CAMPUS_OMEGA_LAMBDA_E1_T104_XH0_EXTERNAL_DETACHED_QUALIFICATION
  File: `xh0_independent_semantic_probe.lean`

  Purpose (`XH0-B` & `XH0-T` Cross-Term Axis — Zero-Shared-Algorithmic-Assumptions):
    Even if two hosts execute the same certificate checker (`checkSourceLocalCert0x01`, `binomDP`,
    `kSubsets`), they could share an algorithmic modeling assumption. This probe mentions NONE of
    `checkSourceLocalCert0x01`, `ExtractedLocalE1Evidence`, `kSubsets`, or `binomDP` in its target
    statements: instead, it directly unpacks `e1_ex_k3_exact_resilience_2_proven` into raw
    carrier-survival quantifiers over string-keyed retractable record deletions `D_str`:
      1. Every duplicate-free retractable deletion `D_str` with `|D_str| < 2` (`0` or `1` records)
         CANNOT break `pktK3` (`SourceCarrierSurvivesStr` still holds).
      2. Some duplicate-free retractable deletion `D_str_star` with `|D_str_star| ≤ 2` DOES break
         `pktK3` (`¬ SourceCarrierSurvivesStr`).
-/

import OmegaLambdaE1Core

namespace XH0SemanticGroundTruthProbe

open OmegaLambda
open OmegaLambda.E1Examples

theorem xh0_k3_every_sub2_retraction_leaves_carrier_surviving :
    ∀ (D_str : List AsciiId),
      NodupList D_str →
      (∀ rid ∈ D_str, rid ∈ sourceRemRecordIds snapK3 entK3.pinnedConstIds) →
      D_str.length < 2 →
      SourceCarrierSurvivesStr snapK3 .ePlus 0 4 (.localPacket pktK3) D_str := by
  intro D_str hnd hrem hlt2
  have hExact := e1_ex_k3_exact_resilience_2_proven.2.2.2
  rcases hExact with ⟨ent, hlk, _, _, _, _, _, ⟨_, hLow2, _⟩⟩
  have hentEq : ent = entK3 := by
    have h0 : lookupPinnedA1 snapK3.snapshotId regK3 = some entK3 := rfl
    rw [h0] at hlk
    injection hlk with heq
    exact heq.symm
  subst hentEq
  apply Classical.byContradiction
  intro hNotSurv
  have hGe2 : 2 ≤ D_str.length := hLow2 D_str hnd hrem hNotSurv
  omega

theorem xh0_k3_exists_at_most_2_retraction_breaking_carrier :
    ∃ (D_str_star : List AsciiId),
      NodupList D_str_star ∧
      (∀ rid ∈ D_str_star, rid ∈ sourceRemRecordIds snapK3 entK3.pinnedConstIds) ∧
      D_str_star.length ≤ 2 ∧
      ¬ SourceCarrierSurvivesStr snapK3 .ePlus 0 4 (.localPacket pktK3) D_str_star := by
  have hExact := e1_ex_k3_exact_resilience_2_proven.2.2.2
  rcases hExact with ⟨ent, hlk, _, _, _, _, _, ⟨_, _, hUp2⟩⟩
  have hentEq : ent = entK3 := by
    have h0 : lookupPinnedA1 snapK3.snapshotId regK3 = some entK3 := rfl
    rw [h0] at hlk
    injection hlk with heq
    exact heq.symm
  subst hentEq
  exact hUp2

end XH0SemanticGroundTruthProbe
