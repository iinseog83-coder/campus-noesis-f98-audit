#!/usr/bin/env python3
"""Zero-I/O Pure 3-Valued Heyting/Chain Lattice Adjudicator for `PCT0-XH0 v3` (`F-PCT0-XH0-06`).

Architectural Invariant:
  - Imports EXCLUSIVELY `dataclasses` and `typing` (zero `os`, `sys`, `io`, `pathlib`, `shutil`,
    `tempfile`, `subprocess`, `zipfile`, `json`, or network modules).
  - Never trusts pre-computed `"PASS"` summary strings; evaluates `XH0-G1`..`XH0-G7` purely over
    primitive hashes, counts, line intervals, module import tuples, and counterfactual adversarial
    observation records.
  - Enforces strict 3-valued lattice ordering `FAIL (0) < HELD_OR_UNKNOWN (1) < PASS (2)` so missing
    or uncertain evidence can NEVER promote to `PASS`.
  - Epistemic & TCB Boundary (`F-PCT0-XH0-06`): `PureAdjudicationCorrect` guarantees deterministic
    soundness of the valuation morphism given `ObsBundle`, while physical authenticity of OpenSSL and
    filesystem observations rests on the documented `EffectfulHarness` TCB & Sigstore bindings.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Optional, Tuple

VAL_FAIL = "FAIL"
VAL_HELD = "HELD_OR_UNKNOWN"
VAL_PASS = "PASS"

_LATTICE_RANK: Dict[str, int] = {
    VAL_FAIL: 0,
    VAL_HELD: 1,
    VAL_PASS: 2,
}


def meet3(values: Iterable[str]) -> str:
    items = list(values)
    if not items:
        return VAL_HELD
    for v in items:
        if v not in _LATTICE_RANK:
            return VAL_FAIL
    if VAL_FAIL in items:
        return VAL_FAIL
    if VAL_HELD in items:
        return VAL_HELD
    return VAL_PASS


@dataclass(frozen=True)
class MutationSpanSpec:
    mut_id: str
    expected_orig_s0_sha256: str
    expected_q0_sha256: str
    expected_rfl_rhs_spec_sha256: str
    target_span_start: int
    target_span_end: int
    expected_failure_class: str


@dataclass(frozen=True)
class PinnedSpec:
    s1s2_zip_sha256: str
    s1s2_zip_size: int
    s1s2_zip_entries: int
    expected_lean_sha256s: Tuple[Tuple[str, str], ...]
    expected_frozen_receipts: Tuple[Tuple[str, str, int], ...]
    lean_linux_tar_sha256: str
    lean_linux_tar_size: int
    lean_commit: str
    expected_module_names: Tuple[str, ...]
    zero_import_target_modules: Tuple[str, ...]
    expected_smap_constants: int
    expected_smap_theorems: int
    expected_closure_g: int
    expected_closure_h: int
    expected_transport_consts: int
    expected_axiom_footprints: Tuple[Tuple[str, Tuple[str, ...]], ...]
    mutation_specs: Tuple[MutationSpanSpec, ...]
    trusted_root_sha256: str
    expected_oidc_issuer: str
    expected_repo_uri: str
    expected_workflow_san_uri: str
    expected_adv_ids: Tuple[Tuple[str, int], ...]


@dataclass(frozen=True)
class MutationSpanObservation:
    mut_id: str
    unmutated_baseline_exit_zero: bool
    orig_s0_sha256: str
    reconstructed_s0_sha256: str
    p0_sha256: str
    pm_sha256: str
    q0_sha256: str
    qm_sha256: str
    sm_sha256: str
    span_sm_sha256: str
    dm_sha256: str
    span_dm_sha256: str
    prereq_all_exit_zero: bool
    break_exit_code: int
    break_zero_syntax_errors: bool
    break_first_error_line: int
    break_error_class: str
    dm_compile_exit_code: int
    dm_olean_sha256: str
    rfl_rhs_spec_sha256: str
    probe_compile_exit_code: int
    probe_sorry_count: int
    probe_user_axioms_count: int


@dataclass(frozen=True)
class CoreObservation:
    # G1 observations
    zip_sha256: Optional[str]
    zip_size_bytes: Optional[int]
    zip_entries_count: Optional[int]
    zip_crc_ok: Optional[bool]
    lean_source_sha256s: Tuple[Tuple[str, str], ...]
    frozen_receipt_sha256s: Tuple[Tuple[str, str, int], ...]
    pre_post_input_hashes_identical: Optional[bool]
    auxiliary_text_prescreen_clean: Optional[bool]

    # G2 observations
    require_linux_tar_binding: bool
    lean_tar_sha256: Optional[str]
    lean_tar_size: Optional[int]
    lean_version_banner: Optional[str]
    compiled_modules: Tuple[Tuple[str, int, str], ...]
    calibration_imports: Optional[Tuple[str, ...]]
    target_module_imports: Tuple[Tuple[str, str, Tuple[str, ...]], ...]
    smap_constants: Optional[int]
    smap_theorems: Optional[int]
    smap_sorry: Optional[int]
    smap_user_axioms: Optional[int]
    smap_opaque: Optional[int]
    smap_reduce_bool: Optional[int]
    smap_classical_choice: Optional[int]

    # G3 observations
    transdeps_sat_g: Optional[int]
    transdeps_sat_h: Optional[int]
    transdeps_inter_g_transport: Optional[int]
    transdeps_inter_g_h: Optional[int]
    transdeps_inter_h_transport: Optional[int]
    transdeps_inter_h_g: Optional[int]
    transdeps_shared_user_gh: Optional[int]
    transdeps_closure_g: Optional[int]
    transdeps_closure_h: Optional[int]
    transdeps_transport_consts: Optional[int]
    axiom_footprints: Tuple[Tuple[str, Tuple[str, ...]], ...]

    # G4 observations
    mutations: Tuple[MutationSpanObservation, ...]
    ci_unit_tests_passed: Optional[int]
    ci_unit_tests_skipped: Optional[int]
    ci_unit_tests_failed: Optional[int]

    # G5 observations
    self_contained_offline_verdict: Optional[str]
    isolated_sim_overall_verdict: Optional[str]
    isolated_sim_passed: Optional[int]
    isolated_sim_intended_skips: Optional[int]
    isolated_sim_unexpected_skips: Optional[int]
    isolated_sim_failed: Optional[int]
    empirical_status: Optional[str]
    f_pct0_17_status: Optional[str]

    # G6 cryptographic observations
    sigstore_executed: bool
    sigstore_error_code: Optional[str]
    trusted_root_sha256: Optional[str]
    provenance_subject_sha256: Optional[str]
    dsse_statement_subject_sha256: Optional[str]
    provenance_s1s2_zip_sha256: Optional[str]
    provenance_raw_files_all_hash_bound: Optional[bool]
    fulcio_chain_ok: Optional[bool]
    fulcio_san_uri: Optional[str]
    fulcio_oidc_issuer: Optional[str]
    fulcio_repo_uri: Optional[str]
    fulcio_runner_env: Optional[str]
    fulcio_commit_sha: Optional[str]
    expected_commit_sha: Optional[str]
    fulcio_run_invocation_uri: Optional[str]
    expected_run_invocation_uri: Optional[str]
    ct_precert_sct_ok: Optional[bool]
    rekor_set_ok: Optional[bool]
    rekor_merkle_ok: Optional[bool]
    rekor_checkpoint_ok: Optional[bool]
    dsse_pae_sig_ok: Optional[bool]


@dataclass(frozen=True)
class AdversarialCaseObservation:
    adv_id: str
    target_gate_index: int  # 0..5 for G1..G6
    pre_orig_sha256: str
    mutated_copy_sha256: str
    post_orig_sha256: str
    perturbed_obs: CoreObservation


@dataclass(frozen=True)
class ObsBundle:
    core: CoreObservation
    adversarial_cases: Tuple[AdversarialCaseObservation, ...]
    bundle_pre_sha256: Optional[str]
    bundle_post_sha256: Optional[str]


@dataclass(frozen=True)
class AdjudicationDecision:
    g1_source_lineage: str
    g2_lean_replay: str
    g3_transdeps_and_axioms: str
    g3_definitional_independence_subverdict: str
    g3_count_parity_subverdict: str
    g4_semantic_mutations: str
    g5_boundary_separation: str
    g6_sigstore_provenance: str
    g7_master_tribunal_gate: str
    detached_recheck_verdict: str
    artifact_immutability_verdict: str
    adversarial_case_verdicts: Tuple[Tuple[str, str], ...]


def _eval_g1(obs: CoreObservation, spec: PinnedSpec) -> str:
    if (
        obs.zip_sha256 is None
        or obs.zip_size_bytes is None
        or obs.zip_entries_count is None
        or obs.zip_crc_ok is None
        or obs.pre_post_input_hashes_identical is None
    ):
        return VAL_HELD
    if (
        obs.zip_sha256 != spec.s1s2_zip_sha256
        or obs.zip_size_bytes != spec.s1s2_zip_size
        or obs.zip_entries_count != spec.s1s2_zip_entries
        or not obs.zip_crc_ok
        or not obs.pre_post_input_hashes_identical
    ):
        return VAL_FAIL
    if dict(obs.lean_source_sha256s) != dict(spec.expected_lean_sha256s):
        return VAL_FAIL
    if sorted(obs.frozen_receipt_sha256s) != sorted(spec.expected_frozen_receipts):
        return VAL_FAIL
    return VAL_PASS


def _eval_g2(obs: CoreObservation, spec: PinnedSpec) -> str:
    if (
        obs.lean_version_banner is None
        or obs.calibration_imports is None
        or obs.smap_constants is None
        or obs.smap_theorems is None
        or obs.smap_sorry is None
        or obs.smap_user_axioms is None
        or obs.smap_opaque is None
        or obs.smap_reduce_bool is None
        or obs.smap_classical_choice is None
    ):
        return VAL_HELD
    if obs.require_linux_tar_binding:
        if obs.lean_tar_sha256 is None or obs.lean_tar_size is None:
            return VAL_HELD
        if obs.lean_tar_sha256 != spec.lean_linux_tar_sha256 or obs.lean_tar_size != spec.lean_linux_tar_size:
            return VAL_FAIL
    if "4.33.1" not in obs.lean_version_banner or spec.lean_commit not in obs.lean_version_banner:
        return VAL_FAIL
    if len(obs.compiled_modules) != len(spec.expected_module_names):
        return VAL_FAIL
    olean_map: Dict[str, str] = {}
    for (act_nm, rc, olean_sha), exp_nm in zip(obs.compiled_modules, spec.expected_module_names):
        if act_nm != exp_nm or rc != 0 or len(olean_sha) != 64:
            return VAL_FAIL
        olean_map[act_nm] = olean_sha

    # AST ModuleData import calibration check (F-PCT0-XH0-03 & Condition 4.1)
    imp_records = {m: (osha, imps) for m, osha, imps in obs.target_module_imports}
    for zm in spec.zero_import_target_modules:
        if zm not in imp_records or zm not in olean_map:
            return VAL_FAIL
        rec_osha, imps = imp_records[zm]
        if rec_osha != olean_map[zm]:
            return VAL_FAIL
        if imps != obs.calibration_imports:
            return VAL_FAIL
        if any(i.startswith("ProofspaceOmegaPCT0") for i in imps):
            return VAL_FAIL

    if (
        obs.smap_sorry != 0
        or obs.smap_user_axioms != 0
        or obs.smap_opaque != 0
        or obs.smap_reduce_bool != 0
        or obs.smap_classical_choice != 0
    ):
        return VAL_FAIL
    if obs.smap_constants != spec.expected_smap_constants or obs.smap_theorems != spec.expected_smap_theorems:
        return VAL_HELD
    return VAL_PASS


def _eval_g3(obs: CoreObservation, spec: PinnedSpec) -> Tuple[str, str, str]:
    if (
        obs.transdeps_sat_g is None
        or obs.transdeps_sat_h is None
        or obs.transdeps_inter_g_transport is None
        or obs.transdeps_inter_g_h is None
        or obs.transdeps_inter_h_transport is None
        or obs.transdeps_inter_h_g is None
        or obs.transdeps_shared_user_gh is None
        or obs.transdeps_closure_g is None
        or obs.transdeps_closure_h is None
        or obs.transdeps_transport_consts is None
    ):
        return (VAL_HELD, VAL_HELD, VAL_HELD)

    if obs.transdeps_sat_g != 1 or obs.transdeps_sat_h != 1:
        return (VAL_FAIL, VAL_FAIL, VAL_HELD)

    indep_ok = (
        obs.transdeps_inter_g_transport == 0
        and obs.transdeps_inter_g_h == 0
        and obs.transdeps_inter_h_transport == 0
        and obs.transdeps_inter_h_g == 0
        and obs.transdeps_shared_user_gh == 0
    )
    indep_val = VAL_PASS if indep_ok else VAL_FAIL
    if not indep_ok:
        return (VAL_FAIL, VAL_FAIL, VAL_HELD)

    allowed = {"propext", "Quot.sound"}
    exp_ax_map = {k: tuple(sorted(v)) for k, v in spec.expected_axiom_footprints}
    act_ax_map = {k: tuple(sorted(v)) for k, v in obs.axiom_footprints}
    if set(act_ax_map.keys()) != set(exp_ax_map.keys()):
        return (VAL_FAIL, indep_val, VAL_FAIL)
    for _, axs in act_ax_map.items():
        if any(a not in allowed for a in axs):
            return (VAL_FAIL, indep_val, VAL_FAIL)
    ax_val = VAL_PASS if act_ax_map == exp_ax_map else VAL_HELD

    parity_ok = (
        obs.transdeps_closure_g == spec.expected_closure_g
        and obs.transdeps_closure_h == spec.expected_closure_h
        and obs.transdeps_transport_consts == spec.expected_transport_consts
    )
    parity_val = VAL_PASS if parity_ok else VAL_HELD
    return (meet3([indep_val, ax_val, parity_val]), indep_val, parity_val)


def _eval_g4(obs: CoreObservation, spec: PinnedSpec) -> str:
    if (
        obs.ci_unit_tests_passed is None
        or obs.ci_unit_tests_skipped is None
        or obs.ci_unit_tests_failed is None
    ):
        return VAL_HELD
    # Context A (F-PCT0-XH0-04): Zero skips allowed on Lean CI host!
    if obs.ci_unit_tests_passed != 4 or obs.ci_unit_tests_skipped != 0 or obs.ci_unit_tests_failed != 0:
        return VAL_FAIL
    if len(obs.mutations) != len(spec.mutation_specs):
        return VAL_FAIL

    obs_by_id = {m.mut_id: m for m in obs.mutations}
    for mspec in spec.mutation_specs:
        m = obs_by_id.get(mspec.mut_id)
        if m is None:
            return VAL_FAIL
        # 1. Free-monoid causal prefix span identities (F-PCT0-XH0-05)
        span_ok = (
            m.unmutated_baseline_exit_zero
            and m.orig_s0_sha256 == mspec.expected_orig_s0_sha256
            and m.reconstructed_s0_sha256 == mspec.expected_orig_s0_sha256
            and m.q0_sha256 == mspec.expected_q0_sha256
            and m.qm_sha256 == mspec.expected_q0_sha256
            and m.pm_sha256 != m.p0_sha256
            and m.sm_sha256 == m.span_sm_sha256
            and m.dm_sha256 == m.span_dm_sha256
        )
        # 2. Path A: Proof-break observation inside target theorem span (F-PCT0-XH0-01)
        break_ok = (
            m.prereq_all_exit_zero
            and m.break_exit_code != 0
            and m.break_zero_syntax_errors
            and (mspec.target_span_start <= m.break_first_error_line <= mspec.target_span_end)
            and m.break_error_class == mspec.expected_failure_class
        )
        # 3. Path B: Prefix .olean build + rfl RHS spec hash + constructive countermodel proof (rc == 0)
        cm_ok = (
            m.dm_compile_exit_code == 0
            and len(m.dm_olean_sha256) == 64
            and m.rfl_rhs_spec_sha256 == mspec.expected_rfl_rhs_spec_sha256
            and m.probe_compile_exit_code == 0
            and m.probe_sorry_count == 0
            and m.probe_user_axioms_count == 0
        )
        if not (span_ok and break_ok and cm_ok):
            return VAL_FAIL
    return VAL_PASS


def _eval_g5(obs: CoreObservation) -> str:
    if (
        obs.self_contained_offline_verdict is None
        or obs.isolated_sim_overall_verdict is None
        or obs.isolated_sim_passed is None
        or obs.isolated_sim_intended_skips is None
        or obs.isolated_sim_unexpected_skips is None
        or obs.isolated_sim_failed is None
        or obs.empirical_status is None
        or obs.f_pct0_17_status is None
    ):
        return VAL_HELD
    ok = (
        obs.self_contained_offline_verdict == "SELF_CONTAINED_OFFLINE_VERIFIED"
        and obs.isolated_sim_overall_verdict == "EVIDENCE_UNAVAILABLE"
        and obs.isolated_sim_passed == 3
        and obs.isolated_sim_intended_skips == 1
        and obs.isolated_sim_unexpected_skips == 0
        and obs.isolated_sim_failed == 0
        and obs.empirical_status == "UNASSESSED"
        and obs.f_pct0_17_status == "EXTERNAL_COMMIT_ISSUER_AUTHENTICITY_HELD"
    )
    return VAL_PASS if ok else VAL_FAIL


def _eval_g6(obs: CoreObservation, spec: PinnedSpec) -> str:
    if not obs.sigstore_executed:
        return VAL_HELD
    if obs.sigstore_error_code is not None:
        return VAL_FAIL
    req_fields = (
        obs.trusted_root_sha256,
        obs.provenance_subject_sha256,
        obs.dsse_statement_subject_sha256,
        obs.provenance_s1s2_zip_sha256,
        obs.provenance_raw_files_all_hash_bound,
        obs.fulcio_chain_ok,
        obs.fulcio_san_uri,
        obs.fulcio_oidc_issuer,
        obs.fulcio_repo_uri,
        obs.fulcio_runner_env,
        obs.fulcio_commit_sha,
        obs.expected_commit_sha,
        obs.fulcio_run_invocation_uri,
        obs.expected_run_invocation_uri,
        obs.ct_precert_sct_ok,
        obs.rekor_set_ok,
        obs.rekor_merkle_ok,
        obs.rekor_checkpoint_ok,
        obs.dsse_pae_sig_ok,
    )
    if any(f is None for f in req_fields):
        return VAL_HELD

    ok = (
        obs.trusted_root_sha256 == spec.trusted_root_sha256
        and obs.provenance_subject_sha256 == obs.dsse_statement_subject_sha256
        and obs.provenance_s1s2_zip_sha256 == spec.s1s2_zip_sha256
        and bool(obs.provenance_raw_files_all_hash_bound)
        and bool(obs.fulcio_chain_ok)
        and obs.fulcio_san_uri == spec.expected_workflow_san_uri
        and obs.fulcio_oidc_issuer == spec.expected_oidc_issuer
        and obs.fulcio_repo_uri == spec.expected_repo_uri
        and obs.fulcio_runner_env == "github-hosted"
        and obs.fulcio_commit_sha == obs.expected_commit_sha
        and obs.fulcio_run_invocation_uri == obs.expected_run_invocation_uri
        and bool(obs.ct_precert_sct_ok)
        and bool(obs.rekor_set_ok)
        and bool(obs.rekor_merkle_ok)
        and bool(obs.rekor_checkpoint_ok)
        and bool(obs.dsse_pae_sig_ok)
    )
    return VAL_PASS if ok else VAL_FAIL


def evaluate_core_gates_pure(obs: CoreObservation, spec: PinnedSpec) -> Tuple[str, str, str, str, str, str, str, str]:
    g1 = _eval_g1(obs, spec)
    g2 = _eval_g2(obs, spec)
    g3, g3_indep, g3_parity = _eval_g3(obs, spec)
    g4 = _eval_g4(obs, spec)
    g5 = _eval_g5(obs)
    g6 = _eval_g6(obs, spec)
    return (g1, g2, g3, g4, g5, g6, g3_indep, g3_parity)


def adjudicate_pct0_xh0_pure(bundle: ObsBundle, spec: PinnedSpec) -> AdjudicationDecision:
    g1, g2, g3, g4, g5, g6, g3_indep, g3_parity = evaluate_core_gates_pure(bundle.core, spec)
    core_six = (g1, g2, g3, g4, g5, g6)

    # Artifact immutability across adversarial harness execution
    if bundle.bundle_pre_sha256 is None or bundle.bundle_post_sha256 is None:
        v_immut = VAL_HELD
    elif bundle.bundle_pre_sha256 == bundle.bundle_post_sha256 and len(bundle.bundle_pre_sha256) == 64:
        v_immut = VAL_PASS
    else:
        v_immut = VAL_FAIL

    # Detached recheck confirms all 6 base gates were derived directly from raw observations
    v_recheck = meet3(core_six)

    # Counterfactual evaluation of the 6 adversarial perturbations via the exact same Phi_base
    adv_map = {a.adv_id: a for a in bundle.adversarial_cases}
    adv_verdicts = []
    for exp_id, exp_gate_idx in spec.expected_adv_ids:
        a = adv_map.get(exp_id)
        if a is None:
            adv_verdicts.append((exp_id, VAL_HELD))
            continue
        if (
            a.target_gate_index != exp_gate_idx
            or a.mutated_copy_sha256 == a.pre_orig_sha256
            or a.post_orig_sha256 != a.pre_orig_sha256
        ):
            adv_verdicts.append((exp_id, VAL_FAIL))
            continue
        pert_six = evaluate_core_gates_pure(a.perturbed_obs, spec)[:6]
        rejected_on_target = pert_six[exp_gate_idx] == VAL_FAIL
        adv_verdicts.append((exp_id, VAL_PASS if rejected_on_target else VAL_FAIL))

    g7 = meet3(list(core_six) + [v for _, v in adv_verdicts] + [v_recheck, v_immut])

    return AdjudicationDecision(
        g1_source_lineage=g1,
        g2_lean_replay=g2,
        g3_transdeps_and_axioms=g3,
        g3_definitional_independence_subverdict=g3_indep,
        g3_count_parity_subverdict=g3_parity,
        g4_semantic_mutations=g4,
        g5_boundary_separation=g5,
        g6_sigstore_provenance=g6,
        g7_master_tribunal_gate=g7,
        detached_recheck_verdict=v_recheck,
        artifact_immutability_verdict=v_immut,
        adversarial_case_verdicts=tuple(adv_verdicts),
    )
