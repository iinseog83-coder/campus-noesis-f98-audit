# CAMPUS-NATIVE PROOFSPACE Ω — `PCT0-XH0` Detached Multi-Host Qualification (`v3`)

## Architecture (`PCT0-XH0 v3` Static Plan Implementation)

1. **Frozen Subject (`0 B` Modified):**
   - `readonly_s1s2_input/CAMPUS_PROOFSPACE_OMEGA_PCT0_S1S2_MINIMAL_FORMALIZATION_BUNDLE.zip` (`45,265 B`, `SHA-256 = 0700fd1cf3225b1b791d5d3dc35cc05ef925acf1ebc443bab8b73d5a4884025e`, `15` entries).
2. **Detached Linux CI Raw Runner (`src/pct0_xh0_linux_runner.py`):**
   - Runs on GitHub Actions `ubuntu-24.04` against official `lean-4.33.1-linux.tar.zst` (`570,405,234 B`, `SHA-256 = 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`).
   - Emits ONLY raw `G1`..`G5` JSON artifacts, `LINUX_LEAN_RAW_TRANSCRIPT.log`, and `PCT0_XH0_SIGNED_PROVENANCE.json` (never emitting `G6` or `G7`).
   - Implements Causal Prefix Span decomposition (`S_m = P_m || Q_0 || E_ns`, `D_m = P_m || E_ns`) so every pre-locked mutation `M_PCT0_LEAN_01`..`05` yields both a `Proof-Break` failure inside the target theorem line span and a compiled `D_m.olean` + kernel-verified `rfl` definition-equality and constructive `Countermodel` refutation proof (`exit_code == 0`, `sorry == 0`, `userAxioms == 0`).
3. **Orthogonal Effectful Harness & Zero-I/O Pure Adjudicator (`F-PCT0-XH0-06`):**
   - `src/effectful_harness.py` (`H_IO`): Performs OpenSSL Sigstore (Fulcio X.509 chain, SAN URI, OIDC commit/run extensions, CT PreCert SCT, Rekor SET + RFC 6962 Merkle + Checkpoint STH, DSSE PAE) observations and executes the 6 adversarial perturbations (`MXH0_PCT0_01`..`06`) inside isolated temporary copies.
   - `src/pure_adjudicator.py` (`A_pure`): Imports exclusively `dataclasses` and `typing`, evaluating `XH0-G1`..`XH0-G7` over the 3-valued chain lattice `FAIL < HELD_OR_UNKNOWN < PASS`.

## Preserved Epistemic & Authority Boundaries

- `T105`, `P0 v1~XH0`, `PCT-S1/S2`: **`FROZEN` (`0 B` modified)**.
- `F-PCT0-17` (`EXTERNAL_COMMIT_ISSUER_AUTHENTICITY_HELD`), concurrent commit atomicity, Harness/OpenSSL TCB boundary, `EmpiricalStatus = UNASSESSED`, `F-XH0-01`, `F-R2-01~03`, `PCT-S3/S4`: **`HELD` / `UNASSESSED`**.
- `P1`, `E1-D`, `Release #47`: **`NOT_AUTHORIZED`**.
