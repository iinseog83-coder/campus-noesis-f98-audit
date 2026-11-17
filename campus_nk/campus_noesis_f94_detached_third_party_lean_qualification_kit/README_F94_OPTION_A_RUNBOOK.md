# CAMPUS-NOESIS — `F98` Two-Stage Detached Third-Party Lean 4.33.1 Runbook

Targets frozen Release `#46` (`CAMPUS_NOESIS_OMEGA_LAMBDA_W2_OUTER_PACKET_AND_SNAPSHOT_REFINEMENT_PACKAGE.zip`, `236,214 B`, `SHA-256 = 4c42f12b605083d13228c02c84e12b4689cdf32be0f507041b6a36360eec4608`) with zero modifications.

## Stage A — Detached Execution (`DETACHED_HOST_CANDIDATE` Ceiling, `F96-01`)

`verify_frozen46_zero_shared_third_party.py` treats all environment variables as unauthenticated and caps its maximum emitted state at `DETACHED_HOST_CANDIDATE` (`LIVE_LEAN_REEXECUTED_PROVENANCE_UNVERIFIED`).

### Option A1: GitHub Actions Cloud Runner (`ubuntu-24.04`)
Place `ci/f94_github_actions_third_party_lean46.yml` at `.github/workflows/f94_github_actions_third_party_lean46.yml`, trigger **Run workflow**, and download `f96-detached-lean46-candidate-bundle` (`F96_DETACHED_AUDIT_RECEIPT.json`, `F96_SIGSTORE_ATTESTATION_BUNDLE.jsonl`, `F96_CI_RUNTIME_PROVENANCE.txt`, `F96_ATTESTATION_METADATA.txt`).

### Option A2: Runtime-Network-Isolated Container (`F96-02` Scope)
*(Note: `docker build` uses outbound HTTPS to fetch `apt` packages and the SHA-256-pinned Lean 4.33.1 archive; `--network=none` isolates ONLY the container runtime execution phase.)*

```bash
cp ../../CAMPUS_NOESIS_OMEGA_LAMBDA_W2_OUTER_PACKET_AND_SNAPSHOT_REFINEMENT_PACKAGE.zip .
docker build -f Dockerfile.f94_cleanroom -t campus-f96-cleanroom .
mkdir -p out
docker run --rm --network=none -v "$(pwd)/out:/audit/out" campus-f96-cleanroom
```

---

## Stage B — External Sigstore Attestation & SLSA/Fulcio Binding (`F97-01` + `F98-01/02`)

`verify_f96_provenance_bundle.py` embeds the pre-pinned official `cli/cli` `v2.67.0` (`2025-02-11`) binary SHA-256 baseline (`PINNED_OFFICIAL_GH_V2_67_0_BINARIES` — e.g. `linux_amd64` archive `d77623479bec017ef8eebadfefc785bafd4658343b3eb6d3f3e26fd5e11368d5`, `bin/gh` `32ca129895be5c9843d059d0e6923325bf239efe18c415799ecde566b366af75`; `windows_amd64` archive `3a52a68a95d007d0c97f3a0a27f7302872eb31010e69312d20c59e90e0ba1e9f`, `bin/gh.exe` `edd3626605c40866f74a3056f681479f7339254f607c0276993a8e0c77dab0c2`). Never pass a self-hashed `$(sha256sum $(command -v gh))`; use the pre-pinned `v2.67.0` binary directly:

```bash
# 1. Fetch & SHA-256-verify official pre-pinned GitHub CLI v2.67.0 (linux_amd64)
curl --proto '=https' --tlsv1.2 -fsSL -O https://github.com/cli/cli/releases/download/v2.67.0/gh_2.67.0_linux_amd64.tar.gz
echo "d77623479bec017ef8eebadfefc785bafd4658343b3eb6d3f3e26fd5e11368d5  gh_2.67.0_linux_amd64.tar.gz" | sha256sum --check --strict
tar -xzf gh_2.67.0_linux_amd64.tar.gz
echo "32ca129895be5c9843d059d0e6923325bf239efe18c415799ecde566b366af75  gh_2.67.0_linux_amd64/bin/gh" | sha256sum --check --strict

# 2. Verify F96_DETACHED_AUDIT_RECEIPT.json + F96_SIGSTORE_ATTESTATION_BUNDLE.jsonl offline
python3 verify_f96_provenance_bundle.py \
  --gh-bin gh_2.67.0_linux_amd64/bin/gh \
  --receipt F96_DETACHED_AUDIT_RECEIPT.json \
  --sigstore-bundle F96_SIGSTORE_ATTESTATION_BUNDLE.jsonl \
  --custom-trusted-root F98_SIGSTORE_PUBLIC_GOOD_TRUSTED_ROOT.jsonl \
  --expected-repo <OWNER/REPO> \
  --expected-workflow-path .github/workflows/f94_github_actions_third_party_lean46.yml \
  --expected-commit-sha <40_HEX_GIT_COMMIT_SHA> \
  --expected-run-id <NUMERIC_RUN_ID> \
  --output-verdict F98_PROVENANCE_BUNDLE_VERDICT.json
```

Only when `gh 2.67.0` matches `PINNED_OFFICIAL_GH_V2_67_0_BINARIES`, cryptographic Sigstore verification succeeds, and the verified `Statement` + `Fulcio` certificate match both `.jsonl` and all expected SLSA claims does Stage B emit `DETACHED_EXECUTION_EVIDENCED`. Final promotion to `THIRD_PARTY_SCOPED_VERIFIED` remains reserved exclusively for the Tribunal.
