# Notes: Problem #142 Gap Interface Redesign Sketch (2026-03-05)

## Why Redesign Is Needed

The feasibility audit shows current gap interfaces are over-strong:

- `k = 3`: upper side plausible, but full matched two-sided witness is not currently justified
- `k = 4`: only upper-profile support is represented
- `k >= 5`: only upper-profile support is represented

Therefore current `MainTheoreticalGap` should be split into honesty-preserving components before
attempting theorem-backed instance work.

## Redesign Goals

1. separate "best-known upper consequences" from "full asymptotic formula"
2. avoid forcing a matched two-sided profile in branches where literature layer does not support it
3. keep full-solution path explicit and auditable as conjectural/imported when needed

## Proposed Interface Split

### Branch-local upper witnesses

- `K3UpperProfileWitnessImported`
  - fields: `β c C`, positivity assumptions, and upper `isBigO` profile
- `K4UpperProfileWitnessImported`
  - fields: `c C`, positivity assumptions, and upper `isBigO` profile
- `Kge5UpperProfileWitnessImported`
  - family fields for each `k >= 5` with upper `isBigO` profile

### Branch-local lower witnesses (optional/independent)

- `K3LowerProfileWitnessImported` (can target Behrend-shape lower profile first)
- `K4LowerProfileWitnessImported` (currently expected absent)
- `Kge5LowerProfileWitnessImported` (currently expected absent)

### Keep strong matched witnesses separate

- retain current two-sided matched-profile classes as a stronger layer
- rename/package them as "strong/full-profile assumptions" to avoid confusion with best-known layer

## Theorem Path Split

1. **Upper-only best-known theorem path** (new)
   - prove `erdos_142.variants.upper 3`, `erdos_142.variants.upper 4`,
     and `forall k >= 5, erdos_142.variants.upper k` from upper witness classes
   - aggregate into a theorem equivalent to:
     - `upper_variant_of_literature_for_all_k_ge_three`
   - this should be theorem-backed/import-backed without requiring lower witnesses

2. **Full asymptotic-formula path** (existing strong path)
   - keep requiring two-sided matched witnesses
   - explicitly mark as stronger-than-best-known dependency surface

## Minimal Migration Order

1. add new upper witness classes and conversion lemmas from existing `bound_targets` assumptions
2. add upper-only aggregate theorem for all `k >= 3`
3. refactor `Problem142Gap.lean` into:
   - `MainUpperGap` (best-known achievable target)
   - `MainFullGap` (two-sided full-asymptotic target)
4. keep backward-compatible theorem names via wrappers where useful

## Risk Notes

- Avoid deleting current strong classes immediately; add compatibility layer first.
- Keep checker policy unchanged until new theorems are integrated and named targets are stable.

## Implementation Status Update (2026-03-05)

Completed in code:

- Upper-side split implemented (`MainUpperGap`, branch-local upper witness interfaces).
- Lower-side split implemented (`MainLowerGap`, branch-local lower witness interfaces).
- `k = 3` lower route wired from `LiteratureRateAssumptions` into
  `K3BehrendLowerProfileWitnessImported`.

Frontier decision now encoded:

- Keep `k = 4` / `k >= 5` lower interfaces as intentionally uninstantiated placeholders in the
  current literature layer.
- Do not introduce artificial placeholder assumptions in `LiteratureRateAssumptions` yet.
- Treat these as explicit open-lower debt surfaces for future imports/proofs.
