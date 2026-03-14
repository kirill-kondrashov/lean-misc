# Research program: false frontier `OddHalfCubeMinimalOutsideLower`

Date: 2026-03-13

## Status

`OddHalfCubeMinimalOutsideLowerStatement` is false.

The Lean witness is
`oddHalfCubeMinimalOutsideCounterexample : Finset (Finset (Fin 3))`
defined by

`(Finset.univ.erase 0).powerset`.

This is a down-set in `2^[3]` with

- `|D| = 4 = 2^(2*1)`, so it has half-cube mass
- `minimalOutside D = {{0}}`
- therefore `#minimalOutside D = 1 < choose(3,1) = 3`

The formal negation theorem is
`not_OddHalfCubeMinimalOutsideLowerStatement`.

Because
`oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower`
was already proved, the antichain reformulation is false as well:

`not_OddAntichainUpperClosureLowerStatement`.

## Why this matters

This kills the clean universal fallback:

- `OddHalfCubeMinimalOutsideLowerStatement`
- `OddAntichainUpperClosureLowerStatement`

So the remaining odd balanced proof cannot be finished by lower-bounding
`minimalOutside` alone for arbitrary odd half-cube down-sets.

The obstruction is structural, not accidental: a codimension-1 subcube already has half-cube mass,
but its minimal excluded antichain can have size `1`.

## What remains usable

The following Lean reductions are still mathematically correct, but they are now archival or
conditional infrastructure rather than live targets:

- `oddAntichainUpperClosureLower_iff_oddHalfCubeMinimalOutsideLower`
- `oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower`
- `oddHalfCubeBoundaryLower_of_minimalOutsideLower`

They remain useful only if a stronger true hypothesis is later found that implies the same
universal `minimalOutside` bound.

## Replacement program

### Route A: direct odd balanced proof

Return to the actual theorem surface:

- `OddHalfCubeUpperShadowGapLowerStatement`

Live tasks:

1. Strengthen the current slice / upper-shadow-gap inequalities so they close without any appeal to
   universal `minimalOutside` bounds.
2. Identify a structural forcing lemma on half-cube down-sets that is not secretly an equality-case
   theorem in disguise.
3. Keep the current exact-shadow closure lemmas as the downstream target once the forcing lemma is
   found.

### Route B: minimizer-only salvage

The counterexample does not refute minimizer-only statements.

Live targets:

- `OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement`
- `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement`
- `OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement`

These are still plausible because the dimension-3 counterexample is not a boundary minimizer.

Live tasks:

1. Compare the codimension-1-subcube counterexample with actual odd half-cube boundary minimizers.
2. Search for a proof that global boundary minimizers force larger `minimalOutside` or vanishing
   lower boundary slices.
3. Use the already-built Lean bridges from those minimizer-only statements back to
   `OddHalfCubeUpperShadowGapLowerStatement`.
4. Treat the corrected antichain surface as the antichain-form version of Route B, not as a
   replacement for the dead universal antichain theorem.

### Route C: corrected antichain theorem

The antichain theorem failed because the hypothesis was too weak, not because the whole idea is
useless.

Possible corrected forms to test:

1. Add a genuine minimizer hypothesis.
2. Add a boundary-minimality or shadow-minimality hypothesis.
3. Restrict to compressed / symmetric antichains.
4. Replace raw cardinality of `minimalOutside` with a weighted or rank-sensitive lower bound.

Any corrected version must survive the codimension-1-subcube counterexample first.

## Immediate next actions

1. Keep the false theorem surfaces in Lean, but mark them archival and reference the negation
   theorems.
2. Update the low-dimensional search tool so it can emit a red warning for the universal
   `minimalOutside` frontier.
3. Resume Phase 1 on Route A or Route B only.

## Exit criterion

This note is complete when the main proof program no longer treats
`OddHalfCubeMinimalOutsideLowerStatement` as a live theorem target.
