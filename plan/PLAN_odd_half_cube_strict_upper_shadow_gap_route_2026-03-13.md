# Research program: strict upper-shadow-gap route for the odd balanced case

Date: 2026-03-13

## Goal

Prove
`OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement`.

This is the explicit direct subtarget on the live Phase 1 route:

- if `𝒟` is a genuine odd half-cube global boundary minimizer
- and some lower positive-boundary slice `((positiveBoundary 𝒟) # r)` with `1 ≤ r ≤ m` is nonzero

then

- `choose(2m+1,m) < upperShadowGap 𝒟`.

Lean already proves that this statement closes the odd balanced theorem.

## Status update (2026-03-14)

Step 1 and Step 2 are now implemented in Lean:

- `odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto`
- `odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos`

The direct route is now factored through two local statement surfaces:

- `OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement`
- `OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement`

Important correction:

- these local “first bad slice” surfaces must use `r < m`, not `r ≤ m`
- the endpoint `r = m` is realized by the witness `oddLowerHalfFamily`, where slice `m + 1` is
  indeed deficient but the upper-shadow gap is exactly, not strictly above, the middle binomial

and the current global-minimizer target reduces to the latter via:

- `oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap`
- `oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit`

There is now an additional proved reduction layer:

- `totalSize_eq_sum_range_mul_card_slice`
- `totalSize_oddLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit`
- `oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_of_largerTotalSizeThanWitness`

So the active direct-route subtarget can be sharpened further to:

- `OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement`

The old weighted-drop version of Step 3 is not viable in the raw form written below.

Explicit no-go already formalized:

- `lower_boundary_slice_pos_oddHalfCubeMinimalOutsideCounterexample`
- `weightedDrop_oddHalfCubeMinimalOutsideCounterexample`
- `weightedDrop_lt_choose_middle_oddHalfCubeMinimalOutsideCounterexample`
- `choose_middle_lt_upperShadowGap_oddHalfCubeMinimalOutsideCounterexample`

So the 3-dimensional half-cube counterexample has:

- a nonzero lower boundary slice
- `weightedDrop = 7/3 < 3`
- but `upperShadowGap = 4 > 3`

Conclusion: `weightedDrop` is too coarse to serve as the strict optimization functional by itself.
The remaining gap is now sharpened to:

- prove `OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement`

The slice-deficit route now feeds into this through the proved strict total-size inequality above.

## Strategy

### Step 1: cutoff shadow propagation

Generalize the existing lemma
`odd_initial_slices_full_of_lower_boundary_slices_vanish`
to a cutoff form:

- if lower positive-boundary slices vanish only up to rank `k`,
  then slices `0..k` are already full.

This isolates the first bad boundary slice.

### Step 2: first bad slice gives a strict family-slice deficit

Assume:

- slice `k-1` is full
- boundary slice `k` is nonzero

Then the decomposition

- `upShadow(slice_{k-1}) = slice_k ∪ boundary_k`

forces

- `#(𝒟 # k) < choose(2m+1,k)`.

This is the first strictness statement on the direct route.

### Step 3: replace weighted drop with a strict upper-shadow-gap mechanism

The remaining missing ingredient is no longer a weighted-drop optimization theorem.

Instead, we need a strict inequality that sees the extra exposed mass missed by `weightedDrop`,
for example through:

- a strengthened codimension-threshold / partial-sum inequality
- a direct lower bound on the full positive boundary from the first bad slice
- or an additional structural property forced by global boundary minimality

### Step 4: conclude strict upper-shadow gap

Once Step 3 is repaired, combine it with

- `upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily`
- the witness upper bound on global minimizers

to get the target strict inequality.

## Immediate implementation tasks

1. Keep the implemented cutoff propagation lemma.
2. Keep the implemented first-bad-slice strict-deficit lemma.
3. Replace the old weighted-drop target with a strict full-boundary / upper-shadow-gap lemma.

## Current status

- theorem surface is formalized
- closure to the odd theorem is formalized
- Step 1 and Step 2 local lemmas are done
- the live gap is a replacement for the old weighted-drop Step 3
