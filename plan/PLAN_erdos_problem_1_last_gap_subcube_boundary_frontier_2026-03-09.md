# Plan: Erdős Problem #1 last gap — subtype half-cube boundary frontier

This plan replaces the discarded March 9 `minimalOutside` version. That sharpening is false, so the
repository should not keep aiming at it.

## Correction to the previous plan

The statement

```text
choose(n, floor(n/2)) ≤ |minimalOutside D|
```

for every half-cube down-set `D` is false.

Concrete counterexample in dimension `2`:

- let `α = {1,2}`
- let `D = {∅, {1}}`
- then `D` is a nonempty down-set and `|D| = 2 = 2^(2-1)`
- but
  - `minimalOutside D = {{2}}`, so `|minimalOutside D| = 1`
  - `positiveBoundary D = {{2}, {1,2}}`, so `|positiveBoundary D| = 2`

Hence:

```text
choose(2,1) = 2
```

matches the boundary size, not the minimal-outside size.

So the last gap remains a boundary theorem, not a minimal-excluded-antichain theorem.

## Current blocker

The true remaining frontier is now:

- `ErdosProblems/Problem1CubeHalfLowerFrontier.lean`
  - `subcubeHalfCubeBoundaryLower_frontier`

with statement:

```text
If A ⊆ ℕ is sum-distinct and nonempty, then

choose(|A|, floor(|A|/2))
  ≤ |positiveBoundary (negativeHalfFamilySubcubeNat A)|.
```

This is the correct final subtype-cube theorem still missing.

Focused proof program for the cube theorem:

- `plan/PLAN_erdos_problem_1_half_cube_boundary_lower_proof_program_2026-03-09.md`

## What is already proved

### Transport layer

- `ErdosProblems/Problem1CubeNatBridge.lean`
  - `negativeHalfFamilySubcubeNat`
  - `isDownSetFamily_negativeHalfFamilySubcubeNat`
  - `card_negativeHalfFamilySubcubeNat_eq_half_cube`
  - `image_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat`
  - `card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat`

So the subset-sum problem has already been transported to the Boolean cube on the subtype `A`.

### Boundary recursion layer

- `ErdosProblems/Problem1CubeBoundary.lean`
  - `positiveBoundary_eq_upShadow_sdiff`
  - `nonMemberSubfamily_positiveBoundary`
  - `memberSubfamily_positiveBoundary`
  - recursive cardinality inequalities for boundary sections

### Down-set reduction layer

- `ErdosProblems/Problem1CubeDownset.lean`
  - down-compression infrastructure
  - existence of same-card down-set reductions
  - section-size inequalities for down-sets

This is still useful if a proof of boundary monotonicity under compression is found, but that is no
longer assumed as the main route.

### Minimal-outside layer

- `ErdosProblems/Problem1CubeMinimalOutside.lean`
  - `minimalOutside`
  - `upperClosure_minimalOutside_eq_compl`
  - `minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily`

This remains useful as a lower-support object, but it is not itself the final quantity to minimize.

### Sharp witnesses

- `ErdosProblems/Problem1CubeOddExtremizer.lean`
  - exact odd half-cube witness
  - exact boundary size
  - exact `minimalOutside` size
- `ErdosProblems/Problem1CubeEvenExtremizer.lean`
  - exact even half-cube witness
  - exact boundary size
  - exact `minimalOutside` size

So the sharp constant is already verified on the extremizers.

### Public routing

- `ErdosProblems/Problem1CubeHalfLowerFrontier.lean`
  - subtype boundary frontier
  - arithmetic positive-boundary theorem
  - exact integer lower theorem
- `ErdosProblems/Problem1Bridge.lean`
  - public bridge now routes through the subtype-cube frontier

## Exact theorem to prove

The right cube theorem is:

```text
halfCubeBoundaryLower

For any finite α and any family 𝒟 ⊆ P(α),
if
  - 0 < |α|,
  - 𝒟 is nonempty,
  - 𝒟 is a down-set,
  - |𝒟| = 2^(|α|-1),
then
  choose(|α|, floor(|α|/2)) ≤ |positiveBoundary 𝒟|.
```

This is strong enough to discharge the subtype frontier immediately by specialization to
`negativeHalfFamilySubcubeNat A`.

Technical correction:

- the unrestricted `|α| = 0` version is false
  - for `α = ∅`, the unique down-set has size `2^(0-1) = 1`, but its positive boundary is empty
  - so the actual cube theorem should include `0 < |α|`
  - this is harmless for the subtype application, since `A.Nonempty` already gives `0 < |A|`

## Main proof routes

### Route A: direct half-cube boundary theorem

Create a dedicated file:

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

Primary target:

```text
theorem halfCubeBoundaryLower
  {α : Type*} [DecidableEq α] [Fintype α] {𝒟 : Finset (Finset α)}
  (hcard_pos : 0 < Fintype.card α)
  (hne : 𝒟.Nonempty)
  (h𝒟 : IsDownSetFamily 𝒟)
  (hcard : #𝒟 = 2 ^ (Fintype.card α - 1)) :
  Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ #(positiveBoundary 𝒟)
```

This is the cleanest target because it matches the actual open frontier exactly.

### Route B: derive a stronger but true theorem on a paired invariant

Since `minimalOutside` alone is too small, the right auxiliary object may be a sum such as:

```text
|minimalOutside 𝒟| + extra_term(𝒟)
```

where `extra_term` measures the non-minimal part of the boundary.

The existing section decomposition

- `memberSubfamily_positiveBoundary`

already splits the boundary into:

1. a section gap term
2. a recursive boundary term

So a viable route is to define the right inductive quantity directly from that decomposition rather
than forcing everything through `minimalOutside`.

### Route C: mathlib extremal-set-theory probe

Probe whether mathlib already yields the boundary theorem from a known inequality.

Relevant files:

- `Mathlib/Combinatorics/SetFamily/LYM.lean`
- `Mathlib/Combinatorics/SetFamily/AhlswedeZhang.lean`
- `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`

Current assessment:

- `Sperner` bounds antichains, but the boundary is not an antichain in general.
- `minimalOutside` is an antichain, but by the dimension-2 counterexample it is too small to carry
  the desired lower bound by itself.
- so any mathlib shortcut would need to control the full boundary or a weighted version of it.

Therefore Route C is a probe, not the default proof plan.

## Concrete implementation steps

### Step 1: add the dedicated theorem file

Create:

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

This file should only contain the final half-cube boundary theorem and helper lemmas directly needed
for it.

Status:

- done structurally
- the file now exists and isolates the last gap as `HalfCubeBoundaryLowerStatement`
- it already contains the two transport lemmas
  - `subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower`
  - `positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower`
- the remaining work in that file is to replace the frontier placeholder by the actual theorem
  `halfCubeBoundaryLower`

### Step 2: reduce the down-set theorem to a weighted slice inequality

Use the slice lemmas already established in:

- `Problem1CubeHalfBoundary.lean`
- `Problem1CubeBoundary.lean`
- `Problem1CubeDownset.lean`

The active reduction is now:

1. define normalized slice densities `a_r := |𝒟 # r| / choose(n,r)`
2. use down-set local-LYM to prove `a_{r+1} ≤ a_r`
3. use the boundary-slice recurrence to prove
   `|(positiveBoundary 𝒟)#(r+1)| / choose(n,r+1) ≥ a_r - a_{r+1}`
4. sum these inequalities into a weighted lower bound for `|positiveBoundary 𝒟|`
5. discharge the remaining problem as a pure monotone-sequence optimization at half mass

Status:

- started in `Problem1CubeHalfBoundary.lean`
- the file now contains slice-shadow and local-LYM helpers for down-sets
- it also contains the parallel local-LYM bound for the outside slice after removing the positive
  boundary slice
- it now contains the raw adjacent recurrence and its normalized form
  - `card_slice_mul_le_card_positiveBoundary_slice_succ_add_card_slice_succ_mul`
  - `card_slice_div_choose_le_card_positiveBoundary_slice_succ_add_card_slice_succ_div_choose`
  - `card_positiveBoundary_slice_succ_div_choose_ge_sub_card_slice_div_choose`
- it now contains the first global weighted reduction layer
  - `sliceDensity`
  - `weightedDrop`
  - `sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary`
  - `weightedDrop_le_card_positiveBoundary`
- the blocker in this step is now exact:
  prove the weighted monotone-sequence inequality obtained after summing the normalized slice-drop
  bounds

### Step 3: keep `minimalOutside` only as support, not as the target

Use:

- `minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily`

only when it gives a genuine lower bound that is compatible with the recurrence. Do not attempt to
prove the false global theorem `choose ≤ |minimalOutside 𝒟|`.

### Step 4: discharge the subtype frontier

In `Problem1CubeHalfLowerFrontier.lean`, replace:

- `subcubeHalfCubeBoundaryLower_frontier`

by:

```text
by
  apply halfCubeBoundaryLower
  ...
```

using:

- `negativeHalfFamilySubcubeNat_nonempty`
- `isDownSetFamily_negativeHalfFamilySubcubeNat`
- `card_negativeHalfFamilySubcubeNat_eq_half_cube`

Status:

- partially done
- `Problem1CubeHalfLowerFrontier.lean` now imports `Problem1CubeHalfBoundary.lean`
- the subtype frontier and arithmetic boundary theorem are already routed through the general cube
  placeholder `halfCubeBoundaryLower`
- when `halfCubeBoundaryLower` is proved, this file should become a short specialization wrapper

### Step 5: only after that clean the old arithmetic axiom

Once the subtype theorem is proved:

1. route `Problem1LowerExactCore.lean` through the proved subtype theorem
2. remove or deprecate `positiveBoundaryMiddleLower_frontier`
3. keep `Problem1Bridge.lean` surface unchanged

## What not to do

- Do not keep pursuing the false `minimalOutside` frontier.
- Do not spend more time on arbitrary-family compression monotonicity unless it directly helps the
  half-cube boundary theorem.
- Do not re-express the last gap as a subset-sum theorem; that translation is already done.
- Do not assume the odd/even sharp witnesses imply the universal theorem without an extremal
  comparison argument.

## Success criterion

The plan is complete when:

1. `Problem1CubeHalfBoundary.lean` proves `halfCubeBoundaryLower`.
2. `subcubeHalfCubeBoundaryLower_frontier` is replaced by a theorem.
3. `Problem1CubeHalfLowerFrontier.lean`, `Problem1Bridge.lean`, and the exact integer lower theorem
   build through the proved cube theorem.
4. the remaining open item is not “find the right frontier statement” anymore; it is gone.
