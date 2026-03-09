# Plan: proving `halfCubeBoundaryLower`

## Target

Prove the last cube theorem placeholder in

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

namely:

```text
halfCubeBoundaryLower

If 0 < |α|, D ⊆ P(α), D is a nonempty down-set, and |D| = 2^(|α|-1),
then |positiveBoundary D| >= choose(|α|, floor(|α|/2)).
```

This is now the only mathematical theorem missing from the exact Erdős #1 route.

## Program summary

The proof program is:

1. reduce the theorem from families to a statement about normalized slice densities
2. package the remaining inequality as an abstract weighted monotone-sequence theorem
3. prove that abstract theorem by forcing an extremizer to a canonical half-cube profile
4. instantiate back to `halfCubeBoundaryLower`
5. discharge the already-routed subtype and arithmetic wrappers

The main route is no longer compression. The active route is a down-set slice optimization theorem.

## Phase 1: family-to-sequence reduction

### Goal

Attach to a down-set `D ⊆ P([n])` the normalized layer profile

```text
a_r := |D_r| / choose(n,r)
```

and prove that `|positiveBoundary D|` dominates the corresponding weighted drop functional.

### File plan

- keep the family-facing API in `ErdosProblems/Problem1CubeHalfBoundary.lean`
- create a new abstract helper file:
  - `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`

### Proposed definitions

```text
sliceDensity (D : Finset (Finset α)) (r : ℕ) : ℚ
weightedDrop (n : ℕ) (a : ℕ → ℚ) : ℚ
```

with

```text
weightedDrop n a
  := ∑ r in range n, (choose n (r+1) : ℚ) * (a r - a (r+1))
```

### Lemmas to prove

1. `sliceDensity_antitone_of_isDownSetFamily`
   - from the local-LYM lemma already in `Problem1CubeHalfBoundary.lean`
   - statement: `sliceDensity D (r+1) ≤ sliceDensity D r`

2. `boundarySlice_ge_density_drop`
   - from the normalized adjacent recurrence already proved
   - statement:
   ```text
   |(positiveBoundary D)_(r+1)| / choose(n,r+1) >= a_r - a_{r+1}
   ```

3. `boundary_card_ge_weightedDrop`
   - sum the previous inequality over `r`
   - conclude:
   ```text
   |positiveBoundary D| >= weightedDrop n a
   ```

4. `halfCubeBoundaryLower_of_weightedDropLower`
   - abstract bridge:
   ```text
   weightedDrop n a >= choose(n, floor(n/2))
   =>
   halfCubeBoundaryLower
   ```

### Acceptance criterion

At the end of Phase 1, the last theorem should be reduced to one abstract sequence statement with no
remaining family combinatorics except the already-proved slice lemmas.

### Status

- started in `Problem1CubeHalfBoundary.lean`
- already formalized:
  - `sliceDensity`
  - `weightedDrop`
  - `sliceDensity_succ_le_sliceDensity_of_isDownSetFamily`
  - `card_positiveBoundary_slice_succ_div_choose_ge_sliceDensity_sub_sliceDensity_succ`
  - `sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary`
  - `weightedDrop_le_card_positiveBoundary`
- the remaining work in Phase 1 is to package the half-cube assumptions as an abstract
  `HalfCubeProfile` theorem input, rather than to prove more family-local combinatorics

## Phase 2: abstract half-mass sequence theorem

### Goal

Prove the purely numerical statement:

```text
If
  - 0 <= a_n <= ... <= a_0 <= 1
  - ∑ r, choose(n,r) * a_r = 2^(n-1),
then
  weightedDrop n a >= choose(n, floor(n/2)).
```

This is the real mathematical core now.

### Proposed packaging

Define a predicate:

```text
HalfCubeProfile n a : Prop
```

recording:

- monotonicity
- `0 ≤ a r`
- `a r ≤ 1`
- half-mass identity

Then state:

```text
halfCubeWeightedDropLower :
  HalfCubeProfile n a -> (choose n (n / 2) : ℚ) ≤ weightedDrop n a
```

### Immediate helper lemmas

1. `weightedDrop_eq_sum_choose_mul_diff`
   - definitional rewrite lemma

2. `halfCubeProfile_mass_eq`
   - restate the half-mass identity in the exact summation form used by the proof

3. `weightedDrop_nonneg_of_monotone`
   - sanity lemma used by later inequalities

### Acceptance criterion

At the end of Phase 2, `halfCubeBoundaryLower` should depend only on `halfCubeWeightedDropLower`.

## Phase 3: solve the sequence theorem by extremizer reduction

### Main proof idea

Treat the feasible profiles as a monotone box-constrained polytope with one linear mass equation.
The objective `weightedDrop n a` is linear in `a`.

The intended argument is:

1. any minimizer may be assumed to have at most one fractional coordinate
2. the monotonicity constraints then force the profile to be a step function, or a step function
   with one middle fractional value
3. the half-mass equation then forces the canonical odd/even half-cube profiles
4. compute `weightedDrop` exactly on those profiles

### Canonical target profiles

Odd `n = 2m + 1`:

```text
a_r = 1 for r <= m
a_r = 0 for r >= m + 1
```

Even `n = 2m`:

```text
a_r = 1 for r < m
a_m = 1/2
a_r = 0 for r > m
```

### Sub-lemmas to target

1. `weightedDrop_linear`
   - explicit linearity in the profile coordinates

2. `extremal_profile_has_at_most_one_fractional_coordinate`
   - prove by a perturbation / exchange argument, not by importing heavy convex-geometry machinery

3. `half_mass_profile_is_canonical_odd`
   - odd-dimensional classification under the half-mass equation

4. `half_mass_profile_is_canonical_even`
   - even-dimensional classification under the half-mass equation

5. `weightedDrop_canonical_odd`
   - compute exact value `choose(2m+1, m)`

6. `weightedDrop_canonical_even`
   - compute exact value `choose(2m, m)`

### Preferred proof style

Prefer an elementary perturbation argument over a general convex-extreme-point development.

The intended pattern is:

- if two separated coordinates are both fractional, shift a small `ε` of mass between them while
  preserving monotonicity and total weighted mass
- show the objective cannot increase under the improving direction
- iterate until only the canonical profile remains

This is more likely to be Lean-manageable than setting up a general linear-programming framework.

## Phase 4: odd/even split if unified proof stalls

If the unified extremizer argument becomes awkward, split immediately into:

1. `halfCubeWeightedDropLower_odd`
2. `halfCubeWeightedDropLower_even`

This is acceptable. The repository already has odd/even witness files, and the combinatorics is
different enough that a split may reduce proof friction rather than increase it.

The unification can happen only at the final wrapper theorem.

## Phase 5: instantiate back to families

After the sequence theorem is proved:

1. deduce `halfCubeBoundaryLower` in `Problem1CubeHalfBoundary.lean`
2. remove the placeholder dependency from:
   - `Problem1CubeHalfLowerFrontier.lean`
   - `Problem1Bridge.lean`
   - `Problem1LowerExactCore.lean`

At this point the exact theorem chain should be theorem-only.

## Fallback route

If Phase 3 fails, the fallback is:

1. keep the same abstract sequence theorem target
2. re-derive it by recursion on dimension using section decompositions of down-sets
3. do not reopen arbitrary-family compression unless that recursive route genuinely collapses

This fallback is acceptable only if it still targets `halfCubeWeightedDropLower`. If it drifts back
to proving a global Harper theorem for arbitrary families, stop.

## What to avoid

- Do not treat compression monotonicity as the default next step.
- Do not try to classify all minimizers before proving the sharp lower bound.
- Do not reintroduce the false `minimalOutside` target.
- Do not bury the sequence theorem inside family-specific proofs; keep it as a clean numerical layer.

## Deliverables

### Lean deliverables

1. `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
2. `boundary_card_ge_weightedDrop`
3. `halfCubeWeightedDropLower`
4. `halfCubeBoundaryLower`

### Verification deliverables

1. `lake build ErdosProblems.Problem1CubeHalfBoundarySequence`
2. `lake build ErdosProblems.Problem1CubeHalfBoundary`
3. `lake build ErdosProblems.Problem1CubeHalfLowerFrontier ErdosProblems.Problem1Bridge`

## Stop condition

If the abstract sequence theorem resists both:

1. the perturbation/extremizer proof, and
2. the odd/even direct proof,

then the blocker should be reclassified as a new standalone discrete-optimization frontier rather
than “unfinished cube formalization”.

That is the honest boundary of the current program.
