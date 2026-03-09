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
- abstract sequence interface added in `Problem1CubeHalfBoundarySequence.lean`
  - `profileMass`
  - `HalfCubeProfile`
  - `HalfCubeWeightedDropLowerStatement`
  - `profileMass_sliceDensity_eq_card`
  - `halfCubeProfile_sliceDensity_of_isDownSetFamily_of_card_eq_half_cube`
  - `halfCubeBoundaryLower_of_halfCubeWeightedDropLower`
- the remaining work in Phase 1 is to package the half-cube assumptions as an abstract
  `HalfCubeProfile` theorem input, rather than to prove more family-local combinatorics
  - this is now complete

## Phase 2: abstract half-mass sequence theorem

### Goal

Original candidate target:

```text
If
  - 0 <= a_n <= ... <= a_0 <= 1
  - ∑ r, choose(n,r) * a_r = 2^(n-1),
then
  weightedDrop n a >= choose(n, floor(n/2)).
```

This target is false.

Concrete formalized counterexample:

- `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
  - `halfCubeProfileCounterexample`
  - `not_HalfCubeWeightedDropLowerStatement`

In dimension `2`, the profile

```text
a_0 = 1, a_1 = 1/2, a_2 = 0
```

has half-cube mass, but

```text
weightedDrop = 3/2 < 2 = choose(2,1).
```

So `weightedDrop` is a valid lower bound for the true boundary, but it is too weak to close the
half-cube theorem.

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

The original acceptance criterion is invalid because the candidate theorem is false.

### Status

- the interface reduction is complete
- the original abstract target has been disproved
- the live blocker is no longer `HalfCubeWeightedDropLowerStatement`
- the next route needs a stronger abstract quantity than `weightedDrop`

## Phase 3: replace `weightedDrop` by a stronger slice-extremal quantity

### Main proof idea

The failure shows that the boundary cannot be controlled sharply from the slice densities alone via
the linear drop functional

```text
choose(n,r+1) * (a_r - a_{r+1}).
```

The missing strength must come from extra structure inside each fixed-size slice, namely the size of
the upper shadow of the `r`-slice family.

So the next candidate route is:

1. for each `r`, use
   ```text
   |(positiveBoundary D)_(r+1)| + |D_(r+1)| = |upShadow(D_r)|
   ```
2. replace the weak local-LYM lower bound on `|upShadow(D_r)|` by a sharp lower bound as a function
   of `|D_r|`
3. optimize the resulting nonlinear slice recurrence under the half-mass constraint

This points to a Kruskal-Katona / Lovász style slice theorem rather than a pure monotone-sequence LP.

Status update:

- this exact identity is now formalized in `Problem1CubeHalfBoundary.lean`
  - `upShadow_slice_eq_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily`
  - `card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily`
- the global exact reduction is also formalized there
  - `upperShadowGap`
  - `upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily`
  - `HalfCubeUpperShadowGapLowerStatement`
  - `halfCubeBoundaryLower_of_halfCubeUpperShadowGapLower`
- so the live frontier is no longer “find a better linear surrogate than `weightedDrop`”
- it is now: prove the sharp lower bound for the exact nonlinear quantity `upperShadowGap`

## Phase 4: new main route via sharp upper-shadow bounds

### Step 4A: formalize the exact boundary slice identity

For down-sets `D`, prove:

```text
|(positiveBoundary D)_(r+1)| + |D_(r+1)| = |upShadow(D_r)|.
```

This is stronger than the current recurrence because it keeps the actual upper shadow instead of
only its local-LYM lower bound.

Status:

- complete in `Problem1CubeHalfBoundary.lean`
- strengthened further to the exact global identity
  ```text
  |positiveBoundary D| = sum_r (|upShadow(D_r)| - |D_(r+1)|)
  ```
  via `upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily`

### Step 4B: import the sharp slice theorem

Use mathlib’s Kruskal-Katona / Lovász layer machinery, if possible, to derive a lower bound of the
form

```text
|upShadow(A)| >= Φ_{n,r}(|A|)
```

for `A ⊆ (n choose r)`.

This is now the most plausible source of the missing even-dimensional strength.

Status:

- partially complete in `Problem1CubeHalfBoundary.lean`
- the codimension-1 threshold case is now formalized:
  - `choose_pred_le_card_upShadow_of_choose_pred_le_card`
  - `choose_pred_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_pred`
- concretely, if an `r`-uniform slice has size at least `choose(n-1, r-1)`, then its upper shadow
  has size at least `choose(n-1, r)`, hence the corresponding
  `|(positiveBoundary D)_(r+1)| + |D_(r+1)|` term is at least `choose(n-1, r)`
- this is a real nonlinear shadow bound, but it is still only the first threshold case, not yet the
  full function `Φ_{n,r}(|A|)`

### Step 4C: optimize the nonlinear recurrence

After Step 4B, the half-cube theorem reduces to a discrete optimization problem on slice sizes:

```text
B_{r+1} >= Φ_{n,r}(|D_r|) - |D_{r+1}|.
```

The remaining task is to show that, under:

- down-set monotonicity
- total size `|D| = 2^(n-1)`

the sum of these lower bounds is at least `choose(n, floor(n/2))`.

### Step 4D: odd/even split

Do not force a unified optimization theorem if the even case is the only place where the weak route
failed. Split the nonlinear argument into:

1. odd dimensions
2. even dimensions

immediately if that makes the optimization tractable.

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

These remain the expected sharp slice-density profiles, but they are no longer enough by themselves
to determine the right abstract theorem.

## Phase 5: instantiate the stronger abstract theorem back to families

After the stronger slice-shadow theorem is proved:

1. deduce `halfCubeBoundaryLower` in `Problem1CubeHalfBoundary.lean`
2. remove the placeholder dependency from:
   - `Problem1CubeHalfLowerFrontier.lean`
   - `Problem1Bridge.lean`
   - `Problem1LowerExactCore.lean`

At this point the exact theorem chain should be theorem-only.

## Fallback route

If the sharp upper-shadow route stalls, the fallback is:

1. keep the same abstract sequence theorem target
2. replace `weightedDrop` by a stronger recursively defined quantity built from actual section
   boundary sizes or upper shadows
3. re-derive the half-cube lower bound by recursion on dimension using section decompositions of
   down-sets
3. do not reopen arbitrary-family compression unless that recursive route genuinely collapses

This fallback is acceptable only if it still targets the down-set half-cube theorem directly. If it
drifts back to proving a global Harper theorem for arbitrary families, stop.

## What to avoid

- Do not treat compression monotonicity as the default next step.
- Do not try to classify all minimizers before proving the sharp lower bound.
- Do not reintroduce the false `minimalOutside` target.
- Do not bury the sequence theorem inside family-specific proofs; keep it as a clean numerical layer.

## Deliverables

### Lean deliverables

1. `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
2. `boundary_card_ge_weightedDrop`
3. explicit falsity witness for `HalfCubeWeightedDropLowerStatement`
4. a stronger replacement abstract theorem
5. `halfCubeBoundaryLower`

### Verification deliverables

1. `lake build ErdosProblems.Problem1CubeHalfBoundarySequence`
2. `lake build ErdosProblems.Problem1CubeHalfBoundary`
3. `lake build ErdosProblems.Problem1CubeHalfLowerFrontier ErdosProblems.Problem1Bridge`

## Stop condition

If both:

1. the sharp upper-shadow route, and
2. the recursive down-set route,

fail to replace the false `weightedDrop` target by a true one, then the blocker should be
reclassified as a new standalone slice-isoperimetric frontier rather
than “unfinished cube formalization”.

That is the honest boundary of the current program.
