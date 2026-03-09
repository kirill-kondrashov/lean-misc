# Research Program: Erdős #1 Phase 3 — revised half-cube boundary program

## Current frontier

The live blocker is no longer in the arithmetic layer. It is isolated as the cube theorem placeholder

- `ErdosProblems/Problem1CubeHalfBoundary.lean`
  - `halfCubeBoundaryLower`

with statement:

```text
If 0 < |α|, D ⊆ P(α), D is a nonempty down-set, and |D| = 2^(|α|-1),
then |positiveBoundary D| >= choose(|α|, floor(|α|/2)).
```

The subtype frontier and the public exact theorem route already pass through this statement, so this
is now the only mathematical gap that matters.

## Current code state

The program has already crossed the structural reductions.

### Already done

- Subtype transport is complete:
  - `negativeHalfFamilySubcubeNat`
  - `isDownSetFamily_negativeHalfFamilySubcubeNat`
  - `card_negativeHalfFamilySubcubeNat_eq_half_cube`
  - boundary transport back to `positiveBoundaryFamilyNat`
- The sharp odd/even half-cube witnesses are formalized, together with their exact boundary sizes.
- `positiveBoundary = upShadow \\ family` and the section decomposition infrastructure are in place.
- The local down-set slice machinery is now proved in `Problem1CubeHalfBoundary.lean`:
  - normalized slice monotonicity for down-sets
  - outside-slice local-LYM after removing the boundary slice
  - the raw adjacent recurrence
  - the normalized boundary-drop inequality

### Explicitly not done

- Full boundary monotonicity under compression is still unproved.
- A general Harper theorem for arbitrary families is still unproved.
- The final cube theorem is still an axiom placeholder.

## Technical correction

The unrestricted `|α| = 0` form of the cube theorem is false.

- If `α = ∅`, then the unique down-set has size `2^(0-1) = 1`.
- Its positive boundary is empty.
- So the correct theorem must assume `0 < |α|`.

This does not affect the Erdős #1 application because the subtype family comes from a nonempty
finite set `A`, hence automatically satisfies `0 < |A|`.

## Revised mathematical reduction

The current local lemmas expose the real remaining problem as a weighted optimization on layer
densities of a down-set.

For a down-set `D ⊆ P([n])`, define

```text
a_r := |D_r| / choose(n,r)
b_{r+1} := |(positiveBoundary D)_{r+1}| / choose(n,r+1)
```

where `D_r` is the `r`-slice.

The codebase now already supplies the key local facts:

1. `a_{r+1} <= a_r`
   - normalized slices of a down-set are nonincreasing
2. `b_{r+1} >= a_r - a_{r+1}`
   - the normalized boundary slice controls the drop between adjacent slice densities
3. `sum_r choose(n,r) * a_r = |D|`
   - by definition of the slice densities

So at half-cube size the remaining theorem reduces to the weighted monotone-sequence claim

```text
If
  - 0 <= a_n <= ... <= a_0 <= 1
  - sum_r choose(n,r) * a_r = 2^(n-1),
then
  sum_{r=0}^{n-1} choose(n,r+1) * (a_r - a_{r+1})
    >= choose(n, floor(n/2)).
```

Because

```text
|positiveBoundary D|
  = sum_{r=0}^{n-1} |(positiveBoundary D)_{r+1}|
  >= sum_{r=0}^{n-1} choose(n,r+1) * (a_r - a_{r+1}).
```

This is the precise blocker now exposed by the Lean development.

## Extremal profiles to expect

The expected sharp profiles on the sequence side are:

- odd `n = 2m + 1`:

```text
a_r = 1 for r <= m, and a_r = 0 for r >= m + 1
```

- even `n = 2m`:

```text
a_r = 1 for r < m, a_m = 1/2, and a_r = 0 for r > m
```

These are exactly the normalized layer profiles of the sharp half-cube witnesses already present in
the repository. Full uniqueness of extremizers is not required for the Erdős #1 application; the
sharp lower bound is enough.

## Revised strategic view

The current blocker is not “more local cube infrastructure”. That work is already largely done.

The main route should now be:

1. reduce the down-set theorem to the weighted monotone-sequence inequality above
2. solve that inequality directly
3. instantiate it to `halfCubeBoundaryLower`
4. immediately discharge the subtype frontier and exact theorem chain

The compression / Harper route is now a fallback, not the primary path.

## Main route: down-set slice LP / telescoping

### Step A1: keep `Problem1CubeHalfBoundary.lean` as the cube interface

This file should continue to contain:

- the cube theorem statement
- local slice lemmas
- the final instantiation of the abstract sequence theorem back to families

Do not overload it with a second large compression development.

### Step A2: formalize the weighted reduction

Either in `Problem1CubeHalfBoundary.lean` or a new file such as

- `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`

prove the family-to-sequence reduction:

```text
|positiveBoundary D|
  >= sum_{r=0}^{n-1} choose(n,r+1) * (a_r - a_{r+1})
```

for down-sets `D`.

Deliverables:

- a clean definition of the normalized slice density sequence
- a clean definition of the weighted drop sum
- a theorem reducing `halfCubeBoundaryLower` to the abstract weighted inequality

### Step A3: solve the abstract weighted inequality

This is now the main mathematical task.

Preferred proof styles:

1. a direct telescoping / summation argument using monotonicity and symmetry of binomial
   coefficients
2. an explicit linear-programming style extremal argument on monotone sequences
3. an odd/even split if the unified formula is awkward in Lean

The important point is that this step is no longer about arbitrary families. It is a pure theorem
about monotone sequences with binomial weights.

Deliverable:

- `half_cube_weighted_drop_lower`

### Step A4: instantiate the abstract inequality to the cube theorem

Use the reduction from Step A2 plus the weighted theorem from Step A3 to prove:

- `halfCubeBoundaryLower`

This should close the only remaining placeholder in `Problem1CubeHalfBoundary.lean`.

### Step A5: discharge the already-routed frontier

After Step A4, the following files should become theorem-only consequences:

- `ErdosProblems/Problem1CubeHalfLowerFrontier.lean`
- `ErdosProblems/Problem1Bridge.lean`
- `ErdosProblems/Problem1LowerExactCore.lean`

At that point the arithmetic statement is no longer the research problem.

## Fallback route: recursive section proof

If Step A3 stalls, the next fallback is not full arbitrary-family compression. It is to stay inside
down-sets and use the already-proved section decompositions:

- `memberSubfamily_positiveBoundary`
- down-set section closure lemmas
- half-mass inequalities on sections

The aim would be to re-derive the same weighted sequence theorem by induction on dimension or on the
middle-rank deficit.

This fallback is acceptable only if it is clearly converging to the same abstract monotone-sequence
statement. If it starts rebuilding a full Harper theorem from scratch, stop.

## Parked route: compression / Harper

Compression is no longer the default route because the hard missing lemma remains exactly the same as
before:

```text
|positiveBoundary (downCompression_i F)| <= |positiveBoundary F|
```

That route should stay parked unless one of the following happens:

1. the sequence optimization route is shown to be insufficient
2. a one-step compression monotonicity proof becomes unexpectedly accessible
3. an external mathlib theorem or literature formalization gives a near-complete Harper bridge

Without one of those, more compression engineering is likely to spend time without reducing the live
blocker.

## What not to do

- Do not keep treating arbitrary-family compression as the main plan.
- Do not search for another “middle-layer pressure” statement; the frontier statement is already
  correct.
- Do not revive the false `minimalOutside` lower bound.
- Do not add more witness files unless they directly support the weighted sequence proof.
- Do not spend time classifying all extremizers before proving the sharp lower bound itself.

## Lean file split

Recommended active split now:

1. `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - theorem statement
   - local slice lemmas
   - reduction from families to weighted drop sums
   - final cube theorem

2. `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
   - abstract monotone-sequence lemmas
   - odd/even weighted inequality
   - sharp profile computations

3. `ErdosProblems/Problem1CubeHalfLowerFrontier.lean`
   - subtype specialization wrapper only

4. `ErdosProblems/Problem1Bridge.lean`
   - public exact theorem routing only

Compression and minimal-outside files remain support libraries, not the main research surface.

## Early checkpoints

Checkpoint 1:

```text
formalize the weighted drop lower bound for |positiveBoundary D|
from the existing adjacent-slice lemmas
```

Checkpoint 2:

```text
prove the odd-dimensional weighted sequence inequality
```

Checkpoint 3:

```text
prove the even-dimensional weighted sequence inequality
```

Checkpoint 4:

```text
instantiate the sequence theorem to halfCubeBoundaryLower
```

If Checkpoint 2 or 3 stalls, the issue is no longer cube combinatorics. It is the abstract weighted
optimization theorem and should be treated as such.

## Success criterion

This program succeeds when the following chain is theorem-only:

```text
weighted monotone-sequence lower bound
=> halfCubeBoundaryLower
=> subcubeHalfCubeBoundaryLower_frontier
=> PositiveBoundaryMiddleLower
=> exact Dubroff-Fox-Xu integer lower bound
```

In Lean terms:

1. replace the placeholder `halfCubeBoundaryLower` by a proof
2. keep `Problem1CubeHalfLowerFrontier.lean` as a thin specialization wrapper
3. route `Problem1Bridge.lean` and the exact integer theorem through the proved cube theorem
4. remove the remaining exact-theorem frontier dependency

## Short summary

The honest current blocker is:

```text
one weighted extremal inequality on monotone layer densities of a down-set.
```

That is the research program that now matches the actual Lean state.
