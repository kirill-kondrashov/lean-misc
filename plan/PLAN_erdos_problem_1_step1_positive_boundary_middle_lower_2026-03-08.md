# Plan: Erdős #1 step 1 — prove `PositiveBoundaryMiddleLower`

## Goal

Discharge the current integer exact-lower frontier in

- `ErdosProblems/Problem1LowerExactCore.lean`

by proving the theorem

```text
PositiveBoundaryMiddleLower
```

that is, for every sum-distinct set `A ⊆ {1, ..., N}`,

```text
C(|A|, floor(|A|/2)) <= |positiveBoundaryFamilyNat(A)|.
```

Combined with the already proved upper bound

```text
|positiveBoundaryFamilyNat(A)| <= N,
```

this yields the exact Dubroff-Fox-Xu integer lower theorem

```text
C(|A|, floor(|A|/2)) <= N.
```

## Current Lean state

Already formalized in `Problem1LowerExactCore.lean`:

- `negativeHalfFamilyNat A`
- `positiveBoundaryFamilyNat A`
- `positiveBoundaryFamilyNat_card_le`
- `PositiveBoundaryMiddleLower`
- `erdos_1_lower_bound_exact_of_positiveBoundaryMiddleLower`

So the remaining task is exactly to replace the frontier input

- `positiveBoundaryMiddleLower_frontier`

with a theorem from base axioms.

## Mathematical formulation

Write

- `A = {a_1, ..., a_n}`
- `T = sum(A)`
- `G(A) = { S ⊆ A : 2 sum(S) < T }`
- `B^+(A) = { S ⊆ A : T < 2 sum(S) and exists a in S, 2 sum(S \ {a}) < T }`

Then the target is

```text
|B^+(A)| >= C(n, floor(n/2)).
```

The intended route is:

1. prove `|G(A)| = 2^(n-1)`
2. identify `B^+(A)` with the positive vertex boundary of `G(A)`
3. prove a half-cube boundary lower bound
   `|∂^+ G(A)| >= C(n, floor(n/2))`

Step 3 is the actual hard combinatorial theorem.

## Proof decomposition

### Phase 1: half-cube cardinality

Prove that distinct subset sums imply:

- no subset sum equals `T / 2`
- complement swaps `G(A)` with its strict upper half
- therefore `|G(A)| = 2^(n-1)`

Lean deliverables:

- `subset_sum_ne_half_total_of_isSumDistinct`
- `negativeHalfFamilyNat_card`

### Phase 2: boundary identification

Show that `positiveBoundaryFamilyNat A` is exactly the positive vertex boundary of
`negativeHalfFamilyNat A`.

This should be stated as an iff between:

- the current concrete arithmetic definition of `positiveBoundaryFamilyNat`
- a cube-boundary statement using one-element insertion/deletion

Lean deliverables:

- `mem_positiveBoundaryFamilyNat_iff_boundary`
- `positiveBoundaryFamilyNat_eq_positiveBoundary`

### Phase 3: combinatorial boundary lower bound

Formalize the pure cube theorem:

```text
If F is a family of subsets of an n-element set and |F| = 2^(n-1),
then its positive vertex boundary has size at least C(n, floor(n/2)).
```

This is the Harper-style step.

Possible implementation routes:

1. derive it from existing mathlib `SetFamily` shadow / LYM / Kruskal-Katona machinery
2. formalize a direct Harper theorem for half-cube boundary size
3. formalize a symmetric-chain proof if that ends up shorter than rebuilding Harper

Lean deliverable:

- `half_cube_positive_boundary_card_lower`

### Phase 4: final assembly

Combine:

- `negativeHalfFamilyNat_card`
- `positiveBoundaryFamilyNat_eq_positiveBoundary`
- `half_cube_positive_boundary_card_lower`

to prove:

- `PositiveBoundaryMiddleLower`

and then remove

- `positiveBoundaryMiddleLower_frontier`

from `Problem1LowerExactCore.lean`.

## Likely bottleneck

The bottleneck is Phase 3, not Phases 1 or 2.

Phases 1 and 2 are problem-specific arithmetic/cube bookkeeping and should be routine.
Phase 3 is the actual combinatorial theorem. If mathlib does not already expose the right
vertex-isoperimetric consequence of its shadow machinery, we may need a dedicated local theorem.

## Minimal success criterion

For this step to count as complete:

1. `positiveBoundaryMiddleLower_frontier` is removed
2. `PositiveBoundaryMiddleLower` is proved from base axioms
3. `erdos_1_lower_bound_exact_of_positiveBoundaryMiddleLower` becomes theorem-only
4. the integer exact literature axiom can be replaced by this theorem

## Nice-to-have after completion

After Step 1 lands, immediately route

- `erdos_1_dubroff_fox_xu_lower_exact`

through the new theorem, and then start the real analogue with the same structure.
