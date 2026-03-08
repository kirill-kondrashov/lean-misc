# Research Program: Erdős #1 Phase 3 — revised half-cube boundary program

## Frontier statement

The current blocker in

- `ErdosProblems/Problem1LowerExactCore.lean`

is still the theorem

```text
PositiveBoundaryMiddleLower
```

which has now been reduced to the pure cube problem:

```text
If F ⊆ P([n]) and |F| = 2^(n-1),
then |∂^+ F| >= C(n, floor(n/2)).
```

Here:

- `P([n])` is the Boolean cube of all subsets of an `n`-element set
- `∂^+ F := { S ∉ F : exists a ∈ S, S \ {a} ∈ F }`
  is the positive vertex boundary
- `C(n,k)` is `choose(n,k)`

The important correction after criticism is:

- the real missing mathematics is not a vague "middle-layer pressure lemma"
- the real missing mathematics is an exact Harper-type extremal theorem

So the proof plan must target that theorem directly.

## What is already done

In the current Erdos1 code we already have:

- `negativeHalfFamilyNat`
- `positiveBoundaryFamilyNat`
- `positiveVertexBoundaryNat`
- `mem_positiveBoundaryFamilyNat_iff_boundary`
- `positiveBoundaryFamilyNat_eq_positiveBoundary`
- `negativeHalfFamilyNat_card`
- `positiveBoundaryFamilyNat_card_le`

Therefore the remaining work is no longer about subset sums. It is only about the Boolean cube.

## What mathlib gives and what it does not

Useful existing infrastructure:

- `Mathlib/Combinatorics/SetFamily/Shadow.lean`
  - `Finset.shadow`
  - `Finset.upShadow`
  - `mem_shadow_iff`
  - `mem_upShadow_iff_erase_mem`
- `Mathlib/Combinatorics/SetFamily/LYM.lean`
  - Sperner / LYM
- `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`
  - `kruskal_katona`
  - `kruskal_katona_lovasz_form`

What is not present:

- no ready-made Harper vertex-isoperimetric theorem
- no direct theorem minimizing positive vertex boundary at fixed family size

So the research program must build exactly that missing extremal layer.

## Corrected strategic view

The previous Route B plan was too optimistic. Its weak point was:

```text
derive layerwise shadow bounds
=> aggregate them
=> recover the exact boundary constant C(n, floor(n/2))
```

That last implication is basically the whole theorem in disguise.

So the corrected strategy is:

1. make the exact extremizer theorem the main target
2. use compression as the primary route
3. use shadow / Kruskal-Katona only as a bounded probe for reusable lemmas and possible shortcuts

## Main theorem to aim for

The actual target should be stated as:

```text
Among all families F ⊆ P([n]) of a fixed size m,
the minimum of |∂^+ F| is attained by an initial segment of simplicial order.
```

For our application we only need the special case `m = 2^(n-1)`.

Then the required corollary is:

```text
If |F| = 2^(n-1), then |∂^+ F| >= C(n, floor(n/2)).
```

This immediately matches the exact Erdos1 frontier.

## Exact extremizer shape at half the cube

Write `n = 2m` or `n = 2m + 1`.

For odd `n = 2m + 1`:

```text
L_odd := { S : |S| <= m }
```

has size `2^(n-1)`, and

```text
∂^+ L_odd = { S : |S| = m + 1 }
```

so

```text
|∂^+ L_odd| = C(n, m + 1) = C(n, floor(n/2)).
```

For even `n = 2m`:

```text
L_even := { S : |S| < m } union I
```

where `I` is an initial segment of the middle layer `{ S : |S| = m }` in simplicial order chosen so
that `|L_even| = 2^(n-1)`.

Then the required sharp theorem is that

```text
|∂^+ L_even| = C(n, m).
```

The program should not pretend that "some half of the middle layer" is enough. The exact initial
segment structure matters.

## Primary route: compression / Harper

This is now the main route.

### Step A1: finite-cube model

Work in `Fin n`, with families

```text
F : Finset (Finset (Fin n)).
```

Define:

- positive boundary
- simplicial order / initial segments
- rank layers if needed

Deliverable:

- `ErdosProblems/Problem1CubeBoundary.lean`

### Step A2: identify our boundary with mathlib `upShadow`

Prove:

```text
∂^+ F = (upShadow F) \ F
```

This should be done early because it prevents two parallel APIs.

Deliverable:

- `positive_boundary_eq_upShadow_sdiff`

### Step A3: define coordinate compressions

Define the relevant compressions on cube families:

```text
C_i(F)
```

or the standard UV-compressions if that aligns better with existing mathlib.

Need:

- card preservation
- termination of repeated compression
- compressed families become down-sets / initial segments

Deliverables:

- `compression_preserves_card`
- `iterated_compression_exists_downset`

### Step A4: prove boundary monotonicity under compression

This is the central technical lemma:

```text
|∂^+ (C_i(F))| <= |∂^+ F|.
```

Without this, compression does not help.

This is the place where the whole program can fail, so it should be attacked early.

Deliverable:

- `compression_boundary_card_le`

### Step A5: reduce to down-sets

From Step A4 conclude:

```text
For every F, there exists a down-set D with |D| = |F| and |∂^+ D| <= |∂^+ F|.
```

So to prove a lower bound on `|∂^+ F|`, it suffices to prove it for down-sets.

Deliverable:

- `exists_downset_card_eq_boundary_le`

### Step A6: solve the half-cube problem for down-sets

This is the exact extremal theorem specialized to down-sets.

Show:

```text
If D is a down-set and |D| = 2^(n-1),
then |∂^+ D| >= C(n, floor(n/2)).
```

And identify the extremizer:

- odd `n`: all layers up to rank `m`
- even `n`: all layers below `m`, plus an initial segment of the middle layer

Deliverables:

- `half_cube_downset_boundary_card_lower`
- `half_cube_initial_segment_boundary_card`

### Step A7: conclude the general cube theorem

Combine A5 and A6 to obtain:

```text
If |F| = 2^(n-1), then |∂^+ F| >= C(n, floor(n/2)).
```

Deliverable:

- `half_cube_positive_boundary_card_lower_on_fin`

### Step A8: bridge back to Erdos1

Use the already proved bridge in `Problem1LowerExactCore.lean`:

```text
|G(A)| = 2^(|A|-1)
B^+(A) = ∂^+ G(A)
|B^+(A)| <= N
```

to deduce:

```text
C(|A|, floor(|A|/2)) <= N.
```

Deliverables:

- remove `positiveBoundaryMiddleLower_frontier`
- prove `PositiveBoundaryMiddleLower`
- route the integer exact literature theorem through it

## Secondary route: bounded shadow / Kruskal-Katona probe

This route is no longer the main proof plan. It is only an early probe for reusable lemmas.

The only things worth extracting from this route are:

1. `∂^+ F = upShadow(F) \ F`
2. complement / duality lemmas turning upper shadows into ordinary shadows
3. rank-layer API on `Finset (Finset (Fin n))`
4. exact computation of the boundary of the half-cube extremizer

Abort this route if it starts depending on a theorem of the form:

```text
half the cube => middle-layer pressure
```

without already having an extremal theorem. That is just Harper hidden under different language.

## Concrete Lean file split

Recommended file split:

1. `ErdosProblems/Problem1CubeBoundary.lean`
   - boundary definition on `Fin n`
   - compatibility with `upShadow`
   - basic complement lemmas

2. `ErdosProblems/Problem1CubeCompression.lean`
   - coordinate or UV compressions
   - card preservation
   - boundary monotonicity
   - reduction to down-sets

3. `ErdosProblems/Problem1CubeExtremal.lean`
   - initial segments in simplicial order
   - exact boundary computation at size `2^(n-1)`
   - down-set extremal theorem

4. `ErdosProblems/Problem1LowerExactCore.lean`
   - final bridge back to Erdos1

## Early feasibility checkpoints

Do these in order, and stop the program early if they fail badly.

Checkpoint 1:

```text
prove ∂^+ F = upShadow(F) \ F
```

Checkpoint 2:

```text
define compressions using existing mathlib conventions cleanly
```

Checkpoint 3:

```text
prove one-step boundary monotonicity under compression
```

Checkpoint 4:

```text
compute |∂^+ L| exactly for the half-cube initial segment L
```

If Checkpoint 3 stalls, the compression route is in genuine trouble.
If Checkpoint 4 stalls, the extremizer model is not encoded sharply enough.

## Success criterion

This program succeeds when the following chain is theorem-only:

```text
Harper-type half-cube boundary theorem
=> PositiveBoundaryMiddleLower
=> exact Dubroff-Fox-Xu integer lower bound
=> removal of the main integer literature axiom
```

In Lean terms:

1. remove `positiveBoundaryMiddleLower_frontier`
2. prove `PositiveBoundaryMiddleLower` from base axioms
3. replace `erdos_1_dubroff_fox_xu_lower_exact` by a theorem

## Short mathematical summary

The corrected view is:

```text
The blocker is an exact cube isoperimetric theorem.
It should be attacked as a Harper extremal problem, not as a shadow-aggregation problem.
```

That is the mathematically honest route to the exact Erdos1 lower bound.
