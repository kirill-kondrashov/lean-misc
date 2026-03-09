# Plan: proving `halfCubeBoundaryLower`

## Target

Replace the remaining axiom in

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

namely:

```text
halfCubeBoundaryLower

If 0 < |alpha|, D subseteq P(alpha), D is a nonempty down-set, and |D| = 2^(|alpha|-1),
then |positiveBoundary D| >= choose(|alpha|, floor(|alpha|/2)).
```

Equivalently, for `n >= 1`:

$$
\mathcal D \subseteq 2^{[n]},\quad
\mathcal D \text{ down-set},\quad
|\mathcal D| = 2^{n-1}
\;\Longrightarrow\;
|\partial^+ \mathcal D| \ge \binom{n}{\lfloor n/2 \rfloor}.
$$

This is the last mathematical gap on the exact Erdos #1 cube-boundary route.

## Current status

The current code no longer supports the older March 9 frontiers as live targets.

Discarded routes:

1. Pure weighted-drop profile inequality.
   - formalized false in `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
   - witness: `halfCubeProfileCounterexample`
   - negation: `not_HalfCubeWeightedDropLowerStatement`

2. Paired odd-section boundary inequality.
   - formalized false in `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - witness theorem: `not_OddSectionPairBoundaryLowerStatement`

So the active plan must avoid both of those statements.

## Live reduction already proved in Lean

The file `ErdosProblems/Problem1CubeHalfBoundary.lean` now packages the global theorem into two odd-dimensional inputs.

Active placeholders:

- `OddHalfCubeBoundaryLowerStatement`
- `OddSectionStrictExcessOptimizationStatement`

Active master reduction:

- `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization`

Mathematically, the proved reduction is:

If the following two statements hold, then the full half-cube theorem holds for every `n`.

### Input A: odd half-cube boundary theorem

For every `m >= 0` and every down-set `D subseteq 2^[2m+1]`,

$$
|D| = 2^{2m}
\;\Longrightarrow\;
|\partial^+ D| \ge \binom{2m+1}{m}.
$$

### Input B: strict-excess odd-section optimization

For every `m >= 0` and every `e > 0`, give a lower profile `beta(m,e)` such that for every down-set
`N subseteq 2^[2m+1]` with

$$
|N| = 2^{2m} + e,
$$

one has

$$
beta(m,e) \le |\partial^+ N|
$$

and

$$
2\binom{2m+1}{m} \le beta(m,e) + 2e.
$$

Once A and B are available, the file already derives:

$$
\mathcal D \subseteq 2^{[n]},\quad
\mathcal D \text{ down-set},\quad
|\mathcal D| = 2^{n-1}
\;\Longrightarrow\;
|\partial^+ \mathcal D| \ge \binom{n}{\lfloor n/2 \rfloor}.
$$

## Why this is the live route

The even-dimensional branch is now reduced correctly.

- Balanced section case: already routed to smaller half-cube problems.
- Strict deficit case: already routed to an odd-dimensional section with excess `e > 0`.
- Coordinate normalization issues: already removed by the arbitrary-pivot transport lemmas.
- Old paired-section route: explicitly false, so no longer admissible.

What remains is therefore genuinely odd-dimensional.

## Concrete proof program from here

### Phase 1: solve Input A

Prove `OddHalfCubeBoundaryLowerStatement`.

This is the symmetric half-mass case in odd dimension:

$$
|D| = 2^{2m}
$$

inside `2^[2m+1]`.

Possible productive subroutes:

1. show the odd extremizers are initial segments in the right Kruskal-Katona order and compute their boundary exactly
2. prove a direct odd-dimensional compression/extremizer theorem for down-sets of size `2^(2m)`
3. derive the bound from a sharp upper-shadow-gap inequality specialized to the balanced odd case

Acceptance criterion:

- a theorem proving `OddHalfCubeBoundaryLowerStatement`
- no appeal to the false weighted-drop or paired-boundary frontiers

### Phase 2: solve Input B

Prove `OddSectionStrictExcessOptimizationStatement`.

The problem is to convert strict excess above half-cube size in dimension `2m+1` into enough boundary gain so that

$$
|\partial^+ N| + 2e \ge 2\binom{2m+1}{m}.
$$

The key mathematical task is to choose or derive a true boundary lower profile `beta(m,e)`.

Likely routes:

1. prove a sharp lower bound for the minimal positive boundary among odd-cube down-sets of size `2^(2m)+e`
2. prove discrete convexity / monotonicity of the boundary profile around half-cube mass
3. derive a true nonlinear slice optimization strong enough to absorb the `+ 2e` term

Acceptance criterion:

- a theorem proving `OddSectionStrictExcessOptimizationStatement`
- exact compatibility with the already-proved even-dimensional reduction

### Phase 3: instantiate the global theorem

Once Inputs A and B are proved, replace the axiom `halfCubeBoundaryLower` by the theorem obtained from

- `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization`

Then discharge the subtype and arithmetic frontiers already wired through:

- `subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower`
- `positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower`

## Non-goals

These should not be pursued as active targets unless the route is redesigned again.

- `HalfCubeWeightedDropLowerStatement`
- `OddSectionPairBoundaryLowerStatement`
- any plan that claims `minimalOutside` alone has size at least `choose(n, floor(n/2))`

## Lean status outside the mathematics

There is a separate build failure in

- `ErdosProblems/Problem1CubeEvenExtremizer.lean`

This is transport/refactor debt, not the conceptual blocker for the proof plan above.

## Acceptance criteria for closing this plan

This plan is complete only when all of the following hold:

1. `OddHalfCubeBoundaryLowerStatement` is proved
2. `OddSectionStrictExcessOptimizationStatement` is proved
3. `halfCubeBoundaryLower` is proved without axioms
4. the public subtype frontier in `Problem1CubeHalfLowerFrontier.lean` is discharged from that theorem
