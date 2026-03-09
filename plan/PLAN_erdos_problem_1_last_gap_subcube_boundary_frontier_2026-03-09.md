# Plan: Erdos Problem #1 last gap - subtype half-cube boundary frontier

## Public target

The remaining public-facing exact theorem is the subtype-cube boundary statement used by the Erdos #1 route.

Current frontier:

- `ErdosProblems/Problem1CubeHalfLowerFrontier.lean`
  - `subcubeHalfCubeBoundaryLower_frontier`

Mathematical form:

$$
\binom{|A|}{\lfloor |A|/2 \rfloor}
\le
|\partial^+(\mathrm{negativeHalfFamilySubcubeNat}(A))|
$$

for every nonempty sum-distinct finite set `A`.

## Reduction already completed

The subtype problem is already transported to the Boolean cube on the subtype `A`.

Key transport layer:

- `ErdosProblems/Problem1CubeNatBridge.lean`
  - `negativeHalfFamilySubcubeNat`
  - `isDownSetFamily_negativeHalfFamilySubcubeNat`
  - `card_negativeHalfFamilySubcubeNat_eq_half_cube`
  - `image_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat`
  - `card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat`

So the subtype frontier reduces to the cube theorem:

$$
\mathcal D \subseteq 2^{[n]},\quad
\mathcal D \text{ down-set},\quad
|\mathcal D| = 2^{n-1}
\;\Longrightarrow\;
|\partial^+ \mathcal D| \ge \binom{n}{\lfloor n/2 \rfloor},
$$

with `n = |A| > 0`.

## Current exact cube-level frontier

The live frontier sits in

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

and is now correctly factored through two odd-dimensional inputs.

### Input A: odd half-cube boundary theorem

For every `m >= 0` and every down-set `D subseteq 2^[2m+1]`,

$$
|D| = 2^{2m}
\;\Longrightarrow\;
|\partial^+ D| \ge \binom{2m+1}{m}.
$$

### Input B: strict-excess odd-section optimization

For every `m >= 0` and `e > 0`, find a true lower profile `beta(m,e)` such that every down-set
`N subseteq 2^[2m+1]` with `|N| = 2^(2m) + e` satisfies

$$
beta(m,e) \le |\partial^+ N|
$$

and

$$
2\binom{2m+1}{m} \le beta(m,e) + 2e.
$$

### Proved reduction theorem

These two inputs are already enough in Lean via

- `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization`

Therefore the subtype frontier will close once Inputs A and B are proved and `halfCubeBoundaryLower` is instantiated from them.

## False routes now ruled out

The repository should not keep targeting the following discarded statements.

1. Weighted-drop half-cube lower theorem.
   - false
   - see `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
   - witness: `halfCubeProfileCounterexample`

2. Paired odd-section boundary theorem.
   - false
   - see `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - witness: `not_OddSectionPairBoundaryLowerStatement`

3. Any route claiming `minimalOutside` alone gives the sharp middle binomial lower bound.
   - false already in low dimension

## What is already proved and still useful

- `ErdosProblems/Problem1CubeBoundary.lean`
  - section decomposition formulas for `positiveBoundary`
- `ErdosProblems/Problem1CubeDownset.lean`
  - down-set reduction infrastructure and section inequalities
- `ErdosProblems/Problem1CubeOddExtremizer.lean`
  - sharp odd witnesses
- `ErdosProblems/Problem1CubeEvenExtremizer.lean`
  - sharp even witnesses and transport lemmas
- `ErdosProblems/Problem1CubeHalfBoundary.lean`
  - the current live reduction to Inputs A and B

## Remaining work

1. Prove `OddHalfCubeBoundaryLowerStatement`
2. Prove `OddSectionStrictExcessOptimizationStatement`
3. Replace the axiom `halfCubeBoundaryLower`
4. Reuse the existing transport lemmas to discharge `subcubeHalfCubeBoundaryLower_frontier`

## Separate implementation debt

The file

- `ErdosProblems/Problem1CubeEvenExtremizer.lean`

currently has build failures in the transport layer. That is a Lean maintenance issue and should not be confused with the mathematical frontier above.
