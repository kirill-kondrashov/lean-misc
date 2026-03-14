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

The frontier sits in

- `ErdosProblems/Problem1CubeHalfBoundary.lean`

but the earlier odd excess input has now been ruled out.

### Still-plausible theorem target: odd half-cube boundary theorem

For every `m >= 0` and every down-set `D subseteq 2^[2m+1]`,

$$
|D| = 2^{2m}
\;\Longrightarrow\;
|\partial^+ D| \ge \binom{2m+1}{m}.
$$

This statement survived exhaustive search in odd dimensions `1`, `3`, and `5`.

### False odd-section routes now ruled out

1. Weighted-drop half-cube lower theorem.
   - false
   - see `ErdosProblems/Problem1CubeHalfBoundarySequence.lean`
   - witness: `halfCubeProfileCounterexample`

2. Paired odd-section boundary theorem.
   - false
   - see `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - witness: `not_OddSectionPairBoundaryLowerStatement`

3. Strong one-family odd excess theorem.
   - false
   - see `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - witness: `not_OddSectionExcessBoundaryLowerStatement`

4. Direct / optimized `+ 2e` odd excess frontier.
   - false
   - explicit witness: `N = {∅, {0}, {1}, {2}, {1,2}}` in `2^[3]`
   - in particular, this kills `OddSectionDirectStrictExcessStatement` and
     `OddSectionStrictExcessOptimizationStatement`

5. Any route claiming `minimalOutside` alone gives the sharp middle binomial lower bound.
   - false already in low dimension

### Revised exact cube-level program

The revised program is:

1. Prove `OddHalfCubeBoundaryLowerStatement`.
2. Determine the correct odd excess profile above half-cube mass. This is now a formulation
   problem, not a fixed theorem target.
3. Rebuild the even-dimensional closure from that corrected excess theorem.

Current pair-interface status:

- empirical support through exhaustive search in odd dimensions `1`, `3`, and `5`
- in the same searched dimensions, every half-cube boundary minimizer found by exhaustive search
  has the exact `oddLowerHalfFamily` slice profile
- Lean now exposes a weaker split frontier:
  - `OddHalfCubeBoundaryLowerStatement`
  - `OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement`
- the old all-`e` pair-interface statement is equivalent to that split; the forward/backward bridge
  is now explicit via
  `oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeBoundaryLower_and_positiveExcessPairInterfaceBoundaryLower`
  and
  `oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
  and, on the canonical odd upper-shadow-gap surface, via
  `oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeUpperShadowGapLower_and_positiveExcessPairInterfaceBoundaryLower`
- the split already closes the public frontier conditionally through:
  - `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `halfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `halfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `halfCubeUpperShadowGapLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `subcubeHalfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
  - `positiveBoundaryFamilyNat_lower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`

A natural object is

$$
b_{2m+1}(2^{2m}+e)
:=
\min\{\,|\partial^+ N| : N \subseteq 2^{[2m+1]} \text{ down-set},\ |N| = 2^{2m}+e\,\}.
$$

The replacement theorem must match the explicit small-dimensional data and still be strong enough
to close the already-developed even recursion.

The current Phase 1 signal is therefore sharper than the earlier slice-minimum heuristic:
odd extremizer classification remains a useful structural target, but by feasibility it should not
block the direct proof of `OddHalfCubeBoundaryLowerStatement`.

Current feasibility ranking:

1. most feasible: prove `OddHalfCubeBoundaryLowerStatement` directly from the actual odd down-set
   slice / upper-shadow-gap inequalities
   - the odd upper-shadow-gap surface is now packaged explicitly in Lean as
     `OddHalfCubeUpperShadowGapLowerStatement`, equivalent to the odd boundary statement
   - the weaker search-guided slice target is now explicit in Lean as
     `OddHalfCubeSliceThresholdStatement`
   - that slice target now already yields a proved partial-sum consequence toward the boundary
     functional:
     `sum_Icc_choose_even_le_card_positiveBoundary_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - the same partial-sum consequence is also packaged on the canonical odd upper-shadow-gap
     surface:
     `sum_Icc_choose_even_le_upperShadowGap_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - the left-hand side of that partial sum is now evaluated exactly in Lean by
     `two_mul_sum_Icc_choose_even`, yielding the doubled explicit obstruction
     `two_pow_add_choose_middle_even_sub_two_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - that obstruction is now also repackaged against the `1`-slice and upper tail:
     `choose_middle_even_add_two_mul_card_slice_one_add_two_mul_sum_card_slice_succ_upper_tail_le_two_mul_upperShadowGap_add_two_pow_of_oddHalfCubeSliceThreshold`
   - a naive tail-subtraction closure of that theorem is too weak already in small odd dimension,
     so the missing step is now explicitly a stronger structural control on the `1`-slice plus
     upper tail, not just another algebraic rewrite
   - there is now a second exact-shadow closure route in Lean:
     `odd_initial_slices_full_of_lower_boundary_slices_vanish`,
     `choose_middle_le_card_positiveBoundary_of_lower_boundary_slices_vanish`, and
     `choose_middle_le_upperShadowGap_of_lower_boundary_slices_vanish`
   - the old wording “for the relevant sharp odd candidates” was too close to an equality-case
     theorem in disguise
   - the live route is now refactored through actual boundary minimizers:
     `IsOddHalfCubeBoundaryGlobalMinimizer`,
     `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement`, and
     `exists_isOddHalfCubeBoundaryGlobalMinimizer`
   - the new bridge
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySlicesVanish`
     shows it is enough to prove lower-boundary-slice vanishing only for genuine global minimizers
     of the odd half-cube boundary functional
   - that route now already recovers the searched extremizer shape locally: a global minimizer with
     vanishing lower boundary slices is forced to equal `oddLowerHalfFamily`, with
     `positiveBoundary = minimalOutside = oddMiddleLayer`
   - there is now also a weaker global-minimizer route through `minimalOutside` alone:
     `OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement`
   - the new bridge
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower`
     shows that proving a middle-binomial lower bound for `minimalOutside` on global minimizers
     would already close the odd theorem, without first proving slice vanishing
   - this weaker route is now refactored through an antichain upper-closure problem:
     `OddAntichainUpperClosureLowerStatement`
   - the new bridge
     `oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_antichainUpperClosureLower`
     sends that antichain statement back to the global-minimizer route via
     `minimalOutside` and `upperClosure_minimalOutside_eq_compl`
   - this is now sharpened to an exact reformulation through the universal half-cube statement
     `OddHalfCubeMinimalOutsideLowerStatement`
   - the new equivalence
     `oddAntichainUpperClosureLower_iff_oddHalfCubeMinimalOutsideLower`
     removes the need to talk about minimizers at the theorem surface: the antichain problem is
     exactly the same as lower-bounding `minimalOutside` for every odd half-cube down-set
   - the direct odd closures now sit on that stronger surface:
     `oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower` and
     `oddHalfCubeBoundaryLower_of_minimalOutsideLower`
   - the odd witness on that surface is now explicit:
     `oddMiddleLayer_realizes_oddAntichainUpperClosureLowerTarget`
   - so the live fallback is now a true reformulation rather than more disguised equality-case
     work on minimizers
   - this weaker route now also forces the first equality case automatically on any such minimizer:
     sharp boundary equality and `minimalOutside = positiveBoundary`
   - update on 2026-03-13: this universal `minimalOutside` / antichain route is false
   - Lean now contains the explicit half-cube counterexample in dimension `3`:
     `oddHalfCubeMinimalOutsideCounterexample = (Finset.univ.erase 0).powerset`
   - it has `|D| = 4 = 2^(2*1)` but `minimalOutside D = {{0}}`, so
     `#minimalOutside D = 1 < choose(3,1) = 3`
   - the formal negations are now present as
     `not_OddHalfCubeMinimalOutsideLowerStatement` and
     `not_OddAntichainUpperClosureLowerStatement`
   - therefore this route is now archival only; the live frontier returns to the direct odd
     upper-shadow-gap route and the minimizer-only salvage routes
2. secondary: use the new minimizer packaging to pursue equality-case classification only if the
   lower-bound proof begins to force sharpness slice-by-slice
   - exact-profile closure now already gives the full sharp boundary shape of any such minimizer:
     `positiveBoundary 𝒟 = minimalOutside 𝒟 = oddMiddleLayer m`
  - there is now a weaker minimizer-side structural statement on the table:
    `OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement`
  - the canonical witness `oddLowerHalfFamily` already realizes that weaker target directly via
    `oddLowerHalfFamily_realizes_oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishTarget`
   - that weaker statement is now equivalent to full exact profile on sharp odd minimizers, via
     `oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanish_of_exactProfile`,
     `oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish`, and
     `oddHalfCubeBoundaryMinimizerExactProfileStatement_iff_lowerBoundarySlicesVanishStatement`
  - it also now exposes the same practical sharp-minimizer outputs directly:
    `eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    and `oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`
3. least feasible: revive the false weighted-drop route or restart a full compression/Harper
   development

Current live odd frontier after the counterexample:

1. direct odd theorem surface:
   `OddHalfCubeUpperShadowGapLowerStatement`
   - the current explicit direct subtarget is now
     `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement`
   - this is the formal version of the intended contradiction:
     if a genuine global minimizer has any nonzero lower positive-boundary slice, then its
     `upperShadowGap` must already be strictly larger than `choose(2m+1,m)`
   - Lean now proves that this strict-gap target would close the odd theorem
2. minimizer-only salvage:
   `OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement` or
   `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement`
   - a corrected minimizer-only antichain reformulation is now available:
     `OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement`
   - this is equivalent to the minimizer-only `minimalOutside` lower bound, but unlike the dead
     universal route it only speaks about genuine global minimizers
   - it is already implied by the stronger lower-boundary-slice-vanishing route
3. archival false frontier:
   `OddHalfCubeMinimalOutsideLowerStatement` and
   `OddAntichainUpperClosureLowerStatement`

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
  - the odd/even reduction skeleton, balanced recursion, and archival false-route counterexamples

## Remaining work

1. Prove `OddHalfCubeBoundaryLowerStatement`
2. Identify and prove a corrected odd excess theorem
3. Rebuild the final cube closure from those true inputs
4. Replace the axiom `halfCubeBoundaryLower`
5. Reuse the existing transport lemmas to discharge `subcubeHalfCubeBoundaryLower_frontier`

## Separate implementation debt

`make build` currently passes. The blocker is the mathematical frontier above, not transport debt.
