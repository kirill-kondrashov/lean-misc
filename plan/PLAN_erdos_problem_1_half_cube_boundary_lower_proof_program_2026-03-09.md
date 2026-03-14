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

The upper-shadow-gap surface is now formalized as an exact reformulation of this same gap:

- `halfCubeUpperShadowGapLower_of_halfCubeBoundaryLower`
- `halfCubeBoundaryLower_of_halfCubeUpperShadowGapLower`
- `halfCubeBoundaryLower_iff_halfCubeUpperShadowGapLower`

So upper-shadow-gap arguments are now interchangeable with direct positive-boundary arguments,
not a separate frontier assumption.

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

3. Strong one-family odd excess frontier.
   - formalized false in `ErdosProblems/Problem1CubeHalfBoundary.lean`
   - witness theorem: `not_OddSectionExcessBoundaryLowerStatement`

4. Direct / optimized `+ 2e` strict-excess odd frontier.
   - mathematically false
   - explicit witness: `N = {∅, {0}, {1}, {2}, {1,2}}` in `2^[3]`
   - this kills both `OddSectionDirectStrictExcessStatement` and
     `OddSectionStrictExcessOptimizationStatement`

So the active plan must avoid all of those statements.

## What remains plausible

The only currently plausible named theorem target is:

- `OddHalfCubeBoundaryLowerStatement`

It survived exhaustive search in odd dimensions `1`, `3`, and `5`.

The balanced even-dimensional recursion and section transport work already done in
`ErdosProblems/Problem1CubeHalfBoundary.lean` still matter, but the specific odd excess input they
were wired to is not a viable frontier anymore.

## Feasibility assessment

The current routes are not equally promising.

Most feasible next theorem:

- prove `OddHalfCubeBoundaryLowerStatement` directly

This is weaker than full extremizer classification and is the only theorem actually needed to move
the global proof program forward.

Moderately feasible supporting route:

- derive the odd half-cube lower bound from actual down-set slice / upper-shadow-gap inequalities in
  odd dimension
  - Lean surface now packaged as
    `OddHalfCubeUpperShadowGapLowerStatement` and
    `oddHalfCubeBoundaryLower_iff_oddHalfCubeUpperShadowGapLower`
  - the conditional global closure is now also exposed on that same surface via
    `halfCubeUpperShadowGapLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`

Useful but likely harder than the lower bound itself:

- prove `OddHalfCubeBoundaryMinimizerExactProfileStatement`

That is now well-packaged in Lean and would immediately identify sharp minimizers with
`oddLowerHalfFamily`, but it is an equality-case theorem and therefore should be treated as a
secondary target unless the proof starts yielding equality information naturally.

Low-feasibility parked routes:

- any unrestricted sequence LP / weighted-drop theorem
- a full compression / Harper redevelopment

## Revised research program

The revised program has three stages.

### Phase 1: prove the odd half-cube theorem

Prove `OddHalfCubeBoundaryLowerStatement`.

For every `m >= 0` and every down-set `D subseteq 2^[2m+1]`,

$$
|D| = 2^{2m}
\;\Longrightarrow\;
|\partial^+ D| \ge \binom{2m+1}{m}.
$$

Possible productive subroutes:

1. derive the bound directly from actual down-set slice or upper-shadow-gap inequalities in the
   balanced odd case
2. prove the weaker slice-threshold statement that looks compatible with the current low-dimensional
   data, if it is strong enough to close the boundary lower bound
   - Lean target surface now added: `OddHalfCubeSliceThresholdStatement`
   - witness packaging already added:
     `oddLowerHalfFamily_realizes_oddHalfCubeSliceThresholdTarget`
   - this route now has a first proved output in Lean:
     `sum_Icc_choose_even_le_card_positiveBoundary_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - the same partial-sum consequence is now also exposed on the canonical odd theorem surface:
     `sum_Icc_choose_even_le_upperShadowGap_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - the left-hand binomial obstruction is now also evaluated exactly in Lean via
     `two_mul_sum_Icc_choose_even`, giving the doubled canonical reformulation
     `two_pow_add_choose_middle_even_sub_two_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
   - that doubled obstruction is now further rewritten against the `1`-slice plus upper tail:
     `choose_middle_even_add_two_mul_card_slice_one_add_two_mul_sum_card_slice_succ_upper_tail_le_two_mul_upperShadowGap_add_two_pow_of_oddHalfCubeSliceThreshold`
   - so the remaining direct-route gap is now explicit: prove a structural estimate on
     `#(𝒟 # 1) + ∑_{r=m+1}^{2m} #(𝒟 # (r+1))` strong enough to close against `2^(2m)`
   - a new exact-shadow conditional closure is now proved in Lean:
     `odd_initial_slices_full_of_lower_boundary_slices_vanish`,
     `choose_middle_le_card_positiveBoundary_of_lower_boundary_slices_vanish`, and
     `choose_middle_le_upperShadowGap_of_lower_boundary_slices_vanish`
   - this exposes a sharper structural subtarget than the tail arithmetic alone, but the earlier
     phrasing “under the right optimality hypothesis” was too vague and drifted back toward an
     equality-case theorem in disguise
   - the route is now refactored through actual boundary minimizers:
     `IsOddHalfCubeBoundaryGlobalMinimizer`,
     `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement`, and
     `exists_isOddHalfCubeBoundaryGlobalMinimizer`
   - the direct contradiction target is now also formalized explicitly in Lean:
     `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement`
   - it captures the intended next step exactly:
     global minimizer + one nonzero lower boundary slice
     `=> upperShadowGap > choose(2m+1,m)`
   - Lean now proves that this strict-gap statement would already imply the vanishing route and
     therefore the odd theorem:
     `oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_lowerBoundarySliceForcesStrictUpperShadowGap`,
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap`,
     and
     `oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap`
   - the new closure theorem
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySlicesVanish`
     shows it is enough to prove lower-boundary-slice vanishing only for genuine global minimizers
     of the odd half-cube boundary functional
   - this route now already recovers the expected sharp extremizer shape locally: from a single
     global minimizer plus local vanishing, Lean derives exact slice profile, then
     `𝒟 = oddLowerHalfFamily m`,
     `positiveBoundary 𝒟 = oddMiddleLayer m`, and
     `minimalOutside 𝒟 = oddMiddleLayer m`
   - there is now an even weaker minimizer-only alternative target:
     `OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement`
   - the new closure theorem
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower`
     shows that it would already suffice to lower-bound `minimalOutside` on global minimizers; this
     avoids proving slice vanishing first and uses only
     `minimalOutside ⊆ positiveBoundary` plus the global minimizing property
   - this weaker route is now factored through a genuinely different antichain surface:
     `OddAntichainUpperClosureLowerStatement`
   - the new bridge
     `oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_antichainUpperClosureLower`
     reduces the global-minimizer `minimalOutside` lower bound to an antichain theorem, using only
     `isAntichain_minimalOutside` and
     `upperClosure_minimalOutside_eq_compl`
   - this has now been sharpened to a universal half-cube route:
     `OddHalfCubeMinimalOutsideLowerStatement`
   - the new equivalence
     `oddAntichainUpperClosureLower_iff_oddHalfCubeMinimalOutsideLower`
     shows that the antichain upper-closure problem is exactly the same as proving a
     middle-binomial lower bound for `minimalOutside` on every odd half-cube down-set, not just on
     minimizers
   - consequently the odd theorem now has a direct closure from that universal surface:
     `oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower` and
     `oddHalfCubeBoundaryLower_of_minimalOutsideLower`
   - the canonical odd witness is now packaged on that surface too:
     `oddMiddleLayer_realizes_oddAntichainUpperClosureLowerTarget`
   - so the clean fallback is no longer “prove vanishing on minimizers”, but:
     prove that an antichain in `2^[2m+1]` with upper closure of size `2^(2m)` has cardinality at
     least `choose (2m+1) m`
   - this weaker route is now sharper in Lean than before: on a global minimizer, a
     `minimalOutside` lower bound already forces sharp boundary equality and
     `minimalOutside 𝒟 = positiveBoundary 𝒟`, via
     `isOddHalfCubeBoundaryMinimizer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower`
     and
     `minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower`
   - the current vanishing route now implies that weaker `minimalOutside` route through
     `oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerLowerBoundarySlicesVanish`
   - this avoids the previous dead-end formulation where vanishing was implicitly being asked either
     for arbitrary half-cube down-sets or for already-sharp minimizers
   - update on 2026-03-13: the stronger universal route through
     `OddHalfCubeMinimalOutsideLowerStatement` is false
   - Lean now contains the explicit dimension-3 counterexample
     `oddHalfCubeMinimalOutsideCounterexample = (Finset.univ.erase 0).powerset`,
     together with
     `not_OddHalfCubeMinimalOutsideLowerStatement`
   - concretely, in `2^[3]` this down-set has half-cube mass `4 = 2^(2*1)` but
     `minimalOutside = {{0}}`, so `#minimalOutside = 1 < choose(3,1) = 3`
   - by the already-proved implication
     `oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower`,
     the antichain reformulation is false as well:
     `not_OddAntichainUpperClosureLowerStatement`
   - therefore the universal `minimalOutside` / antichain upper-closure surface is now archival
     only; the live Step 1 targets are again the direct odd upper-shadow-gap route and the
     minimizer-only routes
3. treat extremizer classification via `OddHalfCubeBoundaryMinimizerExactProfileStatement` as an
   equality-case upgrade, not the default next theorem
   - exact-profile closure is now sharper in Lean: if a sharp odd minimizer satisfies the target,
     then `𝒟 = oddLowerHalfFamily m` and
     `positiveBoundary 𝒟 = minimalOutside 𝒟 = oddMiddleLayer m`
  - a new weaker minimizer-side target is now named:
    `OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement`
  - the canonical witness `oddLowerHalfFamily` now realizes that weaker target directly via
    `oddLowerHalfFamily_realizes_oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishTarget`
   - this weaker target is now actually equivalent to exact profile on sharp odd minimizers:
     `oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanish_of_exactProfile`,
     `oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish`, and
     `oddHalfCubeBoundaryMinimizerExactProfileStatement_iff_lowerBoundarySlicesVanishStatement`
  - the weaker target now also inherits the main sharp-minimizer consequences directly in Lean:
    `eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    `minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`,
    and `oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish`
4. only return to a larger compression/extremizer development if the direct odd lower-bound route
   stalls

Current Phase 1 target after the counterexample:

1. primary: return to the direct odd theorem surface
   `OddHalfCubeUpperShadowGapLowerStatement`
2. secondary: salvage a minimizer-only theorem such as
   `OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement` or
   `OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement`
   - a corrected minimizer-only antichain surface is now explicit in Lean:
     `OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement`
   - this avoids the false universal antichain theorem by quantifying only over genuine global
     minimizers
   - it is now equivalent to the minimizer-only `minimalOutside` route:
     `oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_iff_globalMinimizerMinimalOutsideLower`
   - it is also downstream of the stronger slice-vanishing route:
     `oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerLowerBoundarySlicesVanish`
   - and it already closes the odd theorem through
     `oddHalfCubeUpperShadowGapLower_of_globalMinimizerPositiveBoundaryAntichain`
3. archival only: `OddHalfCubeMinimalOutsideLowerStatement` and
   `OddAntichainUpperClosureLowerStatement`

Acceptance criterion:

- a theorem proving `OddHalfCubeBoundaryLowerStatement`
- no appeal to the false weighted-drop, paired-boundary, or `+ 2e` odd-section frontiers

### Phase 2: identify the correct odd excess frontier

This is no longer a theorem-proving phase against a fixed statement. It is a formulation phase.

Define the odd excess boundary profile

$$
b_{2m+1}(2^{2m}+e)
:=
\min\{\,|\partial^+ N| : N \subseteq 2^{[2m+1]} \text{ down-set},\ |N| = 2^{2m}+e\,\}.
$$

The immediate task is to determine a true lower bound for this profile near half-cube mass.
Whatever replaces the false `+ 2e` bound must:

1. survive exhaustive search at least through `n = 5`
2. be compatible with the explicit `n = 3` counterexample
3. be strong enough to feed the already-built even-dimensional recursion

Current reproducible search data for `n = 1, 3, 5` now lives in:

- [NOTES_problem1_odd_excess_profile_search_2026-03-11.md](NOTES_problem1_odd_excess_profile_search_2026-03-11.md)
- `tools/problem1_odd_profile_search.py`

Current plausible interface split:

- `OddHalfCubeBoundaryLowerStatement`
- `OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement`

The old all-`e` pair-interface statement is now equivalent to this split:

- `oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeBoundaryLower_and_positiveExcessPairInterfaceBoundaryLower`
- `oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
- `oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeUpperShadowGapLower_and_positiveExcessPairInterfaceBoundaryLower`

This split now has:

1. no counterexample in the current exhaustive search through `n = 5` for the positive-excess
   pair-interface branch
2. a packaged all-`n` conditional closure theorem already in Lean:
   `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
   and its upper-shadow-gap counterpart
   `choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
3. transport bridges from those `Fin n` theorems to the general theorem surface and public frontier:
   - `halfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
   - `halfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
   - `halfCubeUpperShadowGapLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower`
   - `subcubeHalfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
   - `positiveBoundaryFamilyNat_lower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower`
4. a new empirical odd-half-cube slice signal in `n = 1, 3, 5`:
   the minimum half-cube slice vector matches the truncated even-binomial profile
   `choose(2m, r)` for `0 <= r <= m` and `0` above it
5. a stronger extremizer signal in the same searched dimensions:
   among half-cube down-sets with minimum positive boundary, the slice profile is exactly the
   `oddLowerHalfFamily` profile `choose(2m + 1, r)` for `0 <= r <= m` and `0` above it
   - Lean target surface added: `OddHalfCubeBoundaryMinimizerExactProfileStatement`
   - minimizer predicate and witness packaging added:
     `IsOddHalfCubeBoundaryMinimizer`,
     `oddHalfCubeBoundaryMinimizerExactProfileStatement_iff`,
     `oddLowerHalfFamily_isOddHalfCubeBoundaryMinimizer`,
     `oddLowerHalfFamily_realizes_oddHalfCubeBoundaryMinimizerExactProfileTarget`
   - exact slice profile now collapses to literal extremizer equality via
     `eq_oddLowerHalfFamily_of_exact_slice_profile` and
     `eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile`
   - exact-profile minimizers now also satisfy the weaker searched threshold via
     `oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile`
   - sharp witness profile now formalized in `Problem1CubeOddExtremizer.lean` via
     `oddLowerHalfFamily_has_exact_slice_profile`

Current threshold-route status:

- the slice-threshold candidate is now explicit in Lean and witnessed by `oddLowerHalfFamily`
- it already yields a proved partial-sum boundary consequence via
  `sum_Icc_choose_even_le_card_positiveBoundary_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
- that consequence is also packaged directly on the upper-shadow-gap surface via
  `sum_Icc_choose_even_le_upperShadowGap_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold`
- a naive tail-subtraction closure on top of this partial-sum theorem is too weak already in small
  odd dimension, so the remaining gap is not just a one-line tail estimate

Likely routes:

1. prove an odd extremizer classification at half-cube mass, showing the sharp boundary minimizers
   are exactly the odd lower-half families (or at least have that full lower-half slice profile)
2. prove the weaker odd half-cube slice-threshold candidate suggested by search:
   `|(D # r)| >= choose(2m, r)` for `0 <= r <= m`
3. classify extremizers for small `e`, starting from `oddLowerHalfFamily` plus extra middle-layer sets
4. prove a sharp lower bound for the minimal positive boundary among odd-cube down-sets of size `2^(2m)+e`
5. derive a corrected section inequality with dimension-dependent or profile-dependent excess term

Acceptance criterion:

- a replacement odd excess theorem that is both plausible and empirically validated in low dimension
- a clear Lean interface replacing the false `OddSectionStrictExcessOptimizationStatement`,
  ideally in the split form above so the odd balanced case is isolated from the strict
  positive-excess recursion

### Phase 3: reconnect the global theorem

Once Phase 1 and the corrected excess theorem from Phase 2 are available:

1. replace the archival reduction through `OddSectionStrictExcessOptimizationStatement`
2. prove a new final closure theorem in `Problem1CubeHalfBoundary.lean`
3. replace the axiom `halfCubeBoundaryLower`
4. discharge the subtype and arithmetic frontiers already wired through
   `subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower` and
   `positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower`

## Non-goals

These should not be pursued as active targets unless the route is redesigned again.

- `HalfCubeWeightedDropLowerStatement`
- `OddSectionPairBoundaryLowerStatement`
- `OddSectionExcessBoundaryLowerStatement`
- `OddSectionDirectStrictExcessStatement`
- `OddSectionStrictExcessOptimizationStatement`
- `OddHalfCubeMinimalOutsideLowerStatement`
- `OddAntichainUpperClosureLowerStatement`
- any plan that claims `minimalOutside` alone has size at least `choose(n, floor(n/2))`

## Lean status outside the mathematics

`make build` currently passes. The blocker is mathematical, not build plumbing.

## Acceptance criteria for closing this plan

This plan is complete only when all of the following hold:

1. `OddHalfCubeBoundaryLowerStatement` is proved
2. a corrected odd excess theorem has been identified and proved
3. the final half-cube closure theorem has been rebuilt from those true inputs
4. `halfCubeBoundaryLower` is proved without axioms
5. the public subtype frontier in `Problem1CubeHalfLowerFrontier.lean` is discharged from that theorem
