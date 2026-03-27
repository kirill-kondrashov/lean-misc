# Prism Theorem Progress - 2026-03-27

Validation gate:

- `make build`: pass
- `make check`: pass
- `scripts/verify_output.sh`: pass

Progress bar:

`[#########-] 9/10`

This is a heuristic program-progress bar for the current formal route, not a probability claim.

Completed program layers:

- prism packaging (`twoSheetFamily`, exact boundary decomposition)
- even minimizer existence/compression infrastructure
- middle-transition-window normalization
- even witness `totalSize` reduction machinery
- balanced-zero-section witness-collapse machinery
- current leaf frontier bundled into `PrismTheoremCurrentLeafFrontierStatement`
- direct prism-boundary-side extraction from the current leaf frontier to the first strict prism slice
- combined prism-boundary-side strict-excess packaging for the exterior-support leaves
- support-silent middle-window branch packaged directly to the lower/upper strict prism-boundary slices
- downstream even-minimizer and middle-window consequences rerouted through those strict prism-boundary slices
- current six-leaf frontier repackaged into a five-leaf strict prism-boundary bundle for the downstream consequence chain
- strict prism-boundary bundle further collapsed into a two-leaf even-consequence frontier
- theorem-level boundary-lower and equivalence wrappers collapsed from the two-leaf even-consequence frontier to a one-leaf upper-shadow-gap boundary frontier
- theorem-level upper-shadow-gap route detached from the even-consequence bundle and factored through a one-leaf odd-size source frontier
- odd local pair-interface boundary-lower bottleneck localized to the equivalent first-separation and first-positive-gap statements
- canonical bottleneck package added:
  `PrismTheoremCanonicalPairInterfaceBoundaryLowerBottleneckStatement`
- direct closures from the canonical bottleneck to:
  `OddSectionPairInterfaceBoundaryLowerStatement`
  `TwoSheetBoundaryTheorem`
  `PrismHalfCubeBoundaryLowerStatement`
  `HalfCubeBoundaryLowerStatement`
  `HalfCubeUpperShadowGapLowerStatement`
- arithmetic corollaries extended from the canonical bottleneck to the subcube and
  `positiveBoundaryFamilyNat` consequences

Current bottleneck:

- `PrismTheoremCanonicalPairInterfaceBoundaryDefectBottleneckStatement`

Equivalent local formulations:

- `OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerTotalSizeThanEvenWitnessStatement`
- `OddSectionFirstSeparationPairInterfaceBoundaryDefectForcesLargerTotalSizeThanEvenWitnessStatement`
- `OddSectionPositiveExcessPairInterfaceBoundaryDefectForcesLargerTotalSizeThanEvenWitnessStatement`

These are no longer separate proof goals in the theorem graph; they are equivalent reformulations of
the same remaining local odd defect-to-`totalSize` bridge.

Current plan:

1. Add a targeted `n = 7` first-positive-gap defect search mode for the simple-lower model
   `𝒩 = lower_half ∪ upper_part`, `ℳ = lower_half \ rank3_removed`, with exact reporting of:
   the upper-rank slice profile, the weighted upper-tail gain
   `u₅ + 2 u₆ + 3 u₇ = totalSize(twoSheetFamily ℳ 𝒩) - totalSize(evenLowerHalfFamily 3)`,
   and the best pair-interface boundary margin above/below the target `2 * choose(7, 3) = 70`.
2. Use that data to isolate the zero-margin regime (`u₅ = u₆ = u₇ = 0`, i.e. pure rank-4 upper
   tails) and formulate the missing intermediate lemma:
   first-positive-gap pair-interface defect forces positive weighted upper-tail gain.
3. Prove that intermediate lemma in Lean, first in the first-positive-gap form, then via the
   existing equivalence layer for the canonical defect bottleneck.
4. Plug that theorem into the existing closure graph; the current file already propagates it to the
   two-sheet theorem, prism theorem, half-cube boundary theorem, half-cube upper-shadow-gap
   theorem, and the downstream arithmetic corollaries.

Interpretation:

The remaining work is no longer packaging. The theorem graph is already in place. The real missing
piece is a new local combinatorial proof about the first positive gap slice of `𝒩 \ ℳ`, and the
current search plan is to identify that proof through the weighted upper-tail invariant in the
structured `n = 7` model before formalizing it abstractly.

Latest step:

Added a targeted exact `n = 7` simple-lower first-gap defect search mode in
`tools/problem1_odd_profile_search.py` and ran it on the single/pair generator orbit classes with
upper part size at most `12`. No searched class produced a defect candidate. The tightest exact
zero-gain class was `single-4`, with upper profile `[1, 0, 0, 0]` and minimum pair-interface
boundary `73 > 70`; the other exact pure rank-4 classes had margins `5` and `6`.

Working intermediate-lemma candidate:

- in the first-positive-gap simple-lower model, pure rank-4 upper tails cannot produce a
  pair-interface boundary defect;
- equivalently, any first-positive-gap defect forces positive weighted upper-tail gain
  `u₅ + 2 u₆ + 3 u₇ > 0`.

This does not prove the canonical defect bottleneck yet, but it gives a concrete local proof target:
rule out the zero-gain regime abstractly, then convert positive weighted upper-tail gain into the
desired `totalSize` inequality.

The Lean file now also has the exact prism-form target
`OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerPrismThanEvenWitnessStatement`,
proved equivalent to the canonical defect bottleneck and wired directly to the exact Erdős #1
endpoint under the current leaf frontier. So the remaining missing step is now explicitly
"defect => larger prism" in the same language used by both the search tooling and the existing leaf
strict-boundary route.

The zero-gain contradiction surface is now explicit as well:
`OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossibleStatement`.
It is proved equivalent to the larger-prism surface and wired directly to the exact Erdős #1
endpoint. So the remaining local target can now be attacked either as a positivity statement
(`defect => larger prism`) or as the contradiction form promised by the current plan
(`defect` plus `prism <= witness` is impossible).

The simple-lower intermediate target is now explicit in Lean too:
`SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`.
It is proved equivalent to the simple-lower larger-prism surface
`SimpleLowerPairInterfaceBoundaryDefectForcesLargerPrismThanEvenWitnessStatement`,
the uniform-upper contradiction surface
`SimpleLowerPairInterfaceBoundaryDefectWithUniformUpperImpossibleStatement`,
and the no-larger-prism contradiction surface
`SimpleLowerPairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossibleStatement`.

So the remaining work is sharper again: bridge the current first-positive-gap defect bottleneck to
that simple-lower upper-tail statement, then the larger-prism contradiction is already formalized.

The final route is now split into two explicit theorem inputs:

- `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerStatement`
- `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`

The Lean files now show directly that those two inputs close the canonical defect bottleneck and
therefore the exact Erdős #1 endpoint under `PrismTheoremCurrentLeafFrontierStatement`.

Latest normalization-side sharpening:

- the simple-lower no-larger-prism condition is now explicitly equivalent to the uniform-upper
  condition `∀ s ∈ 𝒰, s.card = m + 1`;
- correspondingly, Lean now has the stronger normalization surface
  `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerUniformUpperStatement`,
  and shows that this stronger form already implies the original normalization statement, the
  canonical defect bottleneck, the half-cube boundary / upper-shadow-gap consequences, and the
  exact Erdős #1 endpoint under the current leaf frontier.

So the `totalSize` transport inequality is no longer the right target in raw form. The remaining
normalization burden is sharper:

- transfer the boundary defect to a simple-lower pair,
- and normalize the upper part entirely into the middle layer.
