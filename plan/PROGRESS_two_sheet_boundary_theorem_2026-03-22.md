# Prism Theorem Progress - 2026-03-28

Validation gate:

- `make build`: pass
- `make check`: pass
- `scripts/verify_output.sh`: pass

Progress bar:

`[#########>] 9.5/10`

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

- `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

Equivalent theorem surfaces already in Lean:

- `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`
- `SimpleLowerPairInterfaceBoundaryDefectWithUniformUpperImpossibleStatement`
- `SimpleLowerPairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossibleStatement`

Current reduced mathematical blocker:

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\]

where \(U \subseteq \binom{[2m+1]}{m+1}\), \(V \subseteq \binom{[2m+1]}{m}\), and \(T(V)\) is the
family of \((m+1)\)-sets whose full \(m\)-shadow lies in \(V\).

Current plan:

1. Prove the uniform-upper pair-interface lower bound directly in the simple-lower model:
   \[
   |\partial^+(L_m \cup U)| + |(U \cup V)\cup \partial^+(L_m \setminus V)|
   \ge
   2\binom{2m+1}{m}.
   \]
2. Attack it as a middle-layer compression/isoperimetric problem on the balanced graph
   \[
   \binom{[2m+1]}{m} \leftrightarrow \binom{[2m+1]}{m+1}.
   \]
3. Once that statement is proved, use the already-formalized equivalence layer to recover
   `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`.
4. Then the proved normalization theorem plus the existing closure graph finish the canonical
   defect bottleneck, the prism theorem, and the exact Erdős #1 endpoint under the current leaf
   frontier.

Interpretation:

The remaining work is no longer packaging. The theorem graph is in place, and the general odd
first-gap problem has already been normalized to the simple-lower uniform-upper regime. The actual
missing piece is now one middle-layer compression/isoperimetric lemma.

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

Update on 2026-03-27:

- `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerUniformUpperStatement`
  is now fully proved in Lean at
  [Problem1CubeHalfBoundary.lean:8065](/home/kir/pers/erdos/lean-misc/ErdosProblems/Problem1CubeHalfBoundary.lean:8065).
- The proof does not use a separate shifted-compression lemma. Instead it works directly with
  `𝒟 := twoSheetFamily ℳ 𝒩`, proves all lower slices of `𝒟` are full up to rank `m`, deduces
  `oddLowerHalfFamily m ⊆ 𝒩`, decomposes
  `𝒩 = oddLowerHalfFamily m ∪ 𝒰` and `ℳ = (oddLowerHalfFamily m \ 𝒱) ∪ 𝒲`, and then uses the
  `totalSize ≤ witness` hypothesis to force `𝒲 = ∅`. That yields the simple-lower shape
  `ℳ = oddLowerHalfFamily m \ 𝒱`, `𝒩 = oddLowerHalfFamily m ∪ 𝒰`.
- The already-formalized simple-lower equivalence
  `totalSize ≤ witness ↔ uniform upper layer`
  then gives `∀ s ∈ 𝒰, s.card = m + 1`, so the stronger normalization theorem closes directly.

So this branch of the plan is complete. The remaining live subgoal in the overall prism route is
now just:

- `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`.

Update on 2026-03-28:

- The remaining simple-lower subgoal has now been sharpened in Lean to the explicit contrapositive
  boundary-lower surface
  `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`,
  and the file proves it equivalent to
  `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`.
- The active proof note now reduces this surface to a pure middle-layer inequality
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|,
  \]
  where \(U \subseteq \binom{[2m+1]}{m+1}\) and \(T(V)\) is the family of middle-layer sets whose
  entire \(m\)-shadow lies in \(V \subseteq \binom{[2m+1]}{m}\).
- This is the current blocker. The development is no longer missing plumbing; it is stuck on that
  compression/isoperimetric middle-layer lemma.

Latest computational sharpening:

- the search tooling now has dedicated `n = 7` diagnostics for the reduced middle-layer inequality
  on uniform-upper simple-lower classes and for colex initial middle-layer pairs;
- all searched structured uniform-upper classes satisfy
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|,
  \]
  with margins `3`, `5`, and `6`;
- all colex `n = 7` initial segment pairs satisfy the stronger property
  \[
  T(V)\setminus U = \varnothing.
  \]

So the current best research direction is sharper again:

- prove compression/shifting does not increase
  \[
  |T(V)\setminus U| - |\partial^\uparrow U|;
  \]
- then prove the stronger colex containment statement \(T(V^\ast) \subseteq U^\ast\), or otherwise
  compute the compressed case exactly.
