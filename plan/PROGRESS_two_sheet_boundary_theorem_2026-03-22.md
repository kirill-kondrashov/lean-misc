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
2. Work through the reduced middle-layer inequality
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|.
   \]
3. Use the live direct route:
   prove the equivalent two-layer middle-boundary inequality
   \[
   |\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|.
   \]
   Archived stuck routes are tracked separately in
   [STUCK_PLANS.md](/home/kir/pers/erdos/lean-misc/plan/STUCK_PLANS.md).
4. Once that statement is proved, use the already-formalized equivalence layer to recover
   `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`.
5. Then the proved normalization theorem plus the existing closure graph finish the canonical
   defect bottleneck, the prism theorem, and the exact Erdős #1 endpoint under the current leaf
   frontier.

Interpretation:

The remaining work is no longer packaging. The theorem graph is in place, and the general odd
first-gap problem has already been normalized to the simple-lower uniform-upper regime. The actual
missing piece is now one middle-layer compression/isoperimetric lemma.

Critical review:

- completing the current exact route would recover the exact middle-binomial lower bound
  \[
  N \ge \binom{n}{\lfloor n/2\rfloor},
  \]
  matching the published Dubroff-Fox-Xu benchmark already formalized in
  `Problem1Literature.lean`;
- so the exact route should now be treated as foundational infrastructure, not the final research
  destination;
- the genuinely new direction is to strengthen the same two-layer route to a positive gap beyond
  equality, as recorded in
  [PLAN_stronger_than_middle_binomial_via_two_layer_gap.md](/home/kir/pers/erdos/lean-misc/plan/PLAN_stronger_than_middle_binomial_via_two_layer_gap.md).

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
- the search tooling now also has an exact `n = 5` diagnostic for the actual two-layer
  compression target, and that check finds no counterexample:
  every layer-preserving shift of a two-layer family \(F\) weakly decreases \(|\partial^+F|\)
  across all equal-size middle-layer pairs;
- that compression evidence now extends exactly to shifted `n = 7` as well:
  across all `5164` shifted pairs and all `108444` layer-preserving shifts, no counterexample to
  the actual two-layer compression lemma appears;
- the stronger strict-compression shortcut is now ruled out already in exact `n = 5`:
  some nonshifted pairs admit no layer-preserving shift that strictly lowers \(|\partial^+F|\),
  so the compression route cannot be closed by a strictly descending potential alone;
- exact shifted `n = 5` classification now sharpens the equality picture too:
  within shifted two-layer families, equality in
  \[
  |\partial^+F| \ge |F\cap \tbinom{[5]}{2}|
  \]
  occurs only in the full lower-layer orbit and the principal-star orbit;
- the minimizer-plateau route now sharpens positively in exact `n = 5`:
  every two-layer minimizer is connected to a shifted minimizer by a chain of
  boundary-preserving layer shifts;
- more sharply, for every `e`, the exact `n = 5` minimizer graph under boundary-preserving
  layer shifts is connected;
- stronger again, for every `e`, every exact `n = 5` equal-size two-layer pair reaches a shifted
  pair by a chain of nonincreasing layer-preserving shifts, so the full weak-compression
  reduction to the shifted world now survives exactly in `n = 5`;
- but the cleaner two-phase variant is now falsified:
  exact `n = 5` has strict local minima at `e = 5,6` whose boundary-preserving shift components
  contain no shifted pair, so the route cannot be simplified to strict descent followed by a
  plateau argument;
- however, the quotient-level structure is better:
  exact `n = 5` now shows that for every `e`, the graph of equal-boundary shift components has a
  unique sink component, and that sink component contains shifted pairs;
- exact shifted `n = 7` enumeration now matches the same picture:
  the shifted-only search over all `352 × 352` middle-layer families finds no counterexample, and
  the only shifted equality orbits are again the full lower-layer orbit and the principal-star
  orbit;
- the stronger-gap branch now has its first exact profile:
  among shifted two-layer families, the first positive boundary gap off those equality templates is
  `2` in `n = 5` and `3` in `n = 7`, so the quantitative program is now aiming beyond the
  naive additive `+1` target;
- the stronger-gap branch is now refined by template distance as well:
  in both shifted `n = 5` and shifted `n = 7`, the nearest non-equality pairs lie at distance `2`
  from the equality templates, while the first positive boundary gaps are `2` and `3`
  respectively;
- the stronger-gap branch now has its first orbit-level near-equality classification:
  the global strict gap is attained by `7` shifted orbit types in `n = 5` and `5` shifted orbit
  types in `n = 7`, and in shifted `n = 7` every one of those global first-gap orbits already
  lies at template distance `2`;
- the near-template picture is now sharper still:
  the full shifted distance-`2` shell has exactly `5` orbit types in `n = 7`, all with gap `3`,
  so in shifted `n = 7` the global first-gap set is exactly the distance-`2` shell;
  this exact shell characterization is false in shifted `n = 5`, so it currently looks like a
  genuinely higher-dimensional phenomenon rather than a universal odd-dimensional rule;
- the shifted shell ladder is now partially exact beyond the first shell:
  shifted `n = 5` has shell gaps
  `0, 2, 3, [2..4], 5`
  at template distances `0, 2, 4, 6, 8`;
  shifted `n = 7` has shell gap `5` uniformly on the full distance-`4` shell, while the
  distance-`6` shell already splits with gaps `6` and `7`;
  so the first two nontrivial shells are rigid in shifted `n = 7`, but shell rigidity already
  breaks by distance `6`;
- the shell-attribution picture is now sharper as well:
  in shifted `n = 7`, the low shells are heavily concentrated near the principal-star template:
  the distance-`2` shell splits as `1` full-lower pair and `4` principal-star pairs,
  the distance-`4` shell splits as `1` full-lower pair and `9` principal-star pairs,
  and the distance-`6` shell splits as `4` full-lower pairs and `36` principal-star pairs;
  shifted `n = 5` already shows the same asymmetry in the first two shells, but farther shells
  introduce tied families, so the clean template split currently looks like a higher-dimensional
  signal rather than a uniform small-`n` rule;
- the full shifted `n = 7` attribution profile is now exact too:
  every positive shell from distance `2` through distance `18` splits only into
  `full-lower` and `principal-star` classes, tied classes do not appear until distance `20`,
  and in every positive shell the principal-star side is much larger than the full-lower side;
  so the stronger-gap route is now best read as a principal-star-dominated stability program with
  a thin exceptional full-lower strand, not as a symmetric two-template stability problem;
- the shifted strand profile is now sharper still:
  in shifted `n = 7`, throughout the entire pre-tied regime `d = 0,2,\dots,18`,
  the `full-lower` and `principal-star` strands have exactly the same shell gap envelope;
  the asymmetry is therefore in multiplicity, not in the observed shell gap interval itself;
  this suggests the stronger theorem may need to split into a distance-only shell-envelope
  statement plus a separate template-attribution statement;
- pushing the same brute-force shifted-enumeration idea to `n = 9` no longer looks productive:
  the shifted-family count itself does not return on a short/medium run, so the search side is
  effectively saturated at `n = 7`;
- the same saturation issue now appears on the stronger branch as well:
  the full shifted `n = 7` shell-profile enumeration does not look worth pushing further with the
  current brute-force tool, so the next step has to be theorem-level work on shifted shell/gap
  rigidity rather than deeper shell scans;
- that stronger-branch bottleneck is now partially resolved:
  the filtered global shell probe has been replaced by a genuinely template-local shifted
  generator, built by bounded-distance BFS in the lattice of shifted families;
- the new generator exactly reproduces the known shifted `n = 7` strand profile through
  distance `6`, and now pushes the shell calculation out to shifted `n = 9` and shifted `n = 11`
  through distance `10`;
- in both of those dimensions, the `full-lower` and `principal-star` strands still have exactly
  the same shell gap envelopes at every computed shell distance;
- so the shell-envelope symmetry now has exact support in shifted `n = 7, 9, 11`, rather than
  only in shifted `n = 7`;
- the next computational wall has moved outward but remains real:
  even the template-local generator does not return quickly at shifted `n = 13` with distance
  bound `4`, so the current shell program is now saturated at `n = 11`;
- on the new additive-improvement branch, the first-shell formula is now sharper:
  the distance-`2` shell has exact minimum gap
  ```math
  m = \frac{n-1}{2}
  ```
  in shifted `n = 5,7,9,11,13,15,17,19,21,23,25`;
- this makes
  ```math
  N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor
  ```
  the best explicit current target beyond the middle-binomial benchmark;
- the first-shell generator itself has now been sped up by replacing full comparability with
  immediate cover relations in the shifted poset;
- as a result, the exact distance-`2` shell now returns through shifted `n = 25`;
- in every newly checked odd dimension, that shell still splits as
  `1` full-lower pair plus `4` principal-star pairs, all with margin exactly `m`;
- the next untested odd dimension on that narrower first-shell branch is now `n = 27`;
- the proof note now contains an exact coordinate-section reduction:
  for
  \[
  F=C\cup U\subseteq \binom{[2m+1]}{m}\sqcup \binom{[2m+1]}{m+1},
  \]
  sectioning at coordinate `0` gives
  \[
  |\partial^+F|
  \ge
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)|,
  \]
  reducing the odd middle-layer target to a paired even-dimensional section theorem;
- the first naive version of that section route is now falsified:
  the unrestricted adjacent-layer claim
  \[
  |\partial^+G| \ge |G_r|,
  \qquad
  G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1},
  \]
  fails already for shifted families in `n = 4` and `n = 6`;
  for instance
  \[
  G = \binom{[4]}{2}\sqcup \binom{[4]}{3}
  \]
  has
  \[
  |\partial^+G| = 1 < 6 = |G_2|;
  \]
- the corrected coupled section target is now falsified as well:
  in exact `n = 5`, taking
  \[
  V = \{\{0,1\},\{0,2\},\{0,3\},\{0,4\}\},
  \qquad
  U = \{\{1,2,3\},\{1,2,4\},\{1,3,4\},\{2,3,4\}\},
  \]
  gives sections
  \[
  A = \varnothing,
  \qquad
  B = \binom{[4]}{2},
  \qquad
  D = \varnothing,
  \qquad
  E = \binom{[4]}{3},
  \]
  and therefore
  \[
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)| = 1 < 6 = |A| + |B|;
  \]
  so sectioning remains useful only as an exact identity, not as an active reduction theorem;
- the flux route now has its first positive exact evidence:
  the naive codimension-`1` local Hall graph already fails in exact `n = 5`, but the
  codimension-`2` local Hall graph survives exact `n = 5` across all equal-size middle-layer
  pairs;
- that split is now stable in the shifted `n = 7` model as well:
  codimension-`1` fails with worst deficiency `-15` at `e = 20`, while the codimension-`2` local
  Hall graph survives across all shifted pairs;
- the first naive codimension-`2` calibration is now falsified:
  equal-split transport already overloads a boundary point in exact `n = 5`, and also in shifted
  `n = 7`;
- the next natural codimension-`2` calibration is now falsified as well:
  inverse-degree transport already overloads a boundary point in exact `n = 5`, and also in
  shifted `n = 7`;
- the first finite family of canonical codimension-`2` greedy injections is now archived too:
  all eight tested priority rules fail already in exact `n = 5`, even though one survives on the
  shifted `n = 7` subproblem;
- the codimension-`2` matching route nevertheless sharpens positively:
  in exact `n = 5` and in shifted `n = 7`, the minimum number of codimension-`2` edges needed in a
  perfect local matching always equals the codimension-`1` Hall deficiency lower bound;
- the first naive explanation of that deficiency is now ruled out:
  in exact `n = 5` and in shifted `n = 7`, the codimension-`1` deficiency can be strictly larger
  than the number of lower cells with no codimension-`1` boundary neighbor;
- the next geometric shortcut is ruled out as well:
  in exact `n = 5` and in shifted `n = 7`, the codimension-`1` deficiency can be strictly larger
  than the best single-coordinate contain/avoid cut deficiency;
- but the shifted Hall route sharpens positively:
  in shifted `n = 5` and shifted `n = 7`, the codimension-`1` deficiency is always witnessed by a
  shifted lower subfamily;
- the obvious prefix simplifications are now partly archived:
  colex-prefix witnesses fail already in shifted `n = 5`, and lex-prefix witnesses fail in shifted
  `n = 7`;
- the next principal-star simplification is archived too:
  initial-principal-star witnesses survive shifted `n = 5` but fail in shifted `n = 7`;
- but the shifted Hall route still has a positive finite-complexity refinement:
  exact shifted diagnostics show that a Hall witness can be chosen with at most `1` maximal
  generator in shifted `n = 5` and at most `4` maximal generators in shifted `n = 7`;
- that generator-witness branch is now computationally saturated again:
  the analogous exact shifted summary for `n = 9` does not return on a short/medium run with the
  current enumerator;
- the next pattern-level refinement is now sharply split:
  exact shifted `n = 7` already has `143` distinct minimal-generator witness patterns overall, so
  there is no tiny global witness catalogue, but only `2` four-generator patterns at the
  maximally complex frontier;
- all searched structured uniform-upper classes satisfy
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|,
  \]
  with margins `3`, `5`, and `6`;
- all colex `n = 7` initial segment pairs satisfy the stronger property
  \[
  T(V)\setminus U = \varnothing.
  \]

Archived stuck routes:

- the naive compression-monotonicity route is no longer active and is summarized in
  [STUCK_PLANS.md](/home/kir/pers/erdos/lean-misc/plan/STUCK_PLANS.md).

Latest replacement-route evidence:

- the search tooling now has generalized colex summary checks for odd dimensions;
- for colex equal-size middle-layer pairs in `n = 7, 9, 11`, every searched case satisfies the
  stronger compressed-case containment
  \[
  T(V^\ast)\subseteq U^\ast,
  \]
  hence in particular
  \[
  T(V^\ast)\setminus U^\ast=\varnothing;
  \]
- the worst reduced margins in those colex summaries are `3` at `n = 7`, `4` at `n = 9`, and `5`
  at `n = 11`, each attained at `e = 1`.

The old colex replacement conjecture is now dead.

Current implementation status of that archived branch:

- the theorem \(T(V^\ast)\subseteq U^\ast\) has a paper proof, but that proof note is no longer
  part of the active plan set;
- a direct Lean formalization attempt of that note is currently stuck at the `Finset.Colex` /
  local-LYM interface and is not present in
  [Problem1CubeHalfBoundary.lean](/home/kir/pers/erdos/lean-misc/ErdosProblems/Problem1CubeHalfBoundary.lean);
- an exact exhaustive `n = 5` search now falsifies the proposed weaker colex defect-reduction
  theorem:
  for `e = 3`, the colex pair has defect `-4`, but a non-colex pair with the same upper family has
  defect `-3`; this archived branch is now summarized in
  [STUCK_PLANS.md](/home/kir/pers/erdos/lean-misc/plan/STUCK_PLANS.md);
- the direct middle-layer route has now been sharpened further in
  [PROOF_two_layer_middle_boundary_inequality.md](/home/kir/pers/erdos/lean-misc/plan/PROOF_two_layer_middle_boundary_inequality.md):
  with
  \[
  P_m := \binom{[2m+1]}{m},
  \qquad
  C := P_m \setminus V,
  \qquad
  F := C \cup U,
  \]
  the reduced inequality
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|
  \]
  is equivalent to the two-layer boundary inequality
  \[
  |\partial^+ F| \ge |C|.
  \]
- the search tooling now also has an exact `n = 5` diagnostic for that direct route, and the full
  exhaustive search over equal-size middle-layer pairs finds no counterexample to
  \[
  |\partial^+ F| \ge |C|.
  \]
  The minimum margin is nonnegative for every `e = 0,\dots,10`; the tight values are `0` at
  `e = 0` and `e = 6`, and the smallest nontrivial margin is `2`.
- a new Hall-based sufficient-condition route has now also been tested and archived:
  the stronger inequality
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|
  \]
  would imply the direct two-layer target, but exact exhaustive `n = 5` search falsifies it at
  `e = 5,6,7,8`, with worst margin `-2` at `e = 6`.
- the direct-route compression picture now has exact `n = 5` support in the right model:
  for every `e = 0,\dots,10`, the lex-initial lower slice \(C\) of size \(\binom{5}{2}-e\)
  together with the lex-initial upper slice \(U\) of size \(e\) attains the exact minimum of
  \[
  |\partial^+(C\cup U)|.
  \]
- but the stronger uniqueness guess is now dead:
  exact `n = 5` minimizer-orbit classification shows that for several values of `e`, multiple
  minimizer orbits occur, so the live compression conjecture is only existence of shifted
  minimizers, not uniqueness of a single lex orbit.
- so the overall active plan is now purely direct: prove the equivalent two-layer
  middle-boundary inequality directly. The route remains mathematically open, but it survives the
  exact low-dimensional checks currently in the toolchain.
