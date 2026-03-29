# Research Plan: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note records the active plan for the last remaining simple-lower bottleneck.

## Active Files

The active documentation set for this route is:

- [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md)
- [PLAN_stronger_than_middle_binomial_via_two_layer_gap.md](./PLAN_stronger_than_middle_binomial_via_two_layer_gap.md)
- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)
- [PLAN_two_layer_geometric_enrichment.md](./PLAN_two_layer_geometric_enrichment.md)
- [PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md)
- [STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md](./STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md)
- [PROGRESS_two_sheet_boundary_theorem_2026-03-22.md](./PROGRESS_two_sheet_boundary_theorem_2026-03-22.md)

Archived branches are summarized only in [STUCK_PLANS.md](./STUCK_PLANS.md).

## Main Target

Let

\[
n := 2m+1,
\qquad
L_m := \{S \subseteq [n] : |S| \le m\}.
\]

Let

\[
V \subseteq \binom{[n]}{m},
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
|U| = |V|.
\]

Define

\[
M := L_m \setminus V,
\qquad
N := L_m \cup U.
\]

The theorem to prove is

\[
|\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
\ge
2\binom{2m+1}{m}.
\]

## Reduced Middle-Layer Form

The statement has already been reduced to

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\]

where

\[
\partial^\uparrow U
:=
\{T \in \binom{[n]}{m+2} : \exists s \in U,\ s \subset T\},
\]

and

\[
T(V)
:=
\left\{B \in \binom{[n]}{m+1} : \binom{B}{m}\subseteq V\right\}.
\]

Everything downstream of this inequality is already wired in Lean. No further theorem packaging is
needed.

## Critical Review Of The Current Route

The present route is extremely successful as a reduction of the *exact* middle-binomial endpoint,
but it does **not** by itself go beyond the current published lower bound
\[
N \ge \binom{n}{\lfloor n/2\rfloor}.
\]

In particular:

- if we prove the current two-layer theorem exactly as stated, we recover the Dubroff-Fox-Xu
  lower bound through the existing closure graph;
- but that alone would still be only the literature-level exact middle-binomial lower bound, not a
  genuinely stronger result toward the open conjecture \(N \gg 2^n\);
- so the next research direction has to be a *gap/stability strengthening* of the current
  reduction, not just completion of the exact-bound bottleneck.

## Active Route

The only active route is the direct two-layer boundary route.

Let

\[
P_m := \binom{[n]}{m},
\qquad
C := P_m \setminus V,
\qquad
F := C \cup U.
\]

Then the reduced middle-layer inequality is equivalent to

\[
|\partial^+ F| \ge |C|.
\]

This route is recorded in:

- [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md)
- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)
- [PLAN_two_layer_geometric_enrichment.md](./PLAN_two_layer_geometric_enrichment.md)
- [PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md)
- [STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md](./STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md)

This route should now be read in two layers:

1. prove the exact two-layer theorem
   \[
   |\partial^+F| \ge |C|;
   \]
2. strengthen it, on the families coming from the sum-distinct subcube transport, to obtain a
   positive gap beyond equality. That new direction is recorded in
   [PLAN_stronger_than_middle_binomial_via_two_layer_gap.md](./PLAN_stronger_than_middle_binomial_via_two_layer_gap.md).

## Archived Routes

Archived and falsified branches are summarized in
[STUCK_PLANS.md](./STUCK_PLANS.md).

In particular, the naive compression route and the weaker colex reduction route are both archived,
the Hall-shadow sufficient-condition route is now archived as well, and the separate colex
formalization issue is no longer part of the active proof notebook set.

## Current Evidence

The current computational evidence still points in the right direction:

- the exact direct two-layer boundary inequality survives exhaustive `n = 5` search for all
  equal-size middle-layer pairs;
- exact `n = 5` also supports the actual two-layer compression target:
  every layer-preserving shift of a two-layer family \(F\) weakly decreases \(|\partial^+F|\)
  across all equal-size middle-layer pairs;
- this now extends exactly to shifted `n = 7`:
  across all `5164` shifted pairs and all `108444` layer-preserving shifts, no counterexample to
  the actual two-layer compression lemma appears;
- but the stronger strict-descent shortcut is now falsified already in exact `n = 5`:
  some nonshifted pairs admit no layer-preserving shift that strictly lowers \(|\partial^+F|\),
  so the compression program has to work with weak descent plus a separate rigidity argument;
- more sharply, the exact `n = 5` direct search supports the shifted-minimizer model:
  for every `e`, a lex/shifted two-layer family \(F=C\cup U\) attains the minimum boundary;
- exact shifted `n = 5` classification is sharper again:
  equality occurs only in the trivial full lower-layer orbit and the principal-star two-layer
  orbit;
- exact shifted `n = 7` enumeration now matches the same picture:
  all shifted pairs satisfy the two-layer inequality, and the only shifted equality orbits are
  again the trivial full lower-layer orbit and the principal-star two-layer orbit;
- with the current brute-force enumerator, exact shifted search is now effectively saturated at
  `n = 7`: the analogous `n = 9` shifted-family count does not return on a short/medium run, so
  the next step is paper proof rather than deeper exhaustive computation;
- but exact `n = 5` rules out the stronger uniqueness guess:
  the minimizers are not all contained in a single lex/shifted orbit;
- but the weaker minimizer-plateau statement now survives exactly in `n = 5`:
  every minimizer is connected to a shifted minimizer by a chain of boundary-preserving
  layer-preserving shifts;
- more strongly, for every `e`, the exact `n = 5` minimizer graph under boundary-preserving
  layer shifts is connected;
- stronger again, for every `e`, every exact `n = 5` equal-size two-layer pair reaches a shifted
  pair by a chain of nonincreasing layer-preserving shifts, so the weak-compression reduction to
  the shifted world now survives exactly on the full `n = 5` state space;
- but the cleaner strict-descent-plus-plateau version is now ruled out:
  exact `n = 5` has strict local minima at `e = 5,6` whose boundary-preserving shift components
  contain no shifted pair, so the active route has to work with genuinely interleaved
  nonincreasing paths rather than a strict phase followed by a plateau phase;
- however, the quotient-level weak-compression picture is still positive:
  exact `n = 5` now shows that for every `e`, the equal-boundary component graph has a unique
  sink component and that sink component contains shifted pairs;
- structured uniform-upper `n = 7` classes satisfy
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|
  \]
  with margins `3`, `5`, and `6`;
- colex equal-size middle-layer pairs in `n = 7, 9, 11` satisfy the stronger compressed-case
  containment
  \[
  T(V^\ast)\subseteq U^\ast.
  \]
- on the flux side, exact `n = 5` now sharply separates the first naive local transport models:
  the codimension-`1` local Hall condition fails, but the codimension-`2` local Hall condition
  survives over all equal-size middle-layer pairs;
- that same separation now survives in the shifted `n = 7` problem:
  codimension-`1` fails, but codimension-`2` survives across all shifted pairs;
- the first naive codimension-`2` weighting rule is now ruled out:
  equal-split local flux already overloads a boundary point in exact `n = 5`, and also in shifted
  `n = 7`;
- the next natural codimension-`2` weighting rule is ruled out as well:
  inverse-degree local flux already overloads a boundary point in exact `n = 5`, and also in
  shifted `n = 7`;
- the first finite family of canonical codimension-`2` greedy injections is ruled out as well:
  all eight tested rules fail already in exact `n = 5`, even though one of them survives over all
  shifted pairs in `n = 7`;
- but the codimension-`2` matching route now has a sharper positive invariant:
  in exact `n = 5` and in shifted `n = 7`, the minimum number of codimension-`2` edges needed in a
  perfect local matching always equals the codimension-`1` Hall deficiency lower bound;
- that invariant is now known to be genuinely global:
  exact `n = 5` and shifted `n = 7` both show that the codimension-`1` deficiency can be strictly
  larger than the number of lower cells with no codimension-`1` boundary neighbor;
- and it is not always realized by a single-coordinate cut either:
  exact `n = 5` and shifted `n = 7` both show examples where the codimension-`1` deficiency is
  strictly larger than every one-coordinate contain/avoid cut deficiency;
- but on the shifted route, the Hall obstruction now has a clean witness theorem candidate:
  in shifted `n = 5` and shifted `n = 7`, the codimension-`1` deficiency is always witnessed by a
  shifted lower subfamily;
- the next canonical strengthening is now limited:
  colex-prefix witnesses are false already in shifted `n = 5`, and lex-prefix witnesses are false
  in shifted `n = 7`, so the active shifted Hall route stops at “shifted subfamily witness,” not a
  simple boundary-order prefix theorem;
- the next geometric simplification is limited as well:
  initial-principal-star witnesses survive shifted `n = 5` but are false in shifted `n = 7`, so
  the active shifted Hall route also does not reduce to a single principal-star witness theorem;
- but the shifted witness route still has a positive finite-complexity shape:
  exact shifted diagnostics show that a Hall witness can always be chosen with at most `1` maximal
  generator in `n = 5` and at most `4` maximal generators in `n = 7`;
- the current exact search tooling appears saturated again on that branch:
  the analogous shifted generator-witness summary for `n = 9` does not return on a short/medium
  run with the current enumerator;
- the next pattern-level refinement is now sharply split:
  exact shifted `n = 7` already has `143` distinct minimal-generator witness patterns overall, so
  there is no tiny global pattern catalogue;
  but the maximally complex frontier is rigid, with only `2` four-generator patterns;
- the corrected coupled section inequality
  \[
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)| \ge |A| + |B|
  \]
  is false already in exact `n = 5`, so sectioning remains useful only as an exact decomposition,
  not as a standalone lower-dimensional reduction.

This is evidence only. It does not supply the remaining proof.

What is now ruled out:

- the naive compression-monotonicity route;
- the weaker colex defect-reduction route;
- the Hall-shadow sufficient condition
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|.
  \]
- uniqueness of the lex/shifted minimizer orbit.

So the remaining live task is the direct two-layer inequality itself, not any currently known
stronger substitute.

The latest proof-side sharpening is a coordinate-section reduction written out in
[PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md):
if
\[
F=C\cup U\subseteq \binom{[2m+1]}{m}\sqcup \binom{[2m+1]}{m+1}
\]
is sectioned at coordinate `0`, then
\[
|\partial^+F|
\ge
|\partial^+(A\cup D)| + |\partial^+(B\cup E)|.
\]
The first naive attempt to close the route from here was the arbitrary even-dimensional
adjacent-layer theorem
\[
|\partial^+G| \ge |G_r|,
\qquad
G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1},
\]
but exact shifted diagnostics now falsify that statement already in `n = 4` and `n = 6`.
The next attempt was the corrected coupled theorem
\[
|\partial^+(A\cup D)| + |\partial^+(B\cup E)| \ge |A| + |B|,
\]
but exact `n = 5` also falsifies that statement. Taking
\[
V = \{\{0,1\},\{0,2\},\{0,3\},\{0,4\}\},
\qquad
U = \{\{1,2,3\},\{1,2,4\},\{1,3,4\},\{2,3,4\}\},
\]
one gets
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
|\partial^+(A\cup D)| + |\partial^+(B\cup E)| = 1 < 6 = |A| + |B|.
\]
So the section route is now archived as a direct proof path. Its exact decomposition remains useful
geometric context, but the active proof search is back on the direct two-layer boundary functional
itself.

## Geometric Enrichment

The direct two-layer route now has three live geometric proof shapes.

1. Symmetrization / discrete mean-curvature route.
   Interpret
   \[
   F \subseteq \binom{[n]}{m}\sqcup\binom{[n]}{m+1}
   \]
   as a discrete membrane near the equator of the cube and seek a proof that layer-preserving
   symmetrization does not increase \(|\partial^+F|\). This is the upgraded version of the old
   compression program, but for the actual boundary functional rather than an auxiliary defect.

2. Flux / calibration route.
   Replace literal matching arguments by a fractional transport from lower-layer cells
   \(C = \binom{[n]}{m}\setminus V\) to the outward boundary \(\partial^+F\). The aim is to prove
   \(|C| \le |\partial^+F|\) by a divergence-style inequality rather than by a rigid injection.

3. Coarea / section route.
   This now survives only as geometric intuition. Both the unrestricted even adjacent-layer
   theorem and the corrected coupled section theorem are false, so sectioning is no longer an
   active reduction theorem for the project.

These geometric routes are recorded separately in:

- [PLAN_two_layer_geometric_enrichment.md](./PLAN_two_layer_geometric_enrichment.md)
- [PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md)
- [PLAN_stronger_than_middle_binomial_via_two_layer_gap.md](./PLAN_stronger_than_middle_binomial_via_two_layer_gap.md)

## Quantitative Upgrade Direction

The exact route above remains the active formal bottleneck, but the first quantitative upgrade
beyond the literature-level middle-binomial bound is now more concrete.

Exact shifted diagnostics now show:

- shifted `n = 5`: off the two equality templates, the first positive boundary gap is `2`;
- shifted `n = 7`: off the same templates, the first positive boundary gap is `3`.

The shifted distance profile is now sharper too:

- in both `n = 5` and `n = 7`, the nearest non-equality shifted pairs lie at template distance
  `2`;
- at that distance, the first boundary gap is `2` in `n = 5` and `3` in `n = 7`.

The global first-gap orbit set is now classified exactly in the shifted world:

- shifted `n = 5`: the global strict gap `2` is attained by `7` orbit types;
- shifted `n = 7`: the global strict gap `3` is attained by `5` orbit types;
- in shifted `n = 7`, every global first-gap orbit already lies at template distance `2`.
- the new shell test is sharper still:
  the full shifted distance-`2` shell has exactly `5` orbit types in `n = 7`, all with gap `3`,
  so in shifted `n = 7` the global first-gap set is exactly the distance-`2` shell;
  but this is false in shifted `n = 5`, where the distance-`2` shell has only `5` orbit types
  while the global first-gap set has `7`.

So the stronger-than-middle-binomial program is no longer just a vague stability question. The
current evidence supports a sharper first theorem target:
\[
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| \ge |C| + 2
\]
for shifted odd two-layer families, where \(\mathcal E\) is the pair of equality templates.

That target is recorded separately in
[PLAN_stronger_than_middle_binomial_via_two_layer_gap.md](./PLAN_stronger_than_middle_binomial_via_two_layer_gap.md).

## Practical Success Criterion

The active plan is complete once the direct two-layer boundary inequality

\[
|\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|
\]

is proved on paper and then formalized in Lean.

Once that is done, the existing equivalence layer closes:

- `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`,
- `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`,
- the canonical defect bottleneck,
- the prism theorem route,
- and the exact Erdős #1 endpoint under the current frontier.
