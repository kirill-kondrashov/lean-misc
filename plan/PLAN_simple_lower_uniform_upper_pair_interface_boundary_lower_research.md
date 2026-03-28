# Research Plan: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note records the active plan for the last remaining simple-lower bottleneck.

## Active Files

The active documentation set for this route is:

- [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md)
- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)
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
\{T \in \tbinom{[n]}{m+2} : \exists s \in U,\ s \subset T\},
\]

and

\[
T(V)
:=
\left\{B \in \binom{[n]}{m+1} : \binom{B}{m}\subseteq V\right\}.
\]

Everything downstream of this inequality is already wired in Lean. No further theorem packaging is
needed.

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
- [STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md](./STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md)

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
- more sharply, the exact `n = 5` direct search supports the shifted-minimizer model:
  for every `e`, a lex/shifted two-layer family \(F=C\cup U\) attains the minimum boundary;
- exact shifted `n = 5` classification is sharper again:
  equality occurs only in the trivial full lower-layer orbit and the principal-star two-layer
  orbit;
- exact shifted `n = 7` enumeration now matches the same picture:
  all shifted pairs satisfy the two-layer inequality, and the only shifted equality orbits are
  again the trivial full lower-layer orbit and the principal-star two-layer orbit;
- but exact `n = 5` rules out the stronger uniqueness guess:
  the minimizers are not all contained in a single lex/shifted orbit;
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
