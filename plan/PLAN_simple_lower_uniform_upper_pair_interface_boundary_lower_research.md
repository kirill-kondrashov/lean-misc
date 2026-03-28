# Research Plan: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note records the active plan for the last remaining simple-lower bottleneck.

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

In particular:

- the naive compression-monotonicity route is false;
- the weaker colex defect-reduction route is false already in exact `n = 5`;
- the direct Lean formalization of the compressed colex case remains a separate formalization issue,
  not an active proof route.

## Current Evidence

The current computational evidence still points in the right direction:

- the exact direct two-layer boundary inequality survives exhaustive `n = 5` search for all
  equal-size middle-layer pairs;
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
