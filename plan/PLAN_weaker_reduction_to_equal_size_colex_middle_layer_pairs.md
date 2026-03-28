# Plan: Weaker Reduction To Equal-Size Colex Middle-Layer Pairs

This note isolates the colex-reduction route as a standalone mathematical task.

Status: `stuck / falsified`

## Setting

Let

\[
n := 2m+1.
\]

Let

\[
U \subseteq \binom{[n]}{m+1},
\qquad
V \subseteq \binom{[n]}{m},
\qquad
|U|=|V|.
\]

Define

\[
T(V)
:=
\left\{
B\in \binom{[n]}{m+1} : \binom{B}{m}\subseteq V
\right\},
\]

\[
\partial^\uparrow U
:=
\left\{
X\in \binom{[n]}{m+2} : \exists A\in U,\ A\subset X
\right\},
\]

and the defect functional

\[
\Delta(U,V) := |T(V)\setminus U| - |\partial^\uparrow U|.
\]

The global reduced target is

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\]

equivalently

\[
\Delta(U,V)\le 0.
\]

## The Route-A Task

The theorem to prove on this route is:

> For every pair \((U,V)\) with
> \[
> U \subseteq \binom{[n]}{m+1},
> \qquad
> V \subseteq \binom{[n]}{m},
> \qquad
> |U|=|V|,
> \]
> there exist colex-initial segments
> \[
> U^\ast \subseteq \binom{[n]}{m+1},
> \qquad
> V^\ast \subseteq \binom{[n]}{m},
> \qquad
> |U^\ast|=|V^\ast|=|U|=|V|,
> \]
> such that
> \[
> \Delta(U,V)\le \Delta(U^\ast,V^\ast).
> \tag{R}
> \]

This is the precise weaker reduction from a general middle-layer pair to an equal-size colex pair.

## Why This Would Finish The Bottleneck

The compressed-case theorem already proved mathematically is:

\[
T(V^\ast)\subseteq U^\ast
\]

for equal-size colex initial segments \(U^\ast,V^\ast\); see
[PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md).

Therefore

\[
T(V^\ast)\setminus U^\ast=\varnothing,
\qquad
\Delta(U^\ast,V^\ast)=-|\partial^\uparrow U^\ast|\le 0.
\]

So if the reduction theorem (R) holds, then

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast)\le 0,
\]

which is exactly the reduced middle-layer inequality.

The full argument is written out in
[PROOF_weaker_reduction_to_equal_size_colex_middle_layer_pairs.md](./PROOF_weaker_reduction_to_equal_size_colex_middle_layer_pairs.md).

## Current Status

This route is now falsified.

An exact exhaustive `n = 5` search finds a counterexample at `e = 3`. The equal-size colex pair is

\[
U^\ast=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V^\ast=\bigl\{\{0,1\},\{0,2\},\{1,2\}\bigr\},
\]

for which

\[
\Delta(U^\ast,V^\ast)=-4.
\]

But the pair

\[
U=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V=\bigl\{\{1,2\},\{1,3\},\{2,3\}\bigr\},
\]

satisfies

\[
\Delta(U,V)=-3.
\]

Hence

\[
\Delta(U,V)>\Delta(U^\ast,V^\ast),
\]

so the reduction theorem \((R)\) is false even in `n = 5`.

Therefore this route is no longer active. The current live route is the direct two-layer boundary
inequality in [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md).
