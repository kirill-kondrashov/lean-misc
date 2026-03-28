# Proof Note: Weaker Reduction To Equal-Size Colex Middle-Layer Pairs

This note records the exact mathematical status of the colex-reduction route.

It proves two things:

1. if the weaker reduction theorem holds, then the reduced middle-layer inequality follows;
2. the weaker reduction theorem is in fact false, via an exact `n = 5` counterexample.

So this route is no longer active.

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

and

\[
\Delta(U,V):=|T(V)\setminus U|-|\partial^\uparrow U|.
\]

The target inequality is

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\tag{1}
\]

equivalently

\[
\Delta(U,V)\le 0.
\tag{1'}
\]

## Reduction Theorem Assumed On This Route

Assume:

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

Also use the compressed-case theorem already proved mathematically:

\[
T(V^\ast)\subseteq U^\ast
\tag{C}
\]

for equal-size colex initial segments \(U^\ast,V^\ast\); see
[PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md).

## Theorem

Under assumptions \((R)\) and \((C)\), the target inequality \((1)\) holds for every pair
\((U,V)\).

## Proof

Fix \(U\subseteq \binom{[n]}{m+1}\) and \(V\subseteq \binom{[n]}{m}\) with \(|U|=|V|\).

By the reduction theorem \((R)\), there exist colex-initial segments

\[
U^\ast \subseteq \binom{[n]}{m+1},
\qquad
V^\ast \subseteq \binom{[n]}{m},
\qquad
|U^\ast|=|V^\ast|=|U|=|V|,
\]

such that

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast).
\tag{2}
\]

By the compressed-case theorem \((C)\),

\[
T(V^\ast)\subseteq U^\ast.
\]

Hence

\[
T(V^\ast)\setminus U^\ast=\varnothing.
\]

Therefore

\[
\Delta(U^\ast,V^\ast)
=
|T(V^\ast)\setminus U^\ast|-|\partial^\uparrow U^\ast|
=
0-|\partial^\uparrow U^\ast|
=
-|\partial^\uparrow U^\ast|
\le 0.
\tag{3}
\]

Combining \((2)\) and \((3)\), we get

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast)\le 0.
\]

Thus

\[
|T(V)\setminus U|-|\partial^\uparrow U|\le 0,
\]

which is equivalent to

\[
|T(V)\setminus U|\le |\partial^\uparrow U|.
\]

This is exactly the target inequality \((1)\). ∎

## Counterexample To The Reduction Theorem

Take \(n=5\), so \(m=2\). Let

\[
U^\ast=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V^\ast=\bigl\{\{0,1\},\{0,2\},\{1,2\}\bigr\}.
\]

This is the equal-size colex pair at \(e=3\).

For \(V^\ast\), the only \((m+1)\)-set whose full \(m\)-shadow lies in \(V^\ast\) is

\[
T(V^\ast)=\bigl\{\{0,1,2\}\bigr\}.
\]

Since \(\{0,1,2\}\in U^\ast\), we get

\[
T(V^\ast)\setminus U^\ast=\varnothing.
\]

Also,

\[
\partial^\uparrow U^\ast
=
\bigl\{
\{0,1,2,3\},
\{0,1,2,4\},
\{0,1,3,4\},
\{0,2,3,4\}
\bigr\},
\]

so

\[
|\partial^\uparrow U^\ast|=4.
\]

Therefore

\[
\Delta(U^\ast,V^\ast)=0-4=-4.
\]

Now keep the same upper family but replace the lower family by

\[
U=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V=\bigl\{\{1,2\},\{1,3\},\{2,3\}\bigr\}.
\]

Then

\[
T(V)=\bigl\{\{1,2,3\}\bigr\},
\]

and since \(\{1,2,3\}\notin U\),

\[
|T(V)\setminus U|=1.
\]

The upper family is unchanged, so

\[
|\partial^\uparrow U|=4.
\]

Hence

\[
\Delta(U,V)=1-4=-3.
\]

Thus

\[
\Delta(U,V)=-3>-4=\Delta(U^\ast,V^\ast).
\]

So the reduction theorem \((R)\) fails, even in the smallest nontrivial exact case `n = 5`. ∎

## Consequence

The colex-reduction route is falsified. The remaining active route is the direct two-layer boundary
inequality in [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md).
