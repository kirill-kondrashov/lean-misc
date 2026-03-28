# Proof Note: Route Summary For The Reduced Middle-Layer Inequality

This note records the current route summary for the reduced middle-layer inequality in standard
mathematical notation.

It does **not** claim that the final theorem is already proved. It records:

1. the archived colex-reduction route and why it would have sufficed;
2. the direct counting and two-layer reformulations that still feed the active plan.

## Main Target

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

and

\[
\partial^\uparrow U
:=
\left\{
X\in \binom{[n]}{m+2} : \exists A\in U,\ A\subset X
\right\}.
\]

The remaining theorem to prove is

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|.
\tag{1}
\]

## Route A: Reduction To Equal-Size Colex Middle-Layer Pairs

Status: `archived / falsified`

The compressed-case theorem already proved in
[PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md)
is:

> If \(U^\ast \subseteq \binom{[n]}{m+1}\) and \(V^\ast \subseteq \binom{[n]}{m}\) are colex-initial
> segments with
> \[
> |U^\ast|=|V^\ast|,
> \]
> then
> \[
> T(V^\ast)\subseteq U^\ast.
> \]

So the only missing issue on this route is a weaker reduction from a general pair \((U,V)\) to an
equal-size colex pair \((U^\ast,V^\ast)\).

### Reduction Statement

Define the defect functional

\[
\Delta(U,V):=|T(V)\setminus U|-|\partial^\uparrow U|.
\]

Suppose one can prove the following reduction theorem:

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
> \tag{2}
> \]

Then the main target (1) follows.

### Proof

By the compressed-case theorem,

\[
T(V^\ast)\subseteq U^\ast.
\]

Hence

\[
T(V^\ast)\setminus U^\ast = \varnothing,
\]

so

\[
\Delta(U^\ast,V^\ast)
=
|T(V^\ast)\setminus U^\ast|-|\partial^\uparrow U^\ast|
=
-\,|\partial^\uparrow U^\ast|
\le 0.
\]

Using the reduction inequality (2), we obtain

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast)\le 0.
\]

Therefore

\[
|T(V)\setminus U|-|\partial^\uparrow U|\le 0,
\]

which is exactly

\[
|T(V)\setminus U|\le |\partial^\uparrow U|.
\]

This is the desired inequality (1). ∎

### Conclusion For Route A

So Route A is reduced to one precise missing theorem:

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast)
\]

for some equal-size colex pair \((U^\ast,V^\ast)\) attached to \((U,V)\).

In other words: if a weaker extremal/colex reduction for the defect functional were true, the
compressed-case theorem would close the reduced middle-layer inequality immediately.

However, this route is no longer active. Exact `n = 5` search falsifies the proposed reduction
theorem; see
[PROOF_weaker_reduction_to_equal_size_colex_middle_layer_pairs.md](./PROOF_weaker_reduction_to_equal_size_colex_middle_layer_pairs.md).

## Route B: Direct Middle-Layer Counting

The second live route is to prove (1) directly, without reducing to colex first.

Here is a clean sufficient statement for that direct route.

### Direct Counting Statement

Suppose one can prove

\[
|T(V)| \le |\partial^\uparrow U| + |T(V)\cap U|.
\tag{3}
\]

Then the main target (1) follows.

### Proof

Since

\[
T(V)

=
\bigl(T(V)\setminus U\bigr)\,\sqcup\,\bigl(T(V)\cap U\bigr)
\]

is a disjoint union, we have

\[
|T(V)| = |T(V)\setminus U| + |T(V)\cap U|.
\]

Combining this with (3), we get

\[
|T(V)\setminus U| + |T(V)\cap U|
\le
|\partial^\uparrow U| + |T(V)\cap U|.
\]

Subtracting \(|T(V)\cap U|\) from both sides yields

\[
|T(V)\setminus U|\le |\partial^\uparrow U|.
\]

This is exactly (1). ∎

### Equivalent Injection Form

An even more concrete version of the same route is:

> It is enough to construct an injection
> \[
> \iota:T(V)\longhookrightarrow \partial^\uparrow U \sqcup (T(V)\cap U).
> \]

Indeed, such an injection implies

\[
|T(V)| \le |\partial^\uparrow U| + |T(V)\cap U|,
\]

which is precisely (3), so the previous proof applies.

### Conclusion For Route B

So Route B is reduced to a direct combinatorial counting problem:

- either prove (3) directly by double-counting;
- or build an injection from \(T(V)\) into
  \[
  \partial^\uparrow U \sqcup (T(V)\cap U).
  \]

This avoids any general-to-colex reduction and would settle the reduced middle-layer inequality by
a purely local argument.

## Route C: Two-Layer Boundary Reformulation

There is a third formulation of the same direct route which packages the reduced inequality as a
plain positive-boundary lower bound for a two-layer family.

Let

\[
P_m := \binom{[n]}{m},
\qquad
C := P_m \setminus V,
\qquad
F := C \cup U.
\]

Since \(|V|=|U|\), we have

\[
|C| = \binom{n}{m} - |V| = \binom{n}{m} - |U|.
\]

The family \(F\) lives only on ranks \(m\) and \(m+1\). The claim is that the main target (1) is
equivalent to

\[
|\partial^+ F| \ge |C|.
\tag{4}
\]

### Proof Of The Reformulation

First observe that

\[
T(V)=P_{m+1}\setminus \partial^\uparrow C.
\tag{5}
\]

Indeed, an \((m+1)\)-set \(B\) lies in \(T(V)\) exactly when every \(m\)-subset of \(B\) lies in
\(V\), equivalently when no \(m\)-subset of \(B\) lies in \(C=P_m\setminus V\), equivalently when
\(B\notin \partial^\uparrow C\).

Next, because \(F=C\cup U\) occupies only ranks \(m\) and \(m+1\), its positive boundary splits
across the next two ranks:

\[
\partial^+ F

=
\bigl(\partial^\uparrow C \setminus U\bigr)
\;\sqcup\;
\partial^\uparrow U.
\tag{6}
\]

The first piece is the rank-\((m+1)\) boundary coming from the lower layer \(C\), after removing
the sets already present in \(U\); the second piece is the rank-\((m+2)\) boundary coming from the
upper layer \(U\). These two pieces lie in different ranks, so they are disjoint.

Taking cardinalities in (6) gives

\[
|\partial^+ F|
=
|\partial^\uparrow C \setminus U| + |\partial^\uparrow U|.
\tag{7}
\]

Now (5) implies

\[
T(V)\setminus U
=
\bigl(P_{m+1}\setminus \partial^\uparrow C\bigr)\setminus U
=
P_{m+1}\setminus \bigl(\partial^\uparrow C \cup U\bigr).
\]

Since \(|P_{m+1}|=\binom{n}{m+1}=\binom{n}{m}\), we obtain

\[
|T(V)\setminus U|
=
\binom{n}{m} - |\partial^\uparrow C \cup U|.
\]

Also

\[
|\partial^\uparrow C \cup U|
=
|\partial^\uparrow C \setminus U| + |U|,
\]

so

\[
|T(V)\setminus U|
=
\binom{n}{m} - |U| - |\partial^\uparrow C \setminus U|
=
|C| - |\partial^\uparrow C \setminus U|.
\tag{8}
\]

Substituting (8) into the main target (1), we get

\[
|\partial^\uparrow U|
\ge
|C| - |\partial^\uparrow C \setminus U|,
\]

which is equivalent to

\[
|\partial^\uparrow U| + |\partial^\uparrow C \setminus U|
\ge
|C|.
\]

By (7), this is exactly

\[
|\partial^+ F| \ge |C|.
\]

This proves the equivalence between (1) and (4). ∎

### Conclusion For Route C

So the direct route can be restated as:

> for every two-layer family
> \[
> F=(P_m\setminus V)\cup U
> \]
> with
> \[
> U \subseteq \binom{[n]}{m+1},
> \qquad
> V \subseteq \binom{[n]}{m},
> \qquad
> |U|=|V|,
> \]
> prove
> \[
> |\partial^+ F| \ge |P_m\setminus V|.
> \]

This is equivalent to the reduced middle-layer inequality, but it removes the auxiliary operator
\(T(V)\) from the statement. Any proof of this two-layer boundary inequality would finish the same
remaining bottleneck.

## Final Summary

The live proof task is therefore genuinely one of these routes:

1. prove the direct counting statement
   \[
   |T(V)| \le |\partial^\uparrow U| + |T(V)\cap U|,
   \]
   equivalently construct an injection
   \[
   \iota:T(V)\longhookrightarrow \partial^\uparrow U \sqcup (T(V)\cap U);
   \]
2. or prove the equivalent two-layer boundary inequality
   \[
   |\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|.
   \]

The two items above are equivalent direct routes; the second is often cleaner because it packages
the whole problem as a standard positive-boundary lower bound for a family supported on two
adjacent middle layers.
   T(V)\hookrightarrow \partial^\uparrow U \sqcup (T(V)\cap U).
   \]

Either route would prove the reduced inequality (1), and the existing Lean equivalence layer would
then close the simple-lower bottleneck and the downstream prism-theorem consequences.
