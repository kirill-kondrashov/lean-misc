# Proof Note: Two-Layer Middle Boundary Inequality

This note records the exact mathematical proof currently available for the two-layer route.

It proves that the reduced middle-layer inequality is equivalent to a direct positive-boundary
lower bound for a family supported on the adjacent middle layers. It does **not** prove that
boundary lower bound itself.

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
\right\}.
\]

The reduced target is

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|.
\tag{1}
\]

Now define

\[
P_m := \binom{[n]}{m},
\qquad
C := P_m \setminus V,
\qquad
F := C \cup U.
\]

The two-layer boundary inequality is

\[
|\partial^+ F| \ge |C|.
\tag{2}
\]

## Theorem

The reduced target \((1)\) and the two-layer boundary inequality \((2)\) are equivalent.

## Proof

First observe that

\[
T(V)=P_{m+1}\setminus \partial^\uparrow C.
\tag{3}
\]

Indeed, an \((m+1)\)-set \(B\) lies in \(T(V)\) exactly when every \(m\)-subset of \(B\) lies in
\(V\). Since \(C=P_m\setminus V\), this is equivalent to saying that no \(m\)-subset of \(B\) lies
in \(C\), which is equivalent to \(B\notin \partial^\uparrow C\). This proves \((3)\).

Next, because \(F=C\cup U\) is supported only on ranks \(m\) and \(m+1\), its positive boundary
splits across the next two ranks:

\[
\partial^+ F
=
\bigl(\partial^\uparrow C \setminus U\bigr)
\;\sqcup\;
\partial^\uparrow U.
\tag{4}
\]

Indeed:

- the rank-\((m+1)\) boundary points of \(F\) are exactly the \((m+1)\)-sets obtained from the
  upper shadow of the \(m\)-layer \(C\), after removing those already present in \(U\);
- the rank-\((m+2)\) boundary points of \(F\) are exactly the upper shadow of \(U\);
- there are no other boundary ranks, because \(F\) is empty below rank \(m\) and above rank
  \(m+1\).

The two pieces in \((4)\) lie in different ranks, so they are disjoint. Therefore

\[
|\partial^+ F|
=
|\partial^\uparrow C \setminus U| + |\partial^\uparrow U|.
\tag{5}
\]

Now use \((3)\):

\[
T(V)\setminus U
=
\bigl(P_{m+1}\setminus \partial^\uparrow C\bigr)\setminus U
=
P_{m+1}\setminus \bigl(\partial^\uparrow C \cup U\bigr).
\]

Hence

\[
|T(V)\setminus U|
=
|P_{m+1}| - |\partial^\uparrow C \cup U|.
\tag{6}
\]

Because \(n=2m+1\), we have

\[
|P_{m+1}|=\binom{n}{m+1}=\binom{n}{m}=|P_m|.
\]

Also

\[
|\partial^\uparrow C \cup U|
=
|\partial^\uparrow C \setminus U| + |U|.
\tag{7}
\]

Substituting \((7)\) into \((6)\), and using

\[
|C|=|P_m|-|V|=|P_m|-|U|,
\]

we obtain

\[
|T(V)\setminus U|
=
|P_m|-|U|-|\partial^\uparrow C \setminus U|
=
|C|-|\partial^\uparrow C \setminus U|.
\tag{8}
\]

Now the reduced target \((1)\) becomes

\[
|\partial^\uparrow U|
\ge
|C|-|\partial^\uparrow C \setminus U|,
\]

which is equivalent to

\[
|\partial^\uparrow U| + |\partial^\uparrow C \setminus U|
\ge
|C|.
\]

Using \((5)\), this is exactly

\[
|\partial^+ F| \ge |C|,
\]

namely \((2)\).

Thus \((1)\iff (2)\). ∎

## What Still Remains Open

The proof above is complete **as an equivalence**. What is still missing on this route is a direct
proof of the two-layer boundary inequality itself:

\[
|\partial^+ F| \ge |C|.
\]

So this note converts the remaining bottleneck into a cleaner two-layer boundary problem, but does
not solve that problem.
