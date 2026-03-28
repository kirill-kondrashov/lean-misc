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

## Computational Evidence

The direct two-layer inequality has now been checked exhaustively in the smallest nontrivial odd
dimension `n = 5`.

Writing
\[
\beta(U,V)
:=
\left|\partial^+\!\left(\left(\binom{[5]}{2}\setminus V\right)\cup U\right)\right|
-
\left|\binom{[5]}{2}\setminus V\right|,
\]
the exact search over all equal-size pairs
\[
U \subseteq \binom{[5]}{3},
\qquad
V \subseteq \binom{[5]}{2},
\qquad
|U|=|V|=e,
\]
finds
\[
\min \beta(U,V)\in \{0,2,3,4,5\},
\]
with the full per-\(e\) minima
\[
0,\,2,\,3,\,2,\,3,\,2,\,0,\,2,\,3,\,4,\,5
\qquad
(e=0,\dots,10).
\]

So the direct route survives exact exhaustive search in `n = 5`; what remains missing is a general
proof in arbitrary odd dimension.

The `n = 5` data are sharper than mere nonnegativity: for every `e = 0,\dots,10`, a lex/shifted
two-layer family attains the minimum boundary. Concretely, if one takes
\[
C \subseteq \binom{[5]}{2}
\]
to be the lex-initial segment of size \(10-e\), and
\[
U \subseteq \binom{[5]}{3}
\]
to be the lex-initial segment of size \(e\), then
\[
|\partial^+(C\cup U)|
\]
already matches the exact minimum over all equal-size middle-layer pairs.

So the current computational evidence points toward a genuine shifted/compression theorem for the
direct boundary functional itself.

What the `n = 5` data do **not** support is uniqueness of the lex orbit. An exact orbit
classification of the minimizers shows that multiple minimizer orbits occur for several values of
\(e\); for example, there are `17` minimizer orbits already at `e = 2`. So the viable
compression-based conjecture is:

\[
\text{some shifted minimizer exists, and more generally shifts do not increase } |\partial^+F|,
\]

not

\[
\text{there is a unique lex/shifted minimizer orbit.}
\]

This has now been sharpened further by an exact `n = 5` check of the actual two-layer compression
functional: for every equal-size middle-layer pair
\[
F=C\cup U\subseteq \binom{[5]}{2}\sqcup \binom{[5]}{3}
\]
and every layer-preserving shift \(S_{ij}\),
\[
|\partial^+(S_{ij}F)| \le |\partial^+F|.
\]

So the low-dimensional evidence now supports the real compression lemma of the active route, not
just the weaker shifted-minimizer existence picture. What remains missing is a proof in arbitrary
odd dimension.

- some shifted family attains the minimum boundary;

not the stronger statement:

- every minimizer lies in a single lex/shifted orbit.

## A Tempting Hall Reduction And Why It Is Not Enough

Let \(G\) be the bipartite inclusion graph
\[
P_m \leftrightarrow P_{m+1}.
\]
Because \(n=2m+1\), both sides have size \(\binom{n}{m}\), and every vertex on either side has
degree \(m+1\). Hence \(G\) is balanced and regular, so Hall's theorem gives
\[
|N(C)| \ge |C|
\qquad
\text{for every }
C\subseteq P_m,
\]
where \(N(C)=\partial^\uparrow C\subseteq P_{m+1}\).

Now
\[
\partial^+F
=
(\partial^\uparrow C\setminus U)\sqcup \partial^\uparrow U,
\]
so
\[
|\partial^+F|
=
|\partial^\uparrow C|-|U\cap \partial^\uparrow C|+|\partial^\uparrow U|
\ge
|C|-|U\cap \partial^\uparrow C|+|\partial^\uparrow U|.
\]

Using
\[
\partial^\uparrow C=P_{m+1}\setminus T(V),
\]
this becomes
\[
|\partial^+F|
\ge
|C|-|U\setminus T(V)|+|\partial^\uparrow U|.
\]

Therefore the stronger inequality
\[
|\partial^\uparrow U| \ge |U\setminus T(V)|
\tag{9}
\]
would imply the desired two-layer boundary inequality \((2)\).

However, \((9)\) is false in general.

An exact exhaustive `n=5` search finds failures at \(e=5,6,7,8\). For example, at \(e=6\),
\[
U=
\{
\{0,1,2\},\{0,1,3\},\{0,2,3\},\{0,1,4\},\{0,2,4\},\{0,3,4\}
\},
\]
\[
V=
\{
\{0,2\},\{1,2\},\{0,3\},\{1,3\},\{0,4\},\{1,4\}
\},
\]
for which
\[
|\partial^\uparrow U|=4
\qquad\text{but}\qquad
|U\setminus T(V)|=6.
\]

So the Hall-shadow criterion is a valid sufficient condition, but it cannot by itself prove the
two-layer boundary inequality.
