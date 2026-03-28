# Proof Attempt: Middle-Layer Compression Monotonicity

This note records a mathematical proof attempt for the conjectural compression lemma behind

\[
\texttt{SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement}.
\]

This route is now known to be false in its current form. The exact counterexample is recorded
below.

## Conjectural Compression Lemma

Let

\[
n := 2m+1,
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
V \subseteq \binom{[n]}{m}.
\]

Define the badness quantity

\[
\Delta(U,V)
:=
|T(V)\setminus U| - |\partial^\uparrow U|,
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

The originally desired monotonicity statement was:

> for every left-compression \(C_{ij}\) on \([n]\),
> \[
> \Delta(U,V) \le \Delta(C_{ij}U,\; C_{ij}V).
> \]

Equivalently, compression should not decrease the badness, so the worst case should be attained at
compressed/colex pairs.

## Proposed Proof

Fix a standard left-compression \(C_{ij}\) with \(i<j\), and write

\[
U' := C_{ij}U,
\qquad
V' := C_{ij}V.
\]

We want to show

\[
|T(V)\setminus U| - |\partial^\uparrow U|
\le
|T(V')\setminus U'| - |\partial^\uparrow U'|.
\]

The proof should split into two monotonicity statements.

### Step 1: Upper shadow decreases under compression

This is the standard part. For a family \(U \subseteq \binom{[n]}{m+1}\), one expects

\[
|\partial^\uparrow U'| \le |\partial^\uparrow U|.
\]

This is the familiar compression property behind Kruskal-Katona: left-compressions do not increase
upper shadow.

So it remains to show that the clique term does not decrease:

\[
|T(V')\setminus U'| \ge |T(V)\setminus U|.
\]

### Step 2: Compression should preserve clique support

The natural way to prove the previous inequality is to show a stronger inclusion:

\[
C_{ij}\bigl(T(V)\setminus U\bigr) \subseteq T(V')\setminus U'.
\]

Since compression preserves cardinality, this would imply

\[
|T(V)\setminus U|
=
\left|C_{ij}\bigl(T(V)\setminus U\bigr)\right|
\le
|T(V')\setminus U'|.
\]

Combined with Step 1, this would give the desired monotonicity of \(\Delta(U,V)\).

### Step 3: Why the inclusion is plausible

Take \(B \in T(V)\setminus U\). Then:

1. \(B \notin U\),
2. every \(m\)-subset of \(B\) lies in \(V\).

Let

\[
B' := C_{ij}(B).
\]

To prove

\[
B' \in T(V')\setminus U',
\]

it is enough to show:

1. \(B' \notin U'\),
2. every \(m\)-subset of \(B'\) lies in \(V'\).

The second point is the key structural claim. Every \(m\)-subset \(A' \subset B'\) should arise as
the compression of some \(m\)-subset \(A \subset B\), so that

\[
A \in V
\quad\Longrightarrow\quad
A' = C_{ij}(A) \in V'.
\]

If this “compression commutes with taking \(m\)-subsets of \(B\)” statement is true, then

\[
\binom{B'}{m} \subseteq V',
\]

which is exactly \(B' \in T(V')\).

Likewise, if \(B' \in U'\), then by the basic collision-resolution rule for compression there
should be some \(B^\ast \in U\) whose compression is \(B'\). The desired contradiction is that this
would force either \(B \in U\), or else a duplicate-compression obstruction incompatible with
choosing \(B\) from \(T(V)\setminus U\).

So the proof should reduce to the behavior of compression on:

- subsets of a compressed set,
- and the interaction between \(U\) and \(T(V)\) under collision.

## Falsified Inclusion

The argument above relied on the crucial inclusion

\[
C_{ij}\bigl(T(V)\setminus U\bigr) \subseteq T(C_{ij}V)\setminus C_{ij}U
\]

and that inclusion is false.

Take \(n=7\), so \(m=3\), and let \(C_{0,2}\) be the left-compression replacing \(2\) by \(0\).
Define

\[
V := \bigl\{\{2,3,4\},\{2,3,5\},\{2,4,5\},\{3,4,5\}\bigr\}
\subseteq \binom{[7]}{3},
\]

\[
U := \bigl\{
\{0,1,2,3\},
\{0,1,2,4\},
\{0,1,3,4\},
\{0,3,4,5\}
\bigr\}
\subseteq \binom{[7]}{4}.
\]

Then

\[
T(V)=\bigl\{\{2,3,4,5\}\bigr\},
\qquad
T(V)\setminus U=\bigl\{\{2,3,4,5\}\bigr\}.
\]

Compressing gives

\[
C_{0,2}(V)=
\bigl\{
\{0,3,4\},
\{0,3,5\},
\{0,4,5\},
\{3,4,5\}
\bigr\},
\]

\[
C_{0,2}(U)=U,
\]

and

\[
C_{0,2}\bigl(T(V)\setminus U\bigr)
=
\bigl\{\{0,3,4,5\}\bigr\}.
\]

But

\[
\{0,3,4,5\}\in T(C_{0,2}V)
\]

while simultaneously

\[
\{0,3,4,5\}\in C_{0,2}U.
\]

Hence

\[
C_{0,2}\bigl(T(V)\setminus U\bigr)
\not\subseteq
T(C_{0,2}V)\setminus C_{0,2}U.
\]

So the key inclusion behind the original proof attempt is false.

## Falsified Monotonicity

The weaker monotonicity claim for the badness functional is also false on the same example.

Indeed, for the \(U,V\) above one computes

\[
\Delta(U,V) = -8,
\qquad
\Delta(C_{0,2}U,\; C_{0,2}V) = -9.
\]

Therefore

\[
\Delta(U,V) \nleq \Delta(C_{0,2}U,\; C_{0,2}V),
\]

so the direct compression monotonicity conjecture fails as well.

## Consequence

The current compression proof strategy does not go through. It is not merely incomplete; the
proposed monotonicity statement is wrong.

Any successful compression-based proof would therefore need a different compressed quantity, or a
different coupled transformation of \((U,V)\), than the naive badness

\[
\Delta(U,V)=|T(V)\setminus U|-|\partial^\uparrow U|.
\]

## If a Replacement Route Exists

If one can find a replacement monotone quantity, or a weaker extremal reduction that avoids the
false inclusion above, then the rest of the program would still be:

1. compress repeatedly until \((U,V)\) is colex-compressed;
2. conclude that the maximum of \(\Delta(U,V)\) is attained on compressed pairs;
3. prove the colex statement
   \[
   T(V^\ast)\subseteq U^\ast;
   \]
4. deduce
   \[
   T(V^\ast)\setminus U^\ast = \varnothing,
   \]
   hence
   \[
   \Delta(U^\ast,V^\ast) \le 0,
   \]
   and therefore
   \[
   \Delta(U,V) \le 0
   \]
   for all pairs.

That would finish the reduced middle-layer inequality and therefore the current simple-lower
bottleneck.

## Status

Status: stuck.

The exact route written in this note has been falsified by the explicit \(n=7\) example above.
The remaining live research direction is to replace the failed compression monotonicity with either:

1. a different monotone defect functional,
2. a direct colex/extremal theorem for \(T(V)\setminus U\) versus \(\partial^\uparrow U\),
3. or a non-compression proof of the reduced middle-layer inequality.
