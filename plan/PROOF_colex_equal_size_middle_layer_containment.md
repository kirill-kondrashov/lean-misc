# Proof: Colex Equal-Size Middle-Layer Containment

This note proves the compressed-case theorem suggested by the current research plan for
`SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`.

It is a mathematical proof note only. A direct Lean formalization attempt was made on
`2026-03-28`, but that implementation is currently stuck at the interface to the `Finset.Colex`
API and the balanced local-LYM step. So this note should be treated as a paper proof, not as a
completed Lean asset.

## Statement

Let

\[
n := 2m+1.
\]

Let

\[
V^\ast \subseteq \binom{[n]}{m},
\qquad
U^\ast \subseteq \binom{[n]}{m+1}
\]

be the colex-initial segments of equal size

\[
|V^\ast| = |U^\ast| = e.
\]

Define

\[
T(V^\ast)
:=
\left\{
B \in \binom{[n]}{m+1} : \binom{B}{m}\subseteq V^\ast
\right\}.
\]

Then

\[
T(V^\ast)\subseteq U^\ast.
\]

Equivalently, every \((m+1)\)-set all of whose \(m\)-subsets lie in the first \(e\) middle-layer
\(m\)-sets in colex order already lies in the first \(e\) middle-layer \((m+1)\)-sets in colex
order.

## Colex Convention

For same-size finite subsets \(A,B\subseteq \mathbb N\), write

\[
A <_{\mathrm{colex}} B
\]

iff

\[
\max(A\triangle B)\in B.
\]

This is the usual colex order.

## Step 1: The Largest \(m\)-Subset Of A \((m+1)\)-Set

For a nonempty finite set \(B\), write

\[
\sigma(B) := B\setminus\{\min B\}.
\]

So if \(B\in \binom{[n]}{m+1}\), then \(\sigma(B)\in \binom{[n]}{m}\).

### Lemma 1

For every \(B\in \binom{[n]}{m+1}\), the colex-largest member of \(\binom{B}{m}\) is
\(\sigma(B)\).

### Proof

Write

\[
B=\{b_0<b_1<\cdots<b_m\}.
\]

Every \(m\)-subset of \(B\) has the form

\[
B\setminus\{b_i\}
\qquad (0\le i\le m).
\]

If \(i>0\), compare \(B\setminus\{b_i\}\) with \(B\setminus\{b_0\}\). Their symmetric difference is

\[
\{b_0,b_i\},
\]

whose maximum is \(b_i\), and \(b_i\in B\setminus\{b_0\}\). Hence

\[
B\setminus\{b_i\} <_{\mathrm{colex}} B\setminus\{b_0\}.
\]

So \(B\setminus\{b_0\}=\sigma(B)\) is the colex-largest \(m\)-subset of \(B\). ∎

## Step 2: The Map \(B\mapsto \sigma(B)\) Is Colex-Monotone

### Lemma 2

If

\[
B,C \in \binom{[n]}{m+1}
\qquad\text{and}\qquad
B \le_{\mathrm{colex}} C,
\]

then

\[
\sigma(B)\le_{\mathrm{colex}} \sigma(C).
\]

### Proof

Let

\[
s:=\max(B\triangle C).
\]

If \(B=C\), the claim is trivial, so assume \(B\ne C\). Then

\[
s\in C
\]

because \(B<_{\mathrm{colex}}C\).

There are two cases.

#### Case 1: \(s\ne \min C\)

Then \(s>\min C\), so deleting \(\min C\) does not remove \(s\). Hence

\[
s\in \sigma(C).
\]

Also \(s\notin B\), so certainly

\[
s\notin \sigma(B).
\]

All elements larger than \(s\) agree between \(B\) and \(C\), and deleting the minimum of each set
cannot create a new disagreement above \(s\). Therefore

\[
\max(\sigma(B)\triangle\sigma(C))=s\in \sigma(C),
\]

which gives

\[
\sigma(B)<_{\mathrm{colex}}\sigma(C).
\]

#### Case 2: \(s=\min C\)

Then every element of \(C\setminus B\) is at most \(s\). But \(s\) is already the minimum of \(C\),
so in fact

\[
C\setminus B=\{s\}.
\]

Because \(B\) and \(C\) have the same cardinality, there is exactly one element \(r\) in
\(B\setminus C\), and necessarily

\[
r<s.
\]

Thus

\[
B=(C\setminus\{s\})\cup\{r\}.
\]

Since \(r<s=\min C\), we have \(r=\min B\). Therefore

\[
\sigma(B)=B\setminus\{r\}=C\setminus\{s\}=\sigma(C).
\]

So again

\[
\sigma(B)\le_{\mathrm{colex}}\sigma(C).
\]

This completes the proof. ∎

## Step 3: \(T(V^\ast)\) Is Itself A Colex-Initial Segment

### Lemma 3

If \(V^\ast\subseteq \binom{[n]}{m}\) is colex-initial, then \(T(V^\ast)\subseteq \binom{[n]}{m+1}\)
is also colex-initial.

### Proof

Take \(C\in T(V^\ast)\), and let \(B\in \binom{[n]}{m+1}\) satisfy

\[
B\le_{\mathrm{colex}} C.
\]

Because \(C\in T(V^\ast)\), every \(m\)-subset of \(C\) lies in \(V^\ast\). In particular, by
Lemma 1,

\[
\sigma(C)\in V^\ast.
\]

By Lemma 2,

\[
\sigma(B)\le_{\mathrm{colex}} \sigma(C).
\]

Since \(V^\ast\) is colex-initial and \(\sigma(C)\in V^\ast\), it follows that

\[
\sigma(B)\in V^\ast.
\]

Now \(\sigma(B)\) is the colex-largest \(m\)-subset of \(B\) by Lemma 1. Therefore every
\(m\)-subset of \(B\) is \(\le_{\mathrm{colex}} \sigma(B)\), hence belongs to \(V^\ast\) because
\(V^\ast\) is initial. So

\[
B\in T(V^\ast).
\]

Thus \(T(V^\ast)\) is colex-initial. ∎

## Step 4: A Balanced-Graph Bound Gives \(|T(V^\ast)|\le e\)

Consider the bipartite inclusion graph

\[
G\subseteq \binom{[n]}{m}\times \binom{[n]}{m+1},
\qquad
A\sim B \iff A\subset B.
\]

Because \(n=2m+1\), this graph is biregular of degree \(m+1\) on both sides:

\[
\deg(A)=m+1
\quad (A\in \tbinom{[n]}{m}),
\qquad
\deg(B)=m+1
\quad (B\in \tbinom{[n]}{m+1}).
\]

For any family \(F\subseteq \binom{[n]}{m+1}\), let

\[
\partial_\downarrow F
:=
\left\{
A\in \binom{[n]}{m} : \exists B\in F,\ A\subset B
\right\}
\]

be its lower shadow.

### Lemma 4

For every \(F\subseteq \binom{[n]}{m+1}\),

\[
|F|\le |\partial_\downarrow F|.
\]

### Proof

Count the edges between \(F\) and \(\partial_\downarrow F\).

Each \(B\in F\) contributes exactly \(m+1\) edges, so the number of such edges is

\[
(m+1)|F|.
\]

Each \(A\in \partial_\downarrow F\) is incident to at most \(m+1\) edges in total, so the same edge
set has size at most

\[
(m+1)|\partial_\downarrow F|.
\]

Hence

\[
(m+1)|F|\le (m+1)|\partial_\downarrow F|,
\]

which simplifies to

\[
|F|\le |\partial_\downarrow F|.
\]

∎

Apply this to

\[
F=T(V^\ast).
\]

By definition, every \(m\)-subset of every member of \(T(V^\ast)\) lies in \(V^\ast\). Therefore

\[
\partial_\downarrow T(V^\ast)\subseteq V^\ast.
\]

So Lemma 4 gives

\[
|T(V^\ast)|\le |\partial_\downarrow T(V^\ast)|\le |V^\ast|=e.
\]

## Step 5: Finish The Proof

By Lemma 3, \(T(V^\ast)\) is a colex-initial family in \(\binom{[n]}{m+1}\). By Step 4, its size is
at most \(e\). But \(U^\ast\) is the colex-initial family of size \(e\) in the same layer. Hence

\[
T(V^\ast)\subseteq U^\ast.
\]

This is exactly the desired statement. ∎

## Consequence For The Active Plan

The compressed-case theorem is therefore no longer conjectural:

\[
T(V^\ast)\subseteq U^\ast
\]

is proved mathematically for equal-size colex middle-layer pairs.

So the remaining active gap in the research plan is now sharper:

1. either find a weaker extremal reduction from general \((U,V)\) to colex equal-size middle-layer
   pairs;
2. or bypass reduction entirely and prove
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|
   \]
   directly.
