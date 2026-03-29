# Archived Plan: Even Adjacent-Layer Section Route

This note isolates the coarea / slicing route suggested by the current proof-side reduction.

## Starting Point

Let

\[
F = C \cup U \subseteq \binom{[2m+1]}{m}\sqcup \binom{[2m+1]}{m+1}
\]

with

\[
C = \binom{[2m+1]}{m}\setminus V,
\qquad
U \subseteq \binom{[2m+1]}{m+1},
\qquad
|U| = |V|.
\]

The odd target is

\[
|\partial^+F| \ge |C|.
\tag{B}
\]

## Exact Section Reduction

Fix a coordinate, say `0`, and section by whether a set contains `0`. The current proof note gives
families

\[
A \subseteq \binom{[2m]}{m-1},
\qquad
D \subseteq \binom{[2m]}{m},
\]

and

\[
B \subseteq \binom{[2m]}{m},
\qquad
E \subseteq \binom{[2m]}{m+1},
\]

such that

\[
|\partial^+F|
\ge
|\partial^+(A\cup D)| + |\partial^+(B\cup E)|.
\tag{S}
\]

So the odd problem is reduced to boundary lower bounds for two families on the even cube.

## Naive Even Target And Why It Fails

The first naive guess was the arbitrary even-dimensional adjacent-layer theorem:

\[
|\partial^+G| \ge |G_r|,
\qquad
G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1}.
\tag{E}
\]

This theorem is false.

Exact shifted diagnostics now show failures already in low dimensions:

- in \(n=4\), \(r=2\), take
  \[
  G = \binom{[4]}{2}\sqcup \binom{[4]}{3};
  \]
  then
  \[
  |\partial^+G| = 1 < 6 = |G_2|;
  \]
- in \(n=6\), \(r=3\), take
  \[
  G = \binom{[6]}{3}\sqcup \binom{[6]}{4};
  \]
  then
  \[
  |\partial^+G| = 6 < 20 = |G_3|.
  \]

So the route cannot proceed through the unrestricted theorem \((E)\).

## Corrected Section Target And Why It Also Fails

What the odd proof actually needs is not a theorem about arbitrary \(G\), but a theorem about the
coupled pair of section families \((A\cup D,\; B\cup E)\) arising from one odd family \(F\).

Because
\[
|C| = |A| + |B|,
\]
the exact section formula \((S)\) shows it is enough to prove the coupled inequality

\[
|\partial^+(A\cup D)| + |\partial^+(B\cup E)| \ge |A| + |B|
\tag{E'}
\]

for every section-compatible quadruple \((A,B,D,E)\) coming from
\[
F = C \cup U \subseteq \binom{[2m+1]}{m}\sqcup \binom{[2m+1]}{m+1}.
\]

This would be enough, but it is also false.

An exact `n = 5` counterexample is:

\[
V = \{\{0,1\},\{0,2\},\{0,3\},\{0,4\}\},
\qquad
U = \{\{1,2,3\},\{1,2,4\},\{1,3,4\},\{2,3,4\}\}.
\]

Then
\[
C = \binom{\{1,2,3,4\}}{2},
\qquad
F = C \cup U.
\]

The coordinate-`0` sections are
\[
A = \varnothing,
\qquad
B = \binom{[4]}{2},
\qquad
D = \varnothing,
\qquad
E = \binom{[4]}{3}.
\]

So
\[
|\partial^+(A\cup D)| + |\partial^+(B\cup E)|
=
0 + 1
=
1
<
6
=
|A| + |B|.
\]

Therefore the coupled theorem \((E')\) is false.

## Consequence

The section identity \((S)\) remains exact and geometrically useful, but it does not by itself
yield a viable lower-dimensional reduction theorem. Both of the first two attempts are now
archived:

- the unrestricted adjacent-layer theorem \((E)\);
- the corrected coupled theorem \((E')\).

So this note is now archival context only. The active proof search returns to the direct boundary
functional \(|\partial^+F|\) itself, via the compression and flux/calibration routes.

## Relationship To Other Routes

- The exact section formula still helps interpret why some lower-dimensional shadows appear.
- It may still inspire a flux identity with cross terms.
- But it is no longer part of the active reduction program.
