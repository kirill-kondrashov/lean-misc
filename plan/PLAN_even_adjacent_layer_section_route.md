# Plan: Even Adjacent-Layer Section Route

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

## Corrected Section Target

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

This is now the real target on the section route.

## Why The Corrected Route Looks Cleaner

- It replaces the odd equatorial membrane by a theorem about arbitrary adjacent layers in even
  dimension, but keeps the essential coupling forced by one common odd family.
- The corrected target \((E')\) uses exactly the section pieces appearing in the proved
  decomposition \((S)\), rather than introducing a false standalone lower bound.
- It still reframes the remaining odd theorem as a lower-dimensional problem, but now with the
  right compatibility constraints.

## Proof Program

### 1. Understand Section Compatibility First

The first paper task is to characterize what quadruples \((A,B,D,E)\) can actually arise from a
single odd two-layer family \(F\). Without those compatibility conditions the naive theorem fails.

### 2. Prove The Coupled Inequality \((E')\) First For Shifted Odd Families

The current search evidence suggests shifted extremizers are still the right place to begin, but
now for section-compatible data rather than arbitrary even adjacent-layer families.

### 3. Classify Equality

The expected equality shapes should still be the section images of:

- the full lower layer;
- the principal-star two-layer family.

Writing those section images down explicitly should clarify the inductive step.

### 4. Use Sectioning Recursively

Once in the even adjacent-layer setting, section again by one coordinate and seek a recursive
bound. The hope is that repeated sectioning eventually produces a monotone induction on dimension
and rank.

### 5. Combine With The Odd Section Formula

After proving \((E')\), substitute it into \((S)\) for the two section families \(A\cup D\) and
\(B\cup E\), then recover \((B)\).

## Relationship To Other Routes

- This route is compatible with the compression program: one can still reduce \((E')\) to shifted
  families if the two-layer compression lemma is proved.
- It is also compatible with the flux route: a calibration may be easier to discover for \((E')\)
  than for the original odd theorem.

So this is not a rival theorem. It is the cleanest lower-dimensional formulation of the current
active bottleneck.
