# Plan: Two-Layer Middle Boundary Inequality

This note isolates the direct two-layer route as a standalone mathematical task.

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
P_m := \binom{[n]}{m},
\qquad
C := P_m \setminus V,
\qquad
F := C \cup U.
\]

Then \(F\) is a family supported on the two adjacent middle layers \(m\) and \(m+1\).

## The Route-C Task

The theorem to prove directly on this route is:

\[
|\partial^+ F| \ge |C|.
\tag{B}
\]

Equivalently, in expanded notation:

\[
\left|\partial^+\!\left(\left(\binom{[n]}{m}\setminus V\right)\cup U\right)\right|
\ge
\left|\binom{[n]}{m}\setminus V\right|.
\]

This is the clean two-layer boundary form of the remaining simple-lower bottleneck.

## Why This Would Finish The Bottleneck

The reduced middle-layer inequality

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|
\]

is equivalent to \((B)\); the full proof is written out in
[PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md).

So a direct proof of \((B)\) would immediately finish the reduced middle-layer step, and therefore
close:

- `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`,
- `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`,
- the canonical defect bottleneck,
- and the current prism-theorem route.

## Current Status

- The equivalence between \((B)\) and the reduced middle-layer inequality is proved on paper.
- No direct proof of \((B)\) is currently known in this project.
- The exact `n = 5` exhaustive search over all equal-size middle-layer pairs now supports \((B)\):
  for every `e = 0, \dots, 10`, the minimum value of
  \[
  \left|\partial^+\!\left(\left(\binom{[5]}{2}\setminus V\right)\cup U\right)\right| - \left|\binom{[5]}{2}\setminus V\right|
  \]
  is nonnegative, with the tight values `0` only at `e = 0` and `e = 6`.
- More sharply, the exact `n = 5` search now supports the shifted-minimizer picture behind the
  compression program: for every `e = 0,\dots,10`, a lex/shifted two-layer family
  \[
  F=C\cup U,\qquad C\subseteq \binom{[5]}{2},\quad U\subseteq \binom{[5]}{3},
  \]
  attains the minimum value of \(|\partial^+F|\).
- A tempting stronger sufficient condition,
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|,
  \]
  is now archived: it would imply \((B)\) by Hall in the balanced middle-layer inclusion graph,
  but exact `n = 5` search falsifies it.
- This route remains active because \((B)\) removes the auxiliary operator \(T(V)\) and packages
  the remaining work as an ordinary positive-boundary lower bound for a two-layer family.

## Current Research Program

The best live program is to attack the boundary itself, not stronger surrogate inequalities.

### 1. Formulate The Right Extremal Statement

Treat
\[
F:=C\cup U \subseteq \binom{[n]}{m}\sqcup \binom{[n]}{m+1},
\qquad
|F|=\binom{n}{m},
\]
as the primary object, and seek a direct theorem minimizing \(|\partial^+F|\) among two-layer
families with fixed layer sizes.

### 2. Prove A Two-Layer Compression Lemma

The key new candidate lemma is:

> For every layer-preserving compression/shift acting on the Boolean lattice, applying the shift to
> a two-layer family \(F\subseteq \binom{[n]}{m}\sqcup \binom{[n]}{m+1}\) does not increase
> \(|\partial^+F|\), while preserving the sizes of the rank-\(m\) and rank-\((m+1)\) slices.

This is deliberately different from the archived \(\Delta(U,V)\)-monotonicity route. The object to
control is the actual positive boundary of \(F\), not the auxiliary difference
\(|T(V)\setminus U|-|\partial^\uparrow U|\).

Exact `n = 5` support: for every `e = 0,\dots,10`, the lex-initial lower slice \(C\) of size
\(\binom{5}{2}-e\) together with the lex-initial upper slice \(U\) of size \(e\) attains the
minimum observed two-layer boundary.

### 3. Reduce To Shifted Two-Layer Families

If the compression lemma is proved, the active target \((B)\) reduces to shifted families:
\[
|\partial^+F| \ge |F\cap \binom{[n]}{m}|
\]
for shifted
\[
F\subseteq \binom{[n]}{m}\sqcup \binom{[n]}{m+1}.
\]

### 4. Classify The Shifted Extremizers

Use the exact `n = 5` data and the tight examples to guess the equality cases. The current evidence
suggests that the relevant extremizers should be:

- the full middle layer \(\binom{[n]}{m}\),
- principal-star type two-layer families.

The aim should be a stronger theorem with equality classification, not just the inequality.

### 5. Attack The Shifted Case By One-Coordinate Sections

For shifted \(F\), section by a coordinate \(i\), compare the `contains i` and `avoids i` slices,
and derive a recursive lower bound for \(|\partial^+F|\). The star-type equality candidates
indicate that one-coordinate sectioning is the right shape for the final argument.

### 6. Use Computation Only As Structural Guidance

The search tool should be used to:

- enumerate equality and near-equality families in `n = 5`,
- inspect structured candidates in `n = 7`,
- guess the exact shifted classification.

It should not be used as a substitute for the proof.

### 7. Lean Handoff Only After The Paper Argument Is Clear

Once the paper proof is stable, the formalization order should be:

1. the two-layer compression lemma in
   [Problem1CubeCompression.lean](../ErdosProblems/Problem1CubeCompression.lean),
2. the shifted structural/equality lemmas,
3. the final two-layer boundary theorem in
   [Problem1CubeHalfBoundary.lean](../ErdosProblems/Problem1CubeHalfBoundary.lean).

After that, the existing closure graph should finish the simple-lower bottleneck and the current
Erdős #1 route automatically.

## What Not To Pursue

The following branches are already archived in [STUCK_PLANS.md](./STUCK_PLANS.md) and should not be
revived without a genuinely new idea:

- compression monotonicity for \(\Delta(U,V)\),
- weaker colex reduction,
- Hall-shadow sufficient condition,
- separate colex-formalization route as an active proof program.
