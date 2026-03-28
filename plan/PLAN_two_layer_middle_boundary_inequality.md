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
- A tempting stronger sufficient condition,
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|,
  \]
  is now archived: it would imply \((B)\) by Hall in the balanced middle-layer inclusion graph,
  but exact `n = 5` search falsifies it.
- This route remains active because \((B)\) removes the auxiliary operator \(T(V)\) and packages
  the remaining work as an ordinary positive-boundary lower bound for a two-layer family.
