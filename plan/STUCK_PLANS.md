# Stuck Plans

This note records plan branches that are no longer active.

The active plan set should only contain live routes toward
`SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement` and the prism theorem endpoint.

## 1. Naive Middle-Layer Compression Monotonicity Route

Status: `stuck / falsified`

This was the route based on the badness functional

\[
\Delta(U,V) := |T(V)\setminus U| - |\partial^\uparrow U|
\]

for

\[
U \subseteq \binom{[2m+1]}{m+1},
\qquad
V \subseteq \binom{[2m+1]}{m}.
\]

The intended claim was that left-compressions \(C_{ij}\) should satisfy

\[
\Delta(U,V) \le \Delta(C_{ij}U,\; C_{ij}V),
\]

so that the worst case would reduce to colex/compressed pairs.

The route also relied on the stronger inclusion

\[
C_{ij}\bigl(T(V)\setminus U\bigr) \subseteq T(C_{ij}V)\setminus C_{ij}U.
\]

### Why It Is Archived

This route is false.

There is an explicit counterexample in `n = 7` with compression \(C_{0,2}\), namely

\[
V=
\bigl\{
\{2,3,4\},
\{2,3,5\},
\{2,4,5\},
\{3,4,5\}
\bigr\},
\]

\[
U=
\bigl\{
\{0,1,2,3\},
\{0,1,2,4\},
\{0,1,3,4\},
\{0,3,4,5\}
\bigr\}.
\]

For this pair one has

\[
C_{0,2}\bigl(T(V)\setminus U\bigr)
\not\subseteq
T(C_{0,2}V)\setminus C_{0,2}U,
\]

and the weaker monotonicity also fails:

\[
\Delta(U,V) = -8,
\qquad
\Delta(C_{0,2}U,\; C_{0,2}V) = -9.
\]

So this plan branch cannot be repaired by simply proving the old conjectured monotonicity.

### Consequence

This route is no longer part of the active plan.

The current live replacements are:

1. find a weaker extremal/colex reduction that does not use the false monotonicity;
2. or prove the reduced middle-layer inequality directly:
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|.
   \]

## 2. Lean Formalization Of The Colex Compressed Case

Status: `stuck at formalization`

The compressed-case theorem
\[
T(V^\ast)\subseteq U^\ast
\]
for equal-size colex initial segments in the balanced middle layers is now proved mathematically in
[PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md).

However, the direct attempt to land that proof in Lean inside
[Problem1CubeHalfBoundary.lean](../ErdosProblems/Problem1CubeHalfBoundary.lean) is currently stuck.
The obstruction is formal rather than mathematical:

1. pushing the erased-set comparisons through the `Finset.Colex` API without leaving unresolved
   order-instance goals;
2. packaging the balanced local-LYM step into a usable cardinality lemma of the form
   \[
   |T(V^\ast)| \le |V^\ast|.
   \]

This does not falsify the colex theorem. It only means the current direct formalization route is
not active until a cleaner Lean encoding of the colex proof is found.

## 3. Weaker Reduction To Equal-Size Colex Middle-Layer Pairs

Status: `stuck / falsified`

This was the route based on the weaker extremal statement:

\[
\Delta(U,V)\le \Delta(U^\ast,V^\ast),
\]

where

\[
\Delta(U,V):=|T(V)\setminus U|-|\partial^\uparrow U|,
\]

and \((U^\ast,V^\ast)\) denotes the equal-size colex pair attached to \((U,V)\).

### Why It Is Archived

This route is false.

An exact exhaustive `n = 5` search finds a counterexample at `e = 3`:

\[
U^\ast=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V^\ast=\bigl\{\{0,1\},\{0,2\},\{1,2\}\bigr\},
\]

for which

\[
\Delta(U^\ast,V^\ast)=-4,
\]

but

\[
U=\bigl\{\{0,1,2\},\{0,1,3\},\{0,2,3\}\bigr\},
\qquad
V=\bigl\{\{1,2\},\{1,3\},\{2,3\}\bigr\},
\]

satisfies

\[
\Delta(U,V)=-3.
\]

Hence

\[
\Delta(U,V)>\Delta(U^\ast,V^\ast),
\]

so the proposed weaker colex reduction theorem fails.

### Consequence

This branch is no longer part of the active plan.

The remaining active route is the direct two-layer boundary inequality
\[
|\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|.
\]
