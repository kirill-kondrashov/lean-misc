# Stuck Plans

This note records plan branches that are no longer active.

The current live plan is the direct two-layer boundary route:

- [PLAN_simple_lower_uniform_upper_pair_interface_boundary_lower_research.md](./PLAN_simple_lower_uniform_upper_pair_interface_boundary_lower_research.md)
- [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md)
- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)
- [STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md](./STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md)

Everything listed below is archived.

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

This route is dead. It cannot be revived by proving the old monotonicity conjecture, because that
conjecture is false.

## 2. Colex Compressed Case Formalization Route

Status: `stuck at formalization`

The compressed-case theorem
\[
T(V^\ast)\subseteq U^\ast
\]
for equal-size colex initial segments in the balanced middle layers has a paper proof, but that
paper proof is not part of the active plan anymore.

However, the direct attempt to land that proof in Lean inside
[Problem1CubeHalfBoundary.lean](../ErdosProblems/Problem1CubeHalfBoundary.lean) is currently stuck.
The obstruction is formal rather than mathematical:

1. pushing the erased-set comparisons through the `Finset.Colex` API without leaving unresolved
   order-instance goals;
2. packaging the balanced local-LYM step into a usable cardinality lemma of the form
   \[
   |T(V^\ast)| \le |V^\ast|.
   \]

This does not falsify the colex theorem. It only means the direct formalization route is not
active until a cleaner Lean encoding of the colex proof is found.

### Consequence

This branch is archived. The theorem may still be useful as background evidence, but the project no
longer carries a dedicated active `PROOF_*.md` note for it.

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

This branch is dead. The only remaining active route is the direct two-layer boundary inequality
\[
|\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|.
\]

## 4. Hall-Shadow Sufficient-Condition Route

Status: `stuck / falsified`

This was the route based on the stronger middle-layer inequality
\[
|\partial^\uparrow U| \ge |U\setminus T(V)|.
\]

### Why It Looked Promising

Let \(C:=\binom{[n]}{m}\setminus V\) and \(F:=C\cup U\). In the balanced bipartite inclusion graph
\[
\binom{[n]}{m} \leftrightarrow \binom{[n]}{m+1},
\]
regularity and Hall imply
\[
|\partial^\uparrow C| \ge |C|.
\]
Since
\[
\partial^+F=(\partial^\uparrow C\setminus U)\sqcup \partial^\uparrow U
\]
and
\[
\partial^\uparrow C=\binom{[n]}{m+1}\setminus T(V),
\]
one gets
\[
|\partial^+F|
\ge
|C|-|U\setminus T(V)|+|\partial^\uparrow U|.
\]
So the Hall-shadow inequality above would have implied the active two-layer boundary target
\[
|\partial^+F| \ge |C|.
\]

### Why It Is Archived

The sufficient condition is false.

An exact exhaustive `n = 5` search finds failures already at `e = 5,6,7,8`. For example, at
`e = 6`,
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
|\partial^\uparrow U|=4<6=|U\setminus T(V)|.
\]

### Consequence

This branch is dead as a proof strategy. The direct two-layer boundary inequality may still be
true, but it cannot be proved merely by reducing to the Hall-shadow sufficient condition above.

## 5. Unique Lex/Shifted Minimizer-Orbit Conjecture

Status: `stuck / falsified`

This was the stronger conjecture that, for the direct two-layer boundary problem,
\[
|\partial^+F| \ge |F\cap \tbinom{[n]}{m}|,
\qquad
F\subseteq \binom{[n]}{m}\sqcup \binom{[n]}{m+1},
\]
every boundary minimizer with fixed layer sizes should lie in the same permutation orbit as the
lex/shifted model.

### Why It Looked Plausible

The corrected `n = 5` diagnostics show that for every admissible layer size, a lex/shifted
two-layer family does attain the minimum boundary. So uniqueness up to symmetry was a natural next
guess.

### Why It Is Archived

The uniqueness statement is false already in exact `n = 5`.

For the minimizer orbits under the coordinate-permutation action:

- `e = 1` has `3` minimizer orbits,
- `e = 2` has `17` minimizer orbits,
- `e = 3` has `2` minimizer orbits,
- `e = 4` has `32` minimizer orbits,
- `e = 5` has `4` minimizer orbits,
- `e = 7` has `4` minimizer orbits,
- `e = 8` has `7` minimizer orbits,
- `e = 9` has `2` minimizer orbits.

So the correct surviving conjecture is only:

- some shifted family attains the minimum.

The stronger uniqueness claim is dead.

### Consequence

This branch is archived. The active direct route may still be proved by a compression argument, but
the target should be existence of shifted extremizers, not uniqueness of a single lex orbit.
