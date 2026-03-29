# Stuck Plans

This note compresses the archived branches. The active route is still the direct two-layer
boundary program centered on
\[
|\partial^+\bigl((\binom{[n]}{m}\setminus V)\cup U\bigr)| \ge |\binom{[n]}{m}\setminus V|.
\]

## Archived Branches

### 1. Section Route

- Unrestricted even adjacent-layer theorem:
  \[
  |\partial^+G| \ge |G_r|,
  \qquad
  G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1}.
  \]
- Status: `falsified`.
- Counterexamples:
  \[
  G=\binom{[4]}{2}\sqcup \binom{[4]}{3}
  \quad\Rightarrow\quad
  |\partial^+G|=1<6=|G_2|,
  \]
  \[
  G=\binom{[6]}{3}\sqcup \binom{[6]}{4}
  \quad\Rightarrow\quad
  |\partial^+G|=6<20=|G_3|.
  \]
- Coupled repair attempt:
  \[
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)| \ge |A| + |B|.
  \]
- Status: `falsified`.
- Exact `n=5` counterexample:
  \[
  V = \{\{0,1\},\{0,2\},\{0,3\},\{0,4\}\},
  \qquad
  U = \{\{1,2,3\},\{1,2,4\},\{1,3,4\},\{2,3,4\}\},
  \]
  giving
  \[
  A=\varnothing,\quad B=\binom{[4]}{2},\quad D=\varnothing,\quad E=\binom{[4]}{3},
  \]
  hence
  \[
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)| = 1 < 6 = |A| + |B|.
  \]
- Consequence: sectioning survives only as an exact identity / heuristic, not as an active
  reduction theorem.

### 2. Compression-Monotonicity Route

- Conjectured functional:
  \[
  \Delta(U,V):=|T(V)\setminus U|-|\partial^\uparrow U|.
  \]
- Desired monotonicity:
  \[
  \Delta(U,V)\le \Delta(C_{ij}U,C_{ij}V).
  \]
- Stronger inclusion used by the route:
  \[
  C_{ij}(T(V)\setminus U)\subseteq T(C_{ij}V)\setminus C_{ij}U.
  \]
- Status: `falsified`.
- Explicit `n=7` counterexample with \(C_{0,2}\):
  \[
  V=\{\{2,3,4\},\{2,3,5\},\{2,4,5\},\{3,4,5\}\},
  \]
  \[
  U=\{\{0,1,2,3\},\{0,1,2,4\},\{0,1,3,4\},\{0,3,4,5\}\}.
  \]
  Then
  \[
  C_{0,2}(T(V)\setminus U)\not\subseteq T(C_{0,2}V)\setminus C_{0,2}U,
  \]
  and
  \[
  \Delta(U,V)=-8,\qquad \Delta(C_{0,2}U,C_{0,2}V)=-9.
  \]
- Consequence: this route is dead.

### 3. Weaker Colex Reduction

- Proposed theorem:
  \[
  \Delta(U,V)\le \Delta(U^\ast,V^\ast)
  \]
  for equal-size colex pairs \((U^\ast,V^\ast)\).
- Status: `falsified`.
- Exact `n=5`, `e=3` counterexample:
  \[
  \Delta(U^\ast,V^\ast)=-4,
  \qquad
  \Delta(U,V)=-3.
  \]
- Consequence: no direct reduction from arbitrary pairs to colex pairs via this defect functional.

### 4. Hall-Shadow Sufficient Condition

- Proposed sufficient condition:
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|.
  \]
- Status: `falsified`.
- Exact `n=5` failures occur at `e=5,6,7,8`; for example at `e=6`,
  \[
  |\partial^\uparrow U|=4<6=|U\setminus T(V)|.
  \]
- Consequence: the active boundary theorem cannot be reduced to a Hall-style argument of this form.

### 5. Unique Lex/Shifted Minimizer Orbit

- Conjecture: every minimizer of the two-layer boundary functional lies in the same permutation
  orbit as the lex/shifted model.
- Status: `falsified`.
- Exact `n=5` has multiple minimizer orbits for several values of `e`; for example:
  `e=1` has `3` orbits, `e=2` has `17`, `e=4` has `32`.
- Consequence: only existence of shifted minimizers remains plausible, not uniqueness.

### 6. Colex Paper-Proof Formalization

- Mathematical statement:
  \[
  T(V^\ast)\subseteq U^\ast
  \]
  for balanced colex initial segments.
- Status: `stuck at formalization`, not falsified.
- Obstruction: the current Lean route gets stuck at the `Finset.Colex` erased-set comparison layer
  and the balanced local-LYM packaging.
- Consequence: useful background evidence, but not part of the active proof route.

## Current Use

These branches are archived. They should be cited only as:

- evidence about what fails,
- a source of counterexamples,
- or heuristic background for the live direct-boundary and flux/calibration routes.
