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
- Even more sharply, the exact `n = 5` search supports the actual two-layer compression lemma:
  for every equal-size middle-layer pair \(F=C\cup U\) and every layer-preserving shift
  \(S_{ij}\), one has
  \[
  |\partial^+(S_{ij}F)| \le |\partial^+F|.
  \]
- Exact shifted classification in `n = 5` is now sharper as well:
  among shifted two-layer families, equality in \((B)\) occurs only in two orbits:
  the trivial full lower layer at `e = 0`, and the principal-star two-layer family at `e = 6`
  (up to permutation).
- The shifted subproblem is now exact in `n = 7` as well:
  there are only `352` shifted families in each middle rank, exhaustive shifted enumeration shows
  no counterexample to \((B)\), and the only shifted equality orbits are again the trivial full
  lower layer (`e = 0`) and the principal-star two-layer family (`e = 20`).
- With the current brute-force search tool, this exact shifted-enumeration strategy appears to top
  out at `n = 7`: an analogous `n = 9` shifted-family count does not finish on a short/medium
  run, so deeper exhaustive search is no longer the right next step.
- However, exact `n = 5` does **not** support uniqueness of the lex orbit of minimizers:
  for several values of `e`, multiple minimizer orbits occur.
- A tempting stronger sufficient condition,
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|,
  \]
  is now archived: it would imply \((B)\) by Hall in the balanced middle-layer inclusion graph,
  but exact `n = 5` search falsifies it.
- On the flux side, the first local transport picture is now sharper:
  exact `n = 5` shows that the codimension-`1` local Hall graph fails, but the codimension-`2`
  local Hall graph survives across all equal-size middle-layer pairs.
- This is no longer only a tiny-dimensional phenomenon:
  in the shifted `n = 7` model, codimension-`1` still fails, while codimension-`2` survives across
  all shifted pairs.
- But the first naive codimension-`2` calibration is already dead:
  equal-split transport overloads a boundary point both in exact `n = 5` and in shifted `n = 7`.
- The next natural codimension-`2` calibration is dead as well:
  inverse-degree transport overloads a boundary point both in exact `n = 5` and in shifted
  `n = 7`.
- The first finite family of canonical codimension-`2` greedy injections is dead as well:
  all eight tested greedy rules fail already in exact `n = 5`, so the matching route cannot be
  closed by a fixed local priority rule.
- But the codimension-`2` matching route has a new exact invariant:
  in exact `n = 5` and in shifted `n = 7`, the minimum number of codimension-`2` edges required
  by a perfect local matching always equals the codimension-`1` Hall deficiency.
- That invariant is not explained by the simplest local obstruction:
  in exact `n = 5` and in shifted `n = 7`, the codimension-`1` Hall deficiency can be strictly
  larger than the number of zero-degree lower cells in the codimension-`1` local graph.
- Nor is it always realized by the simplest geometric cut:
  in exact `n = 5` and in shifted `n = 7`, the codimension-`1` Hall deficiency can be strictly
  larger than the best single-coordinate contain/avoid cut deficiency.
- The coordinate-section decomposition remains exact, but both standalone reductions suggested by
  it are now archived: the unrestricted even adjacent-layer theorem and the corrected coupled
  section theorem are both false.
- This route remains active because \((B)\) removes the auxiliary operator \(T(V)\) and packages
  the remaining work as an ordinary positive-boundary lower bound for a two-layer family.

## Geometric Proof Paths

The direct route now has two active geometric proof paths and one archived heuristic:

- [PLAN_two_layer_geometric_enrichment.md](./PLAN_two_layer_geometric_enrichment.md)
  records the high-level membrane / one-sided isoperimetry / hypersimplex viewpoint.
- [PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md)
  records the divergence-style route, replacing rigid matching by fractional transport from
  \(C\) to \(\partial^+F\).
- [STUCK_PLANS.md](./STUCK_PLANS.md)
  records the archived coarea / section branch and its counterexamples.

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
minimum observed two-layer boundary. In addition, the exact `n = 5` check of the actual
compression statement finds no counterexample: every layer-preserving shift weakly decreases the
two-layer boundary.

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
supports the existence of shifted extremizers, but it already rules out the strongest uniqueness
guess: the exact `n = 5` minimizers are not all contained in a single lex orbit.

So the classification target should be:

- identify the full list of shifted extremal orbits;
- isolate which of those are equality cases and which are merely near-equality templates.

Current `n = 5` evidence suggests the equality cases should be only:

- the full lower middle layer \(F=\binom{[n]}{m}\),
- the principal-star two-layer family
  \[
  F=
  \{A\in \binom{[n]}{m}: 0\in A\}
  \;\cup\;
  \{B\in \binom{[n]}{m+1}: 0\in B\},
  \]
  up to permutation.

This equality conjecture is now supported exactly on the shifted subproblem for both `n = 5` and
`n = 7`.

The aim should still be a stronger theorem with equality classification, but not one that assumes
there is a unique lex/shifted orbit.

### 5. Treat Sectioning As Geometric Guidance Only

For shifted \(F\), section by a coordinate \(i\), compare the `contains i` and `avoids i` slices,
and derive a recursive lower bound for \(|\partial^+F|\). The star-type equality candidates
indicate that one-coordinate sectioning is the right shape for the final argument.

This is now more concrete than before. The proof note records the exact coordinate-section
decomposition
\[
|\partial^+F|
\ge
|\partial^+(A\cup D)| + |\partial^+(B\cup E)|,
\]
where \(A\cup D\) and \(B\cup E\) are two-layer families on \([2m]\) supported on ranks
\((m-1,m)\) and \((m,m+1)\) respectively. However, both standalone reductions suggested by this
formula are now archived:

- the unrestricted even adjacent-layer theorem is false;
- the corrected coupled section theorem is also false already in exact `n = 5`.

So sectioning is no longer an active reduction theorem for the project. It remains a useful way to
organize the geometry of the problem, but the live proof search has to control the direct boundary
functional \(|\partial^+F|\) itself. The archived branch is summarized in
[STUCK_PLANS.md](./STUCK_PLANS.md).

### 5A. Try A Flux / Calibration Proof In Parallel

In parallel with the compression-first route, try to prove \((B)\) by a fractional flow from the
lower sheet \(C\) to the exposed boundary \(\partial^+F\). The target is a family of weights
\[
w_{A,B}\ge 0
\]
with
\[
\sum_B w_{A,B}=1 \quad (A\in C),
\qquad
\sum_A w_{A,B}\le 1 \quad (B\in \partial^+F),
\]
which would imply
\[
|C| \le |\partial^+F|.
\]

This route is tracked separately in
[PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md).

### 6. Use Computation Only As Structural Guidance

The search tool should be used to:

- enumerate equality and near-equality families in `n = 5`,
- inspect structured candidates in `n = 7`,
- guess the exact shifted classification.

It should not be used as a substitute for the proof.

At this point, the computational side is essentially saturated: the shifted classification is exact
in `n = 5` and `n = 7`, and the current brute-force enumerator no longer scales comfortably to
`n = 9`. So the next advance has to be a paper proof of the compression lemma / shifted theorem,
not another exhaustive search branch.

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
- uniqueness of the lex/shifted minimizer orbit,
- separate colex-formalization route as an active proof program.
