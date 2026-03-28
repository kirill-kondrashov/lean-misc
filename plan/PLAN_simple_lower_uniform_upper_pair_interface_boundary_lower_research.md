# Research Plan: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note records the current research plan for proving
`SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`.

## Main Target

Let

\[
n := 2m+1,
\qquad
L_m := \{S \subseteq [n] : |S| \le m\}.
\]

Let

\[
V \subseteq \binom{[n]}{m},
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
|U| = |V|.
\]

Define

\[
M := L_m \setminus V,
\qquad
N := L_m \cup U.
\]

The theorem to prove is

\[
|\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
\ge
2\binom{2m+1}{m}.
\]

## Reduced Middle-Layer Form

The statement has already been reduced to the inequality

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\]

where:

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

So the remaining work is a pure middle-layer combinatorial inequality.

## Standalone Proof Attempt

The compression-route proof attempt for the reduced inequality is recorded separately in
[PLAN_middle_layer_compression_monotonicity_proof_attempt.md](./PLAN_middle_layer_compression_monotonicity_proof_attempt.md).

That note writes down the conjectural badness functional

\[
\Delta(U,V) := |T(V)\setminus U| - |\partial^\uparrow U|
\]

and the originally proposed compression strategy:

\[
\Delta(U,V) \le \Delta(C_{ij}U,\; C_{ij}V).
\]

That route is now known to fail. The separate note records an explicit \(n=7\) counterexample to
both the strong inclusion

\[
C_{ij}\bigl(T(V)\setminus U\bigr) \subseteq T(C_{ij}V)\setminus C_{ij}U
\]

and the weaker monotonicity claim

\[
\Delta(U,V) \le \Delta(C_{ij}U,\; C_{ij}V).
\]

So the standalone note should now be read as a falsified proof attempt rather than as a live proof
program.

## Why This Is The Right Route

The Lean development already proves:

\[
\texttt{SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement}
\iff
\texttt{SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement}.
\]

It also already proves the normalization theorem reducing the general odd first-gap bottleneck to
the simple-lower uniform-upper regime. So no more theorem-graph packaging is needed. The only
missing content is the reduced middle-layer inequality.

## Research Steps

### 1. Recast the problem as a graph inequality

Work in the balanced bipartite inclusion graph

\[
\binom{[2m+1]}{m}
\leftrightarrow
\binom{[2m+1]}{m+1}.
\]

Interpret:

- \(T(V)\) as the set of right vertices whose full neighborhood lies in \(V\),
- \(\partial^\uparrow U\) as the upper shadow of \(U\) into rank \(m+2\).

The goal is then to compare a clique-style family on the right with the upper shadow of a family of
the same size.

### 2. Replace the falsified compression route

The old working conjecture was that for fixed

\[
|U| = |V| = e,
\]

the minimum of

\[
|\partial^\uparrow U| - |T(V)\setminus U|
\]

is attained by compressed / colex-initial configurations.

That exact reduction is false: the direct left-compression monotonicity fails already in the
explicit \(n=7\) example from the standalone note.

So the new subgoal is to replace the failed route with one of:

- a different monotone defect functional,
- a weaker extremal reduction that does not use the false monotonicity,
- or a direct non-compression proof of
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|.
  \]

### 3. Compute the compressed extremizers explicitly

For compressed initial segments \(U^\ast, V^\ast\), compute:

\[
|\partial^\uparrow U^\ast|,
\qquad
|T(V^\ast)|,
\qquad
|T(V^\ast)\setminus U^\ast|.
\]

The expected outcome was

\[
|\partial^\uparrow U^\ast| \ge |T(V^\ast)\setminus U^\ast|.
\]

This remains computationally plausible, but it is no longer enough by itself, because the failed
compression step no longer reduces the general case to the compressed case.

Current `n=7` evidence is stronger than this:

- for all colex initial segments \(U^\ast \subseteq \binom{[7]}{4}\),
  \(V^\ast \subseteq \binom{[7]}{3}\) with \(|U^\ast|=|V^\ast|=e\),
  the search data gives
  \[
  T(V^\ast)\subseteq U^\ast,
  \]
  hence
  \[
  T(V^\ast)\setminus U^\ast = \varnothing.
  \]

So the current compressed-model conjecture can be sharpened:

> for equal-size colex initial segments in the balanced middle layers,
> \[
> T(V^\ast)\subseteq U^\ast.
> \]

If this stronger statement is true in general, then the reduced inequality is immediate in the
compressed case.

### 4. Use computation to guess the exact extremizers

Extend the existing `n=7` search tooling so it reports:

- \(|\partial^\uparrow U|\),
- \(|T(V)|\),
- \(|T(V)\setminus U|\),
- and the corresponding compressed candidate.

This step is now partially implemented. The tooling has dedicated `n=7` diagnostics for:

- exact structured uniform-upper classes,
- and colex initial middle-layer pairs.

Current evidence:

- no exact structured `n=7` simple-lower defect candidate,
- tightest zero-gain class `single-4`,
- boundary margin `73 - 70 = 3`.
- all searched structured uniform-upper classes satisfy
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|
  \]
  with margins \(3,5,6\);
- all colex `n=7` samples satisfy the stronger property
  \[
  T(V)\setminus U=\varnothing.
  \]

So the search evidence supports the theorem and can be used to guess the real extremal families.

### 5. Prove a sharper intermediate inequality if needed

A plausible intermediate theorem is

\[
|T(V)| \le |\partial^\uparrow U| + |U|
\qquad\text{whenever } |U|=|V|.
\]

Since

\[
|T(V)\setminus U| = |T(V)| - |T(V)\cap U| \le |T(V)|,
\]

this would already imply the target inequality if the overlap is handled correctly.

So one reasonable tactical split is:

1. prove
   \[
   |T(V)| \le |\partial^\uparrow U| + |U|,
   \]
2. then refine it to the exact
   \[
   |T(V)\setminus U| \le |\partial^\uparrow U|.
   \]

### 6. Only then formalize in Lean

Once the paper proof is clear, encode the result as a standalone theorem feeding
`SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`. After that, the existing Lean
equivalences close:

- the simple-lower defect theorem,
- the canonical defect bottleneck,
- the prism theorem route,
- and the exact Erdős #1 endpoint under the current frontier.

## Practical Success Criterion

The plan is successful once one of the following is achieved:

1. a replacement extremal reduction to a provable compressed model, together with an explicit count
   in that reduced case; or
2. a direct middle-layer counting lemma proving
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|.
   \]

Either one is enough to finish the current bottleneck.

## Current Status

This plan is partially implemented:

- the reduced middle-layer inequality has been isolated,
- the structured `n=7` uniform-upper diagnostics have been added,
- and the colex `n=7` diagnostics still suggest the stronger compressed containment
  \[
  T(V^\ast)\subseteq U^\ast.
  \]

The project is still stuck mathematically, and the blocker is now sharper than before:

1. the naive compression monotonicity route is false and cannot be repaired by proving the old
   conjecture;
2. the next live task is to find a replacement reduction or a direct proof of
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|.
   \]
