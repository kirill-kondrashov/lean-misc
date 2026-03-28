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

## Current Plan Snapshot

The current plan is:

1. Keep the live target at the reduced middle-layer inequality
   \[
   |\partial^\uparrow U| \ge |T(V)\setminus U|.
   \]
2. Use one of the live routes:
   - a weaker extremal/colex reduction from general \((U,V)\) to canonical equal-size middle-layer
     pairs;
   - or a direct counting proof of the reduced inequality.
   The best current live conjecture is the weaker colex route:
   first reduce to equal-size colex middle-layer pairs \((U^\ast,V^\ast)\), then prove
   \[
   T(V^\ast)\subseteq U^\ast.
   \]
   That compressed-case theorem is now proved mathematically in
   [PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md),
   but its direct Lean formalization is currently stuck and should not be treated as a theorem that
   already exists in the codebase.
3. Archived stuck routes are tracked separately in
   [STUCK_PLANS.md](./STUCK_PLANS.md).
4. Once that reduced inequality is proved, use the already-formalized Lean equivalence layer to
   recover
   `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`,
   `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`,
   the canonical defect bottleneck, and the exact Erdős #1 endpoint under the current frontier.

So the remaining work is no longer theorem packaging. It is one new middle-layer combinatorial
argument.

## Archived Routes

Stuck plan branches are recorded separately in
[STUCK_PLANS.md](./STUCK_PLANS.md).

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

### 2. Pursue a weaker extremal reduction

For fixed

\[
|U| = |V| = e,
\]

the active subgoal is to find a weaker extremal reduction from general \((U,V)\) to colex
equal-size middle-layer pairs, or else bypass reduction entirely and prove

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

This remains computationally plausible, but it is not yet a full proof route by itself, because the
general-to-colex reduction is still missing.

Current computational evidence is stronger than this:

- for all colex initial segments in odd dimensions \(n=7,9,11\),
  with
  \[
  U^\ast \subseteq \binom{[n]}{(n+1)/2},
  \qquad
  V^\ast \subseteq \binom{[n]}{(n-1)/2},
  \qquad
  |U^\ast|=|V^\ast|=e,
  \]
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

This stronger statement is now proved mathematically in
[PROOF_colex_equal_size_middle_layer_containment.md](./PROOF_colex_equal_size_middle_layer_containment.md).
Therefore the reduced inequality is immediate in the compressed case on paper. The direct Lean
formalization attempt is currently archived in
[STUCK_PLANS.md](./STUCK_PLANS.md).

### 4. Use computation to guess the exact extremizers

Extend the existing `n=7` search tooling so it reports:

- \(|\partial^\uparrow U|\),
- \(|T(V)|\),
- \(|T(V)\setminus U|\),
- and the corresponding compressed candidate.

This step is now partially implemented. The tooling has dedicated `n=7` diagnostics for:

- exact structured uniform-upper classes,
- colex initial middle-layer pairs in `n=7`,
- and summary checks for colex initial middle-layer pairs in odd dimensions `n=7,9,11`.

Current evidence:

- no exact structured `n=7` simple-lower defect candidate,
- tightest zero-gain class `single-4`,
- boundary margin `73 - 70 = 3`.
- all searched structured uniform-upper classes satisfy
  \[
  |\partial^\uparrow U| \ge |T(V)\setminus U|
  \]
  with margins \(3,5,6\);
- all colex samples in `n=7,9,11` satisfy the stronger property
  \[
  T(V)\setminus U=\varnothing.
  \]

The sharpest current replacement route is therefore:

1. prove a weaker extremal reduction from general \((U,V)\) to colex equal-size middle-layer
   pairs, without using the false naive monotonicity;
2. use the mathematically proved colex containment theorem
   \[
   T(V^\ast)\subseteq U^\ast;
   \]
3. conclude the reduced inequality in the compressed case on paper, and then in general once the weaker
   reduction is established:
   \[
    |\partial^\uparrow U| \ge |T(V)\setminus U|.
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
