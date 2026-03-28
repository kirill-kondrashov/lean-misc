# Proof Note: `SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement`

This note records the mathematical formulation of
`SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement` and a plausible proof
route in standard notation. It is a research note, not a formal proof.

## Statement

Write

\[
n := 2m+1,
\qquad
L_m := \{S \subseteq [n] : |S| \le m\}.
\]

Let

\[
V \subseteq \binom{[n]}{m},
\qquad
U \cap L_m = \varnothing,
\qquad
|U| = |V|.
\]

Define

\[
M := L_m \setminus V,
\qquad
N := L_m \cup U.
\]

Then the theorem says:

> If
> \[
> |\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
> <
> 2 \binom{2m+1}{m},
> \]
> then there exists some \(s \in U\) such that
> \[
> |s| > m+1.
> \]

Equivalently, in contrapositive form:

> If every set in \(U\) has cardinality exactly \(m+1\), then
> \[
> |\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
> \ge
> 2 \binom{2m+1}{m}.
> \]

Since \(U \cap L_m = \varnothing\), every \(s \in U\) automatically satisfies \(|s| \ge m+1\). So
the content is that a strict boundary defect forces some set of \(U\) to lie strictly above the
middle layer.

## Equivalent Forms Already Present In Lean

The file [Problem1CubeHalfBoundary.lean](/home/kir/pers/erdos/lean-misc/ErdosProblems/Problem1CubeHalfBoundary.lean)
already proves that this statement is equivalent to the following two forms.

### Larger-prism form

\[
|\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
<
2 \binom{2m+1}{m}
\Longrightarrow
\operatorname{ts}(\operatorname{TwoSheet}(M,N)) > \operatorname{ts}(E_m).
\]

### Uniform-upper impossibility form

If

\[
|\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
<
2 \binom{2m+1}{m},
\]

then it is impossible that

\[
\forall s \in U,\quad |s| = m+1.
\]

So the theorem can be attacked either as a direct boundary statement or as a contradiction theorem
for the uniform-upper regime.

As of 2026-03-28, Lean also has the explicit contrapositive boundary-lower surface

\[
\texttt{SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement},
\]

and proves

\[
\texttt{SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement}
\iff
\texttt{SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement}.
\]

So the remaining live subgoal is no longer implicit: it is exactly the uniform-upper pair-interface
boundary lower bound.

## Useful Identities

In the simple-lower model one already has the exact total-size identity

\[
\operatorname{ts}(\operatorname{TwoSheet}(L_m \setminus V,\; L_m \cup U))
=
\operatorname{ts}(E_m)
+
\operatorname{ts}(U)
-
(m+1)|U|.
\]

Hence:

\[
\operatorname{ts}(\operatorname{TwoSheet}(L_m \setminus V,\; L_m \cup U))
>
\operatorname{ts}(E_m)
\iff
\operatorname{ts}(U) > (m+1)|U|.
\]

And since \(U \cap L_m = \varnothing\), every \(s \in U\) has \(|s| \ge m+1\), so

\[
\operatorname{ts}(U) > (m+1)|U|
\iff
\exists s \in U,\quad |s| > m+1.
\]

Thus the theorem really says:

> a strict pair-interface boundary defect forces positive weighted upper-tail gain.

## Proposed Proof Route

The cleanest route appears to be the contrapositive.

Assume from now on that

\[
U \subseteq \binom{[n]}{m+1}.
\]

We must show

\[
|\partial^+ N| + |(N \setminus M)\cup \partial^+ M|
\ge
2\binom{n}{m}.
\]

Because \(n=2m+1\), we have

\[
\binom{n}{m} = \binom{n}{m+1}.
\]

So the target is naturally a middle-layer statement.

### Step 1: Rewrite the defect functional

Define

\[
\Phi(U,V)
:=
|\partial^+(L_m \cup U)| + |(U \cup V)\cup \partial^+(L_m \setminus V)|.
\]

Since \(N \setminus M = U \cup V\), the theorem becomes the claim

\[
U \subseteq \binom{[n]}{m+1},\ |U|=|V|
\Longrightarrow
\Phi(U,V)\ge 2\binom{n}{m}.
\]

### Step 2: Compute the boundary terms in the uniform-upper regime

Under the uniform-upper assumption \(U \subseteq \binom{[n]}{m+1}\):

- every missing \((m+1)\)-set lies in \(\partial^+(L_m \cup U)\), so
  \[
  \binom{[n]}{m+1}\setminus U \subseteq \partial^+(L_m \cup U);
  \]
- the only other elements of \(\partial^+(L_m \cup U)\) occur in rank \(m+2\), namely the upper
  shadow
  \[
  \partial^\uparrow U := \{T \in \tbinom{[n]}{m+2} : \exists s \in U,\ s \subset T\};
  \]
- every member of \(V\) lies in \(\partial^+(L_m \setminus V)\), because all of its
  \((m-1)\)-subsets still lie in \(L_m \setminus V\).

So in fact

\[
\partial^+(L_m \cup U)
=
\left(\binom{[n]}{m+1}\setminus U\right) \sqcup \partial^\uparrow U.
\]

For the second term, define

\[
T(V)
:=
\left\{B \in \binom{[n]}{m+1} : \binom{B}{m} \subseteq V\right\}.
\]

Then a rank-\((m+1)\) set belongs to \(\partial^+(L_m \setminus V)\) iff not all of its
\(m\)-subsets were removed, i.e.

\[
\partial^+(L_m \setminus V)\cap \binom{[n]}{m+1}
=
\binom{[n]}{m+1}\setminus T(V).
\]

Since \(L_m \setminus V\) has no sets above rank \(m\), there is no higher-rank contribution, so

\[
\partial^+(L_m \setminus V)=\binom{[n]}{m+1}\setminus T(V).
\]

Hence

\[
\Phi(U,V)
=
\left(\binom{n}{m+1}-|U|\right)
+
|\partial^\uparrow U|
+
|U \cup V \cup (\tbinom{[n]}{m+1}\setminus T(V))|.
\]

Because \(V\) lies in rank \(m\) and \(U, \binom{[n]}{m+1}\setminus T(V)\) lie in rank \(m+1\),
this simplifies to

\[
\Phi(U,V)
=
\binom{n}{m+1}
+
|\partial^\uparrow U|
+
\left|U \cup \left(\binom{[n]}{m+1}\setminus T(V)\right)\right|.
\]

Since \(\binom{n}{m+1}=\binom{n}{m}\), this becomes

\[
\Phi(U,V)
=
2\binom{n}{m}
+
|\partial^\uparrow U|
-
|T(V)\setminus U|.
\]

Therefore the desired lower bound is equivalent to the sharp inequality

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|.
\]

This is the exact reduced middle-layer statement now blocking the proof.

### Step 3: Interpret the reduced inequality

The two terms have natural graph meanings:

- \(\partial^\uparrow U\) is the upper shadow of the \((m+1)\)-uniform family \(U\) into rank
  \(m+2\);
- \(T(V)\) is the family of \((m+1)\)-sets whose entire \(m\)-shadow lies in \(V\), i.e. the
  \((m+1)\)-cliques supported by the \(m\)-uniform family \(V\).

So the theorem reduces to:

> for families \(U \subseteq \binom{[n]}{m+1}\), \(V \subseteq \binom{[n]}{m}\) with
> \(|U|=|V|\), the upper shadow of \(U\) dominates the clique family generated by \(V\), up to the
> trivial overlap with \(U\) itself.

### Step 4: Pass to the middle-layer bipartite graph

Consider the bipartite inclusion graph

\[
G_{m,m+1}
\subseteq
\binom{[n]}{m} \times \binom{[n]}{m+1},
\]

where \(A \sim B\) iff \(A \subset B\).

This graph is regular on both sides:

\[
\deg(A) = m+1
\quad (A \in \tbinom{[n]}{m}),
\qquad
\deg(B) = m+1
\quad (B \in \tbinom{[n]}{m+1}),
\]

because \(n=2m+1\). In particular, Hall's inequality gives

\[
|\Gamma(\mathcal A)| \ge |\mathcal A|
\qquad
(\mathcal A \subseteq \tbinom{[n]}{m}),
\]

where \(\Gamma(\mathcal A)\) is the upper shadow in the \((m+1)\)-layer.

Now set

\[
\mathcal A := \binom{[n]}{m} \setminus V.
\]

Then the \((m+1)\)-part of \(\partial^+(L_m \setminus V)\) is exactly \(\Gamma(\mathcal A)\). So
the second term in \(\Phi(U,V)\) contains

\[
V \cup U \cup \Gamma(\mathcal A).
\]

Since \(V\) lies in rank \(m\) and \(U,\Gamma(\mathcal A)\) lie in rank \(m+1\), this gives

\[
|(U \cup V)\cup \partial^+(L_m \setminus V)|
\ge
|V| + |U \cup \Gamma(\mathcal A)|.
\]

### Step 5: Compression conjecture

The remaining difficulty is to bound

\[
|U \cup \Gamma(\mathcal A)|
\]

from below by a quantity strong enough to force \(\Phi(U,V)\ge 2\binom{n}{m}\).

The plausible route is:

1. apply standard compressions inside the two middle layers,
2. show these compressions do not increase \(\Phi(U,V)\),
3. reduce to a canonical colex-compressed pair \((U^\ast,V^\ast)\),
4. compute \(\Phi(U^\ast,V^\ast)\) explicitly.

The expected extremal picture is that, for fixed \(|U|=|V|=e\), the minimum of \(\Phi(U,V)\) among
uniform-upper pairs occurs when

\[
V^\ast
\]

is an initial segment of \(\binom{[n]}{m}\) in colex order and

\[
U^\ast
\]

is the corresponding initial segment of \(\binom{[n]}{m+1}\) under the symmetric middle-layer
matching. In that canonical situation, one expects an exact count

\[
\Phi(U^\ast,V^\ast) = 2\binom{n}{m}.
\]

If this compression statement is true, then automatically

\[
\Phi(U,V)\ge \Phi(U^\ast,V^\ast)=2\binom{n}{m},
\]

which proves the contrapositive.

## Why The Current Lean Development Is Stuck Here

The Lean file already proves the algebraic equivalences

\[
\Phi(U,V) < 2\binom{n}{m}
\iff
\operatorname{ts}(\operatorname{TwoSheet}(L_m\setminus V,\;L_m\cup U))
>
\operatorname{ts}(E_m)
\]

and

\[
\operatorname{ts}(\operatorname{TwoSheet}(L_m\setminus V,\;L_m\cup U))
>
\operatorname{ts}(E_m)
\iff
\exists s \in U,\quad |s|>m+1.
\]

So once the uniform-upper contradiction

\[
U \subseteq \binom{[n]}{m+1}
\Longrightarrow
\Phi(U,V)\ge 2\binom{n}{m}
\]

is established by a middle-layer argument, the rest of the theorem is already formalized.

At this point the obstruction is not theorem-graph plumbing. It is exactly the missing inequality

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|,
\]

or an equivalent compression/isoperimetric statement on the balanced middle layers.

## Practical Research Sublemma

The sharp missing middle-layer estimate can be isolated as follows.

Let

\[
\mathcal A := \binom{[n]}{m}\setminus V,
\qquad
\Psi(U,V)
:=
\left|\binom{[n]}{m+1}\setminus U\right|
+
|U \cup \Gamma(\mathcal A)|
+
|V|.
\]

Then

\[
\Phi(U,V)\ge \Psi(U,V),
\]

so it is enough to prove

\[
\Psi(U,V)\ge 2\binom{n}{m}
\qquad
\text{whenever } U \subseteq \binom{[n]}{m+1},\ |U|=|V|.
\]

This reduces the theorem to a pure incidence inequality in the balanced bipartite graph
\(G_{m,m+1}\).

## Status

This note gives the exact reduction, but not yet a finished proof. The likely missing ingredient
is a compression or isoperimetric lemma on the balanced middle-layer graph

\[
\binom{[2m+1]}{m}
\leftrightarrow
\binom{[2m+1]}{m+1}.
\]

Structured evidence is still favorable: the exact `n=7` structured simple-lower search finds no
uniform-upper defect candidate, and its tightest zero-gain class is `single-4` with boundary
margin \(73-70=3\). But the general proof remains stuck at the middle-layer inequality above.
