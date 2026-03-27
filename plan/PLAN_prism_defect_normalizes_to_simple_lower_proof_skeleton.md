# Proof Outline: `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerUniformUpperStatement`

This note records the current suggested proof of the stronger normalization theorem

\[
\texttt{PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerUniformUpperStatement}.
\]

Status on 2026-03-27: implemented in Lean at
[Problem1CubeHalfBoundary.lean:8065](/home/kir/pers/erdos/lean-misc/ErdosProblems/Problem1CubeHalfBoundary.lean:8065).
What follows is now the mathematical proof outline matching the formal proof, not just a conjectural
route.

The older statement

\[
\texttt{PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerStatement}
\]

is now a formal corollary of this stronger surface, because in the simple-lower model the condition

\[
\operatorname{TS}(L_m \setminus V,\; L_m \cup U) \le \operatorname{ts}(E_m)
\]

is already equivalent to

\[
\forall s \in U,\ |s| = m+1.
\]

So the real normalization target is not a raw `totalSize` transport statement. The right target is:

> normalize an arbitrary first-gap bad pair to a simple-lower bad pair whose upper part already
> lies entirely in the middle layer.

## Statement in Standard Notation

Write

- \(L_m := \{S \subseteq [2m+1] : |S| \le m\}\),
- \(E_m\) for the even witness in dimension \(2m+2\),
- \(\partial^+\) for positive boundary,
- \(\operatorname{TS}(\mathcal M,\mathcal N) := \operatorname{ts}(\operatorname{TwoSheet}(\mathcal M,\mathcal N))\).

The theorem says:

> If every simple-lower bad pair with **uniform upper layer**
> \[
> \forall s \in U,\ |s| = m+1
> \]
> is impossible, then every first-positive-gap bad pair is impossible.

Equivalently:

\[
\Bigl[\forall m,\forall U,V,\ \mathrm{SimpleLowerBad}^{\mathrm{unif}}(m;U,V)\Rightarrow \bot\Bigr]
\Longrightarrow
\Bigl[\forall m,q,e,\forall \mathcal M \subseteq \mathcal N,\ \mathrm{FirstGapBad}(m,q,e;\mathcal M,\mathcal N)\Rightarrow \bot\Bigr].
\]

Here:

### First-gap bad configuration

\[
0 < e,\qquad \mathcal M \subseteq \mathcal N \subseteq 2^{[2m+1]},
\]

\[
|\mathcal N| = 2^{2m}+e,\qquad |\mathcal M| = 2^{2m}-e,
\]

\[
(\mathcal N \setminus \mathcal M)\cap \binom{[2m+1]}{r}=\varnothing \quad (r<q),
\qquad
(\mathcal N \setminus \mathcal M)\cap \binom{[2m+1]}{q}\neq\varnothing,
\]

\[
|\partial^+\mathcal N| + |(\mathcal N\setminus\mathcal M)\cup\partial^+\mathcal M|
<
2\binom{2m+1}{m},
\]

and

\[
\operatorname{TS}(\mathcal M,\mathcal N)\le \operatorname{ts}(E_m).
\]

### Simple-lower bad configuration with uniform upper layer

\[
V \subseteq \binom{[2m+1]}{m},\qquad U \cap L_m = \varnothing,\qquad |U|=|V|,
\]

\[
|\partial^+(L_m\cup U)|
+
\left|((L_m\cup U)\setminus(L_m\setminus V))\cup\partial^+(L_m\setminus V)\right|
<
2\binom{2m+1}{m},
\]

and

\[
\forall s \in U,\ |s| = m+1.
\]

## Proof

Assume a first-gap bad pair \((\mathcal M,\mathcal N)\), so

\[
0 < e,\qquad \mathcal M \subseteq \mathcal N \subseteq 2^{[2m+1]},
\]

\[
|\mathcal N| = 2^{2m}+e,\qquad |\mathcal M| = 2^{2m}-e,
\]

\[
|\partial^+\mathcal N| + |(\mathcal N\setminus\mathcal M)\cup\partial^+\mathcal M|
<
2\binom{2m+1}{m},
\]

and

\[
\operatorname{TS}(\mathcal M,\mathcal N)\le \operatorname{ts}(E_m).
\]

Set

\[
\mathcal D := \operatorname{TwoSheet}(\mathcal M,\mathcal N)
\subseteq 2^{[2m+2]}.
\]

Then the first step is to rewrite the problem entirely in terms of the even prism family
\(\mathcal D\).

### Step 1: Prism translation

By the existing prism identities:

\[
|\mathcal D| = 2^{2m+1},
\]

\[
\operatorname{ts}(\mathcal D)=\operatorname{TS}(\mathcal M,\mathcal N),
\]

and

\[
|\partial^+\mathcal D|
=
|\partial^+\mathcal N| + |(\mathcal N\setminus\mathcal M)\cup\partial^+\mathcal M|.
\]

So \(\mathcal D\) is an even-dimensional down-set of half-cube size with

\[
|\partial^+\mathcal D| < \binom{2m+2}{m+1},
\qquad
\operatorname{ts}(\mathcal D)\le \operatorname{ts}(E_m).
\]

Moreover,

\[
|\mathcal D^{0\text{-free}}| = |\mathcal N| = 2^{2m}+e > 2^{2m},
\]

so the \(0\)-free section of \(\mathcal D\) has strict excess over half-cube size.

This means \(\mathcal D\) is already an even half-cube counterexample with a distinguished
coordinate \(0\) carrying zero-section excess.

### Step 2: Rule out lower-slice deficits below the middle

This is the key rigidity argument.

Because \(\mathcal D\) has half-cube size, any missing mass below the middle layer forces
`totalSize` to increase above the even witness. This is exactly the estimate already proved in the
file through the theorem

\[
\texttt{totalSize\_evenLowerHalfFamily\_lt\_of\_card\_eq\_half\_cube\_of\_lower\_slice\_deficit}.
\]

So if there were some \(r \le m\) such that

\[
|\mathcal D \cap \binom{[2m+2]}{r}| < \binom{2m+2}{r},
\]

then one would get

\[
\operatorname{ts}(E_m) < \operatorname{ts}(\mathcal D),
\]

contradicting the badness assumption.

Therefore \(\mathcal D\) has **all lower slices full up to the middle**:

\[
|\mathcal D \cap \binom{[2m+2]}{r}| = \binom{2m+2}{r}
\qquad (0 \le r \le m).
\]

### Step 3: Deduce simple-lower shape from full lower slices

Set

\[
L_m := \{S\subseteq [2m+1]: |S|\le m\},
\qquad
U := \mathcal N \setminus L_m,
\qquad
V := L_m \setminus \mathcal M,
\qquad
W := \mathcal M \setminus L_m.
\]

The full lower-slice identities for \(\mathcal D\) imply:

\[
|\mathcal M \cap \tbinom{[2m+1]}{r}| = \binom{2m+1}{r}
\quad (r<m),
\]

and

\[
|\mathcal N \cap \tbinom{[2m+1]}{r}| = \binom{2m+1}{r}
\quad (1\le r\le m).
\]

Hence every set of size at most \(m\) lies in \(\mathcal N\), i.e.

\[
L_m \subseteq \mathcal N.
\]

So

\[
\mathcal N = L_m \cup U.
\]

Likewise, every set in \(V\) must lie in the middle layer:

\[
V \subseteq \binom{[2m+1]}{m}.
\]

Also

\[
\mathcal M = (L_m\setminus V)\cup W,
\]

with \(W\cap L_m=\varnothing\), so every set in \(W\) has size at least \(m+1\).

\[
\mathcal N = L_m \cup U,
\qquad
\mathcal M = (L_m\setminus V)\cup W.
\]

The cardinality identities give

\[
\lvert U\rvert = e,
\qquad
\lvert V\rvert = e + \lvert W\rvert.
\]

Now compare `totalSize` on both sides. Since every set in \(U\) and \(W\) has size at least
\(m+1\), and every set in \(V\) has size exactly \(m\), one gets the lower bounds

\[
\operatorname{ts}(\mathcal N)\ge \operatorname{ts}(L_m) + (m+1)\lvert U\rvert,
\]

\[
\operatorname{ts}(\mathcal M)+|\mathcal M|
+ (m+1)\lvert V\rvert
\ge
\operatorname{ts}(L_m)+|L_m| + (m+2)\lvert W\rvert.
\]

Combining these with

\[
\lvert U\rvert = e,\qquad \lvert V\rvert = e+\lvert W\rvert
\]

and

\[
\operatorname{ts}(E_m)=2\,\operatorname{ts}(L_m)+|L_m|,
\qquad
\operatorname{TS}(\mathcal M,\mathcal N)
=
\operatorname{ts}(\mathcal N)+\operatorname{ts}(\mathcal M)+|\mathcal M|,
\]

one obtains

\[
\operatorname{ts}(E_m)+|W|
\le
\operatorname{TS}(\mathcal M,\mathcal N).
\]

But by assumption

\[
\operatorname{TS}(\mathcal M,\mathcal N)\le \operatorname{ts}(E_m),
\]

so \(|W|=0\). Therefore \(W=\varnothing\), and hence

\[
\mathcal M = L_m\setminus V.
\]

This is the simple-lower normalization.

### Step 4: Force the upper part to lie in the middle layer

At this point the simple-lower algebra already proved in the file applies:

\[
\operatorname{ts}\bigl(\operatorname{TwoSheet}(L_m\setminus V,\; L_m\cup U)\bigr)
\le
\operatorname{ts}(E_m)
\iff
\forall s \in U,\ |s|=m+1.
\]

But the left-hand side holds because

\[
\operatorname{TwoSheet}(L_m\setminus V,\; L_m\cup U)=\mathcal D
\]

after the normalization of Step 5, and \(\mathcal D\) was assumed to satisfy

\[
\operatorname{ts}(\mathcal D)\le \operatorname{ts}(E_m).
\]

Hence automatically:

\[
\forall s \in U,\ |s|=m+1.
\]

So the “uniform upper” part of the target is not an extra burden once the simple-lower shape is
identified.

### Step 5: Transfer the defect inequality

The boundary defect now transfers by the exact prism identity:

\[
|\partial^+\mathcal D|
=
|\partial^+(L_m\cup U)|
+
\left|((L_m\cup U)\setminus(L_m\setminus V))\cup\partial^+(L_m\setminus V)\right|.
\]

Since \(|\partial^+\mathcal D| < \binom{2m+2}{m+1} = 2\binom{2m+1}{m}\), the normalized pair
\((L_m\setminus V,\; L_m\cup U)\) is a simple-lower bad pair with uniform upper layer.

### Step 6: Contradiction

Apply the assumed simple-lower impossibility statement to \((U,V)\).

This yields a contradiction, so the original first-gap bad pair cannot exist.

## Outcome

This proof is now implemented. The normalization theorem is no longer a speculative route: it is a
proved reduction from the general first-gap defect configuration to the simple-lower uniform-upper
configuration.

As a consequence, the remaining live subgoal in the overall prism program is no longer any
normalization statement. It is the simple-lower local theorem

\[
\texttt{SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement}.
\]
