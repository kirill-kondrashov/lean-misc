# Proof Skeleton: `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerStatement`

This note records the mathematical meaning of the remaining normalization subgoal and a plausible
proof route for implementing it in Lean.

## Target Statement

Write

- \(L_m := \{ S \subseteq [2m+1] : |S| \le m \}\) for the odd lower half,
- \(E_m\) for the even witness,
- \(\partial^+\) for positive boundary,
- \(\operatorname{ts}(\cdot)\) for `totalSize`,
- \(\operatorname{TS}(\mathcal M,\mathcal N) := \operatorname{ts}(\operatorname{TwoSheet}(\mathcal M,\mathcal N))\).

The normalization statement says:

> If every **simple-lower** counterexample is impossible, then every **first-positive-gap**
> counterexample is impossible.

More explicitly:

\[
\Bigl[\forall m,\forall U,V,\ \mathrm{SimpleLowerBad}(m;U,V)\Rightarrow \bot\Bigr]
\Longrightarrow
\Bigl[\forall m,q,e,\forall \mathcal M \subseteq \mathcal N,\ \mathrm{FirstGapBad}(m,q,e;\mathcal M,\mathcal N)\Rightarrow \bot\Bigr].
\]

Here:

### Simple-lower bad configuration

\[
V \subseteq \binom{[2m+1]}{m}, \qquad U \cap L_m = \varnothing, \qquad |U| = |V|,
\]

\[
|\partial^+(L_m \cup U)|
+
\left| ((L_m \cup U) \setminus (L_m \setminus V)) \cup \partial^+(L_m \setminus V) \right|
<
2 \binom{2m+1}{m},
\]

and

\[
\operatorname{TS}(L_m \setminus V,\; L_m \cup U) \le \operatorname{ts}(E_m).
\]

### First-positive-gap bad configuration

\[
0 < e, \qquad \mathcal M \subseteq \mathcal N \subseteq 2^{[2m+1]},
\]

\[
|\mathcal N| = 2^{2m} + e, \qquad |\mathcal M| = 2^{2m} - e,
\]

\[
(\mathcal N \setminus \mathcal M) \cap \binom{[2m+1]}{r} = \varnothing
\quad \text{for all } r < q,
\]

\[
(\mathcal N \setminus \mathcal M) \cap \binom{[2m+1]}{q} \neq \varnothing,
\]

\[
|\partial^+\mathcal N| + \left|(\mathcal N \setminus \mathcal M)\cup \partial^+\mathcal M\right|
<
2 \binom{2m+1}{m},
\]

and

\[
\operatorname{TS}(\mathcal M,\mathcal N) \le \operatorname{ts}(E_m).
\]

So the desired normalization theorem is:

> Given a first-positive-gap bad pair \((\mathcal M,\mathcal N)\), construct a simple-lower bad
> pair \((L_m \setminus V,\, L_m \cup U)\).

## Intended Construction

The natural normalization target is

\[
\mathcal M' := L_m \setminus V, \qquad \mathcal N' := L_m \cup U,
\]

where:

- \(V\) records the missing middle-layer sets removed from \(L_m\),
- \(U\) records the upper-layer sets added above \(L_m\).

The construction should satisfy:

\[
V \subseteq \binom{[2m+1]}{m}, \qquad U \cap L_m = \varnothing, \qquad |U| = |V| = e,
\]

and preserve the two properties needed for contradiction:

1. the pair-interface defect inequality,
2. the no-larger-prism inequality
   \(\operatorname{TS}(\mathcal M',\mathcal N') \le \operatorname{ts}(E_m)\).

## Proof Skeleton

Assume a first-positive-gap bad pair \((\mathcal M,\mathcal N)\).

### Step 1: Identify the lower-half baseline

Show that the cardinal constraints

\[
|\mathcal N| = 2^{2m} + e, \qquad |\mathcal M| = 2^{2m} - e
\]

mean that \((\mathcal M,\mathcal N)\) differs from the half-cube baseline by exactly \(e\) upward
moves and \(e\) downward removals.

Expected Lean output:

- a decomposition of the relevant layers into a lower-half core plus a deficit part \(V\) and an
  upper excess part \(U\),
- cardinal equalities such as \(|U| = |V|\).

### Step 2: Normalize to simple-lower shape

Construct \(U\) and \(V\) so that

\[
\mathcal M' = L_m \setminus V, \qquad \mathcal N' = L_m \cup U.
\]

Show:

\[
V \subseteq \binom{[2m+1]}{m}, \qquad U \cap L_m = \varnothing.
\]

Expected Lean output:

- a theorem that every normalized deficit sits in the middle layer,
- a theorem that every normalized excess sits strictly above the middle layer,
- a theorem that the normalized pair has the same section-cardinality gap as the original pair.

### Step 3: Transfer the first-gap defect to the normalized pair

Prove that the strict boundary defect survives normalization:

\[
|\partial^+\mathcal N'| + \left|(\mathcal N' \setminus \mathcal M') \cup \partial^+\mathcal M'\right|
\le
|\partial^+\mathcal N| + \left|(\mathcal N \setminus \mathcal M) \cup \partial^+\mathcal M\right|.
\]

Since the right-hand side is \(< 2\binom{2m+1}{m}\), this yields the simple-lower defect.

This is the most delicate part. The proof likely needs either:

- a compression/minimality argument showing normalization cannot increase the pair-interface
  boundary, or
- an exact slice-by-slice rewrite showing the defect quantity depends only on the normalized
  deficit/excess data.

Expected Lean output:

- a monotonicity lemma or exact identity for the pair-interface defect under the normalization.

### Step 4: Collapse the no-larger-prism condition to a uniform-upper condition

This step is easier than a raw `totalSize` transport inequality.

The existing simple-lower algebra already proves:

\[
\operatorname{TS}(L_m \setminus V,\; L_m \cup U) \le \operatorname{ts}(E_m)
\iff
\forall s \in U,\ |s| = m+1.
\]

So on the normalized side, the no-larger-prism hypothesis is equivalent to saying that every
upper-sheet set lies exactly on the middle layer.

Therefore the normalization problem can be strengthened as follows:

> it is enough to normalize a first-gap bad pair to a simple-lower bad pair
> \((L_m \setminus V,\; L_m \cup U)\) with
> \[
> \forall s \in U,\ |s| = m+1.
> \]

Then the inequality
\[
\operatorname{TS}(L_m \setminus V,\; L_m \cup U) \le \operatorname{ts}(E_m)
\]
holds automatically, by the already proved simple-lower `totalSize` equivalence.

So the transport burden is not really:

\[
\operatorname{TS}(\mathcal M',\mathcal N') \le \operatorname{TS}(\mathcal M,\mathcal N).
\]

Instead it is:

\[
\text{construct the normalized upper part } U \text{ entirely in rank } m+1.
\]

Expected Lean output:

- a stronger normalization theorem reducing the target to the simple-lower
  `uniform upper` contradiction surface,
- rather than a direct theorem transporting a raw `totalSize` inequality.

### Step 5: Invoke the simple-lower contradiction surface

Now \((U,V)\) satisfies the simple-lower bad hypotheses, so by the assumed theorem

\[
\forall m,\forall U,V,\ \mathrm{SimpleLowerBad}(m;U,V)\Rightarrow \bot,
\]

we obtain a contradiction.

Therefore no first-positive-gap bad pair exists.

## Minimal Lean Sublemma Checklist

The likely implementation path is to prove the normalization statement from the following local
lemmas.

1. `firstGap_bad_pair_has_simpleLower_card_profile`

   From the original hypotheses, construct \(U,V\) with
   \[
   V \subseteq \binom{[2m+1]}{m}, \qquad U \cap L_m = \varnothing, \qquad |U| = |V|.
   \]

2. `firstGap_bad_pair_normalizes_to_simpleLower_boundary_defect`

   Transfer
   \[
   |\partial^+\mathcal N| + |(\mathcal N \setminus \mathcal M)\cup \partial^+\mathcal M|
   <
   2 \binom{2m+1}{m}
   \]
   to the normalized pair.

3. `firstGap_bad_pair_normalizes_to_simpleLower_uniform_upper`

   Construct the normalized upper part so that
   \[
   \forall s \in U,\ |s| = m+1.
   \]

   Then the simple-lower no-larger-prism hypothesis follows automatically from the existing
   algebraic equivalence.

4. `firstGap_bad_pair_normalizes_to_simpleLower`

   Bundle the previous three lemmas into the exact implication
   `PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerStatement`.

## Tactical Interpretation

This theorem does not itself prove the prism bottleneck. It isolates the remaining abstract
normalization burden:

- convert an arbitrary first-gap defect counterexample into the simple-lower model,
- keep both the defect inequality and the non-larger-prism inequality intact,
- then apply the already isolated simple-lower contradiction theorem.

If this normalization is achieved, the remaining proof burden is entirely concentrated in the
simple-lower statement

\[
\mathrm{SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddle}.
\]
