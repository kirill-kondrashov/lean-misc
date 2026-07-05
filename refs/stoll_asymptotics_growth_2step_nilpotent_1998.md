# Stoll (1998) — reference stub (paywalled primary; PDF not redistributable)

**Michael Stoll.** *On the asymptotics of the growth of 2-step nilpotent groups.*
Journal of the London Mathematical Society (2), **58** (1998), no. 1, 38–48.
DOI: [10.1112/S0024610798006371](https://doi.org/10.1112/S0024610798006371)

> **Note on availability.** This is a copyrighted journal article behind a paywall
> (Cambridge University Press / LMS). No free author-hosted PDF exists on Michael
> Stoll's homepage (`mathe2.uni-bayreuth.de/stoll/schrift.html` lists it with only a
> DOI link). We therefore do **not** redistribute the PDF here. The precise
> statements we depend on are recorded below, sourced from their verbatim
> restatement in Bodart's paper (`bodart_intermediate_geodesic_growth_virtually_nilpotent_2025.pdf`,
> openly available as arXiv:2306.10381v3, in this folder), which is a legitimate
> secondary source we may quote for statements.

## What we need from Stoll (as used by Bodart §1)

Setting: `H̄` a simply connected nilpotent Lie group, `X` a finite Lie generating
set, `σ : X → ℤ_{>0}` a weight function. `X_R^*` = the "real words" (R-words)
allowing real exponents on generators; `ℓ_σ(w)` the weighted length.

- **Definition 1.3 (Stoll metric).**
  `‖h‖_{Stoll,X,σ} = inf { ℓ_σ(w) | w ∈ X_R^*, w = h }`.
  Since `X^* ⊆ X_R^*`, one always has `‖h‖_{X,σ} ≥ ‖h‖_{Stoll,X,σ}`.

- **Lemma 1.4 (Minkowski-norm form).** On the abelianization `ℝ^d`, the Stoll
  metric coincides with a Minkowski norm: `‖v‖_{Stoll,X,σ} = ‖v‖_{Mink,P}
  = min { λ ≥ 0 | v ∈ λ·P }`, where `P` is the symmetric convex polytope spanned
  by the weighted generators.

- **Proposition 1.6 (Rough isometry) [Sto98, Prop 4.3].** For `H` torsion-free
  **2-step** nilpotent with finite generating set `X` and weight `σ`, the word
  metric and the Stoll metric differ by a bounded amount:
  `‖g‖_X − ‖g‖_{Stoll,X} = O_{H,X}(1)`.
  (This is the "more than we could bargain for" 2-step statement; the general
  s-step version is only `o(‖g‖)`.)

These give the **word-metric ⇄ Stoll-metric comparison** that Bodart's §2–§3
upper bound (our `theorem_4_upper`) routes through.

## Role in the formalization program

`theorem_4_upper` (γ_geod(n) ≤ c₂·exp(n^{3/5}·log n) eventually) decomposes as:
Stoll rough-isometry (this paper) + Pansu volume growth (`pansu_*_1983`) +
Bodart §2 virtually-nilpotent comparison + §3 counting. The elementary
volume-growth ingredient (polynomial reachability box) is already formalized in
`Groups/EngelGeodesicGrowth.lean`.
