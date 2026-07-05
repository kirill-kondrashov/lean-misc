# Stoll–Pansu discharge program (A2 endgame)

Goal: remove the last two internal-facing axioms, `VirtuallyEngel.theorem_4_upper` and
`VirtuallyEngel.theorem_4_lower`, so that `BronnimannQuestion3.positive_answer` depends only on
the Lean/Mathlib core axioms plus the compiler axioms `Lean.ofReduceBool` / `Lean.trustCompiler`
(the latter coming from the `native_decide` word-problem decision procedure and outside the scope
of this program).

## Reference materials (`refs/`)

Primary sources are paywalled journal articles; we do **not** redistribute their PDFs. Citation
stubs with the precise statements we depend on (sourced from Bodart §1, arXiv:2306.10381v3, which
is included) are provided instead:

- `refs/stoll_asymptotics_growth_2step_nilpotent_1998.md` — Stoll 1998, Stoll metric + rough
  isometry (Def 1.3, Lem 1.4, Prop 1.6).
- `refs/pansu_croissance_boules_geodesiques_nilvarietes_1983.md` — Pansu 1983, polynomial volume
  growth `β(n) = c·n^d + o(n^d)`.
- `refs/breuillard_polynomial_growth_shape_of_large_balls_2014.pdf` — E. Breuillard,
  arXiv:0704.0095 (openly available surrogate that states and generalizes Pansu's theorem).
- `refs/bodart_intermediate_geodesic_growth_virtually_nilpotent_2025.pdf` — the paper being
  formalized; §1–§4 give the full proof skeleton.

## Current axiom status

- `theorem_4` — **proved theorem** (glue from the two below). `Groups/VirtuallyEngelGroup.lean`.
- `theorem_4_upper : ∃ c₂>0, ∀ᶠ n, γ(n) ≤ c₂·exp(n^{3/5} log n)` — **axiom** (target).
- `theorem_4_lower : ∃ c₁>0, ∀ᶠ n, c₁·exp(n^{3/5} log n) ≤ γ(n)` — **axiom** (target).

## Layered plan

### Layer 0 — geodesic-to-model reduction  ✅ done
`Groups/EngelGeodesicGrowth.lean`: `geodesicGrowth_eq_coordCount`, `evalCoordWord_*`.

### Layer 1 — polynomial volume growth (Pansu, elementary for this group)  ✅ done
`Groups/EngelGeodesicGrowth.lean` reachability box (`endpoint_le_length`, `area_le_length_sq`,
`bary3_le_length_cube`) + `Groups/StollPansu.lean`:
`coordBox`, `engelToTuple_mem_coordBox`, `coordBox_card`,
`reachLeft_finite`, `reachLeft_ncard_le_poly` — the reachable endpoint set has degree-`6`
polynomial cardinality, proved from scratch (no general Pansu needed).

### Layer 2 — geodesic multiplicity ⇒ upper bound  ⏳ target
Split `theorem_4_upper` as: (polynomial volume growth, Layer 1) × (geodesics per endpoint).
Target `Program.geodesicMultiplicityBound` (in `StollPansu.lean`): the number of length-`n`
geodesic words ending at a fixed coordinate is `≤ C·exp(n^{3/5} log n)`. Then
`γ(n) = Σ_g (#geodesics to g) ≤ |reachLeft n| · max_g(#geodesics to g) ≤ poly(n)·C·exp(...)`,
which is `≤ c₂·exp(...)` eventually (polynomial × sub-exp is absorbed). The multiplicity bound is
where the **Stoll metric** enters: geodesics to `g` correspond to lattice paths realizing the
Stoll/Minkowski norm, counted via Bodart §3.
Sub-steps:
  1. Stoll/Minkowski norm on `ℤ⁴` model (Def 1.3 / Lem 1.4).
  2. Word-norm vs Stoll-norm rough isometry for this 2-step-ish model (Prop 1.6).
  3. Count of norm-realizing paths ⇒ the `exp(n^{3/5} log n)` multiplicity.
  4. Assemble Layer-1 × multiplicity ⇒ re-derive `theorem_4_upper` as a theorem.

### Layer 3 — explicit geodesic family ⇒ lower bound  ⏳ target
Target `Program.geodesicLowerFamily` (= `theorem_4_lower` verbatim). Bodart §4: build, for large
`n`, an explicit set of `≥ c₁·exp(n^{3/5} log n)` distinct length-`n` geodesic words on the
`EngelCoords`/Hall-normal-form substrate (Prop 4.1 concatenation parameters, Prop 4.2 "back from
the depths", Cor 4.5). The coordinate model + `hallNormalWord` give the constructive substrate;
geodesicity uses the Layer-2 norm lower bounds.

### Layer 4 — close out
Re-derive `theorem_4_upper` / `theorem_4_lower` as theorems from Layers 2–3; delete the two
axioms; update `check_axioms.lean` (only the compiler axioms remain), README expected-output,
`docs/proof.tex`; run `make check` / `make verify`.

## Honesty note

Layers 2–3 remain research-scale (they *are* the Stoll/Pansu-dependent mathematics). Layer 1 is
fully discharged and is a genuine, self-contained sub-result. The `Program.*` `Prop`s are
definitions, not axioms: they sharpen the debt into concrete goals without adding to the
dependency graph of `positive_answer`.
