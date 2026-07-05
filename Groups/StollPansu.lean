import Groups.EngelGeodesicGrowth

/-!
# Stoll–Pansu program: discharging the analytic axioms of Theorem 4

Bodart's Theorem 4 (`VirtuallyEngel.theorem_4`) is now a proved theorem, assembled by elementary
glue from the two named analytic sub-axioms `VirtuallyEngel.theorem_4_upper` and
`VirtuallyEngel.theorem_4_lower` (see `Groups/VirtuallyEngelGroup.lean`). Those two are the sole
remaining internal-facing axioms on which `BronnimannQuestion3.positive_answer` depends (modulo
the compiler axioms `Lean.ofReduceBool` / `Lean.trustCompiler`).

This file starts the *program* of discharging those two axioms from scratch, following the
structure of Bodart §1–§4, which routes through:

* **Pansu** (`refs/pansu_*_1983`): polynomial volume growth of nilpotent word metrics; and
* **Stoll** (`refs/stoll_*_1998`): the rough isometry between the word metric and the Stoll
  (Minkowski/sub-Finsler) metric on 2-step nilpotent groups.

Because the virtually Engel group has an explicit integer coordinate model
(`VirtuallyEngel.EngelCoords`), several ingredients that are *hard in general* become
*elementary for this specific group*. This file formalizes the first such ingredient in full
(no axioms, no `sorry`):

* the **polynomial volume-growth bound** — the coordinate endpoints reachable by words of length
  at most `n` number at most a fixed degree-`6` polynomial in `n` — proved directly from the
  reachability box (`endpoint_le_length`, `area_le_length_sq`, `bary3_le_length_cube`), i.e.
  *without* invoking the general Pansu theorem.

The remaining, genuinely deep ingredients (the Stoll rough isometry and the geodesic-multiplicity
count that produces the `exp(n^{3/5} log n)` factor) are recorded as precisely-stated `Prop`s in
the `VirtuallyEngel.Program` namespace at the end of the file. They are **definitions, not
axioms**, so they do not enter the dependency graph of `positive_answer`; they are the explicit
targets whose eventual proof will let `theorem_4_upper` / `theorem_4_lower` be re-derived as
theorems.
-/

open PresentedGroup

namespace VirtuallyEngel

/-! ## Coordinate embedding into `ℤ⁴` -/

/-- Embed an Engel coordinate as a raw integer 4-tuple. -/
def engelToTuple (g : EngelCoords) : ℤ × ℤ × ℤ × ℤ := (g.u, g.v, g.area, g.bary3)

theorem engelToTuple_injective : Function.Injective engelToTuple := by
  intro g h hgh
  cases g; cases h
  simp only [engelToTuple, Prod.mk.injEq] at hgh
  obtain ⟨h1, h2, h3, h4⟩ := hgh
  subst h1; subst h2; subst h3; subst h4; rfl

/-! ## The polynomial coordinate box -/

/-- The polynomial coordinate box guaranteed to contain the image of any length-`≤ n` word:
`|u|, |v| ≤ n`, `|area| ≤ n²`, `|bary3| ≤ 3n³`. -/
def coordBox (n : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n) ×ˢ
    (Finset.Icc (-((n : ℤ) ^ 2)) ((n : ℤ) ^ 2)) ×ˢ
    (Finset.Icc (-(3 * (n : ℤ) ^ 3)) (3 * (n : ℤ) ^ 3))

/-- Every length-`≤ n` word lands, in coordinates, inside the polynomial box. -/
theorem engelToTuple_mem_coordBox {w : List Letter} {n : ℕ} (h : w.length ≤ n) :
    engelToTuple (evalCoordWord w).left ∈ coordBox n := by
  have he := endpoint_le_length w
  have ha := area_le_length_sq w
  have hb := bary3_le_length_cube w
  set g := (evalCoordWord w).left
  have hu : g.u.natAbs ≤ n := by omega
  have hv : g.v.natAbs ≤ n := by omega
  have ha2 : g.area.natAbs ≤ n * n := le_trans ha (Nat.mul_le_mul h h)
  have hb3 : g.bary3.natAbs ≤ 3 * (n * n * n) :=
    le_trans hb (by have := Nat.mul_le_mul (Nat.mul_le_mul h h) h; omega)
  have hn2 : ((n * n : ℕ) : ℤ) = (n : ℤ) ^ 2 := by push_cast; ring
  have hn3 : ((n * n * n : ℕ) : ℤ) = (n : ℤ) ^ 3 := by push_cast; ring
  simp only [coordBox, engelToTuple, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- The box has an explicit degree-`6` polynomial cardinality. -/
theorem coordBox_card (n : ℕ) :
    (coordBox n).card
      = (2 * n + 1) * ((2 * n + 1) * ((2 * n ^ 2 + 1) * (6 * n ^ 3 + 1))) := by
  have e1 : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]; omega
  have e2 : (Finset.Icc (-((n : ℤ) ^ 2)) ((n : ℤ) ^ 2)).card = 2 * n ^ 2 + 1 := by
    rw [Int.card_Icc]
    have h : ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; omega
  have e3 : (Finset.Icc (-(3 * (n : ℤ) ^ 3)) (3 * (n : ℤ) ^ 3)).card = 6 * n ^ 3 + 1 := by
    rw [Int.card_Icc]
    have h : (3 * (n : ℤ) ^ 3) = ((3 * n ^ 3 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; omega
  unfold coordBox
  rw [Finset.card_product, Finset.card_product, Finset.card_product, e1, e2, e3]

/-! ## Elementary polynomial volume growth for the virtually Engel group -/

/-- The set of coordinate endpoints reachable by words of length at most `n`. -/
def reachLeft (n : ℕ) : Set EngelCoords :=
  {g | ∃ w : List Letter, w.length ≤ n ∧ (evalCoordWord w).left = g}

theorem reachLeft_finite (n : ℕ) : (reachLeft n).Finite := by
  apply Set.Finite.of_finite_image (f := engelToTuple)
  · apply Set.Finite.subset (coordBox n).finite_toSet
    rintro _ ⟨g, ⟨w, hw, rfl⟩, rfl⟩
    exact engelToTuple_mem_coordBox hw
  · exact engelToTuple_injective.injOn

theorem reachLeft_ncard_le_card (n : ℕ) :
    (reachLeft n).ncard ≤ (coordBox n).card := by
  rw [← Set.ncard_image_of_injective (reachLeft n) engelToTuple_injective,
    ← Set.ncard_coe_finset (coordBox n)]
  apply Set.ncard_le_ncard _ (coordBox n).finite_toSet
  rintro _ ⟨g, ⟨w, hw, rfl⟩, rfl⟩
  exact engelToTuple_mem_coordBox hw

/-- **Elementary polynomial volume growth (the Pansu input, from scratch for this group).**
The number of distinct coordinate endpoints reachable by words of length at most `n` is bounded
by a fixed degree-`6` polynomial in `n`. Proved directly from the reachability box, *without*
invoking the general Pansu volume-growth theorem. -/
theorem reachLeft_ncard_le_poly (n : ℕ) :
    (reachLeft n).ncard
      ≤ (2 * n + 1) * ((2 * n + 1) * ((2 * n ^ 2 + 1) * (6 * n ^ 3 + 1))) := by
  rw [← coordBox_card]; exact reachLeft_ncard_le_card n

/-! ## Program targets (the remaining deep ingredients)

The statements below are `Prop`-valued **definitions** — the explicit mathematical targets that
remain between the current axiom debt and a full discharge of `theorem_4_upper` /
`theorem_4_lower`. They are *not* axioms and do not affect `positive_answer`'s dependency graph.
Each corresponds to a labelled step in Bodart §1–§4. Proving them (bottom-up, from Mathlib and the
elementary volume growth above) is the content of this program.
-/

namespace Program

/-- **Target (multiplicity ⇒ upper bound).** If the number of *geodesic words* of length `n`
that share a common coordinate endpoint is eventually at most `exp(n^{3/5} log n)` up to a
constant, then — combined with the polynomial volume growth `reachLeft_ncard_le_poly` — the total
geodesic-word count `γ(n)` satisfies the upper half of Theorem 4. This is the shape of the
reduction that will turn `theorem_4_upper` into a theorem. -/
def geodesicMultiplicityBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ g : EngelCoords,
        (Nat.card {w : WordTuple Letter n //
          CoordGeodesic (List.ofFn w) ∧ (evalCoordWord (List.ofFn w)).left = g} : ℝ)
          ≤ C * modelGrowth n

/-- **Target (explicit geodesic family ⇒ lower bound).** An explicit family assigning to each
large `n` at least `c₁ · exp(κ · n^{3/5} log n)` distinct geodesic words of length `n`, for some
exponent constant `κ ∈ (0, 1]`. Bodart's §4 lower estimate only controls the exponent up to this
smaller constant; this is the combinatorial heart of Bodart §4 (Prop 4.1 / Prop 4.2 / Cor 4.5)
and will turn `theorem_4_lower` into a theorem. -/
def geodesicLowerFamily : Prop :=
  ∃ κ c₁ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 0 < c₁ ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      c₁ * LinearRecurrenceGrowth.scaledModelGrowthReal κ n ≤ (geodesicGrowth n : ℝ)

/-- Sanity check: the lower-family target is *definitionally* the content of `theorem_4_lower`. -/
theorem geodesicLowerFamily_iff : geodesicLowerFamily ↔
    (∃ κ c₁ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 0 < c₁ ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        c₁ * LinearRecurrenceGrowth.scaledModelGrowthReal κ n ≤ (geodesicGrowth n : ℝ)) :=
  Iff.rfl

end Program

end VirtuallyEngel
