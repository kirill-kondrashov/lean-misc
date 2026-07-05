import Groups.GeodesicGrowth

open Filter

namespace VirtuallyEngel

/-!
# A virtually Engel group

This file records Bodart's virtually `3`-step nilpotent example with intermediate geodesic
growth.
-/

/-- Generators in the two-generator presentation used for Bodart's virtually Engel group. -/
inductive Generator where
  | a
  | t
  deriving DecidableEq, Fintype

noncomputable instance : Primcodable Generator :=
  Primcodable.ofEquiv (Fin 2) (Fintype.equivFin Generator)

/-- The free-group word corresponding to the generator `a`. -/
abbrev A : FreeGroup Generator :=
  FreeGroup.of Generator.a

/-- The free-group word corresponding to the generator `t`. -/
abbrev T : FreeGroup Generator :=
  FreeGroup.of Generator.t

/-- The conjugate `t⁻¹ a t`, written `aᵗ` in the literature. -/
abbrev Aconj : FreeGroup Generator :=
  T⁻¹ * A * T

/-- The common third-step commutator in Bodart's presentation. -/
abbrev C : FreeGroup Generator :=
  ⁅A, ⁅A, Aconj⁆⁆

/-- Relators for Bodart's virtually Engel group:
`t² = 1`, `C = [aᵗ, [a, aᵗ]]`, and `C` commutes with both `a` and `aᵗ`. -/
abbrev relators : Set (FreeGroup Generator) :=
  {T * T, C * (⁅Aconj, ⁅A, Aconj⁆⁆)⁻¹, ⁅C, A⁆, ⁅C, Aconj⁆}

/-- Bodart's virtually Engel group. -/
abbrev Group : Type :=
  PresentedGroup relators

/-- The geodesic-growth alphabet `S = {a, a⁻¹, t}` used in Bodart's theorem. -/
inductive Letter where
  | a
  | aInv
  | t
  deriving DecidableEq, Fintype

/-- Interpretation of the Bodart alphabet in the presented group. -/
def letterValue : Letter → Group
  | .a => PresentedGroup.mk relators A
  | .aInv => (PresentedGroup.mk relators A)⁻¹
  | .t => PresentedGroup.mk relators T

/-- Geodesic growth with respect to `S = {a, a⁻¹, t}`. -/
noncomputable abbrev geodesicGrowth : ℕ → ℕ :=
  PresentedGroup.geodesicGrowth relators letterValue

/-- The comparison function appearing in Bodart's asymptotic estimate. -/
noncomputable def modelGrowth (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ).rpow ((3 : ℝ) / 5) * Real.log (n : ℝ))

/-- A literal formalization of `γ(n) ≍ exp(n^{3/5} log n)` as an eventual two-sided bound. -/
def theorem_4_statement : Prop :=
  ∃ c₁ c₂ : ℝ,
    0 < c₁ ∧
    c₁ ≤ c₂ ∧
    ∀ᶠ n : ℕ in atTop,
      c₁ * modelGrowth n ≤ (geodesicGrowth n : ℝ) ∧
      (geodesicGrowth n : ℝ) ≤ c₂ * modelGrowth n

/-- Theorem 4 of Bodart, imported as literature axiom.

It states that the virtually Engel group above has intermediate geodesic growth with respect to
the generating alphabet `S = {a, a⁻¹, t}`. -/
axiom theorem_4 : theorem_4_statement

/-- Standard background consequence for Bodart's example: the virtually Engel presentation has
solvable word problem. -/
axiom solvableWordProblem : PresentedGroup.SolvableWordProblem relators

/-- Bodart's example has irrational geodesic growth in the sense of Question 3 of Brönnimann's
thesis. -/
axiom irrationalGeodesicGrowth :
  PresentedGroup.HasIrrationalGeodesicGrowth relators letterValue

end VirtuallyEngel
