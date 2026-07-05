import Groups.GeodesicGrowth

namespace VirtuallyHeisenberg

/-!
# A virtually Heisenberg group

This file records the Bishop--Elder example of a virtually `2`-step nilpotent group with
polynomial geodesic growth.
-/

/-- Generators in the presentation `⟨a, b, t | [[a,b],a] = [[a,b],b] = 1, t^2 = 1, t⁻¹at = b⟩`. -/
inductive Generator where
  | a
  | b
  | t
  deriving DecidableEq, Fintype

/-- The free-group word corresponding to the generator `a`. -/
abbrev A : FreeGroup Generator :=
  FreeGroup.of Generator.a

/-- The free-group word corresponding to the generator `b`. -/
abbrev B : FreeGroup Generator :=
  FreeGroup.of Generator.b

/-- The free-group word corresponding to the generator `t`. -/
abbrev T : FreeGroup Generator :=
  FreeGroup.of Generator.t

/-- Relators for the virtually Heisenberg group used by Bishop--Elder. -/
abbrev relators : Set (FreeGroup Generator) :=
  {⁅⁅A, B⁆, A⁆, ⁅⁅A, B⁆, B⁆, T * T, T⁻¹ * A * T * B⁻¹}

/-- The Bishop--Elder virtually Heisenberg group. -/
abbrev Group : Type :=
  PresentedGroup relators

/-- The geodesic-growth alphabet `S = {a, a⁻¹, t}` used in Bishop--Elder. -/
inductive Letter where
  | a
  | aInv
  | t
  deriving DecidableEq, Fintype

/-- Interpretation of the Bishop--Elder alphabet in the presented group. -/
def letterValue : Letter → Group
  | .a => PresentedGroup.mk relators A
  | .aInv => (PresentedGroup.mk relators A)⁻¹
  | .t => PresentedGroup.mk relators T

/-- Geodesic growth with respect to `S = {a, a⁻¹, t}`. -/
noncomputable abbrev geodesicGrowth : ℕ → ℕ :=
  PresentedGroup.geodesicGrowth relators letterValue

/-- The formal statement of Bishop--Elder's polynomial upper bound. -/
def theorem_1_statement : Prop :=
  ∃ C : ℕ, ∀ n, geodesicGrowth n ≤ C * (n + 1) ^ 8

/-- Theorem 1 of Bishop--Elder, imported as literature axiom.

It states that the virtually Heisenberg group above has polynomial geodesic growth with respect
to the generating alphabet `S = {a, a⁻¹, t}`. -/
axiom theorem_1 : theorem_1_statement

end VirtuallyHeisenberg
