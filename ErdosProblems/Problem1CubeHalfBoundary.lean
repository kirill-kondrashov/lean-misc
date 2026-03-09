import ErdosProblems.Problem1CubeNatBridge

namespace Erdos1

/--
The sharp half-cube boundary lower statement on the Boolean cube.

This is the exact cube theorem whose proof would remove the final frontier assumption in the exact
integer route for Erdős Problem #1.
-/
def HalfCubeBoundaryLowerStatement : Prop :=
  ∀ {α : Type} [DecidableEq α] [Fintype α] {𝒟 : Finset (Finset α)},
    𝒟.Nonempty →
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (Fintype.card α - 1) →
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ (positiveBoundary 𝒟).card

/--
Remaining frontier input: the sharp half-cube boundary theorem on the Boolean cube.

Replacing this axiom with a proof removes the final exact-theorem blocker.
-/
axiom halfCubeBoundaryLower : HalfCubeBoundaryLowerStatement

/--
Specialization of the general half-cube boundary theorem to the subtype cube transported from a
sum-distinct set `A`.
-/
theorem subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
  unfold HalfCubeBoundaryLowerStatement at hCube
  have hCube' :
      Nat.choose (Fintype.card ↥A) (Fintype.card ↥A / 2) ≤
        (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
    exact hCube (α := ↥A) (𝒟 := negativeHalfFamilySubcubeNat A)
      (negativeHalfFamilySubcubeNat_nonempty h hA)
      (isDownSetFamily_negativeHalfFamilySubcubeNat A)
      (card_negativeHalfFamilySubcubeNat_eq_half_cube h hA)
  simpa [Fintype.card_coe] using hCube'

/--
Arithmetic positive-boundary lower bound derived from the general half-cube boundary theorem.
-/
theorem positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card := by
  have hsub := subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower hCube h hA
  simpa [card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat h hA] using
    hsub

end Erdos1
