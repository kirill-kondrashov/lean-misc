import ErdosProblems.Problem1CubeHalfBoundary

namespace Erdos1

/--
Subtype-cube boundary lower bound obtained by specializing the global half-cube boundary theorem to
the transported strict lower-half family.
-/
theorem subcubeHalfCubeBoundaryLower_frontier :
    ∀ ⦃N : ℕ⦄ ⦃A : Finset ℕ⦄, IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
  intro N A h hA
  exact subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower halfCubeBoundaryLower h hA

/--
The arithmetic positive-boundary middle lower bound obtained from the subtype-cube frontier input.
-/
theorem PositiveBoundaryMiddleLower_via_subcubeHalfCubeBoundaryLower :
    ∀ ⦃N : ℕ⦄ ⦃A : Finset ℕ⦄, IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card := by
  intro N A h hA
  exact positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower halfCubeBoundaryLower h hA

/--
The exact Dubroff-Fox-Xu lower theorem, routed through the subtype-cube half-cube frontier.
-/
theorem erdos_1_lower_bound_exact_of_subcubeHalfCubeBoundaryLower
    :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (PositiveBoundaryMiddleLower_via_subcubeHalfCubeBoundaryLower hA hAne)

end Erdos1
