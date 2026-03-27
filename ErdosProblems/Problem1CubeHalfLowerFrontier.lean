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

/--
Exact Erdős #1 lower theorem obtained directly from the current prism leaf frontier together with
the canonical defect-side bottleneck.
-/
theorem erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_prismTheoremCanonicalPairInterfaceBoundaryDefectBottleneck
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hCanonDefect : PrismTheoremCanonicalPairInterfaceBoundaryDefectBottleneckStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (positiveBoundaryFamilyNat_lower_of_prismTheoremCurrentLeafFrontier_of_prismTheoremCanonicalPairInterfaceBoundaryDefectBottleneck
      hFrontier hCanonDefect hA hAne)

/--
Equivalent exact Erdős #1 endpoint using the first-positive-gap defect bridge directly.
-/
theorem erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_firstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerTotalSize
    (hDefect :
      OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerTotalSizeThanEvenWitnessStatement)
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (positiveBoundaryFamilyNat_lower_of_firstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerTotalSize_of_prismTheoremCurrentLeafFrontier
      hDefect hFrontier hA hAne)

/--
Equivalent exact Erdős #1 endpoint using the first-positive-gap defect bridge in direct prism
language.
-/
theorem erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_firstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerPrismThanEvenWitness
    (hDefect :
      OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerPrismThanEvenWitnessStatement)
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (positiveBoundaryFamilyNat_lower_of_firstPositiveGapSlicePairInterfaceBoundaryDefectForcesLargerPrismThanEvenWitness_of_prismTheoremCurrentLeafFrontier
      hDefect hFrontier hA hAne)

/--
Equivalent exact Erdős #1 endpoint using the first-positive-gap contradiction surface: a defect
cannot coexist with a prism of size at most the even witness.
-/
theorem erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_firstPositiveGapSlicePairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossible
    (hDefect :
      OddSectionFirstPositiveGapSlicePairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossibleStatement)
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (positiveBoundaryFamilyNat_lower_of_firstPositiveGapSlicePairInterfaceBoundaryDefectWithNoLargerPrismThanEvenWitnessImpossible_of_prismTheoremCurrentLeafFrontier
      hDefect hFrontier hA hAne)

/--
Exact Erdős #1 endpoint factored through the two explicit remaining subgoals:
normalize the canonical defect bottleneck to the simple-lower contradiction surface, and then
prove the simple-lower upper-tail bridge.
-/
theorem
    erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_prismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLower_of_simpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddle
    (hNorm : PrismTheoremCanonicalPairInterfaceBoundaryDefectNormalizesToSimpleLowerStatement)
    (hSimple : SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement)
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  exact
    erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_prismTheoremCanonicalPairInterfaceBoundaryDefectBottleneck
      hFrontier
      (prismTheoremCanonicalPairInterfaceBoundaryDefectBottleneck_of_normalizesToSimpleLower_of_simpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddle
        hNorm hSimple)

/--
Equivalent exact Erdős #1 endpoint using the positive-excess defect bridge directly.
-/
theorem erdos_1_lower_bound_exact_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryDefectForcesLargerTotalSize
    (hDefect :
      OddSectionPositiveExcessPairInterfaceBoundaryDefectForcesLargerTotalSizeThanEvenWitnessStatement)
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA
    (positiveBoundaryFamilyNat_lower_of_positiveExcessPairInterfaceBoundaryDefectForcesLargerTotalSize_of_prismTheoremCurrentLeafFrontier
      hDefect hFrontier hA hAne)

end Erdos1
