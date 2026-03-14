import ErdosProblems.Problem1CubeAlexanderDual
import ErdosProblems.Problem1CubeHalfBoundary

open Finset
open scoped FinsetFamily

namespace Erdos1

/-- Topological / Alexander-dual reformulation of the minimizer-only `minimalOutside` route:
the dual complex of a genuine odd half-cube global boundary minimizer should have at least the
middle-binomial number of facets. -/
def OddHalfCubeBoundaryGlobalMinimizerDualFacetLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      Nat.choose (2 * m + 1) m ≤ #(maximalInside (alexanderDual 𝒟))

/-- Universal dual-facet reformulation of the odd half-cube problem. This is the Alexander-dual
version of `OddHalfCubeMinimalOutsideLowerStatement`, so it is archival and false. -/
def OddHalfCubeDualFacetLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      Nat.choose (2 * m + 1) m ≤ #(maximalInside (alexanderDual 𝒟))

theorem
    oddHalfCubeBoundaryGlobalMinimizerDualFacetLower_iff_globalMinimizerMinimalOutsideLower :
    OddHalfCubeBoundaryGlobalMinimizerDualFacetLowerStatement ↔
      OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  constructor
  · intro hFacet m 𝒟 hmin
    simpa [card_maximalInside_alexanderDual] using hFacet hmin
  · intro hMin m 𝒟 hmin
    simpa [card_maximalInside_alexanderDual] using hMin hmin

theorem oddHalfCubeDualFacetLower_iff_minimalOutsideLower :
    OddHalfCubeDualFacetLowerStatement ↔ OddHalfCubeMinimalOutsideLowerStatement := by
  constructor
  · intro hFacet m 𝒟 h𝒟 hcard
    simpa [card_maximalInside_alexanderDual] using hFacet h𝒟 hcard
  · intro hMin m 𝒟 h𝒟 hcard
    simpa [card_maximalInside_alexanderDual] using hMin h𝒟 hcard

theorem not_OddHalfCubeDualFacetLowerStatement :
    ¬ OddHalfCubeDualFacetLowerStatement := by
  intro hFacet
  exact not_OddHalfCubeMinimalOutsideLowerStatement
    ((oddHalfCubeDualFacetLower_iff_minimalOutsideLower).mp hFacet)

theorem oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerDualFacetLower
    (hFacet : OddHalfCubeBoundaryGlobalMinimizerDualFacetLowerStatement) :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerMinimalOutsideLower
      ((oddHalfCubeBoundaryGlobalMinimizerDualFacetLower_iff_globalMinimizerMinimalOutsideLower).mp
        hFacet)

theorem oddHalfCubeUpperShadowGapLower_of_globalMinimizerDualFacetLower
    (hFacet : OddHalfCubeBoundaryGlobalMinimizerDualFacetLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact
    oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower
      ((oddHalfCubeBoundaryGlobalMinimizerDualFacetLower_iff_globalMinimizerMinimalOutsideLower).mp
        hFacet)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerDualFacetLower
    (hFacet : OddHalfCubeBoundaryGlobalMinimizerDualFacetLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_globalMinimizerDualFacetLower hFacet)

theorem oddHalfCubeUpperShadowGapLower_of_dualFacetLower
    (hFacet : OddHalfCubeDualFacetLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact
    oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower
      ((oddHalfCubeDualFacetLower_iff_minimalOutsideLower).mp hFacet)

theorem oddHalfCubeBoundaryLower_of_dualFacetLower
    (hFacet : OddHalfCubeDualFacetLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_dualFacetLower hFacet)

end Erdos1
