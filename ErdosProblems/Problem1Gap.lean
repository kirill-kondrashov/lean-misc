import ErdosProblems.Problem1Integer

open Filter
open scoped Topology Real

namespace Erdos1

/--
The open exponential target for the integer problem, separated from the currently known lower/upper
literature package.
-/
def OpenIntegerExponentialVariant : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
    IsSumDistinctSet A N → N ≠ 0 → C * 2 ^ A.card < N

/--
Honest current gap package for the integer problem: exact/asymptotic lower theory together with
the best known exponential upper construction.
-/
def KnownIntegerGapTheory : Prop :=
  KnownIntegerLowerTheory ∧ BohmanUpperConstruction

/-- The existing open-problem placeholder exposed under an explicit gap-module name. -/
theorem openIntegerExponentialVariant_axiom : OpenIntegerExponentialVariant :=
  erdos_1

/-- The best known upper construction routed through the existing derived surface. -/
theorem knownIntegerUpperConstruction_from_imports : BohmanUpperConstruction :=
  erdos_1.known.bohman_upper_construction

/-- The current best known integer gap theory, packaged from the imported lower and upper results. -/
theorem knownIntegerGapTheory_from_imports : KnownIntegerGapTheory :=
  ⟨knownIntegerLowerTheory_from_imports, knownIntegerUpperConstruction_from_imports⟩

/--
The older `BestKnownIntegerGap` surface is recovered from the bundled gap theory by keeping only
the sharp lower branch together with the upper construction.
-/
theorem bestKnownIntegerGap_of_knownIntegerGapTheory (h : KnownIntegerGapTheory) :
    BestKnownIntegerGap := by
  rcases h with ⟨hLower, hUpper⟩
  rcases hLower with ⟨-, -, -, hLowerStrong⟩
  exact ⟨hUpper, hLowerStrong⟩

/-- The imported bundled gap theory implies the older literature-facing gap surface. -/
theorem bestKnownIntegerGap_from_gapTheory : BestKnownIntegerGap :=
  bestKnownIntegerGap_of_knownIntegerGapTheory knownIntegerGapTheory_from_imports

end Erdos1
