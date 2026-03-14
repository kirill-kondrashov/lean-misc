import ErdosProblems.Problem1Literature

open Filter
open scoped Topology Real

namespace Erdos1

/--
Derived non-axiomatic replacement for the public lower-bound placeholder
`Erdos1.erdos_1.variants.lb`.
-/
theorem erdos_1.variants.proved.lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_variants_lb_from_imports

/--
Derived non-axiomatic replacement for the public sharp lower-bound placeholder
`Erdos1.erdos_1.variants.lb_strong`.
-/
theorem erdos_1.variants.proved.lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_variants_lb_strong_from_choose_middle_asymptotic

/--
Derived non-axiomatic real-valued `1 / 4` lower package, separated from the open exponential real
variant `Erdos1.erdos_1.variants.real`.
-/
theorem erdos_1.variants.proved.real_lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_real_variants_lb_from_imports

/--
Derived non-axiomatic real-valued sharp lower package at the `sqrt (2 / pi)` scale.
-/
theorem erdos_1.variants.proved.real_lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_real_variants_lb_strong_from_choose_middle_asymptotic

/-- Derived literature-backed wrapper for the current Bohman upper construction surface. -/
theorem erdos_1.known.bohman_upper_construction :
    BohmanUpperConstruction :=
  bohmanUpperConstruction_imported

/-- Derived literature-backed package of the current best known upper/lower sandwich. -/
theorem erdos_1.known.best_known_integer_gap :
    BestKnownIntegerGap :=
  bestKnownIntegerGap_from_imports

end Erdos1
