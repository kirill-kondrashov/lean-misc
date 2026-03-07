import ErdosProblems.Problem1Derived

open Filter
open scoped Topology Real

namespace Erdos1

/--
Literature-facing proposition for the currently known real-valued spacing lower bound at the
classical `2^n / sqrt n` scale.
-/
def RealSpacingLowerBound : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/--
Literature-facing proposition for the sharp known real-valued spacing lower bound with constant
`sqrt (2 / pi)`.
-/
def RealSpacingLowerBoundStrong : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/--
The open exponential real-valued variant, separated from the known lower-bound theory.
-/
def OpenRealExponentialVariant : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℝ),
    IsSumDistinctRealSet A N → N ≠ 0 → C * 2 ^ A.card < N

/-- The exact imported real lower theorem immediately yields a clean `2^n / (n + 1)` bound. -/
theorem real_spacing_lower_bound_avg {N : ℕ} {A : Finset ℝ}
    (h : IsSumDistinctRealSet A N) : ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N :=
  two_pow_div_card_succ_le_of_isSumDistinctReal h

/-- The known real-valued `1 / 4` lower package, routed through the derived non-axiomatic layer. -/
theorem realSpacingLowerBound_from_imports : RealSpacingLowerBound :=
  erdos_1.variants.proved.real_lb

/--
The known real-valued sharp lower package with leading constant `sqrt (2 / pi)`, routed through
the derived non-axiomatic layer.
-/
theorem realSpacingLowerBoundStrong_from_imports : RealSpacingLowerBoundStrong :=
  erdos_1.variants.proved.real_lb_strong

/-- Alias exposing the current open exponential real-valued conjecture surface explicitly. -/
theorem openRealExponentialVariant_axiom : OpenRealExponentialVariant :=
  erdos_1.variants.real

end Erdos1
