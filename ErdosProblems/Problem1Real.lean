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

/--
Bundled surface for the currently known real-valued spacing theory: the exact middle-binomial
lower bound, its average-binomial consequence, and the two asymptotic lower packages.
-/
def KnownRealSpacingTheory : Prop :=
  (∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
    Nat.choose A.card (A.card / 2) ≤ N) ∧
  (∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
    ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N) ∧
  RealSpacingLowerBound ∧
  RealSpacingLowerBoundStrong

/-- Short alias for the exact imported real middle-binomial lower theorem. -/
theorem real_spacing_lower_bound_exact_imported {N : ℕ} {A : Finset ℝ}
    (h : IsSumDistinctRealSet A N) : Nat.choose A.card (A.card / 2) ≤ N :=
  erdos_1_real_lower_bound_exact_imported h

/-- The exact imported real lower theorem immediately yields a clean `2^n / (n + 1)` bound. -/
theorem real_spacing_lower_bound_avg {N : ℕ} {A : Finset ℝ}
    (h : IsSumDistinctRealSet A N) : ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N :=
  two_pow_div_card_succ_le_of_isSumDistinctReal h

/--
The sharp real-valued spacing lower package implies the weaker `1 / 4` package by comparing the
leading constants.
-/
theorem realSpacingLowerBound_of_strong (hStrong : RealSpacingLowerBoundStrong) :
    RealSpacingLowerBound := by
  rcases hStrong with ⟨o, ho, hstrong⟩
  refine ⟨o, ho, ?_⟩
  intro N A hA
  have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt (2 / Real.pi) := by
    have hdiv : (1 / 16 : ℝ) < 2 / Real.pi := by
      rw [lt_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four]
    have hsqrt' : Real.sqrt (1 / 16 : ℝ) < Real.sqrt (2 / Real.pi) := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · exact hdiv
    have hquarter : Real.sqrt (1 / 16 : ℝ) = (1 / 4 : ℝ) := by norm_num
    linarith
  have hfactor_nonneg : 0 ≤ (2 : ℝ) ^ A.card / (A.card : ℝ).sqrt := by
    positivity
  have hcoeff :
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤
        (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt := by
    have hbase : 1 / 4 - o A.card ≤ Real.sqrt (2 / Real.pi) - o A.card := by linarith
    have hmul :
        (1 / 4 - o A.card) * ((2 : ℝ) ^ A.card / (A.card : ℝ).sqrt) ≤
          (Real.sqrt (2 / Real.pi) - o A.card) * ((2 : ℝ) ^ A.card / (A.card : ℝ).sqrt) :=
      mul_le_mul_of_nonneg_right hbase hfactor_nonneg
    simpa [mul_assoc, div_eq_mul_inv, mul_left_comm, mul_comm] using hmul
  exact hcoeff.trans (hstrong N A hA)

/-- The known real-valued `1 / 4` lower package, routed through the derived non-axiomatic layer. -/
theorem realSpacingLowerBound_from_imports : RealSpacingLowerBound :=
  erdos_1.variants.proved.real_lb

/--
The known real-valued sharp lower package with leading constant `sqrt (2 / pi)`, routed through
the derived non-axiomatic layer.
-/
theorem realSpacingLowerBoundStrong_from_imports : RealSpacingLowerBoundStrong :=
  erdos_1.variants.proved.real_lb_strong

/-- The imported real theory packages exactly into the local bundled known-theory surface. -/
theorem knownRealSpacingTheory_from_imports : KnownRealSpacingTheory := by
  refine ⟨?_, ?_, realSpacingLowerBound_from_imports, realSpacingLowerBoundStrong_from_imports⟩
  · intro N A hA
    exact real_spacing_lower_bound_exact_imported hA
  · intro N A hA
    exact real_spacing_lower_bound_avg hA

/-- Alias exposing the current open exponential real-valued conjecture surface explicitly. -/
theorem openRealExponentialVariant_axiom : OpenRealExponentialVariant :=
  erdos_1.variants.real

end Erdos1
