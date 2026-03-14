import ErdosProblems.Problem1Derived

open Filter
open scoped Topology Real

namespace Erdos1

/--
Literature-facing proposition for the currently known integer lower bound at the classical
`2^n / sqrt n` scale.
-/
def IntegerLowerBound : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/--
Literature-facing proposition for the sharp known integer lower bound with constant
`sqrt (2 / pi)`.
-/
def IntegerLowerBoundStrong : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/--
Bundled surface for the currently known integer lower theory: the exact middle-binomial lower
bound, its average-binomial consequence, and the two asymptotic lower packages.
-/
def KnownIntegerLowerTheory : Prop :=
  (∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    Nat.choose A.card (A.card / 2) ≤ N) ∧
  (∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N) ∧
  IntegerLowerBound ∧
  IntegerLowerBoundStrong

/-- Short alias for the exact imported integer middle-binomial lower theorem. -/
theorem integer_lower_bound_exact_imported {N : ℕ} {A : Finset ℕ}
    (h : IsSumDistinctSet A N) : Nat.choose A.card (A.card / 2) ≤ N :=
  erdos_1_lower_bound_exact_imported h

/-- The exact imported integer lower theorem immediately yields a clean `2^n / (n + 1)` bound. -/
theorem integer_lower_bound_avg {N : ℕ} {A : Finset ℕ}
    (h : IsSumDistinctSet A N) : ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N :=
  two_pow_div_card_succ_le_of_isSumDistinct h

/--
The sharp integer lower package implies the weaker `1 / 4` package by comparing the leading
constants.
-/
theorem integerLowerBound_of_strong (hStrong : IntegerLowerBoundStrong) :
    IntegerLowerBound := by
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

/-- The known integer `1 / 4` lower package, routed through the derived non-axiomatic layer. -/
theorem integerLowerBound_from_imports : IntegerLowerBound :=
  erdos_1.variants.proved.lb

/--
The known integer sharp lower package with leading constant `sqrt (2 / pi)`, routed through the
derived non-axiomatic layer.
-/
theorem integerLowerBoundStrong_from_imports : IntegerLowerBoundStrong :=
  erdos_1.variants.proved.lb_strong

/-- The imported integer lower theory packages exactly into the local bundled surface. -/
theorem knownIntegerLowerTheory_from_imports : KnownIntegerLowerTheory := by
  refine ⟨?_, ?_, integerLowerBound_from_imports, integerLowerBoundStrong_from_imports⟩
  · intro N A hA
    exact integer_lower_bound_exact_imported hA
  · intro N A hA
    exact integer_lower_bound_avg hA

end Erdos1
