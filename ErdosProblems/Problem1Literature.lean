import ErdosProblems.Problem1

open Filter

namespace Erdos1

/-- A simple explicit upper bound on the Stirling sequence, enough for a `1/4` lower constant. -/
theorem stirlingSeq_le_two {n : ℕ} (hn : n ≠ 0) : Stirling.stirlingSeq n ≤ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  have hmono : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa using Stirling.stirlingSeq'_antitone (show 0 ≤ m by exact Nat.zero_le _)
  rw [Stirling.stirlingSeq_one] at hmono
  have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num : (7 / 5 : ℝ) ^ 2 < 2)
  have hexp : Real.exp 1 < 2 * Real.sqrt 2 := by
    have h14 : Real.exp 1 < (14 / 5 : ℝ) := by
      exact lt_trans Real.exp_one_lt_d9 (by norm_num)
    nlinarith
  have hbound : Real.exp 1 / Real.sqrt 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    exact hexp.le
  exact hmono.trans hbound

/-- A concrete upper Stirling bound derived from `stirlingSeq_le_two`. -/
theorem factorial_le_two_mul_stirling {n : ℕ} (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) ≤ 2 * (Real.sqrt (2 * n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n)) := by
  have hratio : Stirling.stirlingSeq n ≤ 2 := stirlingSeq_le_two hn
  rw [Stirling.stirlingSeq] at hratio
  have hpos : 0 < Real.sqrt (2 * n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) := by
    positivity
  exact (div_le_iff₀ hpos).mp hratio

/-- Squared version of `factorial_le_two_mul_stirling`, with the constants simplified. -/
theorem factorial_sq_le_eight_mul_stirling {n : ℕ} (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) ≤ 8 * n * ((((n : ℝ) / Real.exp 1) ^ n) ^ 2) := by
  let a : ℝ := (((n : ℝ) / Real.exp 1) ^ n)
  have hfact : (Nat.factorial n : ℝ) ≤ 2 * (Real.sqrt (2 * n : ℝ) * a) := by
    simpa [a] using factorial_le_two_mul_stirling hn
  have hsq :
      (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) ≤
        (2 * (Real.sqrt (2 * n : ℝ) * a)) * (2 * (Real.sqrt (2 * n : ℝ) * a)) := by
    exact mul_le_mul hfact hfact (by positivity) (by positivity)
  calc
    (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)
        ≤ (2 * (Real.sqrt (2 * n : ℝ) * a)) * (2 * (Real.sqrt (2 * n : ℝ) * a)) := hsq
    _ = 8 * n * (a ^ 2) := by
      ring_nf
      rw [Real.sq_sqrt (by positivity)]
      ring

/-- Casted factorial formula for the central binomial coefficient. -/
theorem cast_centralBinom_eq_factorial_ratio (n : ℕ) :
    (Nat.centralBinom n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.add_choose]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial_add n n) (by positivity)]
  simp [Nat.cast_mul]

/--
An explicit middle-binomial lower bound at the `1 / 4` scale, proved from global Stirling bounds.
-/
theorem quarter_four_pow_div_sqrt_le_centralBinom (n : ℕ) :
    (1 / 4 : ℝ) * 4 ^ n / (n : ℝ).sqrt ≤ Nat.centralBinom n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.centralBinom_zero]
  · let a : ℝ := (((n : ℝ) / Real.exp 1) ^ n)
    have hden_pos : 0 < (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) := by positivity
    have hden_le : (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) ≤ 8 * n * (a ^ 2) := by
      simpa [a] using factorial_sq_le_eight_mul_stirling hn
    have hnum_le :
        Real.sqrt (2 * Real.pi * (2 * n : ℝ)) *
            ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) ≤ (Nat.factorial (2 * n) : ℝ) := by
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
        (Stirling.le_factorial_stirling (2 * n))
    have hchoose := cast_centralBinom_eq_factorial_ratio n
    rw [hchoose, le_div_iff₀ hden_pos]
    have hsqrt_ne : (n : ℝ).sqrt ≠ 0 := by
      exact Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hdiv : (n : ℝ) / (n : ℝ).sqrt = (n : ℝ).sqrt := by
      rw [div_eq_iff hsqrt_ne]
      simpa [sq] using (Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)).symm
    have hsqrt :
        2 * (n : ℝ).sqrt ≤ Real.sqrt (2 * Real.pi * (2 * n : ℝ)) := by
      apply Real.le_sqrt_of_sq_le
      have hsq : (2 * (n : ℝ).sqrt) ^ 2 = (4 : ℝ) * n := by
        ring_nf
        rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      rw [hsq]
      nlinarith [Real.pi_gt_three, show (0 : ℝ) ≤ n by positivity]
    have hpow :
        (4 : ℝ) ^ n * (a ^ 2) = ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) := by
      rw [show (((2 * n : ℕ) : ℝ) / Real.exp 1) = 2 * ((n : ℝ) / Real.exp 1) by
        simp [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]]
      rw [mul_pow, pow_mul]
      norm_num
      rw [show (((n : ℝ) / Real.exp 1) ^ (2 * n)) = (a ^ 2) by
        rw [Nat.mul_comm, pow_mul]]
    have hmain :
        (1 / 4 : ℝ) * 4 ^ n / (n : ℝ).sqrt *
          ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))
          ≤ Real.sqrt (2 * Real.pi * (2 * n : ℝ)) *
              ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) := by
      calc
        (1 / 4 : ℝ) * 4 ^ n / (n : ℝ).sqrt *
            ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))
            ≤ (1 / 4 : ℝ) * 4 ^ n / (n : ℝ).sqrt * (8 * n * (a ^ 2)) := by
              gcongr
        _ = 2 * a ^ 2 * (4 : ℝ) ^ n * (n : ℝ).sqrt := by
          calc
            (1 / 4 : ℝ) * 4 ^ n / (n : ℝ).sqrt * (8 * n * (a ^ 2))
                = 2 * (4 : ℝ) ^ n * a ^ 2 * ((n : ℝ) / (n : ℝ).sqrt) := by ring
            _ = 2 * (4 : ℝ) ^ n * a ^ 2 * (n : ℝ).sqrt := by rw [hdiv]
            _ = 2 * a ^ 2 * (4 : ℝ) ^ n * (n : ℝ).sqrt := by ring
        _ = (2 * (n : ℝ).sqrt) * ((4 : ℝ) ^ n * (a ^ 2)) := by ring
        _ ≤ Real.sqrt (2 * Real.pi * (2 * n : ℝ)) * ((4 : ℝ) ^ n * (a ^ 2)) := by
          exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
        _ = Real.sqrt (2 * Real.pi * (2 * n : ℝ)) *
              ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) := by rw [hpow]
    exact hmain.trans hnum_le

/-- Explicit `1 / 4` lower bound for the middle binomial coefficient. -/
theorem choose_middle_lower_quarter (n : ℕ) :
    (1 / 4 : ℝ) * 2 ^ n / (n : ℝ).sqrt ≤ Nat.choose n (n / 2) := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases even_iff_exists_two_mul.mp hEven with ⟨m, hm_even⟩
    rw [hm_even]
    by_cases hm : m = 0
    · norm_num [hm]
    · have hm_sqrt_pos : 0 < (m : ℝ).sqrt := by
        exact Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
      have htwo_sqrt_pos : 0 < ((2 * m : ℕ) : ℝ).sqrt := by
        positivity
      have hsqrt : (m : ℝ).sqrt ≤ ((2 * m : ℕ) : ℝ).sqrt := by
        have hle : (m : ℝ) ≤ (2 * m : ℝ) := by nlinarith
        simpa [Nat.cast_mul] using Real.sqrt_le_sqrt hle
      have hscale :
          (1 / 4 : ℝ) * 2 ^ (2 * m) / ((2 * m : ℕ) : ℝ).sqrt ≤
            (1 / 4 : ℝ) * 4 ^ m / (m : ℝ).sqrt := by
        rw [show (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m by
          rw [pow_mul]
          norm_num]
        have hsqrt_inv : (((2 * m : ℕ) : ℝ).sqrt)⁻¹ ≤ ((m : ℝ).sqrt)⁻¹ := by
          exact (inv_le_inv₀ htwo_sqrt_pos hm_sqrt_pos).2 hsqrt
        have hscaled := mul_le_mul_of_nonneg_left hsqrt_inv
          (by positivity : 0 ≤ (1 / 4 : ℝ) * (4 : ℝ) ^ m)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact hscale.trans (by simpa [Nat.centralBinom_eq_two_mul_choose] using
        quarter_four_pow_div_sqrt_le_centralBinom m)
  · rcases odd_iff_exists_bit1.mp hOdd with ⟨m, hm_odd⟩
    rw [hm_odd]
    by_cases hm : m = 0
    · norm_num [hm]
    · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
      have hm_sqrt_pos : 0 < (m : ℝ).sqrt := Real.sqrt_pos.2 hm_pos
      have hodd_sqrt_pos : 0 < ((2 * m + 1 : ℕ) : ℝ).sqrt := by positivity
      have hchoose_nat :
          Nat.centralBinom m * (2 * m + 1) = Nat.choose (2 * m + 1) m * (m + 1) := by
        have hsub : 2 * m + 1 - m = m + 1 := by omega
        simpa [Nat.centralBinom_eq_two_mul_choose, hsub] using Nat.choose_mul_succ_eq (2 * m) m
      have hchoose :
          (Nat.centralBinom m : ℝ) * (2 * m + 1) =
            (Nat.choose (2 * m + 1) m : ℝ) * (m + 1) := by
        exact_mod_cast hchoose_nat
      have hscale_sq :
          (2 * (m + 1 : ℝ) * (m : ℝ).sqrt) ^ 2 ≤
            ((((2 * m + 1 : ℕ) : ℝ).sqrt) * (2 * m + 1)) ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt hm_pos.le, Real.sq_sqrt (by positivity)]
        have hpoly : 0 ≤ 4 * (m : ℝ) ^ 3 + 4 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 := by
          positivity
        norm_num [Nat.cast_mul, Nat.cast_add] at hpoly ⊢
        ring_nf at hpoly ⊢
        nlinarith
      have hscale_core :
          2 * (m + 1 : ℝ) * (m : ℝ).sqrt ≤
            (((2 * m + 1 : ℕ) : ℝ).sqrt) * (2 * m + 1) := by
        exact le_of_sq_le_sq hscale_sq (by positivity)
      have hscale :
          ((1 / 4 : ℝ) * 2 ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ).sqrt) * (m + 1)
            ≤ ((1 / 4 : ℝ) * 4 ^ m / (m : ℝ).sqrt) * (2 * m + 1) := by
        rw [show (2 : ℝ) ^ (2 * m + 1) = 2 * (4 : ℝ) ^ m by
          rw [pow_add, show (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m by
            rw [pow_mul]
            norm_num]
          ring]
        have hscaled := mul_le_mul_of_nonneg_left hscale_core
          (by positivity :
            0 ≤ (1 / 4 : ℝ) * (4 : ℝ) ^ m /
                ((((2 * m + 1 : ℕ) : ℝ).sqrt) * (m : ℝ).sqrt))
        calc
          ((1 / 4 : ℝ) * (2 * (4 : ℝ) ^ m) / ((2 * m + 1 : ℕ) : ℝ).sqrt) * (m + 1)
              = ((1 / 4 : ℝ) * (4 : ℝ) ^ m /
                    ((((2 * m + 1 : ℕ) : ℝ).sqrt) * (m : ℝ).sqrt)) *
                  (2 * (m + 1 : ℝ) * (m : ℝ).sqrt) := by
                    field_simp [hm_sqrt_pos.ne', hodd_sqrt_pos.ne']
          _ ≤ ((1 / 4 : ℝ) * (4 : ℝ) ^ m /
                    ((((2 * m + 1 : ℕ) : ℝ).sqrt) * (m : ℝ).sqrt)) *
                  ((((2 * m + 1 : ℕ) : ℝ).sqrt) * (2 * m + 1)) := hscaled
          _ = ((1 / 4 : ℝ) * (4 : ℝ) ^ m / (m : ℝ).sqrt) * (2 * m + 1) := by
                field_simp [hm_sqrt_pos.ne', hodd_sqrt_pos.ne']
      have hhalf : (2 * m + 1) / 2 = m := by omega
      have hmul :
          ((1 / 4 : ℝ) * 2 ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ).sqrt) * (m + 1)
            ≤ (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ) * (m + 1) := by
        calc
          ((1 / 4 : ℝ) * 2 ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ).sqrt) * (m + 1)
              ≤ ((1 / 4 : ℝ) * 4 ^ m / (m : ℝ).sqrt) * (2 * m + 1) := hscale
          _ ≤ (Nat.centralBinom m : ℝ) * (2 * m + 1) := by
            gcongr
            exact quarter_four_pow_div_sqrt_le_centralBinom m
          _ = (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ) * (m + 1) := by
            simpa [hhalf] using hchoose
      exact le_of_mul_le_mul_right hmul (show (0 : ℝ) < m + 1 by positivity)

/--
Imported exact lower bound from Dubroff-Fox-Xu (2021): if `A ⊆ {1, ..., N}` is sum-distinct, then
`N` is at least the middle binomial coefficient `choose |A| ⌊|A| / 2⌋`.
-/
axiom erdos_1_dubroff_fox_xu_lower_exact :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      Nat.choose A.card (A.card / 2) ≤ N

/--
Imported real-valued analogue from the same line of work: the spacing variant also satisfies the
same middle-binomial lower bound.
-/
axiom erdos_1_real_dubroff_fox_xu_lower_exact :
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      Nat.choose A.card (A.card / 2) ≤ N

/--
Asymptotic lower control on the middle binomial coefficient at the sharp `sqrt (2 / pi)` scale.
This is the purely analytic/binomial ingredient needed to derive the standard Erdős-Moser style
lower bounds for Problem #1 from the exact Dubroff-Fox-Xu theorem.
-/
axiom choose_middle_lb_strong_asymptotic_axiom :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ n : ℕ,
        (Real.sqrt (2 / Real.pi) - o n) * 2 ^ n / (n : ℝ).sqrt ≤ Nat.choose n (n / 2)

/--
Imported Bohman upper construction: for all sufficiently large `n`, there exists an `n`-element
sum-distinct set inside `{1, ..., N}` with `N ≤ 0.22002 * 2^n`.
-/
axiom erdos_1_bohman_upper_construction :
    ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, HasSumDistinctSetCard N n ∧ (N : ℝ) ≤ (0.22002 : ℝ) * 2 ^ n

/-- Literature-facing proposition for the best known Bohman upper construction. -/
def BohmanUpperConstruction : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ N : ℕ, HasSumDistinctSetCard N n ∧ (N : ℝ) ≤ (0.22002 : ℝ) * 2 ^ n

/-- Literature-facing proposition for the sharp `sqrt (2 / pi)` lower envelope. -/
def DubroffFoxXuSharpLowerBound : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/-- Real-valued counterpart of `DubroffFoxXuSharpLowerBound`. -/
def DubroffFoxXuSharpLowerBoundReal : Prop :=
  ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/-- Honest current literature gap surface for the integer problem. -/
def BestKnownIntegerGap : Prop :=
  BohmanUpperConstruction ∧ DubroffFoxXuSharpLowerBound

/--
Expose the existing open-problem placeholder under a `solution_axiom` name, mirroring the
repository's `Problem142` surface.
-/
theorem erdos_1_solution_axiom :
    ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N :=
  erdos_1

/-- Short imported wrapper for the exact integer lower bound. -/
theorem erdos_1_lower_bound_exact_imported {N : ℕ} {A : Finset ℕ}
    (h : IsSumDistinctSet A N) : Nat.choose A.card (A.card / 2) ≤ N :=
  erdos_1_dubroff_fox_xu_lower_exact N A h

/-- Short imported wrapper for the exact real-valued lower bound. -/
theorem erdos_1_real_lower_bound_exact_imported {N : ℕ} {A : Finset ℝ}
    (h : IsSumDistinctRealSet A N) : Nat.choose A.card (A.card / 2) ≤ N :=
  erdos_1_real_dubroff_fox_xu_lower_exact N A h

/-- The middle binomial coefficient dominates the average binomial coefficient. -/
theorem two_pow_le_succ_mul_choose_middle (n : ℕ) :
    2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) := by
  calc
    2 ^ n = ∑ m ∈ Finset.range (n + 1), Nat.choose n m := by
      symm
      exact Nat.sum_range_choose n
    _ ≤ ∑ _m ∈ Finset.range (n + 1), Nat.choose n (n / 2) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact Nat.choose_le_middle m n
    _ = (n + 1) * Nat.choose n (n / 2) := by simp

/-- Real-valued version of `two_pow_le_succ_mul_choose_middle`. -/
theorem two_pow_div_succ_le_choose_middle (n : ℕ) :
    ((2 : ℝ) ^ n) / (n + 1) ≤ Nat.choose n (n / 2) := by
  have hnat : 2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) :=
    two_pow_le_succ_mul_choose_middle n
  have hreal : ((2 : ℝ) ^ n) ≤ (n + 1 : ℝ) * Nat.choose n (n / 2) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_iff₀ hpos, mul_comm]
  exact hreal

/-- Exact imported lower bound implies a clean `2^n / (n + 1)` lower bound. -/
theorem two_pow_div_card_succ_le_of_isSumDistinct {N : ℕ} {A : Finset ℕ}
    (h : IsSumDistinctSet A N) : ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N := by
  refine (two_pow_div_succ_le_choose_middle A.card).trans ?_
  exact_mod_cast erdos_1_lower_bound_exact_imported h

/-- Real-valued spacing variant also inherits the `2^n / (n + 1)` lower bound. -/
theorem two_pow_div_card_succ_le_of_isSumDistinctReal {N : ℕ} {A : Finset ℝ}
    (h : IsSumDistinctRealSet A N) : ((2 : ℝ) ^ A.card) / (A.card + 1) ≤ N := by
  refine (two_pow_div_succ_le_choose_middle A.card).trans ?_
  exact_mod_cast erdos_1_real_lower_bound_exact_imported h

/-- The classical `1 / 4` lower-bound package follows from the explicit middle-binomial bound. -/
theorem erdos_1_variants_lb_from_explicit_choose_middle :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simpa using (Asymptotics.isLittleO_zero (g' := (1 : ℕ → ℝ)) (l := atTop))
  · intro N A hA
    simpa using
      (choose_middle_lower_quarter A.card).trans
        (by exact_mod_cast erdos_1_lower_bound_exact_imported hA)

/-- Real-valued `1 / 4` lower-bound package from the same explicit middle-binomial theorem. -/
theorem erdos_1_real_variants_lb_from_explicit_choose_middle :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simpa using (Asymptotics.isLittleO_zero (g' := (1 : ℕ → ℝ)) (l := atTop))
  · intro N A hA
    simpa using
      (choose_middle_lower_quarter A.card).trans
        (by exact_mod_cast erdos_1_real_lower_bound_exact_imported hA)

/-- Derived sharp-constant lower bound from the exact import plus binomial asymptotics. -/
theorem erdos_1_variants_lb_strong_from_choose_middle_asymptotic :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  rcases choose_middle_lb_strong_asymptotic_axiom with ⟨o, ho, hchoose⟩
  refine ⟨o, ho, ?_⟩
  intro N A hA
  exact (hchoose A.card).trans (by exact_mod_cast erdos_1_lower_bound_exact_imported hA)

/-- Real-valued sharp lower bound from the same binomial asymptotic input. -/
theorem erdos_1_real_variants_lb_strong_from_choose_middle_asymptotic :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  rcases choose_middle_lb_strong_asymptotic_axiom with ⟨o, ho, hchoose⟩
  refine ⟨o, ho, ?_⟩
  intro N A hA
  exact (hchoose A.card).trans (by exact_mod_cast erdos_1_real_lower_bound_exact_imported hA)

/-- The classical `1 / 4` lower-bound variant follows from the stronger sharp-constant version. -/
theorem erdos_1_variants_lb_from_choose_middle_asymptotic :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  rcases erdos_1_variants_lb_strong_from_choose_middle_asymptotic with ⟨o, ho, hstrong⟩
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

/-- The imported Bohman statement is exactly the local upper-construction surface. -/
theorem bohmanUpperConstruction_imported : BohmanUpperConstruction :=
  erdos_1_bohman_upper_construction

/-- The exact import plus the middle-binomial asymptotic input give the sharp lower surface. -/
theorem dubroffFoxXuSharpLowerBound_from_imports : DubroffFoxXuSharpLowerBound :=
  erdos_1_variants_lb_strong_from_choose_middle_asymptotic

/-- Imported exact lower bound plus the explicit middle-binomial theorem give the `1 / 4` surface. -/
theorem erdos_1_variants_lb_from_imports :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_variants_lb_from_explicit_choose_middle

/-- Real-valued sharp lower surface from the same imported ingredients. -/
theorem dubroffFoxXuSharpLowerBoundReal_from_imports : DubroffFoxXuSharpLowerBoundReal :=
  erdos_1_real_variants_lb_strong_from_choose_middle_asymptotic

/-- Real-valued `1 / 4` lower package from the same explicit middle-binomial theorem. -/
theorem erdos_1_real_variants_lb_from_imports :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1_real_variants_lb_from_explicit_choose_middle

/-- Honest package of the current best known upper and lower results for the integer problem. -/
theorem bestKnownIntegerGap_from_imports : BestKnownIntegerGap :=
  ⟨bohmanUpperConstruction_imported, dubroffFoxXuSharpLowerBound_from_imports⟩

end Erdos1
