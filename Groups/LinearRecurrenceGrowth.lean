import Groups.GeodesicGrowth

/-!
# Growth theory for linear-recurrence sequences

This file develops the analytic ingredients needed to discharge the "asymptotic to
irrationality" bridge for Brönnimann's Question 3 (axiom `A3`).

The mathematical content:

* `modelGrowthReal n = exp (n^{3/5} · log n)` is **super-polynomial** (grows faster than any
  polynomial) and **sub-exponential** (grows slower than any geometric sequence `(1+ε)^n`).
* A constant-coefficient linear-recurrence integer sequence with sub-exponential growth is
  polynomially bounded (the hard kernel, proved elsewhere in this file).

Combining these yields: a sequence pinched between `c₁ · modelGrowth` and `c₂ · modelGrowth`
cannot satisfy a linear recurrence, which is exactly what irrational geodesic growth requires.
-/

open Filter Topology
open scoped Filter

namespace LinearRecurrenceGrowth

/-- The real comparison function `exp(n^{3/5} · log n)` appearing in Bodart's estimate. -/
noncomputable def modelGrowthReal (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ))

lemma modelGrowthReal_pos (n : ℕ) : 0 < modelGrowthReal n :=
  Real.exp_pos _

/-- The logarithm of `modelGrowthReal`. -/
lemma log_modelGrowthReal (n : ℕ) :
    Real.log (modelGrowthReal n) = (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) := by
  rw [modelGrowthReal, Real.log_exp]

/-- `n^{2/5} · n^{3/5} = n` as reals, for `0 < n`. -/
private lemma rpow_two_fifths_mul_three_fifths {x : ℝ} (hx : 0 < x) :
    x ^ ((2 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) = x := by
  rw [← Real.rpow_add hx]
  norm_num

/-- `modelGrowthReal` is **sub-exponential**: it grows slower than any geometric sequence
`(1 + ε)^n`. -/
lemma modelGrowthReal_lt_geometric {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, modelGrowthReal n < (1 + ε) ^ n := by
  set L : ℝ := Real.log (1 + ε) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  -- eventually `log n ≤ (L/2) · n^{2/5}`, from `log = o(n^{2/5})`.
  have hlittle : Real.log =o[atTop] fun x : ℝ => x ^ ((2 : ℝ) / 5) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hbound : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (L / 2) * ‖x ^ ((2 : ℝ) / 5)‖ :=
    (Asymptotics.isLittleO_iff.mp hlittle) (by positivity)
  have hbound' : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ (L / 2) * (n : ℝ) ^ ((2 : ℝ) / 5) := by
    have hpb := tendsto_natCast_atTop_atTop.eventually hbound
    filter_upwards [hpb, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := le_abs_self _
    have h2 : ‖(n : ℝ) ^ ((2 : ℝ) / 5)‖ = (n : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)
    calc Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := h1
      _ ≤ (L / 2) * ‖(n : ℝ) ^ ((2 : ℝ) / 5)‖ := hn
      _ = (L / 2) * (n : ℝ) ^ ((2 : ℝ) / 5) := by rw [h2]
  filter_upwards [hbound', eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  -- `n^{3/5} · log n ≤ (L/2) · n < L · n`.
  have hkey : (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) < L * (n : ℝ) := by
    have hmul : (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)
        ≤ (n : ℝ) ^ ((3 : ℝ) / 5) * ((L / 2) * (n : ℝ) ^ ((2 : ℝ) / 5)) := by
      apply mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hnpos.le _)
    have hcollapse : (n : ℝ) ^ ((3 : ℝ) / 5) * ((L / 2) * (n : ℝ) ^ ((2 : ℝ) / 5))
        = (L / 2) * (n : ℝ) := by
      have hr := rpow_two_fifths_mul_three_fifths hnpos
      have : (n : ℝ) ^ ((3 : ℝ) / 5) * (n : ℝ) ^ ((2 : ℝ) / 5) = (n : ℝ) := by
        rw [mul_comm]; exact hr
      calc (n : ℝ) ^ ((3 : ℝ) / 5) * ((L / 2) * (n : ℝ) ^ ((2 : ℝ) / 5))
          = (L / 2) * ((n : ℝ) ^ ((3 : ℝ) / 5) * (n : ℝ) ^ ((2 : ℝ) / 5)) := by ring
        _ = (L / 2) * (n : ℝ) := by rw [this]
    have hlt : (L / 2) * (n : ℝ) < L * (n : ℝ) := by nlinarith [hLpos, hnpos]
    calc (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)
        ≤ (L / 2) * (n : ℝ) := by rw [← hcollapse]; exact hmul
      _ < L * (n : ℝ) := hlt
  -- exponentiate.
  have hRHS : ((1 + ε) : ℝ) ^ n = Real.exp (L * (n : ℝ)) := by
    rw [hL, ← Real.rpow_natCast (1 + ε) n, Real.rpow_def_of_pos (by linarith)]
  rw [modelGrowthReal, hRHS]
  exact Real.exp_lt_exp.mpr hkey

/-- `modelGrowthReal` is **super-polynomial**: it eventually dominates `A · (n+1)^k` for every
real `A` and exponent `k`. -/
lemma poly_lt_modelGrowthReal (A : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, A * ((n : ℝ) + 1) ^ k < modelGrowthReal n := by
  -- eventually `log(n) ≤ n^{2/5}` (from `log = o(n^{2/5})` with constant `1`).
  have hlittle : Real.log =o[atTop] fun x : ℝ => x ^ ((2 : ℝ) / 5) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hbnd : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 : ℝ) * ‖x ^ ((2 : ℝ) / 5)‖ :=
    (Asymptotics.isLittleO_iff.mp hlittle) (by norm_num)
  have hlogle : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := by
    have hpb := tendsto_natCast_atTop_atTop.eventually hbnd
    filter_upwards [hpb, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2 : ‖(n : ℝ) ^ ((2 : ℝ) / 5)‖ = (n : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)
    calc Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := le_abs_self _
      _ ≤ (1 : ℝ) * ‖(n : ℝ) ^ ((2 : ℝ) / 5)‖ := hn
      _ = (n : ℝ) ^ ((2 : ℝ) / 5) := by rw [h2]; ring
  -- It suffices to show the exponent `n^{3/5} log n` dominates `log A + k log(n+1)`.
  -- We instead show `A · (n+1)^k < exp(n^{3/5} log n)` by comparing logs on a suitable tail.
  -- Concretely, eventually `log(A·(n+1)^k) < n^{3/5} log n` and both sides describe positives.
  -- Reduce to the exponent inequality via `Real.lt_exp` style bound.
  have hexp : ∀ᶠ n : ℕ in atTop,
      Real.log (|A| + 1) + (k : ℝ) * Real.log ((n : ℝ) + 1)
        < (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) := by
    -- `log((n)+1) ≤ 2 log n` eventually, and `n^{3/5} ≥ (k+1)·2 + C` eventually.
    have hlog1 : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with n hn1
      have hnpos : (1 : ℝ) < n := by exact_mod_cast hn1
      have hnge : (2 : ℝ) ≤ n := by exact_mod_cast hn1
      have hle : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith [hnge]
      have := Real.log_le_log (by linarith) hle
      rwa [Real.log_pow] at this
      -- `log(n^2) = 2 log n`
    have hbig : ∀ᶠ n : ℕ in atTop,
        Real.log (|A| + 1) + (k : ℝ) * (2 * Real.log (n : ℝ))
          < (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) := by
      -- choose threshold: need `n^{3/5} > 2k+1` and `log n > 0` and `log(|A|+1) < log n`.
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 5)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      have hlogtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hpow.eventually_gt_atTop (2 * (k : ℝ) + 1),
        hlogtop.eventually_gt_atTop (Real.log (|A| + 1) + 1),
        hlogtop.eventually_gt_atTop 0] with n hpk hlA hlpos
      have hkey : (2 * (k : ℝ) + 1) * Real.log (n : ℝ)
          ≤ (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hpk.le hlpos.le
      nlinarith [hkey, hlA, hlpos]
    filter_upwards [hlog1, hbig] with n hn1 hn2
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have : (k : ℝ) * Real.log ((n : ℝ) + 1) ≤ (k : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn1 hk0
    linarith
  filter_upwards [hexp, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  -- Turn the exponent inequality into the target using positivity and exp/log.
  have hApos : (0 : ℝ) < |A| + 1 := by positivity
  have hpow_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  have hLHS_le : A * ((n : ℝ) + 1) ^ k ≤ (|A| + 1) * ((n : ℝ) + 1) ^ k := by
    apply mul_le_mul_of_nonneg_right _ hpow_pos.le
    nlinarith [le_abs_self A]
  have hlogLHS : Real.log ((|A| + 1) * ((n : ℝ) + 1) ^ k)
      = Real.log (|A| + 1) + (k : ℝ) * Real.log ((n : ℝ) + 1) := by
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hpow_pos), Real.log_pow]
  have hpos_prod : (0 : ℝ) < (|A| + 1) * ((n : ℝ) + 1) ^ k := by positivity
  have hlt2 : (|A| + 1) * ((n : ℝ) + 1) ^ k < modelGrowthReal n := by
    rw [modelGrowthReal]
    have := hn
    rw [← hlogLHS] at this
    calc (|A| + 1) * ((n : ℝ) + 1) ^ k
        = Real.exp (Real.log ((|A| + 1) * ((n : ℝ) + 1) ^ k)) :=
          (Real.exp_log hpos_prod).symm
      _ < Real.exp ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)) := Real.exp_lt_exp.mpr this
  linarith

/-- The rescaled comparison function `exp(κ · n^{3/5} · log n)` with an exponent constant
`κ`. For `κ = 1` this is `modelGrowthReal`. It is the lower-bound model appearing in Bodart's
estimate, whose lower half only controls the exponent up to a smaller constant `κ < 1`. -/
noncomputable def scaledModelGrowthReal (κ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (κ * ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)))

lemma scaledModelGrowthReal_pos (κ : ℝ) (n : ℕ) : 0 < scaledModelGrowthReal κ n :=
  Real.exp_pos _

/-- For every positive exponent constant `κ`, the rescaled model `exp(κ · n^{3/5} · log n)` is
still **super-polynomial**: it eventually dominates `A · (n+1)^k` for every real `A` and `k`. -/
lemma poly_lt_scaledModelGrowthReal (κ : ℝ) (hκ : 0 < κ) (A : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, A * ((n : ℝ) + 1) ^ k < scaledModelGrowthReal κ n := by
  have hexp : ∀ᶠ n : ℕ in atTop,
      Real.log (|A| + 1) + (k : ℝ) * Real.log ((n : ℝ) + 1)
        < κ * ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)) := by
    have hlog1 : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with n hn1
      have hnge : (2 : ℝ) ≤ n := by exact_mod_cast hn1
      have hle : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith [hnge]
      have := Real.log_le_log (by linarith) hle
      rwa [Real.log_pow] at this
    have hbig : ∀ᶠ n : ℕ in atTop,
        Real.log (|A| + 1) + (k : ℝ) * (2 * Real.log (n : ℝ))
          < κ * ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ)) := by
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 5)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      have hlogtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hpow.eventually_gt_atTop ((2 * (k : ℝ) + 1) / κ),
        hlogtop.eventually_gt_atTop (Real.log (|A| + 1) + 1),
        hlogtop.eventually_gt_atTop 0] with n hpk hlA hlpos
      have hpk' : (2 * (k : ℝ) + 1) < κ * (n : ℝ) ^ ((3 : ℝ) / 5) := by
        rw [div_lt_iff₀ hκ] at hpk; linarith [hpk]
      have hkey : (2 * (k : ℝ) + 1) * Real.log (n : ℝ)
          ≤ κ * (n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right hpk'.le hlpos.le
      nlinarith [hkey, hlA, hlpos]
    filter_upwards [hlog1, hbig] with n hn1 hn2
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have : (k : ℝ) * Real.log ((n : ℝ) + 1) ≤ (k : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn1 hk0
    linarith
  filter_upwards [hexp, eventually_gt_atTop 0] with n hn hn0
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hApos : (0 : ℝ) < |A| + 1 := by positivity
  have hpow_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  have hLHS_le : A * ((n : ℝ) + 1) ^ k ≤ (|A| + 1) * ((n : ℝ) + 1) ^ k := by
    apply mul_le_mul_of_nonneg_right _ hpow_pos.le
    nlinarith [le_abs_self A]
  have hlogLHS : Real.log ((|A| + 1) * ((n : ℝ) + 1) ^ k)
      = Real.log (|A| + 1) + (k : ℝ) * Real.log ((n : ℝ) + 1) := by
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hpow_pos), Real.log_pow]
  have hpos_prod : (0 : ℝ) < (|A| + 1) * ((n : ℝ) + 1) ^ k := by positivity
  have hlt2 : (|A| + 1) * ((n : ℝ) + 1) ^ k < scaledModelGrowthReal κ n := by
    rw [scaledModelGrowthReal]
    have hthis := hn
    rw [← hlogLHS] at hthis
    calc (|A| + 1) * ((n : ℝ) + 1) ^ k
        = Real.exp (Real.log ((|A| + 1) * ((n : ℝ) + 1) ^ k)) :=
          (Real.exp_log hpos_prod).symm
      _ < Real.exp (κ * ((n : ℝ) ^ ((3 : ℝ) / 5) * Real.log (n : ℝ))) :=
          Real.exp_lt_exp.mpr hthis
  linarith

/-!
## Nilpotent growth bound

The heart of the "sub-exponential ⇒ polynomial" kernel: if `T = a + b` with `a`, `b` commuting,
`b` nilpotent of index `d`, and `‖a‖ ≤ 1`, then the powers `‖T^n‖` grow at most polynomially.
Applied per generalized eigenspace of the companion operator (where `a = λ • 1` with `|λ| ≤ 1`
and `b` the nilpotent part), this yields a polynomial bound on the whole orbit.
-/

open Finset in
/-- Binomial growth bound for a commuting sum of a norm-`≤ 1` element and a nilpotent element. -/
lemma norm_add_pow_nilpotent_le {A : Type*} [NormedRing A] [NormOneClass A]
    {a b : A} (hab : Commute a b) {d : ℕ} (hbd : b ^ d = 0)
    (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖(a + b) ^ n‖ ≤ ((n : ℝ) + 1) ^ d * ∑ m ∈ range d, ‖b‖ ^ m := by
  have hcomm : Commute b a := hab.symm
  have hexpand : (a + b) ^ n = ∑ m ∈ range (n + 1), b ^ m * a ^ (n - m) * ↑(n.choose m) := by
    rw [add_comm a b, hcomm.add_pow]
  rw [hexpand]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ range (n + 1),
      ‖b ^ m * a ^ (n - m) * ↑(n.choose m)‖
        ≤ (if m < d then ((n : ℝ) + 1) ^ d * ‖b‖ ^ m else 0) := by
    intro m _
    by_cases hmd : m < d
    · rw [if_pos hmd]
      -- rewrite the natCast multiplication as an `nsmul`
      have hcast : b ^ m * a ^ (n - m) * ↑(n.choose m)
          = (n.choose m) • (b ^ m * a ^ (n - m)) := by
        rw [nsmul_eq_mul]
        rw [(Nat.cast_commute (n.choose m) (b ^ m * a ^ (n - m))).eq]
      rw [hcast]
      calc ‖(n.choose m) • (b ^ m * a ^ (n - m))‖
          ≤ (n.choose m : ℝ) * ‖b ^ m * a ^ (n - m)‖ := norm_nsmul_le
        _ ≤ (n.choose m : ℝ) * (‖b‖ ^ m * ‖a‖ ^ (n - m)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc ‖b ^ m * a ^ (n - m)‖ ≤ ‖b ^ m‖ * ‖a ^ (n - m)‖ := norm_mul_le _ _
              _ ≤ ‖b‖ ^ m * ‖a‖ ^ (n - m) :=
                    mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
                      (by positivity) (by positivity)
        _ ≤ (n.choose m : ℝ) * (‖b‖ ^ m * 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_one₀ (norm_nonneg _) ha
        _ = (n.choose m : ℝ) * ‖b‖ ^ m := by ring
        _ ≤ ((n : ℝ) + 1) ^ d * ‖b‖ ^ m := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (n.choose m : ℝ) ≤ ((n : ℝ)) ^ m := by
                  exact_mod_cast Nat.choose_le_pow n m
              _ ≤ ((n : ℝ) + 1) ^ m := by
                    apply pow_le_pow_left₀ (by positivity); linarith
              _ ≤ ((n : ℝ) + 1) ^ d := by
                    apply pow_le_pow_right₀ (by linarith) (le_of_lt hmd)
    · rw [if_neg hmd]
      have hb0 : b ^ m = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, m = d + k := ⟨m - d, by omega⟩
        rw [pow_add, hbd, zero_mul]
      simp [hb0]
  calc ∑ m ∈ range (n + 1), ‖b ^ m * a ^ (n - m) * ↑(n.choose m)‖
      ≤ ∑ m ∈ range (n + 1), (if m < d then ((n : ℝ) + 1) ^ d * ‖b‖ ^ m else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ m ∈ (range (n + 1)).filter (· < d), ((n : ℝ) + 1) ^ d * ‖b‖ ^ m := by
        rw [Finset.sum_filter]
    _ ≤ ∑ m ∈ range d, ((n : ℝ) + 1) ^ d * ‖b‖ ^ m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_filter] at hm
          exact Finset.mem_range.mpr hm.2
        · intro m _ _; positivity
    _ = ((n : ℝ) + 1) ^ d * ∑ m ∈ range d, ‖b‖ ^ m := by rw [Finset.mul_sum]

open Finset in
/-- **Vector-wise generalized-eigenvector growth bound.**  If `v` is a generalized
eigenvector of the operator `T` for an eigenvalue `μ` of modulus `≤ 1`, killed by
`(T - μ)^d`, then the orbit `‖Tⁿ v‖` grows at most polynomially (degree `d`).  This is the
per-eigenspace estimate used to deduce polynomial growth of `‖Tⁿ‖` from spectral radius
`≤ 1`, without appealing to Jordan normal form. -/
theorem norm_pow_apply_le_of_pow_sub_smul_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : V →L[ℂ] V) {μ : ℂ} (hμ : ‖μ‖ ≤ 1) {d : ℕ} {v : V}
    (hv : ((T - μ • 1) ^ d) v = 0) (n : ℕ) :
    ‖(T ^ n) v‖ ≤ ((n : ℝ) + 1) ^ d *
      (∑ j ∈ Finset.range d, ‖(T - μ • (1 : V →L[ℂ] V))‖ ^ j) * ‖v‖ := by
  set b : V →L[ℂ] V := T - μ • 1 with hb
  have hnpow : ∀ (m : ℕ) (w : V), ‖(b ^ m) w‖ ≤ ‖b‖ ^ m * ‖w‖ := by
    intro m w
    calc ‖(b ^ m) w‖ ≤ ‖b ^ m‖ * ‖w‖ := (b ^ m).le_opNorm w
      _ ≤ ‖b‖ ^ m * ‖w‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          induction m with
          | zero =>
              rw [pow_zero, pow_zero, ContinuousLinearMap.one_def]
              exact ContinuousLinearMap.norm_id_le
          | succ k ih =>
              rw [pow_succ, pow_succ]
              exact le_trans (norm_mul_le _ _)
                (by nlinarith [norm_nonneg (b ^ k), norm_nonneg b, ih])
  have hTb : T = b + μ • 1 := by rw [hb]; abel
  have hcomm : Commute b (μ • (1 : V →L[ℂ] V)) := by
    rw [Algebra.algebraMap_eq_smul_one (R := ℂ) μ |>.symm]
    exact (Algebra.commute_algebraMap_right μ b)
  have hexp : (T ^ n) v
      = ∑ m ∈ range (n + 1), (μ ^ (n - m) * (n.choose m : ℂ)) • ((b ^ m) v) := by
    conv_lhs => rw [hTb, hcomm.add_pow]
    rw [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro m _
    have hkey : b ^ m * (μ • (1 : V →L[ℂ] V)) ^ (n - m) * (n.choose m : V →L[ℂ] V)
        = (μ ^ (n - m) * (n.choose m : ℂ)) • b ^ m := by
      simp only [smul_pow, one_pow, mul_smul_comm, mul_one]
      rw [show (n.choose m : V →L[ℂ] V) = (n.choose m : ℂ) • (1 : V →L[ℂ] V) by
            rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one],
          smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
    rw [hkey, ContinuousLinearMap.smul_apply]
  rw [hexp]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ range (n + 1),
      ‖(μ ^ (n - m) * (n.choose m : ℂ)) • ((b ^ m) v)‖
        ≤ (if m < d then ((n : ℝ) + 1) ^ d * ‖b‖ ^ m * ‖v‖ else 0) := by
    intro m _
    by_cases hmd : m < d
    · rw [if_pos hmd, norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
      calc ‖μ‖ ^ (n - m) * (n.choose m : ℝ) * ‖(b ^ m) v‖
          ≤ 1 ^ (n - m) * (n.choose m : ℝ) * (‖b‖ ^ m * ‖v‖) := by
            gcongr
            exact hnpow m v
        _ = (n.choose m : ℝ) * ‖b‖ ^ m * ‖v‖ := by rw [one_pow]; ring
        _ ≤ ((n : ℝ) + 1) ^ d * ‖b‖ ^ m * ‖v‖ := by
            gcongr
            calc (n.choose m : ℝ) ≤ ((n : ℝ)) ^ m := by exact_mod_cast Nat.choose_le_pow n m
              _ ≤ ((n : ℝ) + 1) ^ m := by apply pow_le_pow_left₀ (by positivity); linarith
              _ ≤ ((n : ℝ) + 1) ^ d := by apply pow_le_pow_right₀ (by linarith) (le_of_lt hmd)
    · rw [if_neg hmd]
      have hb0 : (b ^ m) v = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + d := ⟨m - d, by omega⟩
        rw [pow_add, ContinuousLinearMap.mul_apply, hv, map_zero]
      simp [hb0]
  calc ∑ m ∈ range (n + 1), ‖(μ ^ (n - m) * (n.choose m : ℂ)) • ((b ^ m) v)‖
      ≤ ∑ m ∈ range (n + 1),
          (if m < d then ((n : ℝ) + 1) ^ d * ‖b‖ ^ m * ‖v‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ m ∈ (range (n + 1)).filter (· < d), ((n : ℝ) + 1) ^ d * ‖b‖ ^ m * ‖v‖ := by
        rw [Finset.sum_filter]
    _ ≤ ∑ m ∈ range d, ((n : ℝ) + 1) ^ d * ‖b‖ ^ m * ‖v‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm; rw [Finset.mem_filter] at hm; exact Finset.mem_range.mpr hm.2
        · intro m _ _; positivity
    _ = ((n : ℝ) + 1) ^ d * (∑ m ∈ range d, ‖b‖ ^ m) * ‖v‖ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

section KernelPolyBound
open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

-- coercion/eigenvector bridge helper
private lemma pow_sub_smul_apply_bridge (T : V →L[ℂ] V) (μ : ℂ) :
    ∀ (d : ℕ) (v : V), (((T - μ • 1 : V →L[ℂ] V) ^ d) v)
       = (((T : Module.End ℂ V) - μ • 1) ^ d) v := by
  have step : ∀ (w : V), ((T - μ • 1 : V →L[ℂ] V)) w = ((T : Module.End ℂ V) - μ • 1) w := by
    intro w
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply]
  intro d
  induction d with
  | zero => intro v; simp
  | succ k ih =>
      intro v
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ih, step]

/-- **K-A.** If every eigenvalue of a continuous operator `T` on a finite-dimensional complex
normed space has modulus `≤ 1`, then `‖Tⁿ‖` grows at most polynomially. -/
theorem norm_pow_le_poly_of_eigenvalues_le_one
    (T : V →L[ℂ] V)
    (hev : ∀ μ : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ V) μ → ‖μ‖ ≤ 1) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  classical
  set f : Module.End ℂ V := (T : Module.End ℂ V) with hf
  have hInt : DirectSum.IsInternal (fun μ : ℂ => f.maxGenEigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  set b : ∀ μ : ℂ, Basis (Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) ℂ (f.maxGenEigenspace μ) :=
    fun μ => Module.finBasis ℂ (f.maxGenEigenspace μ) with hb
  set B := hInt.collectedBasis b with hB
  haveI : Fintype (Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) :=
    FiniteDimensional.fintypeBasisIndex B
  -- per-index data
  have hmem : ∀ (i : Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))), (B i) ∈ f.maxGenEigenspace i.1 := by
    intro i
    rw [hB, DirectSum.IsInternal.collectedBasis_coe]
    exact (b i.1 i.2).2
  -- eigenvalue modulus bound
  have hμle : ∀ (i : Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))), ‖(i.1 : ℂ)‖ ≤ 1 := by
    intro i
    apply hev
    have hne : f.maxGenEigenspace i.1 ≠ ⊥ := by
      intro hbot
      exact B.ne_zero i (by have := hmem i; rw [hbot, Submodule.mem_bot] at this; exact this)
    have hgen : f.HasGenEigenvalue i.1 (Module.finrank ℂ V) := by
      rw [Module.End.hasGenEigenvalue_iff, ← Module.End.maxGenEigenspace_eq_genEigenspace_finrank]
      exact hne
    exact Module.End.hasEigenvalue_of_hasGenEigenvalue hgen
  -- nilpotency index per index
  have hnil : ∀ (i : Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))), ∃ d, ((T - (i.1) • (1 : V →L[ℂ] V)) ^ d) (B i) = 0 := by
    intro i
    obtain ⟨d, hd⟩ := (Module.End.mem_maxGenEigenspace f i.1 (B i)).1 (hmem i)
    exact ⟨d, by rw [pow_sub_smul_apply_bridge T i.1 d (B i)]; exact hd⟩
  choose d hd using hnil
  set k := Finset.univ.sup d with hk
  refine ⟨∑ i, ‖(B.coord i).toContinuousLinearMap‖ *
      (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖, k, ?_, ?_⟩
  · positivity
  · intro n
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hsum : (T ^ n) v = ∑ i, (B.repr v i) • ((T ^ n) (B i)) := by
      conv_lhs => rw [← B.sum_repr v]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hbound : ∀ i ∈ (Finset.univ : Finset (Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ)))),
        ‖(B.repr v i) • ((T ^ n) (B i))‖
          ≤ (‖(B.coord i).toContinuousLinearMap‖ *
              (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖)
              * ((n : ℝ) + 1) ^ k * ‖v‖ := by
      intro i _
      rw [norm_smul]
      have h1 : ‖(T ^ n) (B i)‖ ≤ ((n : ℝ) + 1) ^ (d i) *
          (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖ :=
        norm_pow_apply_le_of_pow_sub_smul_eq_zero T (hμle i) (hd i) n
      have h2 : ‖B.repr v i‖ ≤ ‖(B.coord i).toContinuousLinearMap‖ * ‖v‖ := by
        have := (B.coord i).toContinuousLinearMap.le_opNorm v
        rwa [LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] at this
      calc ‖B.repr v i‖ * ‖(T ^ n) (B i)‖
          ≤ (‖(B.coord i).toContinuousLinearMap‖ * ‖v‖) *
              (((n : ℝ) + 1) ^ (d i) *
                (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ ≤ (‖(B.coord i).toContinuousLinearMap‖ *
              (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖) *
              ((n : ℝ) + 1) ^ k * ‖v‖ := by
            have hdik : ((n : ℝ) + 1) ^ (d i) ≤ ((n : ℝ) + 1) ^ k :=
              pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
                (Finset.le_sup (Finset.mem_univ i))
            have key : (‖(B.coord i).toContinuousLinearMap‖ * ‖v‖) *
                (((n : ℝ) + 1) ^ (d i) *
                  (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖)
                = (‖(B.coord i).toContinuousLinearMap‖ *
                    (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) *
                    ‖B i‖ * ‖v‖) * ((n : ℝ) + 1) ^ (d i) := by ring
            have key2 : (‖(B.coord i).toContinuousLinearMap‖ *
                (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖) *
                ((n : ℝ) + 1) ^ k * ‖v‖
                = (‖(B.coord i).toContinuousLinearMap‖ *
                    (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) *
                    ‖B i‖ * ‖v‖) * ((n : ℝ) + 1) ^ k := by ring
            rw [key, key2]
            exact mul_le_mul_of_nonneg_left hdik (by positivity)
    calc ∑ i, ‖(B.repr v i) • ((T ^ n) (B i))‖
        ≤ ∑ i, (‖(B.coord i).toContinuousLinearMap‖ *
            (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖)
            * ((n : ℝ) + 1) ^ k * ‖v‖ := Finset.sum_le_sum hbound
      _ = (∑ i, ‖(B.coord i).toContinuousLinearMap‖ *
            (∑ j ∈ Finset.range (d i), ‖(T - (i.1) • (1 : V →L[ℂ] V))‖ ^ j) * ‖B i‖)
            * ((n : ℝ) + 1) ^ k * ‖v‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

end KernelPolyBound


section Companion

open scoped Matrix
open Finset

variable {d : ℕ}

/-- Companion matrix of a linear recurrence with coefficients `coeffs`. -/
noncomputable def companion (coeffs : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun j i => if h : (j:ℕ) + 1 < d then (if i = ⟨(j:ℕ)+1, h⟩ then 1 else 0) else coeffs i

lemma companion_mulVec_apply (coeffs : Fin d → ℂ) (x : Fin d → ℂ) (j : Fin d) :
    (companion coeffs).mulVec x j
      = if h : (j:ℕ) + 1 < d then x ⟨(j:ℕ) + 1, h⟩ else ∑ i, coeffs i * x i := by
  unfold companion Matrix.mulVec
  by_cases h : (j:ℕ) + 1 < d
  · simp only [h, dif_pos]
    rw [dotProduct]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (⟨(j:ℕ)+1, h⟩ : Fin d) (fun i => x i)]
    simp
  · simp only [h, dif_neg, not_false_iff]
    rfl

/-- State vector `(f n, f (n+1), …, f (n+d-1))` of a sequence `f`. -/
noncomputable def state (f : ℕ → ℂ) (n : ℕ) : Fin d → ℂ := fun j => f (n + (j : ℕ))

lemma companion_mulVec_state (coeffs : Fin d → ℂ) (f : ℕ → ℂ) (n : ℕ)
    (hrec : f (n + d) = ∑ i, coeffs i * f (n + (i : ℕ))) :
    (companion coeffs).mulVec (state f n) = state f (n + 1) := by
  funext j
  rw [companion_mulVec_apply]
  by_cases h : (j : ℕ) + 1 < d
  · simp only [h, dif_pos]
    show f (n + ((j : ℕ) + 1)) = f (n + 1 + (j : ℕ))
    ring_nf
  · simp only [h, dif_neg, not_false_iff]
    have hj : (j : ℕ) + 1 = d := by omega
    show (∑ i, coeffs i * state f n i) = f (n + 1 + (j : ℕ))
    have : n + 1 + (j : ℕ) = n + d := by omega
    rw [this]
    rw [hrec]
    rfl

/-- Companion operator as a continuous linear map. -/
noncomputable def companionCLM (coeffs : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  (Matrix.mulVecLin (companion coeffs)).toContinuousLinearMap

lemma companionCLM_apply (coeffs : Fin d → ℂ) (x : Fin d → ℂ) :
    companionCLM coeffs x = (companion coeffs).mulVec x := by
  rw [companionCLM, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]

lemma companionCLM_pow_state (coeffs : Fin d → ℂ) (f : ℕ → ℂ) (N : ℕ)
    (hrec : ∀ n, N ≤ n → f (n + d) = ∑ i, coeffs i * f (n + (i : ℕ))) :
    ∀ m, ((companionCLM coeffs) ^ m) (state f N) = state f (N + m) := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, companionCLM_apply,
        companion_mulVec_state coeffs f (N + k) (hrec (N + k) (by omega))]
      rfl

end Companion


section Orbit

open Finset Module
open scoped Classical

theorem orbit_poly_of_subExponential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (C : E →L[ℂ] E) (x₀ : E)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ‖(C ^ m) x₀‖ ≤ (1 + ε) ^ m) :
    ∃ (K : ℝ) (p : ℕ), 0 ≤ K ∧ ∀ m : ℕ, ‖(C ^ m) x₀‖ ≤ K * ((m : ℝ) + 1) ^ p := by
  classical
  set g : ℕ → E := fun m => (C ^ m) x₀
  let W : Submodule ℂ E := Submodule.span ℂ (Set.range g)
  have hmaps : Set.MapsTo (C : E →ₗ[ℂ] E) W W := by
    intro x hx
    change x ∈ Submodule.span ℂ (Set.range g) at hx
    change C x ∈ Submodule.span ℂ (Set.range g)
    refine Submodule.span_induction
      (s := Set.range g)
      (p := fun y _ => C y ∈ Submodule.span ℂ (Set.range g))
      ?mem ?zero ?add ?smul hx
    · intro y hy
      rcases hy with ⟨m, rfl⟩
      exact Submodule.subset_span ⟨m + 1, by
        simp [g, pow_succ', ContinuousLinearMap.mul_apply, add_comm, add_left_comm, add_assoc]
      ⟩
    · simp
    · intro u v hu hv hCu hCv
      simpa [map_add] using (Submodule.add_mem _ hCu hCv)
    · intro a u hu hCu
      simpa [map_smul] using (Submodule.smul_mem _ a hCu)
  have x0mem : x₀ ∈ W := by
    exact Submodule.subset_span ⟨0, by simp [g]⟩
  let CW : W →L[ℂ] W := (LinearMap.restrict (C : E →ₗ[ℂ] E) hmaps).toContinuousLinearMap
  let xW : W := ⟨x₀, x0mem⟩

  have hpowW : ∀ m : ℕ, (((CW ^ m) xW : W) : E) = (C ^ m) x₀ := by
    intro m
    induction m with
    | zero =>
        simp [CW, xW]
    | succ n ih =>
        calc
          (((CW ^ (n + 1)) xW : W) : E)
              = ((CW (((CW ^ n) xW)) : W) : E) := by simp [pow_succ']
          _ = C ((((CW ^ n) xW : W) : E)) := by
                simp [CW, LinearMap.coe_toContinuousLinearMap', LinearMap.restrict_apply]
          _ = C ((C ^ n) x₀) := by simpa [ih]
          _ = (C ^ (n + 1)) x₀ := by
                simp [pow_succ', ContinuousLinearMap.mul_apply]

  have hpowW_gen : ∀ m : ℕ, ∀ w : W, (((CW ^ m) w : W) : E) = (C ^ m) (w : E) := by
    intro m w
    induction m with
    | zero => simp
    | succ n ih =>
        calc
          (((CW ^ (n + 1)) w : W) : E)
              = ((CW (((CW ^ n) w)) : W) : E) := by simp [pow_succ']
          _ = C ((((CW ^ n) w : W) : E)) := by
                simp [CW, LinearMap.coe_toContinuousLinearMap', LinearMap.restrict_apply]
          _ = C ((C ^ n) (w : E)) := by simpa [ih]
          _ = (C ^ (n + 1)) (w : E) := by
                simp [pow_succ', ContinuousLinearMap.mul_apply]

  have hev : ∀ μ : ℂ, Module.End.HasEigenvalue (CW : Module.End ℂ W) μ → ‖μ‖ ≤ 1 := by
    intro μ hμ
    obtain ⟨w, hw⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    have hwne : w ≠ 0 := hw.2
    have hweqW : (CW : Module.End ℂ W) w = μ • w := hw.apply_eq_smul
    have hweqE : C (w : E) = μ • (w : E) := by
      have hCWw : (CW w : W) = μ • w := hweqW
      have htmp : (((CW w : W) : E)) = ((μ • w : W) : E) := by rw [hCWw]
      rw [Submodule.coe_smul] at htmp
      rw [← htmp]
      simp [CW, LinearMap.coe_toContinuousLinearMap', LinearMap.restrict_apply]
    have hwneE : (w : E) ≠ 0 := by
      intro hw0
      apply hwne
      ext
      simpa using hw0
    have hwnorm_pos : 0 < ‖(w : E)‖ := norm_pos_iff.mpr hwneE

    have hpow_eig : ∀ m : ℕ, (C ^ m) (w : E) = μ ^ m • (w : E) := by
      intro m
      induction m with
      | zero => simp
      | succ n ih =>
          calc
            (C ^ (n + 1)) (w : E) = C ((C ^ n) (w : E)) := by
                simp [pow_succ', ContinuousLinearMap.mul_apply]
            _ = C (μ ^ n • (w : E)) := by simpa [ih]
            _ = μ ^ n • C (w : E) := by simp [map_smul]
            _ = μ ^ n • (μ • (w : E)) := by simpa [hweqE]
            _ = μ ^ (n + 1) • (w : E) := by
                rw [pow_succ, mul_smul, smul_comm]

    have hw_in_span : (w : E) ∈ Submodule.span ℂ (Set.range g) := by
      exact w.property
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw_in_span

    have hCm_as_sum : ∀ m : ℕ, (C ^ m) (w : E) = l.sum (fun k a => a • g (m + k)) := by
      intro m
      calc
        (C ^ m) (w : E) = (C ^ m) (l.sum fun k a => a • g k) := by simpa [hl]
        _ = l.sum (fun k a => a • (C ^ m) (g k)) := by
              simp [Finsupp.sum, map_sum, map_smul]
        _ = l.sum (fun k a => a • g (m + k)) := by
              refine Finsupp.sum_congr ?_
              intro k hk
              simp [g, pow_add, ContinuousLinearMap.mul_apply, add_comm, add_left_comm, add_assoc]

    have hnorm_sum : ∀ m : ℕ,
        ‖(C ^ m) (w : E)‖ ≤ ∑ k ∈ l.support, ‖l k‖ * ‖g (m + k)‖ := by
      intro m
      rw [hCm_as_sum m, Finsupp.sum]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum (fun k hk => by simp [norm_smul, mul_comm, mul_left_comm, mul_assoc])

    have hμle_eps : ∀ ε : ℝ, 0 < ε → ‖μ‖ ≤ 1 + ε := by
      intro ε hε
      have hsub' : ∀ᶠ n in atTop, ‖g n‖ ≤ (1 + ε) ^ n := by simpa [g] using hsub ε hε
      have hk_ev : ∀ k : ℕ, ∀ᶠ m in atTop, ‖g (m + k)‖ ≤ (1 + ε) ^ (m + k) := by
        intro k
        exact (tendsto_add_atTop_nat k).eventually hsub'
      have hall : ∀ᶠ m in atTop, ∀ k ∈ l.support, ‖g (m + k)‖ ≤ (1 + ε) ^ (m + k) := by
        rw [Filter.eventually_all_finset]
        intro k hk
        exact hk_ev k
      let Kε : ℝ := ∑ k ∈ l.support, ‖l k‖ * (1 + ε) ^ k
      have hbound_eventually : ∀ᶠ m in atTop,
          ‖μ‖ ^ m * ‖(w : E)‖ ≤ Kε * (1 + ε) ^ m := by
        filter_upwards [hall] with m hm
        have h1 : ‖(C ^ m) (w : E)‖ ≤ Kε * (1 + ε) ^ m := by
          calc
            ‖(C ^ m) (w : E)‖ ≤ ∑ k ∈ l.support, ‖l k‖ * ‖g (m + k)‖ := hnorm_sum m
            _ ≤ ∑ k ∈ l.support, ‖l k‖ * ((1 + ε) ^ (m + k)) := by
                  refine Finset.sum_le_sum ?_
                  intro k hk
                  exact mul_le_mul_of_nonneg_left (hm k hk) (norm_nonneg _)
            _ = ∑ k ∈ l.support, (‖l k‖ * (1 + ε) ^ k) * (1 + ε) ^ m := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  rw [pow_add]; ring
            _ = Kε * (1 + ε) ^ m := by
                  simp [Kε, Finset.sum_mul]
        have h2 : ‖μ‖ ^ m * ‖(w : E)‖ = ‖(C ^ m) (w : E)‖ := by
          calc
            ‖μ‖ ^ m * ‖(w : E)‖ = ‖μ ^ m‖ * ‖(w : E)‖ := by simp
            _ = ‖μ ^ m • (w : E)‖ := by simp [norm_smul]
            _ = ‖(C ^ m) (w : E)‖ := by simpa [hpow_eig m]
        simpa [h2] using h1

      by_contra hlt
      have hgt : 1 + ε < ‖μ‖ := lt_of_not_ge hlt
      have hpos : (0:ℝ) < 1 + ε := by linarith
      set r : ℝ := ‖μ‖ / (1 + ε) with hr_def
      have hratio : 1 < r := (one_lt_div hpos).2 hgt
      have hKnonneg : 0 ≤ Kε := by dsimp [Kε]; positivity
      have hEvent : ∀ᶠ m in atTop, r ^ m * ‖(w : E)‖ ≤ Kε := by
        filter_upwards [hbound_eventually] with m hm
        have hpospow : (0:ℝ) < (1 + ε) ^ m := by positivity
        rw [hr_def, div_pow, div_mul_eq_mul_div, div_le_iff₀ hpospow]
        linarith [hm]
      have htend : Filter.Tendsto (fun m : ℕ => r ^ m * ‖(w : E)‖) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt hratio).atTop_mul_const hwnorm_pos
      have hgtev := htend.eventually_gt_atTop Kε
      obtain ⟨m, hm1, hm2⟩ := (hEvent.and hgtev).exists
      exact absurd hm1 (not_le.mpr hm2)

    have hμle1 : ‖μ‖ ≤ 1 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have := hμle_eps ε hε
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact hμle1

  obtain ⟨C', k', hC'0, hC'⟩ := norm_pow_le_poly_of_eigenvalues_le_one CW hev
  refine ⟨C' * ‖x₀‖, k', by positivity, ?_⟩
  intro m
  calc
    ‖(C ^ m) x₀‖ = ‖(((CW ^ m) xW : W) : E)‖ := by simpa [hpowW m]
    _ = ‖(CW ^ m) xW‖ := rfl
    _ ≤ ‖CW ^ m‖ * ‖xW‖ := (CW ^ m).le_opNorm xW
    _ ≤ (C' * ((m : ℝ) + 1) ^ k') * ‖xW‖ := by
          gcongr
          exact hC' m
    _ = (C' * ‖x₀‖) * ((m : ℝ) + 1) ^ k' := by
          have hxw : ‖xW‖ = ‖x₀‖ := rfl
          rw [hxw]; ring


end Orbit


section RecurrencePolyBound

open PresentedGroup
open scoped Classical

/-- A sub-exponentially growing integer sequence satisfying a linear recurrence is
polynomially bounded. -/
theorem polyBound_of_recurrence_subExp (f : ℕ → ℤ)
    (hrec : SatisfiesLinearRecurrence f)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (|f n| : ℝ) ≤ (1 + ε) ^ n) :
    ∃ (K : ℝ) (p : ℕ), 0 ≤ K ∧ ∀ n, (|f n| : ℝ) ≤ K * ((n : ℝ) + 1) ^ p := by
  classical
  obtain ⟨d, hd, coeffs, hrecev⟩ := hrec
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrecev
  set fc : ℕ → ℂ := fun n => (f n : ℂ) with hfc
  set cc : Fin d → ℂ := fun i => (coeffs i : ℂ) with hcc
  -- cast the recurrence to ℂ
  have hrecC : ∀ n, N ≤ n → fc (n + d) = ∑ i, cc i * fc (n + (i : ℕ)) := by
    intro n hn
    have := hN n hn
    simp only [hfc, hcc]
    push_cast [this]
    ring
  -- companion operator and orbit
  set C : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) := companionCLM cc with hC
  set x₀ : Fin d → ℂ := state fc N with hx0
  have hpow : ∀ m, (C ^ m) x₀ = state fc (N + m) :=
    companionCLM_pow_state cc fc N hrecC
  -- helper: norm of a state vector equals sup of |f|
  have hstate_coord : ∀ (n : ℕ) (j : Fin d), ‖(state fc n) j‖ = (|f (n + (j:ℕ))| : ℝ) := by
    intro n j
    simp [state, hfc, Complex.norm_intCast]
  -- orbit sub-exponential bound
  have horbit : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ‖(C ^ m) x₀‖ ≤ (1 + ε) ^ m := by
    intro ε hε
    set δ : ℝ := ε / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hδlt : 1 + δ < 1 + ε := by simp [hδdef]; linarith
    have hbase : (1:ℝ) ≤ 1 + δ := by linarith
    set A : ℝ := (1 + δ) ^ (N + d) with hA
    set r : ℝ := (1 + ε) / (1 + δ) with hr
    have hrpos : 0 < 1 + δ := by linarith
    have hr1 : 1 < r := by
      rw [hr, lt_div_iff₀ hrpos]; linarith
    have hgeo : ∀ᶠ m in atTop, A ≤ r ^ m :=
      (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop A
    -- for each coordinate j, eventually |f(N+m+j)| ≤ (1+δ)^(N+m+j)
    have hcoordev : ∀ᶠ m in atTop, ∀ j : Fin d,
        (|f (N + m + (j:ℕ))| : ℝ) ≤ (1 + δ) ^ (N + m + (j:ℕ)) := by
      rw [eventually_all]
      intro j
      have hsubδ := hsub δ hδ
      have : Tendsto (fun m : ℕ => N + m + (j:ℕ)) atTop atTop := by
        rw [tendsto_atTop_atTop]
        exact fun b => ⟨b, fun m hm => by omega⟩
      exact this.eventually hsubδ
    filter_upwards [hgeo, hcoordev] with m hgeom hcoordm
    -- bound the sup norm of state fc (N+m)
    have hstate_le : ‖(state fc (N + m) : Fin d → ℂ)‖ ≤ A * (1 + δ) ^ m := by
      apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
      intro j
      rw [hstate_coord]
      have h1 : (|f (N + m + (j:ℕ))| : ℝ) ≤ (1 + δ) ^ (N + m + (j:ℕ)) := hcoordm j
      have h2 : (1 + δ) ^ (N + m + (j:ℕ)) ≤ (1 + δ) ^ (N + d + m) := by
        apply pow_le_pow_right₀ hbase
        have : (j:ℕ) < d := j.2
        omega
      calc (|f (N + m + (j:ℕ))| : ℝ) ≤ (1 + δ) ^ (N + m + (j:ℕ)) := h1
        _ ≤ (1 + δ) ^ (N + d + m) := h2
        _ = A * (1 + δ) ^ m := by rw [hA, ← pow_add]
    -- finish: A*(1+δ)^m ≤ (1+ε)^m
    have hfin : A * (1 + δ) ^ m ≤ (1 + ε) ^ m := by
      have : A * (1 + δ) ^ m ≤ r ^ m * (1 + δ) ^ m := by
        apply mul_le_mul_of_nonneg_right hgeom (by positivity)
      calc A * (1 + δ) ^ m ≤ r ^ m * (1 + δ) ^ m := this
        _ = (1 + ε) ^ m := by
              rw [hr, div_pow, div_mul_cancel₀]
              positivity
    calc ‖(C ^ m) x₀‖ = ‖state fc (N + m)‖ := by rw [hpow]
      _ ≤ A * (1 + δ) ^ m := hstate_le
      _ ≤ (1 + ε) ^ m := hfin
  -- apply the orbit poly lemma
  obtain ⟨K, p, hK0, hKbd⟩ := orbit_poly_of_subExponential C x₀ horbit
  set S : ℝ := ∑ n ∈ Finset.range N, (|f n| : ℝ) with hSdef
  have hSnn : 0 ≤ S := by positivity
  refine ⟨K + S, p, by positivity, ?_⟩
  intro n
  have hpow1 : (1:ℝ) ≤ ((n:ℝ) + 1) ^ p :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  by_cases hn : N ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    have hcoord0 : (|f (N + m)| : ℝ) ≤ ‖(C ^ m) x₀‖ := by
      rw [hpow]
      have hle := norm_le_pi_norm (state fc (N + m) : Fin d → ℂ) ⟨0, hd⟩
      rw [hstate_coord] at hle
      simpa using hle
    have hb : (|f (N + m)| : ℝ) ≤ K * ((m : ℝ) + 1) ^ p := le_trans hcoord0 (hKbd m)
    have hmono : K * ((m : ℝ) + 1) ^ p ≤ (K + S) * (((N + m : ℕ) : ℝ) + 1) ^ p := by
      gcongr
      · linarith
      · push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
    linarith [hb, hmono]
  · push_neg at hn
    have hmem : n ∈ Finset.range N := Finset.mem_range.2 hn
    have hle : (|f n| : ℝ) ≤ S :=
      Finset.single_le_sum (f := fun k => (|f k| : ℝ)) (fun k _ => by positivity) hmem
    nlinarith [hle, hpow1, hK0, hSnn]


end RecurrencePolyBound

section Pinching

open PresentedGroup

/-- A sequence pinched between two constant multiples of `modelGrowthReal` cannot satisfy a
linear recurrence. -/
theorem not_satisfiesLinearRecurrence_of_pinched (f : ℕ → ℤ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hlb : ∀ᶠ n in atTop, c₁ * modelGrowthReal n ≤ (|f n| : ℝ))
    (hub : ∀ᶠ n in atTop, (|f n| : ℝ) ≤ c₂ * modelGrowthReal n) :
    ¬ SatisfiesLinearRecurrence f := by
  intro hrec
  set Cu : ℝ := max c₂ 1 with hCu
  have hCu1 : (1:ℝ) ≤ Cu := le_max_right _ _
  have hCupos : 0 < Cu := by linarith
  have hc2Cu : c₂ ≤ Cu := le_max_left _ _
  -- sub-exponential bound on |f|
  have hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (|f n| : ℝ) ≤ (1 + ε) ^ n := by
    intro ε hε
    set δ : ℝ := ε / 2 with hδ
    have hδpos : 0 < δ := by positivity
    have hδlt : 1 + δ < 1 + ε := by simp [hδ]; linarith
    have hrpos : 0 < 1 + δ := by linarith
    set r : ℝ := (1 + ε) / (1 + δ) with hr
    have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hrpos]; linarith
    have hgeo : ∀ᶠ n in atTop, Cu ≤ r ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop Cu
    have hmodel := modelGrowthReal_lt_geometric hδpos
    filter_upwards [hub, hmodel, hgeo] with n hubn hmodeln hgeon
    have hstep1 : (|f n| : ℝ) ≤ Cu * modelGrowthReal n :=
      le_trans hubn (by
        apply mul_le_mul_of_nonneg_right hc2Cu (modelGrowthReal_pos n).le)
    have hstep2 : Cu * modelGrowthReal n ≤ Cu * (1 + δ) ^ n :=
      mul_le_mul_of_nonneg_left hmodeln.le hCupos.le
    have hstep3 : Cu * (1 + δ) ^ n ≤ (1 + ε) ^ n := by
      have : Cu * (1 + δ) ^ n ≤ r ^ n * (1 + δ) ^ n :=
        mul_le_mul_of_nonneg_right hgeon (by positivity)
      calc Cu * (1 + δ) ^ n ≤ r ^ n * (1 + δ) ^ n := this
        _ = (1 + ε) ^ n := by rw [hr, div_pow, div_mul_cancel₀]; positivity
    linarith [hstep1, hstep2, hstep3]
  -- polynomial bound from recurrence + sub-exponential
  obtain ⟨K, p, hK0, hKbd⟩ := polyBound_of_recurrence_subExp f hrec hsub
  -- contradiction with the lower bound
  have hpoly := poly_lt_modelGrowthReal (K / c₁) p
  obtain ⟨n, hlbn, hpolyn⟩ := (hlb.and hpoly).exists
  have hKn : (|f n| : ℝ) ≤ K * ((n : ℝ) + 1) ^ p := hKbd n
  -- (K/c₁)(n+1)^p < modelGrowthReal n ⟹ K(n+1)^p < c₁ modelGrowthReal n
  have hmul : K * ((n : ℝ) + 1) ^ p < c₁ * modelGrowthReal n := by
    have h := mul_lt_mul_of_pos_left hpolyn hc₁
    have hrw : c₁ * (K / c₁ * ((n : ℝ) + 1) ^ p) = K * ((n : ℝ) + 1) ^ p := by
      field_simp
    rw [hrw] at h
    exact h
  linarith [hlbn, hKn, hmul]

/-- **Two-model pinching.** A generalization of `not_satisfiesLinearRecurrence_of_pinched` that
pinches `f` between constant multiples of two *possibly different* comparison functions: an upper
model `U` that is sub-exponential, and a lower model `L` that is super-polynomial. This is the
form actually justified by Bodart's Theorem 4, whose upper bound uses `exp(n^{3/5} log n)` but
whose lower bound only controls the exponent up to a smaller constant, i.e. uses
`exp(κ · n^{3/5} log n)` with `κ < 1`. The irrationality conclusion needs only that the upper
model is sub-exponential (forcing polynomial growth via the recurrence) and the lower model is
super-polynomial (contradicting that polynomial growth); it does **not** require the two models
to agree. -/
theorem not_satisfiesLinearRecurrence_of_pinched_two
    (f : ℕ → ℤ) (U L : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hUpos : ∀ n, 0 < U n)
    (hUsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, U n < (1 + δ) ^ n)
    (hLsuper : ∀ (A : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, A * ((n : ℝ) + 1) ^ k < L n)
    (hlb : ∀ᶠ n in atTop, c₁ * L n ≤ (|f n| : ℝ))
    (hub : ∀ᶠ n in atTop, (|f n| : ℝ) ≤ c₂ * U n) :
    ¬ SatisfiesLinearRecurrence f := by
  intro hrec
  set Cu : ℝ := max c₂ 1 with hCu
  have hCu1 : (1:ℝ) ≤ Cu := le_max_right _ _
  have hCupos : 0 < Cu := by linarith
  have hc2Cu : c₂ ≤ Cu := le_max_left _ _
  -- sub-exponential bound on |f| from the upper model
  have hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (|f n| : ℝ) ≤ (1 + ε) ^ n := by
    intro ε hε
    set δ : ℝ := ε / 2 with hδ
    have hδpos : 0 < δ := by positivity
    have hrpos : 0 < 1 + δ := by linarith
    set r : ℝ := (1 + ε) / (1 + δ) with hr
    have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hrpos]; linarith
    have hgeo : ∀ᶠ n in atTop, Cu ≤ r ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop Cu
    have hmodel := hUsub δ hδpos
    filter_upwards [hub, hmodel, hgeo] with n hubn hmodeln hgeon
    have hstep1 : (|f n| : ℝ) ≤ Cu * U n :=
      le_trans hubn (by
        apply mul_le_mul_of_nonneg_right hc2Cu (hUpos n).le)
    have hstep2 : Cu * U n ≤ Cu * (1 + δ) ^ n :=
      mul_le_mul_of_nonneg_left hmodeln.le hCupos.le
    have hstep3 : Cu * (1 + δ) ^ n ≤ (1 + ε) ^ n := by
      have hle : Cu * (1 + δ) ^ n ≤ r ^ n * (1 + δ) ^ n :=
        mul_le_mul_of_nonneg_right hgeon (by positivity)
      calc Cu * (1 + δ) ^ n ≤ r ^ n * (1 + δ) ^ n := hle
        _ = (1 + ε) ^ n := by rw [hr, div_pow, div_mul_cancel₀]; positivity
    linarith [hstep1, hstep2, hstep3]
  -- polynomial bound from recurrence + sub-exponential
  obtain ⟨K, p, hK0, hKbd⟩ := polyBound_of_recurrence_subExp f hrec hsub
  -- contradiction with the super-polynomial lower model
  have hpoly := hLsuper (K / c₁) p
  obtain ⟨n, hlbn, hpolyn⟩ := (hlb.and hpoly).exists
  have hKn : (|f n| : ℝ) ≤ K * ((n : ℝ) + 1) ^ p := hKbd n
  have hmul : K * ((n : ℝ) + 1) ^ p < c₁ * L n := by
    have h := mul_lt_mul_of_pos_left hpolyn hc₁
    have hrw : c₁ * (K / c₁ * ((n : ℝ) + 1) ^ p) = K * ((n : ℝ) + 1) ^ p := by
      field_simp
    rw [hrw] at h
    exact h
  linarith [hlbn, hKn, hmul]

end Pinching

/-!
## Coarse growth equivalence (Bodart's `≍`)

Bodart states Theorem 4 as `γ(n) ≍ exp(n^{3/5} log n)`, where `≍` is the standard *growth
equivalence* of geometric group theory: two functions are equivalent when each dominates the
other up to a multiplicative constant on values **and a linear rescaling of the argument**, for
large `n`. This rescaling freedom is essential — it is exactly what reconciles the two different
exponent constants in Bodart's one-sided bounds (`exp(n^{3/5}log n)` above,
`exp(κ·n^{3/5}log n)` with `κ<1` below).
-/

namespace CoarseGrowth

/-- `f` is **coarsely dominated** by `g` (`f ⪯ g`): there are a multiplicative constant `C > 0`
and a linear argument-rescaling factor `k ≥ 1` such that `f n ≤ C · g (k · n)` for all large `n`.
This is the one-sided half of Bodart's growth equivalence `≍`. -/
def CoarseDom (f g : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 < C ∧ 0 < k ∧ ∀ᶠ n in atTop, f n ≤ C * g (k * n)

/-- `f` and `g` are **coarsely equivalent** (`f ≍ g`): each coarsely dominates the other. This is
Bodart's growth-equivalence relation used to state Theorem 4. -/
def CoarseEquiv (f g : ℕ → ℝ) : Prop :=
  CoarseDom f g ∧ CoarseDom g f

lemma CoarseEquiv.symm {f g : ℕ → ℝ} (h : CoarseEquiv f g) : CoarseEquiv g f :=
  ⟨h.2, h.1⟩

end CoarseGrowth

end LinearRecurrenceGrowth
