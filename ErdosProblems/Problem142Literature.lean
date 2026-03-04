import ErdosProblems.Problem142

open Filter

namespace Erdos142

/-- Structured reduction target for `k = 3`:
`r_3(N)` is sandwiched (up to constants) by one common profile `g`. -/
def k3_matched_profile (g : ℕ → ℝ) : Prop :=
  (fun N => (r 3 N : ℝ)) =O[atTop] g ∧ g =O[atTop] (fun N => (r 3 N : ℝ))

/-- The reduction bridge: a matched two-sided profile implies the DeepMind-style `k = 3` goal. -/
theorem erdos_142_three_of_matched_profile {g : ℕ → ℝ} (hg : k3_matched_profile g) :
    erdos_142 3 := by
  exact ⟨g, Asymptotics.IsBigO.antisymm hg.1 hg.2⟩

/-- Temporary branch debt for `k = 3`, now reduced to a matched-profile target. -/
axiom erdos_problem_142_k3_matched_profile_axiom : ∃ g : ℕ → ℝ, k3_matched_profile g

/-- Derived `k = 3` branch from the matched-profile temporary debt axiom. -/
theorem erdos_problem_142_k3_case : erdos_142 3 := by
  rcases erdos_problem_142_k3_matched_profile_axiom with ⟨g, hg⟩
  exact erdos_142_three_of_matched_profile hg

/-- Temporary branch debt for the `k = 4` case in the #142 roadmap. -/
axiom erdos_problem_142_k4_case_axiom : erdos_142 4

/-- Temporary branch debt for the `k ≥ 5` case in the #142 roadmap. -/
axiom erdos_problem_142_kge5_case_axiom : ∀ ⦃k : ℕ⦄, 5 ≤ k → erdos_142 k

/-- Structured theorem outline for the full #142 target.
The body follows the active plan split: `k = 3`, `k = 4`, and `k ≥ 5`. -/
theorem erdos_problem_142_solution_axiom : ErdosProblems.erdos_problem_142 := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk_cases with rfl | rfl | hk5
  · exact (hasAsymptoticFormula_iff_erdos142 3).2 erdos_problem_142_k3_case
  · exact (hasAsymptoticFormula_iff_erdos142 4).2 erdos_problem_142_k4_case_axiom
  · exact (hasAsymptoticFormula_iff_erdos142 k).2 (erdos_problem_142_kge5_case_axiom hk5)

/-- Structured container for deep external benchmark inputs.
Using a typeclass keeps all such dependencies explicit in theorem statements. -/
class LiteratureAssumptions : Prop where
  k3_upper_kelley_meka : bound_targets.k3_upper_kelley_meka
  k4_upper_green_tao : bound_targets.k4_upper_green_tao
  kge5_upper_leng_sah_sawhney : bound_targets.kge5_upper_leng_sah_sawhney

theorem literatureAssumptions_provide_all_targets [h : LiteratureAssumptions] :
    bound_targets.k3_upper_kelley_meka ∧
      bound_targets.k4_upper_green_tao ∧
      bound_targets.kge5_upper_leng_sah_sawhney := by
  exact ⟨h.k3_upper_kelley_meka, h.k4_upper_green_tao, h.kge5_upper_leng_sah_sawhney⟩

/-- Strengthened container that also stores explicit rate-profile targets. -/
class LiteratureRateAssumptions : Prop extends LiteratureAssumptions where
  k3_behrend_lower_profile : bound_targets.k3_behrend_lower_profile
  k3_superpolylog_upper_profile : bound_targets.k3_superpolylog_upper_profile
  k4_polylog_upper_profile : bound_targets.k4_polylog_upper_profile
  kge5_iteratedlog_upper_profile : bound_targets.kge5_iteratedlog_upper_profile
  k3_smallo_n_div_log : erdos_142.variants.lower 3 (by decide)

/-- Under benchmark assumptions, all `k ≥ 3` have a nontrivial `upper`-variant statement. -/
theorem upper_variant_of_literature_for_all_k_ge_three [h : LiteratureAssumptions] :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk_cases with rfl | rfl | hk5
  · exact h.k3_upper_kelley_meka
  · exact h.k4_upper_green_tao
  · exact h.kge5_upper_leng_sah_sawhney hk5

/-- The benchmark rate assumptions imply a two-sided `k = 3` sandwich profile. -/
theorem k3_two_sided_sandwich_of_literature_rates [h : LiteratureRateAssumptions] :
    bound_targets.k3_two_sided_sandwich_profile := by
  exact ⟨h.k3_behrend_lower_profile, h.k3_superpolylog_upper_profile⟩

/-- Elementary helper: `N / log N = O(N)` along `atTop` (for `ℕ`-indexed reals). -/
theorem nat_div_log_isBigO_natCast :
    (fun N : ℕ => (N : ℝ) / (N : ℝ).log) =O[atTop] (fun N : ℕ => (N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  have hNreal : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hlog_gt_one : 1 < (N : ℝ).log := by
    exact (Real.lt_log_iff_exp_lt hNpos).2 (lt_of_lt_of_le Real.exp_one_lt_three hNreal)
  have hlog_pos : 0 < (N : ℝ).log := lt_trans zero_lt_one hlog_gt_one
  have hle : (N : ℝ) / (N : ℝ).log ≤ (N : ℝ) := by
    calc
      (N : ℝ) / (N : ℝ).log ≤ (N : ℝ) / 1 := by
        gcongr
      _ = (N : ℝ) := by ring
  have hnonneg : 0 ≤ (N : ℝ) / (N : ℝ).log := div_nonneg (by positivity) hlog_pos.le
  have hnorm : ‖(N : ℝ) / (N : ℝ).log‖ ≤ ‖(N : ℝ)‖ := by
    calc
      ‖(N : ℝ) / (N : ℝ).log‖ = (N : ℝ) / (N : ℝ).log := by
        exact Real.norm_of_nonneg hnonneg
      _ ≤ (N : ℝ) := hle
      _ = ‖(N : ℝ)‖ := by
        symm
        exact Real.norm_of_nonneg (show 0 ≤ (N : ℝ) by positivity)
  simpa using hnorm

/-- Conditional asymptotic corollary:
the assumed `k = 3` `o(N/log N)` bound implies `o(N)`. -/
theorem k3_sublinear_of_literature_rates [h : LiteratureRateAssumptions] :
    bound_targets.k3_sublinear := by
  exact h.k3_smallo_n_div_log.trans_isBigO nat_div_log_isBigO_natCast

/-- Feasible lower-variant bridge for `k = 2`.
If `‖N / log N‖ → ∞`, then the exact `k = 2` model implies the lower variant. -/
theorem lower_variant_two_of_growth
    (h_growth : Tendsto (fun N : ℕ => ‖(N : ℝ) / (N : ℝ).log‖) atTop atTop) :
    erdos_142.variants.lower 2 (by decide) := by
  have hEq : (fun N => (r 2 N : ℝ)) =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine (eventually_ge_atTop (1 : ℕ)).mono ?_
    intro N hN
    have hpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    simp [ErdosProblems.rk_two_eq_one_of_pos hpos]
  have hconst :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / (N : ℝ).log) := by
    exact
      (Asymptotics.isLittleO_const_left
        (l := atTop)
        (c := (1 : ℝ))
        (g'' := fun N : ℕ => (N : ℝ) / (N : ℝ).log)).2 (Or.inr h_growth)
  exact hEq.trans_isLittleO hconst

end Erdos142
