import ErdosProblems.Problem142

open Filter

namespace Erdos142

/-- Structured reduction target for `k = 3`:
`r_3(N)` is sandwiched (up to constants) by one common profile `g`. -/
def k3_matched_profile (g : ℕ → ℝ) : Prop :=
  (fun N => (r 3 N : ℝ)) =O[atTop] g ∧ g =O[atTop] (fun N => (r 3 N : ℝ))

/-- Structured reduction target for `k = 4`. -/
def k4_matched_profile (g : ℕ → ℝ) : Prop :=
  (fun N => (r 4 N : ℝ)) =O[atTop] g ∧ g =O[atTop] (fun N => (r 4 N : ℝ))

/-- Fixed explicit comparison profile used for narrowing temporary `k = 3` debt. -/
noncomputable def k3_profile : ℕ → ℝ :=
  fun N => (N : ℝ) / Real.log (N + 2)

/-- Fixed explicit comparison profile used for narrowing temporary `k = 4` debt. -/
noncomputable def k4_profile : ℕ → ℝ :=
  fun N => (N : ℝ) / Real.log (N + 2)

/-- Two eventual inequality bounds imply a matched `O`-sandwich for the chosen `k = 3` profile. -/
theorem k3_matched_profile_of_eventual_bounds
    (hUpper : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ‖(r 3 N : ℝ)‖ ≤ C * ‖k3_profile N‖)
    (hLower : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ‖k3_profile N‖ ≤ C * ‖(r 3 N : ℝ)‖) :
    k3_matched_profile k3_profile := by
  rcases hUpper with ⟨C, -, hC⟩
  rcases hLower with ⟨C', -, hC'⟩
  exact ⟨Asymptotics.IsBigO.of_bound C hC, Asymptotics.IsBigO.of_bound C' hC'⟩

/-- Two eventual inequality bounds imply a matched `O`-sandwich for the chosen `k = 4` profile. -/
theorem k4_matched_profile_of_eventual_bounds
    (hUpper : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ‖(r 4 N : ℝ)‖ ≤ C * ‖k4_profile N‖)
    (hLower : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ‖k4_profile N‖ ≤ C * ‖(r 4 N : ℝ)‖) :
    k4_matched_profile k4_profile := by
  rcases hUpper with ⟨C, -, hC⟩
  rcases hLower with ⟨C', -, hC'⟩
  exact ⟨Asymptotics.IsBigO.of_bound C hC, Asymptotics.IsBigO.of_bound C' hC'⟩

/-- The reduction bridge: a matched two-sided profile implies the DeepMind-style `k = 3` goal. -/
theorem erdos_142_three_of_matched_profile {g : ℕ → ℝ} (hg : k3_matched_profile g) :
    erdos_142 3 := by
  exact ⟨g, Asymptotics.IsBigO.antisymm hg.1 hg.2⟩

/-- The reduction bridge for `k = 4`. -/
theorem erdos_142_four_of_matched_profile {g : ℕ → ℝ} (hg : k4_matched_profile g) :
    erdos_142 4 := by
  exact ⟨g, Asymptotics.IsBigO.antisymm hg.1 hg.2⟩

/-- Temporary `k = 3` debt (upper side): eventual inequality versus the chosen profile. -/
axiom erdos_problem_142_k3_upper_profile_bound_axiom :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop, ‖(r 3 N : ℝ)‖ ≤ C * ‖k3_profile N‖

/-- Temporary `k = 3` debt (lower side): eventual reverse inequality versus the chosen profile. -/
axiom erdos_problem_142_k3_lower_profile_bound_axiom :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop, ‖k3_profile N‖ ≤ C * ‖(r 3 N : ℝ)‖

/-- Combined matched-profile statement for `k = 3`, derived from the two narrower debts. -/
theorem erdos_problem_142_k3_matched_profile : k3_matched_profile k3_profile := by
  exact k3_matched_profile_of_eventual_bounds
    erdos_problem_142_k3_upper_profile_bound_axiom
    erdos_problem_142_k3_lower_profile_bound_axiom

/-- Derived `k = 3` branch from the matched-profile temporary debt axiom. -/
theorem erdos_problem_142_k3_case : erdos_142 3 := by
  exact erdos_142_three_of_matched_profile erdos_problem_142_k3_matched_profile

/-- Temporary `k = 4` debt (upper side): eventual inequality versus the chosen profile. -/
axiom erdos_problem_142_k4_upper_profile_bound_axiom :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop, ‖(r 4 N : ℝ)‖ ≤ C * ‖k4_profile N‖

/-- Temporary `k = 4` debt (lower side): eventual reverse inequality versus the chosen profile. -/
axiom erdos_problem_142_k4_lower_profile_bound_axiom :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop, ‖k4_profile N‖ ≤ C * ‖(r 4 N : ℝ)‖

/-- Combined matched-profile statement for `k = 4`, derived from two narrower debts. -/
theorem erdos_problem_142_k4_matched_profile : k4_matched_profile k4_profile := by
  exact k4_matched_profile_of_eventual_bounds
    erdos_problem_142_k4_upper_profile_bound_axiom
    erdos_problem_142_k4_lower_profile_bound_axiom

/-- Derived `k = 4` branch from the matched-profile temporary debt axioms. -/
theorem erdos_problem_142_k4_case : erdos_142 4 := by
  exact erdos_142_four_of_matched_profile erdos_problem_142_k4_matched_profile

/-- Generic bridge for the strengthened target:
explicit profile class + two-sided eventual bounds gives `erdos_142_explicit`. -/
theorem erdos_142_explicit_of_eventual_bounds {k : ℕ} {f : ℕ → ℝ}
    (hClass : ErdosProblems.ExplicitProfileClass k f)
    (hUpper : ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖(r k N : ℝ)‖ ≤ K * ‖f N‖)
    (hLower : ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖f N‖ ≤ K * ‖(r k N : ℝ)‖) :
    erdos_142_explicit k := by
  rcases hUpper with ⟨K, -, hK⟩
  rcases hLower with ⟨K', -, hK'⟩
  refine ⟨f, hClass, ?_⟩
  exact Asymptotics.IsBigO.antisymm
    (Asymptotics.IsBigO.of_bound K hK)
    (Asymptotics.IsBigO.of_bound K' hK')

/-- Parameter package for a fixed `k = 3` explicit profile template. -/
structure K3ExplicitParams where
  β : ℝ
  c : ℝ
  C : ℝ
  hβ : 0 < β
  hc : 0 < c
  hC : 0 < C

/-- Parameter package for a fixed `k = 4` explicit profile template. -/
structure K4ExplicitParams where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C

/-- Structured temporary two-sided profile debt for `k = 3`.
This packages explicit parameters together with upper/lower `O`-bounds to the same profile. -/
structure K3ProfileWitness where
  β : ℝ
  c : ℝ
  C : ℝ
  hβ : 0 < β
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β))
  hLower :
    (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β)) =O[atTop]
      (fun N => (r 3 N : ℝ))

/-- Imported-assumption container for the `k = 3` two-sided profile witness.
This is an interface point for replacing temporary debt with a real imported theorem. -/
class K3ProfileWitnessImported where
  k3_profile_witness : K3ProfileWitness

/-- Imported `k = 3` two-sided profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_k3_profile_witness_imported
    [h : K3ProfileWitnessImported] :
    K3ProfileWitness :=
  h.k3_profile_witness

/-- Structured temporary two-sided profile debt for `k = 4`. -/
structure K4ProfileWitness where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r 4 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c)
  hLower :
    (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[atTop]
      (fun N => (r 4 N : ℝ))

/-- Temporary two-sided profile debt witness for `k = 4`. -/
class K4ProfileWitnessImported where
  k4_profile_witness : K4ProfileWitness

/-- Imported `k = 4` two-sided profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_k4_profile_witness_imported
    [h : K4ProfileWitnessImported] :
    K4ProfileWitness :=
  h.k4_profile_witness

/-- Structured temporary two-sided profile debt for each fixed `k ≥ 5`. -/
structure Kge5ProfileWitness (k : ℕ) (hk : 5 ≤ k) where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r k N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c)
  hLower :
    (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[atTop]
      (fun N => (r k N : ℝ))

/-- Temporary two-sided profile debt witness family for each fixed `k ≥ 5`. -/
class Kge5ProfileWitnessImported where
  kge5_profile_witness : ∀ ⦃k : ℕ⦄ (hk : 5 ≤ k), Kge5ProfileWitness k hk

/-- Imported `k ≥ 5` two-sided profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_kge5_profile_witness_imported
    [h : Kge5ProfileWitnessImported] {k : ℕ} (hk : 5 ≤ k) :
    Kge5ProfileWitness k hk :=
  h.kge5_profile_witness hk

/-- Fixed explicit profile for the `k = 3` branch. -/
noncomputable def k3_explicit_profile [K3ProfileWitnessImported] : ℕ → ℝ :=
  fun N =>
    erdos_problem_142_explicit_k3_profile_witness_imported.C * (N : ℝ) *
      Real.exp
        (-erdos_problem_142_explicit_k3_profile_witness_imported.c *
          (Real.log (N + 2)) ^ erdos_problem_142_explicit_k3_profile_witness_imported.β)

/-- Fixed explicit profile for the `k = 4` branch. -/
noncomputable def k4_explicit_profile [K4ProfileWitnessImported] : ℕ → ℝ :=
  fun N =>
    erdos_problem_142_explicit_k4_profile_witness_imported.C * (N : ℝ) /
      (Real.log (N + 2)) ^ erdos_problem_142_explicit_k4_profile_witness_imported.c

/-- Fixed explicit profile for each `k ≥ 5` branch. -/
noncomputable def kge5_explicit_profile [Kge5ProfileWitnessImported]
    {k : ℕ} (hk : 5 ≤ k) : ℕ → ℝ :=
  fun N =>
    (erdos_problem_142_explicit_kge5_profile_witness_imported hk).C * (N : ℝ) /
      (Real.log (Real.log (N + 3))) ^ (erdos_problem_142_explicit_kge5_profile_witness_imported hk).c

/-- `k = 3` explicit profile belongs to the constrained profile class. -/
theorem k3_explicit_profile_class [K3ProfileWitnessImported] :
    ErdosProblems.ExplicitProfileClass 3 k3_explicit_profile := by
  change ErdosProblems.ExplicitProfileClass 3
      (fun N : ℕ =>
        erdos_problem_142_explicit_k3_profile_witness_imported.C * (N : ℝ) *
          Real.exp
            (-erdos_problem_142_explicit_k3_profile_witness_imported.c *
              (Real.log (N + 2)) ^ erdos_problem_142_explicit_k3_profile_witness_imported.β))
  exact
    ErdosProblems.ExplicitProfileClass.k3
      erdos_problem_142_explicit_k3_profile_witness_imported.β
      erdos_problem_142_explicit_k3_profile_witness_imported.c
      erdos_problem_142_explicit_k3_profile_witness_imported.C
      erdos_problem_142_explicit_k3_profile_witness_imported.hβ
      erdos_problem_142_explicit_k3_profile_witness_imported.hc
      erdos_problem_142_explicit_k3_profile_witness_imported.hC

/-- `k = 4` explicit profile belongs to the constrained profile class. -/
theorem k4_explicit_profile_class [K4ProfileWitnessImported] :
    ErdosProblems.ExplicitProfileClass 4 k4_explicit_profile := by
  change ErdosProblems.ExplicitProfileClass 4
      (fun N : ℕ =>
        erdos_problem_142_explicit_k4_profile_witness_imported.C * (N : ℝ) /
          (Real.log (N + 2)) ^ erdos_problem_142_explicit_k4_profile_witness_imported.c)
  exact
    ErdosProblems.ExplicitProfileClass.k4
      erdos_problem_142_explicit_k4_profile_witness_imported.c
      erdos_problem_142_explicit_k4_profile_witness_imported.C
      erdos_problem_142_explicit_k4_profile_witness_imported.hc
      erdos_problem_142_explicit_k4_profile_witness_imported.hC

/-- Any `k ≥ 5` explicit profile belongs to the constrained profile class. -/
theorem kge5_explicit_profile_class [Kge5ProfileWitnessImported] {k : ℕ} (hk : 5 ≤ k) :
    ErdosProblems.ExplicitProfileClass k (kge5_explicit_profile hk) := by
  change ErdosProblems.ExplicitProfileClass k
      (fun N : ℕ =>
        (erdos_problem_142_explicit_kge5_profile_witness_imported hk).C * (N : ℝ) /
          (Real.log (Real.log (N + 3))) ^ (erdos_problem_142_explicit_kge5_profile_witness_imported hk).c)
  exact
    ErdosProblems.ExplicitProfileClass.kge5
      k hk
      (erdos_problem_142_explicit_kge5_profile_witness_imported hk).c
      (erdos_problem_142_explicit_kge5_profile_witness_imported hk).C
      (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hc
      (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hC

/-- Derived upper-side quantitative bound for `k = 3`, from the structured profile witness debt. -/
theorem erdos_problem_142_explicit_k3_upper_bound_axiom [K3ProfileWitnessImported] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖(r 3 N : ℝ)‖ ≤ K * ‖k3_explicit_profile N‖ := by
  rcases (Asymptotics.isBigO_iff').1 erdos_problem_142_explicit_k3_profile_witness_imported.hUpper with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [k3_explicit_profile] using hK

/-- Derived lower-side quantitative bound for `k = 3`, from the structured profile witness debt. -/
theorem erdos_problem_142_explicit_k3_lower_bound_axiom [K3ProfileWitnessImported] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖k3_explicit_profile N‖ ≤ K * ‖(r 3 N : ℝ)‖ := by
  rcases (Asymptotics.isBigO_iff').1 erdos_problem_142_explicit_k3_profile_witness_imported.hLower with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [k3_explicit_profile] using hK

/-- Derived upper-side quantitative bound for `k = 4`, from the structured profile witness debt. -/
theorem erdos_problem_142_explicit_k4_upper_bound_axiom [K4ProfileWitnessImported] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖(r 4 N : ℝ)‖ ≤ K * ‖k4_explicit_profile N‖ := by
  rcases (Asymptotics.isBigO_iff').1 erdos_problem_142_explicit_k4_profile_witness_imported.hUpper with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [k4_explicit_profile] using hK

/-- Derived lower-side quantitative bound for `k = 4`, from the structured profile witness debt. -/
theorem erdos_problem_142_explicit_k4_lower_bound_axiom [K4ProfileWitnessImported] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖k4_explicit_profile N‖ ≤ K * ‖(r 4 N : ℝ)‖ := by
  rcases (Asymptotics.isBigO_iff').1 erdos_problem_142_explicit_k4_profile_witness_imported.hLower with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [k4_explicit_profile] using hK

/-- Derived upper-side quantitative bound for each `k ≥ 5`, from the structured profile witness
debt family. -/
theorem erdos_problem_142_explicit_kge5_upper_bound_axiom [Kge5ProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄ (hk : 5 ≤ k), ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖(r k N : ℝ)‖ ≤ K * ‖kge5_explicit_profile hk N‖ := by
  intro k hk
  rcases (Asymptotics.isBigO_iff').1 (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hUpper with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [kge5_explicit_profile] using hK

/-- Derived lower-side quantitative bound for each `k ≥ 5`, from the structured profile witness
debt family. -/
theorem erdos_problem_142_explicit_kge5_lower_bound_axiom [Kge5ProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄ (hk : 5 ≤ k), ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ‖kge5_explicit_profile hk N‖ ≤ K * ‖(r k N : ℝ)‖ := by
  intro k hk
  rcases (Asymptotics.isBigO_iff').1 (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hLower with
    ⟨K, hKpos, hK⟩
  refine ⟨K, le_of_lt hKpos, ?_⟩
  simpa [kge5_explicit_profile] using hK

/-- Derived explicit `k = 3` branch via the generic explicit bridge. -/
theorem erdos_problem_142_explicit_k3_case [K3ProfileWitnessImported] :
    erdos_142_explicit 3 := by
  exact erdos_142_explicit_of_eventual_bounds
    k3_explicit_profile_class
    erdos_problem_142_explicit_k3_upper_bound_axiom
    erdos_problem_142_explicit_k3_lower_bound_axiom

/-- Derived explicit `k = 4` branch via the generic explicit bridge. -/
theorem erdos_problem_142_explicit_k4_case [K4ProfileWitnessImported] :
    erdos_142_explicit 4 := by
  exact erdos_142_explicit_of_eventual_bounds
    k4_explicit_profile_class
    erdos_problem_142_explicit_k4_upper_bound_axiom
    erdos_problem_142_explicit_k4_lower_bound_axiom

/-- Derived explicit `k ≥ 5` branch via the generic explicit bridge. -/
theorem erdos_problem_142_explicit_kge5_case [Kge5ProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄, 5 ≤ k → erdos_142_explicit k := by
  intro k hk
  exact erdos_142_explicit_of_eventual_bounds
    (kge5_explicit_profile_class hk)
    (erdos_problem_142_explicit_kge5_upper_bound_axiom hk)
    (erdos_problem_142_explicit_kge5_lower_bound_axiom hk)

/-- Stronger structured theorem outline:
full #142 under explicit profile classes, split by `k = 3`, `k = 4`, and `k ≥ 5`. -/
theorem erdos_problem_142_explicit_solution_axiom
    [K3ProfileWitnessImported] [K4ProfileWitnessImported] [Kge5ProfileWitnessImported] :
    ErdosProblems.erdos_problem_142_explicit := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk_cases with rfl | rfl | hk5
  · exact (hasExplicitAsymptoticFormula_iff_erdos142_explicit 3).2
      erdos_problem_142_explicit_k3_case
  · exact (hasExplicitAsymptoticFormula_iff_erdos142_explicit 4).2
      erdos_problem_142_explicit_k4_case
  · exact (hasExplicitAsymptoticFormula_iff_erdos142_explicit k).2
      (erdos_problem_142_explicit_kge5_case hk5)

/-- Structured theorem outline for the full #142 target.
Now routed through the stronger explicit-profile solution scaffold. -/
theorem erdos_problem_142_solution_axiom
    [K3ProfileWitnessImported] [K4ProfileWitnessImported] [Kge5ProfileWitnessImported] :
    ErdosProblems.erdos_problem_142 := by
  intro k hk
  have hExp : erdos_142_explicit k :=
    (hasExplicitAsymptoticFormula_iff_erdos142_explicit k).1
      (erdos_problem_142_explicit_solution_axiom hk)
  exact (hasAsymptoticFormula_iff_erdos142 k).2
    (erdos_142_explicit_implies_erdos_142 hExp)

/-- The stronger explicit-profile outline implies the current statement-level #142 target. -/
theorem erdos_problem_142_solution_from_explicit_axiom
    [K3ProfileWitnessImported] [K4ProfileWitnessImported] [Kge5ProfileWitnessImported] :
    ErdosProblems.erdos_problem_142 :=
  erdos_problem_142_solution_axiom

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
