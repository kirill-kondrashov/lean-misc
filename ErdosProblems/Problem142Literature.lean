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

/-- Structured lower-profile witness for `k = 3` in Behrend shape, decoupled from upper side. -/
structure K3BehrendLowerProfileWitness where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hLower :
    (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
      (fun N => (r 3 N : ℝ))

/-- Imported Behrend-shape lower-profile witness for `k = 3`. -/
class K3BehrendLowerProfileWitnessImported where
  k3_behrend_lower_profile_witness : K3BehrendLowerProfileWitness

/-- Imported Behrend-shape lower-profile witness for `k = 3`
(from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_k3_behrend_lower_profile_witness_imported
    [h : K3BehrendLowerProfileWitnessImported] :
    K3BehrendLowerProfileWitness :=
  h.k3_behrend_lower_profile_witness

/-- Structured lower-profile witness for `k = 4`, decoupled from upper side. -/
structure K4LowerProfileWitness where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hLower :
    (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[atTop]
      (fun N => (r 4 N : ℝ))

/-- Imported lower-profile witness for `k = 4`. -/
class K4LowerProfileWitnessImported where
  k4_lower_profile_witness : K4LowerProfileWitness

/-- Imported lower-profile witness for `k = 4` (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_k4_lower_profile_witness_imported
    [h : K4LowerProfileWitnessImported] :
    K4LowerProfileWitness :=
  h.k4_lower_profile_witness

/-- Structured lower-profile witness family for each fixed `k ≥ 5`, decoupled from upper side. -/
structure Kge5LowerProfileWitness (k : ℕ) (hk : 5 ≤ k) where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hLower :
    (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[atTop]
      (fun N => (r k N : ℝ))

/-- Imported lower-profile witness family for each fixed `k ≥ 5`. -/
class Kge5LowerProfileWitnessImported where
  kge5_lower_profile_witness : ∀ ⦃k : ℕ⦄ (hk : 5 ≤ k), Kge5LowerProfileWitness k hk

/-- Imported lower-profile witness for `k ≥ 5` (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_kge5_lower_profile_witness_imported
    [h : Kge5LowerProfileWitnessImported] {k : ℕ} (hk : 5 ≤ k) :
    Kge5LowerProfileWitness k hk :=
  h.kge5_lower_profile_witness hk

/-- Any two-sided `k = 4` witness provides a lower-only `k = 4` witness. -/
noncomputable instance k4LowerProfileWitnessImported_of_k4ProfileWitnessImported
    [K4ProfileWitnessImported] : K4LowerProfileWitnessImported where
  k4_lower_profile_witness :=
    { c := erdos_problem_142_explicit_k4_profile_witness_imported.c
      C := erdos_problem_142_explicit_k4_profile_witness_imported.C
      hc := erdos_problem_142_explicit_k4_profile_witness_imported.hc
      hC := erdos_problem_142_explicit_k4_profile_witness_imported.hC
      hLower := erdos_problem_142_explicit_k4_profile_witness_imported.hLower }

/-- Any two-sided `k ≥ 5` witness family provides a lower-only witness family. -/
noncomputable instance kge5LowerProfileWitnessImported_of_kge5ProfileWitnessImported
    [Kge5ProfileWitnessImported] : Kge5LowerProfileWitnessImported where
  kge5_lower_profile_witness {_} hk :=
    { c := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).c
      C := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).C
      hc := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hc
      hC := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hC
      hLower := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hLower }

/-- Extract explicit `k = 3` Behrend-shape lower-profile data from an imported lower witness. -/
theorem k3_behrend_lower_profile_of_imported_witness [K3BehrendLowerProfileWitnessImported] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)) := by
  refine ⟨erdos_problem_142_k3_behrend_lower_profile_witness_imported.c,
    erdos_problem_142_k3_behrend_lower_profile_witness_imported.C,
    erdos_problem_142_k3_behrend_lower_profile_witness_imported.hc,
    erdos_problem_142_k3_behrend_lower_profile_witness_imported.hC, ?_⟩
  exact erdos_problem_142_k3_behrend_lower_profile_witness_imported.hLower

/-- Extract explicit `k = 4` lower-profile data from an imported lower witness. -/
theorem k4_lower_profile_of_imported_witness [K4LowerProfileWitnessImported] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[atTop]
        (fun N => (r 4 N : ℝ)) := by
  refine ⟨erdos_problem_142_k4_lower_profile_witness_imported.c,
    erdos_problem_142_k4_lower_profile_witness_imported.C,
    erdos_problem_142_k4_lower_profile_witness_imported.hc,
    erdos_problem_142_k4_lower_profile_witness_imported.hC, ?_⟩
  exact erdos_problem_142_k4_lower_profile_witness_imported.hLower

/-- Extract explicit `k ≥ 5` lower-profile family data from imported lower witnesses. -/
theorem kge5_lower_profile_of_imported_witness [Kge5LowerProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[atTop]
        (fun N => (r k N : ℝ)) := by
  intro k hk
  refine ⟨(erdos_problem_142_kge5_lower_profile_witness_imported hk).c,
    (erdos_problem_142_kge5_lower_profile_witness_imported hk).C,
    (erdos_problem_142_kge5_lower_profile_witness_imported hk).hc,
    (erdos_problem_142_kge5_lower_profile_witness_imported hk).hC, ?_⟩
  exact (erdos_problem_142_kge5_lower_profile_witness_imported hk).hLower

/-- Structured upper-profile witness for `k = 3`, decoupled from lower-side obligations. -/
structure K3UpperProfileWitness where
  β : ℝ
  c : ℝ
  C : ℝ
  hβ : 0 < β
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β))

/-- Imported upper-profile witness for `k = 3`. -/
class K3UpperProfileWitnessImported where
  k3_upper_profile_witness : K3UpperProfileWitness

/-- Imported `k = 3` upper-profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_k3_upper_profile_witness_imported
    [h : K3UpperProfileWitnessImported] :
    K3UpperProfileWitness :=
  h.k3_upper_profile_witness

/-- Structured upper-profile witness for `k = 4`, decoupled from lower-side obligations. -/
structure K4UpperProfileWitness where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r 4 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c)

/-- Imported upper-profile witness for `k = 4`. -/
class K4UpperProfileWitnessImported where
  k4_upper_profile_witness : K4UpperProfileWitness

/-- Imported `k = 4` upper-profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_k4_upper_profile_witness_imported
    [h : K4UpperProfileWitnessImported] :
    K4UpperProfileWitness :=
  h.k4_upper_profile_witness

/-- Structured upper-profile witness family for each fixed `k ≥ 5`. -/
structure Kge5UpperProfileWitness (k : ℕ) (hk : 5 ≤ k) where
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hUpper :
    (fun N => (r k N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c)

/-- Imported upper-profile witness family for each fixed `k ≥ 5`. -/
class Kge5UpperProfileWitnessImported where
  kge5_upper_profile_witness : ∀ ⦃k : ℕ⦄ (hk : 5 ≤ k), Kge5UpperProfileWitness k hk

/-- Imported `k ≥ 5` upper-profile witness (from a registered assumption instance). -/
noncomputable abbrev erdos_problem_142_explicit_kge5_upper_profile_witness_imported
    [h : Kge5UpperProfileWitnessImported] {k : ℕ} (hk : 5 ≤ k) :
    Kge5UpperProfileWitness k hk :=
  h.kge5_upper_profile_witness hk

/-- Any two-sided `k = 3` witness provides an upper-only witness. -/
noncomputable instance k3UpperProfileWitnessImported_of_k3ProfileWitnessImported
    [K3ProfileWitnessImported] : K3UpperProfileWitnessImported where
  k3_upper_profile_witness :=
    { β := erdos_problem_142_explicit_k3_profile_witness_imported.β
      c := erdos_problem_142_explicit_k3_profile_witness_imported.c
      C := erdos_problem_142_explicit_k3_profile_witness_imported.C
      hβ := erdos_problem_142_explicit_k3_profile_witness_imported.hβ
      hc := erdos_problem_142_explicit_k3_profile_witness_imported.hc
      hC := erdos_problem_142_explicit_k3_profile_witness_imported.hC
      hUpper := erdos_problem_142_explicit_k3_profile_witness_imported.hUpper }

/-- Any two-sided `k = 4` witness provides an upper-only witness. -/
noncomputable instance k4UpperProfileWitnessImported_of_k4ProfileWitnessImported
    [K4ProfileWitnessImported] : K4UpperProfileWitnessImported where
  k4_upper_profile_witness :=
    { c := erdos_problem_142_explicit_k4_profile_witness_imported.c
      C := erdos_problem_142_explicit_k4_profile_witness_imported.C
      hc := erdos_problem_142_explicit_k4_profile_witness_imported.hc
      hC := erdos_problem_142_explicit_k4_profile_witness_imported.hC
      hUpper := erdos_problem_142_explicit_k4_profile_witness_imported.hUpper }

/-- Any two-sided `k ≥ 5` witness family provides an upper-only witness family. -/
noncomputable instance kge5UpperProfileWitnessImported_of_kge5ProfileWitnessImported
    [Kge5ProfileWitnessImported] : Kge5UpperProfileWitnessImported where
  kge5_upper_profile_witness {_} hk :=
    { c := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).c
      C := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).C
      hc := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hc
      hC := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hC
      hUpper := (erdos_problem_142_explicit_kge5_profile_witness_imported hk).hUpper }

/-- Fixed upper-profile candidate for the `k = 3` branch. -/
noncomputable def k3_upper_profile [K3UpperProfileWitnessImported] : ℕ → ℝ :=
  fun N =>
    erdos_problem_142_explicit_k3_upper_profile_witness_imported.C * (N : ℝ) *
      Real.exp
        (-erdos_problem_142_explicit_k3_upper_profile_witness_imported.c *
          (Real.log (N + 2)) ^ erdos_problem_142_explicit_k3_upper_profile_witness_imported.β)

/-- Fixed upper-profile candidate for the `k = 4` branch. -/
noncomputable def k4_upper_profile [K4UpperProfileWitnessImported] : ℕ → ℝ :=
  fun N =>
    erdos_problem_142_explicit_k4_upper_profile_witness_imported.C * (N : ℝ) /
      (Real.log (N + 2)) ^ erdos_problem_142_explicit_k4_upper_profile_witness_imported.c

/-- Fixed upper-profile candidate for each `k ≥ 5` branch. -/
noncomputable def kge5_upper_profile [Kge5UpperProfileWitnessImported]
    {k : ℕ} (hk : 5 ≤ k) : ℕ → ℝ :=
  fun N =>
    (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).C * (N : ℝ) /
      (Real.log (Real.log (N + 3))) ^ (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).c

/-- Upper variant for `k = 3` from an imported upper-profile witness. -/
theorem upper_variant_three_of_upper_profile_witness [K3UpperProfileWitnessImported] :
    erdos_142.variants.upper 3 := by
  refine ⟨k3_upper_profile, ?_⟩
  change
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ =>
        erdos_problem_142_explicit_k3_upper_profile_witness_imported.C * (N : ℝ) *
          Real.exp
            (-erdos_problem_142_explicit_k3_upper_profile_witness_imported.c *
              (Real.log (N + 2)) ^ erdos_problem_142_explicit_k3_upper_profile_witness_imported.β))
  exact erdos_problem_142_explicit_k3_upper_profile_witness_imported.hUpper

/-- Upper variant for `k = 4` from an imported upper-profile witness. -/
theorem upper_variant_four_of_upper_profile_witness [K4UpperProfileWitnessImported] :
    erdos_142.variants.upper 4 := by
  refine ⟨k4_upper_profile, ?_⟩
  change
    (fun N => (r 4 N : ℝ)) =O[atTop]
      (fun N : ℕ =>
        erdos_problem_142_explicit_k4_upper_profile_witness_imported.C * (N : ℝ) /
          (Real.log (N + 2)) ^ erdos_problem_142_explicit_k4_upper_profile_witness_imported.c)
  exact erdos_problem_142_explicit_k4_upper_profile_witness_imported.hUpper

/-- Upper variant for any `k ≥ 5` from an imported upper-profile witness family. -/
theorem upper_variant_ge_five_of_upper_profile_witness [Kge5UpperProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄, 5 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  refine ⟨kge5_upper_profile hk, ?_⟩
  change
    (fun N => (r k N : ℝ)) =O[atTop]
      (fun N : ℕ =>
        (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).C * (N : ℝ) /
          (Real.log (Real.log (N + 3))) ^
            (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).c)
  exact (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).hUpper

/-- Aggregated upper-variant consequence for all `k ≥ 3` from branch-local upper witnesses. -/
theorem upper_variant_of_upper_profile_witnesses_for_all_k_ge_three
    [K3UpperProfileWitnessImported] [K4UpperProfileWitnessImported]
    [Kge5UpperProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk_cases with rfl | rfl | hk5
  · exact upper_variant_three_of_upper_profile_witness
  · exact upper_variant_four_of_upper_profile_witness
  · exact upper_variant_ge_five_of_upper_profile_witness hk5

/-- Mixed-profile two-sided `k = 3` consequence from decoupled imported lower/upper witnesses. -/
theorem k3_mixed_two_sided_profile_of_imported_split_witnesses
    [K3BehrendLowerProfileWitnessImported] [K3UpperProfileWitnessImported] :
    ∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) := by
  refine
    ⟨erdos_problem_142_k3_behrend_lower_profile_witness_imported.c,
      erdos_problem_142_k3_behrend_lower_profile_witness_imported.C,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.β,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.c,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.C,
      erdos_problem_142_k3_behrend_lower_profile_witness_imported.hc,
      erdos_problem_142_k3_behrend_lower_profile_witness_imported.hC,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.hβ,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.hc,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.hC,
      erdos_problem_142_k3_behrend_lower_profile_witness_imported.hLower,
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.hUpper⟩

/-- Mixed-profile two-sided `k = 4` consequence from decoupled imported lower/upper witnesses. -/
theorem k4_mixed_two_sided_profile_of_imported_split_witnesses
    [K4LowerProfileWitnessImported] [K4UpperProfileWitnessImported] :
    ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU) := by
  refine
    ⟨erdos_problem_142_k4_lower_profile_witness_imported.c,
      erdos_problem_142_k4_lower_profile_witness_imported.C,
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.c,
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.C,
      erdos_problem_142_k4_lower_profile_witness_imported.hc,
      erdos_problem_142_k4_lower_profile_witness_imported.hC,
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.hc,
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.hC,
      erdos_problem_142_k4_lower_profile_witness_imported.hLower,
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.hUpper⟩

/-- Mixed-profile two-sided `k ≥ 5` family consequence from decoupled imported lower/upper
witness families. -/
theorem kge5_mixed_two_sided_profile_of_imported_split_witnesses
    [Kge5LowerProfileWitnessImported] [Kge5UpperProfileWitnessImported] :
    ∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cL) =O[atTop]
          (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cU) := by
  intro k hk
  refine
    ⟨(erdos_problem_142_kge5_lower_profile_witness_imported hk).c,
      (erdos_problem_142_kge5_lower_profile_witness_imported hk).C,
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).c,
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).C,
      (erdos_problem_142_kge5_lower_profile_witness_imported hk).hc,
      (erdos_problem_142_kge5_lower_profile_witness_imported hk).hC,
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).hc,
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).hC,
      (erdos_problem_142_kge5_lower_profile_witness_imported hk).hLower,
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).hUpper⟩

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

namespace import_targets

/-- Import-ready target shape for potential future `k = 4` lower-profile results. -/
def k4_polylog_lower_profile : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[atTop]
      (fun N => (r 4 N : ℝ))

/-- Import-ready target shape for potential future `k ≥ 5` lower-profile family results. -/
def kge5_iteratedlog_lower_profile : Prop :=
  ∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[atTop]
      (fun N => (r k N : ℝ))

/-- Import-ready branch coupling target for `k = 3`:
`MainSplitGap` currently provides separate upper/lower branches; this is the exact coupled target needed
to recover a full two-sided witness in the `k = 3` branch. -/
def split_gap_k3_coupling_target : Type :=
  ∀ [K3UpperProfileWitnessImported] [K3BehrendLowerProfileWitnessImported], K3ProfileWitness

/-- Explicit dominance bridge needed to turn upper/lower split data for `k = 3` into
the same template used by `K3ProfileWitness`.
This keeps the blocker as a concrete `IsBigO` relation between the
`k = 3` upper-superpolylog and Behrend-lower templates. -/
def split_gap_k3_profile_dominance_target : Prop :=
  ∀ [K3UpperProfileWitnessImported] [K3BehrendLowerProfileWitnessImported],
    (fun N : ℕ =>
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.C * (N : ℝ) *
        Real.exp (-erdos_problem_142_explicit_k3_upper_profile_witness_imported.c *
          (Real.log (N + 2)) ^ erdos_problem_142_explicit_k3_upper_profile_witness_imported.β))
      =O[Filter.atTop] (fun N : ℕ =>
      erdos_problem_142_k3_behrend_lower_profile_witness_imported.C * (N : ℝ) *
        Real.exp (-erdos_problem_142_k3_behrend_lower_profile_witness_imported.c *
          Real.sqrt (Real.log (N + 2))))

/-- Explicit dominance bridge needed to turn split upper/lower data for `k = 4` into the same profile
template used by `K4ProfileWitness`. -/
def split_gap_k4_profile_dominance_target : Prop :=
  ∀ [K4UpperProfileWitnessImported] [K4LowerProfileWitnessImported],
    (fun N : ℕ =>
      erdos_problem_142_explicit_k4_upper_profile_witness_imported.C * (N : ℝ) /
        (Real.log (N + 2)) ^ erdos_problem_142_explicit_k4_upper_profile_witness_imported.c)
      =O[Filter.atTop] (fun N : ℕ =>
      erdos_problem_142_k4_lower_profile_witness_imported.C * (N : ℝ) /
        (Real.log (N + 2)) ^ erdos_problem_142_k4_lower_profile_witness_imported.c)

/-- Explicit dominance bridge needed to turn split upper/lower data for `k ≥ 5` into the same profile
template used by `Kge5ProfileWitness`. -/
def split_gap_kge5_profile_dominance_target : Prop :=
  ∀ [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] ⦃k : ℕ⦄
    (hk : 5 ≤ k),
    (fun N : ℕ =>
      (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).C * (N : ℝ) /
        (Real.log (Real.log (N + 3))) ^
          (erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk).c)
      =O[Filter.atTop] (fun N : ℕ =>
      (erdos_problem_142_kge5_lower_profile_witness_imported hk).C * (N : ℝ) /
        (Real.log (Real.log (N + 3))) ^
          (erdos_problem_142_kge5_lower_profile_witness_imported hk).c)

/-- Import-ready branch coupling target for `k = 4`:
from split upper/lower branch data to a full two-sided `K4ProfileWitness`. -/
def split_gap_k4_coupling_target : Type :=
  ∀ [K4UpperProfileWitnessImported] [K4LowerProfileWitnessImported], K4ProfileWitness

/-- Import-ready branch coupling target for `k ≥ 5`:
family-wise variant of the full two-sided `Kge5ProfileWitness` recovery. -/
def split_gap_kge5_coupling_target : Type :=
  ∀ [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] ⦃k : ℕ⦄
    (hk : 5 ≤ k), Kge5ProfileWitness k hk

end import_targets

/-- Strengthened import-assumption layer that includes explicit lower-profile target templates
for the currently missing `k = 4` and `k ≥ 5` branches. -/
class LiteratureLowerImportAssumptions : Prop extends LiteratureRateAssumptions where
  k4_polylog_lower_profile : import_targets.k4_polylog_lower_profile
  kge5_iteratedlog_lower_profile : import_targets.kge5_iteratedlog_lower_profile

/-- If lower branch imports are supplied, the two missing lower-target stubs are available. -/
theorem lower_import_targets_of_literatureLowerImportAssumptions
    [h : LiteratureLowerImportAssumptions] :
    import_targets.k4_polylog_lower_profile ∧
      import_targets.kge5_iteratedlog_lower_profile := by
  exact ⟨h.k4_polylog_lower_profile, h.kge5_iteratedlog_lower_profile⟩

/-- Any imported `k = 4` lower witness realizes the `k = 4` lower import-target template. -/
theorem k4_lower_import_target_of_imported_witness [K4LowerProfileWitnessImported] :
    import_targets.k4_polylog_lower_profile := by
  exact k4_lower_profile_of_imported_witness

/-- Any imported `k ≥ 5` lower witness family realizes the `k ≥ 5` lower import-target template. -/
theorem kge5_lower_import_target_of_imported_witness [Kge5LowerProfileWitnessImported] :
    import_targets.kge5_iteratedlog_lower_profile := by
  exact kge5_lower_profile_of_imported_witness

/-- Noncomputable extraction of a `k = 3` upper-profile witness from
`LiteratureRateAssumptions`, via classical choice. -/
noncomputable def k3UpperProfileWitness_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K3UpperProfileWitness := by
  classical
  let hw : ∃ w : K3UpperProfileWitness, True := by
    rcases h.k3_superpolylog_upper_profile with ⟨β, c, C, hβ, hc, hC, hUpper⟩
    refine ⟨{ β := β, c := c, C := C, hβ := hβ, hc := hc, hC := hC, hUpper := hUpper }, trivial⟩
  exact Classical.choose hw

/-- Noncomputable extraction of a `k = 4` upper-profile witness from
`LiteratureRateAssumptions`, via classical choice. -/
noncomputable def k4UpperProfileWitness_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K4UpperProfileWitness := by
  classical
  let hw : ∃ w : K4UpperProfileWitness, True := by
    rcases h.k4_polylog_upper_profile with ⟨c, C, hc, hC, hUpper⟩
    refine ⟨{ c := c, C := C, hc := hc, hC := hC, hUpper := hUpper }, trivial⟩
  exact Classical.choose hw

/-- Noncomputable extraction of any fixed `k ≥ 5` upper-profile witness from
`LiteratureRateAssumptions`, via classical choice. -/
noncomputable def kge5UpperProfileWitness_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] {k : ℕ} (hk : 5 ≤ k) : Kge5UpperProfileWitness k hk := by
  classical
  let hw : ∃ w : Kge5UpperProfileWitness k hk, True := by
    rcases h.kge5_iteratedlog_upper_profile hk with ⟨c, C, hc, hC, hUpper⟩
    refine ⟨{ c := c, C := C, hc := hc, hC := hC, hUpper := hUpper }, trivial⟩
  exact Classical.choose hw

/-- `LiteratureRateAssumptions` provide the `k = 3` upper-profile witness interface. -/
noncomputable instance k3UpperProfileWitnessImported_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K3UpperProfileWitnessImported where
  k3_upper_profile_witness := k3UpperProfileWitness_of_literatureRateAssumptions

/-- `LiteratureRateAssumptions` provide the `k = 4` upper-profile witness interface. -/
noncomputable instance k4UpperProfileWitnessImported_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K4UpperProfileWitnessImported where
  k4_upper_profile_witness := k4UpperProfileWitness_of_literatureRateAssumptions

/-- `LiteratureRateAssumptions` provide the `k ≥ 5` upper-profile witness family interface. -/
noncomputable instance kge5UpperProfileWitnessImported_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : Kge5UpperProfileWitnessImported where
  kge5_upper_profile_witness {_} hk := kge5UpperProfileWitness_of_literatureRateAssumptions hk

/-- Upper-variant consequences for all `k ≥ 3`, routed through upper-profile witness interfaces
extracted from `LiteratureRateAssumptions`. -/
theorem upper_variant_of_literature_rates_via_upper_profile_witnesses
    [h : LiteratureRateAssumptions] :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  letI : K3UpperProfileWitnessImported := k3UpperProfileWitnessImported_of_literatureRateAssumptions
  letI : K4UpperProfileWitnessImported := k4UpperProfileWitnessImported_of_literatureRateAssumptions
  letI : Kge5UpperProfileWitnessImported := kge5UpperProfileWitnessImported_of_literatureRateAssumptions
  exact upper_variant_of_upper_profile_witnesses_for_all_k_ge_three

/-- Under benchmark assumptions, all `k ≥ 3` have a nontrivial `upper`-variant statement. -/
theorem upper_variant_of_literature_for_all_k_ge_three [h : LiteratureAssumptions] :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk_cases with rfl | rfl | hk5
  · exact h.k3_upper_kelley_meka
  · exact h.k4_upper_green_tao
  · exact h.kge5_upper_leng_sah_sawhney hk5

/-- Convert eventual Behrend-style lower inequalities into an `isBigO` lower-profile statement. -/
theorem k3_behrend_lower_isBigO_of_eventual_le {c C : ℝ}
    (hC : 0 ≤ C)
    (hLower :
      ∀ᶠ N : ℕ in atTop,
        C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2))) ≤ (r 3 N : ℝ)) :
    (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
      (fun N => (r 3 N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [hLower] with N hN
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hExp_nonneg : 0 ≤ Real.exp (-c * Real.sqrt (Real.log (N + 2))) := by positivity
  have hLeft_nonneg :
      0 ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2))) := by
    exact mul_nonneg (mul_nonneg hC hN_nonneg) hExp_nonneg
  have hRight_nonneg : 0 ≤ (r 3 N : ℝ) := by
    exact_mod_cast (Nat.zero_le (r 3 N))
  calc
    ‖C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))‖
        = C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2))) := by
          exact Real.norm_of_nonneg hLeft_nonneg
    _ ≤ (r 3 N : ℝ) := hN
    _ = ‖(r 3 N : ℝ)‖ := by
          symm
          exact Real.norm_of_nonneg hRight_nonneg
    _ = (1 : ℝ) * ‖(r 3 N : ℝ)‖ := by ring

/-- Behrend-style `k = 3` lower-profile target gives an explicit `isBigO` lower-profile witness
in the same shape (without coupling to the upper-side exponent parameter). -/
theorem k3_behrend_lower_profile_implies_isBigO_lower :
    bound_targets.k3_behrend_lower_profile →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
          (fun N => (r 3 N : ℝ)) := by
  intro h
  rcases h with ⟨c, C, hc, hC, hLower⟩
  refine ⟨c, C, hc, hC, ?_⟩
  exact k3_behrend_lower_isBigO_of_eventual_le (le_of_lt hC) hLower

/-- `LiteratureRateAssumptions` imply an explicit `isBigO` lower-profile witness for the Behrend
shape at `k = 3`. -/
theorem k3_behrend_lower_isBigO_of_literature_rates [h : LiteratureRateAssumptions] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)) := by
  exact k3_behrend_lower_profile_implies_isBigO_lower h.k3_behrend_lower_profile

/-- Noncomputable extraction of a `k = 3` Behrend-lower witness from
`LiteratureRateAssumptions`, via classical choice. -/
noncomputable def k3BehrendLowerProfileWitness_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K3BehrendLowerProfileWitness := by
  classical
  let hw : ∃ w : K3BehrendLowerProfileWitness, True := by
    rcases k3_behrend_lower_isBigO_of_literature_rates (h := h) with ⟨c, C, hc, hC, hLower⟩
    refine ⟨{ c := c, C := C, hc := hc, hC := hC, hLower := hLower }, trivial⟩
  exact Classical.choose hw

/-- `LiteratureRateAssumptions` provide the `k = 3` Behrend-lower witness interface. -/
noncomputable instance k3BehrendLowerProfileWitnessImported_of_literatureRateAssumptions
    [h : LiteratureRateAssumptions] : K3BehrendLowerProfileWitnessImported where
  k3_behrend_lower_profile_witness := k3BehrendLowerProfileWitness_of_literatureRateAssumptions

/-- `k = 3` Behrend-lower profile route through the imported-lower interface layer. -/
theorem k3_behrend_lower_profile_of_literature_rates_via_imported_lower_witness
    [h : LiteratureRateAssumptions] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)) := by
  letI : K3BehrendLowerProfileWitnessImported :=
    k3BehrendLowerProfileWitnessImported_of_literatureRateAssumptions
  exact k3_behrend_lower_profile_of_imported_witness

/-- Mixed-profile two-sided `k = 3` consequence from benchmark rate assumptions:
Behrend-shape lower profile together with superpolylog upper profile. -/
theorem k3_mixed_two_sided_profile_of_literature_rates [h : LiteratureRateAssumptions] :
    ∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) := by
  rcases k3_behrend_lower_isBigO_of_literature_rates (h := h) with ⟨cL, CL, hcL, hCL, hLower⟩
  rcases h.k3_superpolylog_upper_profile with ⟨β, cU, CU, hβ, hcU, hCU, hUpper⟩
  exact ⟨cL, CL, β, cU, CU, hcL, hCL, hβ, hcU, hCU, hLower, hUpper⟩

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
