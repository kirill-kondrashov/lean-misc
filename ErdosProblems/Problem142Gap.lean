import ErdosProblems.Problem142Literature

namespace Erdos142

/-- Bundle of imported upper-profile witness interfaces for branch-local best-known consequences. -/
structure Problem142UpperImportedWitnessBundle where
  k3 : K3UpperProfileWitnessImported
  k4 : K4UpperProfileWitnessImported
  kge5 : Kge5UpperProfileWitnessImported

/-- Main upper-gap packaging:
provide imported upper-profile witnesses for `k = 3`, `k = 4`, and all `k ≥ 5`. -/
abbrev MainUpperGap : Type := Problem142UpperImportedWitnessBundle

/-- If the upper-gap bundle is provided, all `k ≥ 3` upper variants follow. -/
theorem upper_variant_of_main_upper_gap
    (hGap : MainUpperGap) : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  letI : K3UpperProfileWitnessImported := hGap.k3
  letI : K4UpperProfileWitnessImported := hGap.k4
  letI : Kge5UpperProfileWitnessImported := hGap.kge5
  exact upper_variant_of_upper_profile_witnesses_for_all_k_ge_three

/-- Package existing upper-profile interfaces as a named upper-gap witness. -/
def mainUpperGap_of_instances [K3UpperProfileWitnessImported] [K4UpperProfileWitnessImported]
    [Kge5UpperProfileWitnessImported] : MainUpperGap :=
  { k3 := inferInstance, k4 := inferInstance, kge5 := inferInstance }

/-- Bundle of imported lower-profile witness interfaces for branch-local lower-side consequences. -/
structure Problem142LowerImportedWitnessBundle where
  k3 : K3BehrendLowerProfileWitnessImported
  k4 : K4LowerProfileWitnessImported
  kge5 : Kge5LowerProfileWitnessImported

/-- Main lower-gap packaging:
provide imported lower-profile witnesses for `k = 3`, `k = 4`, and all `k ≥ 5`. -/
abbrev MainLowerGap : Type := Problem142LowerImportedWitnessBundle

/-- If the lower-gap bundle is provided, branch-local lower-profile data become available. -/
theorem lower_profile_data_of_main_lower_gap
    (hGap : MainLowerGap) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
        (fun N => (r 3 N : ℝ))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[Filter.atTop]
        (fun N => (r 4 N : ℝ))) ∧
    (∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[Filter.atTop]
        (fun N => (r k N : ℝ))) := by
  letI : K3BehrendLowerProfileWitnessImported := hGap.k3
  letI : K4LowerProfileWitnessImported := hGap.k4
  letI : Kge5LowerProfileWitnessImported := hGap.kge5
  exact ⟨
    k3_behrend_lower_profile_of_imported_witness,
    k4_lower_profile_of_imported_witness,
    kge5_lower_profile_of_imported_witness⟩

/-- Package existing lower-profile interfaces as a named lower-gap witness. -/
def mainLowerGap_of_instances [K3BehrendLowerProfileWitnessImported] [K4LowerProfileWitnessImported]
    [Kge5LowerProfileWitnessImported] : MainLowerGap :=
  { k3 := inferInstance, k4 := inferInstance, kge5 := inferInstance }

/-- Bundle that combines the decoupled upper/lower gap layers. -/
structure Problem142SplitImportedWitnessBundle where
  upper : MainUpperGap
  lower : MainLowerGap

/-- Main split-gap packaging:
combine upper-only and lower-only interface layers without forcing matched parameters. -/
abbrev MainSplitGap : Type := Problem142SplitImportedWitnessBundle

/-- If the split-gap bundle is provided, upper consequences and branch-local mixed-profile data
are all available simultaneously. -/
theorem split_gap_data_of_main_split_gap
    (hGap : MainSplitGap) :
    (∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
        (fun N => (r 3 N : ℝ))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[Filter.atTop]
        (fun N => (r 4 N : ℝ))) ∧
    (∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[Filter.atTop]
        (fun N => (r k N : ℝ))) ∧
    (∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))) ∧
    (∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)) ∧
    (∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cL) =O[Filter.atTop]
          (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cU)) := by
  letI : K3UpperProfileWitnessImported := hGap.upper.k3
  letI : K4UpperProfileWitnessImported := hGap.upper.k4
  letI : Kge5UpperProfileWitnessImported := hGap.upper.kge5
  letI : K3BehrendLowerProfileWitnessImported := hGap.lower.k3
  letI : K4LowerProfileWitnessImported := hGap.lower.k4
  letI : Kge5LowerProfileWitnessImported := hGap.lower.kge5
  refine ⟨
    upper_variant_of_upper_profile_witnesses_for_all_k_ge_three,
    k3_behrend_lower_profile_of_imported_witness,
    k4_lower_profile_of_imported_witness,
    kge5_lower_profile_of_imported_witness,
    k3_mixed_two_sided_profile_of_imported_split_witnesses,
    k4_mixed_two_sided_profile_of_imported_split_witnesses,
    kge5_mixed_two_sided_profile_of_imported_split_witnesses⟩

/-- Package existing split upper/lower interfaces as a named split-gap witness. -/
def mainSplitGap_of_instances [K3UpperProfileWitnessImported] [K4UpperProfileWitnessImported]
    [Kge5UpperProfileWitnessImported]
    [K3BehrendLowerProfileWitnessImported] [K4LowerProfileWitnessImported]
    [Kge5LowerProfileWitnessImported] : MainSplitGap :=
  { upper := mainUpperGap_of_instances, lower := mainLowerGap_of_instances }

/-- Bundle of imported witness interfaces that currently carry the unresolved
mathematical content behind the #142 solution outline. -/
structure Problem142ImportedWitnessBundle where
  k3 : K3ProfileWitnessImported
  k4 : K4ProfileWitnessImported
  kge5 : Kge5ProfileWitnessImported

/-- Main theoretical gap in the current formalization:
provide imported two-sided asymptotic witnesses for `k = 3`, `k = 4`, and all `k ≥ 5`. -/
abbrev MainTheoreticalGap : Type := Problem142ImportedWitnessBundle

/-- If the gap bundle is provided, the current outline yields the statement-level #142 target. -/
theorem erdos_problem_142_of_main_theoretical_gap
    (hGap : MainTheoreticalGap) : ErdosProblems.erdos_problem_142 := by
  letI : K3ProfileWitnessImported := hGap.k3
  letI : K4ProfileWitnessImported := hGap.k4
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact erdos_problem_142_solution_axiom

/-- Package existing imported interfaces as a named gap witness. -/
def mainTheoreticalGap_of_instances [K3ProfileWitnessImported] [K4ProfileWitnessImported]
    [Kge5ProfileWitnessImported] : MainTheoreticalGap :=
  { k3 := inferInstance, k4 := inferInstance, kge5 := inferInstance }

/-- Any full two-sided main-gap witness bundle yields an upper-gap bundle. -/
noncomputable def mainUpperGap_of_mainTheoreticalGap (hGap : MainTheoreticalGap) : MainUpperGap := by
  letI : K3ProfileWitnessImported := hGap.k3
  letI : K4ProfileWitnessImported := hGap.k4
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainUpperGap_of_instances

/-- Consequently, a full two-sided main-gap witness bundle yields all `k ≥ 3` upper variants. -/
theorem upper_variant_of_mainTheoreticalGap
    (hGap : MainTheoreticalGap) : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k :=
  upper_variant_of_main_upper_gap (mainUpperGap_of_mainTheoreticalGap hGap)

/-- Full two-sided main-gap witnesses, plus a `k = 3` Behrend-lower witness, yield a split-gap
bundle. This isolates the precise extra ingredient not implied by current full witness interfaces:
the Behrend-shape lower branch at `k = 3`. -/
noncomputable def mainSplitGap_of_mainTheoreticalGap_and_k3BehrendLower
    (hGap : MainTheoreticalGap) [K3BehrendLowerProfileWitnessImported] : MainSplitGap := by
  letI : K3ProfileWitnessImported := hGap.k3
  letI : K4ProfileWitnessImported := hGap.k4
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainSplitGap_of_instances

/-- Mixed split-gap data are available from a full main-gap witness bundle once the
`k = 3` Behrend-lower witness is supplied. -/
theorem split_gap_data_of_mainTheoreticalGap_and_k3BehrendLower
    (hGap : MainTheoreticalGap) [K3BehrendLowerProfileWitnessImported] :
    (∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
        (fun N => (r 3 N : ℝ))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c) =O[Filter.atTop]
        (fun N => (r 4 N : ℝ))) ∧
    (∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c) =O[Filter.atTop]
        (fun N => (r k N : ℝ))) ∧
    (∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))) ∧
    (∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)) ∧
    (∀ ⦃k : ℕ⦄, 5 ≤ k → ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cL) =O[Filter.atTop]
          (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cU)) :=
  split_gap_data_of_main_split_gap
    (mainSplitGap_of_mainTheoreticalGap_and_k3BehrendLower hGap)

/-- Minimal coupling-assumption layer needed to reconstruct the strong full-gap witnesses from
the split upper/lower interface layers. -/
abbrev CouplingTargetK3 : Type :=
  ∀ [K3UpperProfileWitnessImported] [K3BehrendLowerProfileWitnessImported], K3ProfileWitness

/-- Branch-local coupling target for `k = 4`: recover a matched `K4ProfileWitness`
from split upper/lower interfaces. -/
abbrev CouplingTargetK4 : Type :=
  ∀ [K4UpperProfileWitnessImported] [K4LowerProfileWitnessImported], K4ProfileWitness

/-- Branch-local coupling target family for `k ≥ 5`: recover matched `Kge5ProfileWitness`
from split upper/lower interfaces. -/
abbrev CouplingTargetKge5 : Type :=
  ∀ [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] ⦃k : ℕ⦄
    (hk : 5 ≤ k), Kge5ProfileWitness k hk

/-- Minimal coupling-assumption layer needed to reconstruct the strong full-gap witnesses from
the split upper/lower interface layers. -/
structure SplitGapToMainTheoreticalGapAssumptions where
  k3_profile_witness_of_split : CouplingTargetK3
  k4_profile_witness_of_split : CouplingTargetK4
  kge5_profile_witness_of_split : CouplingTargetKge5

/-- Frontier axiom placeholders for unresolved split-to-full coupling:
`k = 3`, `k = 4`, and `k ≥ 5` branch recovery still lacks direct derivations from current local
literature assumptions, so these are kept as explicit temporary assumptions. -/
axiom splitGap_k3_profile_dominance_frontier :
  import_targets.split_gap_k3_profile_dominance_target

axiom splitGap_k4_profile_dominance_frontier :
  import_targets.split_gap_k4_profile_dominance_target

axiom splitGap_kge5_profile_dominance_frontier :
  import_targets.split_gap_kge5_profile_dominance_target

/-- Branch-local `k = 3` coupling can be built from an explicit upper/lower template dominance target. -/
noncomputable def splitGap_k3_coupling_target_of_profile_dominance_target
    [K3UpperProfileWitnessImported] [K3BehrendLowerProfileWitnessImported]
    (hDom :
      import_targets.split_gap_k3_profile_dominance_target) :
    import_targets.split_gap_k3_coupling_target := by
  intro _ _
  let wU : K3UpperProfileWitness := erdos_problem_142_explicit_k3_upper_profile_witness_imported
  let wL : K3BehrendLowerProfileWitness := erdos_problem_142_k3_behrend_lower_profile_witness_imported
  refine ⟨wU.β, wU.c, wU.C, wU.hβ, wU.hc, wU.hC, wU.hUpper, ?_⟩
  simpa [wU, wL] using (hDom).trans wL.hLower

noncomputable def splitGap_k3_coupling_frontier : CouplingTargetK3 :=
  splitGap_k3_coupling_target_of_profile_dominance_target
    splitGap_k3_profile_dominance_frontier

/-- Branch-local `k = 4` coupling can be built from an explicit upper/lower template dominance target. -/
noncomputable def splitGap_k4_coupling_target_of_profile_dominance_target
    [K4UpperProfileWitnessImported] [K4LowerProfileWitnessImported]
    (hDom :
      import_targets.split_gap_k4_profile_dominance_target) :
    import_targets.split_gap_k4_coupling_target := by
  intro _ _
  let wU : K4UpperProfileWitness := erdos_problem_142_explicit_k4_upper_profile_witness_imported
  let wL : K4LowerProfileWitness := erdos_problem_142_k4_lower_profile_witness_imported
  refine ⟨wU.c, wU.C, wU.hc, wU.hC, wU.hUpper, ?_⟩
  simpa [wU, wL] using (hDom).trans wL.hLower

noncomputable def splitGap_k4_coupling_frontier : CouplingTargetK4 :=
  splitGap_k4_coupling_target_of_profile_dominance_target
    splitGap_k4_profile_dominance_frontier

/-- Branch-local `k ≥ 5` coupling can be built from an explicit upper/lower template dominance target. -/
noncomputable def splitGap_kge5_coupling_target_of_profile_dominance_target
    [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported]
    (hDom :
      import_targets.split_gap_kge5_profile_dominance_target) :
    ∀ {k : ℕ} (hk : 5 ≤ k), Kge5ProfileWitness k hk := by
  intro k hk
  let wU : Kge5UpperProfileWitness k hk := erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk
  let wL : Kge5LowerProfileWitness k hk := erdos_problem_142_kge5_lower_profile_witness_imported hk
  refine ⟨wU.c, wU.C, wU.hc, wU.hC, wU.hUpper, ?_⟩
  simpa [wU, wL] using (hDom (k := k) hk).trans wL.hLower

noncomputable def splitGap_kge5_coupling_frontier :
    CouplingTargetKge5 := by
  intro _ _ k hk
  let wU : Kge5UpperProfileWitness k hk := erdos_problem_142_explicit_kge5_upper_profile_witness_imported hk
  let wL : Kge5LowerProfileWitness k hk := erdos_problem_142_kge5_lower_profile_witness_imported hk
  refine ⟨wU.c, wU.C, wU.hc, wU.hC, wU.hUpper, ?_⟩
  simpa [wU, wL] using (splitGap_kge5_profile_dominance_frontier (k := k) hk).trans wL.hLower

/-- Pack the current axiom frontier into the split-to-full coupling assumption structure. -/
noncomputable def splitGapToMainTheoreticalGapAssumptions_frontier :
    SplitGapToMainTheoreticalGapAssumptions :=
  { k3_profile_witness_of_split := splitGap_k3_coupling_frontier
    k4_profile_witness_of_split := splitGap_k4_coupling_frontier
    kge5_profile_witness_of_split := by
      intro _ _ k hk
      exact splitGap_kge5_coupling_frontier (k := k) hk }

/-- Import-ready target aliases for branch coupling are definitionally identical to the local coupling
targets. -/
noncomputable def splitGap_k3_coupling_target_of_frontier :
    import_targets.split_gap_k3_coupling_target := by
  exact splitGap_k3_coupling_frontier

/-- Import-ready target aliases for branch coupling are definitionally identical to the local coupling
targets. -/
noncomputable def splitGap_k4_coupling_target_of_frontier :
    import_targets.split_gap_k4_coupling_target := by
  exact splitGap_k4_coupling_frontier

/-- Import-ready target aliases for branch coupling are definitionally identical to the local coupling
targets. -/
noncomputable def splitGap_kge5_coupling_target_of_frontier :
    import_targets.split_gap_kge5_coupling_target := by
  intro _ _ k hk
  exact splitGap_kge5_coupling_frontier (k := k) hk

/-- Package import-ready coupling targets into a concrete assumption structure. -/
noncomputable def splitGapToMainTheoreticalGapAssumptions_of_importTargets
    (h3 : import_targets.split_gap_k3_coupling_target)
    (h4 : import_targets.split_gap_k4_coupling_target)
    (hkge5 : import_targets.split_gap_kge5_coupling_target) :
    SplitGapToMainTheoreticalGapAssumptions :=
  { k3_profile_witness_of_split := h3
    k4_profile_witness_of_split := h4
    kge5_profile_witness_of_split := by
      intro _ _ k hk
      exact hkge5 (k := k) hk }

/-- Expose branch-local coupling targets from the combined coupling-assumption package. -/
def coupling_targets_of_splitGapToMainTheoreticalGapAssumptions
    (h : SplitGapToMainTheoreticalGapAssumptions) :
    CouplingTargetK3 × CouplingTargetK4 × CouplingTargetKge5 := by
  refine ⟨h.k3_profile_witness_of_split, h.k4_profile_witness_of_split, ?_⟩
  intro _ _ k hk
  exact h.kge5_profile_witness_of_split hk

/-- Under explicit coupling assumptions, split-gap data can be promoted to the full main gap. -/
noncomputable def mainTheoreticalGap_of_mainSplitGap_and_assumptions
    (hSplit : MainSplitGap) (hCoupling : SplitGapToMainTheoreticalGapAssumptions) :
    MainTheoreticalGap := by
  letI : K3UpperProfileWitnessImported := hSplit.upper.k3
  letI : K4UpperProfileWitnessImported := hSplit.upper.k4
  letI : Kge5UpperProfileWitnessImported := hSplit.upper.kge5
  letI : K3BehrendLowerProfileWitnessImported := hSplit.lower.k3
  letI : K4LowerProfileWitnessImported := hSplit.lower.k4
  letI : Kge5LowerProfileWitnessImported := hSplit.lower.kge5
  refine
    { k3 := { k3_profile_witness := hCoupling.k3_profile_witness_of_split }
      k4 := { k4_profile_witness := hCoupling.k4_profile_witness_of_split }
      kge5 := { kge5_profile_witness := fun {_} hk =>
        hCoupling.kge5_profile_witness_of_split hk } }

/-- Split-gap witnesses plus explicit coupling assumptions imply the statement-level #142 target. -/
theorem erdos_problem_142_of_mainSplitGap_and_assumptions
    (hSplit : MainSplitGap) (hCoupling : SplitGapToMainTheoreticalGapAssumptions) :
    ErdosProblems.erdos_problem_142 := by
  exact
    erdos_problem_142_of_main_theoretical_gap
      (mainTheoreticalGap_of_mainSplitGap_and_assumptions hSplit hCoupling)

/-- Frontier theorem: statement-level #142 from split-gap together with the current axiom frontier. -/
theorem erdos_problem_142_of_mainSplitGap_and_frontier
    (hSplit : MainSplitGap) : ErdosProblems.erdos_problem_142 := by
  exact erdos_problem_142_of_mainSplitGap_and_assumptions
    hSplit splitGapToMainTheoreticalGapAssumptions_frontier

end Erdos142
