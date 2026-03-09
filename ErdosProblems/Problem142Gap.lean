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

/-- The strengthened lower-import literature layer already packages an ordinary split gap:
upper witnesses come from its inherited rate assumptions, while the `k = 4` and `k ≥ 5` lower
interfaces come from the dedicated lower-import assumptions. -/
noncomputable def mainSplitGap_of_literatureLowerImportAssumptions
    [h : LiteratureLowerImportAssumptions] : MainSplitGap := by
  letI : K3UpperProfileWitnessImported := k3UpperProfileWitnessImported_of_literatureRateAssumptions
  letI : K4UpperProfileWitnessImported := k4UpperProfileWitnessImported_of_literatureRateAssumptions
  letI : Kge5UpperProfileWitnessImported := kge5UpperProfileWitnessImported_of_literatureRateAssumptions
  letI : K3BehrendLowerProfileWitnessImported := k3BehrendLowerProfileWitnessImported_of_literatureRateAssumptions
  letI : K4LowerProfileWitnessImported := k4LowerProfileWitnessImported_of_literatureLowerImportAssumptions
  letI : Kge5LowerProfileWitnessImported :=
    kge5LowerProfileWitnessImported_of_literatureLowerImportAssumptions
  exact mainSplitGap_of_instances

/-- All split-gap consequences follow from `LiteratureLowerImportAssumptions`.
This is the honest currently available endpoint before any matched-profile coupling theorem for
`k = 4` or `k ≥ 5`. -/
theorem split_gap_data_of_literatureLowerImportAssumptions
    [h : LiteratureLowerImportAssumptions] :
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
  exact split_gap_data_of_main_split_gap (mainSplitGap_of_literatureLowerImportAssumptions (h := h))

/-- Gap-layer alias for the strongest currently source-backed `k = 4` split surface. -/
abbrev K4SourceBackedSplitGap : Type := K4SourceBackedSplitWitness

/-- The strengthened lower-import literature layer already instantiates the honest local
`k = 4` split surface. -/
noncomputable def k4SourceBackedSplitGap_of_literatureLowerImportAssumptions
    [h : LiteratureLowerImportAssumptions] :
    K4SourceBackedSplitGap :=
  k4SourceBackedSplitWitness_of_literatureLowerImportAssumptions

/-- Branch-local `k = 4` split data follow directly from the dedicated source-backed split
package extracted from `LiteratureLowerImportAssumptions`. -/
theorem k4_split_data_of_literatureLowerImportAssumptions
    [h : LiteratureLowerImportAssumptions] :
    ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU) := by
  exact k4_mixed_two_sided_profile_of_sourceBackedSplitWitness
    (k4SourceBackedSplitGap_of_literatureLowerImportAssumptions (h := h))

/-- Gap-layer alias for the corrected broader-source `k = 4` split surface. -/
abbrev K4HeterogeneousSourceBackedSplitGap : Type := K4HeterogeneousSourceBackedSplitWitness

/-- The combined broader-source `k = 4` literature layer already instantiates the corrected
heterogeneous split surface. -/
noncomputable def k4HeterogeneousSourceBackedSplitGap_of_literatureK4HeterogeneousSourceBackedSplitAssumptions
    [h : LiteratureK4HeterogeneousSourceBackedSplitAssumptions] :
    K4HeterogeneousSourceBackedSplitGap :=
  k4HeterogeneousSourceBackedSplitWitness_of_literatureK4HeterogeneousSourceBackedSplitAssumptions

/-- Branch-local corrected `k = 4` split data follow directly from the heterogeneous source-backed
package extracted from the broader-source literature assumptions. -/
theorem k4_heterogeneous_split_data_of_literatureK4HeterogeneousSourceBackedSplitAssumptions
    [h : LiteratureK4HeterogeneousSourceBackedSplitAssumptions] :
    ∃ A B CL cU CU : ℝ,
      0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) *
            Real.exp (-A * Real.sqrt (Real.log (N + 2)) + B * Real.log (Real.log (N + 2))))
          =O[Filter.atTop] (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU) := by
  exact k4_mixed_two_sided_profile_of_heterogeneousSourceBackedSplitWitness
    (k4HeterogeneousSourceBackedSplitGap_of_literatureK4HeterogeneousSourceBackedSplitAssumptions
      (h := h))

/-- Gap-layer alias for the current source-backed `k = 5` toy-model split surface. -/
abbrev K5SourceBackedSplitGap : Type := K5SourceBackedSplitWitness

/-- The combined source-facing `k = 5` toy-model literature layer already instantiates the current
honest local `k = 5` split surface. -/
noncomputable def k5SourceBackedSplitGap_of_literatureK5SourceBackedSplitAssumptions
    [h : LiteratureK5SourceBackedSplitAssumptions] :
    K5SourceBackedSplitGap :=
  k5SourceBackedSplitWitness_of_literatureK5SourceBackedSplitAssumptions

/-- Branch-local `k = 5` split data follow directly from the dedicated source-backed split
package extracted from the combined toy-model literature assumptions. -/
theorem k5_split_data_of_literatureK5SourceBackedSplitAssumptions
    [h : LiteratureK5SourceBackedSplitAssumptions] :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  exact k5_mixed_two_sided_profile_of_sourceBackedSplitWitness
    (k5SourceBackedSplitGap_of_literatureK5SourceBackedSplitAssumptions (h := h))

/-- Gap-layer alias for the source-backed tail-family split surface for fixed `k ≥ 6`. -/
abbrev Kge6SourceBackedSplitGap : Type :=
  ∀ ⦃k : ℕ⦄ (hk : 6 ≤ k), Kge6SourceBackedSplitWitness k hk

/-- The combined source-facing `k ≥ 6` tail-family literature layer already instantiates the
source-backed split surface for every fixed `k ≥ 6`. -/
noncomputable def kge6SourceBackedSplitGap_of_literatureKge6SourceBackedSplitAssumptions
    [h : LiteratureKge6SourceBackedSplitAssumptions] :
    Kge6SourceBackedSplitGap :=
  fun _ hk => kge6SourceBackedSplitWitness_of_literatureKge6SourceBackedSplitAssumptions hk

/-- Tail-family `k ≥ 6` split data follow directly from the dedicated source-backed split
package extracted from the combined tail-family literature assumptions. -/
theorem kge6_split_data_of_literatureKge6SourceBackedSplitAssumptions
    [h : LiteratureKge6SourceBackedSplitAssumptions] :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  intro k hk
  exact kge6_mixed_two_sided_profile_of_sourceBackedSplitWitness
    (kge6SourceBackedSplitGap_of_literatureKge6SourceBackedSplitAssumptions (h := h) hk)

/-- Gap-layer alias for the strongest currently source-backed `k = 3` split surface. -/
abbrev K3SourceBackedSplitGap : Type := K3SourceBackedSplitWitness

/-- A source-backed `k = 3` split witness plugs directly into the ordinary split-gap packaging
once the `k = 4` and `k ≥ 5` branches are supplied separately. -/
noncomputable def mainSplitGap_of_k3SourceBackedSplitGap_and_frontierRest
    (hK3 : K3SourceBackedSplitGap)
    [K4UpperProfileWitnessImported] [Kge5UpperProfileWitnessImported]
    [K4LowerProfileWitnessImported] [Kge5LowerProfileWitnessImported] :
    MainSplitGap := by
  letI : K3UpperProfileWitnessImported := ⟨hK3.upper⟩
  letI : K3BehrendLowerProfileWitnessImported := ⟨hK3.lower⟩
  exact mainSplitGap_of_instances

/-- The pivoted Kelley-Meka `β = 1 / 12` literature layer already instantiates the strongest
honest local `k = 3` split surface. -/
noncomputable def k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions
    [h : LiteratureK3OneTwelfthSourceAssumptions] :
    K3SourceBackedSplitGap :=
  k3SourceBackedSplitWitness_of_literatureK3OneTwelfthSourceAssumptions

/-- The honest theorem-level `k = 3` split statement follows from the local source-backed split
package. -/
theorem erdos_142_three_source_backed_split_of_k3SourceBackedSplitGap
    (hK3 : K3SourceBackedSplitGap) :
    Erdos142.erdos_142_three_source_backed_split := by
  exact Erdos142.erdos_142_three_source_backed_split_of_bounds
    hK3.lower.hc hK3.lower.hC hK3.upper.hc hK3.upper.hC
    hK3.lower.hLower
    (by simpa [hK3.upper_beta_eq_one_twelfth] using hK3.upper.hUpper)
    (by
      letI : K3UpperProfileWitnessImported := ⟨hK3.upper⟩
      letI : K3BehrendLowerProfileWitnessImported := ⟨hK3.lower⟩
      convert hK3.hCompatibility using 1
      ext N
      simp [k3_upper_profile,
        erdos_problem_142_explicit_k3_upper_profile_witness_imported,
        hK3.upper_beta_eq_one_twelfth])

/-- The pivoted Kelley-Meka `β = 1 / 12` source layer already yields the strongest honest
theorem-level `k = 3` split statement. -/
theorem erdos_142_three_source_backed_split_of_literatureK3OneTwelfthSourceAssumptions
    [h : LiteratureK3OneTwelfthSourceAssumptions] :
    Erdos142.erdos_142_three_source_backed_split :=
  erdos_142_three_source_backed_split_of_k3SourceBackedSplitGap
    (k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions (h := h))

/-- The optional post-Behrend `β = 1 / 8` import wrapper yields the conjectural theorem-level
`k = 3` split statement. This route is scaffolding only unless a published source-backed theorem
is later audited into the repository. -/
theorem erdos_142_three_source_backed_split_one_eighth_of_literatureK3OneEighthSourceAssumptions
    [h : LiteratureK3OneEighthSourceAssumptions] :
    Erdos142.erdos_142_three_source_backed_split_one_eighth := by
  rcases h.k3_superpolylog_upper_profile_one_eighth with ⟨cU, CU, hcU, hCU, hUpper⟩
  let wU : K3UpperProfileWitness :=
    { β := (1 : ℝ) / 8
      c := cU
      C := CU
      hβ := by norm_num
      hc := hcU
      hC := hCU
      hUpper := hUpper }
  let wL : K3BehrendLowerProfileWitness :=
    k3BehrendLowerProfileWitness_of_literatureRateAssumptions
  letI : K3UpperProfileWitnessImported := ⟨wU⟩
  letI : K3BehrendLowerProfileWitnessImported := ⟨wL⟩
  have hβw : wU.β < (1 : ℝ) / 2 := by
    change (1 : ℝ) / 8 < (1 : ℝ) / 2
    norm_num
  have hβ :
      erdos_problem_142_explicit_k3_upper_profile_witness_imported.β < (1 : ℝ) / 2 := by
    change wU.β < (1 : ℝ) / 2
    exact hβw
  exact Erdos142.erdos_142_three_source_backed_split_one_eighth_of_bounds
    wL.hc wL.hC wU.hc wU.hC
    (by simpa [wL] using wL.hLower)
    (by simpa [wU] using wU.hUpper)
    (by
      have hLowerEq :
          (fun N : ℕ => wL.C * (N : ℝ) * Real.exp (-wL.c * Real.sqrt (Real.log (N + 2)))) =
            k3_behrend_lower_template := by
        funext N
        change
          wL.C * (N : ℝ) * Real.exp (-wL.c * Real.sqrt (Real.log (N + 2))) =
            wL.C * (N : ℝ) * Real.exp (-wL.c * Real.sqrt (Real.log (N + 2)))
        rfl
      have hUpperEq :
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8))) =
            k3_upper_profile := by
        funext N
        change
          CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8)) =
            wU.C * (N : ℝ) * Real.exp (-wU.c * (Real.log (N + 2)) ^ wU.β)
        rw [show wU.C = CU by rfl, show wU.c = cU by rfl, show wU.β = (1 : ℝ) / 8 by rfl]
      rw [hLowerEq, hUpperEq]
      exact k3_behrend_lower_template_dominance_of_beta_lt_half hβ)

/-- Asymmetric split-gap packaging after the source-backed `k = 3` pivot:
`k = 3` is fixed by the honest source-backed split package, while `k = 4` and `k ≥ 5`
still use the ordinary split upper/lower interfaces. -/
structure Problem142K3ResolvedSplitImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4Upper : K4UpperProfileWitnessImported
  k4Lower : K4LowerProfileWitnessImported
  kge5Upper : Kge5UpperProfileWitnessImported
  kge5Lower : Kge5LowerProfileWitnessImported

/-- Active asymmetric split-gap surface: `k = 3` fixed honestly, higher branches still split. -/
abbrev MainK3ResolvedSplitGap : Type := Problem142K3ResolvedSplitImportedWitnessBundle

/-- Package the asymmetric split-gap directly from existing interfaces. -/
def mainK3ResolvedSplitGap_of_instances (hK3 : K3SourceBackedSplitGap)
    [K4UpperProfileWitnessImported] [K4LowerProfileWitnessImported]
    [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] :
    MainK3ResolvedSplitGap :=
  { k3 := hK3
    k4Upper := inferInstance
    k4Lower := inferInstance
    kge5Upper := inferInstance
    kge5Lower := inferInstance }

/-- Upgrade an ordinary split-gap bundle to the asymmetric `k = 3`-resolved split package once
an explicit source-backed `k = 3` witness is supplied. -/
def mainK3ResolvedSplitGap_of_mainSplitGap_and_k3SourceBackedSplitGap
    (hSplit : MainSplitGap) (hK3 : K3SourceBackedSplitGap) :
    MainK3ResolvedSplitGap :=
  { k3 := hK3
    k4Upper := hSplit.upper.k4
    k4Lower := hSplit.lower.k4
    kge5Upper := hSplit.upper.kge5
    kge5Lower := hSplit.lower.kge5 }

/-- Forget the distinguished source-backed `k = 3` packaging and recover the ordinary split-gap
surface. This is the compatibility bridge that keeps existing split-gap results reusable. -/
noncomputable def mainSplitGap_of_mainK3ResolvedSplitGap
    (hGap : MainK3ResolvedSplitGap) :
    MainSplitGap := by
  letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
  letI : K3BehrendLowerProfileWitnessImported := ⟨hGap.k3.lower⟩
  letI : K4UpperProfileWitnessImported := hGap.k4Upper
  letI : K4LowerProfileWitnessImported := hGap.k4Lower
  letI : Kge5UpperProfileWitnessImported := hGap.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hGap.kge5Lower
  exact mainSplitGap_of_instances

/-- All ordinary split-gap consequences remain available from the asymmetric `k = 3`-resolved
split surface. -/
theorem split_gap_data_of_mainK3ResolvedSplitGap
    (hGap : MainK3ResolvedSplitGap) :
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
  exact split_gap_data_of_main_split_gap (mainSplitGap_of_mainK3ResolvedSplitGap hGap)

/-- Asymmetric post-pivot gap packaging:
`k = 3` stays at the honest source-backed split surface, while `k = 4` and `k ≥ 5`
are promoted to full matched-profile witnesses. This is strictly weaker than `MainTheoreticalGap`
and is the natural downstream target after the `k = 3` pivot. -/
structure Problem142K3ResolvedImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4ProfileWitnessImported
  kge5 : Kge5ProfileWitnessImported

/-- Active asymmetric downstream gap surface after resolving `k = 3` only to split strength. -/
abbrev MainK3ResolvedGap : Type := Problem142K3ResolvedImportedWitnessBundle

/-- Any asymmetric post-pivot downstream gap bundle still provides all `k ≥ 3` upper variants. -/
noncomputable def mainUpperGap_of_mainK3ResolvedGap
    (hGap : MainK3ResolvedGap) :
    MainUpperGap := by
  letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
  letI : K4ProfileWitnessImported := hGap.k4
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainUpperGap_of_instances

/-- Consequently, the asymmetric post-pivot downstream gap surface still yields all upper
best-known consequences. -/
theorem upper_variant_of_mainK3ResolvedGap
    (hGap : MainK3ResolvedGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k :=
  upper_variant_of_main_upper_gap (mainUpperGap_of_mainK3ResolvedGap hGap)

/-- Any asymmetric post-pivot downstream gap bundle can be forgotten back to the asymmetric
split surface. This keeps the new interface compatible with ordinary split-gap consequences. -/
noncomputable def mainK3ResolvedSplitGap_of_mainK3ResolvedGap
    (hGap : MainK3ResolvedGap) :
    MainK3ResolvedSplitGap := by
  letI : K4ProfileWitnessImported := hGap.k4
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainK3ResolvedSplitGap_of_instances hGap.k3

/-- Further asymmetric split-gap packaging after the honest `k = 4` pivot:
`k = 3` and `k = 4` are fixed by source-backed split packages, while `k ≥ 5`
still uses the ordinary split upper/lower interfaces. -/
structure Problem142K34ResolvedSplitImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4SourceBackedSplitGap
  kge5Upper : Kge5UpperProfileWitnessImported
  kge5Lower : Kge5LowerProfileWitnessImported

/-- Active asymmetric split-gap surface: `k = 3` and `k = 4` fixed honestly, `k ≥ 5` still split. -/
abbrev MainK34ResolvedSplitGap : Type := Problem142K34ResolvedSplitImportedWitnessBundle

/-- Package the further asymmetric split-gap directly from existing interfaces. -/
def mainK34ResolvedSplitGap_of_instances (hK3 : K3SourceBackedSplitGap) (hK4 : K4SourceBackedSplitGap)
    [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] :
    MainK34ResolvedSplitGap :=
  { k3 := hK3
    k4 := hK4
    kge5Upper := inferInstance
    kge5Lower := inferInstance }

/-- Upgrade the `k = 3`-resolved split surface to the `k = 3,4`-resolved split surface once
an explicit source-backed `k = 4` split witness is supplied. -/
def mainK34ResolvedSplitGap_of_mainK3ResolvedSplitGap_and_k4SourceBackedSplitGap
    (hSplit : MainK3ResolvedSplitGap) (hK4 : K4SourceBackedSplitGap) :
    MainK34ResolvedSplitGap :=
  { k3 := hSplit.k3
    k4 := hK4
    kge5Upper := hSplit.kge5Upper
    kge5Lower := hSplit.kge5Lower }

/-- Upgrade an ordinary split-gap bundle directly to the `k = 3,4`-resolved split surface once
explicit source-backed `k = 3` and `k = 4` split witnesses are supplied. -/
def mainK34ResolvedSplitGap_of_mainSplitGap_and_sourceBackedSplitGaps
    (hSplit : MainSplitGap) (hK3 : K3SourceBackedSplitGap) (hK4 : K4SourceBackedSplitGap) :
    MainK34ResolvedSplitGap :=
  { k3 := hK3
    k4 := hK4
    kge5Upper := hSplit.upper.kge5
    kge5Lower := hSplit.lower.kge5 }

/-- The current literature-side source-backed assumptions already instantiate the active
`k = 3,4`-resolved split surface: `k = 3` via the explicit Kelley-Meka `β = 1/12` route,
`k = 4` via the lower-import split route, and `k ≥ 5` via the inherited split interfaces from
`LiteratureLowerImportAssumptions`. -/
noncomputable def mainK34ResolvedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions] :
    MainK34ResolvedSplitGap := by
  let hK3 := k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions (h := h3)
  let hK4 := k4SourceBackedSplitGap_of_literatureLowerImportAssumptions (h := hLower)
  letI : Kge5UpperProfileWitnessImported :=
    kge5UpperProfileWitnessImported_of_literatureRateAssumptions
      (h := hLower.toLiteratureRateAssumptions)
  letI : Kge5LowerProfileWitnessImported :=
    kge5LowerProfileWitnessImported_of_literatureLowerImportAssumptions
      (h := hLower)
  exact mainK34ResolvedSplitGap_of_instances hK3 hK4

/-- Forget the distinguished source-backed `k = 3,4` packaging and recover the ordinary split-gap
surface. This keeps all split-gap consequences reusable after the `k = 4` pivot. -/
noncomputable def mainSplitGap_of_mainK34ResolvedSplitGap
    (hGap : MainK34ResolvedSplitGap) :
    MainSplitGap := by
  letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
  letI : K3BehrendLowerProfileWitnessImported := ⟨hGap.k3.lower⟩
  letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
  letI : K4LowerProfileWitnessImported := ⟨hGap.k4.lower⟩
  letI : Kge5UpperProfileWitnessImported := hGap.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hGap.kge5Lower
  exact mainSplitGap_of_instances

/-- All ordinary split-gap consequences remain available from the asymmetric `k = 3,4`-resolved
split surface. -/
theorem split_gap_data_of_mainK34ResolvedSplitGap
    (hGap : MainK34ResolvedSplitGap) :
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
  exact split_gap_data_of_main_split_gap (mainSplitGap_of_mainK34ResolvedSplitGap hGap)

/-- All split-gap consequences on the active `k = 3,4`-resolved route follow directly from the
current source-backed literature-side assumption layers. -/
theorem split_gap_data_of_literatureK3OneTwelfth_and_lowerImportAssumptions
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions] :
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
  exact split_gap_data_of_mainK34ResolvedSplitGap
    (mainK34ResolvedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions
      (h3 := h3) (hLower := hLower))

/-- The `k = 3,4`-resolved split surface still yields the earlier `k = 3`-resolved split surface
once the `k = 4` split package is forgotten back to ordinary split witnesses. -/
noncomputable def mainK3ResolvedSplitGap_of_mainK34ResolvedSplitGap
    (hGap : MainK34ResolvedSplitGap) :
    MainK3ResolvedSplitGap := by
  letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
  letI : K4LowerProfileWitnessImported := ⟨hGap.k4.lower⟩
  letI : Kge5UpperProfileWitnessImported := hGap.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hGap.kge5Lower
  exact mainK3ResolvedSplitGap_of_instances hGap.k3

/-- Further asymmetric downstream gap packaging after the honest `k = 4` pivot:
`k = 3` and `k = 4` stay at source-backed split strength, while only `k ≥ 5`
is promoted to matched-profile strength. -/
structure Problem142K34ResolvedImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4SourceBackedSplitGap
  kge5 : Kge5ProfileWitnessImported

/-- Active asymmetric downstream gap surface after resolving `k = 3` and `k = 4`
only to split strength. -/
abbrev MainK34ResolvedGap : Type := Problem142K34ResolvedImportedWitnessBundle

/-- Any `k = 3,4`-resolved downstream gap bundle still provides all `k ≥ 3` upper variants. -/
noncomputable def mainUpperGap_of_mainK34ResolvedGap
    (hGap : MainK34ResolvedGap) :
    MainUpperGap := by
  letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
  letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainUpperGap_of_instances

/-- Consequently, the `k = 3,4`-resolved downstream gap surface still yields all upper
best-known consequences. -/
theorem upper_variant_of_mainK34ResolvedGap
    (hGap : MainK34ResolvedGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k :=
  upper_variant_of_main_upper_gap (mainUpperGap_of_mainK34ResolvedGap hGap)

/-- Any `k = 3,4`-resolved downstream gap bundle can be forgotten back to the corresponding
split surface. This keeps the new interface compatible with ordinary split-gap consequences. -/
noncomputable def mainK34ResolvedSplitGap_of_mainK34ResolvedGap
    (hGap : MainK34ResolvedGap) :
    MainK34ResolvedSplitGap := by
  letI : Kge5ProfileWitnessImported := hGap.kge5
  exact mainK34ResolvedSplitGap_of_instances hGap.k3 hGap.k4

/-- A `k ≥ 6` witness automatically carries the weaker `k ≥ 5` side condition expected by the
legacy `Kge5...` witness families. -/
theorem five_le_of_six_le {k : ℕ} (hk : 6 ≤ k) : 5 ≤ k :=
  Nat.le_trans (by decide : 5 ≤ 6) hk

/-- Tail-family upper witnesses for the remaining `k ≥ 6` branch after isolating the special
source-backed `k = 5` toy model. -/
abbrev Kge6UpperWitnessFamily : Type :=
  ∀ ⦃k : ℕ⦄ (hk : 6 ≤ k), Kge5UpperProfileWitness k (five_le_of_six_le hk)

/-- Tail-family lower witnesses for the remaining `k ≥ 6` branch after isolating the special
source-backed `k = 5` toy model. -/
abbrev Kge6LowerWitnessFamily : Type :=
  ∀ ⦃k : ℕ⦄ (hk : 6 ≤ k), Kge5LowerProfileWitness k (five_le_of_six_le hk)

/-- Tail-family matched-profile witnesses for the remaining `k ≥ 6` frontier. -/
abbrev Kge6ProfileWitnessFamily : Type :=
  ∀ ⦃k : ℕ⦄ (hk : 6 ≤ k), Kge5ProfileWitness k (five_le_of_six_le hk)

/-- Further asymmetric split-gap packaging after the honest `k = 5` pivot:
`k = 3`, `k = 4`, and `k = 5` are fixed by source-backed split packages, while only the
remaining tail `k ≥ 6` still uses the ordinary split upper/lower interface family. -/
structure Problem142K345ResolvedSplitImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4SourceBackedSplitGap
  k5 : K5SourceBackedSplitGap
  kge6Upper : Kge6UpperWitnessFamily
  kge6Lower : Kge6LowerWitnessFamily

/-- Active asymmetric split-gap surface after the `k = 5` pivot:
`k = 3,4,5` are fixed honestly, and only `k ≥ 6` remains split-only. -/
abbrev MainK345ResolvedSplitGap : Type := Problem142K345ResolvedSplitImportedWitnessBundle

/-- Package the `k = 3,4,5` split-resolved surface directly from existing interfaces by
restricting the inherited `k ≥ 5` family to the tail `k ≥ 6`. -/
noncomputable def mainK345ResolvedSplitGap_of_instances
    (hK3 : K3SourceBackedSplitGap) (hK4 : K4SourceBackedSplitGap) (hK5 : K5SourceBackedSplitGap)
    [Kge5UpperProfileWitnessImported] [Kge5LowerProfileWitnessImported] :
    MainK345ResolvedSplitGap :=
  { k3 := hK3
    k4 := hK4
    k5 := hK5
    kge6Upper := by
      intro k hk
      simpa using
        (erdos_problem_142_explicit_kge5_upper_profile_witness_imported (five_le_of_six_le hk))
    kge6Lower := by
      intro k hk
      simpa using
        (erdos_problem_142_kge5_lower_profile_witness_imported (five_le_of_six_le hk)) }

/-- Upgrade the `k = 3,4`-resolved split surface to the `k = 3,4,5`-resolved split surface once
the explicit source-backed `k = 5` split package is supplied. -/
noncomputable def mainK345ResolvedSplitGap_of_mainK34ResolvedSplitGap_and_k5SourceBackedSplitGap
    (hSplit : MainK34ResolvedSplitGap) (hK5 : K5SourceBackedSplitGap) :
    MainK345ResolvedSplitGap := by
  letI : Kge5UpperProfileWitnessImported := hSplit.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hSplit.kge5Lower
  exact mainK345ResolvedSplitGap_of_instances hSplit.k3 hSplit.k4 hK5

/-- The current literature-side source-backed assumptions already instantiate the active
`k = 3,4,5`-resolved split surface: `k = 3` via the explicit Kelley-Meka `β = 1/12` route,
`k = 4` via the lower-import split route, `k = 5` via the new mixed source-backed toy model,
and only the tail `k ≥ 6` inherited from the remaining generic split interfaces. -/
noncomputable def
    mainK345ResolvedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions_and_k5SourceBackedSplitAssumptions
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] :
    MainK345ResolvedSplitGap := by
  let hK3 := k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions (h := h3)
  let hK4 := k4SourceBackedSplitGap_of_literatureLowerImportAssumptions (h := hLower)
  let hK5 := k5SourceBackedSplitGap_of_literatureK5SourceBackedSplitAssumptions (h := h5)
  letI : Kge5UpperProfileWitnessImported :=
    kge5UpperProfileWitnessImported_of_literatureRateAssumptions
      (h := hLower.toLiteratureRateAssumptions)
  letI : Kge5LowerProfileWitnessImported :=
    kge5LowerProfileWitnessImported_of_literatureLowerImportAssumptions
      (h := hLower)
  exact mainK345ResolvedSplitGap_of_instances hK3 hK4 hK5

/-- Upper variants on the active `k = 3,4,5`-resolved split route: the special `k = 5`
stretched-exponential source-backed upper witness is used at `k = 5`, and only the tail
`k ≥ 6` still uses the legacy iterated-log upper family. -/
theorem upper_variant_of_mainK345ResolvedSplitGap
    (hGap : MainK345ResolvedSplitGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k := by omega
  rcases hk_cases with rfl | rfl | rfl | hk6
  · letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
    exact upper_variant_three_of_upper_profile_witness
  · letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
    exact upper_variant_four_of_upper_profile_witness
  · letI : K5UpperStretchedexpProfileWitnessImported := ⟨hGap.k5.upper⟩
    exact upper_variant_five_of_stretchedexp_upper_profile_witness
  · let wU : Kge5UpperProfileWitness k (five_le_of_six_le hk6) := hGap.kge6Upper hk6
    refine ⟨fun N : ℕ => wU.C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ wU.c, ?_⟩
    simpa [wU] using wU.hUpper

/-- The active `k = 3,4,5`-resolved split route carries the first-class source-backed `k = 5`
mixed split data without re-routing through the obsolete iterated-log `k ≥ 5` placeholder. -/
theorem k5_split_data_of_mainK345ResolvedSplitGap
    (hGap : MainK345ResolvedSplitGap) :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  exact k5_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k5

/-- The remaining tail `k ≥ 6` still carries the inherited iterated-log split data from the
legacy `Kge5...` family, now explicitly restricted away from the special `k = 5` branch. -/
theorem kge6_split_data_of_mainK345ResolvedSplitGap
    (hGap : MainK345ResolvedSplitGap) :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cL) =O[Filter.atTop]
          (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ cU) := by
  intro k hk
  let wL : Kge5LowerProfileWitness k (five_le_of_six_le hk) := hGap.kge6Lower hk
  let wU : Kge5UpperProfileWitness k (five_le_of_six_le hk) := hGap.kge6Upper hk
  exact ⟨wL.c, wL.C, wU.c, wU.C, wL.hc, wL.hC, wU.hc, wU.hC, wL.hLower, wU.hUpper⟩

/-- Further asymmetric downstream gap packaging after the honest `k = 5` pivot:
`k = 3`, `k = 4`, and `k = 5` stay at source-backed split strength, while only `k ≥ 6`
is promoted to matched-profile strength. -/
structure Problem142K345ResolvedImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4SourceBackedSplitGap
  k5 : K5SourceBackedSplitGap
  kge6 : Kge6ProfileWitnessFamily

/-- Active asymmetric downstream gap surface after resolving `k = 3`, `k = 4`, and `k = 5`
only to split strength. -/
abbrev MainK345ResolvedGap : Type := Problem142K345ResolvedImportedWitnessBundle

/-- Any `k = 3,4,5`-resolved downstream gap bundle still provides all `k ≥ 3` upper variants. -/
theorem upper_variant_of_mainK345ResolvedGap
    (hGap : MainK345ResolvedGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k := by omega
  rcases hk_cases with rfl | rfl | rfl | hk6
  · letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
    exact upper_variant_three_of_upper_profile_witness
  · letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
    exact upper_variant_four_of_upper_profile_witness
  · letI : K5UpperStretchedexpProfileWitnessImported := ⟨hGap.k5.upper⟩
    exact upper_variant_five_of_stretchedexp_upper_profile_witness
  · let w : Kge5ProfileWitness k (five_le_of_six_le hk6) := hGap.kge6 hk6
    refine ⟨fun N : ℕ => w.C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ w.c, ?_⟩
    simpa [w] using w.hUpper

/-- Legacy local all-branches source-backed split packaging after the tail-family pivot:
`k = 3`, `k = 4`, `k = 5`, and every fixed `k ≥ 6` are all represented by explicit
source-backed split witnesses, but the `k = 4` slot still uses the older polylog-lower
placeholder. -/
structure Problem142AllSourceBackedSplitImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4SourceBackedSplitGap
  k5 : K5SourceBackedSplitGap
  kge6 : Kge6SourceBackedSplitGap

/-- Legacy local all-branches split target before the March 9, 2026 `k = 4` public cutover. -/
abbrev MainAllSourceBackedSplitGap : Type := Problem142AllSourceBackedSplitImportedWitnessBundle

/-- The current source-backed literature-side assumption layers already instantiate the practical
all-branches split target once the tail-family `k ≥ 6` source-backed assumptions are supplied. -/
noncomputable def
    mainAllSourceBackedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions_and_sourceBackedTail
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    MainAllSourceBackedSplitGap :=
  { k3 := k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions (h := h3)
    k4 := k4SourceBackedSplitGap_of_literatureLowerImportAssumptions (h := hLower)
    k5 := k5SourceBackedSplitGap_of_literatureK5SourceBackedSplitAssumptions (h := h5)
    kge6 := kge6SourceBackedSplitGap_of_literatureKge6SourceBackedSplitAssumptions (h := h6) }

/-- The practical all-branches source-backed split target still yields all upper variants. -/
theorem upper_variant_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k := by omega
  rcases hk_cases with rfl | rfl | rfl | hk6
  · letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
    exact upper_variant_three_of_upper_profile_witness
  · letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
    exact upper_variant_four_of_upper_profile_witness
  · letI : K5UpperStretchedexpProfileWitnessImported := ⟨hGap.k5.upper⟩
    exact upper_variant_five_of_stretchedexp_upper_profile_witness
  · letI : Kge6UpperStretchedexpProfileWitnessImported :=
        { kge6_upper_stretchedexp_profile_witness := fun _ hk => (hGap.kge6 hk).upper }
    exact upper_variant_ge_six_of_stretchedexp_upper_profile_witness hk6

/-- The practical all-branches split target carries the explicit source-backed `k = 5` split
data. -/
theorem k5_split_data_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  exact k5_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k5

/-- The practical all-branches split target carries the explicit source-backed tail-family split
data for every fixed `k ≥ 6`. -/
theorem kge6_split_data_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  intro k hk
  exact kge6_mixed_two_sided_profile_of_sourceBackedSplitWitness (hGap.kge6 hk)

/-- Named mathematical endpoint for the legacy local all-branches split route:
all upper variants together with the branchwise source-backed split data on the correct scale for
each branch. This packages the older local route as one reusable object rather than a large
conjunction. -/
structure Problem142AllSourceBackedSplitData where
  upper : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k
  k3 :
    ∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))
  k4 :
    ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)
  k5 :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))
  kge6 :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))

/-- Build the named all-branches source-backed split endpoint from the practical gap witness. -/
noncomputable def mainAllSourceBackedSplitData_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    Problem142AllSourceBackedSplitData :=
  { upper := upper_variant_of_mainAllSourceBackedSplitGap hGap
    k3 := k3_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k3
    k4 := k4_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k4
    k5 := k5_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k5
    kge6 := kge6_split_data_of_mainAllSourceBackedSplitGap hGap }

/-- Export the internal practical endpoint to the statement-level theorem surface declared in
`Problem142.lean`. This keeps the honest split route usable without depending on gap-layer
implementation details. -/
noncomputable def sourceBackedSplitRoute_of_mainAllSourceBackedSplitData
    (hData : Problem142AllSourceBackedSplitData) :
    Erdos142.SourceBackedSplitRoute :=
  { upper := hData.upper
    k3 := hData.k3
    k4 := hData.k4
    k5 := hData.k5
    kge6 := hData.kge6 }

/-- Direct export from the practical all-branches split gap to the statement-level split route. -/
noncomputable def sourceBackedSplitRoute_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    Erdos142.SourceBackedSplitRoute :=
  sourceBackedSplitRoute_of_mainAllSourceBackedSplitData
    (mainAllSourceBackedSplitData_of_mainAllSourceBackedSplitGap hGap)

/-- The practical all-branches split gap already yields the honest theorem-level endpoint
`Erdos142.erdos_142_source_backed_split`. -/
theorem erdos_142_source_backed_split_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    Erdos142.erdos_142_source_backed_split :=
  Erdos142.erdos_142_source_backed_split_of_route
    (sourceBackedSplitRoute_of_mainAllSourceBackedSplitGap hGap)

/-- Aggregate mathematical consequence of the practical all-branches source-backed split route:
all upper variants are available, and each branch carries explicit source-backed split data on the
correct scale for that branch. -/
theorem all_source_backed_split_data_of_mainAllSourceBackedSplitGap
    (hGap : MainAllSourceBackedSplitGap) :
    (∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k) ∧
    (∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))) ∧
    (∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)) ∧
    (∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) ∧
    (∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) := by
  let hData := mainAllSourceBackedSplitData_of_mainAllSourceBackedSplitGap hGap
  exact ⟨hData.upper, hData.k3, hData.k4, hData.k5, hData.kge6⟩

/-- The current legacy local literature-side assumption layers already instantiate the named
all-branches source-backed split endpoint on the older local route. -/
noncomputable def mainAllSourceBackedSplitData_of_literature_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Problem142AllSourceBackedSplitData :=
  mainAllSourceBackedSplitData_of_mainAllSourceBackedSplitGap
    (mainAllSourceBackedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions_and_sourceBackedTail
      (h3 := h3) (hLower := hLower) (h5 := h5) (h6 := h6))

/-- Statement-level theorem surface for the current honest route:
the source-backed literature assumptions imply the split-strength route packaged in
`Erdos142.SourceBackedSplitRoute`. -/
noncomputable def sourceBackedSplitRoute_of_literature_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Erdos142.SourceBackedSplitRoute :=
  sourceBackedSplitRoute_of_mainAllSourceBackedSplitData
    (mainAllSourceBackedSplitData_of_literature_sourceBacked_route
      (h3 := h3) (hLower := hLower) (h5 := h5) (h6 := h6))

/-- The current source-backed literature-side assumptions directly realize the honest theorem-level
split statement `Erdos142.erdos_142_source_backed_split`. -/
theorem erdos_142_source_backed_split_of_literature_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Erdos142.erdos_142_source_backed_split :=
  Erdos142.erdos_142_source_backed_split_of_route
    (sourceBackedSplitRoute_of_literature_sourceBacked_route
      (h3 := h3) (hLower := hLower) (h5 := h5) (h6 := h6))

/-- Gap-layer alias for the stabilized post-critic negative `k = 3` route. -/
abbrev K3NegativeRouteStable : Prop := Erdos142.erdos_142_three_negative_route_stable

/-- The stabilized post-critic negative `k = 3` route already holds in this repository. -/
theorem k3_negative_route_stable : K3NegativeRouteStable :=
  Erdos142.erdos_142_three_negative_route_stable_true

/-- The current source-backed literature-side assumption layers already instantiate the full
aggregate split-data theorem on the practical route. -/
theorem all_source_backed_split_data_of_literature_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions] [hLower : LiteratureLowerImportAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    (∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k) ∧
    (∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))) ∧
    (∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[Filter.atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)) ∧
    (∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) ∧
    (∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) := by
  exact all_source_backed_split_data_of_mainAllSourceBackedSplitGap
    (mainAllSourceBackedSplitGap_of_literatureK3OneTwelfth_and_lowerImportAssumptions_and_sourceBackedTail
      (h3 := h3) (hLower := hLower) (h5 := h5) (h6 := h6))

/-- Corrected broader-source all-branches split packaging after the March 9, 2026 `k = 4`
public cutover: `k = 3`, corrected `k = 4`, `k = 5`, and every fixed `k ≥ 6` are all
represented by explicit source-backed split witnesses. -/
structure Problem142AllHeterogeneousSourceBackedSplitImportedWitnessBundle where
  k3 : K3SourceBackedSplitGap
  k4 : K4HeterogeneousSourceBackedSplitGap
  k5 : K5SourceBackedSplitGap
  kge6 : Kge6SourceBackedSplitGap

/-- Canonical broader-source practical target after the March 9, 2026 `k = 4` cutover. -/
abbrev MainAllHeterogeneousSourceBackedSplitGap : Type :=
  Problem142AllHeterogeneousSourceBackedSplitImportedWitnessBundle

/-- The current broader-source literature-side assumption layers already instantiate the canonical
all-branches split target once the corrected heterogeneous `k = 4` layer is supplied. -/
noncomputable def
    mainAllHeterogeneousSourceBackedSplitGap_of_literatureK3OneTwelfth_and_k4HeterogeneousSourceBackedSplitAssumptions_and_sourceBackedTail
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    MainAllHeterogeneousSourceBackedSplitGap :=
  { k3 := k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions (h := h3)
    k4 :=
      k4HeterogeneousSourceBackedSplitGap_of_literatureK4HeterogeneousSourceBackedSplitAssumptions
        (h := h4)
    k5 := k5SourceBackedSplitGap_of_literatureK5SourceBackedSplitAssumptions (h := h5)
    kge6 := kge6SourceBackedSplitGap_of_literatureKge6SourceBackedSplitAssumptions (h := h6) }

/-- The canonical broader-source all-branches split target still yields all upper variants. -/
theorem upper_variant_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k := by
  intro k hk
  have hk_cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k := by omega
  rcases hk_cases with rfl | rfl | rfl | hk6
  · letI : K3UpperProfileWitnessImported := ⟨hGap.k3.upper⟩
    exact upper_variant_three_of_upper_profile_witness
  · letI : K4UpperProfileWitnessImported := ⟨hGap.k4.upper⟩
    exact upper_variant_four_of_upper_profile_witness
  · letI : K5UpperStretchedexpProfileWitnessImported := ⟨hGap.k5.upper⟩
    exact upper_variant_five_of_stretchedexp_upper_profile_witness
  · letI : Kge6UpperStretchedexpProfileWitnessImported :=
        { kge6_upper_stretchedexp_profile_witness := fun _ hk => (hGap.kge6 hk).upper }
    exact upper_variant_ge_six_of_stretchedexp_upper_profile_witness hk6

/-- The canonical broader-source practical route carries the corrected heterogeneous `k = 4`
split data. -/
theorem k4_heterogeneous_split_data_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    ∃ A B CL cU CU : ℝ,
      0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) *
            Real.exp (-A * Real.sqrt (Real.log (N + 2)) + B * Real.log (Real.log (N + 2))))
          =O[Filter.atTop] (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU) := by
  exact k4_mixed_two_sided_profile_of_heterogeneousSourceBackedSplitWitness hGap.k4

/-- The canonical broader-source all-branches split target carries the explicit source-backed
`k = 5` split data. -/
theorem k5_split_data_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  exact k5_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k5

/-- The canonical broader-source all-branches split target carries the explicit source-backed
tail-family split data for every fixed `k ≥ 6`. -/
theorem kge6_split_data_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) := by
  intro k hk
  exact kge6_mixed_two_sided_profile_of_sourceBackedSplitWitness (hGap.kge6 hk)

/-- Named mathematical endpoint for the canonical broader-source practical route:
all upper variants together with the branchwise source-backed split data on the correct scale for
each branch, now with the corrected heterogeneous `k = 4` component. -/
structure Problem142AllHeterogeneousSourceBackedSplitData where
  upper : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k
  k3 :
    ∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))
  k4 :
    ∃ A B CL cU CU : ℝ,
      0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) *
            Real.exp (-A * Real.sqrt (Real.log (N + 2)) + B * Real.log (Real.log (N + 2))))
          =O[Filter.atTop] (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)
  k5 :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))
  kge6 :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))

/-- Build the canonical broader-source practical endpoint from the corrected gap witness. -/
noncomputable def mainAllHeterogeneousSourceBackedSplitData_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    Problem142AllHeterogeneousSourceBackedSplitData :=
  { upper := upper_variant_of_mainAllHeterogeneousSourceBackedSplitGap hGap
    k3 := k3_mixed_two_sided_profile_of_sourceBackedSplitWitness hGap.k3
    k4 := k4_mixed_two_sided_profile_of_heterogeneousSourceBackedSplitWitness hGap.k4
    k5 := k5_split_data_of_mainAllHeterogeneousSourceBackedSplitGap hGap
    kge6 := kge6_split_data_of_mainAllHeterogeneousSourceBackedSplitGap hGap }

/-- Export the canonical broader-source practical endpoint to the corrected statement-level theorem
surface declared in `Problem142.lean`. -/
noncomputable def heterogeneousSourceBackedSplitRoute_of_mainAllHeterogeneousSourceBackedSplitData
    (hData : Problem142AllHeterogeneousSourceBackedSplitData) :
    Erdos142.HeterogeneousSourceBackedSplitRoute :=
  { upper := hData.upper
    k3 := hData.k3
    k4 := hData.k4
    k5 := hData.k5
    kge6 := hData.kge6 }

/-- Direct export from the corrected broader-source practical gap to the corrected statement-level
split route. -/
noncomputable def heterogeneousSourceBackedSplitRoute_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    Erdos142.HeterogeneousSourceBackedSplitRoute :=
  heterogeneousSourceBackedSplitRoute_of_mainAllHeterogeneousSourceBackedSplitData
    (mainAllHeterogeneousSourceBackedSplitData_of_mainAllHeterogeneousSourceBackedSplitGap hGap)

/-- The corrected broader-source practical gap already yields the canonical theorem-level endpoint
`Erdos142.erdos_142_heterogeneous_source_backed_split`. -/
theorem erdos_142_heterogeneous_source_backed_split_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    Erdos142.erdos_142_heterogeneous_source_backed_split :=
  Erdos142.erdos_142_heterogeneous_source_backed_split_of_route
    (heterogeneousSourceBackedSplitRoute_of_mainAllHeterogeneousSourceBackedSplitGap hGap)

/-- Aggregate mathematical consequence of the corrected broader-source practical route:
all upper variants are available, and each branch carries explicit source-backed split data on the
correct scale for that branch. -/
theorem all_heterogeneous_source_backed_split_data_of_mainAllHeterogeneousSourceBackedSplitGap
    (hGap : MainAllHeterogeneousSourceBackedSplitGap) :
    (∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k) ∧
    (∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))) ∧
    (∃ A B CL cU CU : ℝ,
      0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) *
            Real.exp (-A * Real.sqrt (Real.log (N + 2)) + B * Real.log (Real.log (N + 2))))
          =O[Filter.atTop] (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)) ∧
    (∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) ∧
    (∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[Filter.atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))) := by
  let hData := mainAllHeterogeneousSourceBackedSplitData_of_mainAllHeterogeneousSourceBackedSplitGap hGap
  exact ⟨hData.upper, hData.k3, hData.k4, hData.k5, hData.kge6⟩

/-- The current broader-source literature-side assumption layers already instantiate the named
all-branches split endpoint on the corrected practical route. -/
noncomputable def mainAllHeterogeneousSourceBackedSplitData_of_literature_heterogeneous_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Problem142AllHeterogeneousSourceBackedSplitData :=
  mainAllHeterogeneousSourceBackedSplitData_of_mainAllHeterogeneousSourceBackedSplitGap
    (mainAllHeterogeneousSourceBackedSplitGap_of_literatureK3OneTwelfth_and_k4HeterogeneousSourceBackedSplitAssumptions_and_sourceBackedTail
      (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6))

/-- Statement-level theorem surface for the corrected practical route:
the broader-source literature assumptions imply the heterogeneous split-strength route packaged in
`Erdos142.HeterogeneousSourceBackedSplitRoute`. -/
noncomputable def heterogeneousSourceBackedSplitRoute_of_literature_heterogeneous_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Erdos142.HeterogeneousSourceBackedSplitRoute :=
  heterogeneousSourceBackedSplitRoute_of_mainAllHeterogeneousSourceBackedSplitData
    (mainAllHeterogeneousSourceBackedSplitData_of_literature_heterogeneous_sourceBacked_route
      (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6))

/-- The current broader-source literature-side assumptions directly realize the corrected
theorem-level split statement `Erdos142.erdos_142_heterogeneous_source_backed_split`. -/
theorem erdos_142_heterogeneous_source_backed_split_of_literature_heterogeneous_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Erdos142.erdos_142_heterogeneous_source_backed_split :=
  Erdos142.erdos_142_heterogeneous_source_backed_split_of_route
    (heterogeneousSourceBackedSplitRoute_of_literature_heterogeneous_sourceBacked_route
      (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6))

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

/-- Tail-only coupling target family after isolating the special source-backed `k = 5` toy model:
recover matched `Kge5ProfileWitness` only for the remaining `k ≥ 6` branch. -/
abbrev CouplingTargetKge6 : Type :=
  ∀ ⦃k : ℕ⦄ (hk : 6 ≤ k),
    Kge5UpperProfileWitness k (five_le_of_six_le hk) →
      Kge5LowerProfileWitness k (five_le_of_six_le hk) →
        Kge5ProfileWitness k (five_le_of_six_le hk)

/-- Remaining coupling-assumption layer after fixing `k = 3` honestly:
only the `k = 4` and `k ≥ 5` branches remain unresolved. -/
structure K3ResolvedSplitGapToMainK3ResolvedGapAssumptions where
  k4_profile_witness_of_split : CouplingTargetK4
  kge5_profile_witness_of_split : CouplingTargetKge5

/-- Under the asymmetric post-pivot assumptions, the `k = 3`-resolved split gap can be promoted
to the corresponding asymmetric downstream gap surface. -/
noncomputable def mainK3ResolvedGap_of_mainK3ResolvedSplitGap_and_assumptions
    (hSplit : MainK3ResolvedSplitGap)
    (hCoupling : K3ResolvedSplitGapToMainK3ResolvedGapAssumptions) :
    MainK3ResolvedGap := by
  letI : K4UpperProfileWitnessImported := hSplit.k4Upper
  letI : K4LowerProfileWitnessImported := hSplit.k4Lower
  letI : Kge5UpperProfileWitnessImported := hSplit.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hSplit.kge5Lower
  refine
    { k3 := hSplit.k3
      k4 := { k4_profile_witness := hCoupling.k4_profile_witness_of_split }
      kge5 := by
        refine { kge5_profile_witness := ?_ }
        intro k hk
        exact hCoupling.kge5_profile_witness_of_split hk }

/-- Minimal consumer-side replacement for the old uniform coupling theorem:
take an ordinary split-gap bundle, replace only the `k = 3` branch by the honest source-backed
split package, and promote the remaining higher branches under their coupling assumptions. -/
noncomputable def mainK3ResolvedGap_of_mainSplitGap_and_k3SourceBackedSplitGap_and_assumptions
    (hSplit : MainSplitGap) (hK3 : K3SourceBackedSplitGap)
    (hCoupling : K3ResolvedSplitGapToMainK3ResolvedGapAssumptions) :
    MainK3ResolvedGap :=
  mainK3ResolvedGap_of_mainK3ResolvedSplitGap_and_assumptions
    (mainK3ResolvedSplitGap_of_mainSplitGap_and_k3SourceBackedSplitGap hSplit hK3)
    hCoupling

/-- Remaining coupling-assumption layer after fixing `k = 3` and `k = 4` honestly:
only the `k ≥ 5` branch remains unresolved. -/
structure K34ResolvedSplitGapToMainK34ResolvedGapAssumptions where
  kge5_profile_witness_of_split : CouplingTargetKge5

/-- Under the further asymmetric post-pivot assumptions, the `k = 3,4`-resolved split gap can be
promoted to the corresponding downstream gap surface. -/
noncomputable def mainK34ResolvedGap_of_mainK34ResolvedSplitGap_and_assumptions
    (hSplit : MainK34ResolvedSplitGap)
    (hCoupling : K34ResolvedSplitGapToMainK34ResolvedGapAssumptions) :
    MainK34ResolvedGap := by
  letI : Kge5UpperProfileWitnessImported := hSplit.kge5Upper
  letI : Kge5LowerProfileWitnessImported := hSplit.kge5Lower
  refine
    { k3 := hSplit.k3
      k4 := hSplit.k4
      kge5 := by
        refine { kge5_profile_witness := ?_ }
        intro k hk
        exact hCoupling.kge5_profile_witness_of_split hk }

/-- Minimal consumer-side replacement after the `k = 4` pivot:
take an ordinary split-gap bundle, replace the `k = 3` and `k = 4` branches by the honest
source-backed split packages, and promote only the `k ≥ 5` branch under its coupling assumption. -/
noncomputable def mainK34ResolvedGap_of_mainSplitGap_and_sourceBackedSplitGaps_and_assumptions
    (hSplit : MainSplitGap) (hK3 : K3SourceBackedSplitGap) (hK4 : K4SourceBackedSplitGap)
    (hCoupling : K34ResolvedSplitGapToMainK34ResolvedGapAssumptions) :
    MainK34ResolvedGap :=
  mainK34ResolvedGap_of_mainK34ResolvedSplitGap_and_assumptions
    (mainK34ResolvedSplitGap_of_mainSplitGap_and_sourceBackedSplitGaps hSplit hK3 hK4)
    hCoupling

/-- Remaining coupling-assumption layer after fixing `k = 3`, `k = 4`, and `k = 5` honestly:
only the tail `k ≥ 6` remains unresolved. -/
structure K345ResolvedSplitGapToMainK345ResolvedGapAssumptions where
  kge6_profile_witness_of_split : CouplingTargetKge6

/-- Under the further asymmetric post-pivot assumptions, the `k = 3,4,5`-resolved split gap can
be promoted to the corresponding downstream gap surface. -/
noncomputable def mainK345ResolvedGap_of_mainK345ResolvedSplitGap_and_assumptions
    (hSplit : MainK345ResolvedSplitGap)
    (hCoupling : K345ResolvedSplitGapToMainK345ResolvedGapAssumptions) :
    MainK345ResolvedGap :=
  { k3 := hSplit.k3
    k4 := hSplit.k4
    k5 := hSplit.k5
    kge6 := by
      intro k hk
      exact hCoupling.kge6_profile_witness_of_split hk (hSplit.kge6Upper hk) (hSplit.kge6Lower hk) }

/-- Minimal coupling-assumption layer needed to reconstruct the strong full-gap witnesses from
the split upper/lower interface layers. -/
structure SplitGapToMainTheoreticalGapAssumptions where
  k3_profile_witness_of_split : CouplingTargetK3
  k4_profile_witness_of_split : CouplingTargetK4
  kge5_profile_witness_of_split : CouplingTargetKge5

/-- Frontier axiom placeholders for unresolved split-to-full coupling:
`k = 3`, `k = 4`, and `k ≥ 5` branch recovery still lacks direct derivations from current local
literature assumptions, so these are kept as explicit temporary assumptions. -/
axiom splitGap_k3_upper_exponent_gt_half_frontier :
  import_targets.k3_upper_exponent_gt_half_target

theorem splitGap_k3_profile_dominance_frontier :
    import_targets.split_gap_k3_profile_dominance_target :=
  import_targets.split_gap_k3_profile_dominance_target_of_beta_gt_half
    splitGap_k3_upper_exponent_gt_half_frontier

axiom splitGap_k4_profile_dominance_frontier :
  import_targets.split_gap_k4_profile_dominance_target

axiom splitGap_kge5_profile_dominance_frontier :
  import_targets.split_gap_kge5_profile_dominance_target

/-- Named off-path matched-profile frontier package:
this is the stronger conjectural route that would upgrade the honest split data to full matched
profiles. It is kept separate from the practical source-backed split endpoint. -/
structure Problem142MatchedProfileFrontier where
  k3_upper_exponent_gt_half :
    import_targets.k3_upper_exponent_gt_half_target
  k4_profile_dominance :
    import_targets.split_gap_k4_profile_dominance_target
  kge5_profile_dominance :
    import_targets.split_gap_kge5_profile_dominance_target

/-- The current explicit axiom debt instantiates the named off-path matched-profile frontier
package. -/
noncomputable def matchedProfileFrontier_axiomDebt :
    Problem142MatchedProfileFrontier :=
  { k3_upper_exponent_gt_half := splitGap_k3_upper_exponent_gt_half_frontier
    k4_profile_dominance := splitGap_k4_profile_dominance_frontier
    kge5_profile_dominance := by
      intro _ _ k hk
      exact @splitGap_kge5_profile_dominance_frontier _ _ k hk }

/-- Proposition-level surface asserting that the named off-path matched-profile frontier is
realized. -/
abbrev MatchedProfileFrontierExists : Prop := Nonempty Problem142MatchedProfileFrontier

/-- The current explicit frontier axiom debt already realizes the named matched-profile frontier
package. -/
theorem matchedProfileFrontier_exists : MatchedProfileFrontierExists :=
  ⟨matchedProfileFrontier_axiomDebt⟩

/-- Canonical package for the current repository research state:
the corrected broader-source practical split route, the stabilized post-critic negative `k = 3`
route, and the separate off-path matched-profile frontier package. -/
structure Problem142CurrentResearchStatus where
  practical : Erdos142.erdos_142_heterogeneous_source_backed_split
  k3_negative : K3NegativeRouteStable
  frontier : Problem142MatchedProfileFrontier

/-- The current repository state packaged as one named object. -/
noncomputable def currentResearchStatus_of_literature_heterogeneous_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    Problem142CurrentResearchStatus :=
  { practical := erdos_142_heterogeneous_source_backed_split_of_literature_heterogeneous_sourceBacked_route
      (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6)
    k3_negative := k3_negative_route_stable
    frontier := matchedProfileFrontier_axiomDebt }

/-- Proposition-level surface asserting that the canonical current-status package is realized. -/
abbrev CurrentResearchStatusExists : Prop := Nonempty Problem142CurrentResearchStatus

/-- The current source-backed literature assumptions already realize the canonical current-status
package. -/
theorem currentResearchStatus_exists_of_literature_heterogeneous_sourceBacked_route
    [h3 : LiteratureK3OneTwelfthSourceAssumptions]
    [h4 : LiteratureK4HeterogeneousSourceBackedSplitAssumptions]
    [h5 : LiteratureK5SourceBackedSplitAssumptions] [h6 : LiteratureKge6SourceBackedSplitAssumptions] :
    CurrentResearchStatusExists :=
  ⟨currentResearchStatus_of_literature_heterogeneous_sourceBacked_route
    (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6)⟩

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
  change k3_upper_profile =O[Filter.atTop] (fun N => (r 3 N : ℝ))
  simpa [k3_behrend_lower_template, wL] using (hDom).trans wL.hLower

noncomputable def splitGap_k3_coupling_frontier : CouplingTargetK3 :=
  splitGap_k3_coupling_target_of_profile_dominance_target
    splitGap_k3_profile_dominance_frontier

/-- The `k = 3` coupling target is already derivable from the strengthened literature-side
exponent hypothesis `β > 1 / 2`; this removes `k = 3` from the frontier once that import layer
is available. -/
noncomputable def splitGap_k3_coupling_target_of_literatureK3ExponentGtHalfAssumptions
    [LiteratureK3ExponentGtHalfAssumptions] :
    import_targets.split_gap_k3_coupling_target :=
  splitGap_k3_coupling_target_of_profile_dominance_target
    split_gap_k3_profile_dominance_target_of_literatureK3ExponentGtHalfAssumptions

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

/-- The current frontier axioms already realize a concrete split-to-full coupling package. -/
theorem splitGapToMainTheoreticalGapAssumptions_exists_of_frontier :
    Nonempty SplitGapToMainTheoreticalGapAssumptions :=
  ⟨splitGapToMainTheoreticalGapAssumptions_frontier⟩

/-- Convert the named off-path matched-profile frontier package into the corresponding coupling
assumptions. This is the canonical bridge from the conjectural frontier route to the strong full
matched-profile route. -/
noncomputable def splitGapToMainTheoreticalGapAssumptions_of_matchedProfileFrontier
    (hFrontier : Problem142MatchedProfileFrontier) :
    SplitGapToMainTheoreticalGapAssumptions :=
  { k3_profile_witness_of_split :=
      splitGap_k3_coupling_target_of_profile_dominance_target
        (import_targets.split_gap_k3_profile_dominance_target_of_beta_gt_half
          hFrontier.k3_upper_exponent_gt_half)
    k4_profile_witness_of_split :=
      splitGap_k4_coupling_target_of_profile_dominance_target
        hFrontier.k4_profile_dominance
    kge5_profile_witness_of_split := by
      intro _ _ k hk
      exact
        splitGap_kge5_coupling_target_of_profile_dominance_target
          (by
            intro _ _ k hk
            exact @hFrontier.kge5_profile_dominance _ _ k hk) hk }

/-- Proposition-level surface asserting that a named matched-profile frontier package determines
concrete split-to-full coupling assumptions. -/
abbrev SplitGapToMainTheoreticalGapAssumptionsExists : Prop :=
  Nonempty SplitGapToMainTheoreticalGapAssumptions

/-- Any named off-path matched-profile frontier package canonically yields a concrete split-to-full
coupling package. -/
theorem splitGapToMainTheoreticalGapAssumptions_exists_of_matchedProfileFrontier
    (hFrontier : Problem142MatchedProfileFrontier) :
    SplitGapToMainTheoreticalGapAssumptionsExists :=
  ⟨splitGapToMainTheoreticalGapAssumptions_of_matchedProfileFrontier hFrontier⟩

/-- Mixed replacement package: once the literature-side `k = 3` exponent threshold is imported,
the remaining explicit frontier debt is only in the `k = 4` and `k ≥ 5` dominance branches. -/
noncomputable def splitGapToMainTheoreticalGapAssumptions_of_literatureK3ExponentGtHalf_frontierRest
    [LiteratureK3ExponentGtHalfAssumptions] :
    SplitGapToMainTheoreticalGapAssumptions :=
  { k3_profile_witness_of_split :=
      splitGap_k3_coupling_target_of_literatureK3ExponentGtHalfAssumptions
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

/-- Proposition-level surface asserting that the full matched-profile gap object is realized. -/
abbrev MainTheoreticalGapExists : Prop := Nonempty MainTheoreticalGap

/-- Explicit coupling assumptions already realize the full matched-profile gap object. -/
theorem mainTheoreticalGap_exists_of_mainSplitGap_and_assumptions
    (hSplit : MainSplitGap) (hCoupling : SplitGapToMainTheoreticalGapAssumptions) :
    MainTheoreticalGapExists :=
  ⟨mainTheoreticalGap_of_mainSplitGap_and_assumptions hSplit hCoupling⟩

/-- Split-gap witnesses plus explicit coupling assumptions imply the statement-level #142 target. -/
theorem erdos_problem_142_of_mainSplitGap_and_assumptions
    (hSplit : MainSplitGap) (hCoupling : SplitGapToMainTheoreticalGapAssumptions) :
    ErdosProblems.erdos_problem_142 := by
  exact
    erdos_problem_142_of_main_theoretical_gap
      (mainTheoreticalGap_of_mainSplitGap_and_assumptions hSplit hCoupling)

/-- Off-path matched-profile route: if the named matched-profile frontier package is provided,
split-gap data can be promoted all the way to the full main gap. -/
noncomputable def mainTheoreticalGap_of_mainSplitGap_and_matchedProfileFrontier
    (hSplit : MainSplitGap) (hFrontier : Problem142MatchedProfileFrontier) :
    MainTheoreticalGap :=
  mainTheoreticalGap_of_mainSplitGap_and_assumptions hSplit
    (splitGapToMainTheoreticalGapAssumptions_of_matchedProfileFrontier hFrontier)

/-- Statement-level #142 from split-gap data plus the named off-path matched-profile frontier
package. This is the clean theorem form of the stronger conjectural route. -/
theorem erdos_problem_142_of_mainSplitGap_and_matchedProfileFrontier
    (hSplit : MainSplitGap) (hFrontier : Problem142MatchedProfileFrontier) :
    ErdosProblems.erdos_problem_142 := by
  exact erdos_problem_142_of_main_theoretical_gap
    (mainTheoreticalGap_of_mainSplitGap_and_matchedProfileFrontier hSplit hFrontier)

/-- Frontier theorem: statement-level #142 from split-gap together with the current axiom frontier. -/
theorem erdos_problem_142_of_mainSplitGap_and_frontier
    (hSplit : MainSplitGap) : ErdosProblems.erdos_problem_142 := by
  exact erdos_problem_142_of_mainSplitGap_and_matchedProfileFrontier
    hSplit matchedProfileFrontier_axiomDebt

end Erdos142
