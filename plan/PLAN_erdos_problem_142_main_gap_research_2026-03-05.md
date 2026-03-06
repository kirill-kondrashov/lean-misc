# Plan: Erdős #142 Main-Gap Research (2026-03-05)

## Objective

Close the remaining gap encoded by `ErdosProblems/Problem142Gap.lean`:
replace imported witness interfaces with mathematically justified imported/proved results, or
redesign targets if current interfaces are stronger than known theorems.

## Progress Bar

- Main-gap research program: `6 / 6` milestones completed
- Progress: `100%` `[####################]`
- Real-solution feasibility: full two-sided `MainTheoreticalGap` is still not derivable from current local assumptions.

## Remaining Formal Gap (Current Encoding)

In `ErdosProblems/Problem142Gap.lean`, the remaining gap is packaged as:

- `Erdos142.MainTheoreticalGap`
- bundle fields:
  - `Erdos142.K3ProfileWitnessImported`
  - `Erdos142.K4ProfileWitnessImported`
  - `Erdos142.Kge5ProfileWitnessImported`

This means the checker is clean, but mathematical content is still represented by imported
interfaces rather than concrete theorem instances.

## Feasibility Reassessment (as of 2026-03-06)

This plan is operationally complete as infrastructure, but the **actual theorem-to-theorem closure** is still incomplete.

- implemented and honest frontiers: `MainUpperGap`, `MainLowerGap`, and `MainSplitGap`;
- unresolved coupling plane: `SplitGapToMainTheoreticalGapAssumptions` (all three branch-local targets remain open);
- unresolved concrete coupling: `CouplingTargetK3`, `CouplingTargetK4`, `CouplingTargetKge5`;
- practical implication: the full `erdos_problem_142` route is not yet realized as a non-s speculative theorem consequence.

Revised feasibility bar by route:

- `MainUpperGap`: `5 / 5` milestones (implemented)
- `MainLowerGap`: `4 / 4` milestones (implemented)
- `MainSplitGap`: `3 / 3` milestones (implemented)
- `MainTheoreticalGap`: `0 / 5` milestones (currently blocked at split-to-full coupling)

## Explicit Proof-Obligation Matrix (From `Problem142Literature.lean`)

1. `k = 3` (`K3ProfileWitnessImported`)
   - Provide one witness with parameters `β c C : ℝ`, `0 < β`, `0 < c`, `0 < C`.
   - Prove:
     - `hUpper : r 3 =O[atTop] (N ↦ C * N * exp (-c * (log (N+2))^β))`
     - `hLower : (N ↦ C * N * exp (-c * (log (N+2))^β)) =O[atTop] r 3`

2. `k = 4` (`K4ProfileWitnessImported`)
   - Provide one witness with parameters `c C : ℝ`, `0 < c`, `0 < C`.
   - Prove:
     - `hUpper : r 4 =O[atTop] (N ↦ C * N / (log (N+2))^c)`
     - `hLower : (N ↦ C * N / (log (N+2))^c) =O[atTop] r 4`

3. `k ≥ 5` (`Kge5ProfileWitnessImported`)
   - Provide a family witness `∀ k ≥ 5` with parameters `c C : ℝ`, `0 < c`, `0 < C`.
   - Prove for each fixed `k`:
     - `hUpper : r k =O[atTop] (N ↦ C * N / (log (log (N+3)))^c)`
     - `hLower : (N ↦ C * N / (log (log (N+3)))^c) =O[atTop] r k`

## Milestones

1. **Feasibility audit vs known literature** — `completed`
   - Verify whether each obligation above is supported by known results (as stated, or via
     transparent bridge lemmas).
   - Output: branch-by-branch table (`k=3`, `k=4`, `k≥5`) with citation, exact theorem shape,
     Lean-shape verdict (`direct`, `bridge`, `not currently supported`).
   - Output file:
     - `plan/NOTES_problem142_gap_feasibility_audit.md`
   - Verdict summary:
     - `k=3`: upper `bridge`, full two-sided witness `not currently supported`.
     - `k=4`: upper `direct`, lower `not currently supported`.
     - `k≥5`: upper `direct`, lower `not currently supported`.
     - Overall: direct instantiation of current `MainTheoreticalGap` is not currently honest.

2. **`k = 3` closure path** — `completed`
   - Either instantiate `K3ProfileWitnessImported` from imported theorem(s), or document minimal
     weakening/reparameterization needed for a true statement.
   - Acceptance criterion: closure decision is encoded in Lean and documented with explicit blocker
     classification (`instantiate` vs `redesign/weakening`).
   - Progress update (2026-03-05):
     - Implemented Behrend-lower bridge theorems in `Problem142Literature.lean`:
       - `k3_behrend_lower_isBigO_of_eventual_le`
       - `k3_behrend_lower_profile_implies_isBigO_lower`
       - `k3_behrend_lower_isBigO_of_literature_rates`
       - `k3_mixed_two_sided_profile_of_literature_rates`
     - Result: obtained a valid lower-side `isBigO` consequence in Behrend shape.
     - Remaining blocker: still does not instantiate `K3ProfileWitnessImported` due to
       matched single-profile coupling with upper-side parameter `β`.
     - Decision: treat current `K3ProfileWitnessImported` as strong/full target; use mixed-profile
       theorem path for best-known honest `k=3` consequence.

3. **`k = 4` closure path** — `completed`
   - Either instantiate `K4ProfileWitnessImported`, or document minimal weakening needed.
   - Acceptance criterion: closure decision is encoded in Lean/docs with exact bottleneck class.
   - Progress update (2026-03-05):
     - Added executable upper-only extraction path from `LiteratureRateAssumptions`
       (via classical-choice wrappers and imported upper interfaces).
     - Added route theorem:
       - `upper_variant_of_literature_rates_via_upper_profile_witnesses`
   - Bottleneck classification: `missing lower`.
   - Decision: keep `K4ProfileWitnessImported` as strong/full target; use upper-only path as
     current best-known honest consequence.

4. **`k ≥ 5` closure path** — `completed`
   - Either instantiate `Kge5ProfileWitnessImported`, or isolate minimal true family statement.
   - Acceptance criterion: explicit decision encoded for family-wise honesty.
   - Progress update (2026-03-05):
     - Added executable family upper-only extraction path from `LiteratureRateAssumptions`.
     - Family upper closure now routes through `Kge5UpperProfileWitnessImported`.
   - Bottleneck classification: `missing lower`.
   - Decision: current full two-sided family witness remains too strong; upper-only family path is
     the honest current frontier.

5. **Target/interface redesign (if needed)** — `completed`
   - If milestones 2–4 fail due true mathematical mismatch, redesign interfaces to match
     strongest honest currently-known consequences.
   - Preserve a clear separation between “proved/imported” and “conjectural”.
   - Draft produced:
     - `plan/NOTES_problem142_gap_interface_redesign.md`
   - Implemented in Lean:
     - new upper-only witness interfaces in `ErdosProblems/Problem142Literature.lean`
     - new upper-only aggregate theorem:
       `upper_variant_of_upper_profile_witnesses_for_all_k_ge_three`
     - new `MainUpperGap` packaging + bridge theorem:
       `upper_variant_of_main_upper_gap`
       in `ErdosProblems/Problem142Gap.lean`

6. **Integration and checker policy update** — `completed`
   - Replace imported interfaces with theorem-backed instances where possible.
   - Update `check_axioms.lean`, `README.md`, and `Problem142Gap.lean` to reflect final status.
   - Completed items:
     - `Problem142Gap.lean` includes `MainUpperGap` and `upper_variant_of_main_upper_gap`.
     - `README.md` now distinguishes upper-only best-known route vs strong/full two-sided route.
     - Verification run:
       - `make verify` passed.
     - Checker policy decision:
       - no `check_axioms.lean` target-list change needed for this step.

## Blocked Planes (And Elimination Strategy)

1. **Over-strong interface plane**
   - Risk: witness interfaces require stronger two-sided matching than literature provides.
   - Elimination: run feasibility audit first; redesign interfaces before proof engineering.

2. **Source-to-Lean statement mismatch plane**
   - Risk: published theorem shape does not match current Lean predicates.
   - Elimination: add explicit bridge lemmas with named assumptions and provenance notes.

3. **Asymptotic normalization plane**
   - Risk: equivalent asymptotic forms differ in constants/log shifts/exponent presentation.
   - Elimination: prove reusable normalization lemmas (`N+2`, `N+3`, nested-log domains, constants).

4. **Branch coupling plane**
   - Risk: forcing one uniform schema across `k=3`, `k=4`, `k≥5` may block honest progress.
   - Elimination: keep branch-local interfaces and only unify where mathematically justified.

## Immediate Next Action

Cycles 1-3 in this file are complete. Next research cycle should target:

- criteria for when/if to retire strong matched witness interfaces
- split-gap to full-gap comparison lemmas (what exact extra assumptions close the gap)
- import-ready statement templates for future `k=4`/`k≥5` lower results

The current cycle should now follow:

- [PLAN_erdos_problem_142_feasibility_reassessment_2026-03-06.md](PLAN_erdos_problem_142_feasibility_reassessment_2026-03-06.md)
- [PLAN_erdos_problem_142_main_gap_coupling_cycle6_2026-03-06.md](PLAN_erdos_problem_142_main_gap_coupling_cycle6_2026-03-06.md)

## Cycle 2 Extension (Lower-Interface Track)

### Progress Bar

- Cycle 2 lower-interface program: `4 / 4` milestones completed
- Progress: `100%` `[####################]`

### Milestones

1. **Add decoupled lower witness interfaces** — `completed`
   - Added in `ErdosProblems/Problem142Literature.lean`:
     - `K3BehrendLowerProfileWitnessImported`
     - `K4LowerProfileWitnessImported`
     - `Kge5LowerProfileWitnessImported`
   - Added strong-to-lower conversion instances for `k = 4` and `k ≥ 5`.

2. **Expose lower-profile data theorems from imported witnesses** — `completed`
   - Added extraction theorems:
     - `k3_behrend_lower_profile_of_imported_witness`
     - `k4_lower_profile_of_imported_witness`
     - `kge5_lower_profile_of_imported_witness`

3. **Add lower-gap packaging in `Problem142Gap.lean`** — `completed`
   - Added:
     - `MainLowerGap`
     - `lower_profile_data_of_main_lower_gap`
     - `mainLowerGap_of_instances`

4. **Integrate lower-route status into docs and frontier classification** — `completed`
   - Update README and research notes to distinguish:
     - available lower-route interfaces (`k=3` Behrend lower is wired from literature rates)
     - missing lower-source support (`k=4`, `k≥5`)
   - Decide whether to create explicit placeholder assumptions for `k=4`/`k≥5` lower routes, or
     keep them as intentionally uninstantiated interfaces.
   - Decision recorded:
     - keep `k=4`/`k≥5` lower interfaces uninstantiated in current literature layer
     - do not add artificial placeholder assumptions to `LiteratureRateAssumptions`
   - Documentation updated:
     - `README.md`
     - `plan/NOTES_problem142_gap_interface_redesign.md`

## Cycle 3 Extension (Split-Gap Mixed-Profile Track)

### Progress Bar

- Cycle 3 split-gap program: `3 / 3` milestones completed
- Progress: `100%` `[####################]`

### Milestones

1. **Add mixed-profile theorems from split imported interfaces** — `completed`
   - Added in `ErdosProblems/Problem142Literature.lean`:
     - `k3_mixed_two_sided_profile_of_imported_split_witnesses`
     - `k4_mixed_two_sided_profile_of_imported_split_witnesses`
     - `kge5_mixed_two_sided_profile_of_imported_split_witnesses`

2. **Add combined split-gap packaging in `Problem142Gap.lean`** — `completed`
   - Added:
     - `MainSplitGap`
     - `split_gap_data_of_main_split_gap`
     - `mainSplitGap_of_instances`

3. **Integrate split-gap status into docs/notes** — `completed`
   - Updated:
     - `README.md`
     - `plan/NOTES_problem142_gap_feasibility_audit.md`

## Cycle 4 Extension (Gap-Comparison Mapping)

### Progress Bar

- Cycle 4 comparison-mapping program: `3 / 3` milestones completed
- Progress: `100%` `[####################]`

### Milestones

1. **Map full-gap to upper-gap explicitly** — `completed`
   - Added:
     - `mainUpperGap_of_mainTheoreticalGap`
     - `upper_variant_of_mainTheoreticalGap`

2. **Map full-gap plus `k=3` Behrend-lower to split-gap explicitly** — `completed`
   - Added:
     - `mainSplitGap_of_mainTheoreticalGap_and_k3BehrendLower`
     - `split_gap_data_of_mainTheoreticalGap_and_k3BehrendLower`

3. **Integrate comparison-map status into docs/notes** — `completed`
   - Updated:
     - `README.md`
     - `plan/NOTES_problem142_gap_feasibility_audit.md`
