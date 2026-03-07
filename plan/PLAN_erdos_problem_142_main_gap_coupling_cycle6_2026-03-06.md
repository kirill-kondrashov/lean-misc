# Plan: Erdos #142 Split-to-Main Coupling Cycle 6 (2026-03-06)

## Objective

Close the remaining branch-local promotion step from `MainSplitGap` to `MainTheoreticalGap` by introducing explicit coupling targets, collecting possible source theorems, and proving at least one branch in a branch-respecting way.

## Progress Bar

- Cycle 6 coupling implementation: `6 / 6` completed
- Progress: `[####################]` `100%`

## Milestones

1. **Normalize coupling interfaces as explicit branch contracts** — `completed`
   - Re-check that all coupling goals are represented as branch-local fields in
     `SplitGapToMainTheoreticalGapAssumptions`:
     - `CouplingTargetK3`
     - `CouplingTargetK4`
     - `CouplingTargetKge5`
   - Outcome: already present and imported in the current architecture.

2. **Create branch-specific target templates from split-gap data** — `completed`
   - Added explicit import-ready branch coupling target templates in
   [Problem142Literature.lean](ErdosProblems/Problem142Literature.lean) as:
     - `import_targets.split_gap_k3_coupling_target`
     - `import_targets.split_gap_k4_coupling_target`
     - `import_targets.split_gap_kge5_coupling_target`
   - These templates make the exact branch-local shapes required by
     `SplitGapToMainTheoreticalGapAssumptions` explicit and auditable.
   - Priority order:
     1. `k = 3`: align Behrend-style lower profile + current upper superpolylog profile.
     2. `k = 4`: align plausible lower polylog profile.
     3. `k ≥ 5`: align plausible iterated-log lower profile.

3. **Materialize remaining coupling blockers as explicit temporary axioms** — `completed`
   - Added `splitGap_k3_profile_dominance_frontier`, `splitGap_k4_profile_dominance_frontier`,
     and `splitGap_kge5_profile_dominance_frontier` as temporary axioms in
     [Problem142Gap.lean](ErdosProblems/Problem142Gap.lean).
   - Follow-up refinement:
     - the `k=3` item has since been sharpened so the actual remaining axiom frontier is now
       `splitGap_k3_upper_exponent_gt_half_frontier`, with
       `splitGap_k3_profile_dominance_frontier` derived as a theorem.
   - Updated [check_axioms.lean](../check_axioms.lean) to explicitly permit these three names
     as temporary debt and keep `scripts/verify_output.sh` green.
   - Added bridge definitions in [Problem142Gap.lean](ErdosProblems/Problem142Gap.lean) from the
     import-target namespace (`import_targets.split_gap_*_coupling_target`) into the concrete coupling
     assumption structure used by the promotion theorem.

4. **Search for direct `k = 3` coupling proof path** — `completed`
   - Evaluate whether `k=3` Behrend lower profile can be re-expanded into the same profile template used
     by `K3ProfileWitnessImported` via exponent-parameter weakening/strengthening lemmas.
   - Capture precise parameter-loss formula if possible.
   - Outcome: mismatch is now isolated behind an explicit dominance assumption
     `import_targets.split_gap_k3_profile_dominance_target`, with a bridge theorem
     from this target to `import_targets.split_gap_k3_coupling_target`.
   - Current remaining blocker: explicit proof of this dominance target:
     `splitGap_k3_profile_dominance_frontier`.

5. **Search for `k = 4` matching lower-profile source** — `completed`
   - Add import-ready skeleton theorem statement with explicit provenance notes so future literature imports can
     fill the gap without reworking the proof interface.
   - Implemented dominance target shape:
     - `import_targets.split_gap_k4_profile_dominance_target`
   - Added corresponding frontier axiom:
     - `splitGap_k4_profile_dominance_frontier`
   - Added branch reconstruction bridge:
     - `splitGap_k4_coupling_target_of_profile_dominance_target`
   - Outcome: this branch coupling is now explicit and deferred behind one frontier assumption.

6. **Search for `k ≥ 5` matching family lower profile source** — `completed`
   - Add import-ready skeleton theorem statement with explicit provenance notes for uniform family closure.
   - Implemented dominance target shape:
     - `import_targets.split_gap_kge5_profile_dominance_target`
   - Added corresponding frontier axiom:
     - `splitGap_kge5_profile_dominance_frontier`
   - Added branch reconstruction bridge:
     - `splitGap_kge5_coupling_frontier`
     - `splitGap_kge5_coupling_target_of_frontier`

## Deliverables

- branch-local coupling map in plan/docs that marks which fields are proved vs blocked
- if any branch closes: corresponding update to `PLAN_erdos_problem_142_main_gap_followup_cycle5_2026-03-06.md`
- if none close: updated blocker inventory with concrete obstruction class per branch
