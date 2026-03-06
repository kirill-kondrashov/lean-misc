# Plan: Erdős #142 Main-Gap Follow-up (Cycle 5, 2026-03-06)

## Objective

Drive the remaining `MainTheoreticalGap` blocker into an explicit, branch-local coupling program:
from split-gap frontier statements to full matched two-sided witness interfaces.

## Progress Bar

- Cycle 5 coupling program: `5 / 5` milestones completed
- Progress: `100%` `[####################]`

## Milestones

1. **Name the split-to-full coupling surface in Lean** — `completed`
   - Implemented in `ErdosProblems/Problem142Gap.lean`:
     - `SplitGapToMainTheoreticalGapAssumptions`
     - `mainTheoreticalGap_of_mainSplitGap_and_assumptions`
     - `erdos_problem_142_of_mainSplitGap_and_assumptions`
   - Outcome: residual gap is now an explicit assumption structure, not implicit glue.

2. **Add branch-local coupling targets (`k=3`, `k=4`, `k≥5`)** — `completed`
   - Introduce named proposition aliases for each coupling field so future imports can target
     one branch without touching others.
   - Implemented in `ErdosProblems/Problem142Gap.lean`:
     - `CouplingTargetK3`
     - `CouplingTargetK4`
     - `CouplingTargetKge5`
     - `coupling_targets_of_splitGapToMainTheoreticalGapAssumptions`

3. **Template import-ready theorem stubs for missing lower branches** — `completed`
   - Add clearly named placeholder statements for `k=4` and `k≥5` lower-source imports in a
     dedicated assumptions namespace (without claiming instances).
   - Implemented in `ErdosProblems/Problem142Literature.lean`:
     - `import_targets.k4_polylog_lower_profile`
     - `import_targets.kge5_iteratedlog_lower_profile`
     - `LiteratureLowerImportAssumptions`
     - `k4_lower_import_target_of_imported_witness`
     - `kge5_lower_import_target_of_imported_witness`

4. **Document theorem graph from split-gap to full-gap** — `completed`
   - Update README/research notes with a compact implication map and where each edge is blocked.
   - Progress:
     - README now documents the coupling-assumption bridge surface.
     - Added explicit edge list in:
       - `plan/NOTES_problem142_gap_feasibility_audit.md` (`Cycle-5 Implication Graph`).

5. **Verification and integration check** — `completed`
   - Re-run `make check` and `make verify`.
   - Ensure checker policy remains unchanged unless a new target is intentionally added.
   - Completed: `make verify` passed.

## Blocked Planes (Cycle 5)

1. **Coupling plane**
   - Risk: no known theorem currently upgrades split mixed profiles into matched full witnesses.
   - Elimination: keep coupling assumptions branch-local and explicit.

2. **Lower-source plane (`k=4`, `k≥5`)**
   - Risk: lower interfaces remain uninstantiated.
   - Elimination: isolate import-ready theorem names and attach provenance expectations.

3. **Over-aggregation plane**
   - Risk: trying to solve all branches at once obscures usable progress.
   - Elimination: maintain independent branch milestones and report per-branch status.

## Immediate Next Action

Cycle 5 is complete. Next cycle candidate:

- propose concrete branch-local candidate assumptions for each coupling field in
  `SplitGapToMainTheoreticalGapAssumptions` with provenance tags (`k=3`, `k=4`, `k≥5`).

## Cycle 6 (Coupling Implementation Continuation)

- Status: initiated
- Progress: `2 / 5` ( `40%` ) `[########--------]`
- Implementation plan: [PLAN_erdos_problem_142_main_gap_coupling_cycle6_2026-03-06.md](PLAN_erdos_problem_142_main_gap_coupling_cycle6_2026-03-06.md)
- Current focus:
  - define branch-specific coupling proof obligations with minimal additional assumptions,
  - pursue `k=3` first, then `k=4`, then `k ≥ 5` as evidence becomes available.
