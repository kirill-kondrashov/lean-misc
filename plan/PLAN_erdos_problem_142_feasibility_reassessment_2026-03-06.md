# Feasibility Reassessment: Erdős #142 (2026-03-06)

## Objective

Re-score the current Erdos-142 formalization pipeline against concrete, available inputs in the existing `plan/` artifacts.

## Current Feasibility Verdict

- **Open-problem status**: unchanged; full asymptotic formula for all `k` remains an open mathematical problem.
- **Formalization status**: strong infrastructure exists, but full theorem is not yet derivable from current local assumptions.
- **Main blocker**: one explicit coupling gap between split mixed-profile data and full matched two-sided full-gap witnesses.

## Evidence from Existing Plans

- `PLAN_erdos_problem_142.md`: states the problem is still open and frames this as long-horizon math + formalization work.
- `PLAN_erdos_problem_142_main_gap_research_2026-03-05.md`: records branch-wise milestone completion for interface surgery, but not full witness instantiation.
- `NOTES_problem142_gap_feasibility_audit.md`: identifies over-strong interface mismatch as the dominant gap (especially `k=4`, `k≥5` lower side).
- `PLAN_erdos_problem_142_main_gap_followup_cycle5_2026-03-06.md`: records the split-gap/coupling plane as the explicit unresolved bridge.
- `PLAN_erdos_problem_142_explicit_branch_axiom_burndown_2026-03-04.md`: confirms axiom debt burndown is complete, meaning remaining issues are theorem-content, not temporary axioms.
- `PLAN_erdos_problem_142_main_gap_coupling_cycle6_2026-03-06.md`: active implementation cycle for branch-local coupling proof obligations.

## Feasibility by Surface (Revised)

### 1) Strong two-sided full formula (current `MainTheoreticalGap`)

- **Status**: not feasible with current imported assumptions.
- **Progress bar**: `1 / 5` `[###---------------]`
- **Blocked planes**:
  - `k=3` coupling of Behrend lower profile to superpolylog upper profile.
  - missing lower-profile interfaces for `k=4` and `k≥5`.

### 2) Best-known upper envelope (implemented `MainUpperGap`)

- **Status**: feasible and implemented.
- **Progress bar**: `5 / 5` `[####################]`
- **Rationale**: branch-local upper witnesses are instantiable from `LiteratureRateAssumptions`.

### 3) Mixed-profile split frontier (`MainSplitGap` + extracted lower data)

- **Status**: feasible and implemented.
- **Progress bar**: `5 / 5` `[####################]`
- **Rationale**: split-gap interface is explicit and available through literature/bridge layers.

### 4) Full gap from split-gap (`SplitGapToMainTheoreticalGapAssumptions`)

- **Status**: not feasible until assumptions are proven or replaced.
- **Progress bar**: `2 / 5` `[#####-------------]`
- **Current status of fields**:
  - `CouplingTargetK3`: unresolved in this exact shape.
  - `CouplingTargetK4`: unresolved.
  - `CouplingTargetKge5`: unresolved.

## Revised Plan

1. **Keep branch decomposition explicit and auditable** (complete)
   - Continue to treat `MainUpperGap` and `MainSplitGap` as the mathematically justified frontier.

2. **Promote coupling assumptions to explicit search targets** (in progress)
   - Define a prioritized search order:
     1. `k=3`: prove a direct coupling from Behrend lower data plus the current upper profile in a branch-justified way.
     2. `k=4`: import or prove matching lower polylog profile witness.
     3. `k≥5`: import or prove matching lower iterated-log profile family.
   - Cycle-6 implementation has added explicit branch-local coupling target templates in
     `ErdosProblems/Problem142Literature.lean`:
     - `import_targets.split_gap_k3_coupling_target`
     - `import_targets.split_gap_k4_coupling_target`
     - `import_targets.split_gap_kge5_coupling_target`

3. **Separate declaration of solvable vs. conjectural routes** (in progress)
   - Ensure README and plan docs continue to distinguish:
     - honest current consequences (`MainUpperGap`, `MainSplitGap`),
     - speculative full theorem (`MainTheoreticalGap`).

4. **If coupling remains out of reach** (ongoing)
   - Introduce a minimal replacement theorem for practical use:
     - explicit upper-only consequence + explicitly conjectural `MainTheoreticalGap`.

## Progress Summary

- **Real-solution feasibility today**: `~33%` (honest partial formalization frontiers are in place; full gap still blocked).
- **Next concrete measurable milestone**: resolve at least one of `CouplingTargetK3/K4/Kge5` without changing core statement strength.
