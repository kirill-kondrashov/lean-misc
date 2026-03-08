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
  - `CouplingTargetK3`: reduced to explicit dominance target `import_targets.split_gap_k3_profile_dominance_target`;
    current elimination route is now factored further into:
    `import_targets.k3_upper_exponent_gt_half_target`,
    `import_targets.k3_decay_template_dominance_of_beta_gt_half_target`,
    and `import_targets.k3_decay_to_profile_transport_target`.
    The decay comparison and transport layers are now proved; the remaining open content is the
    exponent regime `β > 1 / 2`.
    This is now surfaced in code as `LiteratureK3ExponentGtHalfAssumptions`, and
    `Problem142Gap.lean` already contains the corresponding end-to-end `k=3` coupling derivation
    from that assumption layer.
    The source-facing missing import is also explicit:
    `bound_targets.k3_superpolylog_upper_profile_gt_half`.
    Under `LiteratureK3ExponentGtHalfSourceAssumptions`, `Problem142Literature.lean`
    now directly instantiates `K3ProfileWitnessImported`.
    Audit status: completed with negative verdict for the current Kelley-Meka extraction.
    The source audit now identifies an explicit exponent `β = 1 / 12` from the paper's
    `many-3-progs` theorem, so the stronger `β > 1 / 2` import is not available from the
    currently extracted source theorem shape.
    The honest replacement endpoint is now implemented as the source-backed split package
    `K3SourceBackedSplitGap`, which records:
    one explicit `β = 1 / 12` upper witness, one Behrend lower witness, and the true
    compatibility direction `k3_behrend_lower_template =O k3_upper_profile`.
    See:
    [NOTES_problem142_k3_kelley_meka_source_audit_2026-03-07.md](NOTES_problem142_k3_kelley_meka_source_audit_2026-03-07.md)
    and
    [PLAN_erdos_problem_142_k3_split_surface_packaging_2026-03-07.md](PLAN_erdos_problem_142_k3_split_surface_packaging_2026-03-07.md)
  - `CouplingTargetK4`: unresolved.
  - `CouplingTargetKge5`: unresolved.

## Revised Plan

1. **Keep branch decomposition explicit and auditable** (complete)
   - Continue to treat `MainUpperGap` and `MainSplitGap` as the mathematically justified frontier.

2. **Promote coupling assumptions to explicit search targets** (in progress)
   - Define a prioritized search order:
     1. `k=3`: prove `import_targets.split_gap_k3_profile_dominance_target` (branch-justified coupling of upper/superpolylog and Behrend/sqrt branches).
     2. `k=4`: import or prove matching lower polylog profile witness.
     3. `k≥5`: import or prove matching lower iterated-log profile family.
   - Cycle-6 implementation has added explicit branch-local coupling target templates in
     `ErdosProblems/Problem142Literature.lean`:
     - `import_targets.split_gap_k3_coupling_target`
     - `import_targets.split_gap_k4_coupling_target`
     - `import_targets.split_gap_kge5_coupling_target`
   - `k=3` note:
     the old matched-profile elimination route is closed; active `k=3` work should now treat
     `K3SourceBackedSplitGap` as the fixed honest endpoint and avoid further optimization of the
     false `β > 1 / 2` path.
  - Post-pivot redesign status:
    `Problem142Gap.lean` now contains the further asymmetric downstream interfaces
    `MainK34ResolvedGap` and `MainK345ResolvedGap`, the practical all-branches
    source-backed split target `MainAllSourceBackedSplitGap` together with the named endpoint
    `Problem142AllSourceBackedSplitData`, the exported statement-level theorem surface
    `SourceBackedSplitRoute`, and the stronger off-path frontier package
    `Problem142MatchedProfileFrontier`.
    On the active practical path, `k=3`, `k=4`, `k=5`, and all fixed `k≥6`
    are treated by explicit source-backed split witnesses, so there is no remaining
    active coupling frontier on that practical route.
  - `k≥5` note:
    the first elimination route through
    `import_targets.kge5_exponent_order_target`
    is now off-path. Internet publication audit on 2026-03-07 found that the active target
    family is likely mis-specified: the source-backed upper theorem from Leng-Sah-Sawhney is of
    stretched-exponential `\log\log` type, not iterated-log power type. The active replacement
    should therefore be a source-backed split route rather than further work on the exponent-order
    comparison theorem.
    See:
    [PLAN_erdos_problem_142_kge5_frontier_elimination_2026-03-07.md](PLAN_erdos_problem_142_kge5_frontier_elimination_2026-03-07.md)
    and
    [PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md](PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md)

3. **Separate declaration of solvable vs. conjectural routes** (in progress)
   - Ensure README and plan docs continue to distinguish:
     - honest current consequences (`MainUpperGap`, `MainSplitGap`),
     - speculative full theorem (`MainTheoreticalGap`).

4. **If coupling remains out of reach** (ongoing)
   - Introduce a minimal replacement theorem for practical use:
     - explicit upper-only consequence + explicitly conjectural `MainTheoreticalGap`.

## Progress Summary

- **Real-solution feasibility today**: `~33%` (honest partial formalization frontiers are in place; full gap still blocked).
- **Next concrete measurable milestone**: keep the practical target
  `MainAllSourceBackedSplitGap` stable as the honest split-strength endpoint, and isolate any
  future work strictly to the stronger matched-profile route rather than reintroducing it into the
  active practical path.
- Latest completed `k=3` cycle:
  [PLAN_erdos_problem_142_k3_split_surface_packaging_2026-03-07.md](PLAN_erdos_problem_142_k3_split_surface_packaging_2026-03-07.md)
- Active next-cycle files:
  [PLAN_erdos_problem_142_k34_split_resolved_redesign_2026-03-07.md](PLAN_erdos_problem_142_k34_split_resolved_redesign_2026-03-07.md)
  and
  [PLAN_erdos_problem_142_kge6_source_backed_family_2026-03-07.md](PLAN_erdos_problem_142_kge6_source_backed_family_2026-03-07.md)
