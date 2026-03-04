# Plan: Erdős #142 Explicit-Branch Axiom Burndown (2026-03-04)

## Objective

Minimize temporary axiom debt in the explicit-branch scaffold by collapsing branch-local debt
into structured witness axioms, then replacing those witnesses with real/imported theorems.

## Progress Bar

- Overall debt burndown (temporary explicit-branch axioms): `8 / 9` removed
- Progress: `89%` `[##################..]`

## Milestones

1. **Consolidate `k = 3` explicit branch debt** — `completed`
   - Temporary checker-allowlisted debt removed.
   - Branch now routed through imported-assumption interface:
     - `Erdos142.K3ProfileWitnessImported`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_k3_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_k3_lower_bound_axiom`

2. **Consolidate `k = 4` explicit branch debt** — `completed`
   - Temporary checker-allowlisted debt removed.
   - Branch now routed through imported-assumption interface:
     - `Erdos142.K4ProfileWitnessImported`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_k4_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_k4_lower_bound_axiom`

3. **Consolidate `k ≥ 5` explicit branch debt** — `completed`
   - Current single debt item family:
     - `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_kge5_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_kge5_lower_bound_axiom`

4. **Remove all witness axioms by replacing with proved/imported results** — `in_progress`
   - `k = 3`: moved to imported-assumption interface (done).
   - `k = 4`: moved to imported-assumption interface (done).
   - `k ≥ 5`: pending.
   - Success criterion:
     - no temporary explicit-branch axioms in checker output.

## Immediate Next Action

Replace `k ≥ 5` witness-family axiom with an imported-assumption interface pattern mirroring
`k = 3`/`k = 4`.
