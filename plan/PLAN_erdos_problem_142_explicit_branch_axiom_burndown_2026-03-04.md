# Plan: Erdős #142 Explicit-Branch Axiom Burndown (2026-03-04)

## Objective

Minimize temporary axiom debt in the explicit-branch scaffold by collapsing branch-local debt
into structured witness axioms, then replacing those witnesses with real/imported theorems.

## Progress Bar

- Overall debt burndown (temporary explicit-branch axioms): `6 / 9` removed
- Progress: `67%` `[#############.......]`

## Milestones

1. **Consolidate `k = 3` explicit branch debt** — `completed`
   - Current single debt item:
     - `Erdos142.erdos_problem_142_explicit_k3_profile_witness_axiom`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_k3_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_k3_lower_bound_axiom`

2. **Consolidate `k = 4` explicit branch debt** — `completed`
   - Current single debt item:
     - `Erdos142.erdos_problem_142_explicit_k4_profile_witness_axiom`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_k4_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_k4_lower_bound_axiom`

3. **Consolidate `k ≥ 5` explicit branch debt** — `completed`
   - Current single debt item family:
     - `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom`
   - Derived theorem interfaces preserved:
     - `Erdos142.erdos_problem_142_explicit_kge5_upper_bound_axiom`
     - `Erdos142.erdos_problem_142_explicit_kge5_lower_bound_axiom`

4. **Remove all witness axioms by replacing with proved/imported results** — `pending`
   - Success criterion:
     - no temporary explicit-branch axioms in checker output.

## Immediate Next Action

Replace witness axioms with real/imported theorems in the order:
`k = 3` witness, `k = 4` witness, then `k ≥ 5` witness family.
