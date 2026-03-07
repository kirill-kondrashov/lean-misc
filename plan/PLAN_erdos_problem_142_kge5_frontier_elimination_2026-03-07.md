# Plan: `k >= 5` Frontier Elimination

Date: 2026-03-07

## Objective

Eliminate the remaining active matched-profile frontier on the practical route by proving the
family dominance target for each fixed `k >= 5`.

## Status Note

This plan is now off the active path.

Reason:
- the current target compares two iterated-log templates,
- but the publication-backed upper theorem is stretched-exponential in `\log\log N`,
- so the route is now best treated as a stronger speculative branch rather than the live plan.

Replacement active plan:
- [PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md](PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md)

Active theorem surface:

```text
For each fixed k >= 5,

  U_k(N) = O(L_k(N))

where

  U_k(N) = CU(k) * N / (log(log(N+3)))^cU(k)
  L_k(N) = CL(k) * N / (log(log(N+3)))^cL(k).
```

## Status

Progress: `███---` `3 / 6` milestones

## Milestones

1. `[x]` Freeze the exact family target.
   - Use `import_targets.split_gap_kge5_profile_dominance_target` as the primary theorem surface.

2. `[x]` Prove the generic analytic comparison lemma.
   - Implemented as:
     - `import_targets.kge5_iteratedlog_template_dominance_of_exponent_le`

3. `[x]` Make the minimal extra source-side input explicit.
   - Implemented as:
     - `import_targets.kge5_exponent_order_target`
     - `import_targets.split_gap_kge5_profile_dominance_target_of_exponent_order`
     - `LiteratureKge5ExponentOrderAssumptions`
     - `split_gap_kge5_profile_dominance_target_of_literatureKge5ExponentOrderAssumptions`

4. `[ ]` Audit whether the current local `k >= 5` source notes actually supply the family
   exponent-order relation.

5. `[ ]` If the exponent order is source-backed, remove the active remaining frontier on the
   practical route.

6. `[ ]` If not, decide whether to pivot further to an all-branches split-only practical target.

## Mathematical Status

What is now proved in code:

```text
If cL(k) <= cU(k) for each fixed k >= 5,
then U_k(N) = O(L_k(N)) for each fixed k >= 5.
```

So the blocker on this stronger speculative route is the precise family input

```text
For each fixed k >= 5,
  cL(k) <= cU(k).
```
