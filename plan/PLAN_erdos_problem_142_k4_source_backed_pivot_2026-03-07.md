# Plan: `k = 4` Source-Backed Pivot

Date: 2026-03-07

## Objective

Close the over-strong matched-profile route for `k = 4` as an active implementation target,
and replace it with the strongest honest local endpoint:
a first-class split package consisting of

- one lower polylog witness,
- one upper polylog witness,
- and explicit mixed two-sided split data,

without any claim that the two exponents match.

## Status

Progress: `█████-` `5 / 6` milestones

## Milestones

1. `[x]` Freeze the honest `k = 4` endpoint.
   - Treat the branch goal as split data
     `L_4(N) = O(r_4(N))` and `r_4(N) = O(U_4(N))`,
     not as a matched witness `U_4(N) = O(L_4(N))`.

2. `[x]` Package the branch-local split surface explicitly.
   - Implement `K4SourceBackedSplitWitness` in `Problem142Literature.lean`.
   - Add the extractor theorem
     `k4_mixed_two_sided_profile_of_sourceBackedSplitWitness`.

3. `[x]` Connect the package to the current literature layer.
   - Implement
     `k4SourceBackedSplitWitness_of_literatureLowerImportAssumptions`.
   - Add gap-layer alias
     `K4SourceBackedSplitGap`.
   - Add branch-local split theorem
     `k4_split_data_of_literatureLowerImportAssumptions`.

4. `[x]` Decide the downstream redesign target.
   - Implement the asymmetric downstream surface that treats both
     `k = 3` and `k = 4` as resolved only to split strength.
   - Active redesign file:
     - `PLAN_erdos_problem_142_k34_split_resolved_redesign_2026-03-07.md`

5. `[x]` Audit whether any local source note can still discharge the exponent-order target.
   - Target statement:
     `c_l <= c_u`.
   - Local audit result: negative.
   - No local source note currently discharges the exponent-order target.
   - Audit note:
     - `NOTES_problem142_k4_source_audit_2026-03-07.md`
   - So the matched-profile theorem remains explicitly blocked.

6. `[ ]` Update the high-level status docs once the redesign target is fixed.
   - README / feasibility docs should state that
     the active honest `k = 4` endpoint is split, not matched.

## Mathematical Status

Current true `k = 4` result in the repository:

```text
There exist cL, CL, cU, CU > 0 such that

  CL * N / (log(N+2))^cL = O(r_4(N))
  r_4(N) = O(CU * N / (log(N+2))^cU).
```

Still missing for matched-profile closure:

```text
CU * N / (log(N+2))^cU = O(CL * N / (log(N+2))^cL).
```

Minimal sufficient extra input:

```text
cL <= cU.
```

So the honest pivot is:
- keep the split package,
- stop treating matched-profile closure as locally justified,
- reopen the stronger route only if an exponent-order theorem is sourced.
