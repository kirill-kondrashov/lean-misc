# Notes: `k = 4` Local Source Audit (2026-03-07)

## Scope

Audit only the local repository materials for a `k = 4` statement strong enough to discharge

```text
cL <= cU
```

which is the minimal sufficient input currently used by
`import_targets.k4_exponent_order_target`.

No external browsing was used in this audit pass.

## Files Checked

- `README.md`
- `plan/PLAN_erdos_problem_142.md`
- `plan/NOTES_problem142_gap_feasibility_audit.md`
- `plan/NOTES_problem142_gap_interface_redesign.md`
- `ErdosProblems/Problem142.lean`
- `ErdosProblems/Problem142Literature.lean`

## Positive Findings

1. The repository has a local upper-side source anchor for `k = 4`:

```text
Green-Tao (2017) -> bound_targets.k4_upper_green_tao
```

2. The repository has a local formal upper-profile benchmark target:

```text
bound_targets.k4_polylog_upper_profile
```

3. The repository now has a local formal lower split interface:

```text
import_targets.k4_polylog_lower_profile
LiteratureLowerImportAssumptions.k4_polylog_lower_profile
```

4. The repository proves the analytic implication

```text
cL <= cU  ==>  U_4(N) = O(L_4(N)).
```

## Negative Findings

1. No local source note states any explicit lower-side `k = 4` exponent value.
2. No local source note states any explicit upper/lower exponent comparison.
3. No local source note states the exact target

```text
cL <= cU.
```

4. The local notes continue to describe the `k = 4` lower side as not source-backed in the
current literature layer; they only support a split placeholder/import interface.

## Verdict

Local source-note audit result:

```text
The repository does not currently contain a source-backed local route to
import_targets.k4_exponent_order_target.
```

So the honest local mathematical status is:

```text
proved:   L_4(N) = O(r_4(N)) and r_4(N) = O(U_4(N))
missing:  U_4(N) = O(L_4(N))
blocked:  no local source-backed theorem giving cL <= cU
```

Therefore the matched-profile `k = 4` route remains blocked locally, while the split route
remains live.
