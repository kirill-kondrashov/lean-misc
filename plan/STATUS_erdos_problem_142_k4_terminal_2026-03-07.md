# Terminal Status: Erdos #142, `k = 4`

Date: 2026-03-07

## Problem Surface

Goal for the matched-profile route:

```text
Find one profile P_4(N) such that

  P_4(N) = O(r_4(N))
  r_4(N) = O(P_4(N)).
```

Current split profiles in the repository:

```text
L_4(N) := CL * N / (log(N+2))^cL
U_4(N) := CU * N / (log(N+2))^cU
```

with

```text
L_4(N) = O(r_4(N))
r_4(N) = O(U_4(N)).
```

## What Is Proved

1. Generic comparison lemma:

```text
If cL <= cU, then U_4(N) = O(L_4(N)).
```

2. Conditional frontier closure:

```text
If the literature layer provides cL <= cU,
then the `k = 4` matched-profile frontier is closed.
```

3. Honest source-backed split packaging:

```text
From LiteratureLowerImportAssumptions, the repository builds

- a lower `k = 4` polylog witness,
- an upper `k = 4` polylog witness,
- the mixed split statement

  L_4(N) = O(r_4(N))
  r_4(N) = O(U_4(N)).
```

## What Is Missing

The unmatched step is exactly:

```text
U_4(N) = O(L_4(N)).
```

A sufficient condition is:

```text
cL <= cU.
```

## Honest Mathematical Verdict

- Split `k = 4` control: proved.
- Matched-profile `k = 4` closure: not proved.
- Remaining blocker: no source-backed exponent-order theorem is encoded locally.
- Local source-note audit: negative; see `NOTES_problem142_k4_source_audit_2026-03-07.md`.
- Therefore the active honest endpoint is split, not matched.
