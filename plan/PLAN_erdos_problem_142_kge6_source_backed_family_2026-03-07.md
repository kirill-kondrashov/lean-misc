# Plan: `k >= 6` Source-Backed Tail Family

Date: 2026-03-07

## Objective

Continue only on the non-stuck route by replacing the remaining tail frontier

- from: matched-profile coupling for `k >= 6`,
- to: source-backed split control for each fixed `k >= 6`.

This follows the same Tao-style move that succeeded for `k = 5`:
use the strongest true source-backed upper and lower scales, then prove the true compatibility
`lower = O(upper)` instead of chasing a false matched-profile target.

## Status

Progress: `██████` `5 / 5` milestones

## Milestones

1. `[x]` Freeze the new tail-family target.
   - For each fixed `k >= 6`, define a stretched-exponential `log log` upper source target and a
     Rankin/O'Bryant lower source target.

2. `[x]` Add tail-family witness interfaces.
   - `Kge6UpperStretchedexpProfileWitness`
   - `Kge6LowerRankinProfileWitness`
   - `Kge6SourceBackedSplitWitness`

3. `[x]` Prove the tail-family compatibility theorem.
   - For each fixed `k >= 6`,
     `L_k^{src}(N) = O(U_k^{src}(N))`.

4. `[x]` Expose a source-facing literature layer and builders.
   - dedicated assumption classes,
   - extraction from those assumptions.

5. `[x]` Package the result at the gap layer.
   - define a tail source-backed split surface,
   - define an all-source-backed split practical target.

## Mathematical Status

Current live route after this cycle:

```text
k = 3:
  source-backed split

k = 4:
  source-backed split

k = 5:
  source-backed split

k >= 6:
  source-backed split
```

The resulting practical target is now:

```text
MainAllSourceBackedSplitGap
```

with explicit source-backed split control for every branch:

```text
k = 3, 4, 5:
  dedicated source-backed split packages

k >= 6:
  tail-family source-backed split packages
```

This eliminates active coupling debt on the practical route. The remaining stronger blocked route
is only the full matched-profile / full Erdős #142 theorem.
