# Notes: Problem #1 odd-cube excess profile search

## Purpose

Record reproducible low-dimensional search data for the current odd-cube boundary proof program.

Search tool:

- `tools/problem1_odd_profile_search.py`

Command used on March 11, 2026:

```bash
python3 tools/problem1_odd_profile_search.py
```

The script prints a terminal progress bar and uses bold green status lines when no counterexample is
found; it switches to bold red warnings if a searched candidate fails.

## Verified low-dimensional outcomes

Dimensions searched:

- `n = 1`
- `n = 3`
- `n = 5`

Search outcomes:

1. `OddHalfCubeBoundaryLowerStatement` survives exhaustive search in all three dimensions.
2. `OddSectionPairInterfaceBoundaryLowerStatement` has no counterexample in all three dimensions.
3. The search reproduces the already-known failure of the older `+ 2e` strict-excess route via the
   explicit `n = 3` profile data.
4. For odd half-cube down-sets, the minimum slice profile in the searched dimensions matches the
   truncated even-binomial profile `choose(n - 1, r)` on the lower half and `0` above it.
5. Among half-cube down-sets that minimize `|\partial^+ D|`, the searched slice profile matches
   the exact `oddLowerHalfFamily` profile `choose(n, r)` for `r <= (n - 1) / 2` and `0` above it.

## Exact half-cube slice-minimum data

For odd `n = 2m + 1`, write

$$
s_n(r)
:=
\min\{\,|D_r| : D \subseteq 2^{[n]} \text{ down-set},\ |D| = 2^{n-1}\,\}.
$$

The search computes the following exact minima.

### `n = 3`

Half-cube size: `2^(3-1) = 4`

Minimum slice vector:

| rank `r` | `s_3(r)` | truncated target `choose(2, r)` for `r <= 1`, else `0` |
| --- | --- | --- |
| 0 | 1 | 1 |
| 1 | 2 | 2 |
| 2 | 0 | 0 |
| 3 | 0 | 0 |

### `n = 5`

Half-cube size: `2^(5-1) = 16`

Minimum slice vector:

| rank `r` | `s_5(r)` | truncated target `choose(4, r)` for `r <= 2`, else `0` |
| --- | --- | --- |
| 0 | 1 | 1 |
| 1 | 4 | 4 |
| 2 | 6 | 6 |
| 3 | 0 | 0 |
| 4 | 0 | 0 |
| 5 | 0 | 0 |

Empirical consequence:

- a plausible next odd-dimensional target is the slice-threshold statement
  `|(D # r)| >= choose(2m, r)` for `0 <= r <= m` whenever `D` is a down-set in `2^[2m+1]` of
  size `2^(2m)`
- this is strictly weaker than demanding the full lower-half family slices, and is compatible with
  the searched half-cube examples in `n = 3` and `n = 5`
- Lean target surface now added: `OddHalfCubeSliceThresholdStatement`
- the canonical witness `oddLowerHalfFamily` now realizes that target in Lean via
  `oddLowerHalfFamily_realizes_oddHalfCubeSliceThresholdTarget`

## Boundary minimizer slice data

For odd `n = 2m + 1`, write

$$
e_n(r)
:=
\{|D_r| : D \subseteq 2^{[n]} \text{ down-set},\ |D| = 2^{n-1},\ |\partial^+ D| = b_n(2^{n-1})\}.
$$

The search records the distinct slice profiles of half-cube down-sets that actually attain the
minimum boundary.

### `n = 1`

Minimum boundary: `b_1(1) = 1`

Distinct minimizing slice profiles:

- `[1, 0]`

This is exactly the odd lower-half profile `[choose(1, 0), 0]`.

### `n = 3`

Minimum boundary: `b_3(4) = 3`

Distinct minimizing slice profiles:

- `[1, 3, 0, 0]`

This is exactly the odd lower-half profile `[choose(3, 0), choose(3, 1), 0, 0]`.

### `n = 5`

Minimum boundary: `b_5(16) = 10`

Distinct minimizing slice profiles:

- `[1, 5, 10, 0, 0, 0]`

This is exactly the odd lower-half profile
`[choose(5, 0), choose(5, 1), choose(5, 2), 0, 0, 0]`.

Empirical consequence:

- in the searched dimensions, every half-cube boundary minimizer has the same slice profile as
  `oddLowerHalfFamily`
- this makes odd extremizer classification the cleanest currently supported Phase 1 route, stronger
  and more proof-facing than the raw slice-minimum bound

## Exact odd excess profile data

Write

$$
b_n(k) := \min\{\,|\partial^+ N| : N \subseteq 2^{[n]} \text{ down-set},\ |N| = k\,\}.
$$

### `n = 3`

Half-cube size: `2^(3-1) = 4`

Middle binomial target: `choose(3, 1) = 3`

Exact values near half-cube:

| `k` | `e = k - 4` | `b_3(k)` |
| --- | --- | --- |
| 4 | 0 | 3 |
| 5 | 1 | 3 |
| 6 | 2 | 2 |
| 7 | 3 | 1 |
| 8 | 4 | 0 |

### `n = 5`

Half-cube size: `2^(5-1) = 16`

Middle binomial target: `choose(5, 2) = 10`

Exact values near half-cube:

| `k` | `e = k - 16` | `b_5(k)` |
| --- | --- | --- |
| 16 | 0 | 10 |
| 17 | 1 | 11 |
| 18 | 2 | 11 |
| 19 | 3 | 10 |
| 20 | 4 | 10 |
| 21 | 5 | 9 |
| 22 | 6 | 8 |
| 23 | 7 | 8 |
| 24 | 8 | 7 |

## Pair-interface search data

For the candidate

$$
|\partial^+ N| + |(N \setminus M) \cup \partial^+ M|
\ge 2\binom{n}{(n-1)/2}
$$

with nested odd-dimensional down-sets `M ⊆ N` of sizes `2^(n-1) - e` and `2^(n-1) + e`, the
search found the following minima.

### `n = 3`

Target: `2 * choose(3, 1) = 6`

| `e` | minimum LHS |
| --- | --- |
| 0 | 6 |
| 1 | 7 |
| 2 | 6 |
| 3 | 7 |
| 4 | 8 |

### `n = 5`

Target: `2 * choose(5, 2) = 20`

| `e` | minimum LHS |
| --- | --- |
| 0 | 20 |
| 1 | 22 |
| 2 | 23 |
| 3 | 22 |
| 4 | 23 |
| 5 | 22 |
| 6 | 20 |
| 7 | 22 |
| 8 | 23 |

## Immediate proof-program consequences

1. The odd half-cube theorem remains compatible with every exact low-dimensional search now
   reproduced in-repo.
2. The pair-interface candidate remains empirically plausible and is strictly better supported than
   the old `+ 2e` strict-excess wrapper, which already fails in `n = 3`.
3. The odd excess profile is not monotone in `e` near half-cube mass, so any corrected theorem
   should not assume naive linear growth in the excess parameter.
