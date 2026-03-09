# Notes: Erdős #142 `k = 3` Direct Counting Intermediate Target

Date: 2026-03-09

## Objective

Identify the first exact theorem-shaped intermediate target for the direct `k = 3` counting route,
strictly weaker than the full Behrend-scale upper theorem.

## Selection Rule

The intermediate target must satisfy all of the following:

1. be an exact theorem on the original set `A ⊆ {1, ..., N}`;
2. be strictly weaker than the full Behrend-scale theorem

```text
r_3(N) << N exp(-c sqrt(log N));
```

3. avoid inventing unsupported quantitative count formulas;
4. connect to an already meaningful explicit benchmark inside the repository.

## Selected Intermediate Target

The first honest intermediate target is the direct `1 / 8` theorem:

```text
Find c > 0 such that for every N and every A ⊆ {1, ..., N},

  |A| ≥ N exp(-c (log (N + 2))^(1/8))

forces A to contain a nontrivial 3-term arithmetic progression.
```

Equivalent extremal-function form:

```text
r_3(N) = O(N exp(-c (log (N + 2))^(1/8))).
```

## Why `1 / 8`

This is the correct first benchmark because:

- `1 / 8` is already the first explicit intermediate exponent isolated quantitatively in the
  repository;
- it is the strongest exact intermediate scale currently justified by the local theorem program;
- choosing `1 / 2` would violate the “smaller debt” requirement;
- choosing a vague exponent `α > 1 / 9` would fail the exactness requirement.

## Why This Still Counts As A Direct Counting Target

The theorem remains outside the exhausted family because it is stated directly on `A ⊆ [N]`.

It does **not** presuppose:

- the split-to-matched-profile coupling layer;
- the current almost-periodicity / Bohr-set recurrence;
- the current negative architecture.

It only reuses `1 / 8` as the first exact benchmark scale, not as evidence for the proof method.

## What Is Deliberately Not Claimed

The note does **not** claim a quantitative lower bound

```text
T_3(A) ≥ Φ(|A|, N)
```

because no exact non-artificial candidate `Φ` has been isolated in the repository yet.

So the minimal honest target is the existence-form direct theorem at exponent `1 / 8`.

## Route Consequence

```text
The direct counting route should now be narrowed from “full Behrend-scale upper theorem”
to “direct `1 / 8` theorem on A ⊆ [N]”.
```

If even this narrower direct target cannot be reduced further or connected to a concrete
counting/stability lemma, then the direct-counting fork should be closed as too coarse.
