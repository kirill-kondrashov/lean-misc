# Notes: Erdős #1 exact values audit (2026-03-07)

## Scope

This note tracks the exact-value branch for the minimal ambient size

```math
a(n) = \min \{ N : \exists A \subseteq \{1, \dots, N\},\ |A| = n,\ A \text{ sum-distinct}\}.
```

In the local Lean files, the currently relevant theorem surfaces are:

- `Erdos1.erdos_1.variants.least_N_3`
- `Erdos1.erdos_1.variants.least_N_5`
- `Erdos1.erdos_1.variants.least_N_9`

## Source status

- OEIS A276661 lists:
  - `a(3) = 4`
  - `a(5) = 13`
  - `a(9) = 161`
  - `a(10) = 309`
- As of March 7, 2026, the local repo proves `a(3) = 4` and `a(5) = 13` by finite verification.
- `a(9) = 161` is still only an axiom-level statement in Lean.
- `a(10) = 309` is not yet represented in the Lean surface.

## Feasibility split

### 1. Small finite-search values

`a(3)` and `a(5)` are small enough for direct `native_decide` over
`(Finset.Icc 1 N).powersetCard k`.

This approach succeeded locally for:

- nonexistence at `N = 12`, `k = 5`
- existence at `N = 13`, `k = 5`

### 2. Medium exact values

For `a(9) = 161`, a direct kernel-level exhaustive search over
`(Finset.Icc 1 161).powersetCard 9` is not a good default route.

The search space size is:

```math
\binom{161}{9},
```

which is far too large for a naive `native_decide` certificate strategy.

### 3. Better certificate strategy

The realistic route for `a(9)` and `a(10)` is:

1. external verified search or certificate generation,
2. export a compact witness/nonexistence certificate,
3. check the certificate in Lean with a small trusted kernel proof script.

This should avoid asking Lean to perform the entire combinatorial search.

## Recommended next theorem targets

1. Add a theorem surface for `a(10) = 309` in the same style as `least_N_9`, but keep it
   separate from proof implementation until a certificate format exists.
2. Decide a certificate representation for:
   - one witness set at the claimed optimum,
   - one nonexistence certificate for the predecessor ambient size.
3. Keep exact-value proofs separate from asymptotic/literature imports; they are a different
   engineering problem.

## Recommended implementation shape

- Add a future module or helper file for exact-value certificates if this branch grows.
- Keep the search/generation tool outside the kernel.
- Keep the Lean side minimal:
  - parse certificate,
  - verify subset bounds,
  - verify subset-sum injectivity or nonexistence reduction,
  - conclude `IsLeast`.

## Concrete next actions

1. Add a theorem declaration for `a(10) = 309` if exact-value coverage is desired in the public
   API.
2. Prototype an external search script for witness checking on `k = 9` and `k = 10`.
3. Design a certificate format small enough to be checked quickly in Lean.

## Source anchor

- OEIS A276661: <https://oeis.org/A276661>
