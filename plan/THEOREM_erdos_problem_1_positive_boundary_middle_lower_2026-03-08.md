# Theorem note: positive-boundary middle lower bound for Erdős Problem #1

## Statement

Let

- `A = {a_1, ..., a_n} ⊆ {1, 2, ..., N}`
- all subset sums of `A` be distinct

and write

- `T := sum(A) = a_1 + ... + a_n`

Define the positive boundary family

`B^+(A) := { S ⊆ A : T < 2 sum(S) and there exists a in S with 2 sum(S \ {a}) < T }`.

Then the frontier theorem is:

`A != ∅  =>  |B^+(A)| >= C(n, floor(n/2))`.

Here `C(n,k)` means the binomial coefficient `n choose k`.

## Meaning of the terms

### `sum(S)`

For a finite subset `S ⊆ A`,

`sum(S) := sum_{x in S} x`.

### `T = sum(A)`

This is the total sum of all elements of `A`.

### The condition `T < 2 sum(S)`

This means

`sum(S) > T / 2`.

So `S` lies strictly above the half-sum threshold.

### The condition `2 sum(S \ {a}) < T`

This means

`sum(S \ {a}) < T / 2`.

So after deleting one suitable element `a`, the subset drops strictly below the half-sum threshold.

### Therefore `B^+(A)` is the positive boundary

The family `B^+(A)` consists exactly of those subsets `S` which sit just above the threshold
`T/2`, in the sense that one deletion can move them below it.

In cube language:

- vertices are subsets `S ⊆ A`
- moving along one edge means inserting or deleting one element
- the "negative half" is
  `{ S ⊆ A : 2 sum(S) < T }`
- `B^+(A)` is the outer vertex boundary of that half

restricted to the positive side.

## Why this theorem matters

The Lean file

- `ErdosProblems/Problem1LowerExactCore.lean`

already proves the counting upper bound

`|B^+(A)| <= N`

for every sum-distinct `A ⊆ {1, ..., N}`.

The proof is:

1. if `S in B^+(A)`, then
   `T/2 < sum(S) <= T/2 + N`
2. distinct subset sums imply the values `sum(S)` for `S in B^+(A)` are all distinct
3. there are at most `N` integers in the interval `(T/2, T/2 + N]`

So if one proves, for nonempty `A`,

`|B^+(A)| >= C(n, floor(n/2))`,

then immediately

`C(n, floor(n/2)) <= N`.

This is exactly the exact Dubroff-Fox-Xu lower bound for the integer version of Erdős Problem #1.

## Equivalent theorem package

The frontier theorem can be packaged as:

`forall A ⊆ {1,...,N} with distinct subset sums,`

`C(|A|, floor(|A|/2)) <= |B^+(A)|`.

Combining this with the already proved upper bound

`|B^+(A)| <= N`

gives

`C(|A|, floor(|A|/2)) <= N`.

## Relation to the Harper viewpoint

This is a Harper-type vertex-isoperimetric statement on the Boolean cube.

The expected proof shape is:

1. form the lower half
   `G(A) := { S ⊆ A : 2 sum(S) < T }`
2. use distinct subset sums to show `|G(A)| = 2^(n-1)`
3. apply a half-cube boundary lower bound
   `|∂^+ G(A)| >= C(n, floor(n/2))`
4. identify `∂^+ G(A)` with `B^+(A)`

So the present frontier is the combinatorial boundary-lower step of the exact theorem.
