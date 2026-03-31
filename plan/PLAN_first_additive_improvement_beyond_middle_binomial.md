# Plan: First Additive Improvement Beyond The Middle-Binomial Bound

This note records the first concrete strengthening target beyond the current literature-level
benchmark

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

## Proposed Next Bound

The current best explicit next target is

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

For odd `n = 2m+1`, this is

```math
N \ge \binom{2m+1}{m} + m.
```

This is the smallest nontrivial strengthening currently suggested by the shifted-shell data that
also appears dimension-stable.

## Why This Is The Right Next Target

On the stronger two-layer branch, the first nontrivial shifted shell is the template-distance `2`
shell. Its exact minimum gap is now:

- shifted `n = 5`:
  ```math
  |\partial^+F| - |C| = 2;
  ```
- shifted `n = 7`:
  ```math
  |\partial^+F| - |C| = 3;
  ```
- shifted `n = 9`:
  ```math
  |\partial^+F| - |C| = 4;
  ```
- shifted `n = 11`:
  ```math
  |\partial^+F| - |C| = 5.
  ```
- shifted `n = 13`:
  ```math
  |\partial^+F| - |C| = 6.
  ```

So the first-shell minimum gap currently matches

```math
m = \frac{n-1}{2}.
```

This is stronger than the earlier fallback target

```math
\binom{n}{\lfloor n/2\rfloor} + 1,
```

and is the first additive improvement that now looks structurally plausible across several
dimensions.

The current computational frontier for this first-shell check is now:

- exact support through shifted `n = 13`;
- the same first-shell local probe is already slow at shifted `n = 15`.

## Conjectural Two-Layer Form

Let

```math
F := \left(\binom{[n]}{m}\setminus V\right)\cup U,
\qquad
n = 2m+1,
\qquad
|U| = |V|.
```

Let `\mathcal E` be the two shifted equality templates:

1. the full lower layer;
2. the principal-star two-layer family.

The current first concrete conjecture is:

```math
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| \ge |C| + m.
```

At the shifted level, this can be broken into two increasingly realistic statements.

### Shifted Version A

For shifted `F`,

```math
\operatorname{dist}(F,\mathcal E) = 2
\quad\Longrightarrow\quad
|\partial^+F| - |C| = m.
```

### Shifted Version B

For shifted `F`,

```math
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| - |C| \ge m.
```

Version A is directly supported by exact data in `n = 5,7,9,11,13`. Version B is the actual
target needed for the first additive literature improvement.

## How This Connects To The Sum-Distinct Transport

The current formal route already reduces the middle-binomial benchmark to the exact two-layer
theorem

```math
|\partial^+F| \ge |C|.
```

So the additive improvement program is:

1. prove the stronger two-layer estimate
   ```math
   |\partial^+F| \ge |C| + m
   ```
   on the transported family class, or at least on shifted families first;
2. prove that the transported sum-distinct families never realize the equality templates;
3. use the same arithmetic closure mechanism to upgrade the endpoint to
   ```math
   N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
   ```

## Immediate Research Program

### Step 1. Prove Shifted Equality Classification

Promote the two shifted equality templates from computational evidence to theorem status.

### Step 2. Prove The Shifted First-Shell Formula

Prove:

```math
\operatorname{dist}(F,\mathcal E)=2
\quad\Longrightarrow\quad
|\partial^+F|-|C| = m.
```

This is the most concrete theorem now strongly suggested by exact data.
It is also the current best-supported theorem that points directly to the additive `+m` target.

### Step 3. Prove Shifted Lower Bounds Beyond The First Shell

Prove:

```math
\operatorname{dist}(F,\mathcal E)\ge 2
\quad\Longrightarrow\quad
|\partial^+F|-|C| \ge m.
```

This is weaker than a full shell-envelope formula, but already enough for the additive target.

### Step 4. Exclude Equality Templates For Transported Families

Show the transported two-layer family coming from a sum-distinct set cannot be one of the equality
templates. Since template distance changes in even steps, that should force

```math
\operatorname{dist}(F,\mathcal E)\ge 2.
```

### Step 5. Close The First Additive Improvement

Combine Steps 3 and 4 with the existing formal endpoint route to obtain

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

## Why We Focus On This Instead Of A Larger Target

There may be stronger true bounds. But this one has three advantages:

- it is already suggested by exact data in four odd dimensions;
- it is naturally tied to the first nontrivial shell around the equality templates;
- it is strong enough to be a genuine literature improvement while still looking reachable from
  the current two-layer route.

So this is now the best explicit “next theorem” target beyond the current middle-binomial
benchmark.
