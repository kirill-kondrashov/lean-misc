# Note: Stronger Upper Theorem Needed for Full `k = 3`

Date: 2026-03-08

## Context

The repository now proves the strongest honest base-axiom `k = 3` source-backed split statement:

```math
L_3(N)=O(r_3(N)), \qquad r_3(N)=O(U_3(N)), \qquad L_3(N)=O(U_3(N)).
```

with

```math
L_3(N)\asymp N\exp\!\bigl(-c_\ell \sqrt{\log N}\bigr)
```

and current source-backed upper exponent

```math
\beta = \frac{1}{12}, \qquad
U_3(N)\asymp N\exp\!\bigl(-c_u(\log N)^\beta\bigr).
```

This does **not** yet yield a matched asymptotic profile

```math
r_3(N)=\Theta(f(N)).
```

## Missing Mathematical Input

On the current matched-profile route, the missing comparison is

```math
U_3(N)=O(L_3(N)).
```

Equivalently, the missing theorem is a stronger upper bound of Behrend scale:

```math
\exists c>0,\ \exists C>0\ \text{such that}\ 
r_3(N)\le C\,N\exp\!\bigl(-c\sqrt{\log N}\bigr)
\quad\text{for all sufficiently large }N.
```

In Landau notation:

```math
r_3(N)=O\!\left(N\exp(-c\sqrt{\log N})\right).
```

Since the repository already has a Behrend-type lower bound

```math
N\exp\!\bigl(-c'\sqrt{\log N}\bigr)=O(r_3(N)),
```

this stronger upper theorem would close the current `k = 3` gap.

## Sufficient Comparison Forms

Any one of the following would be sufficient for the current formal route:

1. A direct Behrend-scale upper theorem:

   ```math
   r_3(N)=O\!\left(N\exp(-c\sqrt{\log N})\right).
   ```

2. A superpolylog upper theorem with exponent strictly larger than one half:

   ```math
   r_3(N)=O\!\left(N\exp(-c(\log N)^\beta)\right),
   \qquad \beta>\frac12.
   ```

3. A borderline square-root theorem with explicit constant comparison:

   ```math
   r_3(N)=O\!\left(N\exp(-c_u\sqrt{\log N})\right)
   ```

   with `c_u` strong enough to dominate the Behrend lower-side constant.

## Current Obstruction

The current source-backed import fixes

```math
\beta = \frac{1}{12},
```

so option `2` is not supplied by the existing literature layer in this repository.

Therefore the full `k = 3` asymptotic-formula theorem remains blocked, while the
source-backed split theorem is complete.
