# Proof Note: Shifted First-Shell Move-Type Theorem Candidate

This note records the current theorem candidate suggested by the exact shifted first-shell data on
the stronger-than-middle-binomial branch.

## Setup

Let

```math
n = 2m+1,
\qquad
P_m := \binom{[n]}{m},
\qquad
P_{m+1} := \binom{[n]}{m+1}.
```

For

```math
F = C \cup U,
\qquad
C \subseteq P_m,
\qquad
U \subseteq P_{m+1},
\qquad
|U| = |P_m \setminus C|,
```

write

```math
\Delta(F) := |\partial^+F| - |C|.
```

Let `\mathcal E` be the two shifted equality templates:

1. the full lower layer
   ```math
   F_{\mathrm{full}} = P_m;
   ```
2. the principal-star family
   ```math
   F_{\star}
   =
   \{A \in P_m : 0 \in A\}
   \;\cup\;
   \{B \in P_{m+1} : 0 \in B\}.
   ```

The active first-shell theorem candidate concerns shifted families at template distance `2`.

## Observed First-Shell Classification

Exact shifted computation now supports the following.

### Global shell structure

For shifted odd dimensions

```math
n = 7,9,11,13,15,17,19,21,
```

the distance-`2` shell around `\mathcal E` decomposes into:

```math
1 \text{ full-lower orbit } + 4 \text{ principal-star orbits}.
```

Moreover every orbit in that shell satisfies

```math
\Delta(F) = m.
```

### Local move-type decomposition

The sharper local decomposition computation is now exact through shifted

```math
n = 7,9,11,13,15,17,19,21.
```

It shows that the distance-`2` shell splits as follows.

1. Full-lower side:
   exactly one move type,
   ```math
   (\text{lower distance}, \text{upper distance}) = (1,1),
   ```
   with multiplicity `1`.

2. Principal-star side:
   exactly three move types,
   ```math
   (0,2),\qquad (1,1),\qquad (2,0),
   ```
   with multiplicities
   ```math
   1,\qquad 2,\qquad 1.
   ```

Every one of these move types still has

```math
\Delta(F) = m.
```

So the candidate theorem is no longer just a gap statement. It is a rigid shell-classification
statement.

## Canonical Representative Shapes Suggested By The Data

The exact witnesses in low dimensions suggest the following formulas.

### Full-lower shell

The unique full-lower distance-`2` orbit appears to be

```math
C = P_m \setminus \{\{m+1,m+2,\dots,2m\}\},
\qquad
U = \{\{0,1,\dots,m\}\}.
```

That is: remove the top lex/colex lower vertex and add the bottom upper vertex.

### Principal-star `(0,2)` shell

The unique principal-star orbit with lower/upper distances `(0,2)` appears to be

```math
C = \{A \in P_m : 0 \in A\},
\qquad
U = \{B \in P_{m+1} : 0 \in B\} \cup \{\{1,2,\dots,m+1\}\}.
```

So the lower layer stays at the star template, while the upper layer gains the bottom nonzero
vertex.

### Principal-star `(2,0)` shell

The unique principal-star orbit with lower/upper distances `(2,0)` appears to be obtained by the
dual lower-layer move:

```math
C =
\bigl(\{A \in P_m : 0 \in A\} \setminus \{\{0,m+2,\dots,2m\}\}\bigr)
\cup
\{\{1,2,\dots,m\}\},
\qquad
U = \{B \in P_{m+1} : 0 \in B\}.
```

So the upper layer stays at the star template, while the lower layer swaps one top star vertex for
the bottom nonzero vertex.

### Principal-star `(1,1)` shell

There are exactly two shifted orbits of type `(1,1)`.

The new compact delta signatures isolate the two general shapes.

#### Lower-add / upper-remove class

```math
C = \{A \in P_m : 0 \in A\} \cup \{\{1,2,\dots,m\}\},
```
```math
U = \{B \in P_{m+1} : 0 \in B\} \setminus \{\{0,m+2,\dots,2m\}\}.
```

So one first-shell orbit is obtained by adding the bottom nonzero lower vertex while removing the
top star upper vertex.

#### Lower-remove / upper-add class

```math
C = \{A \in P_m : 0 \in A\} \setminus \{\{0,m+2,\dots,2m\}\},
```
```math
U = \{B \in P_{m+1} : 0 \in B\} \cup \{\{1,2,\dots,m+1\}\}.
```

So the other first-shell orbit is obtained by removing the top star lower vertex while adding the
bottom nonzero upper vertex.

## Current Conjectural Theorem

The most concrete current shell theorem candidate is:

```math
\operatorname{dist}(F,\mathcal E)=2
\quad\Longrightarrow\quad
\Delta(F)=m,
```

and the stronger refinement is:

```math
\operatorname{dist}(F,\mathcal E)=2
\quad\Longrightarrow\quad
F \text{ lies in exactly one of the five shell orbits above.}
```

This would be the first real theorem on the way to the additive improvement

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

## Current Status

- The scalar first-shell law `\Delta(F)=m` is exact in shifted data through `n = 25`.
- The sharper move-type decomposition is exact through `n = 21`.
- The compact delta-signature output now isolates all five distance-`2` shifted shell orbits
  symbolically through `n = 21`:
  `1` full-lower orbit plus `4` principal-star orbits.
- The shifted `n = 23` decomposition probe now returns as well, with aggregate profile
  `entry_count = 6` and `pair_count = 7`, consistent with the same
  `2` equality entries plus `4` distance-`2` move-type entries.
- What is still missing is a clean theorem-facing extraction of the exact `n = 23` move rows from
  the verbose witness output; so the fully tabulated move-type statement in this note remains
  recorded only through `n = 21`.

So this note should be read as a theorem candidate backed by exact evidence, not yet as a proof.
