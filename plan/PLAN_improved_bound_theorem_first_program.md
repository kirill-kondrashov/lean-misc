# Plan: Improved-Bound Theorem-First Program

This note records the revised research program for the first genuine improvement beyond

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

The target remains

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

The computational phase has now done its job. It identified the right templates, the right local
first-shell law, and the right half-cube reformulation. From this point on, the branch should be
treated as theorem-first, not frontier-chasing.

## What Is Frozen

The following are now stable inputs, not active brute-force objectives:

- the two candidate equality templates `F_full` and `F_star`;
- the lifted Hamming-ball templates `B(emptyset,m)` and `B({0},m)`;
- the complete shifted distance-`2` shell around the two model templates;
- the local first-shell identity
  ```math
  \Delta(F)=m;
  ```
- sizable local zero-defect exclusion near the templates.

Further `n -> n+2` scans are out of scope unless they settle a specific structural sublemma for a
live blocker.

## The Two Live Blockers

The stronger route is now exactly the pair of shifted two-layer theorems

```math
\Delta(F)=0
\quad\Longrightarrow\quad
F \in \{F_{\mathrm{full}}, F_\star\},
\tag{EQ}
```

and

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\quad\Longrightarrow\quad
\Delta(F)\ge m.
\tag{GAP}
```

By the half-cube bridge, these are equivalent to the two lifted Hamming-ball statements.

## Revised Research Program

The key reduction note is now
[PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md):
the original unconditional inward-descent theorem is false already in shifted `n=5`, but the
corrected route can be weakened further to what is actually needed: once one proves subcritical
counterexample descent for shifted families with `d>=4` and `Delta(F)<m`, the already-proved
first-shell theorem implies both live blockers `(EQ)` and `(GAP)`.

The current preferred proof architecture for that corrected theorem is now
[PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md).
It treats the shifted subcritical region as a discrete-gradient state space and now further reduces
the route to a local average inward-move inequality, recorded in
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md).

### Route A. Equality Classification First

Primary task:

- prove `(EQ)` directly in the shifted two-layer language;
- then transfer it to the lifted half-cube language.

Expected proof shape:

1. characterize zero-defect shifted families as exact minimizers of the one-sided boundary;
2. show any shifted zero-defect family has the same local saturation pattern as one of the two
   model templates;
3. conclude the family is exactly `F_full` or `F_star`.

### Route B. Minimal Positive Defect Reduces To The First Shell

Primary task:

- prove the inward-descent theorem from
  [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md):
  every shifted non-template family with template distance at least `4` and defect below `m`
  admits an inward simplification step reducing the template distance by `2` while staying below
  the threshold `m`.

If this is proved, then the already-established first-shell theorem immediately yields both
`(EQ)` and `(GAP)`.

The new active proof sketch for this route is the discrete-Morse / corner-slide program in
[PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md),
with the local defect step now isolated as an average inward-move inequality in
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md).

### Route C. Template-Directed Simplification

Auxiliary theorem candidate:

```math
\text{every shifted non-template } F
\text{ admits a defect-nonincreasing simplification chain}
```

ending at either

- one of the two templates, or
- one of the five distance-`2` shell classes.

This is useful only if it directly reduces `(EQ)` or `(GAP)`.

## Immediate Proof Tasks

The next proof-facing tasks are:

1. prove that any shifted zero-defect family cannot differ from a model template in both a lower
   and an upper extreme position simultaneously;
2. prove that any shifted family with minimal positive defect is forced into the distance-`2`
   shell;
3. prove a local average inward-move inequality for admissible corner repairs in the shifted class.

The new preferred formulation of Tasks 2 and 3 is exactly the subcritical counterexample-descent
statement plus its averaging reduction.

## Commit Rule

From this point on, the next commit should land only if it advances one of:

- shifted equality classification `(EQ)`;
- shifted global `+m` gap `(GAP)`;
- or a clearly stated auxiliary theorem that reduces one of those two blockers.

More brute-force extension in `n` is no longer a sufficient reason to commit.
