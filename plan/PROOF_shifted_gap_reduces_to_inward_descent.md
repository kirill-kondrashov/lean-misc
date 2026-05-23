# Proof Note: Shifted Gap Reduces To Subcritical Inward Descent

This note records a corrected reduction of the two live stronger-branch blockers to a single
structural descent theorem in the shifted two-layer class.

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

Let the two shifted model templates be

```math
F_{\mathrm{full}} := P_m,
```

and

```math
F_\star
:=
\{A \in P_m : 0 \in A\}
\cup
\{B \in P_{m+1} : 0 \in B\}.
```

Define the shifted template distance

```math
d(F)
:=
\min\bigl(
|F \triangle F_{\mathrm{full}}|,
\ |F \triangle F_\star|
\bigr).
```

Because all balanced two-layer families in this problem have the same cardinality as
`F_full` and `F_star`, the quantity `d(F)` is always even.

## The Strong Inward-Descent Candidate Is False

The first natural candidate was:

### Strong Inward Descent

For every shifted balanced two-layer family `F` with

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\qquad\text{and}\qquad
d(F)\ge 4,
```

there exists another shifted balanced two-layer family `F'` such that

```math
d(F') = d(F)-2
```

and

```math
\Delta(F') \le \Delta(F).
\tag{ID}_{\mathrm{strong}}
```

This statement is false already in shifted `n=5`.

Indeed, the exact shell profile there is:

```math
d=4:\ \Delta(F)=3\ \text{for every shifted family,}
```

but

```math
d=6:\ \text{there exists a shifted family with }\Delta(F)=2.
```

So a shifted family at distance `6` and defect `2` cannot descend to distance `4` without
increasing defect.

An explicit shifted `n=5` witness is:

```math
C=\{\{0,1\},\{0,2\},\{1,2\},\{0,3\},\{1,3\},\{0,4\},\{1,4\}\},
```
```math
U=\{\{0,1,2\},\{0,1,3\},\{0,1,4\}\},
```

for which

```math
d(F)=6,
\qquad
\Delta(F)=2.
```

Since every shifted family at distance `4` has defect `3`, no `F'` with

```math
d(F')=4
\quad\text{and}\quad
\Delta(F')\le 2
```

exists.

So the unconditional inward-descent theorem must be archived.

## The Corrected Theorem Candidate

What we actually need is weaker:

### Subcritical Inward Descent

For every shifted balanced two-layer family `F` with

```math
F \notin \{F_{\mathrm{full}}, F_\star\},
\qquad
d(F)\ge 4,
\qquad
\Delta(F)<m,
```

there exists another shifted balanced two-layer family `F'` such that

```math
d(F') = d(F)-2
```

and

```math
\Delta(F') \le \Delta(F).
\tag{ID}_{<m}
```

The `n=5` counterexample above does not contradict this corrected version, because there
`\Delta(F)=2=m`.

However, even `(ID)_{<m}` is stronger than what the active route actually needs.

## The Minimal Counterexample-Descent Theorem

The exact statement needed by the stronger branch is only:

### Subcritical Counterexample Descent

For every shifted balanced two-layer family `F` with

```math
F \notin \{F_{\mathrm{full}}, F_\star\},
\qquad
d(F)\ge 4,
\qquad
\Delta(F)<m,
```

there exists another shifted balanced two-layer family `F'` such that

```math
d(F') = d(F)-2
```

and

```math
\Delta(F') < m.
\tag{CED}_{<m}
```

This is strictly weaker than `(ID)_{<m}` because it does not require

```math
\Delta(F')\le \Delta(F).
```

It only asks that subcriticality survive one inward step.

## What The Existing First-Shell Theorem Already Gives

By
[PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md),
every shifted family with template distance `2` belongs to one of the five first-shell classes,
and hence satisfies

```math
d(F)=2
\quad\Longrightarrow\quad
\Delta(F)=m.
\tag{FS}
```

So the only missing step on the stronger branch is to force every non-template shifted family down
to that first shell without increasing defect.

## Consequence: Equality Classification

Assume `(CED)_{<m}` and `(FS)`.

We claim that

```math
\Delta(F)=0
\quad\Longrightarrow\quad
F \in \{F_{\mathrm{full}}, F_\star\}.
\tag{EQ}
```

Proof:

- suppose `F` is shifted, `\Delta(F)=0`, and `F` is not a model template;
- if `d(F)=2`, then `(FS)` gives `\Delta(F)=m`, contradiction;
- so `d(F)\ge 4`;
- since `0<m`, we have `\Delta(F)<m`;
- by `(CED)_{<m}`, there is a shifted `F_1` with
  `d(F_1)=d(F)-2` and `\Delta(F_1)<m`;
- repeat until reaching a shifted family `F_k` with `d(F_k)=2`;
- then `(FS)` gives `\Delta(F_k)=m`, contradiction.

So no non-template shifted family can have defect `0`.

## Consequence: Global `+m` Gap

Assume `(CED)_{<m}` and `(FS)`.

We claim that

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\quad\Longrightarrow\quad
\Delta(F)\ge m.
\tag{GAP}
```

Proof:

- let `F` be shifted and non-template;
- assume toward contradiction that `\Delta(F)<m`;
- if `d(F)=2`, then `(FS)` gives `\Delta(F)=m`;
- if `d(F)\ge 4`, repeatedly apply `(CED)` until reaching a shifted family `F_k` with
  `d(F_k)=2` and still `\Delta(F_k)<m`;
- but `(FS)` gives `\Delta(F_k)=m`;
- contradiction.

So the full shifted `+m` gap follows.

## Consequence For The Active Program

The two live stronger-branch blockers are therefore reduced to a single auxiliary theorem:

```math
\text{prove subcritical counterexample descent from distance } d\ge 4
\text{ to distance } d-2.
```

Together with the already-proved first-shell theorem, that one statement implies both:

- shifted equality classification;
- shifted global `+m` stability.

## Why This Is Better Than More Brute Force

This reduction identifies the exact missing theorem shape:

- not more shell data,
- not more template-attribution bookkeeping,
- but a monotone structural descent theorem inside the shifted class, only below the threshold
  `\Delta(F)<m`.

So the next theorem-facing work should be judged by whether it helps prove `(CED)_{<m}`.

The current preferred local target is now the averaging reduction in
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md):
it is enough to construct admissible inward moves and prove that their uniform or weighted average
defect does not exceed `\Delta(F)`.
