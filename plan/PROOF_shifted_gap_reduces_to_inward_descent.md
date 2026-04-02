# Proof Note: Shifted Gap Reduces To Inward Descent

This note records a clean reduction of the two live stronger-branch blockers to a single
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

## The Inward-Descent Theorem Candidate

The single structural statement we now want is:

### Inward Descent

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
\tag{ID}
```

This is exactly the theorem-first replacement for further brute-force shell extension.

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

Assume `(ID)` and `(FS)`.

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
- by `(ID)`, there is a shifted `F_1` with
  `d(F_1)=d(F)-2` and `\Delta(F_1)\le \Delta(F)=0`;
- repeat until reaching a shifted family `F_k` with `d(F_k)=2`;
- then `(FS)` gives `\Delta(F_k)=m`, contradiction.

So no non-template shifted family can have defect `0`.

## Consequence: Global `+m` Gap

Assume `(ID)` and `(FS)`.

We claim that

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\quad\Longrightarrow\quad
\Delta(F)\ge m.
\tag{GAP}
```

Proof:

- let `F` be shifted and non-template;
- if `d(F)=2`, then `(FS)` gives `\Delta(F)=m`;
- if `d(F)\ge 4`, repeatedly apply `(ID)` until reaching a shifted family `F_k` with `d(F_k)=2`;
- along the chain,
  ```math
  \Delta(F_k)\le \Delta(F);
  ```
- but `(FS)` gives `\Delta(F_k)=m`;
- hence `m \le \Delta(F)`.

So the full shifted `+m` gap follows.

## Consequence For The Active Program

The two live stronger-branch blockers are therefore reduced to a single auxiliary theorem:

```math
\text{prove inward defect-nonincreasing descent from distance } d\ge 4
\text{ to distance } d-2.
```

Together with the already-proved first-shell theorem, that one statement implies both:

- shifted equality classification;
- shifted global `+m` stability.

## Why This Is Better Than More Brute Force

This reduction identifies the exact missing theorem shape:

- not more shell data,
- not more template-attribution bookkeeping,
- but a monotone structural descent theorem inside the shifted class.

So the next theorem-facing work should be judged by whether it helps prove `(ID)`.
