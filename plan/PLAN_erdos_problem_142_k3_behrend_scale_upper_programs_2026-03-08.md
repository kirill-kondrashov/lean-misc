# Plan: `k = 3` Programs Toward `bound_targets.k3_behrend_scale_upper_profile`

Date: 2026-03-08

Superseded as the active roadmap by:

- `PLAN_erdos_problem_142_k3_behrend_scale_upper_programs_strict_2026-03-08.md`

This file is kept as the earlier broad ranking of possible routes.

## Objective

Organize the plausible mathematical programs for proving the stronger upper target

```math
\texttt{bound\_targets.k3\_behrend\_scale\_upper\_profile},
```

namely

```math
\exists c>0,\ \exists C>0,\quad
r_3(N)=O\!\left(C\,N\exp(-c\sqrt{\log(N+2)})\right).
```

This is the mathematically natural upper theorem that would close the `k = 3` branch if it were
paired with the existing Behrend-scale lower bound.

## Status

Progress: `████--` `4 / 6` milestones

## Exact Target

The branch target is:

```math
\exists c>0,\ \exists C>0,\ \exists N_0\in\mathbb{N}
\text{ such that }
\forall N\ge N_0,\quad
r_3(N)\le C\,N\exp\!\bigl(-c\sqrt{\log(N+2)}\bigr).
```

Equivalently, for every set

```math
A\subseteq\{1,\dots,N\}
```

with no nontrivial `3`-term arithmetic progression,

```math
|A|\le C\,N\exp\!\bigl(-c\sqrt{\log(N+2)}\bigr)
```

for all sufficiently large `N`.

## Program Ranking

### 1. Active program: strengthen the modern upper-bound line

Route:

```text
Bloom-Sisask / Kelley-Meka style upper bounds
  -> identify the current exponent-loss bottleneck
  -> prove a sharper replacement theorem
  -> push the exponent toward 1/2
```

Current source-backed state:

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/9}\bigr)
```

is available in the literature, while the target is

```math
r_3(N)\ll N\exp\!\bigl(-c\sqrt{\log N}\bigr).
```

Why this is ranked first:
- closest to current best published results
- naturally aligned with the current Lean target
- likely to expose a concrete bottleneck theorem rather than a vague global gap

Immediate subgoals:
1. isolate the exact step in the current upper-bound architecture responsible for the `1/9`
   exponent barrier
2. formulate a local stronger statement that would increase the exponent
3. test whether that stronger statement is plausible or known in adjacent work

### 2. Near-term fallback: intermediate-exponent ladder

Route:

```math
\forall \alpha<\tfrac12,\quad
r_3(N)\ll N\exp\!\bigl(-c_\alpha(\log N)^\alpha\bigr)
```

as an incremental target family.

Why this is useful:
- turns one hard endpoint problem into a continuum of nearby problems
- gives a way to detect whether the barrier is qualitative or only quantitative
- follows Tao-style advice: solve weaker nearby problems first

Decision criterion:
- if even modest improvements beyond `1/9` look inaccessible with the current machinery,
  then the active architecture is likely the wrong one

### 3. Structural research branch: new density-increment architecture

Target style:

```text
new increment mechanism with lower entropy loss per iteration
  -> enough iterations survive down to density exp(-c sqrt(log N))
```

This is the most natural route if the modern almost-periodicity machinery has a genuine
exponent barrier.

Why it is not ranked first:
- mathematically plausible
- but currently too underspecified to be the active implementation plan

### 4. Counting/supersaturation branch

Target theorem shape:

```math
|A|\ge N\exp\!\bigl(-c\sqrt{\log N}\bigr)
\implies T_3(A)\ge 1,
```

or ideally

```math
T_3(A)\ge \Phi(|A|,N)
```

for a quantitative lower bound `\Phi`.

Why this matters:
- it would prove the upper theorem directly
- it bypasses the exact current split/matched-profile formal route

Why it is off-path for now:
- no specific source or partial theorem in the repo currently points to this route

### 5. Geometric/classification branch

Program:

```text
classify near-extremal 3-AP-free sets near Behrend scale
  -> show only Behrend-like geometry is possible
  -> deduce matching upper bound
```

Why it is attractive:
- it matches the lower-bound geometry directly
- if successful, it could give the most conceptually satisfying closure theorem

Why it is low-ranked:
- currently the least concrete program
- no local literature evidence suggests this is close to available technology

### 6. Negative/bottleneck program

Goal:

```text
prove that the present Kelley-Meka / Bloom-Sisask mechanism cannot by itself reach 1/2
```

This would not prove the target, but it would unstick the plan by identifying the exact new
ingredient required.

Why it is important:
- prevents wasting time optimizing a dead architecture
- often the fastest way to clarify the real theorem debt

## Recommended Active Sequence

1. Keep Program `1` as the active mathematical program.
2. Use Program `6` in parallel as a diagnostic program.
3. Use Program `2` as the first fallback if Program `1` cannot be localized to a concrete
   bottleneck theorem.
4. Keep Programs `3`-`5` off-path until a concrete local obstruction is identified.

## Milestones

1. `[x]` State the exact Behrend-scale target in repository notation.
2. `[x]` Rank the plausible proof programs.
3. `[x]` Audit the modern upper-bound architecture for a concrete exponent-loss bottleneck.
   - outcome: localized to almost-periodicity bootstrapping, with a separate integer-case Bohr loss
   - note: `NOTES_problem142_k3_upper_bottleneck_audit_2026-03-08.md`
4. `[x]` Formulate one local stronger theorem that would raise the exponent beyond `1/9`.
   - target: a sharper bootstrapping theorem for turning almost-period sets into structured
     subspaces/Bohr sets with better codimension/rank loss
   - immediate benchmark: recover the source-mentioned omitted `1/8`-type improvement
5. `[ ]` Decide whether Program `1` remains viable or must be replaced by Program `6`.
6. `[ ]` If Program `1` fails, pivot explicitly to an intermediate-exponent or negative result
   plan.

## Current Verdict

```text
The repository can now state the exact stronger k = 3 target cleanly.
It cannot currently prove it.
The most credible proof program is still a strengthening of the modern upper-bound line,
but only if a specific exponent-loss bottleneck can be isolated.
Otherwise the correct next move is a negative/bottleneck program, not blind iteration.
```
