# Plan: `k = 3` Behrend-Scale Upper Program (Strict Rewrite)

Date: 2026-03-08

## Purpose

Replace the earlier high-level `k = 3` Behrend-scale program by a stricter research plan.

The key correction is:

```text
do not treat the Behrend-scale upper theorem as an active live route
until the current modern proof architecture has been quantified precisely enough
to show that improving one local step would materially move the final exponent.
```

## Exact Target

The desired upper theorem is:

```math
\exists c>0,\ \exists C>0,\ \exists N_0\in\mathbb{N}
\text{ such that }
\forall N\ge N_0,\quad
r_3(N)\le C\,N\exp\!\bigl(-c\sqrt{\log(N+2)}\bigr).
```

Equivalently:

```math
r_3(N)=O\!\left(N\exp(-c\sqrt{\log(N+2)})\right).
```

Here

```math
r_3(N)=\max\Bigl\{|A|:\ A\subseteq\{1,\dots,N\},\ A\text{ contains no nontrivial }3\text{-AP}\Bigr\}.
```

## Why The Earlier Plan Was Too Weak

The earlier plan named a bottleneck, but did not yet force the one thing that matters:

```text
write down the exact quantitative recurrence that produces the current exponent.
```

Without that recurrence, the sentence

```text
improve the almost-periodicity bootstrapping step
```

is not yet a proof program. It is only a diagnosis.

## New Order Of Attack

### Step 1. Quantify the current architecture before trying to improve it

Extract from the modern Kelley--Meka / Bloom--Sisask line an explicit recurrence of the form

```math
\alpha_{j+1}\ge \alpha_j + \Delta(\alpha_j),
\qquad
N_{j+1}\ge F(\alpha_j)\,N_j,
```

or an equivalent multiplicative version

```math
\alpha_{j+1}\ge (1+\eta(\alpha_j))\alpha_j,
\qquad
N_{j+1}\ge F(\alpha_j)\,N_j.
```

Definitions:

- `\alpha_j` is the density of the progression-free set after the `j`-th density increment step.
- `N_j` is the ambient scale after the `j`-th restriction to a structured object.
- `\Delta(\alpha)` or `\eta(\alpha)` measures the size of the density increment.
- `F(\alpha)` measures the fraction of ambient size retained at each step.

This is the real quantitative core of any upper-bound proof.

### Step 2. Recover the exponent `1/9` from that recurrence

Do not rely on verbal source summaries. Compute explicitly how the present recurrence yields

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/9}\bigr).
```

This step has one purpose:

```text
identify exactly which parameter combination determines the final exponent.
```

Until this is written down, there is no disciplined way to judge whether a local theorem
improvement matters.

### Step 3. Isolate the local theorem debt in exact quantitative form

Only after Step 2 should the local bottleneck be stated as a theorem target.

The source-backed diagnosis currently points to:

```text
almost-period set -> structured subspace / Bohr set
```

But the target must be made explicit. For example:

```math
\text{If }T\text{ is a set of almost-periods of density }\tau,
\text{ then there exists a structured object }B
\text{ with }
\operatorname{rk}(B)\le R(\tau,\alpha),\ |B|\ge S(\tau,\alpha)|G|.
```

or in the finite-field model:

```math
T \leadsto V\le \mathbb{F}_p^n,
\qquad
\operatorname{codim}(V)\le C(\tau,\alpha).
```

This step should produce one exact replacement theorem candidate, not a family of informal wishes.

### Step 4. Compute what exponent that stronger local theorem would imply

Suppose the local replacement theorem from Step 3 were true. Plug its parameters back into the
recurrence from Step 1.

Then answer a concrete question:

```text
What final exponent would that stronger local theorem actually yield?
```

This is the critical discipline the earlier plan lacked.

Possible outcomes:

1. it only recovers the source-mentioned `1/8` improvement;
2. it reaches some intermediate exponent `\alpha > 1/9`;
3. it still cannot plausibly approach `1/2`;
4. it actually leaves a path toward `1/2`.

### Step 5. Run the negative program before committing to the Behrend-scale target

If Step 4 shows that even a strong local improvement cannot push the exponent close to `1/2`,
then the correct theorem to pursue is a negative one:

```text
the current Kelley--Meka / Bloom--Sisask architecture cannot by itself reach Behrend scale.
```

This is not failure. It is a clean research outcome.

Mathematically, it means proving that under the present density-increment mechanism and present
structured-object conversion costs, the best attainable exponent remains bounded away from `1/2`.

### Step 6. Only then decide whether the Behrend-scale theorem remains the right target

After Steps 1-5, there are three possibilities:

1. the current architecture still has a credible route toward `1/2`;
2. the current architecture can improve, but only to a smaller exponent;
3. the current architecture is fundamentally misaligned with the Behrend-scale target.

Only in case `1` should

```math
\texttt{bound\_targets.k3\_behrend\_scale\_upper\_profile}
```

remain the active theorem target.

In cases `2` or `3`, the honest next target is either:

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^\alpha\bigr)
\quad\text{for some explicit }\alpha>1/9,
```

or a structural negative result about the current method.

## Active Deliverables

The strict plan therefore has these deliverables, in order:

1. exact recurrence extraction for the modern proof line;
2. exact derivation of the current `1/9` exponent from that recurrence;
3. one explicit local replacement theorem candidate;
4. an exponent propagation calculation for that candidate;
5. a viability verdict for the Behrend-scale target.

## Milestones

Progress: `██████` `6 / 6`

1. `[x]` Critique the earlier high-level plan and identify the missing quantitative layer.
2. `[x]` Extract the exact density/scale recurrence underlying the current `1/9` upper bound.
   - note: `NOTES_problem142_k3_upper_recurrence_extraction_2026-03-08.md`
3. `[x]` Re-derive the `1/9` exponent from that recurrence inside repository notes.
   - result: the chain `O(L^6)` rank increment per step + `O(L)` steps + `exp(-O(d_j L + L^7))` size loss per step yields cumulative size `exp(-O(L^9))N`, hence final exponent `1/9`
4. `[x]` State one exact local replacement theorem with explicit parameter gains.
   - note: `NOTES_problem142_k3_upper_local_replacement_candidate_2026-03-08.md`
   - candidate recurrence: `d_{j+1} <= d_j + O(L^5)` and `|B_{j+1}| >= exp(-O(d_j L + L^6)) |B_j|`
5. `[x]` Compute the exponent implied by that replacement theorem.
   - propagated exponent: `1/8`, not `1/2`
6. `[x]` Decide whether the Behrend-scale target remains viable, or pivot to a weaker theorem or
   a negative result.
   - verdict: pivot
   - reason: the first concrete source-motivated local improvement only reaches exponent `1/8`, so the Behrend-scale target is not a live route on the present architecture

## Current Verdict

```text
The earlier plan was too optimistic.
The active route should not be “improve the bottleneck and hope for 1/2”.
The active route should be:
  quantify the architecture,
  compute the exponent,
  test one explicit replacement theorem,
  and only then judge viability of the Behrend-scale target.
```
