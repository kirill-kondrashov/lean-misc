# Plan: `k = 3` Behrend-Scale Upper Route

Date: 2026-03-08

## Objective

Follow the stronger natural `k = 3` route centered on the target

```math
\texttt{bound\_targets.k3\_behrend\_scale\_upper\_profile},
```

that is,

```math
\exists c>0,\ \exists C>0,\quad
r_3(N)=O\!\left(C\,N\exp(-c\sqrt{\log(N+2)})\right).
```

## Status

Progress: `█████-` `5 / 6` milestones

## Milestones

1. `[x]` Freeze the exact stronger upper target in Lean.
   - `bound_targets.k3_behrend_scale_upper_profile`

2. `[x]` Add the literature-side wrapper and extracted upper witness.
   - `LiteratureK3BehrendScaleUpperSourceAssumptions`
   - imported upper witness with exponent `β = 1/2`

3. `[x]` Identify the minimal extra same-scale comparison input.
   - `import_targets.k3_behrend_scale_constant_order_target`
   - meaning: the upper decay constant must be at most the lower Behrend constant

4. `[x]` Prove the exact downstream consequence of steps 1-3.
   - analytic lemma:
     `k3_behrend_lower_template_dominance_of_beta_eq_half_and_constant_order`
   - branch-local consequence:
     `k3_behrend_scale_split_profile_of_literatureK3BehrendScaleOrderedSourceAssumptions`

5. `[x]` Reassess whether the stronger upper theorem alone is enough for a full matched-profile
   closure.
   - verdict: no
   - reason: same `sqrt(log)` scale is not enough by itself; constant alignment still matters
   - Lean route now makes that dependency explicit through:
     `LiteratureK3BehrendScaleOrderedSourceAssumptions`
     and
     `k3_behrend_scale_split_profile_of_literatureK3BehrendScaleOrderedSourceAssumptions`

6. `[ ]` Prove or import `bound_targets.k3_behrend_scale_upper_profile`.
   - this is external mathematical debt, not yet source-backed in the repository

## Mathematical Status

Current exact route:

```text
stronger upper theorem
  + same-scale constant order
  -> Behrend-scale split theorem for k = 3
```

What is now explicit:

```text
proving only the stronger upper theorem is not yet the same as proving the full k = 3 branch
inside the current matched-profile formal route
```

The live remaining debt is therefore twofold:

1. actually prove/import the stronger upper theorem
2. separately justify the same-scale constant-order input, if the goal remains the current
   matched-profile interface
