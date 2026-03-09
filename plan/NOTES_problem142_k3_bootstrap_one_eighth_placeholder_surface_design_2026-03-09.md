# Notes: Erdős #142 `k = 3` Bootstrap `1 / 8` Placeholder Surface Design

Date: 2026-03-09

## Objective

Choose exact placeholder names and layer boundaries for the local `1 / 8` theorem debt.

## Naming Decision

The clean design is:

1. reuse the existing recurrence-closing target

```text
bound_targets.k3_superpolylog_upper_profile_one_eighth
```

2. add exactly one new local placeholder target for the improved bootstrap step

```text
local_targets.k3_bootstrap_one_eighth_step_target
```

3. optionally add one combined package

```text
local_targets.k3_bootstrap_one_eighth_program_target
```

defined schematically as:

```text
k3_bootstrap_one_eighth_step_target
and
bound_targets.k3_superpolylog_upper_profile_one_eighth
```

## Layering Decision

### `Problem142.lean`

This is the correct home for the placeholder targets.

Reason:

- they are mathematical target surfaces;
- they are not literature-import assumptions;
- they are not gap-layer realizations.

### `Problem142Literature.lean`

Do not add a new literature/import wrapper for the bootstrap-step target.

Reason:

- the source-import branch is closed;
- `LiteratureK3OneEighthSourceAssumptions` must remain the separate conjectural import surface for
  the explicit upper theorem, not for the local bootstrap lemma.

### `Problem142Gap.lean`

Do not add a gap-layer export yet.

Reason:

- the gap layer packages realized or high-level route objects;
- this local bootstrap lemma debt is still below that layer.

## Cleanliness Test

This design is clean enough to justify a later Lean encoding cycle because it:

- introduces only one genuinely new local debt name;
- reuses the existing explicit `1 / 8` upper target instead of duplicating it;
- keeps the local theorem debt below the literature/import and gap layers.

## Verdict

```text
Outcome: clean enough for a later Lean encoding cycle.
Add one local placeholder for the bootstrap step, reuse the existing one-eighth upper target,
and do not export any of it through the gap layer yet.
```
