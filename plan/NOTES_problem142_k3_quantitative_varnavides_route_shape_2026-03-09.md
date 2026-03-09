# Notes: Erdős #142 `k = 3` Quantitative Varnavides Route Shape

Date: 2026-03-09

## Objective

Decide the repository-facing layer for the quantitative Varnavides reduction and identify the
first downstream consequence worth targeting.

## Layer Decision

The correct home is:

```text
Problem142Literature.lean
namespace import_targets
```

Reason:

- the theorem is source-backed and import-facing;
- it is a reduction theorem, not a public branch endpoint;
- it should not enter `Problem142Gap.lean` until it supports a genuine higher-level route object.

The raw progression-count statement should **not** be the first encoded repository target.

Reason:

- the current repo has `rk`, progression-freeness, and extremal-set APIs;
- it does not yet have a formal progression-count object `T3(A)`;
- forcing that API now would inflate the route before the reduction is even integrated.

## First Downstream Consequence

The first repository-facing consequence worth targeting is the extremal transport inequality:

```text
for 1 ≤ M ≤ N,

  r3(N) ≤ ((r3(M) + 1) / M) N

up to the obvious real-cast formatting.
```

This is the right first consequence because it:

- is exact;
- uses only existing repo objects;
- is strictly smaller than the full direct `1 / 8` theorem;
- turns the source theorem into an immediately reusable extremal-function reduction.

## Consequence For The Route

The active successor should therefore be:

```text
encode/import the extremal transport target first,
then decide what subscale upper input would make it produce a useful direct-counting theorem.
```

Not:

```text
encode the full T3-count theorem first;
or jump directly to a public direct `1 / 8` theorem surface.
```

## Verdict

```text
The route is now localized.
The first repository-facing theorem debt is the literature-layer extremal transport target,
not the raw progression-count formula and not the final direct theorem.
```
