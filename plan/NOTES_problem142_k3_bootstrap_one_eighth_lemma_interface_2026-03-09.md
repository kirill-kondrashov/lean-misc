# Notes: Erdős #142 `k = 3` Bootstrap `1 / 8` Lemma Interface

Date: 2026-03-09

## Objective

Name the exact strengthened lemma interface that would make the local `1 / 8` theorem program
mathematically concrete.

## Exact Strengthened Lemma Interface

The closest theorem-shaped local target to the present architecture is:

```text
Improved almost-periodicity -> structured-Bohr-set bootstrap lemma.

Input:
the same Kelley--Meka / Bloom--Sisask almost-periodicity hypotheses currently used in the
integer-case `k = 3` density-increment step, inside a regular Bohr set of rank d and
relative density α, with L := log(2 / α).

Output:
a successor structured Bohr set with

  rank ≤ d + O(L^5),

  size ≥ exp(-O(d L + L^6)) times the previous size,

and the same multiplicative density increment

  α' ≥ (1 + c) α.
```

This is the exact local lemma whose existence would realize the recurrence replacement computed in
`NOTES_problem142_k3_bootstrap_one_eighth_theorem_candidate_2026-03-09.md`.

## Minimal Lean-Facing Consequence

If that strengthened lemma is available, the immediate repository path is:

1. derive the improved recurrence;
2. close the recurrence into an explicit upper theorem at exponent `1 / 8`;
3. reuse the existing one-eighth wrappers already present in the repository.

Those reusable wrappers are:

- `bound_targets.k3_superpolylog_upper_profile_one_eighth`
- `erdos_142_three_source_backed_split_one_eighth`
- `erdos_142_three_source_backed_split_one_eighth_of_bounds`

## Remaining Local Theorem Debt

The strengthened lemma alone is still not the final Lean endpoint.
One more local theorem is needed:

```text
recurrence-closing theorem:
the improved iteration implies the explicit `β = 1 / 8` upper profile.
```

So the proof decomposition is:

1. improved bootstrap lemma;
2. recurrence-closing `1 / 8` upper theorem;
3. reuse existing split packaging.

## Scoping Verdict

```text
The route is concrete enough to stay active.
It now has one exact strengthened lemma target and one exact recurrence-closing theorem target.
```
