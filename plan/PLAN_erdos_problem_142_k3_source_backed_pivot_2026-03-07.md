# Plan: Erdős #142 `k=3` Source-Backed Pivot (2026-03-07)

## Objective

Close the failed `β > 1 / 2` elimination route and pivot the active `k=3` work toward the
strongest theorem shape that is actually supported by the Kelley-Meka source audit.

The new goal is not to force a matched full-profile `k=3` witness. It is to make the current
source-backed `k=3` consequence explicit, stable, and first-class in the Lean surface.

## Progress Bar

- `k=3` source-backed pivot: `6 / 6` completed
- Progress: `[####################]` `100%`

## Fixed Facts From The Completed Audit

1. The old active route is closed.
   - The `β > 1 / 2` comparison path is not source-backed by the current Kelley-Meka extraction.

2. The current source-backed exponent visible from the paper is:
   - `β = 1 / 12`

3. So the strongest currently justified `k=3` upper-side shape is of the form

```text
r_3(N) =O N * exp(-c * (log N)^(1/12)).
```

4. The current lower-side shape remains Behrend-type:

```text
N * exp(-c * sqrt(log N)) =O r_3(N).
```

5. Since `1 / 12 < 1 / 2`, the old desired dominance direction

```text
upper =O lower
```

is false for the extracted source regime. The honest asymptotic relation is the reverse-direction
sandwich compatibility:

```text
lower =O upper.
```

## Pivot Target

Replace the old active `k=3` search target

- `splitGap_k3_upper_exponent_gt_half_frontier`

with a source-backed explicit `k=3` split theorem surface that records:

- a Kelley-Meka-style upper template with fixed visible exponent `1 / 12`,
- a Behrend-style lower template,
- and the true relation between those two templates.

This pivot keeps the repo mathematically honest and avoids spending more cycles on a route that is
already audited to failure.

## Milestones

1. **Define an explicit source-backed `k=3` upper target** — `completed`
   - Add a new benchmark target in `Problem142.lean` that captures the currently extracted
     Kelley-Meka shape with visible exponent `1 / 12`.
   - Keep it separate from the weaker existential target
     `bound_targets.k3_superpolylog_upper_profile`.
   - Implemented:
     - `bound_targets.k3_superpolylog_upper_profile_one_twelfth`
     - `k3_superpolylog_upper_profile_of_one_twelfth`

2. **Thread the explicit `1 / 12` source target through the literature layer** — `completed`
   - Add a dedicated literature-side wrapper for the explicit source-backed target.
   - Provide the corresponding imported upper witness extraction in
     `Problem142Literature.lean`.
   - Implemented:
     - `LiteratureK3OneTwelfthSourceAssumptions`
     - `k3_superpolylog_upper_profile_of_literatureK3OneTwelfthSourceAssumptions`
     - `k3UpperProfileWitness_of_literatureK3OneTwelfthSourceAssumptions`

3. **Prove the true template relation for the pivoted `k=3` shapes** — `completed`
   - Show the Behrend lower template is `IsBigO` of the explicit Kelley-Meka upper template.
   - Do not try to recover the false converse direction.
   - Implemented in reusable form:
     - `k3_behrend_decay_template_dominance_of_beta_lt_half`
     - `k3_behrend_to_upper_profile_transport`
     - `k3_behrend_lower_template_dominance_of_beta_lt_half`

4. **Package the source-backed `k=3` split theorem as a first-class output** — `completed`
   - Add a named theorem or witness bundle in `Problem142Gap.lean` for the explicit `k=3`
     sandwich:
     - lower Behrend shape,
     - upper Kelley-Meka `1 / 12` shape,
     - and their compatibility.
   - Implemented:
     - `K3SourceBackedSplitWitness`
     - `k3UpperProfileWitness_beta_eq_one_twelfth_of_literatureK3OneTwelfthSourceAssumptions`
     - `k3SourceBackedSplitWitness_of_literatureK3OneTwelfthSourceAssumptions`
     - `K3SourceBackedSplitGap`
     - `mainSplitGap_of_k3SourceBackedSplitGap_and_frontierRest`
     - `k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions`

5. **Demote the old `β > 1 / 2` route from active search status** — `completed`
   - Keep the old material as a completed failed audit, not as the next recommended path.
   - Update plan references and feasibility notes so the active next-cycle file is this pivot.

6. **Reassess what remains feasible after the pivot** — `completed`
   - Decide whether the strongest honest `k=3` endpoint should be:
     - an explicit split theorem only,
     - a new source-backed interface replacing the failed matched-profile search,
     - or a broader redesign of `MainSplitGap` / coupling usage.
   - Verdict:
     - the strongest honest local `k=3` endpoint is now the source-backed split package
       `K3SourceBackedSplitGap`;
     - `K3ProfileWitnessImported` remains out of reach for the current source-backed route;
     - further work should redesign downstream planning around this split surface instead of
       returning to the `β > 1 / 2` path.

## Blocked Planes To Eliminate

1. **Dead-route repetition plane**
   - Risk: continue optimizing the already-failed `β > 1 / 2` path.
   - Elimination:
     - make the pivoted source-backed target the new active route.

2. **Existential-source blur plane**
   - Risk: keep only an existential `β > 0` statement and lose the explicit extracted exponent.
   - Elimination:
     - add a fixed source-backed `1 / 12` target.

3. **Over-strong witness plane**
   - Risk: keep searching for matched-profile `K3ProfileWitnessImported` even though the
     extracted source supports only a split sandwich.
   - Elimination:
     - package the split theorem itself as a primary output.

## Success Criterion

This pivot succeeds if:

- the old `β > 1 / 2` route is explicitly retired from active search,
- the repo contains a first-class, source-backed explicit `k=3` theorem surface using the extracted
  Kelley-Meka exponent `1 / 12`,
- and the next practical work on `k=3` no longer depends on the false comparison direction.

## Failure Criterion

This pivot fails if we still cannot state the strongest source-backed `k=3` theorem without
dragging the design back toward the false matched-profile target.

In that case, the next move is a broader interface redesign, not another local lemma search.
