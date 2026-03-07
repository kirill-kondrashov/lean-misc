# Plan: Erdős #142 `k=3` Source-Backed Split Surface Packaging (2026-03-07)

## Objective

Package the pivoted Kelley-Meka `β = 1 / 12` route as a stable first-class Lean surface, without
pretending it closes the old matched-profile `k=3` gap.

## Progress Bar

- `k=3` split-surface packaging: `5 / 5` completed
- Progress: `[####################]` `100%`

## Milestones

1. **Define a dedicated first-class `k=3` split bundle** — `completed`
   - Implemented:
     - `K3SourceBackedSplitWitness`

2. **Make the extracted exponent explicit in code** — `completed`
   - Implemented:
     - `k3UpperProfileWitness_beta_eq_one_twelfth_of_literatureK3OneTwelfthSourceAssumptions`

3. **Construct the bundle directly from the pivoted literature layer** — `completed`
   - Implemented:
     - `k3SourceBackedSplitWitness_of_literatureK3OneTwelfthSourceAssumptions`

4. **Expose the package at the gap layer** — `completed`
   - Implemented:
     - `K3SourceBackedSplitGap`
     - `mainSplitGap_of_k3SourceBackedSplitGap_and_frontierRest`
     - `k3SourceBackedSplitGap_of_literatureK3OneTwelfthSourceAssumptions`

5. **Update repository status docs to make this the honest `k=3` endpoint** — `completed`
   - Updated:
     - `README.md`
     - `PLAN_erdos_problem_142_k3_source_backed_pivot_2026-03-07.md`
     - `PLAN_erdos_problem_142_feasibility_reassessment_2026-03-06.md`
     - `NOTES_problem142_gap_feasibility_audit.md`

## Outcome

The strongest currently justified local `k=3` statement is now explicit:

- one source-backed upper witness with exponent `β = 1 / 12`,
- one Behrend lower witness,
- and the true compatibility direction
  `k3_behrend_lower_template =O k3_upper_profile`.

This is a real theorem surface, not a placeholder for the failed `β > 1 / 2` route.

## What This Does Not Solve

- It does **not** instantiate `K3ProfileWitnessImported`.
- It does **not** remove any of the remaining non-base frontier axioms for the full
  `MainTheoreticalGap`.
- It does **not** address the unresolved `k=4` or `k≥5` lower-profile dominance gaps.

## Next Direction

Use this package as the new fixed `k=3` endpoint and redesign downstream full-gap planning around
it, rather than continuing to optimize the false matched-profile elimination route.

Active follow-up plan:

- [PLAN_erdos_problem_142_post_k3_split_gap_redesign_2026-03-07.md](PLAN_erdos_problem_142_post_k3_split_gap_redesign_2026-03-07.md)
