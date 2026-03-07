# Plan: Erdős #142 Post-`k=3` Split-Gap Redesign (2026-03-07)

## Objective

Treat `K3SourceBackedSplitGap` as the fixed honest `k=3` endpoint and redesign downstream gap
planning so the repository no longer models `k=3` as if it were waiting for the failed
matched-profile `β > 1 / 2` route.

## Progress Bar

- Post-`k=3` split-gap redesign: `5 / 6` completed
- Progress: `[#################---]` `83%`

## Fixed Premises

1. `K3SourceBackedSplitGap` is now implemented and verified.
   - It packages:
     - one explicit Kelley-Meka upper witness with `β = 1 / 12`,
     - one Behrend lower witness,
     - and the true compatibility direction
       `k3_behrend_lower_template =O k3_upper_profile`.

2. The old `k=3` matched-profile elimination route is closed.
   - The current Kelley-Meka extraction does not support `β > 1 / 2`.

3. The remaining non-base frontier is therefore structurally asymmetric:
   - `k=3`: honest split surface exists.
   - `k=4`: coupling/lower-profile frontier remains open.
   - `k≥5`: coupling/lower-profile frontier remains open.

## Milestones

1. **Freeze the honest `k=3` endpoint** — `completed`
   - Treat `K3SourceBackedSplitGap` as the canonical local `k=3` package.

2. **Create an active redesign plan that starts from that premise** — `completed`
   - This file is the active next-cycle plan.

3. **Inventory every downstream use of uniform split-to-full coupling** — `completed`
   - Trace all uses of:
     - `SplitGapToMainTheoreticalGapAssumptions`
     - `mainTheoreticalGap_of_mainSplitGap_and_assumptions`
     - `erdos_problem_142_of_mainSplitGap_and_frontier`
   - Goal:
     - separate places that truly need full matched-profile witnesses
       from places that only need the weaker `k=3` split package.
   - Inventory result in `Problem142Gap.lean`:
     - definition site:
       - [Problem142Gap.lean:246](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:246)
         `SplitGapToMainTheoreticalGapAssumptions` itself still requires one uniform field for each
         of `k=3`, `k=4`, `k≥5`.
     - package constructors:
       - [Problem142Gap.lean:331](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:331)
         `splitGapToMainTheoreticalGapAssumptions_frontier`
       - [Problem142Gap.lean:341](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:341)
         `splitGapToMainTheoreticalGapAssumptions_of_literatureK3ExponentGtHalf_frontierRest`
       - [Problem142Gap.lean:371](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:371)
         `splitGapToMainTheoreticalGapAssumptions_of_importTargets`
       - these are the exact constructors that still force `k=3` into the same coupling package as
         the unresolved `k=4` and `k≥5` branches.
     - projection/helper site:
       - [Problem142Gap.lean:383](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:383)
         `coupling_targets_of_splitGapToMainTheoreticalGapAssumptions`
       - this theorem preserves the old uniform triple API.
     - main consumer:
       - [Problem142Gap.lean:391](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:391)
         `mainTheoreticalGap_of_mainSplitGap_and_assumptions`
       - this is the core place where `MainSplitGap` plus the uniform coupling package is promoted
         to `MainTheoreticalGap`.
     - statement-level wrappers:
       - [Problem142Gap.lean:407](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:407)
         `erdos_problem_142_of_mainSplitGap_and_assumptions`
       - [Problem142Gap.lean:415](/home/kir/pers/lean-misc/ErdosProblems/Problem142Gap.lean:415)
         `erdos_problem_142_of_mainSplitGap_and_frontier`
       - these are downstream consequence surfaces that should eventually be rerouted through the
         redesigned asymmetric interface.

4. **Design a replacement interface for the asymmetric frontier** — `completed`
   - Candidate direction:
     - replace the current uniform coupling package with a structure whose `k=3` field is
       `K3SourceBackedSplitGap`-based, while only `k=4` and `k≥5` remain as true open coupling
       targets.
   - Implemented in `Problem142Gap.lean`:
     - `Problem142K3ResolvedSplitImportedWitnessBundle`
     - `MainK3ResolvedSplitGap`
     - `Problem142K3ResolvedImportedWitnessBundle`
     - `MainK3ResolvedGap`
     - `K3ResolvedSplitGapToMainK3ResolvedGapAssumptions`
   - Meaning:
     - the repo now has an explicit asymmetric post-pivot surface;
     - `k=3` is no longer modeled as one more unresolved matched-profile coupling field.

5. **Implement a non-breaking bridge layer** — `completed`
   - Add wrappers or new theorems so existing split-gap results stay usable while the stronger
     full-gap path remains explicit and conjectural.
   - Implemented in `Problem142Gap.lean`:
     - `mainK3ResolvedSplitGap_of_instances`
     - `mainK3ResolvedSplitGap_of_mainSplitGap_and_k3SourceBackedSplitGap`
     - `mainSplitGap_of_mainK3ResolvedSplitGap`
     - `split_gap_data_of_mainK3ResolvedSplitGap`
     - `mainK3ResolvedGap_of_mainK3ResolvedSplitGap_and_assumptions`
     - `mainK3ResolvedGap_of_mainSplitGap_and_k3SourceBackedSplitGap_and_assumptions`
     - `mainUpperGap_of_mainK3ResolvedGap`
     - `upper_variant_of_mainK3ResolvedGap`
     - `mainK3ResolvedSplitGap_of_mainK3ResolvedGap`
   - Meaning:
     - the new asymmetric interface is now compatible with existing split-gap and upper-gap
       consequence surfaces.

6. **Reassess theorem targets after the redesign** — `pending`
   - Decide whether the new practical target should be:
     - a refined split theorem package,
     - a partially coupled theorem (`k=3` resolved, `k=4`/`k≥5` frontier),
     - or a renamed stronger conjectural surface replacing the current full-gap presentation.

## Blocked Planes To Eliminate

1. **Uniform-coupling plane**
   - Risk:
     - keep pretending `k=3`, `k=4`, and `k≥5` are the same kind of missing input.
   - Elimination:
     - redesign the interface so only the genuinely unresolved branches stay on the frontier.

2. **Dead-route leakage plane**
   - Risk:
     - keep routing downstream plans through `splitGap_k3_upper_exponent_gt_half_frontier`.
   - Elimination:
     - make `K3SourceBackedSplitGap` the only active `k=3` planning surface.

3. **False-completion plane**
   - Risk:
     - blur the distinction between “honest split theorem” and “full Erdős #142 solution”.
   - Elimination:
     - keep the redesigned full-gap target explicit and separate from the source-backed `k=3`
       split package.

## Success Criterion

This redesign cycle succeeds if the next implementation patch can point to a downstream interface
where `k=3` is represented by `K3SourceBackedSplitGap` rather than by the failed matched-profile
elimination route.

## Immediate Implementation Target

Reassess the theorem targets after the redesign:

- decide whether `MainK3ResolvedGap` should become the practical downstream target,
- identify whether any legacy names around `MainTheoreticalGap` should now be marked more clearly as
  stronger conjectural surfaces,
- and decide whether the remaining active research frontier should be stated purely as the
  `k=4` / `k≥5` coupling problem.
