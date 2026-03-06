# Notes: Problem #142 Main-Gap Feasibility Audit (2026-03-05)

## Scope

Audit the current main gap encoded in:

- `ErdosProblems/Problem142Gap.lean`
- `ErdosProblems/Problem142Literature.lean`

Goal: decide whether each imported witness interface can be instantiated now from known
literature-shaped targets already represented in this repository, or whether interface
redesign is required.

## Inputs Used

1. Gap packaging:
   - `Erdos142.MainTheoreticalGap`
   - `Erdos142.Problem142ImportedWitnessBundle`
2. Witness obligations:
   - `Erdos142.K3ProfileWitnessImported`
   - `Erdos142.K4ProfileWitnessImported`
   - `Erdos142.Kge5ProfileWitnessImported`
3. Literature-shape targets:
   - `Erdos142.bound_targets.k3_superpolylog_upper_profile`
   - `Erdos142.bound_targets.k3_behrend_lower_profile`
   - `Erdos142.bound_targets.k4_polylog_upper_profile`
   - `Erdos142.bound_targets.kge5_iteratedlog_upper_profile`
4. Repository status + bibliography anchors:
   - `README.md` ("Erdős #142: current status and references")
   - cited works: Kelley-Meka (2023), Green-Tao (2017), Leng-Sah-Sawhney (2024)

## Branch-by-Branch Feasibility Table

| Branch | Witness obligation (current gap) | Best available local literature-shape support | Lean-shape verdict | Decision |
|---|---|---|---|---|
| `k = 3` | Need one witness with both `hUpper` and `hLower` to same profile `C * N * exp(-c*(log(N+2))^β)` | Upper side aligns with `k3_superpolylog_upper_profile`; lower side available only as `k3_behrend_lower_profile` (pointwise Behrend-type shape, fixed `sqrt(log)` form) | `bridge` for upper; `not currently supported` for full two-sided matched witness | `redesign required` |
| `k = 4` | Need one witness with both `hUpper` and `hLower` to same profile `C * N / (log(N+2))^c` | Upper side aligns with `k4_polylog_upper_profile`; no matching lower profile target in current literature-assumption layer | `direct` for upper; `not currently supported` for lower | `redesign required` |
| `k >= 5` | Need family witness (`forall k >= 5`) with both `hUpper` and `hLower` to profile `C * N / (log(log(N+3)))^c` | Upper side aligns with `kge5_iteratedlog_upper_profile`; no matching lower profile target in current layer | `direct` for upper; `not currently supported` for lower | `redesign required` |

## Main Theoretical Gap (Explicit)

The bottleneck is not upper-bound formalization. The bottleneck is the current requirement of
two-sided matched-profile witnesses in all three branches, especially:

- missing lower-profile obligations for `k = 4` and `k >= 5`
- profile-coupling mismatch for `k = 3` (current lower benchmark shape is not yet wired as a
  matched `isBigO` witness to the same parameterized profile used by the upper side)

So the current `MainTheoreticalGap` is stronger than what the present literature-shape layer
honestly supports.

## Blocked Planes: Elimination Report (This Step)

1. Over-strong interface plane
   - Status: diagnosed active.
   - Elimination action: require interface split/redesign before witness instantiation work.

2. Source-to-Lean statement mismatch plane
   - Status: partially eliminated on upper sides (all branches have direct or near-direct shapes).
   - Remaining: lower-side statement shapes.

3. Asymptotic normalization plane
   - Status: still open for `k = 3` lower-to-witness bridge details (`sqrt(log)` and normed `isBigO`).

4. Branch coupling plane
   - Status: diagnosed active.
   - Elimination action: stop forcing one two-sided schema across all branches.

## Recommended Next Step

Proceed to milestone 5 direction early (interface redesign), then return to milestones 2-4 with
honest branch-local targets:

1. split each branch into upper and lower witness interfaces
2. make lower-side witnesses optional/conditional where literature does not currently justify them
3. keep a separate theorem for "upper-only best-known consequences" versus "full asymptotic formula"

## Milestone-2 Execution Update (`k = 3`) (2026-03-05)

Implemented and verified in Lean (`ErdosProblems/Problem142Literature.lean`):

- `k3_behrend_lower_isBigO_of_eventual_le`
- `k3_behrend_lower_profile_implies_isBigO_lower`
- `k3_behrend_lower_isBigO_of_literature_rates`
- `k3_mixed_two_sided_profile_of_literature_rates`

What this achieved:

- We now have a formal bridge from Behrend-style eventual lower inequality to an explicit
  `isBigO` lower-profile statement in the same Behrend shape.
- We now have a formal mixed-profile two-sided `k = 3` consequence theorem
  (Behrend-shape lower + superpolylog upper), making the weaker true target explicit.

What this did not achieve:

- It does **not** instantiate `K3ProfileWitnessImported`.
- Reason: current `K3ProfileWitness` requires lower and upper bounds against one shared
  profile `C * N * exp(-c*(log(N+2))^β)`, while the available lower benchmark is fixed
  `sqrt(log)` shape and is not coupled to the upper-side `β`.

Updated `k = 3` verdict:

- `instantiate now`: no
- `redesign required`: yes (or explicit mixed-profile two-sided theorem path)

## Milestone-3/4 Execution Update (`k = 4`, `k >= 5`) (2026-03-05)

Implemented and verified in Lean (`ErdosProblems/Problem142Literature.lean`):

- `k3UpperProfileWitness_of_literatureRateAssumptions`
- `k4UpperProfileWitness_of_literatureRateAssumptions`
- `kge5UpperProfileWitness_of_literatureRateAssumptions`
- `k3UpperProfileWitnessImported_of_literatureRateAssumptions`
- `k4UpperProfileWitnessImported_of_literatureRateAssumptions`
- `kge5UpperProfileWitnessImported_of_literatureRateAssumptions`
- `upper_variant_of_literature_rates_via_upper_profile_witnesses`

What this achieved:

- The redesigned upper-only interface path is now executable from `LiteratureRateAssumptions`.
- `k = 4` and `k >= 5` upper closures are formally routed through branch-local upper witnesses.

What this did not achieve:

- It does **not** instantiate `K4ProfileWitnessImported` or `Kge5ProfileWitnessImported`.
- Reason: no matching lower-profile targets are currently available in the assumption layer.

Updated verdicts:

- `k = 4`: upper closure `yes`, full two-sided witness `no`, redesign/lower-interface split remains required.
- `k >= 5`: upper closure `yes`, full two-sided witness `no`, redesign/lower-interface split remains required.

## Cycle-2 Lower-Interface Update (2026-03-05)

Implemented and verified:

- New lower interfaces in `Problem142Literature.lean`:
  - `K3BehrendLowerProfileWitnessImported`
  - `K4LowerProfileWitnessImported`
  - `Kge5LowerProfileWitnessImported`
- New lower extraction theorems:
  - `k3_behrend_lower_profile_of_imported_witness`
  - `k4_lower_profile_of_imported_witness`
  - `kge5_lower_profile_of_imported_witness`
- New lower-gap packaging in `Problem142Gap.lean`:
  - `MainLowerGap`
  - `lower_profile_data_of_main_lower_gap`

Meaning:

- lower-side research debt is now represented as first-class interfaces (not only implicit blockers)
- `k=3` Behrend-lower route is wired from `LiteratureRateAssumptions`
- `k=4` and `k>=5` lower interfaces remain intentionally uninstantiated by current literature layer

## Cycle-3 Split-Gap Update (2026-03-05)

Implemented and verified:

- Mixed-profile imported-split witness theorems in `Problem142Literature.lean`:
  - `k3_mixed_two_sided_profile_of_imported_split_witnesses`
  - `k4_mixed_two_sided_profile_of_imported_split_witnesses`
  - `kge5_mixed_two_sided_profile_of_imported_split_witnesses`
- Combined split-gap packaging in `Problem142Gap.lean`:
  - `MainSplitGap`
  - `split_gap_data_of_main_split_gap`

Meaning:

- The split model is now operational: one bundle provides upper consequences, lower-profile data,
  and mixed-profile two-sided branch data in a single theorem surface.
- This still does not close the full `MainTheoreticalGap`; it clarifies and stabilizes the honest
  frontier statements around it.

## Cycle-4 Comparison-Lemma Update (2026-03-05)

Implemented and verified in `Problem142Gap.lean`:

- `mainUpperGap_of_mainTheoreticalGap`
- `upper_variant_of_mainTheoreticalGap`
- `mainSplitGap_of_mainTheoreticalGap_and_k3BehrendLower`
- `split_gap_data_of_mainTheoreticalGap_and_k3BehrendLower`

Meaning:

- The gap-surface implication map is now explicit:
  - full two-sided main gap implies upper-gap consequences
  - full two-sided main gap plus `k=3` Behrend-lower witness implies split-gap data
- This formally identifies a concrete “missing bridge” between strong full interfaces and the
  split mixed-profile frontier.

## Cycle-5 Coupling-Assumption Update (2026-03-06)

Implemented and verified in `Problem142Gap.lean`:

- `SplitGapToMainTheoreticalGapAssumptions`
- `mainTheoreticalGap_of_mainSplitGap_and_assumptions`
- `erdos_problem_142_of_mainSplitGap_and_assumptions`

Meaning:

- The remaining split-to-full promotion step is now a named assumption surface.
- Future progress can target these coupling fields directly, branch by branch, instead of
  implicitly reasoning over the full theorem.

## Cycle-5 Implication Graph (Explicit)

Current formal edge map:

1. `MainTheoreticalGap -> MainUpperGap`
   - `mainUpperGap_of_mainTheoreticalGap`
   - consequence theorem: `upper_variant_of_mainTheoreticalGap`

2. `MainTheoreticalGap + K3BehrendLowerProfileWitnessImported -> MainSplitGap`
   - `mainSplitGap_of_mainTheoreticalGap_and_k3BehrendLower`
   - consequence theorem:
     `split_gap_data_of_mainTheoreticalGap_and_k3BehrendLower`

3. `MainSplitGap + SplitGapToMainTheoreticalGapAssumptions -> MainTheoreticalGap`
   - `mainTheoreticalGap_of_mainSplitGap_and_assumptions`
   - consequence theorem:
     `erdos_problem_142_of_mainSplitGap_and_assumptions`

Interpretation:

- Edge (2) encodes the currently identified extra ingredient needed to pass from strong full
  witnesses to split mixed-profile data (`k=3` Behrend-lower witness).
- Edge (3) encodes the unresolved coupling mathematics as an explicit assumption package.
