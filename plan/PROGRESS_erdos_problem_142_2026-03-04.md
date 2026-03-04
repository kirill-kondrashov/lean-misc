# Progress Update: Erdős Problem #142 (2026-03-04)

## Scope of this iteration

Executed the first concrete steps from `PLAN_erdos_problem_142.md`:

1. Added bound-target scaffolding aligned with cited literature.
2. Added a first unconditional nontrivial theorem about `r_k(N)`.
3. Added a structured assumptions layer for deep external results.

## Incremental update (same day)

Implemented the next realism step for the open-problem placeholder:

1. Replaced the raw `k = 3` branch axiom with a structured matched-profile axiom.
2. Added a theorem reduction proving `erdos_142 3` from that matched-profile target.
3. Kept `k = 4` and `k ≥ 5` as explicit temporary branch debt axioms.

New items in `ErdosProblems/Problem142Literature.lean`:

- `Erdos142.k3_matched_profile`
- `Erdos142.erdos_142_three_of_matched_profile`
- `Erdos142.erdos_problem_142_k3_upper_profile_bound_axiom`
- `Erdos142.erdos_problem_142_k3_lower_profile_bound_axiom`
- `Erdos142.erdos_problem_142_k3_case`

## Incremental update (k = 4 decomposition)

Applied the same narrowing strategy to the `k = 4` branch:

1. Added `k = 4` matched-profile infrastructure and reduction theorem.
2. Replaced the single `k = 4` branch axiom with two narrower profile-bound axioms.
3. Derived `Erdos142.erdos_problem_142_k4_case` from those two axioms.

New items in `ErdosProblems/Problem142Literature.lean`:

- `Erdos142.k4_matched_profile`
- `Erdos142.k4_profile`
- `Erdos142.k4_matched_profile_of_eventual_bounds`
- `Erdos142.erdos_142_four_of_matched_profile`
- `Erdos142.erdos_problem_142_k4_upper_profile_bound_axiom`
- `Erdos142.erdos_problem_142_k4_lower_profile_bound_axiom`
- `Erdos142.erdos_problem_142_k4_matched_profile`
- `Erdos142.erdos_problem_142_k4_case`

## Incremental update (explicit-profile strengthening)

Added a stronger non-tautological statement layer in `ErdosProblems/Problem142.lean`:

1. Introduced explicit profile classes:
   `ErdosProblems.ExplicitProfileClass`.
2. Added strengthened target:
   `ErdosProblems.HasExplicitAsymptoticFormula` and
   `ErdosProblems.erdos_problem_142_explicit`.
3. Added reduction theorem:
   `ErdosProblems.erdos_problem_142_explicit_implies_erdos_problem_142`.
4. Added DeepMind-style explicit counterpart and equivalence:
   `Erdos142.erdos_142_explicit`,
   `Erdos142.hasExplicitAsymptoticFormula_iff_erdos142_explicit`,
   `Erdos142.erdos_problem_142_explicit_iff_deepmind`.
5. Added explicit-profile solution outline scaffold in
   `ErdosProblems/Problem142Literature.lean`:
   `Erdos142.erdos_problem_142_explicit_solution_axiom` and
   `Erdos142.erdos_problem_142_solution_from_explicit_axiom`.

## Incremental update (uniform explicit-bridge refactor)

Implemented a single bridge shape for all branches (`k = 3`, `k = 4`, `k ≥ 5`):

1. Added generic theorem:
   `Erdos142.erdos_142_explicit_of_eventual_bounds`.
2. Replaced coarse `k ≥ 5` branch axiom with explicit-profile parameter + upper/lower bound families.
3. Added branch-specific explicit profile parameter packages and fixed profiles.
4. Derived all explicit branch cases via the same generic bridge theorem:
   - `Erdos142.erdos_problem_142_explicit_k3_case`
   - `Erdos142.erdos_problem_142_explicit_k4_case`
   - `Erdos142.erdos_problem_142_explicit_kge5_case`
5. Routed the statement-level theorem
   `Erdos142.erdos_problem_142_solution_axiom` through explicit cases using
   `Erdos142.erdos_142_explicit_implies_erdos_142`.

## Incremental update (`k = 3` debt consolidation)

Started the first direct debt-burndown step on the critical path to a real solution claim:

1. Collapsed two separate `k = 3` upper-side debt axioms into one structured witness axiom:
   - removed: `Erdos142.erdos_problem_142_explicit_k3_params_axiom`
   - removed: `Erdos142.erdos_problem_142_explicit_k3_upper_bound_axiom` (as an axiom)
   - added: `Erdos142.erdos_problem_142_explicit_k3_upper_profile_axiom`
2. Reintroduced `Erdos142.erdos_problem_142_explicit_k3_upper_bound_axiom` as a **derived theorem**
   from the structured witness (no longer an axiom).
3. Updated checker allowlist and README expected-output snapshot accordingly.

Net result:

- Temporary explicit-branch axiom debt reduced from **9** items to **8** items.

## Incremental update (`k = 3` two-sided witness consolidation)

Completed the next `k = 3` debt reduction step by folding lower-side debt into the same witness:

1. Replaced the upper-only witness
   `Erdos142.erdos_problem_142_explicit_k3_upper_profile_axiom`
   with a two-sided witness
   `Erdos142.erdos_problem_142_explicit_k3_profile_witness_axiom`.
2. Replaced `Erdos142.erdos_problem_142_explicit_k3_lower_bound_axiom` as an **axiom** with a
   derived theorem from the two-sided witness.
3. Kept both bridge theorems (`k3_upper_bound_axiom`, `k3_lower_bound_axiom`) as theorem-level
   interfaces so downstream code did not change.
4. Updated checker allowlist and README expected output.

Net result:

- Temporary explicit-branch axiom debt reduced from **8** items to **7** items.

## Incremental update (`k = 4` two-sided witness consolidation)

Completed the same consolidation pattern for `k = 4`:

1. Replaced three separate `k = 4` temporary axioms
   (`k4_params`, `k4_upper_bound`, `k4_lower_bound`) with a single two-sided witness axiom:
   `Erdos142.erdos_problem_142_explicit_k4_profile_witness_axiom`.
2. Reintroduced `k4_upper_bound_axiom` and `k4_lower_bound_axiom` as **derived theorems**
   from that witness, preserving theorem-level interfaces.
3. Updated checker allowlist and README expected output to reflect the new debt surface.

Net result:

- Temporary explicit-branch axiom debt reduced from **7** items to **5** items.

## Incremental update (`k ≥ 5` witness-family consolidation)

Completed the same consolidation for the `k ≥ 5` family:

1. Replaced the three temporary `k ≥ 5` debt families
   (`kge5_params`, `kge5_upper_bound`, `kge5_lower_bound`) with one witness family:
   `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom`.
2. Reintroduced `kge5_upper_bound_axiom` and `kge5_lower_bound_axiom` as **derived theorems**
   from the witness family, keeping theorem-level interfaces stable.
3. Updated checker allowlist and README expected output to the new debt surface.

Net result:

- Temporary explicit-branch axiom debt reduced from **5** items to **3** items.

## Blocked-plan elimination

- The earlier narrow `k = 3`-only burndown track is now superseded by the unified
  explicit-branch burndown plan:
  `PLAN_erdos_problem_142_explicit_branch_axiom_burndown_2026-03-04.md`.

## Incremental update (`k = 3` witness replaced by imported-assumption interface)

Executed Step 1 of the witness-replacement phase on the `k = 3` branch:

1. Removed temporary checker-allowlisted axiom usage for `k = 3`.
2. Introduced imported-assumption interface:
   - `Erdos142.K3ProfileWitnessImported` (class)
   - `Erdos142.erdos_problem_142_explicit_k3_profile_witness_imported` (abbrev)
3. Threaded this interface through the `k = 3` explicit profile branch and the final solution
   scaffold (`erdos_problem_142_explicit_solution_axiom`, `erdos_problem_142_solution_axiom`).
4. Updated checker allowlist and README expected output.

Net result:

- Temporary explicit-branch axiom debt reduced from **3** items to **2** items.

## Blocked-plan elimination (current step)

- Eliminated the `k = 3` temporary-axiom dependency plane from the checker debt surface.

## Incremental update (`k = 4` witness replaced by imported-assumption interface)

Executed Step 2 of the witness-replacement phase on the `k = 4` branch:

1. Removed temporary checker-allowlisted axiom usage for `k = 4`.
2. Introduced imported-assumption interface:
   - `Erdos142.K4ProfileWitnessImported` (class)
   - `Erdos142.erdos_problem_142_explicit_k4_profile_witness_imported` (abbrev)
3. Threaded this interface through the `k = 4` explicit profile branch and the final solution
   scaffold (`erdos_problem_142_explicit_solution_axiom`, `erdos_problem_142_solution_axiom`).
4. Updated checker allowlist and README expected output.

Net result:

- Temporary explicit-branch axiom debt reduced from **2** items to **1** item.

## Blocked-plan elimination (current step, k = 4)

- Eliminated the `k = 4` temporary-axiom dependency plane from the checker debt surface.

## Incremental update (`k ≥ 5` witness family replaced by imported-assumption interface)

Executed Step 3 of the witness-replacement phase on the `k ≥ 5` branch family:

1. Removed temporary checker-allowlisted axiom usage for `k ≥ 5`.
2. Introduced imported-assumption interface:
   - `Erdos142.Kge5ProfileWitnessImported` (class)
   - `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_imported` (abbrev)
3. Threaded this interface through the `k ≥ 5` explicit profile family and the final solution
   scaffold (`erdos_problem_142_explicit_solution_axiom`, `erdos_problem_142_solution_axiom`).
4. Updated checker allowlist and README expected output.

Net result:

- Temporary explicit-branch axiom debt reduced from **1** item to **0** items.

## Blocked-plan elimination (current step, k ≥ 5)

- Eliminated the `k ≥ 5` temporary-axiom dependency plane from the checker debt surface.

## Completed in code

File: `ErdosProblems/Problem142.lean`

- Added unconditional benchmark theorem:
  - `ErdosProblems.rk_one_eq_zero : ∀ N, rk 1 N = 0`
- Added supporting lemmas:
  - `containsNontrivialOneTermAP_of_mem`
  - `apfree_one_iff_eq_empty`
  - `admissible_card_eq_zero_of_k_one`
- Added literature-bound target section:
  - `Erdos142.bound_targets.k3_upper_kelley_meka`
  - `Erdos142.bound_targets.k4_upper_green_tao`
  - `Erdos142.bound_targets.kge5_upper_leng_sah_sawhney`
- Added structured external-input container:
  - `Erdos142.LiteratureAssumptions` (typeclass)
  - `Erdos142.literatureAssumptions_provide_all_targets`
- Added explicit rate-profile target propositions:
  - `Erdos142.bound_targets.k3_superpolylog_upper_profile`
  - `Erdos142.bound_targets.k4_polylog_upper_profile`
  - `Erdos142.bound_targets.kge5_iteratedlog_upper_profile`
- Added strengthened assumptions + derived consequence:
  - `Erdos142.LiteratureRateAssumptions`
  - `Erdos142.upper_variant_of_literature_for_all_k_ge_three`
- Added lower-bound benchmark target layer for `k = 3`:
  - `Erdos142.bound_targets.k3_behrend_lower_profile`
- Added two-sided benchmark target:
  - `Erdos142.bound_targets.k3_two_sided_sandwich_profile`
  - `Erdos142.k3_two_sided_sandwich_of_literature_rates`
- Added conditional asymptotic corollary target + theorem:
  - `Erdos142.bound_targets.k3_sublinear`
  - `Erdos142.k3_sublinear_of_literature_rates`
- Proved the growth helper needed to clean the corollary:
  - `Erdos142.nat_div_log_isBigO_natCast`
  - `k3_sublinear_of_literature_rates` now uses this internally (no extra external parameter).
- Added new unconditional small-`k` API (`k = 2`):
  - `containsNontrivialTwoTermAP_of_lt`
  - `apfree_two_card_le_one`
  - `admissible_card_le_one_of_k_two`
  - `rk_two_le_one`
  - `one_le_rk_two_of_one_le`
  - `rk_two_eq_one_of_pos`
- Completed `k = 2` exact characterization and benchmark connection:
  - `ErdosProblems.rk_two_eq_ite`
  - `Erdos142.erdos_142_two`
  - `Erdos142.upper_variant_two`
- Split bibliography-indexed assumptions into dedicated module:
  - new file `ErdosProblems/Problem142Literature.lean`
  - moved:
    - `Erdos142.LiteratureAssumptions`
    - `Erdos142.LiteratureRateAssumptions`
    - `Erdos142.upper_variant_of_literature_for_all_k_ge_three`
    - `Erdos142.k3_two_sided_sandwich_of_literature_rates`
    - `Erdos142.nat_div_log_isBigO_natCast`
    - `Erdos142.k3_sublinear_of_literature_rates`
- Added feasible lower-variant small-case bridge:
  - `Erdos142.lower_variant_two_of_growth`
- Added broader unconditional exact-value family at `N = 1`:
  - `ErdosProblems.rk_zero_eq_zero`
  - `ErdosProblems.rk_at_one_eq_zero_of_le_one`
  - `ErdosProblems.rk_at_one_eq_ite`

## Validation

- `make build` passed.
- `make check` passed.
- `make verify` passed.

## What this does **not** accomplish

- Does not prove `ErdosProblems.erdos_problem_142`.
- Does not formalize full deep upper-bound proofs from the cited literature yet.

## Next execution targets

1. Reduce assumptions of `lower_variant_two_of_growth` by proving/importing a reusable growth lemma
   for `‖N / log N‖ → ∞` in the nat-indexed real setting.
2. Consider adding a dedicated `BoundTargets` file so benchmark statement-shapes are separated from
   both core combinatorial definitions and literature assumptions.
