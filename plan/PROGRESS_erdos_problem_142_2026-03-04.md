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
