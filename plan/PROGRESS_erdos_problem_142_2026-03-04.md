# Progress Update: Erdős Problem #142 (2026-03-04)

## Scope of this iteration

Executed the first concrete steps from `PLAN_erdos_problem_142.md`:

1. Added bound-target scaffolding aligned with cited literature.
2. Added a first unconditional nontrivial theorem about `r_k(N)`.
3. Added a structured assumptions layer for deep external results.

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

## Validation

- `make build` passed.
- `make check` passed.
- `make verify` passed.

## What this does **not** accomplish

- Does not prove `ErdosProblems.erdos_problem_142`.
- Does not formalize full deep upper-bound proofs from the cited literature yet.

## Next execution targets

1. Add one more unconditional exact-value family beyond `k = 2` (or prove impossibility/limits
   for immediate next cases) to keep the finite API growth disciplined.
2. Reduce assumptions of `lower_variant_two_of_growth` by proving/importing a reusable growth lemma
   for `‖N / log N‖ → ∞` in the nat-indexed real setting.
