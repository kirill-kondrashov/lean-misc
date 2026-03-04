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

## Validation

- `make build` passed.
- `make check` passed.
- `make verify` passed.

## What this does **not** accomplish

- Does not prove `ErdosProblems.erdos_problem_142`.
- Does not formalize full deep upper-bound proofs from the cited literature yet.

## Next execution targets

1. Prove additional unconditional lemmas for small `k, N` to harden the combinatorial API.
2. Split bibliography-indexed assumptions into a dedicated file to keep statement signatures,
   provenance, and consequences modular.
