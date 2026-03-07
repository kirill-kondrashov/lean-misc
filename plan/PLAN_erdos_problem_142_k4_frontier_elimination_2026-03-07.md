# Plan: `k = 4` Frontier Elimination

Date: 2026-03-07

## Objective

Eliminate the explicit `k = 4` frontier axiom
`Erdos142.splitGap_k4_profile_dominance_frontier`
by proving the exact split-gap dominance target
`import_targets.split_gap_k4_profile_dominance_target`
from a mathematically honest source-side input.

This is the active `k = 4` theorem surface:

```math
\frac{C_u N}{(\log(N+2))^{c_u}}
=
O\!\left(\frac{C_\ell N}{(\log(N+2))^{c_\ell}}\right).
```

## Status

Progress: `█████-` `5 / 6` milestones

## Milestones

1. `[x]` Freeze the exact `k = 4` target.
   - Use `import_targets.split_gap_k4_profile_dominance_target` in
     `ErdosProblems/Problem142Literature.lean` as the primary theorem surface.
   - Keep `K4ProfileWitnessImported` as the downstream consumer, not as the first proof target.

2. `[x]` Prove the generic analytic comparison lemma.
   - Implement a reusable lemma showing that if
     ```math
     c_\ell \le c_u,
     ```
     then
     ```math
     \frac{C_u N}{(\log(N+2))^{c_u}}
     =
     O\!\left(\frac{C_\ell N}{(\log(N+2))^{c_\ell}}\right).
     ```
   - Implemented as:
     - `import_targets.k4_polylog_template_dominance_of_exponent_le`

3. `[x]` Make the minimal extra source-side input explicit.
   - The split witnesses alone do not imply the dominance theorem.
   - Record the missing comparison input as:
     - `import_targets.k4_exponent_order_target`
   - Add the bridge:
     - `import_targets.split_gap_k4_profile_dominance_target_of_exponent_order`

4. `[x]` Audit the actual `k = 4` literature/import layer against the new target.
   - Check whether the current upper and lower imports can honestly supply
     ```math
     c_\ell \le c_u.
     ```
   - If the source gives only existential polylog profiles without exponent alignment, then the
     matched-profile route is still over-strong.
   - Audit result:
     - the strengthened local layer `LiteratureLowerImportAssumptions` now yields lower split
       witnesses for `k = 4` and `k \ge 5`;
     - the strengthened local layer `LiteratureK4ExponentOrderAssumptions` would close the
       frontier if it were source-backed;
     - current local source-backed imports still do not provide the exponent-order statement.

5. `[ ]` If the exponent order is source-backed, remove the frontier axiom.
   - Instantiate `split_gap_k4_profile_dominance_target`.
   - Replace `splitGap_k4_profile_dominance_frontier` by a theorem.
   - Reuse the existing coupling bridge in `Problem142Gap.lean`.
   - Current status: blocked. The local audit did not find a source-backed route to
     `import_targets.k4_exponent_order_target`.

6. `[x]` If the exponent order is not source-backed, pivot early.
   - Do not keep forcing the matched-profile route.
   - Redesign the `k = 4` endpoint to an honest weaker split package, analogous to the
     `k = 3` source-backed pivot.
   - Implemented pivot groundwork:
     - `k4LowerProfileWitness_of_literatureLowerImportAssumptions`
     - `kge5LowerProfileWitness_of_literatureLowerImportAssumptions`
     - `k4LowerProfileWitnessImported_of_literatureLowerImportAssumptions`
     - `kge5LowerProfileWitnessImported_of_literatureLowerImportAssumptions`
     - `mainSplitGap_of_literatureLowerImportAssumptions`
     - `split_gap_data_of_literatureLowerImportAssumptions`

## Current implementation result

The repository now has the right decomposition for the `k = 4` branch:

- one generic analytic comparison lemma,
- one explicit missing source-side input (`c_\ell \le c_u`),
- one theorem showing that this input is enough to produce the exact
  split-gap dominance target already used by the gap layer,
- and an honest split-gap endpoint from `LiteratureLowerImportAssumptions`, without any
  claim of matched-profile coupling.

So the matched-profile elimination route is now fully decomposed and locally audited:

- if a source-backed exponent-order statement appears, the frontier can be removed immediately;
- without it, the honest available endpoint is split-gap data, not `K4ProfileWitnessImported`.

Active follow-up:

- [PLAN_erdos_problem_142_k4_source_backed_pivot_2026-03-07.md](PLAN_erdos_problem_142_k4_source_backed_pivot_2026-03-07.md)
