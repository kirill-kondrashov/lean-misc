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

Progress: `███---` `3 / 6` milestones

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

4. `[ ]` Audit the actual `k = 4` literature/import layer against the new target.
   - Check whether the current upper and lower imports can honestly supply
     ```math
     c_\ell \le c_u.
     ```
   - If the source gives only existential polylog profiles without exponent alignment, then the
     matched-profile route is still over-strong.

5. `[ ]` If the exponent order is source-backed, remove the frontier axiom.
   - Instantiate `split_gap_k4_profile_dominance_target`.
   - Replace `splitGap_k4_profile_dominance_frontier` by a theorem.
   - Reuse the existing coupling bridge in `Problem142Gap.lean`.

6. `[ ]` If the exponent order is not source-backed, pivot early.
   - Do not keep forcing the matched-profile route.
   - Redesign the `k = 4` endpoint to an honest weaker split package, analogous to the
     `k = 3` source-backed pivot.

## Current implementation result

The repository now has the right decomposition for the `k = 4` branch:

- one generic analytic comparison lemma,
- one explicit missing source-side input (`c_\ell \le c_u`),
- one theorem showing that this input is enough to produce the exact
  split-gap dominance target already used by the gap layer.

So the next step is no longer “do more Lean plumbing”. The next step is to decide whether the
current `k = 4` literature import actually supports the required exponent order.
