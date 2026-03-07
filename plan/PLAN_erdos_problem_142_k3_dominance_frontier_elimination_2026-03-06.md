# Plan: Erdős #142 `k=3` Dominance-Frontier Elimination (2026-03-06)

## Objective

Eliminate the temporary non-base axiom
`Erdos142.splitGap_k3_upper_exponent_gt_half_frontier`
by replacing it with a proved theorem showing that the current `k=3` upper template is
`IsBigO` of the current Behrend-shape lower template.

This is the only remaining frontier item that looks plausibly reducible to a comparison lemma
between already-represented profile families, rather than to a genuinely new lower-bound result.

## Progress Bar

- `k=3` dominance-frontier elimination audit: `6 / 6` completed
- Progress: `[####################]` `100%`
- Route verdict: blocked for the current Kelley-Meka extraction; the source-backed exponent visible
  from the paper is `β = 1 / 12`, not `β > 1 / 2`.

## Target Statement

Current target in [ErdosProblems/Problem142Literature.lean](../ErdosProblems/Problem142Literature.lean):

- `import_targets.split_gap_k3_profile_dominance_target`

Current temporary axiom in [ErdosProblems/Problem142Gap.lean](../ErdosProblems/Problem142Gap.lean):

- `splitGap_k3_upper_exponent_gt_half_frontier`
- The older name `splitGap_k3_profile_dominance_frontier` is now a derived theorem from this sharper axiom.

Mathematically, the required comparison is:

```text
C_u * N * exp(-c_u * (log(N+2))^β)
  =O[atTop]
C_l * N * exp(-c_l * sqrt(log(N+2)))
```

After canceling harmless positive multiplicative constants and the factor `N`, the real content is:

```text
exp(-c_u * (log(N+2))^β)
  =O[atTop]
exp(-c_l * sqrt(log(N+2)))
```

## Mathematical Feasibility Check

- If the imported upper witness only guarantees some arbitrary `β > 0`, the target is not uniformly true.
- The comparison is plausible if the upper source can be instantiated with `β > 1 / 2`.
- The borderline `β = 1 / 2` case may still be usable, but would require a sufficiently strong constant comparison between `c_u` and `c_l`.
- If the actual imported upper theorem yields only `β < 1 / 2`, this route fails and the frontier cannot be removed by a pure comparison lemma.

So the first real task is not Lean normalization; it is to make the quantitative `β` regime explicit.

## Milestones

1. **Expose the exact quantitative upper exponent regime** — `completed`
   - Audit the current `k=3` upper import surface and state explicitly what quantitative `β` range is actually justified.
   - Required outcome:
     - either a theorem/assumption surface stating `β > 1 / 2`,
     - or a precise note that only weaker `β` is available, which would block this route.
   - Implementation start:
      - added explicit target name
        `import_targets.k3_upper_exponent_gt_half_target`
      - added literature-side assumption wrapper
        `LiteratureK3ExponentGtHalfAssumptions`
      - added source-facing benchmark target
        `bound_targets.k3_superpolylog_upper_profile_gt_half`
      - added source-facing wrapper
        `LiteratureK3ExponentGtHalfSourceAssumptions`
      - added gap-level bridge
        `splitGap_k3_coupling_target_of_literatureK3ExponentGtHalfAssumptions`
      - added direct full-witness instantiation route
        `k3ProfileWitness_of_literatureK3ExponentGtHalfSourceAssumptions`
      - so the only remaining missing piece is source-backed instantiation of the stronger
        benchmark target `bound_targets.k3_superpolylog_upper_profile_gt_half`.
   - Current audit outcome:
      - the source has now been checked directly from the arXiv source bundle;
      - Theorem `many-3-progs` yields an explicit threshold of shape
        `2^{-O((log N)^(1/12))} * N`, so the source-backed exponent visible in the paper is
        `β = 1 / 12`;
      - therefore the stronger target `bound_targets.k3_superpolylog_upper_profile_gt_half`
        is not justified by the present Kelley-Meka extraction.
   - Evidence file:
      - [NOTES_problem142_k3_kelley_meka_source_audit_2026-03-07.md](NOTES_problem142_k3_kelley_meka_source_audit_2026-03-07.md)

2. **Factor the needed pure comparison lemma on profile templates** — `completed`
   - Introduce a standalone theorem target comparing
     `exp(-a * (log(N+2))^β)` and `exp(-b * sqrt(log(N+2)))`.
   - Keep it independent from `r 3 N`; make it a real-analysis lemma about explicit functions.
   - Implemented in
     [ErdosProblems/Problem142Literature.lean](../ErdosProblems/Problem142Literature.lean):
     - `k3_upper_decay_template`
     - `k3_behrend_decay_template`
     - `import_targets.k3_decay_template_dominance_of_beta_gt_half_target`

3. **Prove the easy constant/shift transport layer** — `completed`
   - Isolate the harmless parts:
     - multiplicative constants `C_u`, `C_l`
     - the common factor `N`
     - the shift `N + 2`
   - Goal: reduce the frontier theorem to one clean asymptotic comparison statement.
   - Implemented in
     [ErdosProblems/Problem142Literature.lean](../ErdosProblems/Problem142Literature.lean):
     - `import_targets.k3_decay_to_profile_transport_target`
     - `k3_decay_to_profile_transport`
     - `import_targets.split_gap_k3_profile_dominance_target_of_decay_route`
   - Outcome:
     - the remaining blocker is now reduced to the sharp exponent hypothesis and the pure decay comparison.

4. **Prove the asymptotic comparison under explicit exponent hypotheses** — `completed`
   - Main mathematical target:
     - if `β > 1 / 2`, prove the upper template is `IsBigO` of the Behrend template.
   - Optional secondary target:
     - characterize the borderline `β = 1 / 2` case with a constant inequality hypothesis.
   - Implemented in
     [ErdosProblems/Problem142Literature.lean](../ErdosProblems/Problem142Literature.lean):
     - `k3_decay_template_dominance_of_beta_gt_half`
   - Outcome:
     - the pure decay comparison is now proved under the sharp hypothesis `β > 1 / 2`.

5. **Wire the comparison lemma into the existing frontier target** — `completed`
   - Use the comparison theorem to prove
     `import_targets.split_gap_k3_profile_dominance_target`.
   - Replace `splitGap_k3_profile_dominance_frontier` by a theorem in
     [ErdosProblems/Problem142Gap.lean](../ErdosProblems/Problem142Gap.lean).
   - Implemented in
     [ErdosProblems/Problem142Literature.lean](../ErdosProblems/Problem142Literature.lean):
     - `split_gap_k3_profile_dominance_target_of_beta_gt_half`
   - Current status:
     - the derived dominance theorem is complete;
     - the only missing input for eliminating the remaining `k=3` frontier axiom is now
       `import_targets.k3_upper_exponent_gt_half_target`.

6. **Re-run checker and reassess remaining non-base axioms** — `completed`
   - Run:
     - `make check`
     - `make verify`
   - Expected outcome:
     - one non-base axiom removed;
     - remaining frontier debt reduced to the `k=4` and `k≥5` dominance items, which are still mathematical-content gaps.
  - Current outcome:
     - the checker-clean debt surface now shows
       `splitGap_k3_upper_exponent_gt_half_frontier`,
       `splitGap_k4_profile_dominance_frontier`,
       `splitGap_kge5_profile_dominance_frontier`.
     - This confirms the old `k=3` dominance axiom has been replaced by the sharper exponent-threshold axiom.
     - It is now also explicit in `Problem142Gap.lean` that importing
       `LiteratureK3ExponentGtHalfAssumptions` would remove the `k=3`
       branch from the frontier package, leaving only `k=4` and `k≥5`.
     - It is now explicit in `Problem142Literature.lean` that the stronger source-facing
       benchmark target `bound_targets.k3_superpolylog_upper_profile_gt_half`
       is already sufficient to instantiate `K3ProfileWitnessImported` directly.

## Blocked Planes

1. **Hidden-exponent plane**
   - Risk: the current imported upper witness does not expose enough quantitative control on `β`.
   - Elimination:
     - make the `β` regime explicit before any real-analysis proof attempt.

2. **False-comparison plane**
   - Risk: the desired dominance is simply false for the available exponent range.
   - Elimination:
     - prove the comparison only under sharp hypotheses;
     - if those hypotheses are unavailable, stop this route rather than forcing a false lemma.

3. **Asymptotic-normalization plane**
   - Risk: proof effort gets wasted on constants and shifts instead of the genuine growth comparison.
   - Elimination:
     - factor a reusable template-comparison lemma first.

## Success Criterion

This plan succeeds if and only if:

- `splitGap_k3_upper_exponent_gt_half_frontier` is deleted as an axiom,
- the replacement is a proved theorem from explicit quantitative hypotheses actually supported by the current `k=3` upper source,
- and `make verify` remains green.

## Failure Criterion

This route should be declared blocked if the best justified upper-side exponent regime does not imply
dominance over the Behrend `sqrt(log)` template.

In that case, the honest next step is not a Lean proof search; it is a redesign of the `k=3`
frontier statement so it matches the strongest true mixed-profile consequence already encoded.

## Final Audit Verdict

This failure criterion is now triggered for the current Kelley-Meka extraction:

- the explicit exponent visible from the source audit is `β = 1 / 12`;
- the current comparison route requires `β > 1 / 2`;
- so the `splitGap_k3_upper_exponent_gt_half_frontier` route is not source-derivable from the
  presently extracted theorem shape.

## Route Closure

This route is closed as an active search direction.

Follow-up pivot file:

- [PLAN_erdos_problem_142_k3_source_backed_pivot_2026-03-07.md](PLAN_erdos_problem_142_k3_source_backed_pivot_2026-03-07.md)
