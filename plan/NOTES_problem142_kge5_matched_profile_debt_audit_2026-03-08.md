# Notes: `k >= 5` Matched-Profile Debt Audit

Date: 2026-03-08

## Objective

Decide whether the current `k >= 5` matched-profile family debt is an honest missing theorem or a
mis-specified target.

Current debt under audit:

- `import_targets.kge5_exponent_order_target`
- `import_targets.split_gap_kge5_profile_dominance_target`

## Primary Sources Checked

1. Leng, Sah, Sawhney, *Improved Bounds for Szemerédi's Theorem*, arXiv:2402.17995
   - abstract: https://arxiv.org/abs/2402.17995
2. Leng, Sah, Sawhney, *Improved bounds for five-term arithmetic progressions*, arXiv:2312.10776
   - abstract: https://arxiv.org/abs/2312.10776
3. O'Bryant, *Sets of Integers that do not Contain Long Arithmetic Progressions*,
   Electron. J. Combin. 18 (2011), P59
   - journal page: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p59

## Findings

### A. Publication-backed upper family scale

The family upper theorem visible on the arXiv abstract for Leng--Sah--Sawhney 2024 is:

```text
for each fixed k >= 5,
  r_k(N) << N exp(-(log log N)^{c_k})
```

This is a stretched-exponential scale in `log log N`, not an iterated-log power scale.

For `k = 5`, the dedicated Leng--Sah--Sawhney paper has the same qualitative shape:

```text
r_5(N) << N / exp((log log N)^c)
```

### B. Publication-backed lower family scale

O'Bryant's lower-bound family is Rankin-type:

```text
r_k(N) >= N C_k exp(-A_k (log N)^{alpha_k} + B_k log log N)
```

again not an iterated-log power family.

### C. Comparison with the repo's current matched-profile family debt

The audited debt currently asks for a theorem of the form:

```text
iterated-log upper family
  =O
iterated-log lower family
```

via:

- `import_targets.kge5_exponent_order_target`
- `import_targets.split_gap_kge5_profile_dominance_target`

But the publication-backed upper family visible in the sources is not of that template.

So the problem is not merely:

```text
we have the right target but are missing a proof.
```

It is:

```text
the current family target is not aligned with the publication-backed theorem shape.
```

### D. Local repository consequence

This matches the March 7 pivot work already present in the repo:

- `PLAN_erdos_problem_142_kge5_frontier_elimination_2026-03-07.md`
- `PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md`
- `import_targets.kge5_stretchedexp_loglog_decay_isLittleO_iteratedlog_neg_rpow`

Those files and the Lean theorem already encode the analytic incompatibility between the
stretched-exponential upper scale and the old iterated-log placeholder.

## Verdict

```text
Outcome: target correction.

The current `k >= 5` matched-profile family debt should not be treated as an honest active
source-backed missing theorem.

It is a mis-specified target relative to the publication-backed upper family scale.
```

## Recommended Next Action

1. Kill the old iterated-log matched-profile family debt as an active research target.
2. Replace it by a corrected route statement that explicitly distinguishes:
   - the off-path stronger family debt,
   - the source-backed split family / toy-model route already supported by the literature.
3. Only reopen the stronger family matched-profile route if a source-backed theorem appears with a
   genuinely compatible family shape.
