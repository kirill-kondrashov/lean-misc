# Plan: `k >= 5` Source-Backed Pivot

Date: 2026-03-07

## Objective

Replace the currently blocked `k >= 5` matched-profile route by a source-backed split route whose
upper and lower templates match the actual scales appearing in the literature.

## Status

Progress: `██----` `2 / 6` milestones

Implemented so far:
- `ErdosProblems/Problem142Literature.lean` now contains the analytic incompatibility theorem
  `import_targets.kge5_stretchedexp_loglog_decay_isLittleO_iteratedlog_neg_rpow`.
- This closes the first Tao-style step: formally prove the old iterated-log placeholder cannot
  remain the active target once a stretched-exponential `\log\log` upper theorem is imported.
- `ErdosProblems/Problem142.lean` now contains the branch-local source-backed benchmark target
  `bound_targets.k5_stretchedexp_loglog_upper_profile`.
- `ErdosProblems/Problem142Literature.lean` now contains the matching witness surface
  `K5UpperStretchedexpProfileWitness`, the source-facing assumption layer
  `LiteratureK5UpperStretchedexpSourceAssumptions`, and the theorem
  `upper_variant_five_of_literatureK5UpperStretchedexpSourceAssumptions`.

## Publication-Backed Evidence

1. Leng, Sah, Sawhney, *Improved bounds for five-term arithmetic progressions*,
   arXiv:2312.10776.
   - For `k = 5`, they prove

   ```math
   r_5(N) \ll \frac{N}{\exp((\log\log N)^c)}
   ```

   for some `c \in (0,1)`.

   Source:
   <https://arxiv.org/abs/2312.10776>

2. Leng, Sah, Sawhney, *Improved Bounds for Szemerédi's Theorem*,
   arXiv:2402.17995.
   - For every fixed `k >= 5`, they prove

   ```math
   r_k(N) \ll N \exp(-(\log\log N)^{c_k})
   ```

   for some `c_k > 0`.

   Source:
   <https://arxiv.org/abs/2402.17995>

3. O'Bryant, *Sets of Integers that do not Contain Long Arithmetic Progressions*,
   Electron. J. Combin. 18 (2011), P59.
   - For every fixed `k`, he gives constructive lower bounds of Rankin type:

   ```math
   r_k(N) \ge N C_k
     \exp\!\Bigl(
       -A_k (\log N)^{\alpha_k}
       + B_k \log\log N
     \Bigr),
   ```

   for explicit constants `A_k > 0`, `\alpha_k > 0`, and `B_k \in \mathbb{R}` depending on `k`.

   Source:
   <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p59>

## Tao-Style Diagnosis

The current active `k >= 5` frontier tries to compare two iterated-log templates

```math
L_k(N) = \frac{C_L(k)\,N}{(\log\log(N+3))^{c_L(k)}},
\qquad
U_k(N) = \frac{C_U(k)\,N}{(\log\log(N+3))^{c_U(k)}},
```

and then prove

```math
U_k(N) = O(L_k(N)).
```

This is the wrong target if the actual published upper theorem is

```math
r_k(N) \ll N \exp(-(\log\log N)^{c_k}).
```

The correct Tao-style move is:

1. Try to prove the negation of the current route.
2. Reduce to the first nontrivial toy case `k = 5`.
3. Replace the mis-specified target by the strongest source-backed split theorem.

## Immediate Mathematical Negation Target

Prove in Lean that for any fixed `C > 0` and `c > 0`,

```math
N \exp(-(\log\log N)^c)
=
o\!\left(\frac{N}{(\log\log N)^C}\right).
```

Consequently, if the Leng-Sah-Sawhney upper theorem is imported, then the old placeholder lower
target

```math
\frac{N}{(\log\log N)^C} = O(r_k(N))
```

cannot be simultaneously used on the active route.

This should be treated as a deliberate refutation of the old active `k >= 5` template, not as a
failed proof attempt.

## Replacement Route

### Stage 1: Toy model `k = 5`

Freeze the exact source-backed pair:

```math
L_5^{\mathrm{src}}(N)
  := N C_5
     \exp\!\Bigl(
       -A_5 (\log N)^{\alpha_5} + B_5 \log\log N
     \Bigr),
```

```math
U_5^{\mathrm{src}}(N)
  := N \exp(-(\log\log N)^{c_5}).
```

Then prove the compatibility theorem

```math
L_5^{\mathrm{src}}(N) = O(U_5^{\mathrm{src}}(N)).
```

This does not give a matched profile. It gives an honest split theorem with explicit, incompatible
scales.

### Stage 2: First-class source-backed split package

Add a new surface:

- `K5SourceBackedSplitWitness`

containing

- one explicit O'Bryant-type lower witness,
- one explicit Leng-Sah-Sawhney upper witness,
- the proved compatibility direction `lower =O upper`.

### Stage 3: Family generalization

If Stage 1 is clean, generalize to

- `Kge5SourceBackedSplitWitness`
- `Kge5SourceBackedSplitGap`

with branch data for every fixed `k >= 5`.

### Stage 4: New practical downstream target

Replace the current practical target `MainK34ResolvedGap` by an all-branches source-backed split
surface, e.g.

- `MainAllSourceBackedSplitGap`

with

- `k = 3`: source-backed split,
- `k = 4`: source-backed split,
- `k >= 5`: source-backed split on the new stretched-exponential / Rankin scales.

## Milestones

1. `[x]` Prove the incompatibility theorem between the Leng-Sah-Sawhney upper scale and the old
   iterated-log lower placeholder.
   - Implemented as
     `import_targets.kge5_stretchedexp_loglog_decay_isLittleO_iteratedlog_neg_rpow`.
2. `[x]` Implement a dedicated `k = 5` source-backed upper target.
   - Implemented as
     `bound_targets.k5_stretchedexp_loglog_upper_profile`,
     `K5UpperStretchedexpProfileWitness`,
     `LiteratureK5UpperStretchedexpSourceAssumptions`,
     and
     `upper_variant_five_of_literatureK5UpperStretchedexpSourceAssumptions`.
3. `[ ]` Implement a dedicated `k = 5` O'Bryant-type lower target.
4. `[ ]` Prove `L_5^{src} = O(U_5^{src})`.
5. `[ ]` Package the result as `K5SourceBackedSplitWitness`.
6. `[ ]` Decide whether to generalize immediately to all fixed `k >= 5` or keep `k = 5` as the
   live toy-model branch.

## Practical Verdict

The active `k >= 5` exponent-order plan should be treated as off-path unless new publications are
found that actually support a common iterated-log profile family.

The honest next step is not

```math
c_L(k) \le c_U(k),
```

but rather

```math
\text{replace the `k >= 5` template family by the published stretched-exponential upper scale.}
```
