# Notes: Erdős #142 Frontier Debt Ledger

Date: 2026-03-08

## Ranking Principle

Rank debts by expected impact on the repo's actual mathematical debt profile, not by convenience
of adding another theorem wrapper.

## Rank 1

```text
Debt: `k >= 5` matched-profile family debt
```

Exact target:

- `import_targets.kge5_exponent_order_target`
- `import_targets.split_gap_kge5_profile_dominance_target`

Current source status:

- negative / mis-specified on the current source read
- the old target compares iterated-log family templates
- the publication-backed upper theorem is stretched-exponential in `log log N`
- the active March 7 pivot already treated the old exponent-order family route as off-path

Downstream leverage:

- highest
- one correct verdict here changes the whole tail family `k >= 5`
- either the family matched-profile route is killed/replaced, or a genuine source-backed family
  route is recovered

Current verdict:

```text
This is the strongest candidate for a target-shape error, not just a missing proof.
```

Recommended next action:

```text
source-first audit
```

Why first:

```text
If the target family is wrong, then proving or packaging more around it is wasted motion.
```

## Rank 2

```text
Debt: `k = 4` matched-profile / exponent-order debt
```

Exact target:

- `import_targets.k4_exponent_order_target`
- `import_targets.split_gap_k4_profile_dominance_target`

Current source status:

- negative on the local audit
- the honest current endpoint is split data, not matched-profile dominance
- no local source note currently supplies the needed exponent-order statement `c_l <= c_u`

Downstream leverage:

- medium-high
- this closes one branch of the stronger frontier route
- but it affects only `k = 4`, not an entire family

Current verdict:

```text
Real debt, but probably not the first audit target once `k >= 5` may be globally mis-specified.
```

Recommended next action:

```text
source audit after the `k >= 5` family verdict
```

## Rank 3

```text
Debt: `k = 3` matched-profile strengthening beyond the audited `β = 1 / 12` split route
```

Exact target:

- `import_targets.k3_upper_exponent_gt_half_target`
- `import_targets.split_gap_k3_profile_dominance_target`
- historically related conjectural scaffolding: `bound_targets.k3_superpolylog_upper_profile_one_eighth`

Current source status:

- audited negative for the presently checked Kelley--Meka / Bloom--Sisask extraction
- honest source-backed endpoint remains the split route with explicit `β = 1 / 12`
- no audited published `1/8` theorem was found
- no audited source-backed route to `β > 1 / 2` is currently available

Downstream leverage:

- medium
- would repair the local `k = 3` matched-profile branch if it existed
- but current evidence is already substantially negative, so more wrapper work is low value

Current verdict:

```text
Important debt, but not the best immediate audit target.
The current evidence already says the active positive strengthening route is not source-backed.
```

Recommended next action:

```text
route kill / hold unless genuinely new source evidence appears
```

## Rank 4

```text
Debt: alternate integer-transfer / structured-object escape outside the current negative template
```

Exact target:

- not one fixed theorem yet
- this debt is the question whether a source-backed alternate transfer can evade the current
  barrier architecture without silently changing methods

Current source status:

- currently negative / absent in the audited source set
- the template-escape critic did not find:
  - a localization escape,
  - an endgame escape,
  - or an alternate integer-transfer escape

Downstream leverage:

- speculative but potentially large
- could falsify or sharply narrow the current negative route

Current verdict:

```text
Keep alive as a scoped critic debt, not as the first active theorem program.
```

Recommended next action:

```text
periodic scoped re-audit, not immediate primary cycle
```

## Chosen Next Audit

```text
Highest-leverage next source-first audit:
`k >= 5` matched-profile family debt
```

Reason:

```text
Among the live debts, it has the best combination of breadth and correction value.
If the family target is mis-specified, that changes an entire frontier block at once.
If it is salvageable, that would be a genuinely new source-backed positive route.
```
