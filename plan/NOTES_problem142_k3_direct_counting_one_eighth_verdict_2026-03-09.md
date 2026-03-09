# Notes: Erdős #142 `k = 3` Direct Counting `1 / 8` Verdict

Date: 2026-03-09

## Objective

Decide whether the narrowed direct `1 / 8` counting branch yields one exact smaller local theorem
debt, or should be closed as too coarse.

## Modality Choice

Between the two permitted modes,

```text
supersaturation-style
vs
stability/classification-style,
```

the correct next mode is:

```text
supersaturation-style
```

Reason:

- the route was explicitly opened as a direct counting / supersaturation bypass;
- the older geometric/classification branch was already ranked as less concrete and more remote;
- stability/classification currently does not isolate one exact theorem-shaped local debt in the
  repository.

## Exactness Test

The narrowed branch still needs one local theorem target strictly smaller than the direct
`1 / 8` theorem itself.

The obvious candidate would be a direct quantitative supersaturation statement of the form

```text
|A| ≥ N exp(-c (log N)^(1/8))
  -> T_3(A) ≥ Φ(|A|, N),
```

for one exact explicit function `Φ`.

But the repository does **not** currently isolate a non-artificial candidate for `Φ`.

So at the present state:

- the direct `1 / 8` existence theorem is exact;
- a smaller direct supersaturation theorem is **not** exact yet;
- any stronger quantitative count formula would be invented rather than extracted.

## Verdict

```text
NO-GO as a theorem-generation chain.
```

Reason:

- the branch can be narrowed to an exact theorem target;
- but it cannot currently be reduced further to one exact smaller local debt;
- so keeping it active would recreate the same false-progress pattern the fork gate was designed to
  prevent.

## Program Consequence

The direct-counting `1 / 8` fork should be closed.

The honest status after closure is:

```text
no active route-generation cycle.
reopen only if a future source/theorem extraction gives an exact local supersaturation or
stability statement smaller than the full direct theorem target.
```
