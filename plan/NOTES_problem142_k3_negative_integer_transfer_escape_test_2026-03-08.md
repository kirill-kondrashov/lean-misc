# Notes: `k = 3` Negative-Route Integer-Transfer Escape Test (2026-03-08)

## Objective

Run the third live test from the `Template-Escape Critic`:

```text
is the extra integer-case Bohr-set loss only a feature of the currently extracted transport path,
or do the audited sources actually support a different transfer route that escapes the present
negative barrier?
```

## Source Record Available In The Repository

The current source-backed audit already records the relevant fact from Bloom--Sisask:

```text
there is an additional loss in the size of the Bohr set in the integer case,
and it is ultimately this which is responsible for losing two logs
between the F_p^n and the integer case.
```

In repository terms, that statement is recorded in:

- `NOTES_problem142_k3_upper_bottleneck_audit_2026-03-08.md`

and summarized there as:

```text
even if the finite-field bootstrapping step were sharp enough,
the integer-to-Bohr-set conversion still introduces a separate quantitative obstruction.
```

## Critic Question

To break the current negative route, the critic would need evidence of one of the following.

1. A source-backed alternative integer transfer within the same modern proof architecture that
   avoids the recorded Bohr-set loss.
2. A source-backed statement showing that the recorded two-log loss is merely an artifact of one
   exposition choice rather than a real quantitative feature of the argument.
3. A different integer-case closure mechanism, still recognizably inside the same architecture,
   that bypasses the present Bohr-set transport.

## Test Against The Audited Sources

Within the audited source set currently used by the repository:

- Kelley--Meka provides the general modern architecture;
- Bloom--Sisask identifies the local bootstrapping improvement and also explicitly flags the
  separate integer-case Bohr loss;
- no audited source note in the repository records a competing integer transfer that removes this
  loss while staying inside the same proof line.

So the current source record supports:

```text
the integer-case loss is a real unresolved quantitative obstruction in the audited architecture,
not merely a bookkeeping artifact already known to be avoidable.
```

## Verdict For This Escape Route

No source-backed integer-transfer escape has been found in the audited source set used by the
repository.

Therefore the critic does **not** currently break the negative route on integer-transfer grounds.

## Scope Of This Verdict

This is a source-limited verdict, not a universal impossibility theorem.

It says only:

```text
given the presently audited Kelley--Meka / Bloom--Sisask source record,
the repository does not yet have evidence for an alternative integer transfer
that invalidates the current barrier program.
```

If a future source or a deeper audit exhibits a different transport route, this verdict must be
reopened.

## Critic Verdict

```text
The integer-transfer escape remains unsubstantiated in the audited sources.
So the negative-route barrier survives all currently tested template-escape objections.
```
