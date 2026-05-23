# Notes: Erdős #142 Restart Admission Current-Candidates Verdict

Date: 2026-03-09

## Objective

Audit the currently visible restart candidates and decide whether any one of them is admissible
right now.

## Cluster A Audit: Benchmark-Surviving Transport

Result:

```text
NO-GO on the currently visible benchmark set.
```

Reason:

- the Varnavides scale benchmark note already checked the sharpest explicit visible `k = 3` upper
  scaffold `bound_targets.k3_superpolylog_upper_profile_one_eighth`;
- under a proper subscale `M = exp((log N)^θ)` with `0 < θ < 1`, transport degrades exponent
  `1 / 8` to `θ / 8`;
- the same geometry also degrades the checked source-backed `1 / 12` benchmark to `θ / 12`;
- preserving the benchmark exponent forces same-scale reuse, which is inadmissible by the restart
  standard.

So Cluster A does not currently yield an admissible restart candidate.

## Cluster B Audit: Intermediate-Debt Mining

Current visible status:

```text
already no-go on the currently localized direct-counting branch.
```

Reason:

- the direct-counting `1 / 8` verdict already found that no exact smaller local supersaturation
  statement had been isolated below the direct theorem target;
- the admission program has not added a new exact intermediate statement since that closure.

So Cluster B also does not currently yield an admissible restart candidate.

## Cluster C Audit: Outside-Family Candidates

Current visible status:

```text
no exact admissible candidate currently visible.
```

Reason:

- the earlier method-family scouting already ranked non-counting alternatives as broader and less
  exact;
- the only candidate previously sharp enough to promote was the direct-counting bypass;
- that promoted candidate has now closed without a smaller extracted debt.

So Cluster C does not currently supply a fresh exact candidate either.

## Global Verdict

```text
Reject all currently visible restart candidates.
Return the top-level program to explicit dormancy.
```

The admission program has therefore done its job:

- it did not reopen theorem construction prematurely;
- it checked the most immediate candidate class first;
- and it preserved the stop rules by ending in a no-go verdict rather than inventing a successor.
