# Notes: Erdős #142 Method-Family Primary Fork Selection

Date: 2026-03-09

## Objective

Decide whether the scouting branch can honestly select one primary candidate family and promote it
to a separate theorem-generation chain.

## Candidate A Test: Direct `k = 3` Counting / Supersaturation Bypass

### Exact theorem-shaped extraction question

The first admissible exact target is:

```text
Direct Behrend-scale `k = 3` upper theorem.

Find c > 0 such that for every N and every A ⊆ {1, ..., N},

  |A| ≥ N exp(-c sqrt(log (N + 2)))

forces A to contain a nontrivial 3-term arithmetic progression.
```

Equivalent extremal-form statement:

```text
r_3(N) ≤ N exp(-c sqrt(log (N + 2))).
```

Preferred stronger version for a true counting route:

```text
derive a quantitative lower bound on the number T_3(A) of nontrivial 3-APs,
not merely existence of one progression.
```

### Why this survives the fork standard

This candidate is outside the exhausted family because it:

- acts directly on the original subset `A ⊆ [N]`;
- does not pass through split upper/lower profile coupling;
- does not require the current matched-profile dominance layer;
- does not use the current almost-periodicity -> Bohr-set recurrence as the engine of proof.

### Why this is not the previously rejected endgame reformulation

The critic already rejected the move

```text
rewrite the final contradiction inside the same recurrence as a counting statement on B_m.
```

That rejected move remains excluded.

The present candidate is different:

- it is a direct theorem on `A ⊆ [N]`,
- it is not phrased through the terminal structured set `B_m`,
- and it is intended to replace the current route, not cosmetically restate its last line.

## Candidate B Test: Higher-order structural replacement

Verdict:

```text
not selected
```

Reason:

- still too broad to extract one exact theorem-shaped question.

## Candidate C Test: Ambient-model / transfer replacement

Verdict:

```text
not selected
```

Reason:

- still the most speculative candidate;
- recent re-audit already found no concrete live instance in the current record.

## Selection Verdict

```text
Select candidate A as the primary fork.
```

Reason:

- it has an exact theorem-shaped extraction question;
- it is genuinely outside the exhausted family;
- it gives a clean successor chain without contaminating current theorem surfaces.

## Immediate Consequence

Open the successor theorem-generation chain:

```text
PLAN_erdos_problem_142_k3_direct_counting_route_generation_2026-03-09.md
```

This remains speculative and quarantined until it produces a concrete theorem debt smaller than the
full Behrend-scale upper theorem itself.
