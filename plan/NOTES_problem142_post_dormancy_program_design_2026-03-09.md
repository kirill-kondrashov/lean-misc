# Notes: Erdős #142 Post-Dormancy Program Design

Date: 2026-03-09

## Objective

Design a restart program that is honest after the closure of all currently explored
theorem-generation branches.

## Constraint From The Dormant Endpoint

The current repository state is:

```text
no active route-generation cycle.
reopen only if a future audited source or theorem extraction yields an exact smaller debt
outside the exhausted family.
```

So the next program cannot be:

- another internal route-generation cycle;
- another theorem-surface packaging cycle;
- another vague “possible direction” list.

It must instead be:

```text
an exact-debt extraction program.
```

## Program Thesis

The clean restart is:

```text
search externally and structurally for one exact smaller theorem debt
that sits outside the exhausted family and is precise enough to deserve
its own theorem-generation chain.
```

This is different from the closed route-generation program because it does **not** try to invent a
new route first and justify it later.
It searches only for exact theorem-shaped debts that can be stated before any new theorem program
is declared active.

## Candidate Extraction Clusters

### A. Direct counting / supersaturation source extraction

Goal:

```text
find one exact direct theorem on A ⊆ [N] that is strictly smaller than the full direct
`1 / 8` theorem, but strong enough to reopen a counting route.
```

Why first:

- this is the most concrete failed fork from the previous cycle;
- the exact failure point is already known: no non-artificial candidate for `Φ(|A|, N)` was
  isolated.

### B. Stability / classification source extraction

Goal:

```text
find one exact near-extremal structural theorem for 3-AP-free sets that is concrete enough
to force a new theorem chain.
```

Why second:

- it is genuinely outside the current recurrence family;
- it was previously rejected only because it was too broad, not because it was false.

### C. Transfer / ambient-model source extraction

Goal:

```text
find one exact transport or structured-object theorem that materially changes the current
integer-case loss profile.
```

Why third:

- it is the most speculative restart;
- earlier audits found no concrete live instance in the currently checked record.

## Admissibility Rule

No cluster counts as successful unless it yields all of:

1. one exact theorem-shaped statement;
2. strict size reduction relative to the full branch target it is meant to reopen;
3. a clear reason it lies outside the exhausted family;
4. a credible downstream consequence for the repository.

## Success / Failure Standard

Success:

```text
extract one exact smaller debt and open exactly one successor theorem-generation chain.
```

Failure:

```text
close the restart program and return to dormant status without inventing a new active route.
```

## Design Verdict

```text
The next honest program is a post-dormancy exact-debt extraction program,
run source-first across three admissible clusters:
direct counting, stability/classification, and transfer replacement.
```
