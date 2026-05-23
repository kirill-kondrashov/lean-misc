# Notes: Erdős #142 Restart Admission Program Design

Date: 2026-03-09

## Objective

Open a new research program that decides whether any restart candidate is admissible, without
pretending that theorem construction has already restarted.

## Why This Program Exists

The current top-level state is dormant:

- the original debt-reduction chain is complete;
- the route-generation chain is complete;
- the post-dormancy Varnavides restart extracted one valid reduction object, but no smaller live
  theorem debt.

So the next honest program is not:

```text
build another proof route.
```

It is:

```text
test whether any exact restart candidate deserves to become a proof route.
```

## Admission Standard

A restart candidate is admissible only if it passes all of:

1. exact statement:
   one theorem-shaped or source-shaped target, not a vague direction;
2. strict reduction:
   genuinely smaller than the current branch target it aims to improve;
3. noncircularity:
   no same-scale reuse or mere renaming of an existing reduction;
4. landing layer:
   a clear home in source audit, import layer, local target layer, or theorem layer.

## Admission Clusters

### Cluster A. Benchmark-surviving transport candidates

Look for concrete upper benchmarks that survive Varnavides transport at a proper subscale.

### Cluster B. Smaller direct-counting intermediate debts

Look for exact supersaturation, stability, or counting statements that sit strictly below the direct
`1 / 8` theorem.

### Cluster C. Outside-family candidates

Look for exact smaller debts outside the exhausted split / matched-profile / Bohr-recurrence /
current direct-counting restart family.

## Allowed Outputs

Exactly one of:

1. open one new restart candidate plan;
2. reject all currently visible candidates and return to dormancy.

## Disallowed Outputs

- multiple speculative restart branches at once;
- another generic wrapper theorem;
- another README/checker/theorem-surface packaging cycle;
- a “promising direction” without one exact statement.

## Verdict

```text
The admission program is the right next layer.

It preserves the dormant stop rules while still allowing one exact restart candidate to be
promoted if it survives scrutiny.
```
