# Notes: `k = 4` External Source Expansion Audit

Date: 2026-03-09

## Objective

Check whether the broader primary-source record for `k = 4` contains a theorem strong enough to

- discharge `import_targets.k4_exponent_order_target`,
- directly prove `import_targets.split_gap_k4_profile_dominance_target`,
- or force a corrected stronger source-backed target shape.

## Primary Sources Checked

1. Green, B.; Tao, T., *New bounds for Szemerédi's theorem, III: A polylogarithmic bound for r_4(N)*.
   - Oxford repository page:
     https://ora.ox.ac.uk/objects/uuid:1d09eef3-01e2-4ce0-ab9d-2892019812c8
2. Green, B.; Tao, T., *New bounds for Szemerédi's theorem, II: A new bound for r_4(N)*.
   - Oxford repository page:
     https://ora.ox.ac.uk/objects/uuid:4a8d5c87-4829-4f48-9ec1-d2f23fbb7c17
3. Green, B.; Tao, T., *New bounds for Szemerédi's theorem, I: Progressions in finite field geometry*.
   - Oxford repository page:
     https://ora.ox.ac.uk/objects/uuid:3a406f4d-458d-4a84-bcf6-34d41813bab6
4. O'Bryant, K., *Sets of integers that do not contain long arithmetic progressions*,
   Electron. J. Combin. 18 (2011), P59.
   - journal page:
     https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p59

## Findings

### A. External upper-source record

The Green--Tao source line gives the repository exactly the kind of upper information it was
already using locally:

```text
`k = 4` has a polylogarithmic upper bound.
```

In particular, the 2017 `Part III` source is the right primary upper benchmark for the existing
`bound_targets.k4_upper_green_tao` / `k4_polylog_upper_profile` side of the repo.

### B. External lower-source record

The primary lower benchmark surfaced in this pass is O'Bryant's general lower-bound family.

Inference from the source:

```text
for `k = 4`, the lower family is Rankin/Behrend type,
with decay on a `sqrt(log N)` scale rather than a polylogarithmic `(log N)^(-c)` scale.
```

So the broader source record visible in this pass does **not** supply a theorem-level
polylogarithmic lower benchmark matching the Green--Tao upper template.

### C. No theorem-level comparison surfaced

In this external source-expansion pass, no primary source surfaced that gives:

- an explicit exponent comparison strong enough to instantiate
  `import_targets.k4_exponent_order_target`, or
- a direct theorem of the form
  `U_4 = O(L_4)` for the polylogarithmic `k = 4` templates.

### D. Consequence for the current repository target

The broader source record therefore does **not** merely confirm the local blocker.
It sharpens it.

The currently audited strong route is not just missing a source-backed exponent comparison.
Its lower-side placeholder is itself misaligned with the main primary lower benchmark surfaced in
this pass.

## Audit Verdict

```text
Outcome: target correction.

The broader source record supports:
  - a Green--Tao polylogarithmic upper route for `k = 4`,
  - and a Rankin/Behrend-type lower route for `k = 4`,
but not a common matched polylogarithmic profile.
```

So the honest next `k = 4` route is not matched-profile closure.
It is a corrected heterogeneous split route.

## Scope

This is an audit-pass verdict, not a universal impossibility theorem.

It says:

```text
among the primary sources surfaced and checked in this pass,
no theorem-level bridge to the current matched-profile target was found,
while a source-backed upper/lower shape mismatch was found.
```
