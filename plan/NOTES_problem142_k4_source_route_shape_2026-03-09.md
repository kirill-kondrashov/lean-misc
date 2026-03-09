# Notes: `k = 4` Corrected Source-Route Shape

Date: 2026-03-09

## Objective

Freeze the exact source-backed route shape for `k = 4` after the external source-expansion audit.

## Corrected Route Shape

The broader primary-source record currently supports the following mixed route:

### Upper side

Green--Tao provides a polylogarithmic upper benchmark for `r_4(N)`.

Repository-language:

```text
upper side remains in the `k4_polylog_upper_profile` family.
```

### Lower side

The surfaced lower benchmark is Rankin/Behrend type rather than polylogarithmic.

Inference from O'Bryant's general lower family:

```text
for `k = 4`, the lower decay is on a `sqrt(log N)`-type scale,
not on a `(log N)^(-c)` scale.
```

Repository-language:

```text
the honest lower side should be treated as a Behrend/Rankin-type source-facing target,
not as `import_targets.k4_polylog_lower_profile` if that target is meant to be source-backed.
```

### Coupling status

No source-backed theorem in the present audit gives:

- a common polylogarithmic matched profile,
- an exponent comparison `cL <= cU`,
- or a direct polylogarithmic dominance theorem `U_4 = O(L_4)`.

So the corrected route type is:

```text
heterogeneous split route
```

not:

```text
matched-profile route
```

## Practical Meaning

The corrected `k = 4` route should look conceptually like:

```text
lower:  N * exp(-c * sqrt(log N))   or comparable Rankin/O'Bryant shape
upper:  N / (log N)^C               or comparable Green--Tao polylog shape
```

with no claim that the two sides collapse to one shared profile.

## Shape Verdict

```text
The external source-expansion pass has changed the `k = 4` branch from
"blocked matched polylog route"
to
"corrected heterogeneous split route".
```
