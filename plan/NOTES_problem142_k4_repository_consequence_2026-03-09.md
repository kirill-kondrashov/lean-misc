# Notes: `k = 4` Repository Consequence Of Route Correction

Date: 2026-03-09

## Objective

Translate the corrected `k = 4` source-route shape into exact repository consequences:

- what should now be treated as off-path or placeholder-only,
- what should replace it,
- and whether the route is already precise enough for Lean-side redesign.

## Surfaces That Are No Longer Honest As Final Source-Backed `k = 4` Endpoints

The corrected source record means the following current `k = 4` surfaces cannot remain the final
honest source-backed route without qualification:

- `import_targets.k4_polylog_lower_profile`
- `import_targets.k4_exponent_order_target`
- `import_targets.split_gap_k4_profile_dominance_target`
- `K4SourceBackedSplitWitness`
- `K4SourceBackedSplitGap`
- `k4_split_data_of_literatureLowerImportAssumptions`

Reason:

```text
these surfaces are built around a polylogarithmic lower-side placeholder,
while the broader primary-source record surfaced in the current audit points to a
Rankin/Behrend-type lower benchmark for `k = 4`.
```

So they may remain in the repository only as:

- local import-shape placeholders,
- or off-path legacy surfaces,

but not as the final broader-source-backed `k = 4` endpoint.

## Replacement Direction

The replacement should mirror the corrected source shape:

- upper side:
  Green--Tao polylogarithmic upper profile
- lower side:
  O'Bryant/Rankin-type lower profile specialized to `k = 4`
- route type:
  heterogeneous split package

Repository consequence:

```text
the final `k = 4` source-backed route should be redesigned to look structurally more like the
current `k = 5` split route than like the old matched/polylog `k = 4` route.
```

In particular, the natural replacement direction is:

- add one explicit `k = 4` lower target on an O'Bryant/Rankin shape,
- extract the corresponding witness surface,
- pair it with the existing Green--Tao upper side,
- and expose the result as a heterogeneous split package.

## Readiness For Lean Integration

The route is **not yet** ready for Lean-side redesign.

Reason:

```text
the current audit fixed the qualitative source shape,
but it has not yet frozen one exact formal lower-target template for `k = 4`
at the same precision level currently used for the `k = 5` Rankin/O'Bryant surfaces.
```

So one more source-shape extraction step is needed before editing Lean.

## Consequence Verdict

```text
Outcome:
- current polylog-lower `k = 4` source-backed surfaces are demoted from final honest endpoints;
- the corrected route is a heterogeneous split route;
- one exact lower-shape extraction note is still needed before Lean integration.
```
