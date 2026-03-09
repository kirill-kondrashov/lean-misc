# Notes: `k = 4` Heterogeneous Split Integration Design

Date: 2026-03-09

## Objective

Freeze the repository-integration design for the corrected `k = 4` route before editing Lean.

## Replacement Surface Design

The corrected `k = 4` branch should gain a new explicit lower-side family matching the extracted
O'Bryant shape.

Natural target-level additions:

- `bound_targets.k4_rankin_obryant_lower_profile`

Natural witness/import additions in `Problem142Literature.lean`:

- `K4LowerRankinProfileWitness`
- `K4LowerRankinProfileWitnessImported`
- `k4_rankin_lower_profile`
- `LiteratureK4LowerRankinSourceAssumptions`

Natural corrected split package:

- `K4HeterogeneousSourceBackedSplitWitness`
- `K4HeterogeneousSourceBackedSplitGap`
- `k4_heterogeneous_split_data_of_...`

The purpose of the explicit `heterogeneous` name is to avoid any ambiguity with the old
polylog/polylog placeholder route.

## Retention Policy For Old `k = 4` Surfaces

The existing surfaces

- `import_targets.k4_polylog_lower_profile`
- `K4SourceBackedSplitWitness`
- `K4SourceBackedSplitGap`
- `k4_split_data_of_literatureLowerImportAssumptions`

should not remain the public final source-backed `k = 4` route.

Recommended retention policy:

- keep them temporarily as legacy/local-placeholder surfaces,
- stop describing them as the broader-source-backed `k = 4` endpoint,
- and move public status text to the new heterogeneous package once it exists.

This avoids breaking the current repo all at once while still correcting the public mathematical
story.

## Exact Lean Edit Set

The next implementation cycle should do exactly this:

1. Add the new `k = 4` lower source target in `Problem142.lean`.
2. Add the matching witness/import/assumption layer in `Problem142Literature.lean`.
3. Add the corrected heterogeneous split package and branch theorem in `Problem142Literature.lean`.
4. Add the gap-layer alias and bridge theorem in `Problem142Gap.lean`.
5. Update README and status surfaces so the new heterogeneous package becomes the honest public
   `k = 4` route.
6. Demote the old polylog-lower `k = 4` surfaces to legacy placeholder status rather than deleting
   them immediately.

## Design Verdict

```text
The route is now fully specified for Lean redesign.
The next cycle should edit code, not write more planning notes.
```
