# Plan: Two-Sheet Boundary Theorem

## Statement

Work in the odd cube `P([2m+1])`. Let `M ⊆ N` be down-sets with

- `|N| = 2^(2m) + e`
- `|M| = 2^(2m) - e`

Define

- `∂+ F := { A ∉ F : exists x in A, A \\ {x} ∈ F }`
- `I(M,N) := (N \\ M) ∪ ∂+ M`
- `B(M,N) := |∂+ N| + |I(M,N)|`

Goal:

- `B(M,N) >= 2 * C(2m+1, m)`

This is the `Two-Sheet Boundary Theorem`.

## Current status

- The repo now treats this as the live frontier for Erdős #1.
- False predecessor frontiers have been explicitly disproved and archived:
  - paired odd-section boundary without interface term
  - one-family `+ 2e` excess bound
  - direct/existential strict-excess variants
- The current Lean reduction already proves:
  - `Two-Sheet Boundary Theorem -> odd half-cube theorem`
  - `Two-Sheet Boundary Theorem -> even half-cube theorem`
  - `Two-Sheet Boundary Theorem -> HalfCubeBoundaryLowerStatement`

So this is now the single live theorem target in the current proof program.

## Main proof program

1. Prism reinterpretation
   - Build an even-cube family `T ⊆ P([2m+2])` from the two sheets:
     - lower sheet = `N`
     - upper sheet = `M`
   - Think of `T` as a monotone region in `B_(2m+1) x B_1`.

2. Show `T` is a half-cube down-set
   - prove `T` is downward-closed
   - prove `|T| = |N| + |M| = 2^(2m+1)`

3. Prove the exact boundary decomposition
   - `|∂+ T| = |∂+ N| + |(N \\ M) ∪ ∂+ M|`
   - this identifies the two-sheet boundary exactly with the outer boundary of `T`

4. Convert to a sharp isoperimetric problem in the even cube
   - among all even-cube down-sets of size `2^(2m+1)`, minimize `|∂+ T|`
   - target minimizer should be the standard lower half

5. Push minimizers toward a canonical form
   - use compression / shifting
   - preserve:
     - down-set structure
     - half-cube size
     - nonincrease of positive boundary

6. Identify the extremizer
   - show the canonical minimizer is the standard lower half
   - conclude `|∂+ T| >= C(2m+2, m+1)`

7. Translate back
   - via the exact decomposition, recover
     - `B(M,N) >= 2 * C(2m+1, m)`

## Why this route

- Direct inequalities on `M` and `N` already produced several false conjectural frontiers.
- The prism view is the first stable formulation that:
  - matches exhaustive data
  - matches the section decomposition already formalized in Lean
  - explains the correct interface term

## First concrete Lean targets

1. Define the prism family explicitly
   - `twoSheetFamily M N`

2. Prove its basic structure
   - `isDownSetFamily_twoSheetFamily`
   - `card_twoSheetFamily`
   - zero-section descriptions of `twoSheetFamily`

3. Prove the exact boundary decomposition
   - `card_positiveBoundary_twoSheetFamily`
   - or a section-by-section equivalent statement

4. Reduce the theorem to even half-cube isoperimetry
   - `TwoSheetBoundaryTheorem_of_halfCubeBoundaryLower`
   - ideally also a converse / equivalence theorem for the prism family

## Parallel exploratory tracks

- Compression track
  - prove positive-boundary monotonicity under suitable compressions

- Alexander dual / minimal-outside track
  - understand minimizers through dual or outside-profile structure

- Data track
  - continue small-`m` extremizer search to pin down the canonical minimizer shape

## Risk assessment

- The theorem still looks like the hard core of Erdős #1, not a cheap intermediate lemma.
- The likely win is not a miraculous local inequality, but a clean extremizer/normal-form proof in the even cube.
