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
- The prism packaging phase is already done in Lean:
  - `twoSheetFamily`
  - its down-set and half-cube cardinality facts
  - the exact outer-boundary identity for the prism family
- The even minimizer route is also partly done:
  - existence of a global minimizer
  - compression/shift normalization
  - a middle-transition-window theorem for the selected minimizer
  - reduction of the remaining even obstruction to two odd strict-gap frontiers
  - collapse to `evenLowerHalfFamily` once the odd strict-gap frontiers force the even witness
    `totalSize` bound and balanced `0`-sections
- The exact slice profile of the witness `evenLowerHalfFamily` is formalized.

So this is now the single live theorem target in the current proof program.

## Main proof program

1. Keep the prism reinterpretation as the global frame
   - all live work still goes through the even-cube family `T = twoSheetFamily M N`
   - the exact identity
     - `|∂+ T| = |∂+ N| + |(N \\ M) ∪ ∂+ M|`
     is already the formal bridge back to the odd two-sheet statement

2. Work with a selected even half-cube global minimizer `𝒟`
   - this minimizer can already be chosen in Lean
   - it can already be normalized by compression / shifting
   - it already satisfies a middle-transition-window constraint

3. Prove the odd one-sheet local stability theorem
   - target the current odd strict-gap route through the first positive outside slice below the
     middle
   - most realistic formulation:
     - a first positive outside slice forces strict weighted-drop, hence strict upper-shadow gap
   - this is the local one-family obstruction behind
     `OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement`

4. Prove the odd two-sheet local stability theorem
   - if nested odd sheets `M ⊆ N` with `e > 0` produce a prism family with larger `totalSize`
     than the diagonal witness, then the visible pair-interface boundary is already strictly above
     the middle threshold
   - combinatorially, this should come from the first rank where the two sheets genuinely separate
     and create unavoidable visible interface mass

5. Push those odd strict-gap theorems through the existing even minimizer reductions
   - deduce `totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m)` for the selected even minimizer
   - recover balanced `0`-sections as a consequence
   - invoke the existing collapse theorem and exact witness slice profile
   - conclude that the canonical minimizer is exactly the standard lower half

6. Finish the even half-cube extremal inequality
   - deduce `|∂+ T| >= C(2m+2, m+1)`
   - discharge `PrismHalfCubeBoundaryLowerStatement`

7. Translate back to the odd statement
   - recover `B(M,N) >= 2 * C(2m+1, m)`
   - replace `halfCubeBoundaryLower` by the proved prism frontier

## Why this route

- Direct inequalities on `M` and `N` already produced several false conjectural frontiers.
- The prism view is the first stable formulation that:
  - matches exhaustive data
  - matches the section decomposition already formalized in Lean
  - explains the correct interface term
- The current stuck state is no longer "find the right compression setup".
- The remaining gap is now a local stability problem:
  - first missing mass below the middle in the odd one-sheet case should force a strict gap;
  - first genuine separation between the two odd sheets should force extra visible interface mass.

## Completed Lean milestones

1. Prism packaging
   - `twoSheetFamily M N`
   - down-set structure and half-cube cardinality
   - exact prism outer-boundary decomposition

2. Even minimizer setup
   - existence of even global minimizers
   - compression/shift normalization
   - middle-transition-window theorem

3. Witness rigidity infrastructure
   - exact slice profile for `evenLowerHalfFamily`
   - collapse of a normalized minimizer to `evenLowerHalfFamily` once the witness `totalSize`
     bound and balanced `0`-sections hold

4. Reduction of the even obstruction to odd local frontiers
   - the remaining even zero-section-excess obstruction is now reduced to an odd two-sheet strict
     pair-interface theorem
   - the balanced even branch with larger `totalSize` is already reduced to the odd one-sheet
     larger-`totalSize` strict upper-shadow-gap theorem

## Immediate Lean target

1. Localize the new odd two-sheet strict-gap theorem
   - reduce the current positive-excess pair-interface frontier to a canonical first-separation or
     wide-middle-window statement for nested sheets
   - keep the proof in the exact prism / pair-interface language already formalized

2. Push the odd one-sheet frontier through the first-positive-outside-slice route
   - target strict weighted-drop or strict upper-shadow-gap from the first deficient slice below
     the middle
   - use the already-developed outside-slice and local-LYM infrastructure rather than generic
     excess inequalities

3. Once those odd local theorems are proved
   - invoke the existing even reductions
   - recover the witness `totalSize` bound and balanced `0`-sections
   - identify the minimizer with `evenLowerHalfFamily`
   - finish the prism theorem by the already-built reduction

## Parallel exploratory tracks

- Odd one-sheet local stability track
  - first missing odd slice below the middle
  - strict weighted-drop / upper-shadow-gap consequence

- Odd two-sheet interface track
  - first genuine separation rank between the sheets
  - unavoidable visible interface mass at that rank

- Even transport track
  - keep converting any completed odd local theorem into the existing even minimizer reduction
    chain

- Data track
  - continue small-`m` extremizer search focused on first outside slice and first sheet-separation
    patterns

## Risk assessment

- The theorem still looks like the hard core of Erdős #1, not a cheap intermediate lemma.
- Compression and generic canonical-form work no longer look like the main risk.
- The active risk is that the needed local stability theorem at the first deficient / separation
  rank is the true hard combinatorial statement in disguise.
- The likely win is now a proof that any residual section imbalance creates a boundary penalty. 
