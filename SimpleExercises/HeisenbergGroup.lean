import Mathlib

namespace PresentedGroup

/-- The element of a presented group represented by a finite word. -/
abbrev evalWord {α : Type*} (rels : Set (FreeGroup α)) (w : List (α × Bool)) :
    PresentedGroup rels :=
  mk rels (FreeGroup.mk w)

end PresentedGroup

/-- A finite word is geodesic for the presentation with relators `rels` if no shorter finite word
represents the same element of the presented group. A letter is represented by `(a, true)`, and the
formal inverse letter by `(a, false)`. -/
def IsGeodesicWord {α : Type*} (rels : Set (FreeGroup α)) (w : List (α × Bool)) : Prop :=
  ∀ v, PresentedGroup.evalWord rels v = PresentedGroup.evalWord rels w → w.length ≤ v.length

namespace Heisenberg

/-!
# The discrete Heisenberg group

Discrete Heisenberg group by the two-generator presentation
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`.
-/

/-- The two generators in the standard presentation of the discrete Heisenberg group. -/
inductive Generator where
  | x
  | y
  deriving DecidableEq

/-- The free-group word corresponding to the generator `x`. -/
abbrev X : FreeGroup Generator :=
  FreeGroup.of Generator.x

/-- The free-group word corresponding to the generator `y`. -/
abbrev Y : FreeGroup Generator :=
  FreeGroup.of Generator.y

/-- The relators `[[x, y], x]` and `[[x, y], y]` for the standard presentation. -/
abbrev relators : Set (FreeGroup Generator) :=
  {⁅⁅X, Y⁆, X⁆, ⁅⁅X, Y⁆, Y⁆}

/-- The discrete Heisenberg group, presented as
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`. -/
abbrev Group : Type :=
  PresentedGroup relators

/-- Geodesic finite words for the standard presentation of the discrete Heisenberg group. -/
abbrev IsGeodesic (w : List (Generator × Bool)) : Prop :=
  IsGeodesicWord relators w

end Heisenberg
