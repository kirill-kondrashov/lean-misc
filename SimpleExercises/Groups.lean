import Mathlib

namespace Heisenberg

/-!
# The discrete Heisenberg group

This file defines the discrete Heisenberg group by the two-generator presentation
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`.
-/

/-- The two generators in the standard presentation of the discrete Heisenberg group. -/
inductive Generator where
  | x
  | y
  deriving DecidableEq

/-- The relators `[[x, y], x]` and `[[x, y], y]` in the free group on `x` and `y`. -/
def relators : Set (FreeGroup Generator) :=
  {⁅⁅FreeGroup.of Generator.x, FreeGroup.of Generator.y⁆, FreeGroup.of Generator.x⁆,
    ⁅⁅FreeGroup.of Generator.x, FreeGroup.of Generator.y⁆, FreeGroup.of Generator.y⁆}

/-- The discrete Heisenberg group, presented as
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`. -/
abbrev Group : Type :=
  PresentedGroup relators

/-- The image of the generator `x` in the discrete Heisenberg group. -/
abbrev x : Group :=
  PresentedGroup.of Generator.x

/-- The image of the generator `y` in the discrete Heisenberg group. -/
abbrev y : Group :=
  PresentedGroup.of Generator.y

end Heisenberg
