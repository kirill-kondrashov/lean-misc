import Mathlib

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

local notation "X" => (FreeGroup.of Generator.x : FreeGroup Generator)
local notation "Y" => (FreeGroup.of Generator.y : FreeGroup Generator)

/-- The discrete Heisenberg group, presented as
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`. -/
abbrev Group : Type :=
  PresentedGroup ({⁅⁅X, Y⁆, X⁆, ⁅⁅X, Y⁆, Y⁆} : Set (FreeGroup Generator))

end Heisenberg
