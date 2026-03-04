import Mathlib

namespace TaoExercises
namespace TaoBook
namespace Chapter2

/-- Tao, Exercise 2.3: the equation `x^4 + 131 = 3y^4`
has no integer solutions. -/
theorem exercise_2_3 : ¬ ∃ x y : ℤ, x ^ 4 + 131 = 3 * y ^ 4 := by
  intro h
  rcases h with ⟨x, y, hxy⟩
  have hmod' : (((x ^ 4 + 131 : ℤ) : ZMod 5) = ((3 * y ^ 4 : ℤ) : ZMod 5)) := by
    exact congrArg (fun t : ℤ => (t : ZMod 5)) hxy
  have hmod : ((x : ZMod 5) ^ 4 + (131 : ZMod 5)) = 3 * (y : ZMod 5) ^ 4 := by
    simpa using hmod'
  have hno : ¬ ∃ a b : ZMod 5, a ^ 4 + (131 : ZMod 5) = 3 * b ^ 4 := by
    native_decide
  exact hno ⟨x, y, hmod⟩

end Chapter2
end TaoBook
end TaoExercises
