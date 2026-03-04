import Mathlib

namespace TaoExercises
namespace TaoBook
namespace Chapter2

/-- Tao, Exercise 2.3: the equation `x^4 + 131 = 3y^4`
has no integer solutions. -/
theorem exercise_2_3 : ¬ ∃ x y : ℤ, x ^ 4 + 131 = 3 * y ^ 4 := by
  intro h
  rcases h with ⟨x, y, hxy⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod' : (((x ^ 4 + 131 : ℤ) : ZMod 5) = ((3 * y ^ 4 : ℤ) : ZMod 5)) := by
    exact congrArg (fun t : ℤ => (t : ZMod 5)) hxy
  have hmod : ((x : ZMod 5) ^ 4 + (1 : ZMod 5)) = 3 * (y : ZMod 5) ^ 4 := by
    simpa using hmod'
  have hpow4_zero_or_one : ∀ a : ZMod 5, a ^ 4 = 0 ∨ a ^ 4 = 1 := by
    intro a
    by_cases ha : a = 0
    · left
      simp [ha]
    · right
      simpa using (ZMod.pow_card_sub_one_eq_one (p := 5) (a := a) ha)
  have hx : (x : ZMod 5) ^ 4 = 0 ∨ (x : ZMod 5) ^ 4 = 1 := hpow4_zero_or_one x
  have hy : (y : ZMod 5) ^ 4 = 0 ∨ (y : ZMod 5) ^ 4 = 1 := hpow4_zero_or_one y
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hmod0 := hmod
    simp [hx, hy] at hmod0
  · have : (1 : ZMod 5) = (3 : ZMod 5) := by simpa [hx, hy] using hmod
    have h13mod : 1 % 5 = 3 % 5 := (ZMod.natCast_eq_natCast_iff' 1 3 5).1 (by simpa using this)
    have h13false : ¬ (1 % 5 = 3 % 5) := by decide
    exact h13false h13mod
  · have : (2 : ZMod 5) = 0 := by simpa [hx, hy] using hmod
    have h20mod : 2 % 5 = 0 % 5 := (ZMod.natCast_eq_natCast_iff' 2 0 5).1 (by simpa using this)
    have h20false : ¬ (2 % 5 = 0 % 5) := by decide
    exact h20false h20mod
  · have : (2 : ZMod 5) = (3 : ZMod 5) := by simpa [hx, hy] using hmod
    have h23mod : 2 % 5 = 3 % 5 := (ZMod.natCast_eq_natCast_iff' 2 3 5).1 (by simpa using this)
    have h23false : ¬ (2 % 5 = 3 % 5) := by decide
    exact h23false h23mod

end Chapter2
end TaoBook
end TaoExercises
