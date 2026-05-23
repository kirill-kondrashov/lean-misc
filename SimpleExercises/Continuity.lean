import Mathlib

def RealCont(f: ℝ → ℝ) (c: ℝ) : Prop :=
  ∀ x : ℝ, ∀ε > 0, ∃δ > 0, |x - c| < δ → |f x - f c| < ε

theorem realCont_comp(f g: ℝ → ℝ) (c: ℝ)
  (hg: RealCont g c) (hf: RealCont f (g c)):
  RealCont (f ∘ g) c := by
  intro x ε
  specialize hg
  specialize hf
  sorry
