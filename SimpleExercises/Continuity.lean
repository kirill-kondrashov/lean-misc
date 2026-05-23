import Mathlib

def realCont(f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |x - y| < δ → |f x - f y| < ε

theorem real_cont_comp(f g : ℝ → ℝ)
  (hg : realCont g) (hf : realCont f):
  realCont (f ∘ g) := by
  unfold realCont
  intro x ε hε
  specialize hf (g x)
  specialize hf ε hε
  choose ξ ξpos hξ using hf
  specialize hg x ξ ξpos
  choose δ δpos hδ using hg
  use δ, δpos
  intro y ω
  specialize hδ y ω
  specialize hξ (g y) hδ
  exact hξ
