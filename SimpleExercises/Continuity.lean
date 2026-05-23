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

theorem real_cont_scale' (f : ℝ → ℝ) (a : ℝ)
  (hf : realCont f) (ha: a > 0):
  realCont ((fun y : ℝ => a * y) ∘ f) := by
  apply real_cont_comp
  · exact hf
  · unfold realCont
    intro x ε hε
    use ε / a
    use div_pos hε ha
    intro y hy
    calc
      |a * x - a * y| = a * |x - y|
      := by rw [← mul_sub, abs_mul, abs_of_pos ha]
      _ < a * (ε / a) := mul_lt_mul_of_pos_left hy ha
      _ = ε := by field_simp [ne_of_gt ha]

theorem real_cont_scale (f : ℝ → ℝ) (a : ℝ)
  (hf : realCont f) (ha: a > 0):
  realCont (fun x : ℝ => a * (f x)) := by
  exact real_cont_scale' f a hf ha
