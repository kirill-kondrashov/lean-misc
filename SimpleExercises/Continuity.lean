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

theorem real_cont_scale_non_zero' (f : ℝ → ℝ) (a : ℝ)
  (hf : realCont f) (ha: a ≠ 0):
  realCont ((fun y : ℝ => a * y) ∘ f) := by
  apply real_cont_comp
  · exact hf
  · unfold realCont
    intro x ε hε
    have hapos : 0 < |a| := abs_pos.mpr ha
    use ε / |a|
    use div_pos hε hapos
    intro y hy
    have h : |a| * |x - y| < |a| * (ε / |a|) :=
      mul_lt_mul_of_pos_left hy hapos
    have hε' : |a| * (ε / |a|) = ε := by field_simp [ha]
    simpa [← mul_sub, abs_mul, hε'] using h

theorem real_cont_scale_non_zero (f : ℝ → ℝ) (a : ℝ)
  (hf : realCont f) (ha: a ≠ 0):
  realCont (fun x : ℝ => a * (f x)) := by
  exact real_cont_scale_non_zero' f a hf ha


theorem real_cont_scale (f : ℝ → ℝ) (a : ℝ) (hf: realCont f):
  realCont (fun x : ℝ => a * (f x)) := by
  by_cases ha : a = 0
  · subst a
    unfold realCont
    intro x ε hε
    use ε, hε
    intro y hy
    simpa using hε
  · exact real_cont_scale_non_zero f a hf ha

theorem real_cont_linear_transform (f : ℝ → ℝ) (a b : ℝ)
  (hf: realCont f):
  realCont (fun x : ℝ => a*(f x) + b) := by
  apply real_cont_comp (fun y : ℝ => y + b) (fun x : ℝ => a * f x)
  · exact real_cont_scale f a hf
  · unfold realCont
    intro x ε hε
    use ε, hε
    intro y hy
    simpa using hy
