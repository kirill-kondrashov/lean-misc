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
  (hf : realCont f):
  realCont (fun x : ℝ => a*(f x) + b) := by
  apply real_cont_comp (fun y : ℝ => y + b) (fun x : ℝ => a * f x)
  · exact real_cont_scale f a hf
  · unfold realCont
    intro x ε hε
    use ε, hε
    intro y hy
    simpa using hy

theorem real_cont_const (c : ℝ) :
  realCont (fun _ : ℝ => c) := by
  unfold realCont
  intro x ε hε
  use ε, hε
  intro y hy
  simpa using hε

theorem real_cont_id :
  realCont (fun x : ℝ => x) := by
  unfold realCont
  intro x ε hε
  use ε, hε
  intro y hy
  simpa [abs_sub_comm] using hy

theorem real_cont_add (f g : ℝ → ℝ)
  (hf : realCont f) (hg : realCont g) :
  realCont (fun x : ℝ => f x + g x) := by
  unfold realCont
  intro x ε hε
  have hε2 : 0 < ε / 2 := by positivity
  specialize hf x (ε / 2) hε2
  specialize hg x (ε / 2) hε2
  choose δf δfpos hδf using hf
  choose δg δgpos hδg using hg
  use min δf δg
  use lt_min δfpos δgpos
  intro y hy
  have hyf : |x - y| < δf := lt_of_lt_of_le hy (min_le_left _ _)
  have hyg : |x - y| < δg := lt_of_lt_of_le hy (min_le_right _ _)
  specialize hδf y hyf
  specialize hδg y hyg
  have hsum : |f x - f y| + |g x - g y| < ε := by linarith
  calc
    |(f x + g x) - (f y + g y)| ≤ |f x - f y| + |g x - g y| := by
      simpa [add_sub_add_comm] using abs_add_le (f x - f y) (g x - g y)
    _ < ε := hsum

theorem real_cont_mul (f g : ℝ → ℝ)
  (hf : realCont f) (hg : realCont g) :
  realCont (fun x : ℝ => f x * g x) := by
  unfold realCont
  intro x ε hε
  have hbf : 0 < |f x| + 1 := by positivity
  have hbg : 0 < |g x| + 1 := by positivity
  have hεf : 0 < ε / (2 * (|g x| + 1)) := by positivity
  have hεg : 0 < ε / (2 * (|f x| + 1)) := by positivity
  have hgbound := hg
  specialize hf x (ε / (2 * (|g x| + 1))) hεf
  specialize hg x (ε / (2 * (|f x| + 1))) hεg
  have h1 : (0 : ℝ) < 1 := by norm_num
  specialize hgbound x 1 h1
  choose δf δfpos hδf using hf
  choose δg δgpos hδg using hg
  choose δb δbpos hδb using hgbound
  use min δf (min δg δb)
  use lt_min δfpos (lt_min δgpos δbpos)
  intro y hy
  have hyf : |x - y| < δf := lt_of_lt_of_le hy (min_le_left _ _)
  have hyg : |x - y| < δg :=
    lt_of_lt_of_le (lt_of_lt_of_le hy (min_le_right _ _)) (min_le_left _ _)
  have hyb : |x - y| < δb :=
    lt_of_lt_of_le (lt_of_lt_of_le hy (min_le_right _ _)) (min_le_right _ _)
  specialize hδf y hyf
  specialize hδg y hyg
  specialize hδb y hyb
  have hgy_bound : |g y| ≤ |g x| + 1 := by
    have hdist : |g y - g x| < 1 := by simpa [abs_sub_comm] using hδb
    have hle : |g y| ≤ |g y - g x| + |g x| := by
      simpa [sub_add_cancel] using abs_add_le (g y - g x) (g x)
    linarith
  have hterm1 : |f x| * |g x - g y| < ε / 2 := by
    have hle : |f x| ≤ |f x| + 1 := by linarith [abs_nonneg (f x)]
    have hmul := mul_lt_mul_of_nonneg_of_pos' hle hδg (abs_nonneg (g x - g y)) hbf
    have hcalc : (|f x| + 1) * (ε / (2 * (|f x| + 1))) = ε / 2 := by
      field_simp [ne_of_gt hbf]
    nlinarith
  have hterm2 : |g y| * |f x - f y| < ε / 2 := by
    have hmul := mul_lt_mul_of_nonneg_of_pos' hgy_bound hδf (abs_nonneg (f x - f y)) hbg
    have hcalc : (|g x| + 1) * (ε / (2 * (|g x| + 1))) = ε / 2 := by
      field_simp [ne_of_gt hbg]
    nlinarith
  have hsum : |f x| * |g x - g y| + |g y| * |f x - f y| < ε := by linarith
  calc
    |f x * g x - f y * g y|
        = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
    _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
      have h := abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h
    _ < ε := hsum

theorem real_cont_polynomial_eval (p : Polynomial ℝ) :
  realCont (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa using real_cont_add (fun x : ℝ => p.eval x) (fun x : ℝ => q.eval x) hp hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      apply real_cont_scale
      induction n with
      | zero =>
          simpa using real_cont_const 1
      | succ n hn =>
          simpa [pow_succ] using
            real_cont_mul (fun x : ℝ => x ^ n) (fun x : ℝ => x) hn real_cont_id

theorem real_cont_polynomial (f : ℝ → ℝ) (p : Polynomial ℝ)
  (hf : realCont f) :
  realCont (fun x : ℝ => p.eval (f x)) := by
  apply real_cont_comp (fun y : ℝ => p.eval y) f
  · exact hf
  · exact real_cont_polynomial_eval p
