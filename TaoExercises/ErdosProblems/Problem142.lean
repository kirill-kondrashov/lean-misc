import Mathlib

open Filter

namespace TaoExercises
namespace ErdosProblems

/-- A finite set of naturals contains a non-trivial `k`-term arithmetic progression if there are
`a,d` with `d > 0` such that all terms `a + i * d` (`i < k`) lie in the set. -/
def ContainsNontrivialKTermAP (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- `A` is progression-free for length `k` iff it contains no non-trivial `k`-term arithmetic
progression. -/
def KTermAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬ ContainsNontrivialKTermAP k A

/-- Admissible cardinalities for Problem #142: cardinalities of subsets of `{1, ..., N}` with no
non-trivial `k`-term arithmetic progression. -/
def admissibleSetCardinals (k N : ℕ) : Set ℕ :=
  {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ KTermAPFree k A ∧ A.card = m}

/-- The extremal function `r_k(N)`: largest size of a subset of `{1, ..., N}` with no non-trivial
`k`-term arithmetic progression. -/
noncomputable def rk (k N : ℕ) : ℕ := sSup (admissibleSetCardinals k N)

theorem zero_mem_admissibleSetCardinals (k N : ℕ) (hk : 1 ≤ k) :
    0 ∈ admissibleSetCardinals k N := by
  refine ⟨∅, by simp, ?_, by simp⟩
  intro hAP
  rcases hAP with ⟨a, d, hd, hmem⟩
  have h0k : 0 < k := Nat.succ_le_iff.mp hk
  have : a + 0 * d ∈ (∅ : Finset ℕ) := hmem 0 h0k
  simp at this

theorem admissible_card_le_N {k N m : ℕ} (hm : m ∈ admissibleSetCardinals k N) :
    m ≤ N := by
  rcases hm with ⟨A, hA, -, rfl⟩
  exact (Finset.card_le_card hA).trans (by
    simp [Nat.card_Icc])

theorem admissibleSetCardinals_bddAbove (k N : ℕ) :
    BddAbove (admissibleSetCardinals k N) := by
  refine ⟨N, ?_⟩
  intro m hm
  exact admissible_card_le_N hm

theorem rk_mem_admissibleSetCardinals (k N : ℕ) (hk : 1 ≤ k) :
    rk k N ∈ admissibleSetCardinals k N := by
  refine Nat.sSup_mem ?_ (admissibleSetCardinals_bddAbove k N)
  exact ⟨0, zero_mem_admissibleSetCardinals k N hk⟩

theorem exists_extremal_set (k N : ℕ) (hk : 1 ≤ k) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ KTermAPFree k A ∧ A.card = rk k N := by
  simpa [admissibleSetCardinals] using (rk_mem_admissibleSetCardinals k N hk)

theorem rk_le_N (k N : ℕ) : rk k N ≤ N := by
  exact csSup_le' (by
    intro m hm
    exact admissible_card_le_N hm)

theorem admissibleSetCardinals_mono {k N M : ℕ} (hNM : N ≤ M) :
    admissibleSetCardinals k N ⊆ admissibleSetCardinals k M := by
  intro m hm
  rcases hm with ⟨A, hA, hfree, hcard⟩
  refine ⟨A, ?_, hfree, hcard⟩
  intro x hxA
  rcases Finset.mem_Icc.mp (hA hxA) with ⟨hx1, hxN⟩
  exact Finset.mem_Icc.mpr ⟨hx1, le_trans hxN hNM⟩

theorem rk_mono {k N M : ℕ} (hNM : N ≤ M) : rk k N ≤ rk k M := by
  exact csSup_le_csSup' (admissibleSetCardinals_bddAbove k M) (admissibleSetCardinals_mono hNM)

theorem rk_zero (k : ℕ) : rk k 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using rk_le_N k 0)

theorem singleton_one_apfree {k : ℕ} (hk : 2 ≤ k) :
    KTermAPFree k ({1} : Finset ℕ) := by
  intro hAP
  rcases hAP with ⟨a, d, hd, hmem⟩
  have ha : a = 1 := by
    have : a + 0 * d ∈ ({1} : Finset ℕ) := hmem 0 (by omega)
    simpa [zero_mul] using this
  have ha1 : a + d = 1 := by
    have : a + 1 * d ∈ ({1} : Finset ℕ) := hmem 1 (by omega)
    simpa [one_mul] using this
  omega

theorem one_mem_admissibleSetCardinals_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    1 ∈ admissibleSetCardinals k 1 := by
  refine ⟨{1}, by simp, singleton_one_apfree hk, by simp⟩

theorem one_le_rk_of_two_le {k : ℕ} (hk : 2 ≤ k) : 1 ≤ rk k 1 := by
  exact le_csSup (admissibleSetCardinals_bddAbove k 1) (one_mem_admissibleSetCardinals_of_two_le hk)

theorem rk_one_eq_one_of_two_le {k : ℕ} (hk : 2 ≤ k) : rk k 1 = 1 := by
  exact Nat.le_antisymm (by simpa using rk_le_N k 1) (one_le_rk_of_two_le hk)

/-- There is an asymptotic formula for `r_k(N)` (formalized as asymptotic equivalence to some
comparison function). -/
def HasAsymptoticFormula (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ,
    (fun N => (rk k N : ℝ)) =Θ[atTop] f

/--
Erdős Problem #142:
"Let `r_k(N)` be the largest possible size of a subset of `{1,…,N}` that does not contain any
non-trivial `k`-term arithmetic progression. Prove an asymptotic formula for `r_k(N)`."

Formalized as: for each fixed `k ≥ 3`, `r_k` has an asymptotic formula.
-/
def erdos_problem_142 : Prop :=
  ∀ ⦃k : ℕ⦄, 3 ≤ k → HasAsymptoticFormula k

end ErdosProblems
end TaoExercises

namespace Erdos142

noncomputable abbrev r := TaoExercises.ErdosProblems.rk

/-- DeepMind `formal-conjectures`-aligned statement shape for Problem #142. -/
def erdos_142 (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, (fun N => (r k N : ℝ)) =Θ[atTop] f

namespace erdos_142
namespace variants

/-- Lower-bound variant from the reference formalization. -/
def lower (k : ℕ) (_hk : 1 < k) : Prop :=
  (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)

/-- Upper-bound variant from the reference formalization. -/
def upper (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, (fun N => (r k N : ℝ)) =O[atTop] f

/-- `k = 3` variant from the reference formalization. -/
def three : Prop :=
  ∃ f : ℕ → ℝ, (fun N => (r 3 N : ℝ)) =Θ[atTop] f

end variants
end erdos_142

theorem hasAsymptoticFormula_iff_erdos142 (k : ℕ) :
    TaoExercises.ErdosProblems.HasAsymptoticFormula k ↔ erdos_142 k := by
  rfl

theorem erdos_problem_142_iff_deepmind :
    TaoExercises.ErdosProblems.erdos_problem_142 ↔
      ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142 k := by
  constructor
  · intro h k hk
    exact (hasAsymptoticFormula_iff_erdos142 k).1 (h hk)
  · intro h k hk
    exact (hasAsymptoticFormula_iff_erdos142 k).2 (h hk)

end Erdos142
