import Mathlib

open Filter

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

/-- Any element of `A` witnesses a non-trivial `1`-term progression in `A`. -/
theorem containsNontrivialOneTermAP_of_mem {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    ContainsNontrivialKTermAP 1 A := by
  refine ⟨a, 1, by decide, ?_⟩
  intro i hi
  have hi0 : i = 0 := Nat.lt_one_iff.mp hi
  subst hi0
  simpa using ha

/-- A finite set is `1`-term-AP-free iff it is empty. -/
theorem apfree_one_iff_eq_empty (A : Finset ℕ) : KTermAPFree 1 A ↔ A = ∅ := by
  constructor
  · intro hfree
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    exact hfree (containsNontrivialOneTermAP_of_mem ha)
  · intro hA
    subst hA
    simp [KTermAPFree, ContainsNontrivialKTermAP]

/-- Every admissible cardinal for `k = 1` is `0`. -/
theorem admissible_card_eq_zero_of_k_one {N m : ℕ} (hm : m ∈ admissibleSetCardinals 1 N) :
    m = 0 := by
  rcases hm with ⟨A, -, hfree, rfl⟩
  have hA : A = ∅ := (apfree_one_iff_eq_empty A).1 hfree
  simp [hA]

/-- Unconditional benchmark: `r_1(N) = 0` for all `N`. -/
theorem rk_one_eq_zero (N : ℕ) : rk 1 N = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine csSup_le' ?_
  intro m hm
  simp [admissible_card_eq_zero_of_k_one hm]

/-- Any finite set contains a non-trivial `0`-term progression (vacuously). -/
theorem containsNontrivialZeroTermAP (A : Finset ℕ) : ContainsNontrivialKTermAP 0 A := by
  refine ⟨0, 1, by decide, ?_⟩
  intro i hi
  exact (Nat.not_lt_zero _ hi).elim

/-- No finite set is `0`-term-AP-free. -/
theorem not_apfree_zero (A : Finset ℕ) : ¬ KTermAPFree 0 A := by
  intro hfree
  exact hfree (containsNontrivialZeroTermAP A)

/-- Every admissible cardinal for `k = 0` is impossible. -/
theorem not_mem_admissibleSetCardinals_zero (N m : ℕ) :
    m ∉ admissibleSetCardinals 0 N := by
  intro hm
  rcases hm with ⟨A, -, hfree, -⟩
  exact not_apfree_zero A hfree

/-- Unconditional benchmark: `r_0(N) = 0` for all `N`. -/
theorem rk_zero_eq_zero (N : ℕ) : rk 0 N = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine csSup_le' ?_
  intro m hm
  exact (not_mem_admissibleSetCardinals_zero N m hm).elim

/-- If `a < b` are both in `A`, they form a non-trivial `2`-term progression in `A`. -/
theorem containsNontrivialTwoTermAP_of_lt {A : Finset ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    ContainsNontrivialKTermAP 2 A := by
  refine ⟨a, b - a, Nat.sub_pos_of_lt hab, ?_⟩
  intro i hi
  interval_cases i
  · simpa
  · have hab' : a + (b - a) = b := Nat.add_sub_of_le (Nat.le_of_lt hab)
    simpa [one_mul, hab'] using hb

/-- Any `2`-term-AP-free finite set has cardinality at most `1`. -/
theorem apfree_two_card_le_one {A : Finset ℕ} (hfree : KTermAPFree 2 A) : A.card ≤ 1 := by
  by_contra hcard
  have htwo : 2 ≤ A.card := by omega
  have hone : 1 < A.card := by omega
  rcases Finset.one_lt_card.mp hone with ⟨a, ha, b, hb, hne⟩
  cases lt_or_gt_of_ne hne with
  | inl hab =>
      exact hfree (containsNontrivialTwoTermAP_of_lt ha hb hab)
  | inr hba =>
      exact hfree (containsNontrivialTwoTermAP_of_lt hb ha hba)

/-- Every admissible cardinal for `k = 2` is at most `1`. -/
theorem admissible_card_le_one_of_k_two {N m : ℕ} (hm : m ∈ admissibleSetCardinals 2 N) :
    m ≤ 1 := by
  rcases hm with ⟨A, -, hfree, rfl⟩
  exact apfree_two_card_le_one hfree

/-- Unconditional upper bound for `k = 2`: `r_2(N) ≤ 1`. -/
theorem rk_two_le_one (N : ℕ) : rk 2 N ≤ 1 := by
  refine csSup_le' ?_
  intro m hm
  exact admissible_card_le_one_of_k_two hm

/-- A singleton witness gives `r_2(N) ≥ 1` for all `N ≥ 1`. -/
theorem one_le_rk_two_of_one_le {N : ℕ} (hN : 1 ≤ N) : 1 ≤ rk 2 N := by
  have hmem : 1 ∈ admissibleSetCardinals 2 N := by
    refine ⟨{1}, ?_, singleton_one_apfree (by decide), by simp⟩
    intro x hx
    rcases Finset.mem_singleton.mp hx with rfl
    exact Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  exact le_csSup (admissibleSetCardinals_bddAbove 2 N) hmem

/-- Exact value for `k = 2` at positive `N`: `r_2(N) = 1`. -/
theorem rk_two_eq_one_of_pos {N : ℕ} (hN : 0 < N) : rk 2 N = 1 := by
  have hN' : 1 ≤ N := Nat.succ_le_of_lt hN
  exact Nat.le_antisymm (rk_two_le_one N) (one_le_rk_two_of_one_le hN')

/-- At `N = 1`, we have `r_k(1) = 0` whenever `k ≤ 1`. -/
theorem rk_at_one_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) : rk k 1 = 0 := by
  interval_cases k
  · simpa using rk_zero_eq_zero 1
  · simpa using rk_one_eq_zero 1

/-- Complete exact-value family at `N = 1`:
`r_k(1) = 0` for `k ≤ 1` and `r_k(1) = 1` for `k ≥ 2`. -/
theorem rk_at_one_eq_ite (k : ℕ) : rk k 1 = if k ≤ 1 then 0 else 1 := by
  by_cases hk : k ≤ 1
  · simp [hk, rk_at_one_eq_zero_of_le_one hk]
  · have hk2 : 2 ≤ k := by omega
    simp [hk, rk_one_eq_one_of_two_le hk2]

/-- Complete exact characterization for `k = 2`. -/
theorem rk_two_eq_ite (N : ℕ) : rk 2 N = if N = 0 then 0 else 1 := by
  by_cases hN : N = 0
  · simp [hN, rk_zero]
  · have hpos : 0 < N := Nat.pos_of_ne_zero hN
    simp [hN, rk_two_eq_one_of_pos hpos]

/-- There is an asymptotic formula for `r_k(N)` (formalized as asymptotic equivalence to some
comparison function). -/
def HasAsymptoticFormula (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ,
    (fun N => (rk k N : ℝ)) =Θ[atTop] f

/-- Constrained explicit profile templates used to make asymptotic targets non-tautological. -/
inductive ExplicitProfileClass : ℕ → (ℕ → ℝ) → Prop
  | k3 (β c C : ℝ) (hβ : 0 < β) (hc : 0 < c) (hC : 0 < C) :
      ExplicitProfileClass 3
        (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β))
  | k4 (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
      ExplicitProfileClass 4
        (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c)
  | kge5 (k : ℕ) (hk : 5 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
      ExplicitProfileClass k
        (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c)

/-- Strengthened asymptotic-formula target: `r_k` is `Θ` of an explicit profile template. -/
def HasExplicitAsymptoticFormula (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, ExplicitProfileClass k f ∧
    (fun N => (rk k N : ℝ)) =Θ[atTop] f

/-- Strengthened (non-tautological) version of Problem #142 using explicit profile classes. -/
def erdos_problem_142_explicit : Prop :=
  ∀ ⦃k : ℕ⦄, 3 ≤ k → HasExplicitAsymptoticFormula k

/-- Any explicit-profile asymptotic formula is, in particular, an asymptotic formula. -/
theorem hasExplicitAsymptoticFormula_implies_hasAsymptoticFormula {k : ℕ}
    (h : HasExplicitAsymptoticFormula k) : HasAsymptoticFormula k := by
  rcases h with ⟨f, -, hf⟩
  exact ⟨f, hf⟩

/--
Erdős Problem #142:
"Let `r_k(N)` be the largest possible size of a subset of `{1,…,N}` that does not contain any
non-trivial `k`-term arithmetic progression. Prove an asymptotic formula for `r_k(N)`."

Formalized as: for each fixed `k ≥ 3`, `r_k` has an asymptotic formula.
-/
def erdos_problem_142 : Prop :=
  ∀ ⦃k : ℕ⦄, 3 ≤ k → HasAsymptoticFormula k

/-- The strengthened explicit target implies the existing statement-level formalization. -/
theorem erdos_problem_142_explicit_implies_erdos_problem_142
    (h : erdos_problem_142_explicit) : erdos_problem_142 := by
  intro k hk
  exact hasExplicitAsymptoticFormula_implies_hasAsymptoticFormula (h hk)

end ErdosProblems

namespace Erdos142

noncomputable abbrev r := ErdosProblems.rk

/-- DeepMind `formal-conjectures`-aligned statement shape for Problem #142. -/
def erdos_142 (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, (fun N => (r k N : ℝ)) =Θ[atTop] f

/-- DeepMind-style shape for the strengthened explicit-profile target. -/
def erdos_142_explicit (k : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, ErdosProblems.ExplicitProfileClass k f ∧
    (fun N => (r k N : ℝ)) =Θ[atTop] f

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

/-- The strongest theorem-level `k = 3` endpoint currently supported by the repository:
there exist explicit source-backed lower and upper profiles for the `k = 3` branch, with imported
upper exponent `1 / 12`, together with the true compatibility direction between them. This is
weaker than `erdos_142 3`, but unlike the matched-profile route it does not rely on the current
frontier axioms. -/
def erdos_142_three_source_backed_split : Prop :=
  ∃ cL CL cU CU : ℝ,
    0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)) ∧
      (fun N => (r 3 N : ℝ)) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 12))) ∧
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 12)))

/-- Any explicit source-backed `k = 3` split sandwich on the `β = 1 / 12` scale realizes the
honest theorem-level endpoint. -/
theorem erdos_142_three_source_backed_split_of_bounds
    {cL CL cU CU : ℝ}
    (hcL : 0 < cL) (hCL : 0 < CL) (hcU : 0 < cU) (hCU : 0 < CU)
    (hLower :
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)))
    (hUpper :
      (fun N => (r 3 N : ℝ)) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 12))))
    (hCompatibility :
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 12)))) :
    erdos_142_three_source_backed_split :=
  ⟨cL, CL, cU, CU, hcL, hCL, hcU, hCU, hLower, hUpper, hCompatibility⟩

/-- Conjectural theorem-level `k = 3` endpoint for the explicit post-Behrend `β = 1 / 8` route:
there exist explicit lower and upper profiles with the true compatibility direction between them.
This is still weaker than `erdos_142 3`; after the March 8, 2026 source audit it should be read as
an import/scaffolding surface rather than an audited source-backed theorem. -/
def erdos_142_three_source_backed_split_one_eighth : Prop :=
  ∃ cL CL cU CU : ℝ,
    0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)) ∧
      (fun N => (r 3 N : ℝ)) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8))) ∧
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8)))

/-- Any imported `k = 3` split sandwich on the conjectural `β = 1 / 8` scale realizes the
corresponding theorem-level endpoint. -/
theorem erdos_142_three_source_backed_split_one_eighth_of_bounds
    {cL CL cU CU : ℝ}
    (hcL : 0 < cL) (hCL : 0 < CL) (hcU : 0 < cU) (hCU : 0 < CU)
    (hLower :
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N => (r 3 N : ℝ)))
    (hUpper :
      (fun N => (r 3 N : ℝ)) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8))))
    (hCompatibility :
      (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
        (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ ((1 : ℝ) / 8)))) :
    erdos_142_three_source_backed_split_one_eighth :=
  ⟨cL, CL, cU, CU, hcL, hCL, hcU, hCU, hLower, hUpper, hCompatibility⟩

/-- Honest statement-level endpoint for the source-backed split route:
all upper variants are available, and each branch carries explicit split data on the source-backed
scale currently supported in the repository. This is weaker than `erdos_problem_142`, but unlike
the matched-profile route it does not rely on the current frontier axioms. -/
structure SourceBackedSplitRoute where
  upper : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142.variants.upper k
  k3 :
    ∃ cL CL β cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < β ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
          (fun N => (r 3 N : ℝ)) ∧
        (fun N => (r 3 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β)) ∧
        (fun N : ℕ => CL * (N : ℝ) * Real.exp (-cL * Real.sqrt (Real.log (N + 2)))) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-cU * (Real.log (N + 2)) ^ β))
  k4 :
    ∃ cL CL cU CU : ℝ,
      0 < cL ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ => CL * (N : ℝ) / (Real.log (N + 2)) ^ cL) =O[atTop]
          (fun N => (r 4 N : ℝ)) ∧
        (fun N => (r 4 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) / (Real.log (N + 2)) ^ cU)
  k5 :
    ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[atTop] (fun N => (r 5 N : ℝ)) ∧
        (fun N => (r 5 N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))
  kge6 :
    ∀ ⦃k : ℕ⦄, 6 ≤ k → ∃ α A B CL cU CU : ℝ,
      0 < α ∧ 0 < A ∧ 0 < CL ∧ 0 < cU ∧ 0 < CU ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[atTop] (fun N => (r k N : ℝ)) ∧
        (fun N => (r k N : ℝ)) =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU)) ∧
        (fun N : ℕ =>
          CL * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
          =O[atTop]
          (fun N : ℕ => CU * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ cU))

/-- The honest theorem-level endpoint currently supported by the repository:
there exists a full source-backed split route covering every branch. This is weaker than
`erdos_problem_142`, but unlike the matched-profile route it does not rely on the current frontier
axioms. -/
def erdos_142_source_backed_split : Prop :=
  Nonempty SourceBackedSplitRoute

/-- Any explicit source-backed split route realizes the honest theorem-level endpoint. -/
theorem erdos_142_source_backed_split_of_route (h : SourceBackedSplitRoute) :
    erdos_142_source_backed_split :=
  ⟨h⟩

/-- Parameter package for the architecture class isolated by the active negative `k = 3` route:
`a` controls rank growth per step, and `b` controls the pure local size-loss term. -/
structure K3ArchitectureBarrierParams where
  a : ℕ
  b : ℕ

namespace K3ArchitectureBarrierParams

/-- Total loss exponent propagated by the recurrence class:
`γ(a,b) = max(a + 3, b + 1)`. -/
def lossExponent (p : K3ArchitectureBarrierParams) : ℕ :=
  max (p.a + 3) (p.b + 1)

/-- Final stretched-exponential exponent propagated by the recurrence class:
`θ(a,b) = 1 / γ(a,b)`. -/
noncomputable def propagatedExponent (p : K3ArchitectureBarrierParams) : ℝ :=
  1 / (lossExponent p : ℝ)

/-- Behrend scale would require the propagated loss exponent to be at most `2`. -/
def behrendScaleViable (p : K3ArchitectureBarrierParams) : Prop :=
  lossExponent p ≤ 2

/-- Any recurrence in this architecture class has propagated loss exponent at least `3`. -/
theorem three_le_lossExponent (p : K3ArchitectureBarrierParams) : 3 ≤ lossExponent p := by
  dsimp [lossExponent]
  have h : 3 ≤ p.a + 3 := by omega
  exact le_trans h (le_max_left (p.a + 3) (p.b + 1))

/-- Therefore no recurrence in this architecture class is compatible with Behrend scale. -/
theorem not_behrendScaleViable (p : K3ArchitectureBarrierParams) : ¬ behrendScaleViable p := by
  intro h
  have hγ : 3 ≤ lossExponent p := three_le_lossExponent p
  have hlt : 2 < lossExponent p := lt_of_lt_of_le (by decide) hγ
  exact not_le_of_gt hlt h

end K3ArchitectureBarrierParams

/-- Parameters extracted from the current published `k = 3` recurrence. -/
def k3CurrentArchitectureBarrierParams : K3ArchitectureBarrierParams :=
  { a := 6, b := 7 }

/-- Parameters extracted from the first source-motivated local refinement. -/
def k3OneEighthArchitectureBarrierParams : K3ArchitectureBarrierParams :=
  { a := 5, b := 6 }

/-- The current published recurrence propagates total loss exponent `9`. -/
theorem k3CurrentArchitectureBarrierParams_lossExponent :
    k3CurrentArchitectureBarrierParams.lossExponent = 9 := by
  norm_num [k3CurrentArchitectureBarrierParams, K3ArchitectureBarrierParams.lossExponent]

/-- The current published recurrence therefore propagates final exponent `1 / 9`. -/
theorem k3CurrentArchitectureBarrierParams_propagatedExponent :
    k3CurrentArchitectureBarrierParams.propagatedExponent = (1 : ℝ) / 9 := by
  norm_num [K3ArchitectureBarrierParams.propagatedExponent,
    k3CurrentArchitectureBarrierParams_lossExponent]

/-- The first local refinement propagates total loss exponent `8`. -/
theorem k3OneEighthArchitectureBarrierParams_lossExponent :
    k3OneEighthArchitectureBarrierParams.lossExponent = 8 := by
  norm_num [k3OneEighthArchitectureBarrierParams, K3ArchitectureBarrierParams.lossExponent]

/-- The first local refinement therefore propagates final exponent `1 / 8`. -/
theorem k3OneEighthArchitectureBarrierParams_propagatedExponent :
    k3OneEighthArchitectureBarrierParams.propagatedExponent = (1 : ℝ) / 8 := by
  norm_num [K3ArchitectureBarrierParams.propagatedExponent,
    k3OneEighthArchitectureBarrierParams_lossExponent]

/-- Named theorem-level post-critic barrier endpoint for the currently extracted architecture. -/
def erdos_142_three_current_architecture_barrier : Prop :=
  ¬ K3ArchitectureBarrierParams.behrendScaleViable k3CurrentArchitectureBarrierParams

/-- The currently extracted architecture is not Behrend-scale viable. -/
theorem erdos_142_three_current_architecture_barrier_true :
    erdos_142_three_current_architecture_barrier := by
  exact K3ArchitectureBarrierParams.not_behrendScaleViable k3CurrentArchitectureBarrierParams

/-- Named theorem-level post-critic barrier endpoint for the first local refinement candidate. -/
def erdos_142_three_one_eighth_refinement_barrier : Prop :=
  ¬ K3ArchitectureBarrierParams.behrendScaleViable k3OneEighthArchitectureBarrierParams

/-- The first local refinement candidate also remains off the Behrend scale. -/
theorem erdos_142_three_one_eighth_refinement_barrier_true :
    erdos_142_three_one_eighth_refinement_barrier := by
  exact K3ArchitectureBarrierParams.not_behrendScaleViable k3OneEighthArchitectureBarrierParams

/-- Combined post-critic negative endpoint:
both the current extracted architecture and the first local refinement remain off the Behrend
scale. -/
def erdos_142_three_negative_route_stable : Prop :=
  erdos_142_three_current_architecture_barrier ∧
    erdos_142_three_one_eighth_refinement_barrier

/-- The current negative route is stable at the theorem surface encoded in this repository. -/
theorem erdos_142_three_negative_route_stable_true :
    erdos_142_three_negative_route_stable := by
  exact ⟨erdos_142_three_current_architecture_barrier_true,
    erdos_142_three_one_eighth_refinement_barrier_true⟩

namespace bound_targets

/-- Literature target corresponding to Kelley-Meka (2023): the `k = 3` upper-bound regime. -/
def k3_upper_kelley_meka : Prop :=
  erdos_142.variants.upper 3

/-- Literature target corresponding to Green-Tao (2017): the `k = 4` upper-bound regime. -/
def k4_upper_green_tao : Prop :=
  erdos_142.variants.upper 4

/-- Literature target corresponding to Leng-Sah-Sawhney (2024): upper bounds for all `k ≥ 5`. -/
def kge5_upper_leng_sah_sawhney : Prop :=
  ∀ ⦃k : ℕ⦄, 5 ≤ k → erdos_142.variants.upper k

/-- Behrend-type lower-profile target for `k = 3`.
This is a statement-shape placeholder for benchmark lower bounds from the literature. -/
def k3_behrend_lower_profile : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2))) ≤ (r 3 N : ℝ)

/-- Rate-template target for `k = 3`: super-polylogarithmic decay in an explicit `O`-profile. -/
def k3_superpolylog_upper_profile : Prop :=
  ∃ β c C : ℝ, 0 < β ∧ 0 < c ∧ 0 < C ∧
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β))

/-- Strengthened `k = 3` upper-profile target: same shape as
`k3_superpolylog_upper_profile`, but with the sharp exponent regime `β > 1/2`.
This is the exact literature-facing target needed by the current `k = 3` frontier-elimination
route. -/
def k3_superpolylog_upper_profile_gt_half : Prop :=
  ∃ β c C : ℝ, (1 : ℝ) / 2 < β ∧ 0 < c ∧ 0 < C ∧
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ β))

/-- The strengthened `β > 1/2` target implies the previously used weaker `β > 0` target. -/
theorem k3_superpolylog_upper_profile_of_gt_half :
    k3_superpolylog_upper_profile_gt_half → k3_superpolylog_upper_profile := by
  intro h
  rcases h with ⟨β, c, C, hβ, hc, hC, hUpper⟩
  refine ⟨β, c, C, ?_, hc, hC, hUpper⟩
  linarith

/-- Source-backed `k = 3` upper-profile target extracted from the Kelley-Meka paper using the
visible exponent coming from the `d^{12}` progression-count bound. -/
def k3_superpolylog_upper_profile_one_twelfth : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ ((1 : ℝ) / 12)))

/-- Candidate `k = 3` upper-profile target for the first concrete post-Behrend pivot:
the explicit `1/8` exponent suggested by the localized recurrence analysis, but not currently
backed by an audited published source in this repository. -/
def k3_superpolylog_upper_profile_one_eighth : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * (Real.log (N + 2)) ^ ((1 : ℝ) / 8)))

/-- Stronger natural `k = 3` upper-profile target on the Behrend scale. -/
def k3_behrend_scale_upper_profile : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N => (r 3 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N + 2))))

/-- The explicit Kelley-Meka-style `β = 1/12` target implies the weaker existential
superpolylogarithmic upper-profile target. -/
theorem k3_superpolylog_upper_profile_of_one_twelfth :
    k3_superpolylog_upper_profile_one_twelfth → k3_superpolylog_upper_profile := by
  intro h
  rcases h with ⟨c, C, hc, hC, hUpper⟩
  refine ⟨(1 : ℝ) / 12, c, C, ?_, hc, hC, hUpper⟩
  norm_num

/-- The explicit `β = 1/8` target implies the weaker existential superpolylogarithmic
upper-profile target. -/
theorem k3_superpolylog_upper_profile_of_one_eighth :
    k3_superpolylog_upper_profile_one_eighth → k3_superpolylog_upper_profile := by
  intro h
  rcases h with ⟨c, C, hc, hC, hUpper⟩
  refine ⟨(1 : ℝ) / 8, c, C, ?_, hc, hC, hUpper⟩
  norm_num

/-- A Behrend-scale `k = 3` upper theorem is, in particular, a superpolylogarithmic upper theorem
with exponent `β = 1/2`. -/
theorem k3_superpolylog_upper_profile_of_behrend_scale_upper_profile :
    k3_behrend_scale_upper_profile → k3_superpolylog_upper_profile := by
  intro h
  rcases h with ⟨c, C, hc, hC, hUpper⟩
  refine ⟨(1 : ℝ) / 2, c, C, ?_, hc, hC, ?_⟩
  · norm_num
  · simpa [Real.sqrt_eq_rpow] using hUpper

/-- Rate-template target for `k = 4`: polylogarithmic decay in an explicit `O`-profile. -/
def k4_polylog_upper_profile : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N => (r 4 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) / (Real.log (N + 2)) ^ c)

/-- Rate-template target for `k ≥ 5`: iterated-log decay in an explicit `O`-profile. -/
def kge5_iteratedlog_upper_profile : Prop :=
  ∀ ⦃k : ℕ⦄, 5 ≤ k →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N => (r k N : ℝ)) =O[atTop]
        (fun N : ℕ => C * (N : ℝ) / (Real.log (Real.log (N + 3))) ^ c)

/-- Branch-local source-backed upper-profile target for `k = 5`:
stretched-exponential decay in `log log N`, matching the Leng-Sah-Sawhney scale. -/
def k5_stretchedexp_loglog_upper_profile : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (fun N => (r 5 N : ℝ)) =O[atTop]
      (fun N : ℕ => C * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ c))

/-- Branch-local source-backed lower-profile target for `k = 5`:
Rankin/O'Bryant-type decay with an explicit positive `(\log N)^\alpha` term in the exponent. -/
def k5_rankin_obryant_lower_profile : Prop :=
  ∃ α A B C : ℝ, 0 < α ∧ 0 < A ∧ 0 < C ∧
    (fun N : ℕ =>
      C * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
      =O[atTop] (fun N => (r 5 N : ℝ))

/-- Tail-family source-backed upper-profile target for fixed `k ≥ 6`:
stretched-exponential decay in `log log N`, matching the Leng-Sah-Sawhney scale. -/
def kge6_stretchedexp_loglog_upper_profile : Prop :=
  ∀ ⦃k : ℕ⦄, 6 ≤ k →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (fun N => (r k N : ℝ)) =O[atTop]
        (fun N : ℕ => C * (N : ℝ) * Real.exp (-(Real.log (Real.log (N + 3))) ^ c))

/-- Tail-family source-backed lower-profile target for fixed `k ≥ 6`:
Rankin/O'Bryant-type decay with an explicit positive `(\log N)^\alpha` term in the exponent. -/
def kge6_rankin_obryant_lower_profile : Prop :=
  ∀ ⦃k : ℕ⦄, 6 ≤ k →
    ∃ α A B C : ℝ, 0 < α ∧ 0 < A ∧ 0 < C ∧
      (fun N : ℕ =>
        C * (N : ℝ) * Real.exp (-A * (Real.log (N + 3)) ^ α + B * Real.log (Real.log (N + 3))))
        =O[atTop] (fun N => (r k N : ℝ))

/-- Two-sided benchmark sandwich for `k = 3`: one lower profile and one upper profile. -/
def k3_two_sided_sandwich_profile : Prop :=
  k3_behrend_lower_profile ∧ k3_superpolylog_upper_profile

/-- Conditional asymptotic corollary target for `k = 3`. -/
def k3_sublinear : Prop :=
  (fun N => (r 3 N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

end bound_targets

/-- Small-case benchmark connection: `k = 2` already has an asymptotic formula
(indeed eventual equality to the constant `1`). -/
theorem erdos_142_two : erdos_142 2 := by
  refine ⟨fun _ => (1 : ℝ), ?_⟩
  have hEq : (fun N => (r 2 N : ℝ)) =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine (eventually_ge_atTop (1 : ℕ)).mono ?_
    intro N hN
    have hpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    simp [ErdosProblems.rk_two_eq_one_of_pos hpos]
  exact hEq.isTheta

/-- Consequently, the `upper` variant is immediate for `k = 2`. -/
theorem upper_variant_two : erdos_142.variants.upper 2 := by
  rcases erdos_142_two with ⟨f, hf⟩
  exact ⟨f, hf.1⟩

theorem hasAsymptoticFormula_iff_erdos142 (k : ℕ) :
    ErdosProblems.HasAsymptoticFormula k ↔ erdos_142 k := by
  rfl

theorem hasExplicitAsymptoticFormula_iff_erdos142_explicit (k : ℕ) :
    ErdosProblems.HasExplicitAsymptoticFormula k ↔ erdos_142_explicit k := by
  rfl

theorem erdos_142_explicit_implies_erdos_142 {k : ℕ}
    (h : erdos_142_explicit k) : erdos_142 k := by
  rcases h with ⟨f, -, hf⟩
  exact ⟨f, hf⟩

theorem erdos_problem_142_iff_deepmind :
    ErdosProblems.erdos_problem_142 ↔
      ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142 k := by
  constructor
  · intro h k hk
    exact (hasAsymptoticFormula_iff_erdos142 k).1 (h hk)
  · intro h k hk
    exact (hasAsymptoticFormula_iff_erdos142 k).2 (h hk)

theorem erdos_problem_142_explicit_iff_deepmind :
    ErdosProblems.erdos_problem_142_explicit ↔
      ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142_explicit k := by
  constructor
  · intro h k hk
    exact (hasExplicitAsymptoticFormula_iff_erdos142_explicit k).1 (h hk)
  · intro h k hk
    exact (hasExplicitAsymptoticFormula_iff_erdos142_explicit k).2 (h hk)

theorem erdos_problem_142_explicit_implies_erdos_problem_142_deepmind
    (h : ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142_explicit k) :
    ∀ ⦃k : ℕ⦄, 3 ≤ k → erdos_142 k := by
  intro k hk
  exact (hasAsymptoticFormula_iff_erdos142 k).1
    (ErdosProblems.erdos_problem_142_explicit_implies_erdos_problem_142
      ((erdos_problem_142_explicit_iff_deepmind).2 h) hk)

end Erdos142
