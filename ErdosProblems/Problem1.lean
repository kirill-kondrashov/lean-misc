import Mathlib

open Filter
open scoped Topology Real

namespace Erdos1

/--
A finite set `A` of naturals is sum-distinct in `{1, ..., N}` if it is contained in that interval
and every subset of `A` has a different sum.
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (fun (S : A.powerset) => S.1.sum id).Injective

/-- There exists a sum-distinct subset of `{1, ..., N}` of cardinality `k`. -/
def HasSumDistinctSetCard (N k : ℕ) : Prop :=
  ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = k

/--
Erdos problem 1: if `A ⊆ {1, ..., N}` has distinct subset sums, then `N` must be exponentially
large in `|A|`.
-/
axiom erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    N ≠ 0 → C * 2 ^ A.card < N

/-- Sum-distinctness means the subset-sum finset has the full powerset cardinality. -/
theorem subsetSum_card_eq_two_pow_card {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) : A.subsetSum.card = 2 ^ A.card := by
  rcases h with ⟨-, hInj⟩
  have hInjOn : Set.InjOn (fun B : Finset ℕ => B.sum id) A.powerset := by
    intro B hB C hC hsum
    exact congrArg Subtype.val <| hInj <|
      show (fun S : A.powerset => S.1.sum id) ⟨B, hB⟩ =
          (fun S : A.powerset => S.1.sum id) ⟨C, hC⟩ from hsum
  calc
    A.subsetSum.card = A.powerset.card := by
      simpa [Finset.subsetSum] using (Finset.card_image_of_injOn hInjOn)
    _ = 2 ^ A.card := Finset.card_powerset A

/-- `IsSumDistinctSet` is equivalent to the subset-sum finset having full powerset cardinality. -/
theorem isSumDistinctSet_iff_subsetSum_card {A : Finset ℕ} {N : ℕ} :
    IsSumDistinctSet A N ↔ A ⊆ Finset.Icc 1 N ∧ A.subsetSum.card = 2 ^ A.card := by
  constructor
  · intro h
    exact ⟨h.1, subsetSum_card_eq_two_pow_card h⟩
  · rintro ⟨hA, hcard⟩
    have hInjOn : Set.InjOn (fun B : Finset ℕ => B.sum id) A.powerset := by
      apply Finset.card_image_iff.mp
      calc
        (A.powerset.image fun B : Finset ℕ => B.sum id).card = A.subsetSum.card := by
          rfl
        _ = 2 ^ A.card := hcard
        _ = A.powerset.card := (Finset.card_powerset A).symm
    refine ⟨hA, ?_⟩
    intro S T hsum
    apply Subtype.ext
    exact hInjOn S.2 T.2 hsum

/-- Every subset sum lies in the interval `[0, |A| N]`. -/
theorem subsetSum_subset_Icc {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    A.subsetSum ⊆ Finset.Icc 0 (A.card * N) := by
  intro x hx
  rcases Finset.mem_subsetSum_iff.mp hx with ⟨B, hB, rfl⟩
  refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
  calc
    ∑ b ∈ B, b ≤ ∑ _b ∈ B, N := by
      refine Finset.sum_le_sum ?_
      intro b hb
      exact (Finset.mem_Icc.mp (hA (hB hb))).2
    _ = B.card * N := by simp
    _ ≤ A.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hB)

/-- Elementary counting bound: distinct subset sums force `2 ^ |A| ≤ |A| N + 1`. -/
theorem two_pow_card_le_card_mul_add_one {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) : 2 ^ A.card ≤ A.card * N + 1 := by
  calc
    2 ^ A.card = A.subsetSum.card := (subsetSum_card_eq_two_pow_card h).symm
    _ ≤ (Finset.Icc 0 (A.card * N)).card := Finset.card_le_card (subsetSum_subset_Icc h.1)
    _ = A.card * N + 1 := by simp [Nat.card_Icc]

/-- Finite-search reformulation of `HasSumDistinctSetCard`. -/
theorem hasSumDistinctSetCard_iff {N k : ℕ} :
    HasSumDistinctSetCard N k ↔
      ∃ A ∈ (Finset.Icc 1 N).powersetCard k,
        (fun (S : A.powerset) => S.1.sum id).Injective := by
  constructor
  · rintro ⟨A, ⟨hA, hInj⟩, hcard⟩
    refine ⟨A, ?_, hInj⟩
    exact Finset.mem_powersetCard.mpr ⟨hA, hcard⟩
  · rintro ⟨A, hA, hInj⟩
    refine ⟨A, ?_, (Finset.mem_powersetCard.mp hA).2⟩
    exact ⟨(Finset.mem_powersetCard.mp hA).1, hInj⟩

/-- Monotonicity in the ambient interval for exact-cardinality sum-distinct existence. -/
theorem hasSumDistinctSetCard_mono {N M k : ℕ} (hNM : N ≤ M) :
    HasSumDistinctSetCard N k → HasSumDistinctSetCard M k := by
  rintro ⟨A, ⟨hA, hInj⟩, hcard⟩
  refine ⟨A, ?_, hcard⟩
  refine ⟨?_, hInj⟩
  intro x hx
  rcases Finset.mem_Icc.mp (hA hx) with ⟨hx1, hxN⟩
  exact Finset.mem_Icc.mpr ⟨hx1, le_trans hxN hNM⟩

/-- Trivial weaker lower bound with an extra factor `1 / |A|`. -/
theorem erdos_1.variants.weaker : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
    IsSumDistinctSet A N → N ≠ 0 → C * 2 ^ A.card / A.card < N := by
  refine ⟨(1 / 4 : ℝ), by norm_num, ?_⟩
  intro N A hA hN
  by_cases hcard0 : A.card = 0
  · have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    simpa [hcard0] using hNpos
  · have hcount := two_pow_card_le_card_mul_add_one hA
    have hcountR : ((2 : ℝ) ^ A.card) ≤ (A.card : ℝ) * N + 1 := by
      exact_mod_cast hcount
    have hcard_pos : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard0)
    have hprod_ge_one_nat : 1 ≤ A.card * N := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hcard0) (Nat.pos_of_ne_zero hN))
    have hprod_ge_one : (1 : ℝ) ≤ (A.card : ℝ) * N := by
      exact_mod_cast hprod_ge_one_nat
    have hcountR' : ((2 : ℝ) ^ A.card) ≤ 2 * ((A.card : ℝ) * N) := by
      nlinarith
    have hbound : (1 / 4 : ℝ) * (2 : ℝ) ^ A.card / A.card ≤ N / 2 := by
      rw [div_le_iff₀ hcard_pos]
      nlinarith [hcountR']
    have hhalf_lt : (N : ℝ) / 2 < N := by
      have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      nlinarith
    exact lt_of_le_of_lt hbound hhalf_lt

/-- Erdős-Moser lower-bound variant. -/
axiom erdos_1.variants.lb : ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/-- Stronger lower-bound variant with constant `sqrt (2 / pi)`. -/
axiom erdos_1.variants.lb_strong : ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

/--
A finite set of reals is sum-distinct in `(0, N]` if all subset sums differ by at least `1`.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  (A : Set ℝ) ⊆ Set.Ioc (0 : ℝ) N ∧
    (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
      1 ≤ dist (S₁.sum id) (S₂.sum id)

/-- Real-valued generalization proposed by Erdős and Graham. -/
axiom erdos_1.variants.real : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℝ),
    IsSumDistinctRealSet A N → N ≠ 0 → C * 2 ^ A.card < N

theorem isSumDistinctSet_124 : IsSumDistinctSet ({1, 2, 4} : Finset ℕ) 4 := by
  native_decide

theorem not_isSumDistinctSet_Icc_3 : ¬ IsSumDistinctSet (Finset.Icc 1 3) 3 := by
  native_decide

/-- The least `N` supporting a 3-element sum-distinct set is `4`. -/
theorem erdos_1.variants.least_N_3 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 3 } 4 := by
  refine ⟨⟨{1, 2, 4}, isSumDistinctSet_124, by decide⟩, ?_⟩
  intro n hn
  rcases hn with ⟨A, hA, hcardA⟩
  rcases hA with ⟨hA, hInj⟩
  have hcard_le : A.card ≤ n := by
    exact (Finset.card_le_card hA).trans (by simp [Nat.card_Icc])
  by_cases hn4 : 4 ≤ n
  · exact hn4
  · have hn3 : n ≤ 3 := by omega
    interval_cases n
    · omega
    · omega
    · omega
    · have hEq : A = Finset.Icc 1 3 := by
        exact (Finset.subset_iff_eq_of_card_le (by simp [hcardA, Nat.card_Icc])).mp hA
      subst A
      exfalso
      exact not_isSumDistinctSet_Icc_3 ⟨subset_rfl, hInj⟩

/-- There exists a 5-element sum-distinct subset of `{1, ..., 13}`. -/
theorem hasSumDistinctSetCard_five_13 : HasSumDistinctSetCard 13 5 := by
  rw [hasSumDistinctSetCard_iff]
  native_decide

/-- There is no 5-element sum-distinct subset of `{1, ..., 12}`. -/
theorem not_hasSumDistinctSetCard_five_12 : ¬ HasSumDistinctSetCard 12 5 := by
  rw [hasSumDistinctSetCard_iff]
  native_decide

/-- OEIS A276661: the least `N` supporting a 5-element sum-distinct set is `13`. -/
theorem erdos_1.variants.least_N_5 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 13 := by
  refine ⟨hasSumDistinctSetCard_five_13, ?_⟩
  intro n hn
  by_cases h13 : 13 ≤ n
  · exact h13
  · have hn12 : n ≤ 12 := by omega
    exfalso
    exact not_hasSumDistinctSetCard_five_12
      (hasSumDistinctSetCard_mono hn12 hn)

/-- OEIS A276661: the least `N` supporting a 9-element sum-distinct set is `161`. -/
axiom erdos_1.variants.least_N_9 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 9 } 161

end Erdos1
