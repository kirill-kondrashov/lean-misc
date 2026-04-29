import ErdosProblems.Problem1CubeExposedRepair
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Erdos1

/-- Fixed-rank subsets of `Fin n`. This is the natural ambient type for a shifted rank slice. -/
abbrev RankSlice (n r : ℕ) := { s : Finset (Fin n) // s.card = r }

namespace RankSlice

variable {n r : ℕ}

/-- Increasing coordinate parametrization of a fixed-rank subset. -/
def coords (s : RankSlice n r) : Fin r ↪o Fin n :=
  s.1.orderEmbOfFin s.2

/-- Sum of the coordinates of a fixed-rank subset. -/
def coordSum (s : RankSlice n r) : ℕ :=
  ∑ i, ((coords s i : Fin n) : ℕ)

/-- Componentwise shifted order on fixed-rank subsets. -/
def shiftedLE (s t : RankSlice n r) : Prop :=
  ∀ i : Fin r, coords s i ≤ coords t i

/-- Strict shifted order: componentwise domination together with strict coordinate-sum increase. -/
def shiftedLT (s t : RankSlice n r) : Prop :=
  shiftedLE s t ∧ coordSum s < coordSum t

theorem coordSum_le_card_mul_ground (s : RankSlice n r) :
    coordSum s ≤ r * n := by
  unfold coordSum
  calc
    ∑ i, ((coords s i : Fin n) : ℕ) ≤ ∑ _i : Fin r, n := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact Nat.le_of_lt (coords s i).is_lt
    _ = r * n := by simp

theorem shiftedLT_wellFounded (n r : ℕ) :
    WellFounded (shiftedLT (n := n) (r := r)) := by
  refine Subrelation.wf ?_ (InvImage.wf coordSum Nat.lt_wfRel.2)
  intro a b hab
  exact hab.2

def reverseCoordMeasure (n r : ℕ) (s : RankSlice n r) : ℕ :=
  r * n - coordSum s

theorem shiftedLT_reverse_wellFounded (n r : ℕ) :
    WellFounded (fun s t : RankSlice n r => shiftedLT (n := n) (r := r) t s) := by
  refine Subrelation.wf ?_ (InvImage.wf (reverseCoordMeasure n r) Nat.lt_wfRel.2)
  intro a b hab
  have hsum : coordSum b < coordSum a := hab.2
  have hbLt : coordSum b < r * n := lt_of_lt_of_le hsum (coordSum_le_card_mul_ground a)
  exact Nat.sub_lt_sub_left hbLt hsum

/-- The full rank slice is trivially lower in the shifted order. -/
theorem isRelLowerSet_univ (n r : ℕ) :
    IsRelLowerSet (shiftedLT (n := n) (r := r)) (Finset.univ : Finset (RankSlice n r)) := by
  intro a b hab hb
  simp

/-- Rank-`r` slice of subsets containing the distinguished coordinate `0`. -/
def containsZeroFamily (n r : ℕ) : Finset (RankSlice (n + 1) r) :=
  Finset.univ.filter fun s => (0 : Fin (n + 1)) ∈ s.1

theorem isRelLowerSet_containsZeroFamily (n r : ℕ) :
    IsRelLowerSet (shiftedLT (n := n + 1) (r := r)) (containsZeroFamily n r) := by
  intro s t hst ht
  rcases Finset.mem_filter.mp ht with ⟨-, hzero⟩
  by_cases hr : r = 0
  · have htcard0 : t.1.card = 0 := by simpa [hr] using t.2
    have hEmpty : t.1 = ∅ := Finset.card_eq_zero.mp htcard0
    simpa [hEmpty] using hzero
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hle0 := hst.1 ⟨0, hrpos⟩
    have htcoord0 : coords t ⟨0, hrpos⟩ = 0 := by
      rw [coords, Finset.orderEmbOfFin_zero t.2 hrpos]
      exact le_antisymm (Finset.min'_le _ _ hzero) (Fin.zero_le _)
    have hscoord0 : coords s ⟨0, hrpos⟩ = 0 := by
      exact le_antisymm (le_trans hle0 (by simpa [htcoord0])) (Fin.zero_le _)
    have hsMem : coords s ⟨0, hrpos⟩ ∈ s.1 :=
      Finset.orderEmbOfFin_mem s.1 s.2 ⟨0, hrpos⟩
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    simpa [hscoord0] using hsMem

end RankSlice

/-- The ambient two-layer fixed-rank type used by the shifted additive-stability route. -/
abbrev TwoLayerSlice (n m : ℕ) :=
  Sum (RankSlice n m) (RankSlice n (m + 1))

/-- Shifted relation on the two-layer state space: compare only within a fixed rank. -/
def twoLayerShiftedLT {n m : ℕ} :
    TwoLayerSlice n m → TwoLayerSlice n m → Prop
  | Sum.inl s, Sum.inl t => RankSlice.shiftedLT s t
  | Sum.inr s, Sum.inr t => RankSlice.shiftedLT s t
  | _, _ => False

theorem twoLayerShiftedLT_wellFounded (n m : ℕ) :
    WellFounded (twoLayerShiftedLT (n := n) (m := m)) := by
  refine Subrelation.wf ?_
    (InvImage.wf
      (fun x : TwoLayerSlice n m =>
        Sum.elim RankSlice.coordSum RankSlice.coordSum x)
      Nat.lt_wfRel.2)
  intro a b hab
  cases a <;> cases b
  · exact hab.2
  · cases hab
  · cases hab
  · exact hab.2

def twoLayerReverseMeasure (n m : ℕ) : TwoLayerSlice n m → ℕ
  | Sum.inl s => RankSlice.reverseCoordMeasure n m s
  | Sum.inr s => RankSlice.reverseCoordMeasure n (m + 1) s

theorem twoLayerShiftedLT_reverse_wellFounded (n m : ℕ) :
    WellFounded (fun a b : TwoLayerSlice n m => twoLayerShiftedLT (n := n) (m := m) b a) := by
  refine Subrelation.wf ?_ (InvImage.wf (twoLayerReverseMeasure n m) Nat.lt_wfRel.2)
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hsum : RankSlice.coordSum b < RankSlice.coordSum a := hab.2
          have hbLt : RankSlice.coordSum b < m * n := by
            exact lt_of_lt_of_le hsum (RankSlice.coordSum_le_card_mul_ground a)
          exact Nat.sub_lt_sub_left hbLt hsum
      | inr b =>
          cases hab
  | inr a =>
      cases b with
      | inl b =>
          cases hab
      | inr b =>
          have hsum : RankSlice.coordSum b < RankSlice.coordSum a := hab.2
          have hbLt : RankSlice.coordSum b < (m + 1) * n := by
            exact lt_of_lt_of_le hsum (RankSlice.coordSum_le_card_mul_ground a)
          exact Nat.sub_lt_sub_left hbLt hsum

/-- The full lower template in the two-layer model: all lower-rank atoms, no upper-rank atoms. -/
def twoLayerFullTemplate (n m : ℕ) : Finset (TwoLayerSlice n m) :=
  (Finset.univ : Finset (RankSlice n m)).map Function.Embedding.inl

theorem isRelLowerSet_twoLayerFullTemplate (n m : ℕ) :
    IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) (twoLayerFullTemplate n m) := by
  intro a b hab hb
  rcases Finset.mem_map.mp hb with ⟨t, ht, rfl⟩
  cases a with
  | inl s =>
      simp [twoLayerFullTemplate]
  | inr u =>
      cases hab

/-- The star template in the two-layer model: both slices consist of atoms containing `0`. -/
def twoLayerStarTemplate (n m : ℕ) : Finset (TwoLayerSlice (n + 1) m) :=
  (RankSlice.containsZeroFamily n m).map Function.Embedding.inl ∪
    (RankSlice.containsZeroFamily n (m + 1)).map Function.Embedding.inr

theorem isRelLowerSet_twoLayerStarTemplate (n m : ℕ) :
    IsRelLowerSet (twoLayerShiftedLT (n := n + 1) (m := m)) (twoLayerStarTemplate n m) := by
  intro a b hab hb
  rw [twoLayerStarTemplate, Finset.mem_union] at hb ⊢
  rcases hb with hb | hb
  · left
    rcases Finset.mem_map.mp hb with ⟨t, ht, rfl⟩
    cases a with
    | inl s =>
        exact Finset.mem_map.mpr ⟨s, RankSlice.isRelLowerSet_containsZeroFamily n m hab ht, rfl⟩
    | inr u =>
        cases hab
  · right
    rcases Finset.mem_map.mp hb with ⟨t, ht, rfl⟩
    cases a with
    | inl s =>
        cases hab
    | inr u =>
        exact Finset.mem_map.mpr
          ⟨u, RankSlice.isRelLowerSet_containsZeroFamily n (m + 1) hab ht, rfl⟩

/-- Fixed-rank subsets of `Fin n` are counted by the binomial coefficient `choose n r`. -/
theorem fintype_card_rankSlice (n r : ℕ) :
    Fintype.card (RankSlice n r) = Nat.choose n r := by
  classical
  let e : RankSlice n r ≃ ((Finset.univ : Finset (Fin n)).powersetCard r) :=
    { toFun := fun s => ⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2⟩⟩
      invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      left_inv := by
        intro s
        rfl
      right_inv := by
        intro s
        cases s
        rfl }
  calc
    Fintype.card (RankSlice n r) = Fintype.card ((Finset.univ : Finset (Fin n)).powersetCard r) := by
      exact Fintype.card_congr e
    _ = Nat.choose n r := by
      simp

theorem card_twoLayerFullTemplate (n m : ℕ) :
    #(twoLayerFullTemplate n m) = Nat.choose n m := by
  classical
  rw [twoLayerFullTemplate, Finset.card_map]
  simpa using fintype_card_rankSlice n m

/-- Repackage a concrete fixed-rank family as a family of `RankSlice` atoms. -/
def rankSliceFamily {n r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ ⦃s : Finset (Fin n)⦄, s ∈ 𝒜 → s.card = r) : Finset (RankSlice n r) :=
  𝒜.attach.map
    ⟨fun s => ⟨s.1, h𝒜 s.2⟩, by
      intro a b hab
      cases a
      cases b
      cases hab
      rfl⟩

theorem card_rankSliceFamily {n r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ ⦃s : Finset (Fin n)⦄, s ∈ 𝒜 → s.card = r) :
    #(rankSliceFamily 𝒜 h𝒜) = #𝒜 := by
  unfold rankSliceFamily
  simpa using Finset.card_map

/-- Two-layer state assembled from concrete lower and upper rank families. -/
def twoLayerStateOfFamilies {n m : ℕ}
    (C : Finset (RankSlice n m)) (U : Finset (RankSlice n (m + 1))) : Finset (TwoLayerSlice n m) :=
  C.map Function.Embedding.inl ∪ U.map Function.Embedding.inr

theorem disjoint_map_inl_map_inr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) :
    Disjoint (A.map Function.Embedding.inl) (B.map Function.Embedding.inr) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨b, hb, hEq⟩
  cases hEq

theorem card_twoLayerStateOfFamilies {n m : ℕ}
    (C : Finset (RankSlice n m)) (U : Finset (RankSlice n (m + 1))) :
    #(twoLayerStateOfFamilies C U) = #C + #U := by
  unfold twoLayerStateOfFamilies
  rw [Finset.card_union_of_disjoint (disjoint_map_inl_map_inr C U)]
  simp

theorem isRelLowerSet_twoLayerStateOfFamilies {n m : ℕ}
    {C : Finset (RankSlice n m)} {U : Finset (RankSlice n (m + 1))}
    (hC : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m)) C)
    (hU : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m + 1)) U) :
    IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) (twoLayerStateOfFamilies C U) := by
  intro a b hab hb
  unfold twoLayerStateOfFamilies at hb ⊢
  rw [Finset.mem_union] at hb ⊢
  rcases hb with hb | hb
  · left
    rcases Finset.mem_map.mp hb with ⟨t, ht, rfl⟩
    cases a with
    | inl s =>
        exact Finset.mem_map.mpr ⟨s, hC hab ht, rfl⟩
    | inr u =>
        cases hab
  · right
    rcases Finset.mem_map.mp hb with ⟨t, ht, rfl⟩
    cases a with
    | inl s =>
        cases hab
    | inr u =>
        exact Finset.mem_map.mpr ⟨u, hU hab ht, rfl⟩

/-- Concrete two-layer state from rank-`m` and rank-`m+1` families. -/
def twoLayerState {n m : ℕ}
    (C : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n)))
    (hC : ∀ ⦃s : Finset (Fin n)⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin n)⦄, s ∈ U → s.card = m + 1) :
    Finset (TwoLayerSlice n m) :=
  twoLayerStateOfFamilies (rankSliceFamily C hC) (rankSliceFamily U hU)

theorem card_twoLayerState {n m : ℕ}
    (C : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n)))
    (hC : ∀ ⦃s : Finset (Fin n)⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin n)⦄, s ∈ U → s.card = m + 1) :
    #(twoLayerState C U hC hU) = #C + #U := by
  unfold twoLayerState
  rw [card_twoLayerStateOfFamilies, card_rankSliceFamily, card_rankSliceFamily]

theorem isRelLowerSet_twoLayerState {n m : ℕ}
    (C : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n)))
    (hC : ∀ ⦃s : Finset (Fin n)⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin n)⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m + 1)) (rankSliceFamily U hU)) :
    IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) (twoLayerState C U hC hU) := by
  unfold twoLayerState
  exact isRelLowerSet_twoLayerStateOfFamilies hCLower hULower

theorem card_twoLayerState_eq_choose_of_balanced {n m : ℕ}
    (C : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n)))
    (hC : ∀ ⦃s : Finset (Fin n)⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin n)⦄, s ∈ U → s.card = m + 1)
    (hCbound : #C ≤ Nat.choose n m)
    (hbal : #U = Nat.choose n m - #C) :
    #(twoLayerState C U hC hU) = Nat.choose n m := by
  rw [card_twoLayerState C U hC hU, hbal]
  exact Nat.add_sub_of_le hCbound

/-- Specialized shifted-instantiation wrapper: once the two-layer states are known to be lower for
the shifted relation and have equal cardinality, the abstract exposed-repair theorem applies. -/
theorem exists_rawExposedRepairPair_preserving_lower_of_twoLayer_eq_card_ne
    {n m : ℕ} {F T : Finset (TwoLayerSlice n m)}
    (hF : IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) F)
    (hT : IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) T)
    (hcard : #F = #T)
    (hne : F ≠ T) :
    ∃ x z,
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n) (m := m)) F T x z ∧
        IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m)) (twoAtomRepair F x z) := by
  exact
    exists_rawExposedRepairPair_preserving_lower_of_lower_eq_card_ne
      hF hT hcard hne
      (twoLayerShiftedLT_wellFounded n m)
      (twoLayerShiftedLT_reverse_wellFounded n m)

/-- Concrete bridge to the full template: a balanced two-layer state with lower-set converted
rank slices inherits a raw exposed repair pair unless it is already the full template. -/
theorem exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_fullTemplate
    {n m : ℕ}
    (C : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n)))
    (hC : ∀ ⦃s : Finset (Fin n)⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin n)⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n) (r := m + 1)) (rankSliceFamily U hU))
    (hCbound : #C ≤ Nat.choose n m)
    (hbal : #U = Nat.choose n m - #C)
    (hne : twoLayerState C U hC hU ≠ twoLayerFullTemplate n m) :
    ∃ x z,
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n) (m := m))
        (twoLayerState C U hC hU) (twoLayerFullTemplate n m) x z ∧
        IsRelLowerSet (twoLayerShiftedLT (n := n) (m := m))
          (twoAtomRepair (twoLayerState C U hC hU) x z) := by
  apply exists_rawExposedRepairPair_preserving_lower_of_twoLayer_eq_card_ne
  · exact isRelLowerSet_twoLayerState C U hC hU hCLower hULower
  · exact isRelLowerSet_twoLayerFullTemplate n m
  · rw [card_twoLayerState_eq_choose_of_balanced C U hC hU hCbound hbal, card_twoLayerFullTemplate]
  · exact hne

end Erdos1
