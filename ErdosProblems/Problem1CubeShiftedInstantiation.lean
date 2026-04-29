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

@[simp]
theorem preimage_map_succEmb (s : Finset (Fin n)) :
    (s.map (Fin.succEmb n)).preimage Fin.succ (Fin.succ_injective n).injOn = s := by
  ext x
  simp

theorem map_preimage_succ_eq_of_zero_not_mem {s : Finset (Fin (n + 1))}
    (h0 : (0 : Fin (n + 1)) ∉ s) :
    (s.preimage Fin.succ (Fin.succ_injective n).injOn).map (Fin.succEmb n) = s := by
  ext x
  by_cases hx0 : x = 0
  · subst x
    simp [h0]
  · rcases Fin.exists_succ_eq_of_ne_zero hx0 with ⟨y, rfl⟩
    simp

theorem card_preimage_succ {s : Finset (Fin (n + 1))}
    (h0 : (0 : Fin (n + 1)) ∉ s) :
    #(s.preimage Fin.succ (Fin.succ_injective n).injOn) = #s := by
  rw [Finset.card_preimage]
  have hfilter : {x ∈ s | x ∈ Set.range Fin.succ} = s := by
    apply Finset.filter_true_of_mem
    intro x hx
    rcases Fin.exists_succ_eq_of_ne_zero (by
      intro hx0
      exact h0 (hx0 ▸ hx)) with ⟨y, hy⟩
    exact hy ▸ Set.mem_range_self y
  rw [hfilter]

def addZero (s : RankSlice n r) : RankSlice (n + 1) (r + 1) :=
  ⟨insert 0 (s.1.map (Fin.succEmb n)), by simp [s.2]⟩

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

noncomputable def removeZero
    (s : { t : RankSlice (n + 1) (r + 1) // t ∈ containsZeroFamily n (r + 1) }) :
    RankSlice n r := by
  refine ⟨(s.1.1.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn, ?_⟩
  have hzero : (0 : Fin (n + 1)) ∈ s.1.1 := (Finset.mem_filter.mp s.2).2
  have hzeroErase : (0 : Fin (n + 1)) ∉ s.1.1.erase 0 := by simp
  simpa using
    (show #((s.1.1.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn) = (r + 1) - 1 by
      rw [card_preimage_succ hzeroErase, Finset.card_erase_of_mem hzero, s.1.2])

theorem leftInverse_removeZero_addZero (s : RankSlice n r) :
    removeZero ⟨addZero s, by
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      simp [addZero]⟩ = s := by
  apply Subtype.ext
  simp [removeZero, addZero, preimage_map_succEmb]

theorem rightInverse_addZero_removeZero
    (s : { t : RankSlice (n + 1) (r + 1) // t ∈ containsZeroFamily n (r + 1) }) :
    addZero (removeZero s) = s.1 := by
  apply Subtype.ext
  have hzero : (0 : Fin (n + 1)) ∈ s.1.1 := (Finset.mem_filter.mp s.2).2
  have hzeroErase : (0 : Fin (n + 1)) ∉ s.1.1.erase 0 := by simp
  calc
    (addZero (removeZero s)).1
        = insert 0 (((s.1.1.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn).map
            (Fin.succEmb n)) := by
              simp [addZero, removeZero]
    _ = insert 0 (s.1.1.erase 0) := by
          rw [map_preimage_succ_eq_of_zero_not_mem hzeroErase]
    _ = s.1.1 := Finset.insert_erase hzero

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

namespace RankSlice

theorem card_containsZeroFamily_zero (n : ℕ) :
    #(containsZeroFamily n 0) = 0 := by
  refine Finset.card_eq_zero.mpr ?_
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨-, hzero⟩
    have hsEmpty : s.1 = ∅ := Finset.card_eq_zero.mp s.2
    simpa [hsEmpty] using hzero
  · simp

theorem card_containsZeroFamily_succ (n r : ℕ) :
    #(containsZeroFamily n (r + 1)) = Nat.choose n r := by
  classical
  let e : RankSlice n r ≃ { t : RankSlice (n + 1) (r + 1) // t ∈ containsZeroFamily n (r + 1) } :=
    { toFun := fun s =>
        ⟨addZero s, by
          refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
          simp [addZero]⟩
      invFun := removeZero
      left_inv := leftInverse_removeZero_addZero
      right_inv := by
        intro s
        apply Subtype.ext
        exact rightInverse_addZero_removeZero s }
  calc
    #(containsZeroFamily n (r + 1))
        = Fintype.card { t : RankSlice (n + 1) (r + 1) // t ∈ containsZeroFamily n (r + 1) } := by
            simp
    _ = Fintype.card (RankSlice n r) := by
            exact Fintype.card_congr e.symm
    _ = Nat.choose n r := fintype_card_rankSlice n r

theorem card_containsZeroFamily_of_pos (n m : ℕ) (hm : 0 < m) :
    #(containsZeroFamily n m) = Nat.choose n (m - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simpa using card_containsZeroFamily_succ n r

end RankSlice

theorem card_twoLayerFullTemplate (n m : ℕ) :
    #(twoLayerFullTemplate n m) = Nat.choose n m := by
  classical
  rw [twoLayerFullTemplate, Finset.card_map]
  simpa using fintype_card_rankSlice n m

theorem card_twoLayerStarTemplate (n m : ℕ) :
    #(twoLayerStarTemplate n m) = Nat.choose (n + 1) m := by
  rw [twoLayerStarTemplate, Finset.card_union_of_disjoint
    (disjoint_map_inl_map_inr _ _), Finset.card_map, Finset.card_map]
  by_cases hm : m = 0
  · subst hm
    simp [RankSlice.card_containsZeroFamily_zero, RankSlice.card_containsZeroFamily_succ]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    rw [RankSlice.card_containsZeroFamily_of_pos n m hmpos, RankSlice.card_containsZeroFamily_succ]
    simpa [Nat.choose_succ_left n m hmpos]

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

/-- Concrete bridge to the star template. -/
theorem exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_starTemplate
    {n m : ℕ}
    (C : Finset (Finset (Fin (n + 1)))) (U : Finset (Finset (Fin (n + 1))))
    (hC : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m + 1)) (rankSliceFamily U hU))
    (hCbound : #C ≤ Nat.choose (n + 1) m)
    (hbal : #U = Nat.choose (n + 1) m - #C)
    (hne : twoLayerState C U hC hU ≠ twoLayerStarTemplate n m) :
    ∃ x z,
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n + 1) (m := m))
        (twoLayerState C U hC hU) (twoLayerStarTemplate n m) x z ∧
        IsRelLowerSet (twoLayerShiftedLT (n := n + 1) (m := m))
          (twoAtomRepair (twoLayerState C U hC hU) x z) := by
  apply exists_rawExposedRepairPair_preserving_lower_of_twoLayer_eq_card_ne
  · exact isRelLowerSet_twoLayerState C U hC hU hCLower hULower
  · exact isRelLowerSet_twoLayerStarTemplate n m
  · rw [card_twoLayerState_eq_choose_of_balanced C U hC hU hCbound hbal, card_twoLayerStarTemplate]
  · exact hne

/-- Deterministic nearest-template selector for the two-layer shifted model. Ties go to the full
template, matching the proof-note convention for `T(F)`. -/
def selectedTwoLayerTemplate (n m : ℕ) (F : Finset (TwoLayerSlice (n + 1) m)) :
    Finset (TwoLayerSlice (n + 1) m) :=
  if templateDistance F (twoLayerFullTemplate (n + 1) m) ≤
      templateDistance F (twoLayerStarTemplate n m) then
    twoLayerFullTemplate (n + 1) m
  else
    twoLayerStarTemplate n m

theorem selectedTwoLayerTemplate_eq_full_of_le {n m : ℕ} {F : Finset (TwoLayerSlice (n + 1) m)}
    (hnear : templateDistance F (twoLayerFullTemplate (n + 1) m) ≤
      templateDistance F (twoLayerStarTemplate n m)) :
    selectedTwoLayerTemplate n m F = twoLayerFullTemplate (n + 1) m := by
  simp [selectedTwoLayerTemplate, hnear]

theorem selectedTwoLayerTemplate_eq_star_of_lt {n m : ℕ} {F : Finset (TwoLayerSlice (n + 1) m)}
    (hnear : templateDistance F (twoLayerStarTemplate n m) <
      templateDistance F (twoLayerFullTemplate (n + 1) m)) :
    selectedTwoLayerTemplate n m F = twoLayerStarTemplate n m := by
  have hnot : ¬templateDistance F (twoLayerFullTemplate (n + 1) m) ≤
      templateDistance F (twoLayerStarTemplate n m) := by
    exact not_le.mpr hnear
  simp [selectedTwoLayerTemplate, hnot]

/-- Concrete bridge to the selected nearest template `T(F)`. -/
theorem exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_selectedTemplate
    {n m : ℕ}
    (C : Finset (Finset (Fin (n + 1)))) (U : Finset (Finset (Fin (n + 1))))
    (hC : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m + 1)) (rankSliceFamily U hU))
    (hCbound : #C ≤ Nat.choose (n + 1) m)
    (hbal : #U = Nat.choose (n + 1) m - #C)
    (hne : twoLayerState C U hC hU ≠ selectedTwoLayerTemplate n m (twoLayerState C U hC hU)) :
    ∃ x z,
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n + 1) (m := m))
        (twoLayerState C U hC hU)
        (selectedTwoLayerTemplate n m (twoLayerState C U hC hU)) x z ∧
        IsRelLowerSet (twoLayerShiftedLT (n := n + 1) (m := m))
          (twoAtomRepair (twoLayerState C U hC hU) x z) := by
  by_cases hnear : templateDistance (twoLayerState C U hC hU) (twoLayerFullTemplate (n + 1) m) ≤
      templateDistance (twoLayerState C U hC hU) (twoLayerStarTemplate n m)
  · simpa [selectedTwoLayerTemplate, hnear] using
      exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_fullTemplate
        (n := n + 1) (m := m) C U hC hU hCLower hULower hCbound hbal
        (by simpa [selectedTwoLayerTemplate, hnear] using hne)
  · have hstarNear : templateDistance (twoLayerState C U hC hU) (twoLayerStarTemplate n m) <
        templateDistance (twoLayerState C U hC hU) (twoLayerFullTemplate (n + 1) m) := by
        exact lt_of_not_ge hnear
    simpa [selectedTwoLayerTemplate, hnear] using
      exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_starTemplate
        (n := n) (m := m) C U hC hU hCLower hULower hCbound hbal
        (by simpa [selectedTwoLayerTemplate, hnear] using hne)

/-- Balanced shifted states that are neither extremal template differ from their selected nearest
template, so they admit a concrete exposed repair pair. -/
theorem exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_nonTemplate
    {n m : ℕ}
    (C : Finset (Finset (Fin (n + 1)))) (U : Finset (Finset (Fin (n + 1))))
    (hC : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m + 1)) (rankSliceFamily U hU))
    (hCbound : #C ≤ Nat.choose (n + 1) m)
    (hbal : #U = Nat.choose (n + 1) m - #C)
    (hneFull : twoLayerState C U hC hU ≠ twoLayerFullTemplate (n + 1) m)
    (hneStar : twoLayerState C U hC hU ≠ twoLayerStarTemplate n m) :
    ∃ x z,
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n + 1) (m := m))
        (twoLayerState C U hC hU)
        (selectedTwoLayerTemplate n m (twoLayerState C U hC hU)) x z ∧
        IsRelLowerSet (twoLayerShiftedLT (n := n + 1) (m := m))
          (twoAtomRepair (twoLayerState C U hC hU) x z) := by
  apply exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_ne_selectedTemplate
    (n := n) (m := m) C U hC hU hCLower hULower hCbound hbal
  by_cases hnear : templateDistance (twoLayerState C U hC hU) (twoLayerFullTemplate (n + 1) m) ≤
      templateDistance (twoLayerState C U hC hU) (twoLayerStarTemplate n m)
  · simpa [selectedTwoLayerTemplate, hnear] using hneFull
  · simpa [selectedTwoLayerTemplate, hnear] using hneStar

end Erdos1
