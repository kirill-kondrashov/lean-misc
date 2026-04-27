import ErdosProblems.Problem1CubeTemplateDistance
import Mathlib.Order.WellFounded

open Finset
open scoped Finset

namespace Erdos1

variable {β : Type} [DecidableEq β]

/-- A finite family is lower for an abstract strict predecessor relation. -/
def IsRelLowerSet (lt : β → β → Prop) (F : Finset β) : Prop :=
  ∀ ⦃a b : β⦄, lt a b → b ∈ F → a ∈ F

/-- A missing template atom can be restored when all of its strict predecessors are present. -/
def IsRestorable (lt : β → β → Prop) (F T : Finset β) (x : β) : Prop :=
  x ∈ T ∧ x ∉ F ∧ ∀ ⦃y : β⦄, lt y x → y ∈ F

/-- An extra atom can be deleted when no strict successor remains present. -/
def IsDeletable (lt : β → β → Prop) (F T : Finset β) (z : β) : Prop :=
  z ∈ F ∧ z ∉ T ∧ ∀ ⦃y : β⦄, lt z y → y ∉ F

/-- Same-rank compatibility: the deleted atom is not needed as a predecessor of the restored one. -/
def CompatibleRepair (lt : β → β → Prop) (x z : β) : Prop :=
  ¬ lt z x

/-- Abstract raw exposed repair pair used by the current template-corner plan. -/
def IsRawExposedRepairPair (lt : β → β → Prop) (F T : Finset β) (x z : β) : Prop :=
  IsRestorable lt F T x ∧ IsDeletable lt F T z ∧ CompatibleRepair lt x z

/-- Minimality inside a finite set for an abstract strict predecessor relation. -/
def IsRelMinimal (lt : β → β → Prop) (S : Finset β) (x : β) : Prop :=
  x ∈ S ∧ ∀ ⦃y : β⦄, y ∈ S → ¬ lt y x

/-- Maximality inside a finite set for an abstract strict predecessor relation. -/
def IsRelMaximal (lt : β → β → Prop) (S : Finset β) (z : β) : Prop :=
  z ∈ S ∧ ∀ ⦃y : β⦄, y ∈ S → ¬ lt z y

theorem isRestorable_of_relMinimal_missing {lt : β → β → Prop} {F T : Finset β}
    {x : β}
    (hT : IsRelLowerSet lt T) (hx : IsRelMinimal lt (T \ F) x) :
    IsRestorable lt F T x := by
  refine ⟨(mem_sdiff.mp hx.1).1, (mem_sdiff.mp hx.1).2, ?_⟩
  intro y hyx
  by_contra hyF
  have hyT : y ∈ T := hT hyx (mem_sdiff.mp hx.1).1
  exact hx.2 (by simp [hyT, hyF]) hyx

theorem isDeletable_of_relMaximal_extra {lt : β → β → Prop} {F T : Finset β} {z : β}
    (hT : IsRelLowerSet lt T) (hz : IsRelMaximal lt (F \ T) z) :
    IsDeletable lt F T z := by
  refine ⟨(mem_sdiff.mp hz.1).1, (mem_sdiff.mp hz.1).2, ?_⟩
  intro y hzy hyF
  by_cases hyT : y ∈ T
  · exact (mem_sdiff.mp hz.1).2 (hT hzy hyT)
  · exact hz.2 (by simp [hyF, hyT]) hzy

omit [DecidableEq β] in
theorem compatibleRepair_of_template_lower_missing_extra {lt : β → β → Prop}
    {T : Finset β} {x z : β}
    (hT : IsRelLowerSet lt T) (hxT : x ∈ T) (hzT : z ∉ T) :
    CompatibleRepair lt x z := by
  intro hzx
  exact hzT (hT hzx hxT)

theorem rawExposedRepairPair_of_relMinimal_missing_relMaximal_extra {lt : β → β → Prop}
    {F T : Finset β} {x z : β}
    (hT : IsRelLowerSet lt T)
    (hx : IsRelMinimal lt (T \ F) x)
    (hz : IsRelMaximal lt (F \ T) z) :
    IsRawExposedRepairPair lt F T x z := by
  have hrest : IsRestorable lt F T x := isRestorable_of_relMinimal_missing hT hx
  have hdel : IsDeletable lt F T z := isDeletable_of_relMaximal_extra hT hz
  exact ⟨hrest, hdel, compatibleRepair_of_template_lower_missing_extra hT hrest.1 hdel.2.1⟩

/--
Abstract lower-set mismatch theorem.

If two finite lower-set states have the same cardinality but are not equal, and the strict
predecessor relation is well-founded in both directions, then there is a compatible raw exposed
repair pair from `F` toward `T`.
-/
theorem exists_rawExposedRepairPair_of_lower_eq_card_ne {lt : β → β → Prop}
    {F T : Finset β}
    (hT : IsRelLowerSet lt T)
    (hcard : #F = #T)
    (hne : F ≠ T)
    (hwfDown : WellFounded lt)
    (hwfUp : WellFounded fun a b => lt b a) :
    ∃ x z, IsRawExposedRepairPair lt F T x z := by
  classical
  have hTnotSubsetF : ¬ T ⊆ F := by
    intro hsub
    have hTF : T = F := eq_of_subset_of_card_le hsub (by rw [hcard])
    exact hne hTF.symm
  have hFnotSubsetT : ¬ F ⊆ T := by
    intro hsub
    have hFT : F = T := eq_of_subset_of_card_le hsub (by rw [← hcard])
    exact hne hFT
  rw [not_subset] at hTnotSubsetF hFnotSubsetT
  rcases hTnotSubsetF with ⟨x₀, hx₀T, hx₀F⟩
  rcases hFnotSubsetT with ⟨z₀, hz₀F, hz₀T⟩
  have hMissNonempty : ((↑(T \ F) : Set β)).Nonempty :=
    ⟨x₀, by simp [hx₀T, hx₀F]⟩
  have hExtraNonempty : ((↑(F \ T) : Set β)).Nonempty :=
    ⟨z₀, by simp [hz₀F, hz₀T]⟩
  rcases hwfDown.has_min ((↑(T \ F) : Set β)) hMissNonempty with
    ⟨x, hxMem, hxMin⟩
  rcases hwfUp.has_min ((↑(F \ T) : Set β)) hExtraNonempty with
    ⟨z, hzMem, hzMax⟩
  refine ⟨x, z, rawExposedRepairPair_of_relMinimal_missing_relMaximal_extra hT ?_ ?_⟩
  · exact ⟨hxMem, fun y hy hyx => hxMin y hy hyx⟩
  · exact ⟨hzMem, fun y hy hzy => hzMax y hy hzy⟩

theorem isRelLowerSet_insert_of_restorable {lt : β → β → Prop} {F T : Finset β} {x : β}
    (hF : IsRelLowerSet lt F) (hx : IsRestorable lt F T x) :
    IsRelLowerSet lt (insert x F) := by
  intro a b hab hb
  rw [mem_insert] at hb
  rcases hb with rfl | hbF
  · exact mem_insert_of_mem (hx.2.2 hab)
  · exact mem_insert_of_mem (hF hab hbF)

theorem isRelLowerSet_erase_of_deletable {lt : β → β → Prop} {F T : Finset β} {z : β}
    (hF : IsRelLowerSet lt F) (hz : IsDeletable lt F T z) :
    IsRelLowerSet lt (F.erase z) := by
  intro a b hab hb
  rw [mem_erase] at hb
  rcases hb with ⟨hbne, hbF⟩
  have haF : a ∈ F := hF hab hbF
  rw [mem_erase]
  refine ⟨?_, haF⟩
  intro haz
  subst a
  exact (hz.2.2 hab) hbF

/--
A raw exposed same-rank repair preserves the lower-set property. This is the abstract Lean form of
the `(REST)+(DEL)+(COMP)` shiftedness argument in the proof note.
-/
theorem isRelLowerSet_twoAtomRepair_of_rawExposed {lt : β → β → Prop}
    {F T : Finset β} {x z : β}
    (hF : IsRelLowerSet lt F) (hraw : IsRawExposedRepairPair lt F T x z) :
    IsRelLowerSet lt (twoAtomRepair F x z) := by
  intro a b hab hb
  have hrest : IsRestorable lt F T x := hraw.1
  have hdel : IsDeletable lt F T z := hraw.2.1
  have hcomp : CompatibleRepair lt x z := hraw.2.2
  rw [twoAtomRepair, mem_insert] at hb
  rcases hb with hbX | hbErase
  · rw [twoAtomRepair, mem_insert]
    by_cases hax : a = x
    · exact Or.inl hax
    · right
      rw [mem_erase]
      have habX : lt a x := by
        simpa [hbX] using hab
      refine ⟨?_, hrest.2.2 habX⟩
      intro haz
      subst a
      exact hcomp habX
  · have hbF : b ∈ F := (mem_erase.mp hbErase).2
    have haF : a ∈ F := hF hab hbF
    rw [twoAtomRepair, mem_insert]
    by_cases hax : a = x
    · exact Or.inl hax
    · right
      rw [mem_erase]
      refine ⟨?_, haF⟩
      intro haz
      subst a
      exact (hdel.2.2 hab) hbF

theorem exists_rawExposedRepairPair_preserving_lower_of_lower_eq_card_ne
    {lt : β → β → Prop} {F T : Finset β}
    (hF : IsRelLowerSet lt F)
    (hT : IsRelLowerSet lt T)
    (hcard : #F = #T)
    (hne : F ≠ T)
    (hwfDown : WellFounded lt)
    (hwfUp : WellFounded fun a b => lt b a) :
    ∃ x z,
      IsRawExposedRepairPair lt F T x z ∧
        IsRelLowerSet lt (twoAtomRepair F x z) := by
  rcases exists_rawExposedRepairPair_of_lower_eq_card_ne hT hcard hne hwfDown hwfUp with
    ⟨x, z, hraw⟩
  exact ⟨x, z, hraw, isRelLowerSet_twoAtomRepair_of_rawExposed hF hraw⟩

/-- A two-atom repair preserves cardinality when it adds a genuinely new atom and deletes one. -/
theorem card_twoAtomRepair_eq_card {F : Finset β} {x z : β}
    (hxF : x ∉ F) (hzF : z ∈ F) :
    #(twoAtomRepair F x z) = #F := by
  have hxErase : x ∉ F.erase z := by
    intro hxErase
    exact hxF ((mem_erase.mp hxErase).2)
  have hzpos : 1 ≤ #F := card_pos.mpr ⟨z, hzF⟩
  calc
    #(twoAtomRepair F x z) = #(F.erase z) + 1 := by
      rw [twoAtomRepair, card_insert_of_notMem hxErase]
    _ = (#F - 1) + 1 := by
      rw [card_erase_of_mem hzF]
    _ = #F := by
      omega

theorem card_twoAtomRepair_eq_card_of_rawExposed {lt : β → β → Prop}
    {F T : Finset β} {x z : β}
    (hraw : IsRawExposedRepairPair lt F T x z) :
    #(twoAtomRepair F x z) = #F :=
  card_twoAtomRepair_eq_card hraw.1.2.1 hraw.2.1.1

theorem templateDistance_twoAtomRepair_eq_sub_two_of_rawExposed {lt : β → β → Prop}
    {F T : Finset β} {x z : β}
    (hraw : IsRawExposedRepairPair lt F T x z) :
    templateDistance (twoAtomRepair F x z) T = templateDistance F T - 2 :=
  templateDistance_twoAtomRepair_eq_sub_two hraw.1.1 hraw.1.2.1 hraw.2.1.1 hraw.2.1.2.1

theorem globalTemplateDistance_twoAtomRepair_eq_sub_two_of_left_nearest_rawExposed
    {lt : β → β → Prop} {F T S : Finset β} {x z : β}
    (hnear : templateDistance F T ≤ templateDistance F S)
    (hraw : IsRawExposedRepairPair lt F T x z) :
    globalTemplateDistance T S (twoAtomRepair F x z) =
      globalTemplateDistance T S F - 2 :=
  globalTemplateDistance_twoAtomRepair_eq_sub_two_of_left_nearest
    hnear hraw.1.1 hraw.1.2.1 hraw.2.1.1 hraw.2.1.2.1

theorem globalTemplateDistance_twoAtomRepair_eq_sub_two_of_right_nearest_rawExposed
    {lt : β → β → Prop} {F T S : Finset β} {x z : β}
    (hnear : templateDistance F S ≤ templateDistance F T)
    (hraw : IsRawExposedRepairPair lt F S x z) :
    globalTemplateDistance T S (twoAtomRepair F x z) =
      globalTemplateDistance T S F - 2 :=
  globalTemplateDistance_twoAtomRepair_eq_sub_two_of_right_nearest
    hnear hraw.1.1 hraw.1.2.1 hraw.2.1.1 hraw.2.1.2.1

end Erdos1
