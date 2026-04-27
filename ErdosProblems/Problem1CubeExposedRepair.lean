import ErdosProblems.Problem1CubeTemplateDistance

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
