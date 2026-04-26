import Mathlib.Data.Finset.Card

open Finset
open scoped Finset

namespace Erdos1

variable {β : Type} [DecidableEq β]

/-- Symmetric-difference distance from a family/state `F` to a fixed template `T`. -/
def templateDistance (F T : Finset β) : ℕ :=
  #(F \ T) + #(T \ F)

/-- Distance to the nearer of two templates. -/
def globalTemplateDistance (T₀ T₁ F : Finset β) : ℕ :=
  min (templateDistance F T₀) (templateDistance F T₁)

/-- The abstract two-atom repair used by the exposed-corner plan: add `x`, delete `z`. -/
def twoAtomRepair (F : Finset β) (x z : β) : Finset β :=
  insert x (F.erase z)

theorem globalTemplateDistance_eq_left_of_le {F T₀ T₁ : Finset β}
    (h : templateDistance F T₀ ≤ templateDistance F T₁) :
    globalTemplateDistance T₀ T₁ F = templateDistance F T₀ := by
  simp [globalTemplateDistance, min_eq_left h]

theorem globalTemplateDistance_eq_right_of_le {F T₀ T₁ : Finset β}
    (h : templateDistance F T₁ ≤ templateDistance F T₀) :
    globalTemplateDistance T₀ T₁ F = templateDistance F T₁ := by
  simp [globalTemplateDistance, min_eq_right h]

theorem globalTemplateDistance_comm (T₀ T₁ F : Finset β) :
    globalTemplateDistance T₀ T₁ F = globalTemplateDistance T₁ T₀ F := by
  simp [globalTemplateDistance, min_comm]

/--
Adding a missing template atom and deleting an extra non-template atom drops the distance to that
fixed template by exactly two.
-/
theorem templateDistance_twoAtomRepair_eq_sub_two {F T : Finset β} {x z : β}
    (hxT : x ∈ T) (hxF : x ∉ F) (hzF : z ∈ F) (hzT : z ∉ T) :
    templateDistance (twoAtomRepair F x z) T = templateDistance F T - 2 := by
  have hxz : x ≠ z := by
    intro h
    exact hzT (h ▸ hxT)
  have hleft : twoAtomRepair F x z \ T = (F \ T).erase z := by
    ext y
    by_cases hyx : y = x
    · subst y
      simp [twoAtomRepair, hxT, hxz]
    · by_cases hyz : y = z
      · subst y
        simp [twoAtomRepair, hzT, hxz.symm]
      · simp [twoAtomRepair, hyx, hyz]
  have hright : T \ twoAtomRepair F x z = (T \ F).erase x := by
    ext y
    by_cases hyx : y = x
    · subst y
      simp [twoAtomRepair]
    · by_cases hyz : y = z
      · subst y
        simp [twoAtomRepair, hzT, hxz.symm]
      · simp [twoAtomRepair, hyx, hyz]
  have hzLeft : z ∈ F \ T := by
    simp [hzF, hzT]
  have hxRight : x ∈ T \ F := by
    simp [hxT, hxF]
  calc
    templateDistance (twoAtomRepair F x z) T
        = #((F \ T).erase z) + #((T \ F).erase x) := by
            simp [templateDistance, hleft, hright]
    _ = (#(F \ T) - 1) + (#(T \ F) - 1) := by
            rw [card_erase_of_mem hzLeft, card_erase_of_mem hxRight]
    _ = #(F \ T) + #(T \ F) - 2 := by
            have hzpos : 1 ≤ #(F \ T) := card_pos.mpr ⟨z, hzLeft⟩
            have hxpos : 1 ≤ #(T \ F) := card_pos.mpr ⟨x, hxRight⟩
            omega
    _ = templateDistance F T - 2 := by
            rfl

/-- A two-atom repair changes distance to any fixed template by at most two. -/
theorem templateDistance_le_twoAtomRepair_add_two (F T : Finset β) (x z : β) :
    templateDistance F T ≤ templateDistance (twoAtomRepair F x z) T + 2 := by
  have hleft_subset : F \ T ⊆ (twoAtomRepair F x z \ T) ∪ {z} := by
    intro y hy
    have hyF : y ∈ F := (mem_sdiff.mp hy).1
    have hyT : y ∉ T := (mem_sdiff.mp hy).2
    by_cases hyz : y = z
    · subst y
      simp
    · have hyRepair : y ∈ twoAtomRepair F x z := by
        simp [twoAtomRepair, hyF, hyz]
      simp [hyRepair, hyT]
  have hright_subset : T \ F ⊆ (T \ twoAtomRepair F x z) ∪ {x} := by
    intro y hy
    have hyT : y ∈ T := (mem_sdiff.mp hy).1
    have hyF : y ∉ F := (mem_sdiff.mp hy).2
    by_cases hyx : y = x
    · subst y
      simp
    · have hyRepair : y ∉ twoAtomRepair F x z := by
        simp [twoAtomRepair, hyx, hyF]
      simp [hyT, hyRepair]
  have hleft_card :
      #(F \ T) ≤ #(twoAtomRepair F x z \ T) + 1 := by
    calc
      #(F \ T) ≤ #((twoAtomRepair F x z \ T) ∪ {z}) :=
        card_le_card hleft_subset
      _ ≤ #(twoAtomRepair F x z \ T) + #({z} : Finset β) :=
        card_union_le _ _
      _ = #(twoAtomRepair F x z \ T) + 1 := by simp
  have hright_card :
      #(T \ F) ≤ #(T \ twoAtomRepair F x z) + 1 := by
    calc
      #(T \ F) ≤ #((T \ twoAtomRepair F x z) ∪ {x}) :=
        card_le_card hright_subset
      _ ≤ #(T \ twoAtomRepair F x z) + #({x} : Finset β) :=
        card_union_le _ _
      _ = #(T \ twoAtomRepair F x z) + 1 := by simp
  simp [templateDistance]
  omega

/--
If a two-atom move drops distance to the selected nearest template by two and changes distance to
the other template by at most two, then the global two-template distance drops by two.
-/
theorem globalTemplateDistance_eq_sub_two_of_drop_and_lipschitz
    {F F' T S : Finset β}
    (hnear : templateDistance F T ≤ templateDistance F S)
    (hdrop : templateDistance F' T = templateDistance F T - 2)
    (hlip : templateDistance F S ≤ templateDistance F' S + 2) :
    globalTemplateDistance T S F' = globalTemplateDistance T S F - 2 := by
  have hglobalF : globalTemplateDistance T S F = templateDistance F T :=
    globalTemplateDistance_eq_left_of_le hnear
  have hSLower : templateDistance F T - 2 ≤ templateDistance F' S := by
    omega
  have hTLower : templateDistance F T - 2 ≤ templateDistance F' T := by
    omega
  have hLower :
      templateDistance F T - 2 ≤
        min (templateDistance F' T) (templateDistance F' S) := by
    exact le_min hTLower hSLower
  have hUpper :
      min (templateDistance F' T) (templateDistance F' S) ≤ templateDistance F T - 2 := by
    exact (min_le_left _ _).trans_eq hdrop
  have hmin :
      min (templateDistance F' T) (templateDistance F' S) = templateDistance F T - 2 :=
    le_antisymm hUpper hLower
  calc
    globalTemplateDistance T S F'
        = min (templateDistance F' T) (templateDistance F' S) := rfl
    _ = templateDistance F T - 2 := hmin
    _ = globalTemplateDistance T S F - 2 := by rw [hglobalF]

/--
If a repair is made toward the left nearest template, then the global two-template distance drops
by exactly two.
-/
theorem globalTemplateDistance_twoAtomRepair_eq_sub_two_of_left_nearest
    {F T S : Finset β} {x z : β}
    (hnear : templateDistance F T ≤ templateDistance F S)
    (hxT : x ∈ T) (hxF : x ∉ F) (hzF : z ∈ F) (hzT : z ∉ T) :
    globalTemplateDistance T S (twoAtomRepair F x z) =
      globalTemplateDistance T S F - 2 :=
  globalTemplateDistance_eq_sub_two_of_drop_and_lipschitz
    hnear
    (templateDistance_twoAtomRepair_eq_sub_two hxT hxF hzF hzT)
    (templateDistance_le_twoAtomRepair_add_two F S x z)

/--
If a repair is made toward the right nearest template, then the global two-template distance drops
by exactly two.
-/
theorem globalTemplateDistance_twoAtomRepair_eq_sub_two_of_right_nearest
    {F T S : Finset β} {x z : β}
    (hnear : templateDistance F S ≤ templateDistance F T)
    (hxS : x ∈ S) (hxF : x ∉ F) (hzF : z ∈ F) (hzS : z ∉ S) :
    globalTemplateDistance T S (twoAtomRepair F x z) =
      globalTemplateDistance T S F - 2 := by
  calc
    globalTemplateDistance T S (twoAtomRepair F x z)
        = globalTemplateDistance S T (twoAtomRepair F x z) := by
            rw [globalTemplateDistance_comm]
    _ = globalTemplateDistance S T F - 2 :=
        globalTemplateDistance_twoAtomRepair_eq_sub_two_of_left_nearest
          hnear hxS hxF hzF hzS
    _ = globalTemplateDistance T S F - 2 := by
        rw [globalTemplateDistance_comm]

end Erdos1
