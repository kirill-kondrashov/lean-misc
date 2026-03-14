import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Shadow

open Finset
open scoped FinsetFamily

namespace Erdos1

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
The positive vertex boundary of a family in the full Boolean cube: these are the sets outside the
family that reach the family after deleting one element.
-/
def positiveBoundary (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (Finset.univ.powerset).filter fun s => s ∉ 𝒜 ∧ ∃ a ∈ s, s.erase a ∈ 𝒜

@[simp]
theorem mem_positiveBoundary {𝒜 : Finset (Finset α)} {s : Finset α} :
    s ∈ positiveBoundary 𝒜 ↔ s ∉ 𝒜 ∧ ∃ a ∈ s, s.erase a ∈ 𝒜 := by
  simp [positiveBoundary]

/--
The positive boundary is exactly the part of the upper shadow lying outside the family.
-/
theorem positiveBoundary_eq_upShadow_sdiff (𝒜 : Finset (Finset α)) :
    positiveBoundary 𝒜 = ∂⁺ 𝒜 \ 𝒜 := by
  ext s
  rw [mem_positiveBoundary, mem_sdiff, Finset.mem_upShadow_iff_erase_mem]
  constructor
  · rintro ⟨hsA, a, has, hErase⟩
    exact ⟨⟨a, has, hErase⟩, hsA⟩
  · rintro ⟨⟨a, has, hErase⟩, hsA⟩
    exact ⟨hsA, a, has, hErase⟩

@[simp]
theorem mem_positiveBoundary_iff_mem_upShadow_and_not_mem {𝒜 : Finset (Finset α)} {s : Finset α} :
    s ∈ positiveBoundary 𝒜 ↔ s ∈ ∂⁺ 𝒜 ∧ s ∉ 𝒜 := by
  rw [positiveBoundary_eq_upShadow_sdiff, mem_sdiff]

/--
If a boundary set avoids `a`, then its boundary membership only depends on the `a`-free section of
the family.
-/
theorem mem_nonMemberSubfamily_positiveBoundary_iff {a : α} {𝒜 : Finset (Finset α)}
    {s : Finset α} (ha : a ∉ s) :
    s ∈ (positiveBoundary 𝒜).nonMemberSubfamily a ↔
      s ∈ positiveBoundary (𝒜.nonMemberSubfamily a) := by
  rw [mem_nonMemberSubfamily, mem_positiveBoundary, mem_positiveBoundary]
  constructor
  · rintro ⟨⟨hsNotA, b, hb, hsErase⟩, -⟩
    refine ⟨?_, b, hb, ?_⟩
    · intro hsSection
      exact hsNotA (mem_nonMemberSubfamily.mp hsSection).1
    · exact mem_nonMemberSubfamily.mpr ⟨hsErase, fun hmem => ha (Finset.mem_of_mem_erase hmem)⟩
  · intro hs
    rcases hs with ⟨hsNotSection, b, hb, hsErase⟩
    refine ⟨?_, ha⟩
    refine ⟨?_, b, hb, (mem_nonMemberSubfamily.mp hsErase).1⟩
    intro hsA
    exact hsNotSection (mem_nonMemberSubfamily.mpr ⟨hsA, ha⟩)

/-- The `a`-free part of the positive boundary is exactly the positive boundary of the `a`-free
section, restricted back to the `a`-free subcube. -/
theorem nonMemberSubfamily_positiveBoundary (a : α) (𝒜 : Finset (Finset α)) :
    (positiveBoundary 𝒜).nonMemberSubfamily a =
      (positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a := by
  ext s
  by_cases ha : a ∈ s
  · simp [mem_nonMemberSubfamily, ha]
  · simpa [mem_nonMemberSubfamily, ha] using
      (mem_nonMemberSubfamily_positiveBoundary_iff (𝒜 := 𝒜) (s := s) ha)

/-- Every set that lies in the `a`-free section but whose `a`-lift leaves the family contributes an
`a`-section boundary point. -/
theorem sdiff_subfamily_subset_memberSubfamily_positiveBoundary {a : α}
    (𝒜 : Finset (Finset α)) :
    𝒜.nonMemberSubfamily a \ 𝒜.memberSubfamily a ⊆ (positiveBoundary 𝒜).memberSubfamily a := by
  intro s hs
  rcases mem_sdiff.mp hs with ⟨hsNon, hsNotMem⟩
  rcases mem_nonMemberSubfamily.mp hsNon with ⟨hsA, ha⟩
  refine mem_memberSubfamily.mpr ⟨?_, ha⟩
  rw [mem_positiveBoundary]
  refine ⟨?_, a, mem_insert_self a s, ?_⟩
  · intro hsInsert
    exact hsNotMem (mem_memberSubfamily.mpr ⟨hsInsert, ha⟩)
  · simpa [ha] using hsA

theorem card_sdiff_subfamily_le_memberSubfamily_positiveBoundary {a : α}
    (𝒜 : Finset (Finset α)) :
    #(𝒜.nonMemberSubfamily a \ 𝒜.memberSubfamily a) ≤
      #((positiveBoundary 𝒜).memberSubfamily a) := by
  exact Finset.card_le_card (sdiff_subfamily_subset_memberSubfamily_positiveBoundary 𝒜)

/-- The `a`-section of the positive boundary splits into the gap between the two `a`-sections of
the family, together with the `a`-free part of the boundary of the member section. -/
theorem memberSubfamily_positiveBoundary (a : α) (𝒜 : Finset (Finset α)) :
    (positiveBoundary 𝒜).memberSubfamily a =
      (𝒜.nonMemberSubfamily a \ 𝒜.memberSubfamily a) ∪
        (positiveBoundary (𝒜.memberSubfamily a)).nonMemberSubfamily a := by
  ext s
  rw [mem_memberSubfamily, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hPb, ha⟩
    rcases mem_positiveBoundary.mp hPb with ⟨hsNotInsert, b, hb, hbErase⟩
    by_cases hba : b = a
    · left
      have hsA : s ∈ 𝒜 := by
        simpa [hba, ha] using hbErase
      refine ⟨mem_nonMemberSubfamily.mpr ⟨hsA, ha⟩, ?_⟩
      · intro hsMember
        exact hsNotInsert (mem_memberSubfamily.mp hsMember).1
    · right
      have hsNotMember : s ∉ 𝒜.memberSubfamily a := by
        intro hsMember
        exact hsNotInsert (mem_memberSubfamily.mp hsMember).1
      have hb' : b ∈ s := by
        simpa [hba, ha] using hb
      have hsEraseMember : s.erase b ∈ 𝒜.memberSubfamily a := by
        refine mem_memberSubfamily.mpr ⟨?_, ?_⟩
        · simpa [Finset.erase_insert_of_ne (Ne.symm hba)] using hbErase
        · exact fun hmem => ha (Finset.mem_of_mem_erase hmem)
      exact mem_nonMemberSubfamily.mpr
        ⟨mem_positiveBoundary.mpr ⟨hsNotMember, b, hb', hsEraseMember⟩, ha⟩
  · rintro (hs | hs)
    · rcases hs with ⟨hsNon, hsNotMember⟩
      rcases mem_nonMemberSubfamily.mp hsNon with ⟨hsA, ha⟩
      refine ⟨mem_positiveBoundary.mpr ?_, ha⟩
      refine ⟨?_, a, mem_insert_self a s, ?_⟩
      · intro hsInsert
        exact hsNotMember (mem_memberSubfamily.mpr ⟨hsInsert, ha⟩)
      · simpa [ha] using hsA
    · rcases mem_nonMemberSubfamily.mp hs with ⟨hsPos, ha⟩
      rcases mem_positiveBoundary.mp hsPos with ⟨hsNotMember, b, hb, hsErase⟩
      refine ⟨mem_positiveBoundary.mpr ?_, ha⟩
      refine ⟨?_, b, ?_, ?_⟩
      · intro hsInsert
        exact hsNotMember (mem_memberSubfamily.mpr ⟨hsInsert, ha⟩)
      · exact Finset.mem_insert_of_mem hb
      · have hba : a ≠ b := by
          intro hab
          subst hab
          exact ha hb
        simpa [Finset.erase_insert_of_ne hba] using (mem_memberSubfamily.mp hsErase).1

theorem card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_card_sdiff
    (a : α) (𝒜 : Finset (Finset α)) :
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        #(𝒜.nonMemberSubfamily a \ 𝒜.memberSubfamily a) ≤
      #(positiveBoundary 𝒜) := by
  calc
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        #(𝒜.nonMemberSubfamily a \ 𝒜.memberSubfamily a)
      ≤ #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
          #((positiveBoundary 𝒜).memberSubfamily a) := by
            exact Nat.add_le_add_left
              (card_sdiff_subfamily_le_memberSubfamily_positiveBoundary 𝒜) _
    _ = #((positiveBoundary 𝒜).memberSubfamily a) +
          #((positiveBoundary 𝒜).nonMemberSubfamily a) := by
            rw [add_comm, ← nonMemberSubfamily_positiveBoundary (a := a) (𝒜 := 𝒜)]
    _ = #(positiveBoundary 𝒜) :=
      Finset.card_memberSubfamily_add_card_nonMemberSubfamily _ _

theorem card_positiveBoundary_ge_two_nonMemberSubfamily_sections
    (a : α) (𝒜 : Finset (Finset α)) :
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        #((positiveBoundary (𝒜.memberSubfamily a)).nonMemberSubfamily a) ≤
      #(positiveBoundary 𝒜) := by
  calc
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        #((positiveBoundary (𝒜.memberSubfamily a)).nonMemberSubfamily a)
      ≤ #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
          #((positiveBoundary 𝒜).memberSubfamily a) := by
            refine Nat.add_le_add_left ?_ _
            rw [memberSubfamily_positiveBoundary]
            exact Finset.card_le_card (by
              intro s hs
              exact Finset.mem_union.mpr (Or.inr hs))
    _ = #((positiveBoundary 𝒜).memberSubfamily a) +
          #((positiveBoundary 𝒜).nonMemberSubfamily a) := by
            rw [add_comm, ← nonMemberSubfamily_positiveBoundary (a := a) (𝒜 := 𝒜)]
    _ = #(positiveBoundary 𝒜) :=
      Finset.card_memberSubfamily_add_card_nonMemberSubfamily _ _

end Erdos1
