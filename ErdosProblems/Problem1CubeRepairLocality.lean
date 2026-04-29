import ErdosProblems.Problem1CubeBoundary
import ErdosProblems.Problem1CubeExposedRepair
import Mathlib.Tactic

open Finset
open scoped Finset

namespace Erdos1

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {F : Finset (Finset α)} {x z s : Finset α}

abbrev familyRepair (F : Finset (Finset α)) (x z : Finset α) : Finset (Finset α) :=
  insert x (F.erase z)

theorem mem_sdiff_of_twoAtomRepair
    (hs : s ∈ (familyRepair F x z \ F)) :
    s = x := by
  rw [mem_sdiff, familyRepair, mem_insert] at hs
  rcases hs with ⟨hsRepair, hsF⟩
  rcases hsRepair with rfl | hsErase
  exact rfl
  exact False.elim (hsF (mem_erase.mp hsErase).2)

theorem mem_sdiff_twoAtomRepair
    (hs : s ∈ (F \ familyRepair F x z)) :
    s = z := by
  rw [mem_sdiff, familyRepair, mem_insert] at hs
  rcases hs with ⟨hsF, hsRepair⟩
  have hsNeX : s ≠ x := by
    intro hsx
    exact hsRepair (Or.inl hsx)
  by_cases hsz : s = z
  · exact hsz
  · exact False.elim (hsRepair (Or.inr (mem_erase.mpr ⟨hsz, hsF⟩)))

/-- A new positive-boundary atom created by a two-atom repair is either the deleted atom itself or a
one-step cover of the inserted atom. -/
theorem mem_sdiff_positiveBoundary_twoAtomRepair_local
    (hs : s ∈ (positiveBoundary (familyRepair F x z) \ positiveBoundary F)) :
    s = z ∨ ∃ a ∈ s, s.erase a = x := by
  rcases mem_sdiff.mp hs with ⟨hsNew, hsOld⟩
  rcases mem_positiveBoundary.mp hsNew with ⟨hsNotRepair, a, ha, hEraseRepair⟩
  rw [familyRepair, mem_insert, mem_erase] at hEraseRepair hsNotRepair
  rcases hEraseRepair with hEraseX | hEraseOld
  · exact Or.inr ⟨a, ha, hEraseX⟩
  · rcases hEraseOld with ⟨-, hEraseF⟩
    have hsNeX : s ≠ x := by
      intro hsx
      exact hsNotRepair (Or.inl hsx)
    by_cases hsz : s = z
    · exact Or.inl hsz
    · have hsNotF : s ∉ F := by
        simpa [familyRepair, hsNeX, hsz] using hsNotRepair
      exact False.elim (hsOld (mem_positiveBoundary.mpr ⟨hsNotF, a, ha, hEraseF⟩))

/-- A positive-boundary atom lost under a two-atom repair is either the inserted atom itself or a
one-step cover of the deleted atom. -/
theorem mem_sdiff_positiveBoundary_of_twoAtomRepair_local
    (hs : s ∈ (positiveBoundary F \ positiveBoundary (familyRepair F x z))) :
    s = x ∨ ∃ a ∈ s, s.erase a = z := by
  rcases mem_sdiff.mp hs with ⟨hsOld, hsNew⟩
  rcases mem_positiveBoundary.mp hsOld with ⟨hsNotF, a, ha, hEraseF⟩
  by_cases hEraseZ : s.erase a = z
  · exact Or.inr ⟨a, ha, hEraseZ⟩
  · by_cases hsx : s = x
    · exact Or.inl hsx
    · have hsNotRepair : s ∉ familyRepair F x z := by
        simpa [familyRepair, hsx, hsNotF] using hsNew
      have hEraseRepair : s.erase a ∈ familyRepair F x z := by
        simp [familyRepair, hEraseF, hEraseZ]
      have hsRepair : s ∈ positiveBoundary (familyRepair F x z) := by
        refine mem_positiveBoundary.mpr ⟨?_, a, ha, hEraseRepair⟩
        exact hsNotRepair
      exact False.elim (hsNew hsRepair)

theorem sdiff_positiveBoundary_twoAtomRepair_subset_local :
    positiveBoundary (familyRepair F x z) \ positiveBoundary F ⊆
      positiveBoundary ({x} : Finset (Finset α)) ∪ (({z} : Finset (Finset α))) := by
  intro s hs
  rcases mem_sdiff_positiveBoundary_twoAtomRepair_local hs with hsEq | ⟨a, ha, hErase⟩
  · rw [hsEq]
    exact mem_union.mpr (Or.inr (by simp))
  · refine mem_union.mpr (Or.inl ?_)
    apply mem_positiveBoundary.mpr
    refine ⟨?_, ?_⟩
    · intro hsx
      have hsxEq : s = x := Finset.mem_singleton.mp hsx
      have hEq : s.erase a = s := by simpa [hsxEq] using hErase
      have haErase : a ∈ s.erase a := by
        rw [hEq]
        exact ha
      exact (notMem_erase a s) haErase
    · exact ⟨a, ha, by simp [hErase]⟩

theorem sdiff_positiveBoundary_of_twoAtomRepair_subset_local :
    positiveBoundary F \ positiveBoundary (familyRepair F x z) ⊆
      positiveBoundary ({z} : Finset (Finset α)) ∪ (({x} : Finset (Finset α))) := by
  intro s hs
  rcases mem_sdiff_positiveBoundary_of_twoAtomRepair_local hs with hsEq | ⟨a, ha, hErase⟩
  · rw [hsEq]
    exact mem_union.mpr (Or.inr (by simp))
  · refine mem_union.mpr (Or.inl ?_)
    apply mem_positiveBoundary.mpr
    refine ⟨?_, ?_⟩
    · intro hsz
      have hszEq : s = z := Finset.mem_singleton.mp hsz
      have hEq : s.erase a = s := by simpa [hszEq] using hErase
      have haErase : a ∈ s.erase a := by
        rw [hEq]
        exact ha
      exact (notMem_erase a s) haErase
    · exact ⟨a, ha, by simp [hErase]⟩

end Erdos1
