import ErdosProblems.Problem1CubeBoundary
import ErdosProblems.Problem1CubeDownset
import Mathlib.Order.UpperLower.Closure

open Finset
open scoped FinsetFamily

namespace Erdos1

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- An antichain is determined by its upper closure. -/
theorem eq_of_upperClosure_eq_of_isAntichain {β : Type*} [DecidableEq β] [PartialOrder β]
    {𝒜 ℬ : Finset β}
    (h𝒜 : IsAntichain (· ≤ ·) (𝒜 : Set β))
    (hℬ : IsAntichain (· ≤ ·) (ℬ : Set β))
    (hEq : (↑(upperClosure (𝒜 : Set β)) : Set β) = ↑(upperClosure (ℬ : Set β))) :
    𝒜 = ℬ := by
  have hMem : ∀ {x : β}, x ∈ upperClosure (𝒜 : Set β) ↔ x ∈ upperClosure (ℬ : Set β) := by
    intro x
    exact by simpa using congrArg (fun s : Set β => x ∈ s) hEq
  ext x
  constructor <;> intro hx
  · refine (hℬ.minimal_mem_upperClosure_iff_mem).1 ?_
    rcases (h𝒜.minimal_mem_upperClosure_iff_mem).2 hx with ⟨hxUp, hxMin⟩
    exact ⟨hMem.mp hxUp, fun y hy hyx => hxMin (hMem.mpr hy) hyx⟩
  · refine (h𝒜.minimal_mem_upperClosure_iff_mem).1 ?_
    rcases (hℬ.minimal_mem_upperClosure_iff_mem).2 hx with ⟨hxUp, hxMin⟩
    exact ⟨hMem.mpr hxUp, fun y hy hyx => hxMin (hMem.mp hy) hyx⟩

/--
The minimal excluded sets of a family: sets outside the family whose proper subsets are all inside.
These are the minimal elements of the complement in the Boolean lattice.
-/
def minimalOutside (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (Finset.univ.powerset).filter fun s => s ∉ 𝒜 ∧ ∀ ⦃t : Finset α⦄, t ⊂ s → t ∈ 𝒜

@[simp]
theorem mem_minimalOutside {𝒜 : Finset (Finset α)} {s : Finset α} :
    s ∈ minimalOutside 𝒜 ↔ s ∉ 𝒜 ∧ ∀ ⦃t : Finset α⦄, t ⊂ s → t ∈ 𝒜 := by
  simp [minimalOutside]

theorem isAntichain_minimalOutside (𝒜 : Finset (Finset α)) :
    IsAntichain (· ⊆ ·) (minimalOutside 𝒜 : Set (Finset α)) := by
  intro s hs t ht hne hst
  have hsIn : s ∈ 𝒜 :=
    (mem_minimalOutside.mp ht).2 (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
  exact ((mem_minimalOutside.mp hs).1 hsIn).elim

theorem minimalOutside_subset_positiveBoundary {𝒜 : Finset (Finset α)} (hEmpty : ∅ ∈ 𝒜) :
    minimalOutside 𝒜 ⊆ positiveBoundary 𝒜 := by
  intro s hs
  rcases mem_minimalOutside.mp hs with ⟨hsNotA, hsMin⟩
  have hsne : s ≠ ∅ := by
    intro hs0
    exact hsNotA (hs0 ▸ hEmpty)
  rcases Finset.nonempty_iff_ne_empty.mpr hsne with ⟨a, ha⟩
  exact mem_positiveBoundary.mpr ⟨hsNotA, a, ha, hsMin (Finset.erase_ssubset ha)⟩

theorem minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (hne : 𝒜.Nonempty) :
    minimalOutside 𝒜 ⊆ positiveBoundary 𝒜 :=
  minimalOutside_subset_positiveBoundary
    (empty_mem_of_nonempty_isDownSetFamily h𝒜 hne)

theorem card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (hne : 𝒜.Nonempty) :
    #(minimalOutside 𝒜) ≤ #(positiveBoundary 𝒜) :=
  Finset.card_le_card
    (minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily h𝒜 hne)

theorem positiveBoundary_subset_minimalOutside_of_nonempty_isDownSetFamily_of_isAntichain
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (hne : 𝒜.Nonempty)
    (hAnt : IsAntichain (· ⊆ ·) (positiveBoundary 𝒜 : Set (Finset α))) :
    positiveBoundary 𝒜 ⊆ minimalOutside 𝒜 := by
  intro s hs
  rcases mem_positiveBoundary.mp hs with ⟨hsNotA, _, _, _⟩
  obtain ⟨t, hts, htMin⟩ := Finite.exists_le_minimal (p := fun u : Finset α => u ∉ 𝒜) hsNotA
  have htMinMem : t ∈ minimalOutside 𝒜 := by
    refine mem_minimalOutside.mpr ⟨htMin.1, ?_⟩
    intro u hu
    have hnot : ¬ u ∉ 𝒜 := htMin.not_prop_of_lt hu
    simpa using hnot
  have htPos : t ∈ positiveBoundary 𝒜 :=
    minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily h𝒜 hne htMinMem
  have htsEq : t = s := by
    by_contra hne'
    exact hAnt htPos hs hne' hts
  simpa [htsEq] using htMinMem

theorem positiveBoundary_eq_minimalOutside_of_nonempty_isDownSetFamily_of_isAntichain
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (hne : 𝒜.Nonempty)
    (hAnt : IsAntichain (· ⊆ ·) (positiveBoundary 𝒜 : Set (Finset α))) :
    positiveBoundary 𝒜 = minimalOutside 𝒜 := by
  apply Finset.Subset.antisymm
  · exact positiveBoundary_subset_minimalOutside_of_nonempty_isDownSetFamily_of_isAntichain
      h𝒜 hne hAnt
  · exact minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily h𝒜 hne

theorem card_positiveBoundary_ge_of_nonempty_downSet_minimalOutside_lower
    (hstep : ∀ a : α, ∀ 𝒜 : Finset (Finset α),
      #(positiveBoundary (downCompression a 𝒜)) ≤ #(positiveBoundary 𝒜))
    {m k : ℕ}
    (hdown : ∀ {𝒟 : Finset (Finset α)},
      𝒟.Nonempty → IsDownSetFamily 𝒟 → #𝒟 = m → k ≤ #(minimalOutside 𝒟))
    {𝒜 : Finset (Finset α)} (hne : 𝒜.Nonempty) (hcard : #𝒜 = m) :
    k ≤ #(positiveBoundary 𝒜) := by
  rcases exists_nonempty_downSetFamily_card_eq_le_positiveBoundary hstep hne with
    ⟨𝒟, hne𝒟, h𝒟, hcard𝒟, hbdry⟩
  exact (hdown hne𝒟 h𝒟 (hcard𝒟.trans hcard)).trans
    ((card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily h𝒟 hne𝒟).trans hbdry)

theorem mem_upperClosure_minimalOutside_of_not_mem {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∉ 𝒜) :
    s ∈ upperClosure (minimalOutside 𝒜 : Set (Finset α)) := by
  obtain ⟨t, hts, htMin⟩ := Finite.exists_le_minimal (p := fun u : Finset α => u ∉ 𝒜) hs
  refine mem_upperClosure.mpr ?_
  refine ⟨t, ?_, hts⟩
  exact mem_minimalOutside.mpr ⟨htMin.1, fun u hu => by
    have hnot : ¬ u ∉ 𝒜 := htMin.not_prop_of_lt hu
    simpa using hnot⟩

theorem not_mem_of_mem_upperClosure_minimalOutside {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) {s : Finset α}
    (hs : s ∈ upperClosure (minimalOutside 𝒜 : Set (Finset α))) :
    s ∉ 𝒜 := by
  rcases mem_upperClosure.mp hs with ⟨t, ht, hts⟩
  exact (mem_minimalOutside.mp ht).1 ∘ h𝒜 hts

theorem nonMemberSubfamily_minimalOutside (a : α) (𝒜 : Finset (Finset α)) :
    (minimalOutside 𝒜).nonMemberSubfamily a =
      (minimalOutside (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a := by
  ext s
  by_cases ha : a ∈ s
  · simp [mem_nonMemberSubfamily, ha]
  · rw [mem_nonMemberSubfamily, mem_nonMemberSubfamily, mem_minimalOutside, mem_minimalOutside]
    constructor
    · rintro ⟨⟨hsNotA, hsMin⟩, -⟩
      refine ⟨⟨?_, ?_⟩, ha⟩
      · intro hsSection
        exact hsNotA (mem_nonMemberSubfamily.mp hsSection).1
      · intro t ht
        refine mem_nonMemberSubfamily.mpr ⟨hsMin ht, ?_⟩
        exact fun hat => ha ((Finset.ssubset_iff_subset_ne.mp ht).1 hat)
    · rintro ⟨⟨hsNotSection, hsMin⟩, -⟩
      refine ⟨⟨?_, ?_⟩, ha⟩
      · intro hsA
        exact hsNotSection (mem_nonMemberSubfamily.mpr ⟨hsA, ha⟩)
      · intro t ht
        exact (mem_nonMemberSubfamily.mp (hsMin ht)).1

theorem memberSubfamily_minimalOutside (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    (minimalOutside 𝒜).memberSubfamily a =
      (minimalOutside (𝒜.memberSubfamily a)).nonMemberSubfamily a ∩ 𝒜.nonMemberSubfamily a := by
  ext s
  rw [mem_memberSubfamily, mem_inter, mem_nonMemberSubfamily, mem_nonMemberSubfamily,
    mem_minimalOutside, mem_minimalOutside, mem_memberSubfamily]
  constructor
  · rintro ⟨hsMin, ha⟩
    rcases hsMin with ⟨hsNotInsert, hsMin⟩
    have hsA : s ∈ 𝒜 := hsMin (Finset.ssubset_insert ha)
    refine ⟨⟨?_, ha⟩, ⟨hsA, ha⟩⟩
    refine ⟨?_, ?_⟩
    · intro hsMember
      exact hsNotInsert hsMember.1
    · intro t ht
      have hta : a ∉ t := fun hat => ha ((Finset.ssubset_iff_subset_ne.mp ht).1 hat)
      have htInsert : insert a t ⊂ insert a s := by
        refine Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.insert_subset_insert a (Finset.ssubset_iff_subset_ne.mp ht).1, ?_⟩
        intro hEq
        apply (Finset.ssubset_iff_subset_ne.mp ht).2
        simpa [hta, ha] using congrArg (fun u : Finset α => u.erase a) hEq
      exact mem_memberSubfamily.mpr ⟨hsMin htInsert, hta⟩
  · rintro ⟨⟨hsMin, ha⟩, ⟨hsA, -⟩⟩
    refine ⟨?_, ha⟩
    rcases hsMin with ⟨hsNotMember, hsMinMember⟩
    refine ⟨?_, ?_⟩
    · intro hsInsert
      exact hsNotMember ⟨hsInsert, ha⟩
    · intro u hu
      by_cases hau : a ∈ u
      · have hEraseSub : u.erase a ⊂ s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · simpa [ha] using
              Finset.erase_subset_erase a (Finset.ssubset_iff_subset_ne.mp hu).1
          · intro hEq
            apply (Finset.ssubset_iff_subset_ne.mp hu).2
            simpa [hau, ha, hEq] using (insert_erase hau).symm
        have hMemMember : u.erase a ∈ 𝒜.memberSubfamily a := hsMinMember hEraseSub
        simpa [hau] using (mem_memberSubfamily.mp hMemMember).1
      · have huSub : u ⊆ s := (Finset.subset_insert_iff_of_notMem hau).1
            ((Finset.ssubset_iff_subset_ne.mp hu).1)
        by_cases hus : u = s
        · simpa [hus] using hsA
        · have huSsub : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨huSub, hus⟩
          have hMemMember : u ∈ 𝒜.memberSubfamily a := hsMinMember huSsub
          exact h𝒜 (Finset.subset_insert _ _) ((mem_memberSubfamily.mp hMemMember).1)

theorem upperClosure_minimalOutside_eq_compl {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) :
    ↑(upperClosure (minimalOutside 𝒜 : Set (Finset α))) = (𝒜 : Set (Finset α))ᶜ := by
  ext s
  constructor
  · exact not_mem_of_mem_upperClosure_minimalOutside h𝒜
  · exact mem_upperClosure_minimalOutside_of_not_mem

end Erdos1
