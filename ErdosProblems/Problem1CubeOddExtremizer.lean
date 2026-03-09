import ErdosProblems.Problem1CubeBoundary
import ErdosProblems.Problem1CubeDownset
import ErdosProblems.Problem1CubeMinimalOutside
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.UpperLower.Closure

open Finset

namespace Erdos1

/-- The lower half of the odd Boolean cube: all subsets of `Fin (2m+1)` of size at most `m`. -/
def oddLowerHalfFamily (m : ℕ) : Finset (Finset (Fin (2 * m + 1))) :=
  (Finset.univ : Finset (Fin (2 * m + 1))).powerset.filter fun s => s.card ≤ m

/-- The middle layer just above the odd lower half. -/
def oddMiddleLayer (m : ℕ) : Finset (Finset (Fin (2 * m + 1))) :=
  (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard (m + 1)

@[simp]
theorem mem_oddLowerHalfFamily {m : ℕ} {s : Finset (Fin (2 * m + 1))} :
    s ∈ oddLowerHalfFamily m ↔ s.card ≤ m := by
  simp [oddLowerHalfFamily]

@[simp]
theorem mem_oddMiddleLayer {m : ℕ} {s : Finset (Fin (2 * m + 1))} :
    s ∈ oddMiddleLayer m ↔ s.card = m + 1 := by
  simp [oddMiddleLayer]

theorem isDownSetFamily_oddLowerHalfFamily (m : ℕ) :
    IsDownSetFamily (oddLowerHalfFamily m) := by
  intro s t hts hs
  change t ∈ oddLowerHalfFamily m
  change s ∈ oddLowerHalfFamily m at hs
  rw [mem_oddLowerHalfFamily] at hs ⊢
  exact (Finset.card_le_card hts).trans hs

theorem oddLowerHalfFamily_eq_biUnion (m : ℕ) :
    oddLowerHalfFamily m =
      (Finset.range (m + 1)).biUnion
        (fun k => (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard k) := by
  ext s
  constructor
  · intro hs
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨s.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_oddLowerHalfFamily.mp hs)), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  · intro hs
    rcases Finset.mem_biUnion.mp hs with ⟨k, hk, hs⟩
    rw [mem_oddLowerHalfFamily]
    exact (Finset.mem_powersetCard.mp hs).2.symm ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem card_oddLowerHalfFamily (m : ℕ) :
    (oddLowerHalfFamily m).card = 4 ^ m := by
  rw [oddLowerHalfFamily_eq_biUnion]
  rw [Finset.card_biUnion]
  · simp_rw [Finset.card_powersetCard]
    simpa using Nat.sum_range_choose_halfway m
  · exact ((Finset.univ : Finset (Fin (2 * m + 1))).pairwise_disjoint_powersetCard).set_pairwise _

theorem card_oddLowerHalfFamily_eq_half_cube (m : ℕ) :
    (oddLowerHalfFamily m).card = 2 ^ (2 * m) := by
  rw [card_oddLowerHalfFamily, show 4 ^ m = 2 ^ (2 * m) by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]]

theorem positiveBoundary_oddLowerHalfFamily (m : ℕ) :
    positiveBoundary (oddLowerHalfFamily m) = oddMiddleLayer m := by
  ext s
  rw [mem_positiveBoundary, mem_oddMiddleLayer]
  constructor
  · rintro ⟨hsNot, a, ha, hsErase⟩
    rw [mem_oddLowerHalfFamily] at hsNot hsErase
    have hgt : m < s.card := lt_of_not_ge hsNot
    have hle : s.card ≤ m + 1 := by
      simpa [Finset.card_erase_of_mem ha] using Nat.succ_le_succ hsErase
    omega
  · intro hsCard
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    rcases hsne with ⟨a, ha⟩
    refine ⟨?_, a, ha, ?_⟩
    · rw [mem_oddLowerHalfFamily]
      omega
    · rw [mem_oddLowerHalfFamily]
      simpa [hsCard, Finset.card_erase_of_mem ha]

theorem card_oddMiddleLayer (m : ℕ) :
    (oddMiddleLayer m).card = Nat.choose (2 * m + 1) m := by
  simpa [oddMiddleLayer, Nat.choose_symm_half] using
    (Finset.card_powersetCard (m + 1) (Finset.univ : Finset (Fin (2 * m + 1))))

theorem card_positiveBoundary_oddLowerHalfFamily (m : ℕ) :
    (positiveBoundary (oddLowerHalfFamily m)).card = Nat.choose (2 * m + 1) m := by
  rw [positiveBoundary_oddLowerHalfFamily, card_oddMiddleLayer]

theorem isAntichain_oddMiddleLayer (m : ℕ) :
    IsAntichain (· ⊆ ·) (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1)))) := by
  simpa [oddMiddleLayer] using
    (Set.sized_powersetCard (Finset.univ : Finset (Fin (2 * m + 1))) (m + 1)).isAntichain

theorem upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily (m : ℕ) :
    (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
      Set (Finset (Fin (2 * m + 1)))) = (oddLowerHalfFamily m : Set (Finset (Fin (2 * m + 1))))ᶜ := by
  ext s
  constructor
  · intro hs
    rcases mem_upperClosure.mp hs with ⟨t, ht, hts⟩
    change t ∈ oddMiddleLayer m at ht
    rw [Set.mem_compl_iff, mem_coe, mem_oddLowerHalfFamily]
    rw [mem_oddMiddleLayer] at ht
    have hcard : t.card ≤ s.card := Finset.card_le_card hts
    omega
  · intro hs
    rw [Set.mem_compl_iff, mem_coe, mem_oddLowerHalfFamily] at hs
    rcases Finset.exists_subset_card_eq (s := s) (by omega : m + 1 ≤ s.card) with ⟨t, hts, htcard⟩
    exact mem_upperClosure.mpr ⟨t, by simpa [mem_oddMiddleLayer] using htcard, hts⟩

theorem minimalOutside_oddLowerHalfFamily (m : ℕ) :
    minimalOutside (oddLowerHalfFamily m) = oddMiddleLayer m := by
  apply eq_of_upperClosure_eq_of_isAntichain
  · exact isAntichain_minimalOutside _
  · exact isAntichain_oddMiddleLayer _
  · rw [upperClosure_minimalOutside_eq_compl (isDownSetFamily_oddLowerHalfFamily m),
      upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily]

theorem card_minimalOutside_oddLowerHalfFamily (m : ℕ) :
    #(minimalOutside (oddLowerHalfFamily m)) = Nat.choose (2 * m + 1) m := by
  rw [minimalOutside_oddLowerHalfFamily, card_oddMiddleLayer]

end Erdos1
