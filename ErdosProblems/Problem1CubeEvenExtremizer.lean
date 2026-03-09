import ErdosProblems.Problem1CubeOddExtremizer
import ErdosProblems.Problem1CubeDownset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Preimage

open Finset
open scoped FinsetFamily

namespace Erdos1

/-- Lift a family on `Fin n` into the nonzero coordinates of `Fin (n+1)`. -/
def succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  𝒜.map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding

@[simp]
theorem card_succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    #(succFamily 𝒜) = #𝒜 := by
  simp [succFamily]

theorem zero_not_mem_of_mem_succFamily {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} (hs : s ∈ succFamily 𝒜) :
    (0 : Fin (n + 1)) ∉ s := by
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change (0 : Fin (n + 1)) ∉ t.map (Fin.succEmb n)
  simp

theorem mem_succFamily_iff {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} :
    s ∈ succFamily 𝒜 ↔
      (0 : Fin (n + 1)) ∉ s ∧
      s.preimage Fin.succ (Fin.succ_injective n).injOn ∈ 𝒜 := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨t, ht, hts0⟩
    have hts : t.map (Fin.succEmb n) = s := by
      simpa [Finset.mapEmbedding_apply] using hts0
    constructor
    · exact zero_not_mem_of_mem_succFamily (𝒜 := 𝒜) (s := s) hs
    · rw [← hts]
      change (t.map (Fin.succEmb n)).preimage (Fin.succEmb n) (Fin.succEmb n).injective.injOn ∈ 𝒜
      rw [Finset.preimage_map]
      exact ht
  · rintro ⟨h0, ht⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨s.preimage Fin.succ (Fin.succ_injective n).injOn, ht, ?_⟩
    have hsImage : (s.preimage Fin.succ (Fin.succ_injective n).injOn).image Fin.succ = s := by
      rw [Finset.image_preimage Fin.succ s (Fin.succ_injective n).injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Fin.exists_succ_eq_of_ne_zero (by
        intro hx0
        exact h0 (hx0 ▸ hx)) with ⟨y, rfl⟩
      exact Set.mem_range_self y
    change (s.preimage Fin.succ (Fin.succ_injective n).injOn).map (Fin.succEmb n) = s
    simpa [Finset.map_eq_image] using hsImage

theorem card_preimage_succ {n : ℕ} {s : Finset (Fin (n + 1))}
    (h0 : (0 : Fin (n + 1)) ∉ s) :
    #(s.preimage Fin.succ (Fin.succ_injective n).injOn) = #s := by
  rw [Finset.card_preimage]
  have hfilter : {x ∈ s | x ∈ Set.range Fin.succ} = s := by
    apply Finset.filter_true_of_mem
    intro x hx
    rcases Fin.exists_succ_eq_of_ne_zero (by
      intro hx0
      exact h0 (hx0 ▸ hx)) with ⟨y, rfl⟩
    exact Set.mem_range_self y
  rw [hfilter]

theorem nonMemberSubfamily_eq_self_of_forall_not_mem {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} {a : α} (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    𝒜.nonMemberSubfamily a = 𝒜 := by
  ext s
  rw [mem_nonMemberSubfamily]
  constructor
  · exact fun hs => hs.1
  · intro hs
    exact ⟨hs, h𝒜 s hs⟩

theorem memberSubfamily_eq_empty_of_forall_not_mem {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} {a : α} (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    𝒜.memberSubfamily a = ∅ := by
  ext s
  rw [mem_memberSubfamily]
  constructor
  · intro hs
    exact (h𝒜 _ hs.1 (mem_insert_self _ _)).elim
  · simp

theorem preimage_erase_succ {n : ℕ} (s : Finset (Fin (n + 1))) (i : Fin n) :
    (s.erase i.succ).preimage Fin.succ (Fin.succ_injective n).injOn =
      (s.preimage Fin.succ (Fin.succ_injective n).injOn).erase i := by
  ext x
  simp

theorem mem_positiveBoundary_succFamily_iff {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} (h0 : (0 : Fin (n + 1)) ∉ s) :
    s ∈ positiveBoundary (succFamily 𝒜) ↔
      s.preimage Fin.succ (Fin.succ_injective n).injOn ∈ positiveBoundary 𝒜 := by
  constructor
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, b, hb, hsErase⟩
    have hb0 : b ≠ 0 := by
      intro hb0
      exact h0 (hb0 ▸ hb)
    rcases Fin.exists_succ_eq_of_ne_zero hb0 with ⟨c, rfl⟩
    refine mem_positiveBoundary.mpr ⟨?_, c, ?_, ?_⟩
    · intro hsPre
      exact hsNot ((mem_succFamily_iff).2 ⟨h0, hsPre⟩)
    · simpa using hb
    · have hsErase' := (mem_succFamily_iff (s := s.erase c.succ)).1 hsErase
      simpa [preimage_erase_succ] using hsErase'.2
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, c, hc, hsErase⟩
    refine mem_positiveBoundary.mpr ⟨?_, c.succ, ?_, ?_⟩
    · intro hsSucc
      exact hsNot ((mem_succFamily_iff (s := s)).1 hsSucc).2
    · simpa using hc
    · refine (mem_succFamily_iff (s := s.erase c.succ)).2 ⟨?_, ?_⟩
      · intro hmem
        exact h0 (Finset.mem_of_mem_erase hmem)
      · simpa [preimage_erase_succ] using hsErase

theorem nonMemberSubfamily_positiveBoundary_succFamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succFamily 𝒜)).nonMemberSubfamily 0 = succFamily (positiveBoundary 𝒜) := by
  ext s
  by_cases h0 : (0 : Fin (n + 1)) ∈ s
  · simp [mem_nonMemberSubfamily, h0, mem_succFamily_iff]
  · rw [mem_nonMemberSubfamily, mem_succFamily_iff]
    simp [h0, mem_positiveBoundary_succFamily_iff h0]

theorem memberSubfamily_positiveBoundary_succFamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succFamily 𝒜)).memberSubfamily 0 = succFamily 𝒜 := by
  ext s
  rw [mem_memberSubfamily, mem_succFamily_iff]
  constructor
  · rintro ⟨hsPb, h0⟩
    rcases mem_positiveBoundary.mp hsPb with ⟨-, b, hb, hsErase⟩
    have hb0 : b = 0 := by
      by_contra hne
      have hmem0 : (0 : Fin (n + 1)) ∈ (insert 0 s).erase b := by
        rw [mem_erase]
        exact ⟨fun h => hne h.symm, mem_insert_self 0 s⟩
      exact zero_not_mem_of_mem_succFamily hsErase hmem0
    subst hb0
    have hsSucc : s ∈ succFamily 𝒜 := by
      simpa [h0] using hsErase
    exact (mem_succFamily_iff).1 hsSucc
  · rintro ⟨h0, hsA⟩
    refine ⟨mem_positiveBoundary.mpr ?_, h0⟩
    refine ⟨?_, 0, mem_insert_self 0 s, ?_⟩
    · intro hsInsert
      exact (mem_succFamily_iff.mp hsInsert).1 (mem_insert_self 0 s)
    · have hsSucc : s ∈ succFamily 𝒜 := (mem_succFamily_iff).2 ⟨h0, hsA⟩
      simpa [h0] using hsSucc

theorem isDownSetFamily_succFamily {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (succFamily 𝒜) := by
  intro s t hts hs
  change t ∈ succFamily 𝒜
  change s ∈ succFamily 𝒜 at hs
  have hsData := mem_succFamily_iff.mp hs
  have ht0 : (0 : Fin (n + 1)) ∉ t := by
    intro ht0
    exact hsData.1 (hts ht0)
  refine (mem_succFamily_iff).2 ⟨ht0, ?_⟩
  exact h𝒜 ((Finset.monotone_preimage (Fin.succ_injective n)) hts) hsData.2

theorem sized_succFamily {n r : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r) :
    (succFamily 𝒜 : Set (Finset (Fin (n + 1)))).Sized r := by
  intro s hs
  rcases mem_succFamily_iff.mp hs with ⟨h0, hsA⟩
  simpa [card_preimage_succ h0] using h𝒜 hsA

theorem isAntichain_succFamily_oddMiddleLayer (m : ℕ) :
    IsAntichain (· ⊆ ·) (succFamily (oddMiddleLayer m) : Set (Finset (Fin (2 * m + 2)))) := by
  exact (sized_succFamily (n := 2 * m + 1) (r := m + 1)
    (by
      simpa [oddMiddleLayer] using
        (Set.sized_powersetCard (Finset.univ : Finset (Fin (2 * m + 1))) (m + 1)))).isAntichain

/-- A sharp half-cube witness in even dimension: two disjoint copies of the odd lower half, split
according to whether the distinguished coordinate `0` is absent or present. -/
def evenLowerHalfFamily (m : ℕ) : Finset (Finset (Fin (2 * m + 2))) :=
  let base := succFamily (oddLowerHalfFamily m)
  base ∪ base.image (insert 0)

theorem nonMemberSubfamily_evenLowerHalfFamily (m : ℕ) :
    (evenLowerHalfFamily m).nonMemberSubfamily 0 = succFamily (oddLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [evenLowerHalfFamily, Finset.nonMemberSubfamily_union, nonMemberSubfamily_image_insert]
  simpa [base] using nonMemberSubfamily_eq_self_of_forall_not_mem hbase

theorem memberSubfamily_evenLowerHalfFamily (m : ℕ) :
    (evenLowerHalfFamily m).memberSubfamily 0 = succFamily (oddLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [evenLowerHalfFamily, Finset.memberSubfamily_union]
  rw [memberSubfamily_eq_empty_of_forall_not_mem hbase, empty_union]
  simpa [base] using Finset.memberSubfamily_image_insert hbase

theorem mem_evenLowerHalfFamily_iff_of_zero_not_mem (m : ℕ) {s : Finset (Fin (2 * m + 2))}
    (hs0 : (0 : Fin (2 * m + 2)) ∉ s) :
    s ∈ evenLowerHalfFamily m ↔
      s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈ oddLowerHalfFamily m := by
  rw [evenLowerHalfFamily, mem_union, mem_succFamily_iff]
  constructor
  · intro hs
    rcases hs with hsBase | hsInsert
    · exact hsBase.2
    · rcases Finset.mem_image.mp hsInsert with ⟨t, -, hts⟩
      exact (hs0 (hts ▸ mem_insert_self 0 t)).elim
  · intro hs
    left
    exact ⟨hs0, hs⟩

theorem isDownSetFamily_evenLowerHalfFamily (m : ℕ) :
    IsDownSetFamily (evenLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : IsDownSetFamily base :=
    isDownSetFamily_succFamily (isDownSetFamily_oddLowerHalfFamily m)
  intro s t hts hs
  change t ∈ evenLowerHalfFamily m
  change s ∈ evenLowerHalfFamily m at hs
  rw [evenLowerHalfFamily, mem_union] at hs ⊢
  rcases hs with hsBase | hsInsert
  · exact Or.inl (hbase hts hsBase)
  · rcases Finset.mem_image.mp hsInsert with ⟨u, hu, rfl⟩
    by_cases ht0 : (0 : Fin (2 * m + 2)) ∈ t
    · right
      refine Finset.mem_image.mpr ⟨t.erase 0, ?_, insert_erase ht0⟩
      apply hbase
      · intro x hx
        have hxt : x ∈ t := Finset.mem_of_mem_erase hx
        have hsx : x ∈ insert 0 u := hts hxt
        rw [Finset.mem_insert] at hsx
        rcases hsx with hx0 | hxu
        · exact ((notMem_erase 0 t) (hx0 ▸ hx)).elim
        · exact hxu
      · exact hu
    · left
      apply hbase
      · intro x hx
        have hsx : x ∈ insert 0 u := hts hx
        rw [Finset.mem_insert] at hsx
        rcases hsx with hx0 | hxu
        · exact (ht0 (hx0 ▸ hx)).elim
        · exact hxu
      · exact hu

theorem card_evenLowerHalfFamily_eq_half_cube (m : ℕ) :
    (evenLowerHalfFamily m).card = 2 ^ (2 * m + 1) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  have hdisj : Disjoint base (base.image (insert 0)) := by
    refine Finset.disjoint_left.mpr ?_
    intro s hsBase hsImage
    have hnot : (0 : Fin (2 * m + 2)) ∉ s := hbase s hsBase
    rcases Finset.mem_image.mp hsImage with ⟨t, ht, rfl⟩
    exact hnot (mem_insert_self _ _)
  rw [evenLowerHalfFamily, Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_image_of_injOn]
  · dsimp [base]
    rw [card_succFamily, card_oddLowerHalfFamily_eq_half_cube]
    ring_nf
  · intro s hs t ht hst
    have hs0 : (0 : Fin (2 * m + 2)) ∉ s := hbase s hs
    have ht0 : (0 : Fin (2 * m + 2)) ∉ t := hbase t ht
    have hErase := congrArg (fun u : Finset (Fin (2 * m + 2)) => u.erase 0) hst
    simpa [hs0, ht0] using hErase

theorem nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    (positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0 =
      succFamily (oddMiddleLayer m) := by
  rw [nonMemberSubfamily_positiveBoundary (a := 0) (𝒜 := evenLowerHalfFamily m)]
  rw [nonMemberSubfamily_evenLowerHalfFamily, nonMemberSubfamily_positiveBoundary_succFamily]
  rw [positiveBoundary_oddLowerHalfFamily]

theorem memberSubfamily_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    (positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0 =
      succFamily (oddMiddleLayer m) := by
  rw [memberSubfamily_positiveBoundary]
  rw [nonMemberSubfamily_evenLowerHalfFamily, memberSubfamily_evenLowerHalfFamily]
  simp [nonMemberSubfamily_positiveBoundary_succFamily, positiveBoundary_oddLowerHalfFamily]

theorem card_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    #(positiveBoundary (evenLowerHalfFamily m)) = Nat.choose (2 * m + 2) (m + 1) := by
  rw [← Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0
    (positiveBoundary (evenLowerHalfFamily m))]
  rw [memberSubfamily_positiveBoundary_evenLowerHalfFamily,
    nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
    card_succFamily, card_oddMiddleLayer]
  rw [Nat.choose_succ_succ', Nat.choose_symm_half]

theorem upperClosure_succFamily_oddMiddleLayer_eq_compl_evenLowerHalfFamily (m : ℕ) :
    (↑(upperClosure (succFamily (oddMiddleLayer m) : Set (Finset (Fin (2 * m + 2))))) :
      Set (Finset (Fin (2 * m + 2)))) = (evenLowerHalfFamily m : Set (Finset (Fin (2 * m + 2))))ᶜ := by
  ext s
  constructor
  · intro hs hsEven
    rcases mem_upperClosure.mp hs with ⟨t, ht, hts⟩
    change t ∈ succFamily (oddMiddleLayer m) at ht
    have htEven : t ∈ evenLowerHalfFamily m := isDownSetFamily_evenLowerHalfFamily m hts hsEven
    have ht0 : (0 : Fin (2 * m + 2)) ∉ t := zero_not_mem_of_mem_succFamily ht
    have htMid : #(t.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn) = m + 1 := by
      simpa [mem_oddMiddleLayer] using (mem_succFamily_iff.mp ht).2
    have htLow : t.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈ oddLowerHalfFamily m := by
      rw [← mem_evenLowerHalfFamily_iff_of_zero_not_mem m ht0]
      exact htEven
    rw [mem_oddLowerHalfFamily] at htLow
    omega
  · intro hs
    by_cases hs0 : (0 : Fin (2 * m + 2)) ∈ s
    · have hsOddNot : (s.erase 0).preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∉
          oddLowerHalfFamily m := by
        intro hsLow
        have hsBase : s.erase 0 ∈ succFamily (oddLowerHalfFamily m) :=
          (mem_succFamily_iff).2 ⟨notMem_erase 0 s, hsLow⟩
        have hsImage : s ∈ (succFamily (oddLowerHalfFamily m)).image (insert 0) :=
          Finset.mem_image.mpr ⟨s.erase 0, hsBase, insert_erase hs0⟩
        exact hs <| by
          change s ∈ evenLowerHalfFamily m
          rw [evenLowerHalfFamily, mem_union]
          exact Or.inr hsImage
      have hsUpper : (s.erase 0).preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈
          (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
            Set (Finset (Fin (2 * m + 1)))) := by
        rw [upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily]
        simpa [Set.mem_compl_iff, mem_coe] using hsOddNot
      rcases mem_upperClosure.mp hsUpper with ⟨u, hu, hus⟩
      refine mem_upperClosure.mpr ⟨u.map (Fin.succEmb (2 * m + 1)), ?_, ?_⟩
      · change u.map (Fin.succEmb (2 * m + 1)) ∈ succFamily (oddMiddleLayer m)
        change u ∈ oddMiddleLayer m at hu
        exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Finset.mem_of_mem_erase (Finset.mem_preimage.mp (hus hy))
    · have hsOddNot : s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∉
          oddLowerHalfFamily m := by
        rw [← mem_evenLowerHalfFamily_iff_of_zero_not_mem m hs0]
        exact hs
      have hsUpper : s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈
          (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
            Set (Finset (Fin (2 * m + 1)))) := by
        rw [upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily]
        simpa [Set.mem_compl_iff, mem_coe] using hsOddNot
      rcases mem_upperClosure.mp hsUpper with ⟨u, hu, hus⟩
      refine mem_upperClosure.mpr ⟨u.map (Fin.succEmb (2 * m + 1)), ?_, ?_⟩
      · change u.map (Fin.succEmb (2 * m + 1)) ∈ succFamily (oddMiddleLayer m)
        change u ∈ oddMiddleLayer m at hu
        exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Finset.mem_preimage.mp (hus hy)

theorem minimalOutside_evenLowerHalfFamily (m : ℕ) :
    minimalOutside (evenLowerHalfFamily m) = succFamily (oddMiddleLayer m) := by
  apply eq_of_upperClosure_eq_of_isAntichain
  · exact isAntichain_minimalOutside _
  · exact isAntichain_succFamily_oddMiddleLayer _
  · rw [upperClosure_minimalOutside_eq_compl (isDownSetFamily_evenLowerHalfFamily m),
      upperClosure_succFamily_oddMiddleLayer_eq_compl_evenLowerHalfFamily]

theorem card_minimalOutside_evenLowerHalfFamily (m : ℕ) :
    #(minimalOutside (evenLowerHalfFamily m)) = Nat.choose (2 * m + 1) m := by
  rw [minimalOutside_evenLowerHalfFamily, card_succFamily, card_oddMiddleLayer]

end Erdos1
