import ErdosProblems.Problem1CubeBoundary
import Mathlib.Combinatorics.SetFamily.Compression.UV

open Finset
open scoped FinsetFamily

namespace Erdos1

variable {α : Type*} [DecidableEq α]

/-- UV compression on cube families, re-exported under the Erdos1 boundary namespace. -/
abbrev uvCompression (u v : Finset α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝓒 u v 𝒜

/-- Coordinate compression is the singleton-instance of UV compression. -/
abbrev coordCompression (i j : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  uvCompression ({i}) ({j}) 𝒜

/-- Swap the membership of two coordinates when exactly one of them is present. -/
def swapCoord (i j : α) (s : Finset α) : Finset α :=
  if _ : i ∈ s ∧ j ∉ s then insert j (s.erase i)
  else if _ : j ∈ s ∧ i ∉ s then insert i (s.erase j)
  else s

@[simp]
theorem card_uvCompression (u v : Finset α) (𝒜 : Finset (Finset α)) :
    #(uvCompression u v 𝒜) = #𝒜 := by
  simp [uvCompression]

@[simp]
theorem card_coordCompression (i j : α) (𝒜 : Finset (Finset α)) :
    #(coordCompression i j 𝒜) = #𝒜 := by
  simp [coordCompression, uvCompression]

/-- Equal-size UV compression preserves a uniform layer. -/
theorem sized_uvCompression {u v : Finset α} {𝒜 : Finset (Finset α)} {r : ℕ}
    (huv : #u = #v) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (uvCompression u v 𝒜 : Set (Finset α)).Sized r := by
  simpa [uvCompression] using h𝒜.uvCompression huv

/-- Coordinate compression preserves every fixed rank. -/
theorem sized_coordCompression {i j : α} {𝒜 : Finset (Finset α)} {r : ℕ}
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (coordCompression i j 𝒜 : Set (Finset α)).Sized r := by
  simpa [coordCompression, uvCompression] using
    h𝒜.uvCompression (show #(({i} : Finset α)) = #(({j} : Finset α)) by simp)

theorem swapCoord_of_mem_left {i j : α} {s : Finset α} (hi : i ∈ s) (hj : j ∉ s) :
    swapCoord i j s = insert j (s.erase i) := by
  simp [swapCoord, hi, hj]

theorem swapCoord_of_mem_right {i j : α} {s : Finset α} (hj : j ∈ s) (hi : i ∉ s) :
    swapCoord i j s = insert i (s.erase j) := by
  simp [swapCoord, hi, hj]

theorem swapCoord_of_same_side {i j : α} {s : Finset α}
    (h : (i ∈ s ∧ j ∈ s) ∨ (i ∉ s ∧ j ∉ s)) :
    swapCoord i j s = s := by
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> simp [swapCoord, hi, hj]

theorem coordCompress_of_mem_left {i j : α} {s : Finset α} (hi : i ∈ s) (hj : j ∉ s) :
    UV.compress ({i} : Finset α) ({j} : Finset α) s = s := by
  simp [UV.compress, hi, hj]

theorem swapCoord_eq_union_sdiff_singleton_of_mem_left {i j : α} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s) :
    swapCoord i j s = (s ∪ ({j} : Finset α)) \ ({i} : Finset α) := by
  rw [swapCoord_of_mem_left hi hj]
  have hij : i ≠ j := by
    intro hij
    subst hij
    exact hj hi
  ext x
  by_cases hxi : x = i <;> by_cases hxj : x = j
  · subst x
    simp [hij]
  · subst x
    exact by simp [hij]
  · subst x
    exact by simp [Ne.symm hij]
  · simp [hxi, hxj]

theorem mem_swapCoord_right_of_mem_left {i j : α} {s : Finset α} (hi : i ∈ s) (hj : j ∉ s) :
    j ∈ swapCoord i j s := by
  rw [swapCoord_of_mem_left hi hj]
  simp

theorem not_mem_swapCoord_left_of_mem_left {i j : α} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s) :
    i ∉ swapCoord i j s := by
  rw [swapCoord_of_mem_left hi hj]
  have hij : i ≠ j := by
    intro hij
    subst hij
    exact hj hi
  simp [hij]

theorem coordCompress_of_mem_right {i j : α} {s : Finset α} (hi : i ∉ s) (hj : j ∈ s) :
    UV.compress ({i} : Finset α) ({j} : Finset α) s = swapCoord i j s := by
  rw [swapCoord_of_mem_right hj hi]
  have hdisj : Disjoint ({i} : Finset α) s := by
    simp [hi]
  have hsub : ({j} : Finset α) ⊆ s := by
    simpa using hj
  rw [UV.compress_of_disjoint_of_le hdisj hsub]
  have hij : i ≠ j := by
    intro hij
    subst hij
    exact hi hj
  ext x
  by_cases hxi : x = i <;> by_cases hxj : x = j
  · subst x
    simp [hij]
  · subst x
    exact by simp [hij]
  · subst x
    exact by simp [Ne.symm hij]
  · simp [hxi, hxj]

theorem swapCoord_eq_union_sdiff_singleton_of_mem_right {i j : α} {s : Finset α}
    (hi : i ∉ s) (hj : j ∈ s) :
    swapCoord i j s = (s ∪ ({i} : Finset α)) \ ({j} : Finset α) := by
  rw [swapCoord_of_mem_right hj hi]
  have hij : i ≠ j := by
    intro hij
    subst hij
    exact hi hj
  ext x
  by_cases hxi : x = i <;> by_cases hxj : x = j
  · subst x
    simp [hij]
  · subst x
    exact by simp [hij]
  · subst x
    exact by simp [Ne.symm hij]
  · simp [hxi, hxj]

theorem mem_swapCoord_left_of_mem_right {i j : α} {s : Finset α} (hi : i ∉ s) (hj : j ∈ s) :
    i ∈ swapCoord i j s := by
  rw [swapCoord_of_mem_right hj hi]
  simp

theorem not_mem_swapCoord_right_of_mem_right {i j : α} {s : Finset α}
    (hi : i ∉ s) (hj : j ∈ s) :
    j ∉ swapCoord i j s := by
  rw [swapCoord_of_mem_right hj hi]
  have hij : i ≠ j := by
    intro hij
    subst hij
    exact hi hj
  simpa [Ne.symm hij]

theorem swapCoord_swapArgs_of_mem_left {i j : α} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s) :
    swapCoord j i s = swapCoord i j s := by
  rw [swapCoord_of_mem_right (i := j) (j := i) (s := s) hi hj]
  rw [swapCoord_of_mem_left hi hj]

theorem swapCoord_swapCoord_of_mem_left {i j : α} {s : Finset α} (hi : i ∈ s) (hj : j ∉ s) :
    swapCoord i j (swapCoord i j s) = s := by
  have hcomp : UV.compress ({i} : Finset α) ({j} : Finset α) (swapCoord i j s) = s := by
    simpa [swapCoord_eq_union_sdiff_singleton_of_mem_left hi hj] using
      (UV.compress_of_disjoint_of_le'
        (u := ({i} : Finset α)) (v := ({j} : Finset α)) (a := s)
        (by simpa [Finset.disjoint_left, hj])
        (by simpa using hi))
  rw [coordCompress_of_mem_right
      (not_mem_swapCoord_left_of_mem_left hi hj)
      (mem_swapCoord_right_of_mem_left hi hj)] at hcomp
  exact hcomp

theorem swapCoord_swapCoord_of_mem_right {i j : α} {s : Finset α} (hi : i ∉ s) (hj : j ∈ s) :
    swapCoord i j (swapCoord i j s) = s := by
  have hcomp : UV.compress ({j} : Finset α) ({i} : Finset α) (swapCoord i j s) = s := by
    simpa [swapCoord_eq_union_sdiff_singleton_of_mem_right hi hj] using
      (UV.compress_of_disjoint_of_le'
        (u := ({j} : Finset α)) (v := ({i} : Finset α)) (a := s)
        (by simpa [Finset.disjoint_left, hi])
        (by simpa using hj))
  rw [coordCompress_of_mem_right
      (i := j) (j := i)
      (not_mem_swapCoord_right_of_mem_right hi hj)
      (mem_swapCoord_left_of_mem_right hi hj)] at hcomp
  rw [swapCoord_swapArgs_of_mem_left
      (i := i) (j := j) (s := swapCoord i j s)
      (mem_swapCoord_left_of_mem_right hi hj)
      (not_mem_swapCoord_right_of_mem_right hi hj)] at hcomp
  exact hcomp

theorem coordCompression_mem_both_iff {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∈ s) (hj : j ∈ s) :
    s ∈ coordCompression i j 𝒜 ↔ s ∈ 𝒜 := by
  rw [coordCompression, uvCompression, UV.mem_compression]
  constructor
  · rintro (⟨hsA, -⟩ | ⟨hsA, b, hbA, hcb⟩)
    · exact hsA
    · exfalso
      have hb : b = s := by
        by_cases hbi : i ∈ b <;> by_cases hbj : j ∈ b
        · simpa [UV.compress, hbi, hbj] using hcb
        · simpa [UV.compress, hbi, hbj] using hcb
        · have hsj : j ∉ s := by
            rw [← hcb]
            simp [UV.compress, hbi, hbj]
          exact (hsj hj).elim
        · simpa [UV.compress, hbi, hbj] using hcb
      exact hsA (hb.symm ▸ hbA)
  · intro hsA
    exact Or.inl ⟨hsA, by simp [UV.compress, hi, hj, hsA]⟩

theorem coordCompression_mem_neither_iff {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∉ s) (hj : j ∉ s) :
    s ∈ coordCompression i j 𝒜 ↔ s ∈ 𝒜 := by
  rw [coordCompression, uvCompression, UV.mem_compression]
  constructor
  · rintro (⟨hsA, -⟩ | ⟨hsA, b, hbA, hcb⟩)
    · exact hsA
    · exfalso
      have hb : b = s := by
        by_cases hbi : i ∈ b <;> by_cases hbj : j ∈ b
        · simpa [UV.compress, hbi, hbj] using hcb
        · simpa [UV.compress, hbi, hbj] using hcb
        · have hij : i ≠ j := by
            intro hij
            subst hij
            exact hbi hbj
          have hsi : i ∈ s := by
            rw [← hcb]
            simp [UV.compress, hbi, hbj, hij]
          exact (hi hsi).elim
        · simpa [UV.compress, hbi, hbj] using hcb
      exact hsA (hb.symm ▸ hbA)
  · intro hsA
    exact Or.inl ⟨hsA, by simp [UV.compress, hi, hj, hsA]⟩

theorem coordCompression_mem_left_iff {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s) :
    s ∈ coordCompression i j 𝒜 ↔ s ∈ 𝒜 ∨ swapCoord i j s ∈ 𝒜 := by
  constructor
  · intro hs
    have hsComp : s ∈ 𝓒 ({i} : Finset α) ({j} : Finset α) 𝒜 := by
      simpa [coordCompression, uvCompression] using hs
    have hsComp' := hsComp
    rw [UV.mem_compression] at hsComp'
    rcases hsComp' with ⟨hsA, -⟩ | ⟨hsA, b, hbA, hcb⟩
    · exact Or.inl hsA
    · right
      have hswapA : (s ∪ ({j} : Finset α)) \ ({i} : Finset α) ∈ 𝒜 :=
        UV.sup_sdiff_mem_of_mem_compression_of_notMem
          (u := ({i} : Finset α)) (v := ({j} : Finset α))
          (s := 𝒜) (a := s) hsComp hsA
      simpa [swapCoord_eq_union_sdiff_singleton_of_mem_left hi hj] using hswapA
  · intro hs
    rw [coordCompression, uvCompression, UV.mem_compression]
    rcases hs with hsA | hswapA
    · exact Or.inl ⟨hsA, by simpa [coordCompress_of_mem_left hi hj] using hsA⟩
    · by_cases hsA : s ∈ 𝒜
      · exact Or.inl ⟨hsA, by simpa [coordCompress_of_mem_left hi hj] using hsA⟩
      · refine Or.inr ⟨hsA, swapCoord i j s, hswapA, ?_⟩
        simpa [swapCoord_eq_union_sdiff_singleton_of_mem_left hi hj] using
          (UV.compress_of_disjoint_of_le'
            (u := ({i} : Finset α)) (v := ({j} : Finset α)) (a := s)
            (by simpa [Finset.disjoint_left, hj])
            (by simpa using hi))

theorem coordCompression_mem_right_iff {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∉ s) (hj : j ∈ s) :
    s ∈ coordCompression i j 𝒜 ↔ s ∈ 𝒜 ∧ swapCoord i j s ∈ 𝒜 := by
  constructor
  · intro hs
    have hsComp : s ∈ 𝓒 ({i} : Finset α) ({j} : Finset α) 𝒜 := by
      simpa [coordCompression, uvCompression] using hs
    have hsComp' := hsComp
    rw [UV.mem_compression] at hsComp'
    rcases hsComp' with ⟨hsA, hcsA⟩ | ⟨hsA, b, hbA, hcb⟩
    · exact ⟨hsA, by simpa [coordCompress_of_mem_right hi hj] using hcsA⟩
    · exfalso
      have his : ({i} : Finset α) ⊆ s :=
        UV.le_of_mem_compression_of_notMem
          (u := ({i} : Finset α)) (v := ({j} : Finset α))
          (s := 𝒜) (a := s) hsComp hsA
      exact hi (his (by simp))
  · rintro ⟨hsA, hswapA⟩
    rw [coordCompression, uvCompression, UV.mem_compression]
    exact Or.inl ⟨hsA, by simpa [coordCompress_of_mem_right hi hj] using hswapA⟩

theorem mem_coordCompression_sdiff_iff_swap_mem_sdiff_coordCompression
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s) :
    s ∈ coordCompression i j 𝒜 \ 𝒜 ↔ swapCoord i j s ∈ 𝒜 \ coordCompression i j 𝒜 := by
  rw [mem_sdiff, mem_sdiff]
  constructor
  · rintro ⟨hsComp, hsNotA⟩
    have hswapA : swapCoord i j s ∈ 𝒜 := by
      rcases (coordCompression_mem_left_iff hi hj).mp hsComp with hsA | hswapA
      · exact (hsNotA hsA).elim
      · exact hswapA
    have hswapNotComp : swapCoord i j s ∉ coordCompression i j 𝒜 := by
      intro hswapComp
      have hsA : s ∈ 𝒜 := by
        have hpair :=
          (coordCompression_mem_right_iff
            (not_mem_swapCoord_left_of_mem_left hi hj)
            (mem_swapCoord_right_of_mem_left hi hj)).mp hswapComp
        simpa [swapCoord_swapCoord_of_mem_left hi hj] using hpair.2
      exact hsNotA hsA
    exact ⟨hswapA, hswapNotComp⟩
  · rintro ⟨hswapA, hswapNotComp⟩
    have hsNotA : s ∉ 𝒜 := by
      intro hsA
      have hswapComp : swapCoord i j s ∈ coordCompression i j 𝒜 := by
        exact (coordCompression_mem_right_iff
          (not_mem_swapCoord_left_of_mem_left hi hj)
          (mem_swapCoord_right_of_mem_left hi hj)).2
            ⟨hswapA, by simpa [swapCoord_swapCoord_of_mem_left hi hj] using hsA⟩
      exact hswapNotComp hswapComp
    have hsComp : s ∈ coordCompression i j 𝒜 :=
      (coordCompression_mem_left_iff hi hj).2 (Or.inr hswapA)
    exact ⟨hsComp, hsNotA⟩

theorem shadow_coordCompression_subset_coordCompression_shadow (i j : α) (𝒜 : Finset (Finset α)) :
    ∂ (coordCompression i j 𝒜) ⊆ coordCompression i j (∂ 𝒜) := by
  simpa [coordCompression, uvCompression] using
    (UV.shadow_compression_subset_compression_shadow ({i} : Finset α) ({j} : Finset α) (𝒜 := 𝒜)
      (by
        intro x hx
        refine ⟨j, by simp, ?_⟩
        have hxi : x = i := by simpa using hx
        simpa [hxi] using (UV.isCompressed_self (∅ : Finset α) 𝒜)))

theorem card_shadow_coordCompression_le (i j : α) (𝒜 : Finset (Finset α)) :
    #(∂ (coordCompression i j 𝒜)) ≤ #(∂ 𝒜) := by
  calc
    #(∂ (coordCompression i j 𝒜))
      ≤ #(coordCompression i j (∂ 𝒜)) := Finset.card_le_card
          (shadow_coordCompression_subset_coordCompression_shadow i j 𝒜)
    _ = #(∂ 𝒜) := card_coordCompression i j (∂ 𝒜)

section Fintype

variable [Fintype α]

/-- Coordinate compression commutes with taking complements of sets, after swapping the coordinate
direction. -/
theorem coordCompress_compl (i j : α) (a : Finset α) :
    UV.compress ({i} : Finset α) ({j} : Finset α) aᶜ =
      (UV.compress ({j} : Finset α) ({i} : Finset α) a)ᶜ := by
  by_cases hij : i = j
  · subst hij
    simp [UV.compress]
  · by_cases hi : i ∈ a
    · by_cases hj : j ∈ a
      · simp [UV.compress, hi, hj]
      · ext x
        by_cases hxj : x = j <;> by_cases hxi : x = i <;>
          simp [UV.compress, hi, hj, hxj, hxi, hij, Ne.symm hij]
    · by_cases hj : j ∈ a
      · simp [UV.compress, hi, hj]
      · simp [UV.compress, hi, hj]

/-- Family-level complement transport for coordinate compression. -/
theorem coordCompression_compls (i j : α) (𝒜 : Finset (Finset α)) :
    coordCompression i j 𝒜ᶜˢ = (coordCompression j i 𝒜)ᶜˢ := by
  ext s
  rw [Finset.mem_compls]
  constructor
  · intro hs
    rw [coordCompression, uvCompression, UV.mem_compression] at hs ⊢
    rcases hs with (⟨hsA, hcsA⟩ | ⟨hsA, b, hbA, hcb⟩)
    · exact Or.inl ⟨by simpa using hsA, by simpa [coordCompress_compl] using hcsA⟩
    · refine Or.inr ⟨by simpa using hsA, bᶜ, by simpa using hbA, ?_⟩
      simpa [coordCompress_compl] using congrArg Compl.compl hcb
  · intro hs
    rw [coordCompression, uvCompression, UV.mem_compression] at hs ⊢
    rcases hs with (⟨hsA, hcsA⟩ | ⟨hsA, b, hbA, hcb⟩)
    · exact Or.inl ⟨by simpa using hsA, by simpa [coordCompress_compl] using hcsA⟩
    · refine Or.inr ⟨by simpa using hsA, bᶜ, by simpa using hbA, ?_⟩
      simpa [coordCompress_compl] using congrArg Compl.compl hcb

/-- Coordinate compression does not enlarge the upper shadow. -/
theorem upShadow_coordCompression_subset_coordCompression_upShadow
    (i j : α) (𝒜 : Finset (Finset α)) :
    ∂⁺ (coordCompression i j 𝒜) ⊆ coordCompression i j (∂⁺ 𝒜) := by
  have h :=
    shadow_coordCompression_subset_coordCompression_shadow (i := j) (j := i) (𝒜 := 𝒜ᶜˢ)
  have h' : (∂⁺ (coordCompression i j 𝒜))ᶜˢ ⊆ (coordCompression i j (∂⁺ 𝒜))ᶜˢ := by
    simpa [coordCompression_compls] using h
  exact Finset.compls_subset_compls.mp h'

/-- A new positive-boundary point created by coordinate compression in the `10` sector maps,
under `swapCoord`, to a positive-boundary point that disappears after compression. -/
theorem swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∈ s) (hj : j ∉ s)
    (hs : s ∈ positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜) :
    swapCoord i j s ∈ positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜) := by
  rcases mem_sdiff.mp hs with ⟨hsPosC, hsNotPosA⟩
  rcases (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hsPosC) with ⟨hsUpC, hsNotC⟩
  have hsNotComp : ¬ (s ∈ 𝒜 ∨ swapCoord i j s ∈ 𝒜) := by
    simpa [coordCompression_mem_left_iff hi hj] using hsNotC
  have hsNotA : s ∉ 𝒜 := fun hsA => hsNotComp (Or.inl hsA)
  have hswapNotA : swapCoord i j s ∉ 𝒜 := fun hswapA => hsNotComp (Or.inr hswapA)
  have hsNotUpA : s ∉ ∂⁺ 𝒜 := by
    intro hsUpA
    exact hsNotPosA <|
      (mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hsUpA, hsNotA⟩
  have hsCompUp : s ∈ coordCompression i j (∂⁺ 𝒜) :=
    upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜 hsUpC
  have hswapUpA : swapCoord i j s ∈ ∂⁺ 𝒜 := by
    rcases (coordCompression_mem_left_iff hi hj).mp hsCompUp with hsUpA | hswapUpA
    · exact (hsNotUpA hsUpA).elim
    · exact hswapUpA
  have hswapNotPosC : swapCoord i j s ∉ positiveBoundary (coordCompression i j 𝒜) := by
    intro hswapPosC
    have hswapUpC : swapCoord i j s ∈ ∂⁺ (coordCompression i j 𝒜) :=
      (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hswapPosC).1
    have hswapCompUp : swapCoord i j s ∈ coordCompression i j (∂⁺ 𝒜) :=
      upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜 hswapUpC
    have hsUpA : s ∈ ∂⁺ 𝒜 := by
      have hpair :=
        (coordCompression_mem_right_iff
          (not_mem_swapCoord_left_of_mem_left hi hj)
          (mem_swapCoord_right_of_mem_left hi hj)).mp hswapCompUp
      simpa [swapCoord_swapCoord_of_mem_left hi hj] using hpair.2
    exact hsNotUpA hsUpA
  exact mem_sdiff.mpr
    ⟨(mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hswapUpA, hswapNotA⟩, hswapNotPosC⟩

theorem swapCoord_mapsTo_positiveBoundary_sdiff_left_to_right
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.MapsTo (swapCoord i j)
      ↑((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
        fun s => i ∈ s ∧ j ∉ s)
      ↑((positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)).filter
        fun s => i ∉ s ∧ j ∈ s) := by
  intro s hs
  rcases mem_filter.mp hs with ⟨hsDiff, hsector⟩
  rcases hsector with ⟨hi, hj⟩
  refine mem_filter.mpr ⟨?_, ?_⟩
  · exact swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff hi hj hsDiff
  · exact ⟨not_mem_swapCoord_left_of_mem_left hi hj, mem_swapCoord_right_of_mem_left hi hj⟩

theorem swapCoord_injOn_positiveBoundary_sdiff_left
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (swapCoord i j)
      ↑((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
        fun s => i ∈ s ∧ j ∉ s) := by
  intro s hs t ht hEq
  rcases (mem_filter.mp hs).2 with ⟨hiS, hjS⟩
  rcases (mem_filter.mp ht).2 with ⟨hiT, hjT⟩
  calc
    s = swapCoord i j (swapCoord i j s) := by
      symm
      exact swapCoord_swapCoord_of_mem_left hiS hjS
    _ = swapCoord i j (swapCoord i j t) := by simpa [hEq]
    _ = t := swapCoord_swapCoord_of_mem_left hiT hjT

theorem card_positiveBoundary_sdiff_left_sector_le_right_sector
    (i j : α) (𝒜 : Finset (Finset α)) :
    #((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
      fun s => i ∈ s ∧ j ∉ s)
      ≤ #((positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)).filter
        fun s => i ∉ s ∧ j ∈ s) := by
  exact Finset.card_le_card_of_injOn (swapCoord i j)
    (swapCoord_mapsTo_positiveBoundary_sdiff_left_to_right i j 𝒜)
    (swapCoord_injOn_positiveBoundary_sdiff_left i j 𝒜)

theorem not_mem_positiveBoundary_sdiff_of_mem_both
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∈ s) (hj : j ∈ s) :
    s ∉ positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜 := by
  intro hs
  rcases mem_sdiff.mp hs with ⟨hsPosC, hsNotPosA⟩
  rcases (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hsPosC) with ⟨hsUpC, hsNotC⟩
  have hsUpA : s ∈ ∂⁺ 𝒜 := by
    have hsCompUp := upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜 hsUpC
    exact (coordCompression_mem_both_iff hi hj).mp hsCompUp
  have hsNotA : s ∉ 𝒜 := by
    intro hsA
    exact hsNotC ((coordCompression_mem_both_iff hi hj).2 hsA)
  exact hsNotPosA ((mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hsUpA, hsNotA⟩)

theorem not_mem_positiveBoundary_sdiff_of_mem_neither
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∉ s) (hj : j ∉ s) :
    s ∉ positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜 := by
  intro hs
  rcases mem_sdiff.mp hs with ⟨hsPosC, hsNotPosA⟩
  rcases (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hsPosC) with ⟨hsUpC, hsNotC⟩
  have hsUpA : s ∈ ∂⁺ 𝒜 := by
    have hsCompUp := upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜 hsUpC
    exact (coordCompression_mem_neither_iff hi hj).mp hsCompUp
  have hsNotA : s ∉ 𝒜 := by
    intro hsA
    exact hsNotC ((coordCompression_mem_neither_iff hi hj).2 hsA)
  exact hsNotPosA ((mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hsUpA, hsNotA⟩)

theorem swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff_right
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hi : i ∉ s) (hj : j ∈ s)
    (hs : s ∈ positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜) :
    swapCoord i j s ∈ positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜) := by
  rcases mem_sdiff.mp hs with ⟨hsPosC, hsNotPosA⟩
  rcases (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hsPosC) with ⟨hsUpC, hsNotC⟩
  have hsCompUp : s ∈ coordCompression i j (∂⁺ 𝒜) :=
    upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜 hsUpC
  have hsUpA : s ∈ ∂⁺ 𝒜 :=
    (coordCompression_mem_right_iff hi hj).mp hsCompUp |>.1
  have hswapUpA : swapCoord i j s ∈ ∂⁺ 𝒜 :=
    (coordCompression_mem_right_iff hi hj).mp hsCompUp |>.2
  have hswapNotA : swapCoord i j s ∉ 𝒜 := by
    intro hswapA
    by_cases hsA : s ∈ 𝒜
    · exact hsNotC ((coordCompression_mem_right_iff hi hj).2 ⟨hsA, hswapA⟩)
    · exact hsNotPosA ((mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hsUpA, hsA⟩)
  have hswapNotPosC : swapCoord i j s ∉ positiveBoundary (coordCompression i j 𝒜) := by
    intro hswapPosC
    have hswapNotC : swapCoord i j s ∉ coordCompression i j 𝒜 :=
      (mem_positiveBoundary_iff_mem_upShadow_and_not_mem.mp hswapPosC).2
    have hsNotA : s ∉ 𝒜 := by
      have hswapNotComp : ¬ (swapCoord i j s ∈ 𝒜 ∨ s ∈ 𝒜) := by
        intro h
        exact hswapNotC <|
          (coordCompression_mem_left_iff
            (mem_swapCoord_left_of_mem_right hi hj)
            (not_mem_swapCoord_right_of_mem_right hi hj)).2 <|
              by simpa [swapCoord_swapCoord_of_mem_right hi hj] using h
      exact fun hsA => hswapNotComp (Or.inr hsA)
    exact hsNotPosA ((mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hsUpA, hsNotA⟩)
  exact mem_sdiff.mpr
    ⟨(mem_positiveBoundary_iff_mem_upShadow_and_not_mem).2 ⟨hswapUpA, hswapNotA⟩, hswapNotPosC⟩

theorem swapCoord_mapsTo_positiveBoundary_sdiff_right_to_left
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.MapsTo (swapCoord i j)
      ↑((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
        fun s => i ∉ s ∧ j ∈ s)
      ↑((positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)).filter
        fun s => i ∈ s ∧ j ∉ s) := by
  intro s hs
  rcases mem_filter.mp hs with ⟨hsDiff, hsector⟩
  rcases hsector with ⟨hi, hj⟩
  refine mem_filter.mpr ⟨?_, ?_⟩
  · exact swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff_right hi hj hsDiff
  · exact ⟨mem_swapCoord_left_of_mem_right hi hj, not_mem_swapCoord_right_of_mem_right hi hj⟩

theorem swapCoord_injOn_positiveBoundary_sdiff_right
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (swapCoord i j)
      ↑((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
        fun s => i ∉ s ∧ j ∈ s) := by
  intro s hs t ht hEq
  rcases (mem_filter.mp hs).2 with ⟨hiS, hjS⟩
  rcases (mem_filter.mp ht).2 with ⟨hiT, hjT⟩
  calc
    s = swapCoord i j (swapCoord i j s) := by
      symm
      exact swapCoord_swapCoord_of_mem_right hiS hjS
    _ = swapCoord i j (swapCoord i j t) := by simpa [hEq]
    _ = t := swapCoord_swapCoord_of_mem_right hiT hjT

theorem card_positiveBoundary_sdiff_right_sector_le_left_sector
    (i j : α) (𝒜 : Finset (Finset α)) :
    #((positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜).filter
      fun s => i ∉ s ∧ j ∈ s)
      ≤ #((positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)).filter
        fun s => i ∈ s ∧ j ∉ s) := by
  exact Finset.card_le_card_of_injOn (swapCoord i j)
    (swapCoord_mapsTo_positiveBoundary_sdiff_right_to_left i j 𝒜)
    (swapCoord_injOn_positiveBoundary_sdiff_right i j 𝒜)

theorem mem_sector_left_or_right_of_mem_positiveBoundary_sdiff
    {i j : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∈ positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜) :
    (i ∈ s ∧ j ∉ s) ∨ (i ∉ s ∧ j ∈ s) := by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · exact (not_mem_positiveBoundary_sdiff_of_mem_both hi hj hs).elim
    · exact Or.inl ⟨hi, hj⟩
  · by_cases hj : j ∈ s
    · exact Or.inr ⟨hi, hj⟩
    · exact (not_mem_positiveBoundary_sdiff_of_mem_neither hi hj hs).elim

theorem swapCoord_mapsTo_positiveBoundary_sdiff
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.MapsTo (swapCoord i j)
      ↑(positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜)
      ↑(positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)) := by
  intro s hs
  rcases mem_sector_left_or_right_of_mem_positiveBoundary_sdiff hs with hleft | hright
  · exact swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff hleft.1 hleft.2 hs
  · exact swapCoord_mem_positiveBoundary_sdiff_of_mem_positiveBoundary_sdiff_right hright.1 hright.2 hs

theorem swapCoord_injOn_positiveBoundary_sdiff
    (i j : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (swapCoord i j)
      ↑(positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜) := by
  intro s hs t ht hEq
  rcases mem_sector_left_or_right_of_mem_positiveBoundary_sdiff hs with hsleft | hsright
  · rcases mem_sector_left_or_right_of_mem_positiveBoundary_sdiff ht with htleft | htright
    · calc
        s = swapCoord i j (swapCoord i j s) := by
          symm
          exact swapCoord_swapCoord_of_mem_left hsleft.1 hsleft.2
        _ = swapCoord i j (swapCoord i j t) := by simpa [hEq]
        _ = t := swapCoord_swapCoord_of_mem_left htleft.1 htleft.2
    · have : i ∉ swapCoord i j s := by
        exact not_mem_swapCoord_left_of_mem_left hsleft.1 hsleft.2
      have hin : i ∈ swapCoord i j t := by
        exact mem_swapCoord_left_of_mem_right htright.1 htright.2
      have hin' : i ∈ swapCoord i j s := by simpa [hEq] using hin
      exact (‹i ∉ swapCoord i j s› hin').elim
  · rcases mem_sector_left_or_right_of_mem_positiveBoundary_sdiff ht with htleft | htright
    · have hin : i ∈ swapCoord i j s := by
        exact mem_swapCoord_left_of_mem_right hsright.1 hsright.2
      have hnot : i ∉ swapCoord i j t := by
        exact not_mem_swapCoord_left_of_mem_left htleft.1 htleft.2
      have hin' : i ∈ swapCoord i j t := by simpa [hEq] using hin
      exact (hnot hin').elim
    · calc
        s = swapCoord i j (swapCoord i j s) := by
          symm
          exact swapCoord_swapCoord_of_mem_right hsright.1 hsright.2
        _ = swapCoord i j (swapCoord i j t) := by simpa [hEq]
        _ = t := swapCoord_swapCoord_of_mem_right htright.1 htright.2

theorem card_positiveBoundary_sdiff_le
    (i j : α) (𝒜 : Finset (Finset α)) :
    #(positiveBoundary (coordCompression i j 𝒜) \ positiveBoundary 𝒜)
      ≤ #(positiveBoundary 𝒜 \ positiveBoundary (coordCompression i j 𝒜)) := by
  exact Finset.card_le_card_of_injOn (swapCoord i j)
    (swapCoord_mapsTo_positiveBoundary_sdiff i j 𝒜)
    (swapCoord_injOn_positiveBoundary_sdiff i j 𝒜)

theorem card_positiveBoundary_coordCompression_le
    (i j : α) (𝒜 : Finset (Finset α)) :
    #(positiveBoundary (coordCompression i j 𝒜)) ≤ #(positiveBoundary 𝒜) := by
  exact (Finset.card_sdiff_le_card_sdiff_iff).mp
    (card_positiveBoundary_sdiff_le i j 𝒜)

theorem card_upShadow_coordCompression_le (i j : α) (𝒜 : Finset (Finset α)) :
    #(∂⁺ (coordCompression i j 𝒜)) ≤ #(∂⁺ 𝒜) := by
  calc
    #(∂⁺ (coordCompression i j 𝒜))
      ≤ #(coordCompression i j (∂⁺ 𝒜)) := Finset.card_le_card
          (upShadow_coordCompression_subset_coordCompression_upShadow i j 𝒜)
    _ = #(∂⁺ 𝒜) := card_coordCompression i j (∂⁺ 𝒜)

end Fintype

end Erdos1
