import ErdosProblems.Problem1LowerExactCore
import ErdosProblems.Problem1CubeDownset

open Finset

namespace Erdos1

/-- The coordinate embedding from the subtype `A` back into naturals. -/
abbrev natSubtypeEmb (A : Finset ℕ) : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩

/-- The strict lower half of the subset-sum cube, viewed as a family on the subtype `A`. -/
def negativeHalfFamilySubcubeNat (A : Finset ℕ) : Finset (Finset A) :=
  (Finset.univ : Finset A).powerset.filter fun s => 2 * (∑ a ∈ s, (a : ℕ)) < A.sum id

@[simp]
theorem mem_negativeHalfFamilySubcubeNat {A : Finset ℕ} {s : Finset A} :
    s ∈ negativeHalfFamilySubcubeNat A ↔ 2 * (∑ a ∈ s, (a : ℕ)) < A.sum id := by
  rw [negativeHalfFamilySubcubeNat, Finset.mem_filter]
  constructor
  · intro hs
    exact hs.2
  · intro hs
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ s), hs⟩

theorem isDownSetFamily_negativeHalfFamilySubcubeNat (A : Finset ℕ) :
    IsDownSetFamily (negativeHalfFamilySubcubeNat A) := by
  intro s t hts hs
  change t ∈ negativeHalfFamilySubcubeNat A
  have hs' : s ∈ negativeHalfFamilySubcubeNat A := by
    simpa using hs
  rw [mem_negativeHalfFamilySubcubeNat] at hs' ⊢
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset hts))
    hs'

/-- Lift a subset `S ⊆ A` to a subset of the subtype `A`. -/
abbrev liftFinsetToSubtypeEmb {A S : Finset ℕ} (hS : S ⊆ A) : {x // x ∈ S} ↪ A :=
  ⟨fun x => ⟨x.1, hS x.2⟩, fun _ _ hxy => by
    exact Subtype.ext (congrArg (fun z : A => (z : ℕ)) hxy)⟩

def liftFinsetToSubtype (A S : Finset ℕ) (hS : S ⊆ A) : Finset A :=
  S.attach.map (liftFinsetToSubtypeEmb hS)

@[simp]
theorem map_liftFinsetToSubtype (A S : Finset ℕ) (hS : S ⊆ A) :
    (liftFinsetToSubtype A S hS).map (natSubtypeEmb A) = S := by
  have hcomp :
      (liftFinsetToSubtypeEmb hS).trans (natSubtypeEmb A) =
        Function.Embedding.subtype fun x => x ∈ S := by
    ext x
    rfl
  rw [liftFinsetToSubtype, Finset.map_map, hcomp, Finset.attach_map_val]

theorem map_natSubtypeEmb_subset {A : Finset ℕ} (s : Finset A) :
    s.map (natSubtypeEmb A) ⊆ A := by
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
  exact a.2

theorem sum_map_natSubtypeEmb {A : Finset ℕ} (s : Finset A) :
    ∑ a ∈ s.map (natSubtypeEmb A), a = ∑ a ∈ s, (a : ℕ) := by
  rw [Finset.sum_map]
  simp [natSubtypeEmb]

theorem sum_liftFinsetToSubtype (A S : Finset ℕ) (hS : S ⊆ A) :
    ∑ a ∈ liftFinsetToSubtype A S hS, (a : ℕ) = ∑ a ∈ S, a := by
  calc
    ∑ a ∈ liftFinsetToSubtype A S hS, (a : ℕ)
      = ∑ a ∈ (liftFinsetToSubtype A S hS).map (natSubtypeEmb A), a := by
          symm
          exact sum_map_natSubtypeEmb (liftFinsetToSubtype A S hS)
    _ = ∑ a ∈ S, a := by rw [map_liftFinsetToSubtype A S hS]

theorem mem_liftFinsetToSubtype {A S : Finset ℕ} (hS : S ⊆ A) {a : ℕ} (ha : a ∈ S) :
    (⟨a, hS ha⟩ : A) ∈ liftFinsetToSubtype A S hS := by
  rw [liftFinsetToSubtype]
  exact Finset.mem_map.mpr ⟨⟨a, ha⟩, by simp, rfl⟩

theorem image_positiveBoundary_map_natSubtypeEmb (A : Finset ℕ) (𝒜 : Finset (Finset A)) :
    (positiveBoundary 𝒜).image (fun s => s.map (natSubtypeEmb A)) =
      positiveVertexBoundaryNat A (𝒜.image fun s => s.map (natSubtypeEmb A)) := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨s, hs, rfl⟩
    rw [mem_positiveBoundary] at hs
    rcases hs with ⟨hsNotMem, a, ha, hsErase⟩
    rw [mem_positiveVertexBoundaryNat]
    refine ⟨map_natSubtypeEmb_subset s, ?_, a, ?_, ?_⟩
    · intro hsImage
      rcases Finset.mem_image.mp hsImage with ⟨t, ht, htEq⟩
      exact hsNotMem ((Finset.map_injective (natSubtypeEmb A)) htEq ▸ ht)
    · exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    · refine Finset.mem_image.mpr ⟨s.erase a, hsErase, ?_⟩
      rw [Finset.map_erase]
      rfl
  · intro hS
    rw [mem_positiveVertexBoundaryNat] at hS
    rcases hS with ⟨hSA, hNotImage, a, haS, hEraseImage⟩
    let s : Finset A := liftFinsetToSubtype A S hSA
    let aA : A := ⟨a, hSA haS⟩
    have hsMap : s.map (natSubtypeEmb A) = S := by
      unfold s
      exact map_liftFinsetToSubtype A S hSA
    have haA : aA ∈ s := by
      unfold s aA
      exact mem_liftFinsetToSubtype hSA haS
    have hsNotMem : s ∉ 𝒜 := by
      intro hsMem
      exact hNotImage (Finset.mem_image.mpr ⟨s, hsMem, hsMap⟩)
    rcases Finset.mem_image.mp hEraseImage with ⟨t, ht, htEq⟩
    have hsEraseMap : (s.erase aA).map (natSubtypeEmb A) = S.erase a := by
      calc
        (s.erase aA).map (natSubtypeEmb A)
          = (s.map (natSubtypeEmb A)).erase a := by
              rw [Finset.map_erase]
              rfl
        _ = S.erase a := by rw [hsMap]
    have htEq' : t = s.erase aA := by
      exact (Finset.map_injective (natSubtypeEmb A)) (htEq.trans hsEraseMap.symm)
    have hsEraseMem : s.erase aA ∈ 𝒜 := by
      simpa [htEq'] using ht
    refine Finset.mem_image.mpr ⟨s, ?_, hsMap⟩
    rw [mem_positiveBoundary]
    exact ⟨hsNotMem, aA, haA, hsEraseMem⟩

theorem image_negativeHalfFamilySubcubeNat (A : Finset ℕ) :
    (negativeHalfFamilySubcubeNat A).image (fun s => s.map (natSubtypeEmb A)) =
      negativeHalfFamilyNat A := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨s, hs, rfl⟩
    rw [mem_negativeHalfFamilySubcubeNat] at hs
    rw [mem_negativeHalfFamilyNat]
    refine ⟨map_natSubtypeEmb_subset s, ?_⟩
    simpa [sum_map_natSubtypeEmb] using hs
  · intro hS
    rw [mem_negativeHalfFamilyNat] at hS
    rcases hS with ⟨hSA, hs⟩
    refine Finset.mem_image.mpr ⟨liftFinsetToSubtype A S hSA, ?_, map_liftFinsetToSubtype A S hSA⟩
    rw [mem_negativeHalfFamilySubcubeNat]
    simpa [sum_liftFinsetToSubtype] using hs

theorem card_negativeHalfFamilySubcubeNat (A : Finset ℕ) :
    #(negativeHalfFamilySubcubeNat A) = #(negativeHalfFamilyNat A) := by
  calc
    #(negativeHalfFamilySubcubeNat A)
      = #((negativeHalfFamilySubcubeNat A).image fun s => s.map (natSubtypeEmb A)) := by
          symm
          exact Finset.card_image_of_injOn (by
            intro s hs t ht hEq
            exact (Finset.map_injective (natSubtypeEmb A)) hEq)
    _ = #(negativeHalfFamilyNat A) := by rw [image_negativeHalfFamilySubcubeNat]

theorem image_positiveBoundary_negativeHalfFamilySubcubeNat (A : Finset ℕ) :
    (positiveBoundary (negativeHalfFamilySubcubeNat A)).image (fun s => s.map (natSubtypeEmb A)) =
      positiveVertexBoundaryNat A (negativeHalfFamilyNat A) := by
  rw [image_positiveBoundary_map_natSubtypeEmb, image_negativeHalfFamilySubcubeNat]

theorem card_positiveBoundary_negativeHalfFamilySubcubeNat (A : Finset ℕ) :
    #(positiveBoundary (negativeHalfFamilySubcubeNat A)) =
      #(positiveVertexBoundaryNat A (negativeHalfFamilyNat A)) := by
  calc
    #(positiveBoundary (negativeHalfFamilySubcubeNat A))
      = #((positiveBoundary (negativeHalfFamilySubcubeNat A)).image
          fun s => s.map (natSubtypeEmb A)) := by
            symm
            exact Finset.card_image_of_injOn (by
              intro s hs t ht hEq
              exact (Finset.map_injective (natSubtypeEmb A)) hEq)
    _ = #(positiveVertexBoundaryNat A (negativeHalfFamilyNat A)) := by
      rw [image_positiveBoundary_negativeHalfFamilySubcubeNat]

theorem empty_mem_negativeHalfFamilySubcubeNat {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    ∅ ∈ negativeHalfFamilySubcubeNat A := by
  rw [mem_negativeHalfFamilySubcubeNat]
  have hsumPos : 0 < A.sum id :=
    Finset.sum_pos (fun a ha => (Finset.mem_Icc.mp (h.1 ha)).1) hA
  simpa using hsumPos

theorem negativeHalfFamilySubcubeNat_nonempty {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    (negativeHalfFamilySubcubeNat A).Nonempty :=
  ⟨∅, empty_mem_negativeHalfFamilySubcubeNat h hA⟩

theorem card_negativeHalfFamilySubcubeNat_eq_half_cube {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    #(negativeHalfFamilySubcubeNat A) = 2 ^ (Fintype.card A - 1) := by
  rw [card_negativeHalfFamilySubcubeNat]
  simpa [Fintype.card_coe] using (negativeHalfFamilyNat_card (A := A) (N := N) h hA)

theorem image_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    (positiveBoundary (negativeHalfFamilySubcubeNat A)).image (fun s => s.map (natSubtypeEmb A)) =
      positiveBoundaryFamilyNat A := by
  rw [image_positiveBoundary_negativeHalfFamilySubcubeNat, ← positiveBoundaryFamilyNat_eq_positiveBoundary h hA]

theorem card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    #(positiveBoundary (negativeHalfFamilySubcubeNat A)) = #(positiveBoundaryFamilyNat A) := by
  rw [card_positiveBoundary_negativeHalfFamilySubcubeNat, ← positiveBoundaryFamilyNat_eq_positiveBoundary h hA]

theorem card_positiveBoundaryFamilyNat_ge_of_subcube_halfCube_lower
    {A : Finset ℕ} {N : ℕ}
    (hCube :
      (negativeHalfFamilySubcubeNat A).Nonempty →
        IsDownSetFamily (negativeHalfFamilySubcubeNat A) →
        #(negativeHalfFamilySubcubeNat A) = 2 ^ (Fintype.card A - 1) →
          Nat.choose (Fintype.card A) (Fintype.card A / 2) ≤
            #(positiveBoundary (negativeHalfFamilySubcubeNat A)))
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ #(positiveBoundaryFamilyNat A) := by
  have hBoundary :
      Nat.choose (Fintype.card A) (Fintype.card A / 2) ≤
        #(positiveBoundary (negativeHalfFamilySubcubeNat A)) := by
    exact hCube
      (negativeHalfFamilySubcubeNat_nonempty h hA)
      (isDownSetFamily_negativeHalfFamilySubcubeNat A)
      (card_negativeHalfFamilySubcubeNat_eq_half_cube h hA)
  simpa [Fintype.card_coe, card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat h hA] using
    hBoundary

end Erdos1
