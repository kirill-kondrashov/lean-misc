import ErdosProblems.Problem1CubeOddExtremizer

open Finset
open scoped FinsetFamily

namespace Erdos1

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
Finite Alexander dual of a cube family: a set belongs to the dual exactly when its complement does
not belong to the original family.

For a down-set family, this is the simplicial Alexander dual of the associated simplicial complex.
-/
def alexanderDual (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  ((Finset.univ.powerset \ 𝒜)ᶜˢ)

/-- The maximal faces (facets) of a family. -/
def maximalInside (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter fun s => ∀ ⦃t : Finset α⦄, s ⊂ t → t ∉ 𝒜

@[simp]
theorem mem_maximalInside {𝒜 : Finset (Finset α)} {s : Finset α} :
    s ∈ maximalInside 𝒜 ↔ s ∈ 𝒜 ∧ ∀ ⦃t : Finset α⦄, s ⊂ t → t ∉ 𝒜 := by
  simp [maximalInside]

theorem isAntichain_maximalInside (𝒜 : Finset (Finset α)) :
    IsAntichain (· ⊆ ·) (maximalInside 𝒜 : Set (Finset α)) := by
  intro s hs t ht hne hst
  have htIn : t ∈ 𝒜 := (mem_maximalInside.mp ht).1
  have htNot : t ∉ 𝒜 :=
    (mem_maximalInside.mp hs).2 (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
  exact htNot htIn

@[simp]
theorem mem_alexanderDual {𝒜 : Finset (Finset α)} {s : Finset α} :
    s ∈ alexanderDual 𝒜 ↔ sᶜ ∉ 𝒜 := by
  simp [alexanderDual]

@[simp]
theorem alexanderDual_involutive (𝒜 : Finset (Finset α)) :
    alexanderDual (alexanderDual 𝒜) = 𝒜 := by
  ext s
  simp [alexanderDual]

theorem isDownSetFamily_alexanderDual {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (alexanderDual 𝒜) := by
  intro s t hts hs
  change s ∈ alexanderDual 𝒜 at hs
  change t ∈ alexanderDual 𝒜
  rw [mem_alexanderDual] at hs ⊢
  intro ht
  exact hs (h𝒜 (by simpa using (Finset.compl_subset_compl.2 hts)) ht)

@[simp]
theorem card_alexanderDual (𝒜 : Finset (Finset α)) :
    #(alexanderDual 𝒜) = 2 ^ Fintype.card α - #𝒜 := by
  have hsub : 𝒜 ⊆ (Finset.univ.powerset : Finset (Finset α)) := by
    intro s hs
    exact Finset.mem_powerset.mpr (Finset.subset_univ s)
  calc
    #(alexanderDual 𝒜) = #(((Finset.univ.powerset : Finset (Finset α)) \ 𝒜)ᶜˢ) := by
      rfl
    _ = #((Finset.univ.powerset : Finset (Finset α)) \ 𝒜) := by
      rw [Finset.card_compls]
    _ = #((Finset.univ.powerset : Finset (Finset α))) - #𝒜 := by
      rw [Finset.card_sdiff_of_subset hsub]
    _ = 2 ^ #(Finset.univ : Finset α) - #𝒜 := by
      rw [Finset.card_powerset]
    _ = 2 ^ Fintype.card α - #𝒜 := by
      simp

theorem alexanderDual_oddLowerHalfFamily (m : ℕ) :
    alexanderDual (oddLowerHalfFamily m) = oddLowerHalfFamily m := by
  ext s
  rw [mem_alexanderDual, mem_oddLowerHalfFamily, mem_oddLowerHalfFamily]
  have hcompl : sᶜ.card = 2 * m + 1 - s.card := by
    simpa using Finset.card_compl s
  omega

theorem maximalInside_alexanderDual_eq_compls_minimalOutside (𝒜 : Finset (Finset α)) :
    maximalInside (alexanderDual 𝒜) = (minimalOutside 𝒜)ᶜˢ := by
  ext s
  rw [Finset.mem_compls, mem_maximalInside, mem_minimalOutside, mem_alexanderDual]
  constructor
  · rintro ⟨hsDual, hsMax⟩
    refine ⟨hsDual, ?_⟩
    intro t ht
    have hsst : s ⊂ tᶜ := by
      simpa using (Finset.compl_ssubset_compl).2 ht
    have htNotDual : tᶜ ∉ alexanderDual 𝒜 := hsMax hsst
    simpa [mem_alexanderDual] using htNotDual
  · rintro ⟨hsNot, hsMin⟩
    refine ⟨by simpa [mem_alexanderDual] using hsNot, ?_⟩
    intro t hst
    have htss : tᶜ ⊂ sᶜ := by
      simpa using (Finset.compl_ssubset_compl).2 hst
    have htComplMem : tᶜ ∈ 𝒜 := hsMin htss
    simpa [mem_alexanderDual] using htComplMem

theorem minimalOutside_eq_compls_maximalInside_alexanderDual (𝒜 : Finset (Finset α)) :
    minimalOutside 𝒜 = (maximalInside (alexanderDual 𝒜))ᶜˢ := by
  have h := maximalInside_alexanderDual_eq_compls_minimalOutside (𝒜 := 𝒜)
  simpa using (congrArg Finset.compls h).symm

@[simp]
theorem card_maximalInside_alexanderDual (𝒜 : Finset (Finset α)) :
    #(maximalInside (alexanderDual 𝒜)) = #(minimalOutside 𝒜) := by
  rw [maximalInside_alexanderDual_eq_compls_minimalOutside, Finset.card_compls]

theorem compls_oddMiddleLayer_eq_powersetCard (m : ℕ) :
    (oddMiddleLayer m)ᶜˢ = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard m := by
  ext s
  rw [Finset.mem_compls, mem_oddMiddleLayer, Finset.mem_powersetCard]
  constructor
  · intro hs
    refine ⟨Finset.subset_univ _, ?_⟩
    have hcompl : sᶜ.card = 2 * m + 1 - s.card := by
      simpa using Finset.card_compl s
    have hcard : sᶜ.card = m + 1 := hs
    omega
  · rintro ⟨-, hsCard⟩
    have hcompl : sᶜ.card = 2 * m + 1 - s.card := by
      simpa using Finset.card_compl s
    omega

theorem maximalInside_oddLowerHalfFamily (m : ℕ) :
    maximalInside (oddLowerHalfFamily m) =
      (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard m := by
  calc
    maximalInside (oddLowerHalfFamily m)
      = maximalInside (alexanderDual (oddLowerHalfFamily m)) := by
          rw [alexanderDual_oddLowerHalfFamily]
    _ = (minimalOutside (oddLowerHalfFamily m))ᶜˢ :=
          maximalInside_alexanderDual_eq_compls_minimalOutside _
    _ = (oddMiddleLayer m)ᶜˢ := by
          rw [minimalOutside_oddLowerHalfFamily]
    _ = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard m :=
          compls_oddMiddleLayer_eq_powersetCard m

theorem card_maximalInside_oddLowerHalfFamily (m : ℕ) :
    #(maximalInside (oddLowerHalfFamily m)) = Nat.choose (2 * m + 1) m := by
  rw [maximalInside_oddLowerHalfFamily]
  simp

end Erdos1
