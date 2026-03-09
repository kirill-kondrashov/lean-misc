import ErdosProblems.Problem1CubeNatBridge
import ErdosProblems.Problem1CubeEvenExtremizer
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Sum

open Finset
open scoped BigOperators Finset FinsetFamily

namespace Erdos1

variable {α : Type} [DecidableEq α] [Fintype α]

/--
The sharp half-cube boundary lower statement on the Boolean cube.

This is the exact cube theorem whose proof would remove the final frontier assumption in the exact
integer route for Erdős Problem #1.
-/
def HalfCubeBoundaryLowerStatement : Prop :=
  ∀ {α : Type} [DecidableEq α] [Fintype α] {𝒟 : Finset (Finset α)},
    0 < Fintype.card α →
    𝒟.Nonempty →
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (Fintype.card α - 1) →
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ (positiveBoundary 𝒟).card

/--
Remaining frontier input: the sharp half-cube boundary theorem on the Boolean cube.

Replacing this axiom with a proof removes the final exact-theorem blocker.
-/
axiom halfCubeBoundaryLower : HalfCubeBoundaryLowerStatement

/-- Remaining odd-dimensional paired frontier suggested by the section recursion for even ambient
dimension: nested down-sets whose cardinalities are symmetrically placed around half should have
combined boundary at least twice the odd middle binomial. -/
def OddSectionPairBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      2 * Nat.choose (2 * m + 1) m ≤
        (positiveBoundary 𝒩).card + (positiveBoundary ℳ).card

/-- The normalized density of the `r`-slice of a family. -/
def sliceDensity (𝒟 : Finset (Finset α)) (r : ℕ) : ℚ :=
  (#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r

/-- The weighted drop functional on a profile `a : ℕ → ℚ` across the first `n` layers. -/
def weightedDrop (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  Finset.sum (Finset.range n) fun r =>
    (Nat.choose n (r + 1) : ℚ) * (a r - a (r + 1))

/-- The exact upper-shadow gap across the first `n` layers of a family. -/
def upperShadowGap (𝒟 : Finset (Finset α)) : ℕ :=
  Finset.sum (Finset.range (Fintype.card α)) fun r =>
    #(∂⁺ (𝒟 # r)) - #(𝒟 # (r + 1))

/-- The sharper family-level frontier statement: the exact upper-shadow gap of a half-cube down-set
dominates the middle binomial coefficient. -/
def HalfCubeUpperShadowGapLowerStatement : Prop :=
  ∀ {α : Type} [DecidableEq α] [Fintype α] {𝒟 : Finset (Finset α)},
    0 < Fintype.card α →
    𝒟.Nonempty →
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (Fintype.card α - 1) →
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ upperShadowGap 𝒟

omit [Fintype α] in
/-- The shadow of the `(r+1)`-slice of a down-set family lies in its `r`-slice. -/
theorem shadow_slice_succ_subset_slice_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r := by
  intro s hs
  rcases Finset.mem_shadow_iff_insert_mem.mp hs with ⟨a, ha, hsInsert⟩
  rw [Finset.mem_slice] at hsInsert ⊢
  refine ⟨h𝒟 (Finset.subset_insert _ _) hsInsert.1, ?_⟩
  rw [Finset.card_insert_of_notMem ha] at hsInsert
  exact Nat.succ.inj hsInsert.2

/-- Adjacent normalized slice sizes of a down-set are nonincreasing. -/
theorem card_slice_succ_div_choose_le_card_slice_div_choose_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) ≤
      (#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r := by
  have hlym :
      ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) ≤
        (#(∂ (𝒟 # (r + 1))) : ℚ) / Nat.choose (Fintype.card α) r := by
    simpa using
      (Finset.local_lubell_yamamoto_meshalkin_inequality_div
        (𝒜 := 𝒟 # (r + 1)) (r := r + 1) (𝕜 := ℚ) (by simp)
        (Finset.sized_slice (𝒜 := 𝒟) (r := r + 1)))
  have hcard :
      (#(∂ (𝒟 # (r + 1))) : ℚ) ≤ #(𝒟 # r) := by
    exact_mod_cast Finset.card_le_card
      (shadow_slice_succ_subset_slice_of_isDownSetFamily h𝒟 r)
  have hdiv :
      (#(∂ (𝒟 # (r + 1))) : ℚ) / Nat.choose (Fintype.card α) r ≤
        (#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r := by
    exact div_le_div_of_nonneg_right hcard (by positivity)
  exact hlym.trans hdiv

/-- A boundary slice lies in the corresponding outside slice. -/
theorem positiveBoundary_slice_subset_outside_slice
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    ((positiveBoundary 𝒟) # r) ⊆ (((Finset.univ.powerset) \ 𝒟) # r) := by
  intro s hs
  rcases Finset.mem_slice.mp hs with ⟨hsBoundary, hsCard⟩
  rw [Finset.mem_slice, Finset.mem_sdiff]
  exact ⟨⟨Finset.mem_powerset.mpr (Finset.subset_univ s), (mem_positiveBoundary.mp hsBoundary).1⟩, hsCard⟩

/-- For a down-set, every `(r+1)`-set in the family arises from the upper shadow of the `r`-slice. -/
theorem slice_succ_subset_upShadow_slice_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    𝒟 # (r + 1) ⊆ ∂⁺ (𝒟 # r) := by
  intro s hs
  rcases Finset.mem_slice.mp hs with ⟨hs𝒟, hsCard⟩
  have hsCardPos : 0 < s.card := by omega
  rcases Finset.card_pos.mp hsCardPos with ⟨a, ha⟩
  rw [Finset.mem_upShadow_iff_erase_mem]
  refine ⟨a, ha, ?_⟩
  rw [Finset.mem_slice]
  refine ⟨h𝒟 (Finset.erase_subset a s) hs𝒟, ?_⟩
  have hEraseCard : (s.erase a).card + 1 = r + 1 := by
    simpa [hsCard] using Finset.card_erase_add_one ha
  omega

/-- Every boundary `(r+1)`-set already lies in the upper shadow of the `r`-slice. -/
theorem positiveBoundary_slice_succ_subset_upShadow_slice
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    ((positiveBoundary 𝒟) # (r + 1)) ⊆ ∂⁺ (𝒟 # r) := by
  intro s hs
  rcases Finset.mem_slice.mp hs with ⟨hsBoundary, hsCard⟩
  rcases mem_positiveBoundary.mp hsBoundary with ⟨-, a, ha, hsErase⟩
  rw [Finset.mem_upShadow_iff_erase_mem]
  refine ⟨a, ha, ?_⟩
  rw [Finset.mem_slice]
  refine ⟨hsErase, ?_⟩
  have hEraseCard : (s.erase a).card + 1 = r + 1 := by
    simpa [hsCard] using Finset.card_erase_add_one ha
  omega

/-- For a down-set, the upper shadow of the `r`-slice is covered by the next slice and the next
boundary slice. -/
theorem upShadow_slice_subset_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    ∂⁺ (𝒟 # r) ⊆ (𝒟 # (r + 1)) ∪ ((positiveBoundary 𝒟) # (r + 1)) := by
  intro s hs
  rcases Finset.mem_upShadow_iff_erase_mem.mp hs with ⟨a, ha, hsErase⟩
  rcases Finset.mem_slice.mp hsErase with ⟨hs𝒟, hsCard⟩
  have hCardErase : (s.erase a).card + 1 = s.card := by
    simpa using Finset.card_erase_add_one ha
  have hsCard' : s.card = r + 1 := by
    omega
  by_cases hsMem : s ∈ 𝒟
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_slice.mpr ⟨hsMem, hsCard'⟩
  · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_slice.mpr
      ⟨mem_positiveBoundary.mpr ⟨hsMem, a, ha, hs𝒟⟩, hsCard'⟩

/-- For down-sets, the upper shadow of the `r`-slice splits as the next slice plus the next
boundary slice. -/
theorem upShadow_slice_eq_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    ∂⁺ (𝒟 # r) = (𝒟 # (r + 1)) ∪ ((positiveBoundary 𝒟) # (r + 1)) := by
  refine Finset.Subset.antisymm
    (upShadow_slice_subset_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) r) ?_
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact slice_succ_subset_upShadow_slice_of_isDownSetFamily (𝒟 := 𝒟) h𝒟 r hs
  · exact positiveBoundary_slice_succ_subset_upShadow_slice (𝒟 := 𝒟) r hs

/-- The next family slice and the next boundary slice are disjoint. -/
theorem disjoint_slice_succ_positiveBoundary_slice_succ
    (𝒟 : Finset (Finset α)) (r : ℕ) :
    Disjoint (𝒟 # (r + 1)) ((positiveBoundary 𝒟) # (r + 1)) := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs𝒟 hsBoundary
  exact (mem_positiveBoundary.mp (Finset.mem_slice.mp hsBoundary).1).1
    (Finset.mem_slice.mp hs𝒟).1

/-- For down-sets, the upper shadow of the `r`-slice has exact size equal to the next slice plus
the next boundary slice. -/
theorem card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    #(∂⁺ (𝒟 # r)) = #(𝒟 # (r + 1)) + #((positiveBoundary 𝒟) # (r + 1)) := by
  rw [upShadow_slice_eq_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) h𝒟 r,
    Finset.card_union_of_disjoint]
  exact disjoint_slice_succ_positiveBoundary_slice_succ 𝒟 r

/-- The `r`-th outside slice is exactly the `r`-th layer minus the `r`-slice of the family. -/
theorem outside_slice_eq_powersetCard_sdiff_slice
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    (((Finset.univ.powerset) \ 𝒟) # r) = (Finset.powersetCard r Finset.univ) \ (𝒟 # r) := by
  ext s
  rw [Finset.mem_slice, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_powersetCard_univ,
    Finset.mem_slice]
  constructor
  · rintro ⟨⟨-, hsNotMem⟩, hsCard⟩
    refine ⟨hsCard, ?_⟩
    rintro ⟨hsMem, -⟩
    exact hsNotMem hsMem
  · rintro ⟨hsCard, hsNotSlice⟩
    refine ⟨⟨Finset.mem_powerset.mpr (Finset.subset_univ s), ?_⟩, hsCard⟩
    intro hsMem
    exact hsNotSlice ⟨hsMem, hsCard⟩

/-- The cardinality of the outside `r`-slice is the full layer size minus the family `r`-slice. -/
theorem card_outside_slice_eq_choose_sub_card_slice
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    #((((Finset.univ.powerset) \ 𝒟) # r)) = Nat.choose (Fintype.card α) r - #(𝒟 # r) := by
  have hsubset : 𝒟 # r ⊆ Finset.powersetCard r Finset.univ :=
    Set.Sized.subset_powersetCard_univ (Finset.sized_slice (𝒜 := 𝒟) (r := r))
  rw [outside_slice_eq_powersetCard_sdiff_slice, Finset.card_sdiff_of_subset hsubset,
    Finset.card_powersetCard]
  rw [Fintype.card]

/-- Outside slice plus family slice fills the whole layer. -/
theorem card_outside_slice_add_card_slice_eq_choose
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    #((((Finset.univ.powerset) \ 𝒟) # r)) + #(𝒟 # r) = Nat.choose (Fintype.card α) r := by
  have hsubset : 𝒟 # r ⊆ Finset.powersetCard r Finset.univ :=
    Set.Sized.subset_powersetCard_univ (Finset.sized_slice (𝒜 := 𝒟) (r := r))
  rw [outside_slice_eq_powersetCard_sdiff_slice, Finset.card_sdiff_add_card_eq_card hsubset,
    Finset.card_powersetCard]
  rw [Fintype.card]

/-- If an outside `(r+1)`-set avoids the positive boundary, all of its immediate predecessors stay
outside the family. -/
theorem shadow_outside_slice_succ_sdiff_boundary_slice_subset_outside_slice
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    ∂ ((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) ⊆
      (((Finset.univ.powerset) \ 𝒟) # r) := by
  intro s hs
  rcases Finset.mem_shadow_iff_insert_mem.mp hs with ⟨a, ha, hsInsert⟩
  rcases Finset.mem_sdiff.mp hsInsert with ⟨hsOutsideSlice, hsNotBoundary⟩
  rw [Finset.mem_slice, Finset.mem_sdiff] at hsOutsideSlice ⊢
  refine ⟨⟨Finset.mem_powerset.mpr (Finset.subset_univ s), ?_⟩, ?_⟩
  · intro hsD
    have hsBoundary :
        insert a s ∈ ((positiveBoundary 𝒟) # (r + 1)) := by
      rw [Finset.mem_slice]
      refine ⟨mem_positiveBoundary.mpr ?_, hsOutsideSlice.2⟩
      refine ⟨hsOutsideSlice.1.2, a, Finset.mem_insert_self a s, ?_⟩
      simpa [ha] using hsD
    exact hsNotBoundary hsBoundary
  · rw [Finset.card_insert_of_notMem ha] at hsOutsideSlice
    exact Nat.succ.inj hsOutsideSlice.2

/-- The non-boundary part of the outside `(r+1)`-slice also satisfies the adjacent local-LYM
inequality. -/
theorem card_outside_slice_succ_sdiff_boundary_slice_div_choose_le_card_outside_slice_div_choose
    {𝒟 : Finset (Finset α)} (r : ℕ) :
    ((#((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) : ℚ) /
        Nat.choose (Fintype.card α) (r + 1)) ≤
      (#((((Finset.univ.powerset) \ 𝒟) # r)) : ℚ) / Nat.choose (Fintype.card α) r := by
  let N : Finset (Finset α) :=
    (((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))
  have hsized :
      (N : Set (Finset α)).Sized (r + 1) := by
    intro s hs
    exact (Finset.mem_slice.mp (Finset.mem_sdiff.mp (show s ∈ N by simpa [N] using hs)).1).2
  have hlym :
      ((#N : ℚ) /
          Nat.choose (Fintype.card α) (r + 1)) ≤
        (#(∂ N) : ℚ) /
          Nat.choose (Fintype.card α) r := by
    simpa using
      (Finset.local_lubell_yamamoto_meshalkin_inequality_div
        (𝒜 := N)
        (r := r + 1) (𝕜 := ℚ) (by simp) hsized)
  have hcard :
      (#(∂ N) : ℚ) ≤
        #((((Finset.univ.powerset) \ 𝒟) # r)) := by
    exact_mod_cast Finset.card_le_card
      (shadow_outside_slice_succ_sdiff_boundary_slice_subset_outside_slice (𝒟 := 𝒟) r)
  have hdiv :
      (#(∂ N) : ℚ) /
          Nat.choose (Fintype.card α) r ≤
        (#((((Finset.univ.powerset) \ 𝒟) # r)) : ℚ) / Nat.choose (Fintype.card α) r := by
    exact div_le_div_of_nonneg_right hcard (by positivity)
  simpa [N] using hlym.trans hdiv

/-- The non-boundary part of the outside `(r+1)`-slice satisfies the raw local-LYM inequality. -/
theorem card_outside_slice_succ_sdiff_boundary_slice_mul_le_card_outside_slice_mul
    {𝒟 : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α) :
    #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) * (r + 1) ≤
      #((((Finset.univ.powerset) \ 𝒟) # r)) * (Fintype.card α - r) := by
  let N : Finset (Finset α) :=
    (((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))
  have hsized :
      (N : Set (Finset α)).Sized (r + 1) := by
    intro s hs
    exact (Finset.mem_slice.mp (Finset.mem_sdiff.mp (show s ∈ N by simpa [N] using hs)).1).2
  have hlym :
      #N * (r + 1) ≤
        #(∂ N) *
          (Fintype.card α - r) := by
    have h :=
      Finset.local_lubell_yamamoto_meshalkin_inequality_mul
        (𝒜 := N)
        (r := r + 1) hsized
    have hsimpl : Fintype.card α - (r + 1) + 1 = Fintype.card α - r := by omega
    simpa [hsimpl] using h
  have hcard :
      #(∂ N) ≤
        #((((Finset.univ.powerset) \ 𝒟) # r)) := by
    exact Finset.card_le_card
      (shadow_outside_slice_succ_sdiff_boundary_slice_subset_outside_slice (𝒟 := 𝒟) r)
  simpa [N] using hlym.trans (Nat.mul_le_mul_right (Fintype.card α - r) hcard)

/-- Boundary-plus-next-slice mass controls the previous slice mass in the raw adjacent recurrence. -/
theorem card_slice_mul_le_card_positiveBoundary_slice_succ_add_card_slice_succ_mul
    {𝒟 : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α) :
    #(𝒟 # r) * (Fintype.card α - r) ≤
      (#(((positiveBoundary 𝒟) # (r + 1))) + #(𝒟 # (r + 1))) * (r + 1) := by
  let n := Fintype.card α
  let p := n - r
  let N := #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1))))
  let B := #(((positiveBoundary 𝒟) # (r + 1)))
  let O₀ := #((((Finset.univ.powerset) \ 𝒟) # r))
  let O₁ := #((((Finset.univ.powerset) \ 𝒟) # (r + 1)))
  let D₀ := #(𝒟 # r)
  let D₁ := #(𝒟 # (r + 1))
  have hp : n = r + p := by
    dsimp [p]
    omega
  have hstep :=
    card_outside_slice_succ_sdiff_boundary_slice_mul_le_card_outside_slice_mul (𝒟 := 𝒟) hr
  have hsubset :
      ((positiveBoundary 𝒟) # (r + 1)) ⊆ (((Finset.univ.powerset) \ 𝒟) # (r + 1)) :=
    positiveBoundary_slice_subset_outside_slice (𝒟 := 𝒟) (r := r + 1)
  have hdecomp :
      N + B = O₁ := by
    dsimp [N, B, O₁]
    exact Finset.card_sdiff_add_card_eq_card hsubset
  have hOutside_r :
      O₀ + D₀ = Nat.choose n r := by
    dsimp [O₀, n, D₀]
    exact card_outside_slice_add_card_slice_eq_choose (𝒟 := 𝒟) r
  have hOutside_succ :
      O₁ + D₁ = Nat.choose n (r + 1) := by
    dsimp [O₁, n, D₁]
    exact card_outside_slice_add_card_slice_eq_choose (𝒟 := 𝒟) (r + 1)
  have hchoose :
      Nat.choose n (r + 1) * (r + 1) =
        Nat.choose n r * p := by
    dsimp [p]
    exact Nat.choose_succ_right_eq (Fintype.card α) r
  have hstep' :
      N * (r + 1) ≤ O₀ * p := by
    simpa [p] using hstep
  have hstepQ :
      (N : ℚ) * (r + 1) ≤ (O₀ : ℚ) * p := by
    exact_mod_cast hstep'
  have hdecompQ : (N : ℚ) + B = O₁ := by
    exact_mod_cast hdecomp
  have hOutside_rQ : (O₀ : ℚ) + D₀ = Nat.choose n r := by
    exact_mod_cast hOutside_r
  have hOutside_succQ : (O₁ : ℚ) + D₁ = Nat.choose n (r + 1) := by
    exact_mod_cast hOutside_succ
  have hchooseQ :
      (Nat.choose n (r + 1) : ℚ) * (r + 1) =
        (Nat.choose n r : ℚ) * p := by
    exact_mod_cast hchoose
  have hmainQ :
      (D₀ : ℚ) * p ≤ (B + D₁) * (r + 1) := by
    nlinarith [hstepQ, hdecompQ, hOutside_rQ, hOutside_succQ, hchooseQ]
  have hmain :
      D₀ * p ≤ (B + D₁) * (r + 1) := by
    exact_mod_cast hmainQ
  simpa [p] using hmain

/-- The normalized mass of a slice is controlled by the next slice plus the next boundary slice. -/
theorem card_slice_div_choose_le_card_positiveBoundary_slice_succ_add_card_slice_succ_div_choose
    {𝒟 : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α) :
    ((#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r) ≤
      ((#(((positiveBoundary 𝒟) # (r + 1))) + #(𝒟 # (r + 1)) : ℕ) : ℚ) /
        Nat.choose (Fintype.card α) (r + 1) := by
  let n := Fintype.card α
  let p := n - r
  let D₀ := #(𝒟 # r)
  let E := #(((positiveBoundary 𝒟) # (r + 1))) + #(𝒟 # (r + 1))
  have hrawNat :
      D₀ * p ≤ E * (r + 1) := by
    simpa [n, p, D₀, E] using
      (card_slice_mul_le_card_positiveBoundary_slice_succ_add_card_slice_succ_mul
        (𝒟 := 𝒟) hr)
  have hrawQ :
      (D₀ : ℚ) * p ≤ (E : ℚ) * (r + 1) := by
    exact_mod_cast hrawNat
  have hchooseNat :
      Nat.choose n r * p = Nat.choose n (r + 1) * (r + 1) := by
    simpa [p] using (Nat.choose_succ_right_eq n r).symm
  have hchooseQ :
      (Nat.choose n r : ℚ) * p =
        (Nat.choose n (r + 1) : ℚ) * (r + 1) := by
    exact_mod_cast hchooseNat
  have hchoose_r_pos : 0 < (Nat.choose n r : ℚ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hr)
  have hchoose_succ_pos : 0 < (Nat.choose n (r + 1) : ℚ) := by
    exact_mod_cast Nat.choose_pos hr
  have hcross :
      (D₀ : ℚ) * Nat.choose n (r + 1) ≤ (E : ℚ) * Nat.choose n r := by
    nlinarith [hrawQ, hchooseQ]
  rw [div_le_iff₀ hchoose_r_pos]
  have hquot :
      (D₀ : ℚ) ≤ ((E : ℚ) * Nat.choose n r) / Nat.choose n (r + 1) := by
    exact (le_div_iff₀ hchoose_succ_pos).mpr hcross
  simpa [n, D₀, E, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hquot

/-- The normalized boundary slice controls the drop between adjacent normalized slice masses. -/
theorem card_positiveBoundary_slice_succ_div_choose_ge_sub_card_slice_div_choose
    {𝒟 : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α) :
    ((#(((positiveBoundary 𝒟) # (r + 1))) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) ≥
      ((#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r) -
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) := by
  have h :=
    card_slice_div_choose_le_card_positiveBoundary_slice_succ_add_card_slice_succ_div_choose
      (𝒟 := 𝒟) hr
  have hsum :
      (((#(((positiveBoundary 𝒟) # (r + 1))) + #(𝒟 # (r + 1)) : ℕ) : ℚ) /
          Nat.choose (Fintype.card α) (r + 1)) =
        ((#(((positiveBoundary 𝒟) # (r + 1))) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) +
          ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) := by
    norm_num [div_eq_mul_inv, add_mul]
  rw [hsum] at h
  linarith

/-- For down-sets, normalized slice densities are nonincreasing. -/
theorem sliceDensity_succ_le_sliceDensity_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) (r : ℕ) :
    sliceDensity 𝒟 (r + 1) ≤ sliceDensity 𝒟 r := by
  simpa [sliceDensity] using
    card_slice_succ_div_choose_le_card_slice_div_choose_of_isDownSetFamily (𝒟 := 𝒟) h𝒟 r

/-- The normalized boundary slice controls the drop in slice densities. -/
theorem card_positiveBoundary_slice_succ_div_choose_ge_sliceDensity_sub_sliceDensity_succ
    {𝒟 : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α) :
    ((#(((positiveBoundary 𝒟) # (r + 1))) : ℚ) / Nat.choose (Fintype.card α) (r + 1)) ≥
      sliceDensity 𝒟 r - sliceDensity 𝒟 (r + 1) := by
  simpa [sliceDensity] using
    card_positiveBoundary_slice_succ_div_choose_ge_sub_card_slice_div_choose (𝒟 := 𝒟) hr

/-- The positive boundary has no `0`-slice. -/
theorem card_positiveBoundary_slice_zero_eq_zero
    (𝒟 : Finset (Finset α)) :
    #((positiveBoundary 𝒟) # 0) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rcases Finset.mem_slice.mp hs with ⟨hsBoundary, hsCard⟩
  have hsEmpty : s = ∅ := Finset.card_eq_zero.mp hsCard
  subst hsEmpty
  rcases mem_positiveBoundary.mp hsBoundary with ⟨_, a, ha, _⟩
  simpa using ha

/-- Summing the positive-boundary slices from rank `1` to rank `n` recovers the full boundary. -/
theorem sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat
    (𝒟 : Finset (Finset α)) :
    Finset.sum (Finset.range (Fintype.card α))
        (fun r => #(((positiveBoundary 𝒟) # (r + 1)))) =
      (positiveBoundary 𝒟).card := by
  let n := Fintype.card α
  have hsumNat' :
      ∑ r ∈ Finset.Iic (Fintype.card α), #((positiveBoundary 𝒟) # r) = #(positiveBoundary 𝒟) :=
    Finset.sum_card_slice (positiveBoundary 𝒟)
  have hsumNat :
      Finset.sum (Finset.range (n + 1)) (fun r => #((positiveBoundary 𝒟) # r)) =
        #(positiveBoundary 𝒟) := by
    simpa [n, Nat.range_succ_eq_Iic] using hsumNat'
  have hzero : #((positiveBoundary 𝒟) # 0) = 0 :=
    card_positiveBoundary_slice_zero_eq_zero (𝒟 := 𝒟)
  rw [Finset.sum_range_succ'] at hsumNat
  simpa [hzero] using hsumNat

/-- Summing the family slices from rank `1` to rank `n` recovers the family cardinality minus its
`0`-slice. -/
theorem sum_card_slice_succ_eq_card_sub_card_slice_zero_nat
    (𝒟 : Finset (Finset α)) :
    Finset.sum (Finset.range (Fintype.card α))
        (fun r => #(𝒟 # (r + 1))) =
      𝒟.card - #(𝒟 # 0) := by
  let n := Fintype.card α
  have hsumNat' :
      ∑ r ∈ Finset.Iic (Fintype.card α), #(𝒟 # r) = #𝒟 :=
    Finset.sum_card_slice 𝒟
  have hsumNat :
      Finset.sum (Finset.range (n + 1)) (fun r => #(𝒟 # r)) = #𝒟 := by
    simpa [n, Nat.range_succ_eq_Iic] using hsumNat'
  rw [Finset.sum_range_succ'] at hsumNat
  omega

/-- A nonempty down-set family has exactly one `0`-slice element, namely `∅`. -/
theorem card_slice_zero_eq_one_of_nonempty_isDownSetFamily
    {𝒟 : Finset (Finset α)} (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) :
    #(𝒟 # 0) = 1 := by
  have hempty : (∅ : Finset α) ∈ 𝒟 :=
    empty_mem_of_nonempty_isDownSetFamily h𝒟 hne
  refine Finset.card_eq_one.mpr ?_
  refine ⟨∅, ?_⟩
  ext s
  rw [Finset.mem_slice]
  constructor
  · rintro ⟨hs𝒟, hsCard⟩
    have hsEmpty : s = ∅ := Finset.card_eq_zero.mp hsCard
    simpa [hsEmpty] using hs𝒟
  · rintro rfl
    exact ⟨hempty, rfl⟩

/-- For a nonempty down-set family, summing the positive-rank slices recovers the family
cardinality minus one. -/
theorem sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily
    {𝒟 : Finset (Finset α)} (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) :
    Finset.sum (Finset.range (Fintype.card α))
        (fun r => #(𝒟 # (r + 1))) =
      𝒟.card - 1 := by
  rw [sum_card_slice_succ_eq_card_sub_card_slice_zero_nat,
    card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne h𝒟]

/-- Summing the positive-boundary slices from rank `1` to rank `n` recovers the full boundary. -/
theorem sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary
    (𝒟 : Finset (Finset α)) :
    (Finset.sum (Finset.range (Fintype.card α))
        (fun r => (#(((positiveBoundary 𝒟) # (r + 1))) : ℚ))) =
      (positiveBoundary 𝒟).card := by
  exact_mod_cast sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)

/-- For down-sets, the exact upper-shadow gap is the positive-boundary cardinality. -/
theorem upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟) :
    upperShadowGap 𝒟 = (positiveBoundary 𝒟).card := by
  let n := Fintype.card α
  have hterm :
      ∀ r ∈ Finset.range n,
        #(∂⁺ (𝒟 # r)) - #(𝒟 # (r + 1)) = #((positiveBoundary 𝒟) # (r + 1)) := by
    intro r hr
    have hEq :=
      card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
        (𝒟 := 𝒟) h𝒟 r
    omega
  calc
    upperShadowGap 𝒟
        = Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) := by
            unfold upperShadowGap
            refine Finset.sum_congr rfl ?_
            intro r hr
            exact hterm r hr
    _ = (positiveBoundary 𝒟).card :=
      sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)

/-- The full positive-boundary cardinality dominates the weighted drop functional. -/
theorem weightedDrop_le_card_positiveBoundary
    (𝒟 : Finset (Finset α)) :
    weightedDrop (Fintype.card α) (sliceDensity 𝒟) ≤ (positiveBoundary 𝒟).card := by
  let n := Fintype.card α
  have hpoint :
      ∀ r ∈ Finset.range n,
        (Nat.choose n (r + 1) : ℚ) * (sliceDensity 𝒟 r - sliceDensity 𝒟 (r + 1)) ≤
          #(((positiveBoundary 𝒟) # (r + 1))) := by
    intro r hr
    have hrlt : r < n := Finset.mem_range.mp hr
    have hdrop :
        sliceDensity 𝒟 r - sliceDensity 𝒟 (r + 1) ≤
          (#(((positiveBoundary 𝒟) # (r + 1))) : ℚ) / Nat.choose n (r + 1) := by
      simpa [ge_iff_le, n] using
        card_positiveBoundary_slice_succ_div_choose_ge_sliceDensity_sub_sliceDensity_succ
          (𝒟 := 𝒟) hrlt
    have hchoosePos : 0 < (Nat.choose n (r + 1) : ℚ) := by
      exact_mod_cast Nat.choose_pos hrlt
    simpa [mul_comm] using (le_div_iff₀ hchoosePos).mp hdrop
  have hsum :
      weightedDrop n (sliceDensity 𝒟) ≤
        Finset.sum (Finset.range n) (fun r => (#(((positiveBoundary 𝒟) # (r + 1))) : ℚ)) := by
    unfold weightedDrop
    exact Finset.sum_le_sum hpoint
  calc
    weightedDrop n (sliceDensity 𝒟) ≤
        Finset.sum (Finset.range n) (fun r => (#(((positiveBoundary 𝒟) # (r + 1))) : ℚ)) := hsum
    _ = (positiveBoundary 𝒟).card :=
      sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary (𝒟 := 𝒟)

/-- The exact upper-shadow gap theorem is sufficient to prove the half-cube boundary theorem. -/
theorem halfCubeBoundaryLower_of_halfCubeUpperShadowGapLower
    (hGap : HalfCubeUpperShadowGapLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  intro α _ _ 𝒟 hn hne h𝒟 hcard
  have hGap' :
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ upperShadowGap 𝒟 :=
    hGap hn hne h𝒟 hcard
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hGap'

/-- Sharp upper-shadow lower bound at an arbitrary codimension threshold, obtained from the
Lovász form of Kruskal-Katona by passing to complements. -/
theorem choose_sub_le_card_upShadow_of_choose_sub_le_card
    {n r j : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hj : j ≤ r) (hrn : r < n)
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r)
    (hcard : Nat.choose (n - j) (r - j) ≤ #𝒜) :
    Nat.choose (n - j) (r - j + 1) ≤ #(∂⁺ 𝒜) := by
  have hrle : r ≤ n := Nat.le_of_lt hrn
  have h𝒜bar : (𝒜ᶜˢ : Set (Finset (Fin n))).Sized (n - r) := by
    simpa using h𝒜.compls
  have hcardBar : Nat.choose (n - j) (n - r) ≤ #𝒜ᶜˢ := by
    have hsymm : Nat.choose (n - j) (n - r) = Nat.choose (n - j) (r - j) := by
      exact Nat.choose_symm_of_eq_add (by omega)
    rwa [card_compls, hsymm] using hcard
  have kk :=
    Finset.kruskal_katona_lovasz_form (n := n) (i := 1) (r := n - r) (k := n - j)
      (by omega) (by omega) (Nat.sub_le _ _) h𝒜bar hcardBar
  have hsymm : Nat.choose (n - j) (n - r - 1) = Nat.choose (n - j) (r - j + 1) := by
    exact Nat.choose_symm_of_eq_add (by omega)
  simpa [Function.iterate_one, hsymm, shadow_compls, card_compls] using kk

/-- If the `r`-slice of a down-set on `Fin n` reaches an arbitrary codimension-`j` threshold, then
the next slice together with the next boundary slice has at least the corresponding next threshold
size. -/
theorem choose_sub_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_sub
    {n r j : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟) (hj : j ≤ r) (hrn : r < n)
    (hcard : Nat.choose (n - j) (r - j) ≤ #(𝒟 # r)) :
    Nat.choose (n - j) (r - j + 1) ≤ #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1)) := by
  have hup :
      Nat.choose (n - j) (r - j + 1) ≤ #(∂⁺ (𝒟 # r)) :=
    choose_sub_le_card_upShadow_of_choose_sub_le_card
      (𝒜 := 𝒟 # r) hj hrn (Finset.sized_slice (𝒜 := 𝒟) (r := r)) hcard
  rw [card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) h𝒟 r] at hup
  simpa [add_comm] using hup

/-- If the `r`-slice of a down-set on `Fin n` reaches a codimension-`j` threshold, then the next
boundary slice is at least the deficit between the corresponding next threshold and the next slice.
-/
theorem choose_sub_sub_card_slice_succ_le_card_positiveBoundary_slice_succ_of_card_slice_ge_choose_sub
    {n r j : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟) (hj : j ≤ r) (hrn : r < n)
    (hcard : Nat.choose (n - j) (r - j) ≤ #(𝒟 # r)) :
    Nat.choose (n - j) (r - j + 1) - #(𝒟 # (r + 1)) ≤ #((positiveBoundary 𝒟) # (r + 1)) := by
  have hstep :=
    choose_sub_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_sub
      (𝒟 := 𝒟) h𝒟 hj hrn hcard
  omega

/-- Summing codimension-threshold slice deficits yields a global lower bound for the full positive
boundary of a down-set. -/
theorem sum_choose_sub_sub_card_slice_succ_le_card_positiveBoundary_of_card_slice_ge_choose_sub
    {n : ℕ} {𝒟 : Finset (Finset (Fin n))} {j : ℕ → ℕ}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hj : ∀ r ∈ Finset.range n, j r ≤ r)
    (hcard : ∀ r ∈ Finset.range n, Nat.choose (n - j r) (r - j r) ≤ #(𝒟 # r)) :
    Finset.sum (Finset.range n)
        (fun r => Nat.choose (n - j r) (r - j r + 1) - #(𝒟 # (r + 1))) ≤
      #(positiveBoundary 𝒟) := by
  have hsum :
      Finset.sum (Finset.range n)
          (fun r => Nat.choose (n - j r) (r - j r + 1) - #(𝒟 # (r + 1))) ≤
        Finset.sum (Finset.range n)
          (fun r => #((positiveBoundary 𝒟) # (r + 1))) := by
    exact Finset.sum_le_sum fun r hr =>
      choose_sub_sub_card_slice_succ_le_card_positiveBoundary_slice_succ_of_card_slice_ge_choose_sub
        (𝒟 := 𝒟) h𝒟 (hj r hr) (Finset.mem_range.mp hr) (hcard r hr)
  calc
    Finset.sum (Finset.range n)
        (fun r => Nat.choose (n - j r) (r - j r + 1) - #(𝒟 # (r + 1))) ≤
      Finset.sum (Finset.range n)
        (fun r => #((positiveBoundary 𝒟) # (r + 1))) := hsum
    _ = #(positiveBoundary 𝒟) :=
      sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)

/-- If each slice of a nonempty down-set clears a chosen Kruskal-Katona threshold, then the sum of
the corresponding next-threshold binomial terms is controlled by the boundary plus the family mass.
-/
theorem sum_choose_sub_le_card_positiveBoundary_add_card_sub_one_of_nonempty_isDownSetFamily_of_card_slice_ge_choose_sub
    {n : ℕ} {𝒟 : Finset (Finset (Fin n))} {j : ℕ → ℕ}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟)
    (hj : ∀ r ∈ Finset.range n, j r ≤ r)
    (hcard : ∀ r ∈ Finset.range n, Nat.choose (n - j r) (r - j r) ≤ #(𝒟 # r)) :
    Finset.sum (Finset.range n)
        (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      #(positiveBoundary 𝒟) + 𝒟.card - 1 := by
  have hsum :
      Finset.sum (Finset.range n)
          (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
        Finset.sum (Finset.range n)
          (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := by
    exact Finset.sum_le_sum fun r hr =>
      choose_sub_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_sub
        (𝒟 := 𝒟) h𝒟 (hj r hr) (Finset.mem_range.mp hr) (hcard r hr)
  calc
    Finset.sum (Finset.range n)
        (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      Finset.sum (Finset.range n)
        (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := hsum
    _ =
      Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) +
        Finset.sum (Finset.range n) (fun r => #(𝒟 # (r + 1))) := by
          rw [Finset.sum_add_distrib]
    _ = #(positiveBoundary 𝒟) + (𝒟.card - 1) := by
          rw [sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat,
            sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily hne h𝒟]
    _ = #(positiveBoundary 𝒟) + 𝒟.card - 1 := by omega

/-- Half-cube specialization of the previous threshold-sum inequality. -/
theorem sum_choose_sub_le_card_positiveBoundary_add_halfCube_sub_one_of_isDownSetFamily_of_card_eq_half_cube_of_card_slice_ge_choose_sub
    {n : ℕ} {𝒟 : Finset (Finset (Fin n))} {j : ℕ → ℕ}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟)
    (hhalf : 𝒟.card = 2 ^ (n - 1))
    (hj : ∀ r ∈ Finset.range n, j r ≤ r)
    (hcard : ∀ r ∈ Finset.range n, Nat.choose (n - j r) (r - j r) ≤ #(𝒟 # r)) :
    Finset.sum (Finset.range n)
        (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      #(positiveBoundary 𝒟) + 2 ^ (n - 1) - 1 := by
  simpa [hhalf] using
    sum_choose_sub_le_card_positiveBoundary_add_card_sub_one_of_nonempty_isDownSetFamily_of_card_slice_ge_choose_sub
      (𝒟 := 𝒟) hne h𝒟 hj hcard

/-- Partial-range version of the threshold-sum inequality: only the ranks where one has a sharp
threshold lower bound need to be included in the sum. -/
theorem sum_choose_sub_le_card_positiveBoundary_add_sum_card_slice_succ_of_card_slice_ge_choose_sub_on
    {n : ℕ} {𝒟 : Finset (Finset (Fin n))} {s : Finset ℕ} {j : ℕ → ℕ}
    (hs : s ⊆ Finset.range n) (h𝒟 : IsDownSetFamily 𝒟)
    (hj : ∀ r ∈ s, j r ≤ r)
    (hcard : ∀ r ∈ s, Nat.choose (n - j r) (r - j r) ≤ #(𝒟 # r)) :
    Finset.sum s (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      #(positiveBoundary 𝒟) + Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
  have hlocal :
      Finset.sum s (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
        Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := by
    exact Finset.sum_le_sum fun r hr =>
      choose_sub_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_sub
        (𝒟 := 𝒟) h𝒟 (hj r hr) (Finset.mem_of_mem_subset hs hr) (hcard r hr)
  have hbdry :
      Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1))) ≤
        Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) :=
    Finset.sum_le_sum_of_subset hs
  calc
    Finset.sum s (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := hlocal
    _ =
      Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1))) +
        Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
          rw [Finset.sum_add_distrib]
    _ ≤
      Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) +
        Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
          exact add_le_add hbdry le_rfl
    _ = #(positiveBoundary 𝒟) + Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
          rw [sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat]

/-- The lower-half shifted binomial sum in odd dimension. -/
theorem sum_range_choose_succ_halfway_odd (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) =
      2 ^ (2 * m) - 1 + Nat.choose (2 * m + 1) m := by
  have hhalf :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) = 2 ^ (2 * m) := by
    simpa [show 4 ^ m = 2 ^ (2 * m) by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using
      Nat.sum_range_choose_halfway m
  have hsucc :
      Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 1) r) =
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  have hsplit :
      Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 1) r) =
        2 ^ (2 * m) + Nat.choose (2 * m + 1) (m + 1) := by
    rw [Finset.sum_range_succ]
    simpa [hhalf]
  have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    symm
    exact Nat.choose_symm_of_eq_add (by omega)
  omega

/-- Odd-dimensional reduction: once a half-cube down-set is known to contain every slice up to the
middle rank, the sharp boundary lower bound follows. -/
theorem choose_middle_le_card_positiveBoundary_of_odd_initial_slices_full
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟)
    (hhalf : 𝒟.card = 2 ^ (2 * m))
    (hfull : ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m + 1) r ≤ #(𝒟 # r)) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  have hmain :=
    sum_choose_sub_le_card_positiveBoundary_add_sum_card_slice_succ_of_card_slice_ge_choose_sub_on
      (𝒟 := 𝒟) (s := Finset.range (m + 1)) (j := fun _ => 0)
      (Finset.range_subset_range.2 (by omega)) h𝒟
      (by intro r hr; omega)
      (by
        intro r hr
        simpa using hfull r hr)
  have hslices :
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # (r + 1))) ≤ 2 ^ (2 * m) - 1 := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # (r + 1))) ≤
        Finset.sum (Finset.range (2 * m + 1)) (fun r => #(𝒟 # (r + 1))) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      _ = 𝒟.card - 1 :=
        sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily hne h𝒟
      _ = 2 ^ (2 * m) - 1 := by rw [hhalf]
  rw [sum_range_choose_succ_halfway_odd] at hmain
  omega

/-- Sharp one-step upper-shadow lower bound at the codimension-1 threshold, obtained from the
Lovász form of Kruskal-Katona by passing to complements. -/
theorem choose_pred_le_card_upShadow_of_choose_pred_le_card
    {n r : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hr : 1 ≤ r) (hrn : r < n)
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r)
    (hcard : Nat.choose (n - 1) (r - 1) ≤ #𝒜) :
    Nat.choose (n - 1) r ≤ #(∂⁺ 𝒜) := by
  have hrle : r ≤ n := Nat.le_of_lt hrn
  have h𝒜bar : (𝒜ᶜˢ : Set (Finset (Fin n))).Sized (n - r) := by
    simpa using h𝒜.compls
  have hcardBar : Nat.choose (n - 1) (n - r) ≤ #𝒜ᶜˢ := by
    rwa [card_compls,
      Nat.choose_symm_of_eq_add (tsub_add_tsub_cancel hrle hr).symm]
  have kk :=
    Finset.kruskal_katona_lovasz_form (n := n) (i := 1) (r := n - r) (k := n - 1)
      (by omega) (by omega) (Nat.pred_le _) h𝒜bar hcardBar
  have hsymm : Nat.choose (n - 1) (n - r - 1) = Nat.choose (n - 1) r := by
    symm
    exact Nat.choose_symm_of_eq_add (by omega)
  simpa [Function.iterate_one, hsymm, shadow_compls, card_compls] using kk

/-- If the `r`-slice of a down-set on `Fin n` reaches the codimension-1 threshold, then the next
slice together with the next boundary slice has at least the corresponding next threshold size. -/
theorem choose_pred_le_card_positiveBoundary_slice_succ_add_card_slice_succ_of_card_slice_ge_choose_pred
    {n r : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟) (hr : 1 ≤ r) (hrn : r < n)
    (hcard : Nat.choose (n - 1) (r - 1) ≤ #(𝒟 # r)) :
    Nat.choose (n - 1) r ≤ #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1)) := by
  have hup :
      Nat.choose (n - 1) r ≤ #(∂⁺ (𝒟 # r)) :=
    choose_pred_le_card_upShadow_of_choose_pred_le_card
      (𝒜 := 𝒟 # r) hr hrn (Finset.sized_slice (𝒜 := 𝒟) (r := r)) hcard
  rw [card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) h𝒟 r] at hup
  simpa [add_comm] using hup

/--
Specialization of the general half-cube boundary theorem to the subtype cube transported from a
sum-distinct set `A`.
-/
theorem two_mul_choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin (n + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ n)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (n - 1)) :
    2 * Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  let N := predFamily (𝒟.nonMemberSubfamily 0)
  let M := predFamily (𝒟.memberSubfamily 0)
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hMcardRaw : #(𝒟.memberSubfamily 0) = 2 ^ (n - 1) := by
    omega
  have hNcard : N.card = 2 ^ (n - 1) := by
    simpa [N, hbal] using card_predFamily_nonMemberSubfamily 𝒟
  have hMcard : M.card = 2 ^ (n - 1) := by
    simpa [M, hMcardRaw] using card_predFamily_memberSubfamily 𝒟
  have hNne : N.Nonempty := by
    have hpos : 0 < N.card := by
      rw [hNcard]
      positivity
    exact Finset.card_pos.mp hpos
  have hMne : M.Nonempty := by
    have hpos : 0 < M.card := by
      rw [hMcard]
      positivity
    exact Finset.card_pos.mp hpos
  have hNdown : IsDownSetFamily N := by
    simpa [N] using isDownSetFamily_predFamily_nonMemberSubfamily h𝒟
  have hMdown : IsDownSetFamily M := by
    simpa [M] using isDownSetFamily_predFamily_memberSubfamily h𝒟
  have hNbdry :
      Nat.choose n (n / 2) ≤ #(positiveBoundary N) := by
    exact hCube (α := Fin n) (𝒟 := N) hn hNne hNdown hNcard
  have hMbdry :
      Nat.choose n (n / 2) ≤ #(positiveBoundary M) := by
    exact hCube (α := Fin n) (𝒟 := M) hn hMne hMdown hMcard
  have hNbdry' :
      Nat.choose n (n / 2) ≤ #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) := by
    rw [← card_positiveBoundary_predFamily_nonMemberSubfamily (𝒟 := 𝒟), N]
    exact hNbdry
  have hMbdry' :
      Nat.choose n (n / 2) ≤ #((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
    rw [← card_positiveBoundary_predFamily_memberSubfamily (𝒟 := 𝒟), M]
    exact hMbdry
  have hsum :
      Nat.choose n (n / 2) + Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
    calc
      Nat.choose n (n / 2) + Nat.choose n (n / 2)
          ≤ #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) +
              #((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
                exact add_le_add hNbdry' hMbdry'
      _ ≤ #(positiveBoundary 𝒟) :=
        card_positiveBoundary_ge_two_nonMemberSubfamily_sections 0 𝒟
  simpa [two_mul] using hsum

theorem choose_middle_even_eq_two_mul_choose_middle_odd (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  rw [Nat.choose_succ_succ', Nat.choose_symm_half, two_mul]

theorem choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_even_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact two_mul_choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_of_halfCubeBoundaryLower
    hCube (n := 2 * m + 1) (by positivity) h𝒟 hcard hbal

theorem zero_section_balanced_of_halfCube_of_totalSize_eq_max
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin (n + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ n)
    (htotal : totalSize 𝒟 = (n + 1) * 2 ^ (n - 1)) :
    #(𝒟.nonMemberSubfamily 0) = 2 ^ (n - 1) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ']
  have := card_nonMemberSubfamily_eq_half_of_card_eq_two_mul_of_totalSize_eq
    (𝒜 := 𝒟) h𝒟 (m := 2 ^ (n - 1)) hcard' htotal 0
  simpa using this

theorem exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin (n + 1)))}
    (hcard : 𝒟.card = 2 ^ n)
    (htotal : totalSize 𝒟 < (n + 1) * 2 ^ (n - 1)) :
    ∃ a : Fin (n + 1), 2 ^ (n - 1) < #(𝒟.nonMemberSubfamily a) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ']
  simpa using
    exists_card_nonMemberSubfamily_gt_half_of_card_eq_two_mul_of_totalSize_lt
      (𝒜 := 𝒟) (m := 2 ^ (n - 1)) hcard' htotal

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hbal :
      #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) :=
    zero_section_balanced_of_halfCube_of_totalSize_eq_max
      (n := 2 * m + 1) (by positivity) h𝒟 hcard htotal
  exact choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_even_of_halfCubeBoundaryLower
    hCube h𝒟 hcard hbal

theorem choose_middle_le_card_positiveBoundary_even_of_zero_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m e : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hNcard : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) + e)
    (hMcard : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) - e) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  let 𝒩 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  let ℳ : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.memberSubfamily 0)
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using isDownSetFamily_predFamily_nonMemberSubfamily h𝒟
  have hℳdown : IsDownSetFamily ℳ := by
    simpa [ℳ] using isDownSetFamily_predFamily_memberSubfamily h𝒟
  have hsubset : ℳ ⊆ 𝒩 := by
    simpa [𝒩, ℳ] using predFamily_memberSubfamily_subset_predFamily_nonMemberSubfamily h𝒟
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) + e := by
    simpa [𝒩, hNcard] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have hℳcard : ℳ.card = 2 ^ (2 * m) - e := by
    simpa [ℳ, hMcard] using card_predFamily_memberSubfamily (𝒜 := 𝒟)
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤
        (positiveBoundary 𝒩).card + (positiveBoundary ℳ).card :=
    hPair h𝒩down hℳdown hsubset h𝒩card hℳcard
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤
        #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          #((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
    simpa [𝒩, ℳ,
      card_positiveBoundary_predFamily_nonMemberSubfamily,
      card_positiveBoundary_predFamily_memberSubfamily] using hpair
  have hbdry :
      #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          #((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) ≤
        #(positiveBoundary 𝒟) :=
    card_positiveBoundary_ge_two_nonMemberSubfamily_sections 0 𝒟
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact hpair'.trans hbdry

theorem choose_middle_le_card_positiveBoundary_even_of_zero_section_excess_of_zero_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hexcess : 2 ^ (2 * m) < #(𝒟.nonMemberSubfamily 0)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  let e := #(𝒟.nonMemberSubfamily 0) - 2 ^ (2 * m)
  have hNcard : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) + e := by
    dsimp [e]
    omega
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hMcard : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) - e := by
    dsimp [e]
    omega
  exact choose_middle_le_card_positiveBoundary_even_of_zero_section_pairBoundaryLower
    (m := m) (e := e) hPair h𝒟 hNcard hMcard

theorem choose_middle_le_card_positiveBoundary_even_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m e : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {a : Fin (2 * m + 2)}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hNcard : #(𝒟.nonMemberSubfamily a) = 2 ^ (2 * m) + e)
    (hMcard : #(𝒟.memberSubfamily a) = 2 ^ (2 * m) - e) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  let 𝒩 : Finset (Finset (Fin (2 * m + 1))) := predAboveFamily a (𝒟.nonMemberSubfamily a)
  let ℳ : Finset (Finset (Fin (2 * m + 1))) := predAboveFamily a (𝒟.memberSubfamily a)
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using
      (isDownSetFamily_predAboveFamily (a := a)
        (𝒜 := 𝒟.nonMemberSubfamily a)
        (fun s hs => (mem_nonMemberSubfamily.mp hs).2)
        (isDownSetFamily_nonMemberSubfamily h𝒟 a))
  have hℳdown : IsDownSetFamily ℳ := by
    simpa [ℳ] using
      (isDownSetFamily_predAboveFamily (a := a)
        (𝒜 := 𝒟.memberSubfamily a)
        (fun s hs => (mem_memberSubfamily.mp hs).2)
        (isDownSetFamily_memberSubfamily h𝒟 a))
  have hsubset : ℳ ⊆ 𝒩 := by
    simpa [𝒩, ℳ] using
      (predAboveFamily_memberSubfamily_subset_predAboveFamily_nonMemberSubfamily
        (a := a) h𝒟)
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) + e := by
    have hcardPred :
        #(predAboveFamily a (𝒟.nonMemberSubfamily a)) = #(𝒟.nonMemberSubfamily a) := by
      apply card_predAboveFamily (a := a)
      intro s hs
      exact (mem_nonMemberSubfamily.mp hs).2
    simpa [𝒩, hNcard] using hcardPred
  have hℳcard : ℳ.card = 2 ^ (2 * m) - e := by
    have hcardPred :
        #(predAboveFamily a (𝒟.memberSubfamily a)) = #(𝒟.memberSubfamily a) := by
      apply card_predAboveFamily (a := a)
      intro s hs
      exact (mem_memberSubfamily.mp hs).2
    simpa [ℳ, hMcard] using hcardPred
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤
        (positiveBoundary 𝒩).card + (positiveBoundary ℳ).card :=
    hPair h𝒩down hℳdown hsubset h𝒩card hℳcard
  have h𝒩bdry :
      #(positiveBoundary 𝒩) =
        #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) := by
    symm
    exact card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predAboveFamily
      (a := a) (𝒜 := 𝒟.nonMemberSubfamily a)
      (fun s hs => (mem_nonMemberSubfamily.mp hs).2)
  have hℳbdry :
      #(positiveBoundary ℳ) =
        #((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a) := by
    symm
    exact card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predAboveFamily
      (a := a) (𝒜 := 𝒟.memberSubfamily a)
      (fun s hs => (mem_memberSubfamily.mp hs).2)
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤
        #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) +
          #((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a) := by
    calc
      2 * Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒩) + #(positiveBoundary ℳ) := hpair
      _ = #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) +
            #((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a) := by
              rw [h𝒩bdry, hℳbdry]
  have hbdry :
      #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) +
          #((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a) ≤
        #(positiveBoundary 𝒟) :=
    card_positiveBoundary_ge_two_nonMemberSubfamily_sections a 𝒟
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact hpair'.trans hbdry

theorem choose_middle_le_card_positiveBoundary_even_of_section_excess_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {a : Fin (2 * m + 2)}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hexcess : 2 ^ (2 * m) < #(𝒟.nonMemberSubfamily a)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  let e := #(𝒟.nonMemberSubfamily a) - 2 ^ (2 * m)
  have hNcard : #(𝒟.nonMemberSubfamily a) = 2 ^ (2 * m) + e := by
    dsimp [e]
    omega
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒟
  have hMcard : #(𝒟.memberSubfamily a) = 2 ^ (2 * m) - e := by
    dsimp [e]
    omega
  exact choose_middle_le_card_positiveBoundary_even_of_section_pairBoundaryLower
    (m := m) (e := e) (a := a) hPair h𝒟 hNcard hMcard

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  rcases exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
      (n := 2 * m + 1) (by positivity) hcard htotal with ⟨a, hexcess⟩
  exact choose_middle_le_card_positiveBoundary_even_of_section_excess_of_section_pairBoundaryLower
    (a := a) hPair h𝒟 hcard hexcess

theorem totalSize_le_max_of_isDownSetFamily_of_card_eq_half_cube_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    totalSize 𝒟 ≤ (2 * m + 2) * 2 ^ (2 * m) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, pow_succ']
  have hmember :
      ∀ a : Fin (2 * m + 2), #(𝒟.memberSubfamily a) ≤ 2 ^ (2 * m) := by
    intro a
    have hnon :
        2 ^ (2 * m) ≤ #(𝒟.nonMemberSubfamily a) := by
      exact half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul
        h𝒟 a (2 ^ (2 * m)) hcard'
    have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒟
    omega
  calc
    totalSize 𝒟 = ∑ a, #(𝒟.memberSubfamily a) := by
      symm
      exact sum_card_memberSubfamily_eq_totalSize 𝒟
    _ ≤ ∑ a : Fin (2 * m + 2), 2 ^ (2 * m) := by
      refine Finset.sum_le_sum ?_
      intro a ha
      exact hmember a
    _ = (2 * m + 2) * 2 ^ (2 * m) := by
      simp

theorem choose_middle_le_card_positiveBoundary_odd_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) + #(positiveBoundary 𝒟) := by
    simpa [hcard] using hPair (m := m) (e := 0) h𝒟 h𝒟 subset_rfl hcard hcard
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤ 2 * #(positiveBoundary 𝒟) := by
    simpa [two_mul] using hpair
  omega

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hNcard :
      #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) :=
    zero_section_balanced_of_halfCube_of_totalSize_eq_max
      (n := 2 * m + 1) (by positivity) h𝒟 hcard htotal
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hMcard : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) := by
    omega
  exact choose_middle_le_card_positiveBoundary_even_of_zero_section_pairBoundaryLower
    (m := m) (e := 0) hPair h𝒟 hNcard hMcard

theorem choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have htotal_le :
      totalSize 𝒟 ≤ (2 * m + 2) * 2 ^ (2 * m) :=
    totalSize_le_max_of_isDownSetFamily_of_card_eq_half_cube_even h𝒟 hcard
  rcases lt_or_eq_of_le htotal_le with hlt | hEq
  · exact choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_section_pairBoundaryLower
      hPair h𝒟 hcard hlt
  · exact choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_section_pairBoundaryLower
      hPair h𝒟 hcard hEq

theorem subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
  unfold HalfCubeBoundaryLowerStatement at hCube
  have hAcard : 0 < Fintype.card ↥A := by
    simpa [Fintype.card_coe] using Finset.card_pos.mpr hA
  have hCube' :
      Nat.choose (Fintype.card ↥A) (Fintype.card ↥A / 2) ≤
        (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
    exact hCube (α := ↥A) (𝒟 := negativeHalfFamilySubcubeNat A)
      hAcard
      (negativeHalfFamilySubcubeNat_nonempty h hA)
      (isDownSetFamily_negativeHalfFamilySubcubeNat A)
      (card_negativeHalfFamilySubcubeNat_eq_half_cube h hA)
  simpa [Fintype.card_coe] using hCube'

/--
Arithmetic positive-boundary lower bound derived from the general half-cube boundary theorem.
-/
theorem positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card := by
  have hsub := subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower hCube h hA
  simpa [card_positiveBoundary_negativeHalfFamilySubcubeNat_eq_positiveBoundaryFamilyNat h hA] using
    hsub

end Erdos1
