import ErdosProblems.Problem1CubeNatBridge
import Mathlib.Combinatorics.SetFamily.LYM

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

/-- The normalized density of the `r`-slice of a family. -/
def sliceDensity (𝒟 : Finset (Finset α)) (r : ℕ) : ℚ :=
  (#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r

/-- The weighted drop functional on a profile `a : ℕ → ℚ` across the first `n` layers. -/
def weightedDrop (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  Finset.sum (Finset.range n) fun r =>
    (Nat.choose n (r + 1) : ℚ) * (a r - a (r + 1))

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
theorem sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary
    (𝒟 : Finset (Finset α)) :
    (Finset.sum (Finset.range (Fintype.card α))
        (fun r => (#(((positiveBoundary 𝒟) # (r + 1))) : ℚ))) =
      (positiveBoundary 𝒟).card := by
  let n := Fintype.card α
  have hsumNat' :
      ∑ r ∈ Finset.Iic (Fintype.card α), #((positiveBoundary 𝒟) # r) = #(positiveBoundary 𝒟) :=
    Finset.sum_card_slice (positiveBoundary 𝒟)
  have hsumNat :
      ∑ r ∈ Finset.Iic n, #((positiveBoundary 𝒟) # r) = #(positiveBoundary 𝒟) := by
    simpa [n] using hsumNat'
  have hsumQ :
      (Finset.sum (Finset.range (n + 1)) (fun r => (#((positiveBoundary 𝒟) # r) : ℚ))) =
        (positiveBoundary 𝒟).card := by
    exact_mod_cast (by simpa [Nat.range_succ_eq_Iic] using hsumNat)
  have hzero : (#((positiveBoundary 𝒟) # 0) : ℚ) = 0 := by
    exact_mod_cast card_positiveBoundary_slice_zero_eq_zero (𝒟 := 𝒟)
  rw [Finset.sum_range_succ'] at hsumQ
  simpa [hzero] using hsumQ

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

/--
Specialization of the general half-cube boundary theorem to the subtype cube transported from a
sum-distinct set `A`.
-/
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
