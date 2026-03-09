import ErdosProblems.Problem1CubeHalfBoundary

open Finset
open scoped BigOperators Finset FinsetFamily

namespace Erdos1

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The weighted mass of a profile across the first `n + 1` layers. -/
def profileMass (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  Finset.sum (Finset.range (n + 1)) fun r => (Nat.choose n r : ℚ) * a r

/-- Abstract sequence profile corresponding to a half-cube down-set. -/
def HalfCubeProfile (n : ℕ) (a : ℕ → ℚ) : Prop :=
  (∀ r, a (r + 1) ≤ a r) ∧
    (∀ r, 0 ≤ a r) ∧
    (∀ r, a r ≤ 1) ∧
    profileMass n a = (2 ^ (n - 1) : ℚ)

/-- Abstract weighted-drop lower bound needed to prove the half-cube boundary theorem. -/
def HalfCubeWeightedDropLowerStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) {a : ℕ → ℚ},
    HalfCubeProfile n a →
      (Nat.choose n (n / 2) : ℚ) ≤ weightedDrop n a

/-- The even `n = 2` half-cube profile shows the naive weighted-drop lower statement is false. -/
def halfCubeProfileCounterexample : ℕ → ℚ
  | 0 => 1
  | 1 => 1 / 2
  | _ => 0

/-- The profile mass of the slice-density sequence is the family cardinality. -/
theorem profileMass_sliceDensity_eq_card
    (𝒟 : Finset (Finset α)) :
    profileMass (Fintype.card α) (sliceDensity 𝒟) = 𝒟.card := by
  let n := Fintype.card α
  have hsumNat' :
      ∑ r ∈ Finset.Iic (Fintype.card α), #(𝒟 # r) = #𝒟 :=
    Finset.sum_card_slice 𝒟
  have hsumNat :
      ∑ r ∈ Finset.Iic n, #(𝒟 # r) = #𝒟 := by
    simpa [n] using hsumNat'
  have hsumQ :
      (Finset.sum (Finset.range (n + 1)) fun r => (#(𝒟 # r) : ℚ)) = 𝒟.card := by
    exact_mod_cast (by simpa [Nat.range_succ_eq_Iic] using hsumNat)
  have hterm :
      ∀ r ∈ Finset.range (n + 1),
        (Nat.choose n r : ℚ) * sliceDensity 𝒟 r = #(𝒟 # r) := by
    intro r hr
    have hrle : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hchoosePos : 0 < (Nat.choose n r : ℚ) := by
      exact_mod_cast Nat.choose_pos hrle
    calc
      (Nat.choose n r : ℚ) * sliceDensity 𝒟 r
          = (Nat.choose n r : ℚ) * ((#(𝒟 # r) : ℚ) / Nat.choose n r) := by
            rfl
      _ = #(𝒟 # r) := by
            field_simp [ne_of_gt hchoosePos]
  calc
    profileMass n (sliceDensity 𝒟)
        = Finset.sum (Finset.range (n + 1)) (fun r => (#(𝒟 # r) : ℚ)) := by
            unfold profileMass
            refine Finset.sum_congr rfl ?_
            intro r hr
            exact hterm r hr
    _ = 𝒟.card := hsumQ

/-- Slice densities are bounded above by `1`. -/
theorem sliceDensity_le_one
    (𝒟 : Finset (Finset α)) (r : ℕ) :
    sliceDensity 𝒟 r ≤ 1 := by
  let n := Fintype.card α
  have hsubset : 𝒟 # r ⊆ Finset.powersetCard r (Finset.univ : Finset α) :=
    Set.Sized.subset_powersetCard_univ (Finset.sized_slice (𝒜 := 𝒟) (r := r))
  have hcardNat : #(𝒟 # r) ≤ Nat.choose n r := by
    calc
      #(𝒟 # r) ≤ #(Finset.powersetCard r (Finset.univ : Finset α)) :=
        Finset.card_le_card hsubset
      _ = Nat.choose n r := by
        simp [n]
  have hcardQ : (#(𝒟 # r) : ℚ) ≤ Nat.choose n r := by
    exact_mod_cast hcardNat
  by_cases hchoose : Nat.choose n r = 0
  · have hzeroNat : #(𝒟 # r) = 0 := by
      rw [hchoose] at hcardNat
      exact Nat.eq_zero_of_le_zero hcardNat
    have hzero : (#(𝒟 # r) : ℚ) = 0 := by
      exact_mod_cast hzeroNat
    simp [sliceDensity, n, hchoose, hzero]
  · have hchoosePos : 0 < (Nat.choose n r : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hchoose
    have hdiv : ((#(𝒟 # r) : ℚ) / Nat.choose n r) ≤ 1 := by
      exact (div_le_iff₀ hchoosePos).2 (by simpa using hcardQ)
    simpa [sliceDensity, n] using hdiv

/-- Slice densities are nonnegative. -/
theorem sliceDensity_nonneg
    (𝒟 : Finset (Finset α)) (r : ℕ) :
    0 ≤ sliceDensity 𝒟 r := by
  by_cases hchoose : Nat.choose (Fintype.card α) r = 0
  · simp [sliceDensity, hchoose]
  · have hchoosePos : 0 < (Nat.choose (Fintype.card α) r : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hchoose
    exact div_nonneg (by positivity) hchoosePos.le

/-- A half-cube down-set induces an abstract half-cube profile on slice densities. -/
theorem halfCubeProfile_sliceDensity_of_isDownSetFamily_of_card_eq_half_cube
    {𝒟 : Finset (Finset α)} (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (Fintype.card α - 1)) :
    HalfCubeProfile (Fintype.card α) (sliceDensity 𝒟) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact sliceDensity_succ_le_sliceDensity_of_isDownSetFamily (𝒟 := 𝒟) h𝒟 r
  · intro r
    exact sliceDensity_nonneg 𝒟 r
  · intro r
    exact sliceDensity_le_one 𝒟 r
  · simpa [profileMass_sliceDensity_eq_card, hcard]

/-- The sequence theorem is sufficient to prove the half-cube boundary theorem. -/
theorem halfCubeBoundaryLower_of_halfCubeWeightedDropLower
    (hSeq : HalfCubeWeightedDropLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  intro α _ _ 𝒟 hn hne h𝒟 hcard
  have hprofile :
      HalfCubeProfile (Fintype.card α) (sliceDensity 𝒟) :=
    halfCubeProfile_sliceDensity_of_isDownSetFamily_of_card_eq_half_cube (𝒟 := 𝒟) h𝒟 hcard
  have hdrop :
      (Nat.choose (Fintype.card α) (Fintype.card α / 2) : ℚ) ≤
        weightedDrop (Fintype.card α) (sliceDensity 𝒟) :=
    hSeq hn hprofile
  have hboundary :
      weightedDrop (Fintype.card α) (sliceDensity 𝒟) ≤ (positiveBoundary 𝒟).card :=
    weightedDrop_le_card_positiveBoundary 𝒟
  exact_mod_cast (hdrop.trans hboundary)

/-- The current abstract weighted-drop lower statement is false. -/
theorem not_HalfCubeWeightedDropLowerStatement :
    ¬ HalfCubeWeightedDropLowerStatement := by
  intro h
  have hmass : profileMass 2 halfCubeProfileCounterexample = (2 : ℚ) := by
    norm_num [profileMass, halfCubeProfileCounterexample, Finset.sum_range_succ, Finset.sum_range_zero]
  have hwdrop : weightedDrop 2 halfCubeProfileCounterexample = (3 / 2 : ℚ) := by
    norm_num [weightedDrop, halfCubeProfileCounterexample, Finset.sum_range_succ, Finset.sum_range_zero]
  have hprofile : HalfCubeProfile 2 halfCubeProfileCounterexample := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      cases r with
      | zero =>
          norm_num [halfCubeProfileCounterexample]
      | succ r =>
          cases r with
          | zero =>
              norm_num [halfCubeProfileCounterexample]
          | succ r =>
              norm_num [halfCubeProfileCounterexample]
    · intro r
      cases r with
      | zero =>
          norm_num [halfCubeProfileCounterexample]
      | succ r =>
          cases r with
          | zero =>
              norm_num [halfCubeProfileCounterexample]
          | succ r =>
              norm_num [halfCubeProfileCounterexample]
    · intro r
      cases r with
      | zero =>
          norm_num [halfCubeProfileCounterexample]
      | succ r =>
          cases r with
          | zero =>
              norm_num [halfCubeProfileCounterexample]
          | succ r =>
              norm_num [halfCubeProfileCounterexample]
    · simpa [hmass]
  have hbad := h (n := 2) (by decide) hprofile
  have hbad' : (2 : ℚ) ≤ 3 / 2 := by
    simpa [hwdrop] using hbad
  norm_num at hbad'

end Erdos1
