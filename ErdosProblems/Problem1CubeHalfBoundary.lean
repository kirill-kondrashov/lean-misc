import ErdosProblems.Problem1CubeNatBridge
import ErdosProblems.Problem1CubeEvenExtremizer
import ErdosProblems.Problem1CubeCompression
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

/-- Archival odd-dimensional paired frontier suggested by the first section-recursion route.
This statement is false; see `not_OddSectionPairBoundaryLowerStatement`. -/
def OddSectionPairBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      2 * Nat.choose (2 * m + 1) m ≤
        (positiveBoundary 𝒩).card + (positiveBoundary ℳ).card

/-- Archival stronger one-family odd-section candidate. This statement is false at `e = 0`; see
`not_OddSectionExcessBoundaryLowerStatement`. -/
def OddSectionExcessBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      2 * Nat.choose (2 * m + 1) m ≤ (positiveBoundary 𝒩).card + 2 * e

/-- Archival existential odd strict-excess wrapper. This statement is false; see
`not_OddSectionStrictExcessOptimizationStatement`. -/
def OddSectionStrictExcessOptimizationStatement : Prop :=
  ∃ β : ℕ → ℕ → ℕ,
    (∀ {m e : ℕ} {𝒩 : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
        IsDownSetFamily 𝒩 →
        𝒩.card = 2 ^ (2 * m) + e →
        β m e ≤ (positiveBoundary 𝒩).card) ∧
    (∀ m e : ℕ, 0 < e →
      2 * Nat.choose (2 * m + 1) m ≤ β m e + 2 * e)

/-- Archival direct odd strict-excess frontier. This statement is false; see
`not_OddSectionDirectStrictExcessStatement`. -/
def OddSectionDirectStrictExcessStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 : Finset (Finset (Fin (2 * m + 1)))},
    0 < e →
      IsDownSetFamily 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      2 * Nat.choose (2 * m + 1) m ≤ (positiveBoundary 𝒩).card + 2 * e

theorem oddSectionStrictExcessOptimization_of_directStrictExcess
    (hDirect : OddSectionDirectStrictExcessStatement) :
    OddSectionStrictExcessOptimizationStatement := by
  refine ⟨fun m e => 2 * Nat.choose (2 * m + 1) m - 2 * e, ?_⟩
  constructor
  · intro m e 𝒩 he h𝒩 hcard
    exact (Nat.sub_le_iff_le_add).2 (hDirect (m := m) (e := e) (𝒩 := 𝒩) he h𝒩 hcard)
  · intro m e he
    by_cases hle : 2 * e ≤ 2 * Nat.choose (2 * m + 1) m
    · simpa [Nat.sub_add_cancel hle]
    · have hge : 2 * Nat.choose (2 * m + 1) m ≤ 2 * e := by
        omega
      have hsub : 2 * Nat.choose (2 * m + 1) m - 2 * e = 0 := by
        exact Nat.sub_eq_zero_of_le hge
      have hfinal : 2 * Nat.choose (2 * m + 1) m ≤ 2 * e + (2 * Nat.choose (2 * m + 1) m - 2 * e) := by
        calc
        2 * Nat.choose (2 * m + 1) m ≤ 2 * e := hge
        _ = 2 * e + (2 * Nat.choose (2 * m + 1) m - 2 * e) := by
          simp [hsub]
      simpa [add_comm, add_left_comm, add_assoc] using hfinal

/-- Odd-dimensional half-cube boundary lower bound, isolated as the balanced-case input for the
even proof program. -/
def OddHalfCubeBoundaryLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟)

/-- Search-guided odd half-cube slice-threshold candidate: every lower-half slice of a half-cube
down-set in odd dimension should contain at least the corresponding slice of the even cube one
dimension lower. This is weaker than exact extremizer classification and matches the current
exhaustive data in `n = 1, 3, 5`. -/
def OddHalfCubeSliceThresholdStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m) r ≤ #(𝒟 # r)

/-- A global minimizer of the odd half-cube boundary functional: among all odd-cube down-sets of
half-cube size, `𝒟` has minimum positive-boundary size. Unlike
`IsOddHalfCubeBoundaryMinimizer`, this does not assume the sharp middle-binomial value in advance.
-/
def IsOddHalfCubeBoundaryGlobalMinimizer {m : ℕ}
    (𝒟 : Finset (Finset (Fin (2 * m + 1)))) : Prop :=
  IsDownSetFamily 𝒟 ∧
    𝒟.card = 2 ^ (2 * m) ∧
    ∀ {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒜 →
        𝒜.card = 2 ^ (2 * m) →
        #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜)

/-- A global minimizer of the even half-cube boundary functional: among all even-cube down-sets of
half-cube size, `𝒟` has minimum positive-boundary size. This is the natural extremizer object for
the prism reformulation of the live frontier. -/
def IsEvenHalfCubeBoundaryGlobalMinimizer {m : ℕ}
    (𝒟 : Finset (Finset (Fin (2 * m + 2)))) : Prop :=
  IsDownSetFamily 𝒟 ∧
    𝒟.card = 2 ^ (2 * m + 1) ∧
    ∀ {𝒜 : Finset (Finset (Fin (2 * m + 2)))},
      IsDownSetFamily 𝒜 →
        𝒜.card = 2 ^ (2 * m + 1) →
        #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜)

/-- Secondary potential for compressed-extremizer arguments: total coordinate weight of a cube
family, measured by summing the natural indices of all coordinates appearing in all sets. -/
def totalIndexWeight {n : ℕ} (𝒜 : Finset (Finset (Fin n))) : ℕ :=
  Finset.sum 𝒜 (fun s => Finset.sum s (fun a => (a : ℕ)))

/-- A sharp odd half-cube boundary minimizer: an odd-cube down-set of half-cube size whose
positive boundary attains the middle binomial coefficient exactly. -/
def IsOddHalfCubeBoundaryMinimizer {m : ℕ}
    (𝒟 : Finset (Finset (Fin (2 * m + 1)))) : Prop :=
  IsDownSetFamily 𝒟 ∧
    𝒟.card = 2 ^ (2 * m) ∧
    #(positiveBoundary 𝒟) = Nat.choose (2 * m + 1) m

/-- Candidate odd balanced extremizer classification suggested by exhaustive search: a half-cube
down-set in odd dimension that attains the sharp middle-binomial boundary value should have the
exact lower-half slice profile of `oddLowerHalfFamily`. -/
def OddHalfCubeBoundaryMinimizerExactProfileStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      #(positiveBoundary 𝒟) = Nat.choose (2 * m + 1) m →
      (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0)

/-- Weaker structural extremizer candidate: a sharp odd half-cube minimizer should have no
positive-boundary mass below the middle layer. -/
def OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟 →
      ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0

/-- Minimizer-only structural route for the odd balanced theorem: it should suffice to prove
vanishing of lower positive-boundary slices only for actual global minimizers of the boundary
functional at half-cube mass. -/
def OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0

/-- Even weaker minimizer-only route: it would already suffice to prove that every odd half-cube
global boundary minimizer has `minimalOutside` at least as large as the middle layer. Since
`minimalOutside ⊆ positiveBoundary` for nonempty down-sets, this gives the odd boundary lower bound
without any slice-by-slice structure. -/
def OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      Nat.choose (2 * m + 1) m ≤ #(minimalOutside 𝒟)

/-- Corrected minimizer-only antichain surface: on a genuine odd half-cube global boundary
minimizer, the positive boundary should itself already be a middle-sized antichain. Unlike the
false universal antichain route, this only quantifies over actual boundary minimizers. -/
def OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      IsAntichain (· ⊆ ·) (positiveBoundary 𝒟 : Set (Finset (Fin (2 * m + 1)))) ∧
      #(positiveBoundary 𝒟) = Nat.choose (2 * m + 1) m

/-- Archival antichain reformulation of the odd balanced half-cube problem. This statement is
false; see `not_OddAntichainUpperClosureLowerStatement`. -/
def OddAntichainUpperClosureLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
      IsAntichain (· ⊆ ·) (𝒜 : Set (Finset (Fin (2 * m + 1)))) →
      (↑(upperClosure (𝒜 : Set (Finset (Fin (2 * m + 1))))) :
        Set (Finset (Fin (2 * m + 1)))).ncard = 2 ^ (2 * m) →
      Nat.choose (2 * m + 1) m ≤ #𝒜

/-- Archival universal `minimalOutside` version of the odd balanced half-cube problem. This
statement is false; see `not_OddHalfCubeMinimalOutsideLowerStatement`. -/
def OddHalfCubeMinimalOutsideLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      Nat.choose (2 * m + 1) m ≤ #(minimalOutside 𝒟)

theorem oddHalfCubeBoundaryMinimizerExactProfileStatement_iff :
    OddHalfCubeBoundaryMinimizerExactProfileStatement ↔
      ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
        IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟 →
          (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
          (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) := by
  constructor
  · intro h m 𝒟 hmin
    exact h hmin.1 hmin.2.1 hmin.2.2
  · intro h m 𝒟 h𝒟 hcard hbdry
    exact h ⟨h𝒟, hcard, hbdry⟩

theorem oddLowerHalfFamily_isOddHalfCubeBoundaryMinimizer (m : ℕ) :
    IsOddHalfCubeBoundaryMinimizer (m := m) (oddLowerHalfFamily m) := by
  refine ⟨isDownSetFamily_oddLowerHalfFamily m, card_oddLowerHalfFamily_eq_half_cube m, ?_⟩
  simpa using card_positiveBoundary_oddLowerHalfFamily m

theorem oddLowerHalfFamily_realizes_oddHalfCubeBoundaryMinimizerExactProfileTarget (m : ℕ) :
    IsOddHalfCubeBoundaryMinimizer (m := m) (oddLowerHalfFamily m) ∧
      (∀ r ∈ Finset.range (m + 1),
        #((oddLowerHalfFamily m) # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ r, m + 1 ≤ r → #((oddLowerHalfFamily m) # r) = 0) := by
  refine ⟨oddLowerHalfFamily_isOddHalfCubeBoundaryMinimizer m, ?_⟩
  exact oddLowerHalfFamily_has_exact_slice_profile m

theorem oddLowerHalfFamily_realizes_oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishTarget
    (m : ℕ) :
    IsOddHalfCubeBoundaryMinimizer (m := m) (oddLowerHalfFamily m) ∧
      (∀ r ∈ Finset.Icc 1 m, #((positiveBoundary (oddLowerHalfFamily m)) # r) = 0) := by
  refine ⟨oddLowerHalfFamily_isOddHalfCubeBoundaryMinimizer m, ?_⟩
  intro r hr
  rw [positiveBoundary_oddLowerHalfFamily]
  refine Finset.card_eq_zero.mpr ?_
  ext s
  constructor
  · intro hs
    exfalso
    rcases Finset.mem_slice.mp hs with ⟨hsMid, hsCard⟩
    have hsCard' : s.card = m + 1 := by
      simpa using (mem_oddMiddleLayer.mp hsMid)
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrm⟩
    omega
  · intro hs
    simpa using hs

theorem oddMiddleLayer_realizes_oddAntichainUpperClosureLowerTarget (m : ℕ) :
    IsAntichain (· ⊆ ·) (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1)))) ∧
      (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
        Set (Finset (Fin (2 * m + 1)))).ncard = 2 ^ (2 * m) ∧
      #(oddMiddleLayer m) = Nat.choose (2 * m + 1) m := by
  refine ⟨isAntichain_oddMiddleLayer m, ?_⟩
  constructor
  · rw [upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily, Set.ncard_compl]
    rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin, Set.ncard_coe_finset,
      card_oddLowerHalfFamily_eq_half_cube]
    rw [pow_succ, Nat.mul_comm, two_mul, Nat.add_sub_cancel_left]
  · exact card_oddMiddleLayer m

theorem exists_isOddHalfCubeBoundaryGlobalMinimizer (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))), IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 := by
  classical
  let s : Finset (Finset (Finset (Fin (2 * m + 1)))) :=
    (Finset.univ : Finset (Finset (Finset (Fin (2 * m + 1))))).filter
      (fun 𝒟 => IsDownSetFamily 𝒟 ∧ 𝒟.card = 2 ^ (2 * m))
  have hs_nonempty : s.Nonempty := by
    refine ⟨oddLowerHalfFamily m, ?_⟩
    simp [s, isDownSetFamily_oddLowerHalfFamily m, card_oddLowerHalfFamily_eq_half_cube m]
  obtain ⟨𝒟, h𝒟s, hmin⟩ :=
    Finset.exists_min_image s (fun 𝒜 => #(positiveBoundary 𝒜)) hs_nonempty
  refine ⟨𝒟, ?_⟩
  have h𝒟s' : IsDownSetFamily 𝒟 ∧ 𝒟.card = 2 ^ (2 * m) := by
    simpa [s] using h𝒟s
  rcases h𝒟s' with ⟨h𝒟down, h𝒟card⟩
  refine ⟨h𝒟down, h𝒟card, ?_⟩
  intro 𝒜 h𝒜 h𝒜card
  have h𝒜s : 𝒜 ∈ s := by
    simpa [s, h𝒜, h𝒜card]
  exact hmin 𝒜 h𝒜s

/-- One can choose an odd half-cube global boundary minimizer with least total coordinate weight.
This is a cleaner secondary extremality surface for the simultaneous-compression normalization
program than choosing one coordinate pair at a time. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_minTotalIndexWeight
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
        IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        totalIndexWeight 𝒟 ≤ totalIndexWeight 𝒜 := by
  classical
  let s : Finset (Finset (Finset (Fin (2 * m + 1)))) :=
    (Finset.univ : Finset (Finset (Finset (Fin (2 * m + 1))))).filter
      (fun 𝒟 => IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
  have hs_nonempty : s.Nonempty := by
    obtain ⟨𝒟, h𝒟⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer m
    refine ⟨𝒟, ?_⟩
    simpa [s, h𝒟]
  obtain ⟨𝒟, h𝒟s, hmin⟩ :=
    Finset.exists_min_image s totalIndexWeight hs_nonempty
  refine ⟨𝒟, ?_, ?_⟩
  · simpa [s] using h𝒟s
  · intro 𝒜 h𝒜
    have h𝒜s : 𝒜 ∈ s := by
      simpa [s, h𝒜]
    exact hmin 𝒜 h𝒜s

/-- Ordered coordinate compression strictly decreases the total index weight whenever it changes a
family. This is the family-level strict descent needed to force minimum-weight global minimizers to
already be compressed. -/
theorem totalIndexWeight_coordCompression_lt_of_ne
    {n : ℕ} {i j : Fin n} {𝒜 : Finset (Finset (Fin n))}
    (hij : i < j) (hne : coordCompression i j 𝒜 ≠ 𝒜) :
    totalIndexWeight (coordCompression i j 𝒜) < totalIndexWeight 𝒜 := by
  simpa [totalIndexWeight, setIndexWeight] using
    sum_setIndexWeight_coordCompression_lt_of_ne (𝒜 := 𝒜) hij hne

/-- Coordinate compression preserves the boundary value of a genuine odd half-cube global
minimizer. This is the first normalization step toward a compression-based extremizer proof of the
Prism Theorem. -/
theorem card_positiveBoundary_coordCompression_eq_of_isOddHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (i j : Fin (2 * m + 1)) :
    #(positiveBoundary (coordCompression i j 𝒟)) = #(positiveBoundary 𝒟) := by
  rcases hmin with ⟨h𝒟down, h𝒟card, hmin⟩
  have hcomp :=
    coordCompression_preserves_downset_card_positiveBoundary i j 𝒟 h𝒟down
  have hmin_le :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary (coordCompression i j 𝒟)) := by
    exact hmin hcomp.1 (by simpa [h𝒟card] using hcomp.2.1)
  exact Nat.le_antisymm hcomp.2.2 hmin_le

/-- Coordinate compression keeps an odd half-cube global boundary minimizer inside the same
minimizing class. This packages the compression step in the exact form needed for later canonical
minimizer arguments. -/
theorem isOddHalfCubeBoundaryGlobalMinimizer_coordCompression
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (i j : Fin (2 * m + 1)) :
    IsOddHalfCubeBoundaryGlobalMinimizer (m := m) (coordCompression i j 𝒟) := by
  rcases hmin with ⟨h𝒟down, h𝒟card, hmin'⟩
  have hcomp :=
    coordCompression_preserves_downset_card_positiveBoundary i j 𝒟 h𝒟down
  refine ⟨hcomp.1, ?_, ?_⟩
  · simpa [h𝒟card] using hcomp.2.1
  · intro 𝒜 h𝒜 h𝒜card
    calc
      #(positiveBoundary (coordCompression i j 𝒟))
        = #(positiveBoundary 𝒟) :=
          card_positiveBoundary_coordCompression_eq_of_isOddHalfCubeBoundaryGlobalMinimizer
            ⟨h𝒟down, h𝒟card, hmin'⟩ i j
      _ ≤ #(positiveBoundary 𝒜) := hmin' h𝒜 h𝒜card

/-- For any fixed coordinate pair `(i,j)`, there exists an odd half-cube global boundary minimizer
already normalized by that compression. This is the first genuine existence theorem in the
compression-based normalization program. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_fixed_coordCompression
    (m : ℕ) (i j : Fin (2 * m + 1)) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      coordCompression i j 𝒟 = 𝒟 := by
  obtain ⟨𝒟, hmin⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer m
  refine ⟨coordCompression i j 𝒟, isOddHalfCubeBoundaryGlobalMinimizer_coordCompression hmin i j,
    ?_⟩
  simpa [coordCompression, uvCompression] using
    (UV.compression_idem ({i} : Finset (Fin (2 * m + 1))) ({j} : Finset (Fin (2 * m + 1))) 𝒟)

/-- For a fixed coordinate pair `(i,j)`, one can choose an odd half-cube global boundary minimizer
whose right-sector count is minimal among all global minimizers. This is the natural secondary
extremality surface for turning non-strict compression monotonicity into a normalization theorem. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_minRightSector
    (m : ℕ) (i j : Fin (2 * m + 1)) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
        IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        #((𝒟.filter fun s => i ∉ s ∧ j ∈ s))
          ≤ #((𝒜.filter fun s => i ∉ s ∧ j ∈ s)) := by
  classical
  let s : Finset (Finset (Finset (Fin (2 * m + 1)))) :=
    (Finset.univ : Finset (Finset (Finset (Fin (2 * m + 1))))).filter
      (fun 𝒟 => IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
  have hs_nonempty : s.Nonempty := by
    obtain ⟨𝒟, h𝒟⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer m
    refine ⟨𝒟, ?_⟩
    simpa [s, h𝒟]
  obtain ⟨𝒟, h𝒟s, hmin⟩ :=
    Finset.exists_min_image s (fun 𝒜 => #((𝒜.filter fun s => i ∉ s ∧ j ∈ s))) hs_nonempty
  refine ⟨𝒟, ?_, ?_⟩
  · simpa [s] using h𝒟s
  · intro 𝒜 h𝒜
    have h𝒜s : 𝒜 ∈ s := by
      simpa [s, h𝒜]
    exact hmin 𝒜 h𝒜s

/-- A global odd half-cube minimizer that is also minimal for the `(i,j)` right-sector count must
already be fixed by the `(i,j)` coordinate compression. This is the first secondary-extremality
normalization theorem in the compression route. -/
theorem coordCompression_eq_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minRightSector
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {i j : Fin (2 * m + 1)}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hRightMin :
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
        IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        #((𝒟.filter fun s => i ∉ s ∧ j ∈ s))
          ≤ #((𝒜.filter fun s => i ∉ s ∧ j ∈ s))) :
    coordCompression i j 𝒟 = 𝒟 := by
  by_contra hne
  have hcompMin :
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) (coordCompression i j 𝒟) :=
    isOddHalfCubeBoundaryGlobalMinimizer_coordCompression hmin i j
  have hle :
      #((𝒟.filter fun s => i ∉ s ∧ j ∈ s))
        ≤ #(((coordCompression i j 𝒟).filter fun s => i ∉ s ∧ j ∈ s)) :=
    hRightMin hcompMin
  have hlt :
      #(((coordCompression i j 𝒟).filter fun s => i ∉ s ∧ j ∈ s))
        < #((𝒟.filter fun s => i ∉ s ∧ j ∈ s)) :=
    card_rightSector_coordCompression_lt_of_ne i j 𝒟 hne
  exact (not_lt_of_ge hle) hlt

/-- A global odd half-cube minimizer with least total index weight is fixed by every ordered
coordinate compression. This is the first normalization theorem that is naturally compatible with
simultaneous compression along many pairs. -/
theorem coordCompression_eq_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minTotalIndexWeight
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {i j : Fin (2 * m + 1)}
    (hij : i < j)
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hWeightMin :
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 1)))},
        IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        totalIndexWeight 𝒟 ≤ totalIndexWeight 𝒜) :
    coordCompression i j 𝒟 = 𝒟 := by
  by_contra hne
  have hcompMin :
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) (coordCompression i j 𝒟) :=
    isOddHalfCubeBoundaryGlobalMinimizer_coordCompression hmin i j
  have hle :
      totalIndexWeight 𝒟 ≤ totalIndexWeight (coordCompression i j 𝒟) :=
    hWeightMin hcompMin
  have hlt :
      totalIndexWeight (coordCompression i j 𝒟) < totalIndexWeight 𝒟 :=
    totalIndexWeight_coordCompression_lt_of_ne hij hne
  exact (not_lt_of_ge hle) hlt

/-- There exists an odd half-cube global boundary minimizer that is fixed by every ordered
coordinate compression. This is the first genuine simultaneous-normalization theorem in the Prism
proof program. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_fully_coordCompressed
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃i j : Fin (2 * m + 1)⦄, i < j → coordCompression i j 𝒟 = 𝒟 := by
  obtain ⟨𝒟, hmin, hWeightMin⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_minTotalIndexWeight m
  refine ⟨𝒟, hmin, ?_⟩
  intro i j hij
  exact coordCompression_eq_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minTotalIndexWeight
    hij hmin hWeightMin

/-- There exists an odd half-cube global boundary minimizer that is shifted: whenever an ordered
coordinate swap moves a set downward, the moved set also lies in the family. This is the first
structural consequence extracted from simultaneous compression normalization in the Prism route. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ 𝒟 → i ∉ s → j ∈ s → swapCoord i j s ∈ 𝒟 := by
  obtain ⟨𝒟, hmin, hcomp⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_fully_coordCompressed m
  refine ⟨𝒟, hmin, ?_⟩
  intro i j hij s hs hi hj
  exact swapCoord_mem_of_mem_of_coordCompression_eq (hcomp hij) hi hj hs

/-- The shifted odd global minimizer can be chosen so that every fixed-rank slice is shifted as
well. This is the first slice-level structural consequence in the Prism extremizer program. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted_slices
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r) := by
  obtain ⟨𝒟, hmin, hshift⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted m
  refine ⟨𝒟, hmin, ?_⟩
  intro r i j hij s hs hi hj
  refine Finset.mem_slice.mpr ?_
  refine ⟨(Finset.mem_slice.mp hs).1 |> fun hs' => hshift hij hs' hi hj, ?_⟩
  rw [card_swapCoord_of_mem_right hi hj]
  exact (Finset.mem_slice.mp hs).2

/-- There exists an even half-cube global boundary minimizer. The witness family
`evenLowerHalfFamily` makes the finite search space nonempty. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))), IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 := by
  classical
  let s : Finset (Finset (Finset (Fin (2 * m + 2)))) :=
    (Finset.univ : Finset (Finset (Finset (Fin (2 * m + 2))))).filter
      (fun 𝒟 => IsDownSetFamily 𝒟 ∧ 𝒟.card = 2 ^ (2 * m + 1))
  have hs_nonempty : s.Nonempty := by
    refine ⟨evenLowerHalfFamily m, ?_⟩
    simp [s, isDownSetFamily_evenLowerHalfFamily m, card_evenLowerHalfFamily_eq_half_cube m]
  obtain ⟨𝒟, h𝒟s, hmin⟩ :=
    Finset.exists_min_image s (fun 𝒜 => #(positiveBoundary 𝒜)) hs_nonempty
  refine ⟨𝒟, ?_⟩
  have h𝒟s' : IsDownSetFamily 𝒟 ∧ 𝒟.card = 2 ^ (2 * m + 1) := by
    simpa [s] using h𝒟s
  rcases h𝒟s' with ⟨h𝒟down, h𝒟card⟩
  refine ⟨h𝒟down, h𝒟card, ?_⟩
  intro 𝒜 h𝒜 h𝒜card
  have h𝒜s : 𝒜 ∈ s := by
    simpa [s, h𝒜, h𝒜card]
  exact hmin 𝒜 h𝒜s

/-- One can choose an even half-cube global boundary minimizer with least total coordinate weight.
This is the even-cube analogue of the odd normalization surface used by the prism route. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_minTotalIndexWeight
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 2)))},
        IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        totalIndexWeight 𝒟 ≤ totalIndexWeight 𝒜 := by
  classical
  let s : Finset (Finset (Finset (Fin (2 * m + 2)))) :=
    (Finset.univ : Finset (Finset (Finset (Fin (2 * m + 2))))).filter
      (fun 𝒟 => IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
  have hs_nonempty : s.Nonempty := by
    obtain ⟨𝒟, h𝒟⟩ := exists_isEvenHalfCubeBoundaryGlobalMinimizer m
    refine ⟨𝒟, ?_⟩
    simpa [s, h𝒟]
  obtain ⟨𝒟, h𝒟s, hmin⟩ :=
    Finset.exists_min_image s totalIndexWeight hs_nonempty
  refine ⟨𝒟, ?_, ?_⟩
  · simpa [s] using h𝒟s
  · intro 𝒜 h𝒜
    have h𝒜s : 𝒜 ∈ s := by
      simpa [s, h𝒜]
    exact hmin 𝒜 h𝒜s

/-- Coordinate compression preserves the boundary value of a genuine even half-cube global
minimizer. This is the first normalization step for the even-cube extremizer problem behind the
prism theorem. -/
theorem card_positiveBoundary_coordCompression_eq_of_isEvenHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (i j : Fin (2 * m + 2)) :
    #(positiveBoundary (coordCompression i j 𝒟)) = #(positiveBoundary 𝒟) := by
  rcases hmin with ⟨h𝒟down, h𝒟card, hmin⟩
  have hcomp :=
    coordCompression_preserves_downset_card_positiveBoundary i j 𝒟 h𝒟down
  have hmin_le :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary (coordCompression i j 𝒟)) := by
    exact hmin hcomp.1 (by simpa [h𝒟card] using hcomp.2.1)
  exact Nat.le_antisymm hcomp.2.2 hmin_le

/-- Coordinate compression keeps an even half-cube global boundary minimizer inside the same
minimizing class. -/
theorem isEvenHalfCubeBoundaryGlobalMinimizer_coordCompression
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (i j : Fin (2 * m + 2)) :
    IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) (coordCompression i j 𝒟) := by
  rcases hmin with ⟨h𝒟down, h𝒟card, hmin'⟩
  have hcomp :=
    coordCompression_preserves_downset_card_positiveBoundary i j 𝒟 h𝒟down
  refine ⟨hcomp.1, ?_, ?_⟩
  · simpa [h𝒟card] using hcomp.2.1
  · intro 𝒜 h𝒜 h𝒜card
    calc
      #(positiveBoundary (coordCompression i j 𝒟))
        = #(positiveBoundary 𝒟) :=
          card_positiveBoundary_coordCompression_eq_of_isEvenHalfCubeBoundaryGlobalMinimizer
            ⟨h𝒟down, h𝒟card, hmin'⟩ i j
      _ ≤ #(positiveBoundary 𝒜) := hmin' h𝒜 h𝒜card

/-- A global even half-cube minimizer with least total index weight is fixed by every ordered
coordinate compression. This is the simultaneous-normalization theorem needed before any canonical
extremizer identification. -/
theorem coordCompression_eq_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_minTotalIndexWeight
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {i j : Fin (2 * m + 2)}
    (hij : i < j)
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hWeightMin :
      ∀ {𝒜 : Finset (Finset (Fin (2 * m + 2)))},
        IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 →
        totalIndexWeight 𝒟 ≤ totalIndexWeight 𝒜) :
    coordCompression i j 𝒟 = 𝒟 := by
  by_contra hne
  have hcompMin :
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) (coordCompression i j 𝒟) :=
    isEvenHalfCubeBoundaryGlobalMinimizer_coordCompression hmin i j
  have hle :
      totalIndexWeight 𝒟 ≤ totalIndexWeight (coordCompression i j 𝒟) :=
    hWeightMin hcompMin
  have hlt :
      totalIndexWeight (coordCompression i j 𝒟) < totalIndexWeight 𝒟 :=
    totalIndexWeight_coordCompression_lt_of_ne hij hne
  exact (not_lt_of_ge hle) hlt

/-- There exists an even half-cube global boundary minimizer that is fixed by every ordered
coordinate compression. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_fully_coordCompressed
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃i j : Fin (2 * m + 2)⦄, i < j → coordCompression i j 𝒟 = 𝒟 := by
  obtain ⟨𝒟, hmin, hWeightMin⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_minTotalIndexWeight m
  refine ⟨𝒟, hmin, ?_⟩
  intro i j hij
  exact coordCompression_eq_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_minTotalIndexWeight
    hij hmin hWeightMin

/-- There exists an even half-cube global boundary minimizer that is shifted. This is the first
structural consequence extracted from even-cube simultaneous compression normalization. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ 𝒟 → i ∉ s → j ∈ s → swapCoord i j s ∈ 𝒟 := by
  obtain ⟨𝒟, hmin, hcomp⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_fully_coordCompressed m
  refine ⟨𝒟, hmin, ?_⟩
  intro i j hij s hs hi hj
  exact swapCoord_mem_of_mem_of_coordCompression_eq (hcomp hij) hi hj hs

/-- The shifted even global minimizer can be chosen so that every fixed-rank slice is shifted as
well. This is the first slice-level structural consequence for the even-cube extremizer program. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted_slices
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      ∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r) := by
  obtain ⟨𝒟, hmin, hshift⟩ := exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted m
  refine ⟨𝒟, hmin, ?_⟩
  intro r i j hij s hs hi hj
  refine Finset.mem_slice.mpr ?_
  refine ⟨(Finset.mem_slice.mp hs).1 |> fun hs' => hshift hij hs' hi hj, ?_⟩
  rw [card_swapCoord_of_mem_right hi hj]
  exact (Finset.mem_slice.mp hs).2

/-- Every even half-cube global boundary minimizer is no worse than the standard lower-half prism
witness `evenLowerHalfFamily`. -/
theorem card_positiveBoundary_le_choose_middle_of_isEvenHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 2) (m + 1) := by
  have hle :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary (evenLowerHalfFamily m)) :=
    hmin.2.2 (𝒜 := evenLowerHalfFamily m)
      (isDownSetFamily_evenLowerHalfFamily m) (card_evenLowerHalfFamily_eq_half_cube m)
  simpa [card_positiveBoundary_evenLowerHalfFamily] using hle

theorem oddLowerHalfFamily_realizes_oddHalfCubeSliceThresholdTarget (m : ℕ) :
    IsDownSetFamily (oddLowerHalfFamily m) ∧
      (oddLowerHalfFamily m).card = 2 ^ (2 * m) ∧
      (∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m) r ≤ #((oddLowerHalfFamily m) # r)) := by
  refine ⟨isDownSetFamily_oddLowerHalfFamily m, card_oddLowerHalfFamily_eq_half_cube m, ?_⟩
  intro r hr
  have hrle : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  calc
    Nat.choose (2 * m) r ≤ Nat.choose (2 * m + 1) r := by
      exact Nat.choose_le_choose r (by omega)
    _ = #((oddLowerHalfFamily m) # r) := by
      symm
      exact card_slice_oddLowerHalfFamily_eq_choose hrle

theorem eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    𝒟 = oddLowerHalfFamily m := by
  have hslices :
      (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
        (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) :=
    (oddHalfCubeBoundaryMinimizerExactProfileStatement_iff.mp hProfile) hmin
  exact eq_oddLowerHalfFamily_of_exact_slice_profile hslices.1 hslices.2

theorem positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    positiveBoundary 𝒟 = oddMiddleLayer m := by
  have hEq :
      𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile hProfile hmin
  simpa [hEq] using positiveBoundary_oddLowerHalfFamily m

theorem card_slice_oddMiddleLayer_eq_zero_of_ne_middle
    {m r : ℕ} (hr : r ≠ m + 1) :
    #((oddMiddleLayer m) # r) = 0 := by
  refine Finset.card_eq_zero.mpr ?_
  ext s
  constructor
  · intro hs
    exfalso
    rcases Finset.mem_slice.mp hs with ⟨hsMid, hsCard⟩
    have hsCard' : s.card = m + 1 := by
      simpa using (mem_oddMiddleLayer.mp hsMid)
    exact hr (hsCard.symm.trans hsCard')
  · intro hs
    simpa using hs

theorem oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanish_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement) :
    OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement := by
  intro m 𝒟 hmin r hr
  have hEq :
      positiveBoundary 𝒟 = oddMiddleLayer m :=
    positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      hProfile hmin
  rw [hEq]
  exact card_slice_oddMiddleLayer_eq_zero_of_ne_middle (by
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrm⟩
    omega)

theorem minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    minimalOutside 𝒟 = oddMiddleLayer m := by
  have hEq :
      𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile hProfile hmin
  simpa [hEq] using minimalOutside_oddLowerHalfFamily m

theorem minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    minimalOutside 𝒟 = positiveBoundary 𝒟 := by
  rw [minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      hProfile hmin,
    positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      hProfile hmin]

theorem oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
    (hProfile : OddHalfCubeBoundaryMinimizerExactProfileStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m) r ≤ #(𝒟 # r) := by
  have hslices :
      (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
        (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) :=
    (oddHalfCubeBoundaryMinimizerExactProfileStatement_iff.mp hProfile) hmin
  intro r hr
  calc
    Nat.choose (2 * m) r ≤ Nat.choose (2 * m + 1) r := by
      exact Nat.choose_le_choose r (by omega)
    _ = #(𝒟 # r) := by
      symm
      exact hslices.1 r hr

/-- Candidate odd-dimensional paired interface frontier suggested by the exact member/nonmember
section decomposition of `positiveBoundary` on an even split. -/
def OddSectionPairInterfaceBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      2 * Nat.choose (2 * m + 1) m ≤
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ)

/-- Strictly positive-excess fragment of the pair-interface frontier. This isolates the odd
balanced case from the genuine recursion step needed in even dimension. -/
def OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    0 < e →
      IsDownSetFamily 𝒩 →
        IsDownSetFamily ℳ →
        ℳ ⊆ 𝒩 →
        𝒩.card = 2 ^ (2 * m) + e →
        ℳ.card = 2 ^ (2 * m) - e →
        2 * Nat.choose (2 * m + 1) m ≤
          #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ)

theorem oddSectionPositiveExcessPairInterfaceBoundaryLower_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement) :
    OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement := by
  intro m e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard
  exact hPair h𝒩 hℳ hsub h𝒩card hℳcard

theorem oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    OddSectionPairInterfaceBoundaryLowerStatement := by
  intro m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
  by_cases he : e = 0
  · have hcardLe : 𝒩.card ≤ ℳ.card := by
      omega
    have hEq : ℳ = 𝒩 := Finset.eq_of_subset_of_card_le hsub hcardLe
    have h𝒩bdry : Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒩) := by
      have hhalf : 𝒩.card = 2 ^ (2 * m) := by
        omega
      exact hOdd h𝒩 hhalf
    calc
      2 * Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒩) + #(positiveBoundary 𝒩) := by
        omega
      _ = #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := by
        simp [hEq]
  · exact hPair (Nat.pos_of_ne_zero he) h𝒩 hℳ hsub h𝒩card hℳcard

theorem oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeBoundaryLower_and_positiveExcessPairInterfaceBoundaryLower :
    OddSectionPairInterfaceBoundaryLowerStatement ↔
      (OddHalfCubeBoundaryLowerStatement ∧
        OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) := by
  constructor
  · intro hPair
    refine
      ⟨?_,
        oddSectionPositiveExcessPairInterfaceBoundaryLower_of_section_pairInterfaceBoundaryLower
          hPair⟩
    intro m 𝒟 h𝒟 hcard
    have hpair :
        2 * Nat.choose (2 * m + 1) m ≤
          #(positiveBoundary 𝒟) + #((𝒟 \ 𝒟) ∪ positiveBoundary 𝒟) :=
      hPair (e := 0) h𝒟 h𝒟 (by intro s hs; exact hs) (by simpa using hcard)
        (by simpa using hcard)
    have hpair' :
        2 * Nat.choose (2 * m + 1) m ≤
          #(positiveBoundary 𝒟) + #(positiveBoundary 𝒟) := by
      calc
        2 * Nat.choose (2 * m + 1) m
          ≤ #(positiveBoundary 𝒟) + #((𝒟 \ 𝒟) ∪ positiveBoundary 𝒟) := hpair
        _ = #(positiveBoundary 𝒟) + #(positiveBoundary 𝒟) := by
              simp
    omega
  · rintro ⟨hOdd, hPair⟩
    exact
      oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
        hOdd hPair

theorem not_OddSectionPairBoundaryLowerStatement :
    ¬ OddSectionPairBoundaryLowerStatement := by
  intro hPair
  let 𝒩 : Finset (Finset (Fin 1)) := Finset.univ.powerset
  let ℳ : Finset (Finset (Fin 1)) := ∅
  have h𝒩 : IsDownSetFamily 𝒩 := by
    intro s t hst ht
    simp [𝒩]
  have hℳ : IsDownSetFamily ℳ := by
    intro s t hst ht
    simpa [ℳ] using ht
  have hsub : ℳ ⊆ 𝒩 := by
    intro s hs
    simpa [ℳ] using hs
  have hpair :=
    hPair (m := 0) (e := 1) (𝒩 := 𝒩) (ℳ := ℳ) h𝒩 hℳ hsub (by simp [𝒩]) (by simp [ℳ])
  norm_num [𝒩, ℳ, positiveBoundary] at hpair

theorem not_OddSectionExcessBoundaryLowerStatement :
    ¬ OddSectionExcessBoundaryLowerStatement := by
  intro hExcess
  have hbad :=
    hExcess (m := 1) (e := 0) (𝒩 := oddLowerHalfFamily 1)
      (isDownSetFamily_oddLowerHalfFamily 1)
      (by simpa using card_oddLowerHalfFamily_eq_half_cube 1)
  rw [card_positiveBoundary_oddLowerHalfFamily] at hbad
  norm_num at hbad

theorem not_OddSectionDirectStrictExcessStatement :
    ¬ OddSectionDirectStrictExcessStatement := by
  intro hDirect
  let 𝒩 : Finset (Finset (Fin 3)) :=
    oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))}
  have h𝒩 : IsDownSetFamily 𝒩 := by
    intro t s hts hs
    dsimp [𝒩] at hs ⊢
    change t ∈ oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))} at hs
    change s ∈ oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))}
    rw [mem_union, mem_singleton] at hs ⊢
    rcases hs with hs | rfl
    · exact Or.inl (isDownSetFamily_oddLowerHalfFamily 1 hts hs)
    · by_cases hsEq : s = ({1, 2} : Finset (Fin 3))
      · exact Or.inr hsEq
      · left
        rw [mem_oddLowerHalfFamily]
        have hnot : ¬ ({1, 2} : Finset (Fin 3)) ⊆ s := by
          intro hsup
          apply hsEq
          exact Finset.Subset.antisymm hts hsup
        have hslt : s.card < ({1, 2} : Finset (Fin 3)).card := by
          exact Finset.card_lt_card ⟨hts, hnot⟩
        have hslt' : s.card < 2 := by
          simpa using hslt
        omega
  have hcard : 𝒩.card = 2 ^ (2 * 1) + 1 := by
    decide
  have hbad := hDirect (m := 1) (e := 1) (𝒩 := 𝒩) (by decide) h𝒩 hcard
  have hbdry : (positiveBoundary 𝒩).card = 3 := by
    decide
  rw [hbdry] at hbad
  norm_num at hbad

theorem not_OddSectionStrictExcessOptimizationStatement :
    ¬ OddSectionStrictExcessOptimizationStatement := by
  rintro ⟨β, hlower, hupper⟩
  let 𝒩 : Finset (Finset (Fin 3)) :=
    oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))}
  have h𝒩 : IsDownSetFamily 𝒩 := by
    intro t s hts hs
    dsimp [𝒩] at hs ⊢
    change t ∈ oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))} at hs
    change s ∈ oddLowerHalfFamily 1 ∪ {({1, 2} : Finset (Fin 3))}
    rw [mem_union, mem_singleton] at hs ⊢
    rcases hs with hs | rfl
    · exact Or.inl (isDownSetFamily_oddLowerHalfFamily 1 hts hs)
    · by_cases hsEq : s = ({1, 2} : Finset (Fin 3))
      · exact Or.inr hsEq
      · left
        rw [mem_oddLowerHalfFamily]
        have hnot : ¬ ({1, 2} : Finset (Fin 3)) ⊆ s := by
          intro hsup
          apply hsEq
          exact Finset.Subset.antisymm hts hsup
        have hslt : s.card < ({1, 2} : Finset (Fin 3)).card := by
          exact Finset.card_lt_card ⟨hts, hnot⟩
        have hslt' : s.card < 2 := by
          simpa using hslt
        omega
  have hcard : 𝒩.card = 2 ^ (2 * 1) + 1 := by
    decide
  have hβle := hlower (m := 1) (e := 1) (𝒩 := 𝒩) (by decide) h𝒩 hcard
  have hβge := hupper 1 1 (by decide)
  have hbdry : (positiveBoundary 𝒩).card = 3 := by
    decide
  rw [hbdry] at hβle
  norm_num at hβge
  omega

/-- Explicit odd half-cube down-set witnessing that `minimalOutside` can be much smaller than the
middle layer even at half-cube mass. -/
def oddHalfCubeMinimalOutsideCounterexample : Finset (Finset (Fin 3)) :=
  (Finset.univ.erase 0).powerset

theorem isDownSetFamily_oddHalfCubeMinimalOutsideCounterexample :
    IsDownSetFamily oddHalfCubeMinimalOutsideCounterexample := by
  intro s t hts hs
  simp [oddHalfCubeMinimalOutsideCounterexample] at hs ⊢
  intro x hx
  exact hs (hts hx)

theorem card_oddHalfCubeMinimalOutsideCounterexample :
    oddHalfCubeMinimalOutsideCounterexample.card = 2 ^ (2 * 1) := by
  decide

theorem minimalOutside_oddHalfCubeMinimalOutsideCounterexample :
    minimalOutside oddHalfCubeMinimalOutsideCounterexample = {({0} : Finset (Fin 3))} := by
  decide

theorem not_OddHalfCubeMinimalOutsideLowerStatement :
    ¬ OddHalfCubeMinimalOutsideLowerStatement := by
  intro hMinOut
  have hbad :=
    hMinOut (m := 1) (𝒟 := oddHalfCubeMinimalOutsideCounterexample)
      isDownSetFamily_oddHalfCubeMinimalOutsideCounterexample
      card_oddHalfCubeMinimalOutsideCounterexample
  rw [minimalOutside_oddHalfCubeMinimalOutsideCounterexample] at hbad
  norm_num at hbad

/-- The normalized density of the `r`-slice of a family. -/
def sliceDensity (𝒟 : Finset (Finset α)) (r : ℕ) : ℚ :=
  (#(𝒟 # r) : ℚ) / Nat.choose (Fintype.card α) r

/-- Any family slice is bounded by the full layer. -/
theorem card_slice_le_choose {n r : ℕ} {𝒟 : Finset (Finset (Fin n))} :
    #(𝒟 # r) ≤ Nat.choose n r := by
  have hsubset : 𝒟 # r ⊆ (Finset.univ : Finset (Fin n)).powersetCard r :=
    Set.Sized.subset_powersetCard_univ (Finset.sized_slice (𝒜 := 𝒟) (r := r))
  calc
    #(𝒟 # r) ≤ #((Finset.univ : Finset (Fin n)).powersetCard r) := Finset.card_le_card hsubset
    _ = Nat.choose n r := by simp

/-- Taking a slice is monotone under inclusion of families. -/
theorem card_slice_le_card_slice_of_subset {n r : ℕ}
    {𝒜 ℬ : Finset (Finset (Fin n))} (hsub : 𝒜 ⊆ ℬ) :
    #(𝒜 # r) ≤ #(ℬ # r) := by
  exact Finset.card_le_card <| by
    intro s hs
    exact Finset.mem_slice.mpr ⟨hsub (Finset.mem_slice.mp hs).1, (Finset.mem_slice.mp hs).2⟩

/-- If a larger slice is empty, every smaller slice under inclusion is empty as well. -/
theorem card_slice_eq_zero_of_subset_of_card_slice_eq_zero {n r : ℕ}
    {𝒜 ℬ : Finset (Finset (Fin n))} (hsub : 𝒜 ⊆ ℬ)
    (hzero : #(ℬ # r) = 0) :
    #(𝒜 # r) = 0 := by
  have hle : #(𝒜 # r) ≤ #(ℬ # r) := card_slice_le_card_slice_of_subset hsub
  omega

/-- Taking a slice commutes with set difference. -/
theorem slice_sdiff_eq_sdiff_slice {n r : ℕ}
    {𝒜 ℬ : Finset (Finset (Fin n))} :
    (𝒜 \ ℬ) # r = (𝒜 # r) \ (ℬ # r) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_slice.mp hs with ⟨hsAB, hsCard⟩
    rcases Finset.mem_sdiff.mp hsAB with ⟨hs𝒜, hsℬ⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_slice.mpr ⟨hs𝒜, hsCard⟩, ?_⟩
    intro hsB
    exact hsℬ (Finset.mem_slice.mp hsB).1
  · intro hs
    rcases Finset.mem_sdiff.mp hs with ⟨hs𝒜, hsℬ⟩
    rcases Finset.mem_slice.mp hs𝒜 with ⟨hsA, hsCard⟩
    refine Finset.mem_slice.mpr ⟨Finset.mem_sdiff.mpr ⟨hsA, ?_⟩, hsCard⟩
    intro hsB
    exact hsℬ (Finset.mem_slice.mpr ⟨hsB, hsCard⟩)

/-- For nested families, the gap slice cardinality is the difference of the slice cardinalities. -/
theorem card_slice_sdiff_eq_card_slice_sub_card_slice_of_subset {n r : ℕ}
    {𝒜 ℬ : Finset (Finset (Fin n))} (hsub : ℬ ⊆ 𝒜) :
    #((𝒜 \ ℬ) # r) = #(𝒜 # r) - #(ℬ # r) := by
  rw [slice_sdiff_eq_sdiff_slice, Finset.card_sdiff_of_subset]
  intro s hs
  exact Finset.mem_slice.mpr ⟨hsub (Finset.mem_slice.mp hs).1, (Finset.mem_slice.mp hs).2⟩

/-- Total size is the weighted sum of the slice cardinalities. -/
theorem totalSize_eq_sum_range_mul_card_slice (𝒟 : Finset (Finset α)) :
    totalSize 𝒟 =
      Finset.sum (Finset.range (Fintype.card α + 1)) (fun r => r * #(𝒟 # r)) := by
  calc
    totalSize 𝒟 = ∑ s ∈ 𝒟, s.card := rfl
    _ = ∑ r ∈ Finset.range (Fintype.card α + 1), ∑ s ∈ 𝒟 with s.card = r, s.card := by
        refine (sum_fiberwise_of_maps_to ?_ _).symm
        intro s hs
        simpa [Finset.mem_range] using (Nat.lt_succ_of_le (Finset.card_le_univ s))
    _ = ∑ r ∈ Finset.range (Fintype.card α + 1), ∑ s ∈ 𝒟 # r, s.card := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have hs : {s ∈ 𝒟 | s.card = r} = 𝒟 # r := by
          ext s
          simp [Finset.mem_slice]
        rw [hs]
    _ = Finset.sum (Finset.range (Fintype.card α + 1)) (fun r => r * #(𝒟 # r)) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        rw [Finset.sum_const_nat (s := 𝒟 # r) (m := r) (fun s hs => (Finset.mem_slice.mp hs).2),
          Nat.mul_comm]

/-- Shifting every set away from `0` preserves total size: `succFamily` changes coordinates but
not cardinalities. -/
theorem totalSize_succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    totalSize (succFamily 𝒜) = totalSize 𝒜 := by
  have hsucc :
      totalSize (succFamily 𝒜) =
        Finset.sum (Finset.range (n + 2)) (fun r => r * #((succFamily 𝒜) # r)) := by
    simpa using totalSize_eq_sum_range_mul_card_slice (succFamily 𝒜)
  have hbase :
      totalSize 𝒜 =
        Finset.sum (Finset.range (n + 1)) (fun r => r * #(𝒜 # r)) := by
    simpa using totalSize_eq_sum_range_mul_card_slice 𝒜
  have hsplit :
      Finset.sum (Finset.range (n + 2)) (fun r => r * #(𝒜 # r)) =
        Finset.sum (Finset.range (n + 1)) (fun r => r * #(𝒜 # r)) +
          Finset.sum (Finset.Ico (n + 1) (n + 2)) (fun r => r * #(𝒜 # r)) := by
    symm
    exact Finset.sum_range_add_sum_Ico (fun r => r * #(𝒜 # r)) (by omega)
  have htopZero :
      Finset.sum (Finset.Ico (n + 1) (n + 2)) (fun r => r * #(𝒜 # r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrEq : r = n + 1 := by
      rcases Finset.mem_Ico.mp hr with ⟨hr1, hr2⟩
      omega
    subst hrEq
    have hslice :
        #(𝒜 # (n + 1)) = 0 := by
      exact Nat.eq_zero_of_le_zero (by
        simpa using (card_slice_le_choose (𝒟 := 𝒜) (r := n + 1)))
    simp [hslice]
  calc
    totalSize (succFamily 𝒜)
      = Finset.sum (Finset.range (n + 2)) (fun r => r * #((succFamily 𝒜) # r)) := hsucc
    _ = Finset.sum (Finset.range (n + 2)) (fun r => r * #(𝒜 # r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [card_slice_succFamily]
    _ = Finset.sum (Finset.range (n + 1)) (fun r => r * #(𝒜 # r)) +
          Finset.sum (Finset.Ico (n + 1) (n + 2)) (fun r => r * #(𝒜 # r)) := hsplit
    _ = Finset.sum (Finset.range (n + 1)) (fun r => r * #(𝒜 # r)) := by
          rw [htopZero, add_zero]
    _ = totalSize 𝒜 := hbase.symm

/-- The standard even lower-half witness has explicit total size. In particular, it sits strictly
below the crude uniform upper bound `(2 * m + 2) * 2^(2 * m)`, so that bound cannot be the
correct witness-comparison target for the prism program. -/
theorem totalSize_evenLowerHalfFamily (m : ℕ) :
    totalSize (evenLowerHalfFamily m) =
      (2 * m + 2) * 2 ^ (2 * m) - (m + 1) * Nat.choose (2 * m + 1) m := by
  have hsumAll :
      totalSize (evenLowerHalfFamily m) =
        Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := by
    simpa using totalSize_eq_sum_range_mul_card_slice (evenLowerHalfFamily m)
  have hsplit :
      Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range (m + 2))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
            (fun r => r * #((evenLowerHalfFamily m) # r)) := by
    symm
    exact Finset.sum_range_add_sum_Ico
      (fun r => r * #((evenLowerHalfFamily m) # r)) (by omega)
  have hupperZero :
      Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [card_slice_evenLowerHalfFamily_eq_zero (Finset.mem_Ico.mp hr).1, Nat.mul_zero]
  have hlowerSplit :
      Finset.sum (Finset.range (m + 2))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range (m + 1))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          (m + 1) * #((evenLowerHalfFamily m) # (m + 1)) := by
    rw [Finset.sum_range_succ]
  have hweightedLowerShift :
      Finset.sum (Finset.range (m + 1))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range m)
          (fun r => (r + 1) * #((evenLowerHalfFamily m) # (r + 1))) := by
    have hshift :=
      (Finset.sum_range_succ'
        (f := fun r => r * #((evenLowerHalfFamily m) # r)) (n := m))
    simpa using hshift
  have hweightedLowerChoose :
      Finset.sum (Finset.range (m + 1))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        (2 * m + 2) *
          Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) := by
    rw [hweightedLowerShift]
    calc
      Finset.sum (Finset.range m)
          (fun r => (r + 1) * #((evenLowerHalfFamily m) # (r + 1)))
        =
          Finset.sum (Finset.range m)
            (fun r => (2 * m + 2) * Nat.choose (2 * m + 1) r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [card_slice_evenLowerHalfFamily_eq_choose
                (Nat.succ_le_of_lt (Finset.mem_range.mp hr))]
              simpa [Nat.mul_comm] using
                (Nat.add_one_mul_choose_eq (2 * m + 1) r).symm
      _ =
          (2 * m + 2) *
            Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) := by
              rw [Finset.mul_sum]
  have hhalf :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) =
        2 ^ (2 * m) := by
    simpa [show 4 ^ m = 2 ^ (2 * m) by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using
      Nat.sum_range_choose_halfway m
  have hlowerChoose :
      Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) =
        2 ^ (2 * m) - Nat.choose (2 * m + 1) m := by
    have hsucc :
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) =
          Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) +
            Nat.choose (2 * m + 1) m := by
      rw [Finset.sum_range_succ]
    omega
  have hmiddleLePow : Nat.choose (2 * m + 1) m ≤ 2 ^ (2 * m) := by
    have hle :
        Nat.choose (2 * m + 1) m ≤
          Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) := by
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    omega
  have hdoubleMiddle :
      (2 * m + 2) * Nat.choose (2 * m + 1) m =
        2 * ((m + 1) * Nat.choose (2 * m + 1) m) := by
    ring
  have hdoubleMiddleLe :
      2 * ((m + 1) * Nat.choose (2 * m + 1) m) ≤ (2 * m + 2) * 2 ^ (2 * m) := by
    have hmul := Nat.mul_le_mul_left (m + 1) hmiddleLePow
    calc
      2 * ((m + 1) * Nat.choose (2 * m + 1) m) ≤ 2 * ((m + 1) * 2 ^ (2 * m)) :=
        Nat.mul_le_mul_left 2 hmul
      _ = (2 * m + 2) * 2 ^ (2 * m) := by ring
  calc
    totalSize (evenLowerHalfFamily m)
      =
        Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := hsumAll
    _ =
        Finset.sum (Finset.range (m + 2))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
            (fun r => r * #((evenLowerHalfFamily m) # r)) := hsplit
    _ =
        Finset.sum (Finset.range (m + 2))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := by
            rw [hupperZero, add_zero]
    _ =
        Finset.sum (Finset.range (m + 1))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          (m + 1) * #((evenLowerHalfFamily m) # (m + 1)) := hlowerSplit
    _ =
        (2 * m + 2) * Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) +
          (m + 1) * Nat.choose (2 * m + 1) m := by
            rw [hweightedLowerChoose, card_slice_evenLowerHalfFamily_eq_middle]
    _ =
        (2 * m + 2) * (2 ^ (2 * m) - Nat.choose (2 * m + 1) m) +
          (m + 1) * Nat.choose (2 * m + 1) m := by
            rw [hlowerChoose]
    _ =
        (2 * m + 2) * 2 ^ (2 * m) - (m + 1) * Nat.choose (2 * m + 1) m := by
            rw [Nat.mul_sub_left_distrib, hdoubleMiddle]
            omega

theorem totalSize_evenLowerHalfFamily_lt_max (m : ℕ) :
    totalSize (evenLowerHalfFamily m) < (2 * m + 2) * 2 ^ (2 * m) := by
  rw [totalSize_evenLowerHalfFamily]
  have hchoosePos : 0 < Nat.choose (2 * m + 1) m := by
    exact Nat.choose_pos (by omega)
  have hsubPos : 0 < (m + 1) * Nat.choose (2 * m + 1) m := by
    exact Nat.mul_pos (Nat.succ_pos _) hchoosePos
  exact Nat.sub_lt (by positivity) hsubPos

/-- The weighted drop functional on a profile `a : ℕ → ℚ` across the first `n` layers. -/
def weightedDrop (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  Finset.sum (Finset.range n) fun r =>
    (Nat.choose n (r + 1) : ℚ) * (a r - a (r + 1))

/-- The exact upper-shadow gap across the first `n` layers of a family. -/
def upperShadowGap (𝒟 : Finset (Finset α)) : ℕ :=
  Finset.sum (Finset.range (Fintype.card α)) fun r =>
    #(∂⁺ (𝒟 # r)) - #(𝒟 # (r + 1))

/-- The 3-dimensional half-cube counterexample has weighted drop `7/3`. -/
theorem weightedDrop_oddHalfCubeMinimalOutsideCounterexample :
    weightedDrop (Fintype.card (Fin 3))
        (sliceDensity oddHalfCubeMinimalOutsideCounterexample) = (7 : ℚ) / 3 := by
  native_decide

/-- The same counterexample shows that `weightedDrop` can stay below the middle binomial
coefficient even when a lower positive-boundary slice is present. -/
theorem weightedDrop_lt_choose_middle_oddHalfCubeMinimalOutsideCounterexample :
    weightedDrop (Fintype.card (Fin 3))
        (sliceDensity oddHalfCubeMinimalOutsideCounterexample) < Nat.choose 3 1 := by
  native_decide

/-- The 3-dimensional minimal-outside counterexample has a nonzero lower boundary slice. -/
theorem lower_boundary_slice_pos_oddHalfCubeMinimalOutsideCounterexample :
    0 < #((positiveBoundary oddHalfCubeMinimalOutsideCounterexample) # 1) := by
  native_decide

/-- Despite the weighted-drop failure, the exact upper-shadow gap is still strictly above the
middle binomial coefficient on this example. -/
theorem choose_middle_lt_upperShadowGap_oddHalfCubeMinimalOutsideCounterexample :
    Nat.choose 3 1 < upperShadowGap oddHalfCubeMinimalOutsideCounterexample := by
  native_decide

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

/-- The shifted odd global minimizer can be chosen with a monotone normalized slice profile. This
is the first quantitative slice-structure consequence on the Prism route toward canonical
extremizers. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted_slices_monotoneProfile
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r := by
  obtain ⟨𝒟, hmin, hshift⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted_slices m
  refine ⟨𝒟, hmin, hshift, ?_⟩
  intro r
  simpa [Fintype.card_fin] using
    (card_slice_succ_div_choose_le_card_slice_div_choose_of_isDownSetFamily hmin.1 r)

/-- A single packaged slice-data theorem for the odd half-cube global minimizer selected by the
compression route. This is the exact input surface for the next rigidity phase: shifted slices,
adjacent shadow containment, and monotone normalized slice profile. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r) := by
  obtain ⟨𝒟, hmin, hshift, hmono⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_shifted_slices_monotoneProfile m
  refine ⟨𝒟, hmin, ?_, hshift, hmono⟩
  intro r
  exact shadow_slice_succ_subset_slice_of_isDownSetFamily hmin.1 r

/-- The shifted even global minimizer can be chosen with a monotone normalized slice profile. This
is the first quantitative slice-structure consequence on the even-cube side of the prism route. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted_slices_monotoneProfile
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r := by
  obtain ⟨𝒟, hmin, hshift⟩ := exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted_slices m
  refine ⟨𝒟, hmin, hshift, ?_⟩
  intro r
  simpa [Fintype.card_fin] using
    (card_slice_succ_div_choose_le_card_slice_div_choose_of_isDownSetFamily hmin.1 r)

/-- A single packaged slice-data theorem for the even half-cube global minimizer selected by the
compression route: shifted slices, adjacent shadow containment, and monotone normalized slice
profile. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r) := by
  obtain ⟨𝒟, hmin, hshift, hmono⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_shifted_slices_monotoneProfile m
  refine ⟨𝒟, hmin, ?_, hshift, hmono⟩
  intro r
  exact shadow_slice_succ_subset_slice_of_isDownSetFamily hmin.1 r

/-- For a family with monotone normalized slice profile, a full `(r+1)`-slice forces the `r`-slice
to be full as well. This is the first genuine slice-rigidity lemma extracted from the compression
route. -/
theorem card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r)
    {r : ℕ} (hr : r ≤ 2 * m)
    (hfullSucc : #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1)) :
    #(𝒟 # r) = Nat.choose (2 * m + 1) r := by
  have hchoose_succ_pos : 0 < (Nat.choose (2 * m + 1) (r + 1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hchoose_pos : 0 < (Nat.choose (2 * m + 1) r : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlower :
      (1 : ℚ) ≤ (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r := by
    simpa [hfullSucc, hchoose_succ_pos.ne'] using hmono r
  have hslice_le :
      (#(𝒟 # r) : ℚ) ≤ Nat.choose (2 * m + 1) r := by
    exact_mod_cast card_slice_le_choose (𝒟 := 𝒟) (r := r)
  have hupper :
      (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r ≤ 1 := by
    have hratio :
        (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r ≤
          (Nat.choose (2 * m + 1) r : ℚ) / Nat.choose (2 * m + 1) r := by
      exact div_le_div_of_nonneg_right hslice_le (by positivity)
    simpa [hchoose_pos.ne'] using hratio
  have hEqRatio :
      (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r = 1 :=
    le_antisymm hupper hlower
  have hEqQ :
      (#(𝒟 # r) : ℚ) = Nat.choose (2 * m + 1) r := by
    have := (div_eq_iff hchoose_pos.ne').mp hEqRatio
    simpa using this
  exact_mod_cast hEqQ

/-- For a family with monotone normalized slice profile, a vanishing `r`-slice forces the
`(r+1)`-slice to vanish as well. -/
theorem card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r)
    {r : ℕ} (hr : r ≤ 2 * m)
    (hzero : #(𝒟 # r) = 0) :
    #(𝒟 # (r + 1)) = 0 := by
  have hchoose_succ_pos : 0 < (Nat.choose (2 * m + 1) (r + 1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hratio_le_zero :
      (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1) ≤ 0 := by
    simpa [hzero] using hmono r
  have hratio_nonneg :
      0 ≤ (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1) := by
    positivity
  have hratio_eq :
      (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1) = 0 :=
    le_antisymm hratio_le_zero hratio_nonneg
  have hEqQ :
      (#(𝒟 # (r + 1)) : ℚ) = 0 := by
    have := (div_eq_iff hchoose_succ_pos.ne').mp hratio_eq
    simpa using this
  exact_mod_cast hEqQ

/-- The odd minimizer selected by the compression route can be chosen with the first concrete
slice-rigidity consequences already bundled: full slices propagate downward and zero slices
propagate upward. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_propagation
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r : ℕ⦄, r ≤ 2 * m →
        #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1) →
          #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r : ℕ⦄, r ≤ 2 * m →
        #(𝒟 # r) = 0 → #(𝒟 # (r + 1)) = 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData m
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, ?_, ?_⟩
  · intro r hr hfullSucc
    exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose hmono hr hfullSucc
  · intro r hr hzero
    exact card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero hmono hr hzero

/-- Under a monotone normalized slice profile, a full slice forces every lower slice to be full. -/
theorem card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r) :
    ∀ r : ℕ, r ≤ 2 * m →
      #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1) →
      ∀ s : ℕ, s ≤ r + 1 → #(𝒟 # s) = Nat.choose (2 * m + 1) s
  | 0, hr, hfull, s, hs => by
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl
      · exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose
          hmono (by omega) hfull
      · exact hfull
  | r + 1, hr, hfull, s, hs => by
      have hprev :
          #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1) :=
        card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose
          hmono (by omega) hfull
      by_cases hsTop : s = r + 2
      · subst hsTop
        exact hfull
      · have hsle : s ≤ r + 1 := by omega
        exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix
          hmono r (by omega) hprev s hsle

/-- Under a monotone normalized slice profile, a zero slice forces every higher slice to vanish. -/
theorem card_slice_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_suffix
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r)
    {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ 2 * m + 1)
    (hzero : #(𝒟 # r) = 0) :
    #(𝒟 # s) = 0 := by
  have haux :
      ∀ t : ℕ, r + t ≤ 2 * m + 1 → #(𝒟 # (r + t)) = 0 := by
    intro t
    induction t with
    | zero =>
        intro _
        simpa using hzero
    | succ t iht =>
        intro hbound
        have hcurr : #(𝒟 # (r + t)) = 0 := iht (by omega)
        have hcurrBound : r + t ≤ 2 * m := by omega
        have hnext :
            #(𝒟 # ((r + t) + 1)) = 0 :=
          card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero
            hmono hcurrBound hcurr
        simpa [Nat.add_assoc] using hnext
  have hsub : r + (s - r) = s := Nat.add_sub_of_le hrs
  simpa [hsub] using haux (s - r) (by omega)

/-- The odd minimizer selected by the compression route can be chosen with full-prefix and zero-tail
slice propagation. This is the first interval-structure theorem for the candidate extremizer
profile. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_intervalPropagation
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r s : ℕ⦄, s ≤ r → r ≤ 2 * m + 1 →
        #(𝒟 # r) = Nat.choose (2 * m + 1) r →
          #(𝒟 # s) = Nat.choose (2 * m + 1) s) ∧
      (∀ ⦃r s : ℕ⦄, r ≤ s → s ≤ 2 * m + 1 →
        #(𝒟 # r) = 0 → #(𝒟 # s) = 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono, hfullStep, hzeroStep⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_propagation m
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, ?_, ?_⟩
  · intro r s hsr hr hfull
    cases r with
    | zero =>
        have hs0 : s = 0 := by omega
        subst hs0
        simpa using hfull
    | succ r' =>
        have hr' : r' ≤ 2 * m := by omega
        have hfullTop : #(𝒟 # (r' + 1)) = Nat.choose (2 * m + 1) (r' + 1) := by
          simpa using hfull
        exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix
          hmono r' hr' hfullTop s hsr
  · intro r s hrs hs hzero
    exact card_slice_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_suffix
      hmono hrs hs hzero

/-- Even-cube version: for a family with monotone normalized slice profile, a full `(r+1)`-slice
forces the `r`-slice to be full as well. -/
theorem card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r)
    {r : ℕ} (hr : r ≤ 2 * m + 1)
    (hfullSucc : #(𝒟 # (r + 1)) = Nat.choose (2 * m + 2) (r + 1)) :
    #(𝒟 # r) = Nat.choose (2 * m + 2) r := by
  have hchoose_succ_pos : 0 < (Nat.choose (2 * m + 2) (r + 1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hchoose_pos : 0 < (Nat.choose (2 * m + 2) r : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlower :
      (1 : ℚ) ≤ (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r := by
    simpa [hfullSucc, hchoose_succ_pos.ne'] using hmono r
  have hslice_le :
      (#(𝒟 # r) : ℚ) ≤ Nat.choose (2 * m + 2) r := by
    exact_mod_cast card_slice_le_choose (𝒟 := 𝒟) (r := r)
  have hupper :
      (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r ≤ 1 := by
    have hratio :
        (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r ≤
          (Nat.choose (2 * m + 2) r : ℚ) / Nat.choose (2 * m + 2) r := by
      exact div_le_div_of_nonneg_right hslice_le (by positivity)
    simpa [hchoose_pos.ne'] using hratio
  have hEqRatio :
      (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r = 1 :=
    le_antisymm hupper hlower
  have hEqQ :
      (#(𝒟 # r) : ℚ) = Nat.choose (2 * m + 2) r := by
    have := (div_eq_iff hchoose_pos.ne').mp hEqRatio
    simpa using this
  exact_mod_cast hEqQ

/-- Even-cube version: for a family with monotone normalized slice profile, a vanishing `r`-slice
forces the `(r+1)`-slice to vanish as well. -/
theorem card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r)
    {r : ℕ} (hr : r ≤ 2 * m + 1)
    (hzero : #(𝒟 # r) = 0) :
    #(𝒟 # (r + 1)) = 0 := by
  have hchoose_succ_pos : 0 < (Nat.choose (2 * m + 2) (r + 1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hratio_le_zero :
      (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1) ≤ 0 := by
    simpa [hzero] using hmono r
  have hratio_nonneg :
      0 ≤ (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1) := by
    positivity
  have hratio_eq :
      (#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1) = 0 :=
    le_antisymm hratio_le_zero hratio_nonneg
  have hEqQ :
      (#(𝒟 # (r + 1)) : ℚ) = 0 := by
    have := (div_eq_iff hchoose_succ_pos.ne').mp hratio_eq
    simpa using this
  exact_mod_cast hEqQ

/-- The even minimizer selected by the compression route can be chosen with the first concrete
slice-rigidity consequences already bundled: full slices propagate downward and zero slices
propagate upward. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_propagation
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r) ∧
      (∀ ⦃r : ℕ⦄, r ≤ 2 * m + 1 →
        #(𝒟 # (r + 1)) = Nat.choose (2 * m + 2) (r + 1) →
          #(𝒟 # r) = Nat.choose (2 * m + 2) r) ∧
      (∀ ⦃r : ℕ⦄, r ≤ 2 * m + 1 →
        #(𝒟 # r) = 0 → #(𝒟 # (r + 1)) = 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData m
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, ?_, ?_⟩
  · intro r hr hfullSucc
    exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose_even
      hmono hr hfullSucc
  · intro r hr hzero
    exact card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_even
      hmono hr hzero

/-- Even-cube version: under a monotone normalized slice profile, a full slice forces every lower
slice to be full. -/
theorem card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r) :
    ∀ r : ℕ, r ≤ 2 * m + 1 →
      #(𝒟 # (r + 1)) = Nat.choose (2 * m + 2) (r + 1) →
      ∀ s : ℕ, s ≤ r + 1 → #(𝒟 # s) = Nat.choose (2 * m + 2) s
  | 0, hr, hfull, s, hs => by
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl
      · exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose_even
          hmono (by omega) hfull
      · exact hfull
  | r + 1, hr, hfull, s, hs => by
      have hprev :
          #(𝒟 # (r + 1)) = Nat.choose (2 * m + 2) (r + 1) :=
        card_slice_eq_choose_of_monotoneProfile_of_card_slice_succ_eq_choose_even
          hmono (by omega) hfull
      by_cases hsTop : s = r + 2
      · subst hsTop
        exact hfull
      · have hsle : s ≤ r + 1 := by omega
        exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix_even
          hmono r (by omega) hprev s hsle

/-- Even-cube version: under a monotone normalized slice profile, a zero slice forces every higher
slice to vanish. -/
theorem card_slice_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_suffix_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmono :
      ∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r)
    {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ 2 * m + 2)
    (hzero : #(𝒟 # r) = 0) :
    #(𝒟 # s) = 0 := by
  have haux :
      ∀ t : ℕ, r + t ≤ 2 * m + 2 → #(𝒟 # (r + t)) = 0 := by
    intro t
    induction t with
    | zero =>
        intro _
        simpa using hzero
    | succ t iht =>
        intro hbound
        have hcurr : #(𝒟 # (r + t)) = 0 := iht (by omega)
        have hcurrBound : r + t ≤ 2 * m + 1 := by omega
        have hnext :
            #(𝒟 # ((r + t) + 1)) = 0 :=
          card_slice_succ_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_even
            hmono hcurrBound hcurr
        simpa [Nat.add_assoc] using hnext
  have hsub : r + (s - r) = s := Nat.add_sub_of_le hrs
  simpa [hsub] using haux (s - r) (by omega)

/-- The even minimizer selected by the compression route can be chosen with full-prefix and zero-tail
slice propagation. This is the first interval-structure theorem for the even-cube extremizer
profile. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_intervalPropagation
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r) ∧
      (∀ ⦃r s : ℕ⦄, s ≤ r → r ≤ 2 * m + 2 →
        #(𝒟 # r) = Nat.choose (2 * m + 2) r →
          #(𝒟 # s) = Nat.choose (2 * m + 2) s) ∧
      (∀ ⦃r s : ℕ⦄, r ≤ s → s ≤ 2 * m + 2 →
        #(𝒟 # r) = 0 → #(𝒟 # s) = 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono, hfullStep, hzeroStep⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_propagation m
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, ?_, ?_⟩
  · intro r s hsr hr hfull
    cases r with
    | zero =>
        have hs0 : s = 0 := by omega
        subst hs0
        simpa using hfull
    | succ r' =>
        have hr' : r' ≤ 2 * m + 1 := by omega
        have hfullTop : #(𝒟 # (r' + 1)) = Nat.choose (2 * m + 2) (r' + 1) := by
          simpa using hfull
        exact card_slice_eq_choose_of_monotoneProfile_of_card_slice_eq_choose_prefix_even
          hmono r' hr' hfullTop s hsr
  · intro r s hrs hs hzero
    exact card_slice_eq_zero_of_monotoneProfile_of_card_slice_eq_zero_suffix_even
      hmono hrs hs hzero

/-- A down-set in `P([n])` with cardinality strictly below the full cube has empty top slice. -/
theorem card_top_slice_eq_zero_of_isDownSetFamily_of_card_lt_pow
    {n : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟) (hcard : 𝒟.card < 2 ^ n) :
    #(𝒟 # n) = 0 := by
  rw [Finset.card_eq_zero]
  ext s
  constructor
  · intro hs
    rcases Finset.mem_slice.mp hs with ⟨hs𝒟, hsCard⟩
    have hsUniv : s = (Finset.univ : Finset (Fin n)) := by
      exact (Finset.card_eq_iff_eq_univ s).1 (by simpa [Fintype.card_fin] using hsCard)
    have hEq : 𝒟 = (Finset.univ : Finset (Fin n)).powerset := by
      ext t
      constructor
      · intro ht
        simp
      · intro ht
        exact h𝒟 (Finset.mem_powerset.mp ht) (hsUniv ▸ hs𝒟)
    have hEqCard : 𝒟.card = 2 ^ n := by
      simpa [hEq]
    exfalso
    exact (Nat.ne_of_lt hcard) hEqCard
  · intro hs
    simpa using hs

/-- The selected odd half-cube global minimizer has empty top slice. -/
theorem card_top_slice_eq_zero_of_isOddHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    #(𝒟 # (2 * m + 1)) = 0 := by
  rcases hmin with ⟨h𝒟, hcard, -⟩
  have hltNat : 2 ^ (2 * m) < 2 ^ (2 * m + 1) := by
    rw [show 2 * m + 1 = 2 * m + 1 by omega, Nat.pow_succ]
    have hpos : 0 < 2 ^ (2 * m) := by
      exact pow_pos (by decide : 0 < 2) _
    omega
  have hlt : 𝒟.card < 2 ^ (2 * m + 1) := by
    simpa [hcard] using hltNat
  exact card_top_slice_eq_zero_of_isDownSetFamily_of_card_lt_pow h𝒟 hlt

/-- The selected even half-cube global minimizer has empty top slice. -/
theorem card_top_slice_eq_zero_of_isEvenHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    #(𝒟 # (2 * m + 2)) = 0 := by
  rcases hmin with ⟨h𝒟, hcard, -⟩
  have hltNat : 2 ^ (2 * m + 1) < 2 ^ (2 * m + 2) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Nat.pow_succ]
    have hpos : 0 < 2 ^ (2 * m + 1) := by
      exact pow_pos (by decide : 0 < 2) _
    omega
  have hlt : 𝒟.card < 2 ^ (2 * m + 2) := by
    simpa [hcard] using hltNat
  exact card_top_slice_eq_zero_of_isDownSetFamily_of_card_lt_pow h𝒟 hlt

/-- The selected even minimizer has concrete endpoint data already: its `0`-slice is full and its
top slice is empty. This is the first actual endpoint anchoring for the even-cube extremizer
program. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceEndpoints
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 2)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 2))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 2) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 2) r) ∧
      #(𝒟 # 0) = 1 ∧
      #(𝒟 # (2 * m + 2)) = 0 := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData m
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m + 1))
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, ?_, ?_⟩
  · have hempty : (∅ : Finset (Fin (2 * m + 2))) ∈ 𝒟 :=
      empty_mem_of_nonempty_isDownSetFamily hmin.1 hne
    refine Finset.card_eq_one.mpr ?_
    refine ⟨∅, ?_⟩
    ext s
    rw [Finset.mem_slice]
    constructor
    · rintro ⟨hs𝒟, hsCard⟩
      have hsEmpty : s = ∅ := Finset.card_eq_zero.mp hsCard
      simpa [hsEmpty] using hs𝒟
    · intro hs
      have hsEmpty : s = ∅ := by simpa using hs
      subst hsEmpty
      exact ⟨hempty, by simp⟩
  · exact card_top_slice_eq_zero_of_isEvenHalfCubeBoundaryGlobalMinimizer hmin

/-- The selected even minimizer has a genuine transition window in its slice profile: a full
prefix, then a transition region, then a zero tail. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceTransitionWindow
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))), ∃ t u : ℕ,
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      t ≤ u ∧ u ≤ 2 * m + 2 ∧
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r) ∧
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 2 → #(𝒟 # r) = 0) ∧
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono, hfullPrefix, hzeroSuffix⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_intervalPropagation m
  have htop := card_top_slice_eq_zero_of_isEvenHalfCubeBoundaryGlobalMinimizer hmin
  have htopNotFull : #(𝒟 # (2 * m + 2)) ≠ Nat.choose (2 * m + 2) (2 * m + 2) := by
    simp [htop]
  let t :=
    Nat.find
      (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r from
        ⟨2 * m + 2, le_rfl, htopNotFull⟩)
  let u :=
    Nat.find
      (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) = 0 from
        ⟨2 * m + 2, le_rfl, htop⟩)
  have htSpec : t ≤ 2 * m + 2 ∧ #(𝒟 # t) ≠ Nat.choose (2 * m + 2) t := by
    exact Nat.find_spec
      (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r from
        ⟨2 * m + 2, le_rfl, htopNotFull⟩)
  have huSpec : u ≤ 2 * m + 2 ∧ #(𝒟 # u) = 0 := by
    exact Nat.find_spec
      (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) = 0 from
        ⟨2 * m + 2, le_rfl, htop⟩)
  have huNotFull : #(𝒟 # u) ≠ Nat.choose (2 * m + 2) u := by
    intro huFull
    have hchoosePos : 0 < Nat.choose (2 * m + 2) u := Nat.choose_pos huSpec.1
    omega
  have htu : t ≤ u := by
    exact Nat.find_min'
      (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r from
        ⟨2 * m + 2, le_rfl, htopNotFull⟩)
      ⟨huSpec.1, huNotFull⟩
  refine ⟨𝒟, t, u, hmin, htu, huSpec.1, ?_, ?_, ?_⟩
  · intro r hrt
    by_contra hnotFull
    have hrle : r ≤ 2 * m + 2 := by omega
    have htr : t ≤ r := by
      exact Nat.find_min'
        (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r from
          ⟨2 * m + 2, le_rfl, htopNotFull⟩)
        ⟨hrle, hnotFull⟩
    omega
  · intro r hur hrle
    exact hzeroSuffix hur hrle huSpec.2
  · intro r htr hru
    constructor
    · intro hrFull
      have hrle : r ≤ 2 * m + 2 := by omega
      have htFull : #(𝒟 # t) = Nat.choose (2 * m + 2) t :=
        hfullPrefix htr hrle hrFull
      exact htSpec.2 htFull
    · intro hrZero
      have hrle : r ≤ 2 * m + 2 := by omega
      have hur' : u ≤ r := by
        exact Nat.find_min'
          (show ∃ r : ℕ, r ≤ 2 * m + 2 ∧ #(𝒟 # r) = 0 from
            ⟨2 * m + 2, le_rfl, htop⟩)
          ⟨hrle, hrZero⟩
      omega

/-- The transition window of the selected even minimizer must contain the middle rank `m + 1`. -/
theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 2))), ∃ t u : ℕ,
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      t ≤ m + 1 ∧ m + 1 < u ∧ u ≤ 2 * m + 2 ∧
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r) ∧
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 2 → #(𝒟 # r) = 0) ∧
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) := by
  obtain ⟨𝒟, t, u, hmin, htu, hu, hfull, hzero, hmid⟩ :=
    exists_isEvenHalfCubeBoundaryGlobalMinimizer_sliceTransitionWindow m
  let n := 2 * m + 2
  let lowerMass : ℕ := Finset.sum (Finset.range (m + 2)) (fun k => #(𝒟 # k))
  let upperMass : ℕ := Finset.sum (Finset.Ico (m + 2) (n + 1)) (fun k => #(𝒟 # k))
  have hmle : m + 2 ≤ n + 1 := by
    dsimp [n]
    omega
  have hsumSlices :
      Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m + 1) := by
    simpa [Nat.range_succ_eq_Iic, hmin.2.1] using (Finset.sum_card_slice 𝒟)
  have hsplitMass :
      lowerMass + upperMass = 2 ^ (2 * m + 1) := by
    have hsplit :
        lowerMass + upperMass =
          Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
      simpa [lowerMass, upperMass] using
        (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
    exact hsplit.trans hsumSlices
  have hchoosePrefixTwice :
      2 * Finset.sum (Finset.range (m + 2)) (fun k => Nat.choose n k) =
        2 ^ (2 * m + 2) + Nat.choose n (m + 1) := by
    let q := m + 1
    have hreflect :
        Finset.sum (Finset.Ico (q + 1) (2 * q + 1)) (fun r => Nat.choose (2 * q) r) =
          Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) := by
      calc
        Finset.sum (Finset.Ico (q + 1) (2 * q + 1)) (fun r => Nat.choose (2 * q) r) =
          Finset.sum (Finset.Ico (q + 1) (2 * q + 1)) (fun r => Nat.choose (2 * q) (2 * q - r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hrle : r ≤ 2 * q := Nat.le_of_lt_succ (Finset.mem_Ico.mp hr).2
            symm
            exact Nat.choose_symm hrle
        _ = Finset.sum (Finset.range (2 * q - q)) (fun r => Nat.choose (2 * q) r) := by
            simpa [Nat.Ico_zero_eq_range] using
              (Finset.sum_Ico_reflect (f := fun r => Nat.choose (2 * q) r) (k := q + 1)
                (m := 2 * q + 1) (n := 2 * q) le_rfl)
        _ = Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) := by
            rw [show 2 * q - q = q by omega]
    have hsum :
        Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) +
          Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) =
            2 ^ (2 * q) := by
      have hq : q + 1 ≤ 2 * q + 1 := by
        omega
      calc
        Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) +
            Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) =
          Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) +
            Finset.sum (Finset.Ico (q + 1) (2 * q + 1)) (fun r => Nat.choose (2 * q) r) := by
              rw [hreflect]
        _ = Finset.sum (Finset.range (2 * q + 1)) (fun r => Nat.choose (2 * q) r) := by
              exact Finset.sum_range_add_sum_Ico (fun r => Nat.choose (2 * q) r) hq
        _ = 2 ^ (2 * q) := by
              simpa using Nat.sum_range_choose (2 * q)
    have hsucc :
        Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) =
          Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) + Nat.choose (2 * q) q := by
      rw [Finset.sum_range_succ]
    have hq1 : q + 1 = m + 2 := by
      simpa [q]
    have hnq : 2 * q = 2 * m + 2 := by
      dsimp [q]
      ring
    calc
      2 * Finset.sum (Finset.range (m + 2)) (fun k => Nat.choose n k) =
        2 * Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) := by
          simp [hq1, hnq, n]
      _ =
        Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) +
          Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) := by
            rw [two_mul]
      _ =
        Finset.sum (Finset.range (q + 1)) (fun r => Nat.choose (2 * q) r) +
          (Finset.sum (Finset.range q) (fun r => Nat.choose (2 * q) r) +
            Nat.choose (2 * q) q) := by
              rw [hsucc]
      _ = 2 ^ (2 * q) + Nat.choose (2 * q) q := by
            rw [← add_assoc, hsum]
      _ = 2 ^ (2 * m + 2) + Nat.choose n (m + 1) := by
            simp [hnq, q, n]
  have hmiddleChoosePos : 0 < Nat.choose n (m + 1) := by
    have hm1le : m + 1 ≤ n := by
      dsimp [n]
      omega
    exact Nat.choose_pos hm1le
  have hpow : 2 ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Nat.pow_succ]
    ring
  have htmid : t ≤ m + 1 := by
    by_contra hgt
    have hlt : m + 1 < t := by
      omega
    have hlowerFull :
        lowerMass = Finset.sum (Finset.range (m + 2)) (fun k => Nat.choose n k) := by
      dsimp [lowerMass]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact hfull (lt_of_le_of_lt hkle hlt)
    have hlowerLe : lowerMass ≤ 2 ^ (2 * m + 1) := by
      omega
    have htwice :
        2 * lowerMass = 2 ^ (2 * m + 2) + Nat.choose n (m + 1) := by
      rw [hlowerFull]
      exact hchoosePrefixTwice
    omega
  have humid : m + 1 < u := by
    by_contra hle
    have hule : u ≤ m + 1 := by
      omega
    let coreMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
    have hmidZero : #(𝒟 # (m + 1)) = 0 := by
      have hm1le : m + 1 ≤ n := by
        dsimp [n]
        omega
      exact hzero hule (by simpa [n] using hm1le)
    have hupperZero : upperMass = 0 := by
      dsimp [upperMass]
      apply Finset.sum_eq_zero
      intro k hk
      have hklo : m + 2 ≤ k := (Finset.mem_Ico.mp hk).1
      have huk : u ≤ k := by
        omega
      have hkhi : k ≤ n := by
        exact Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
      exact hzero huk hkhi
    have hcoreEq : coreMass = 2 ^ (2 * m + 1) := by
      have hlowerEq : lowerMass = 2 ^ (2 * m + 1) := by
        omega
      dsimp [lowerMass] at hlowerEq
      rw [Finset.sum_range_succ, hmidZero, add_zero] at hlowerEq
      simpa [coreMass] using hlowerEq
    have hcoreLe :
        coreMass ≤ Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) := by
      dsimp [coreMass]
      apply Finset.sum_le_sum
      intro k hk
      exact card_slice_le_choose (𝒟 := 𝒟) (r := k)
    have hchooseCoreLt :
        Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) < 2 ^ (2 * m + 1) := by
      have hrange :
          Finset.sum (Finset.range (m + 2)) (fun k => Nat.choose n k) =
            Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) +
              Nat.choose n (m + 1) := by
        rw [Finset.sum_range_succ]
      omega
    have hcoreLt : coreMass < 2 ^ (2 * m + 1) :=
      lt_of_le_of_lt hcoreLe hchooseCoreLt
    omega
  refine ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩

/-- If all lower slices of an even half-cube family are full, then its `0`-free section already
contains the canonical odd lower half. -/
theorem succFamily_oddLowerHalfFamily_subset_nonMemberSubfamily_of_fullLowerSlices_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hlower : ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 2) r) :
    succFamily (oddLowerHalfFamily m) ⊆ 𝒟.nonMemberSubfamily 0 := by
  intro s hs
  rcases mem_succFamily_iff.mp hs with ⟨hs0, hsOdd⟩
  have hsCard : s.card ≤ m := by
    have hsOddCard :
        #(s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn) ≤ m :=
      mem_oddLowerHalfFamily.mp hsOdd
    simpa [card_preimage_succ hs0] using hsOddCard
  have hsRange : s.card ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hsCard)
  have hslice :
      𝒟 # s.card =
        (Finset.univ : Finset (Fin (2 * m + 2))).powersetCard s.card :=
    slice_eq_powersetCard_of_card_eq_choose (hlower _ hsRange)
  have hsPow :
      s ∈ (Finset.univ : Finset (Fin (2 * m + 2))).powersetCard s.card := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  have hsSlice : s ∈ 𝒟 # s.card := by
    simpa [hslice] using hsPow
  exact mem_nonMemberSubfamily.mpr ⟨(Finset.mem_slice.mp hsSlice).1, hs0⟩

/-- Full lower slices plus balanced `0`-sections force the canonical even lower-half witness. The
remaining free parameter after the even middle-transition analysis is exactly the section balance. -/
theorem eq_evenLowerHalfFamily_of_fullLowerSlices_of_balancedZeroSections
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hlower : ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hnonSub :
      succFamily (oddLowerHalfFamily m) ⊆ 𝒟.nonMemberSubfamily 0 :=
    succFamily_oddLowerHalfFamily_subset_nonMemberSubfamily_of_fullLowerSlices_even hlower
  have hnonEq :
      succFamily (oddLowerHalfFamily m) = 𝒟.nonMemberSubfamily 0 := by
    apply Finset.eq_of_subset_of_card_le hnonSub
    simpa [hbal, card_succFamily, card_oddLowerHalfFamily_eq_half_cube]
  have hsplit :
      #(𝒟.memberSubfamily 0) + #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m + 1) := by
    simpa [hcard] using
      (Finset.card_memberSubfamily_add_card_nonMemberSubfamily (a := 0) (𝒜 := 𝒟))
  have hpow : 2 ^ (2 * m + 1) = 2 ^ (2 * m) + 2 ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, Nat.pow_succ]
    ring
  have hmemberCard : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) := by
    rw [hbal, hpow] at hsplit
    omega
  have hmemberSub :
      𝒟.memberSubfamily 0 ⊆ 𝒟.nonMemberSubfamily 0 :=
    h𝒟.memberSubfamily_subset_nonMemberSubfamily (a := 0)
  have hmemberEq :
      𝒟.memberSubfamily 0 = 𝒟.nonMemberSubfamily 0 := by
    apply Finset.eq_of_subset_of_card_le hmemberSub
    simpa [hmemberCard, hbal]
  have hnonEq' :
      𝒟.nonMemberSubfamily 0 = (evenLowerHalfFamily m).nonMemberSubfamily 0 := by
    rw [nonMemberSubfamily_evenLowerHalfFamily]
    exact hnonEq.symm
  have hmemberEq' :
      𝒟.memberSubfamily 0 = (evenLowerHalfFamily m).memberSubfamily 0 := by
    rw [memberSubfamily_evenLowerHalfFamily]
    calc
      𝒟.memberSubfamily 0 = 𝒟.nonMemberSubfamily 0 := hmemberEq
      _ = succFamily (oddLowerHalfFamily m) := hnonEq.symm
  ext s
  by_cases hs0 : (0 : Fin (2 * m + 2)) ∈ s
  · constructor
    · intro hs
      have hsMem : s.erase 0 ∈ 𝒟.memberSubfamily 0 := by
        refine mem_memberSubfamily.mpr ⟨?_, notMem_erase 0 s⟩
        simpa [Finset.insert_erase hs0] using hs
      have hsMem' : s.erase 0 ∈ (evenLowerHalfFamily m).memberSubfamily 0 := by
        simpa [hmemberEq'] using hsMem
      have hsIns := (mem_memberSubfamily.mp hsMem').1
      simpa [Finset.insert_erase hs0] using hsIns
    · intro hs
      have hsMem : s.erase 0 ∈ (evenLowerHalfFamily m).memberSubfamily 0 := by
        refine mem_memberSubfamily.mpr ⟨?_, notMem_erase 0 s⟩
        simpa [Finset.insert_erase hs0] using hs
      have hsMem' : s.erase 0 ∈ 𝒟.memberSubfamily 0 := by
        simpa [hmemberEq'] using hsMem
      have hsIns := (mem_memberSubfamily.mp hsMem').1
      simpa [Finset.insert_erase hs0] using hsIns
  · constructor
    · intro hs
      have hsNon : s ∈ 𝒟.nonMemberSubfamily 0 := mem_nonMemberSubfamily.mpr ⟨hs, hs0⟩
      have hsNon' : s ∈ (evenLowerHalfFamily m).nonMemberSubfamily 0 := by
        simpa [hnonEq'] using hsNon
      exact (mem_nonMemberSubfamily.mp hsNon').1
    · intro hs
      have hsNon : s ∈ (evenLowerHalfFamily m).nonMemberSubfamily 0 :=
        mem_nonMemberSubfamily.mpr ⟨hs, hs0⟩
      have hsNon' : s ∈ 𝒟.nonMemberSubfamily 0 := by
        simpa [hnonEq'] using hsNon
      exact (mem_nonMemberSubfamily.mp hsNon').1

/-- Canonical even transition shape collapses to `evenLowerHalfFamily` as soon as the `0`-sections
are balanced. This isolates the remaining prism bottleneck to proving that balance. -/
theorem eq_evenLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle_of_balancedZeroSections
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (htEq : t = m + 1)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hlower : ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 2) r := by
    intro r hr
    have hrt : r < t := by
      rw [htEq]
      exact Finset.mem_range.mp hr
    exact hfull hrt
  exact
    eq_evenLowerHalfFamily_of_fullLowerSlices_of_balancedZeroSections
      hmin.1 hmin.2.1 hlower hbal

/-- The odd minimizer selected by the compression route can be chosen with concrete endpoint data:
its `0`-slice is full and its top slice is empty. This is the first actual transition anchoring for
the candidate profile. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceTransitionEndpoints
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      (∀ r : ℕ, ∂ (𝒟 # (r + 1)) ⊆ 𝒟 # r) ∧
      (∀ ⦃r : ℕ⦄ ⦃i j : Fin (2 * m + 1)⦄, i < j →
        ∀ ⦃s : Finset (Fin (2 * m + 1))⦄,
          s ∈ (𝒟 # r) → i ∉ s → j ∈ s → swapCoord i j s ∈ (𝒟 # r)) ∧
      (∀ r : ℕ,
        ((#(𝒟 # (r + 1)) : ℚ) / Nat.choose (2 * m + 1) (r + 1)) ≤
          (#(𝒟 # r) : ℚ) / Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r s : ℕ⦄, s ≤ r → r ≤ 2 * m + 1 →
        #(𝒟 # r) = Nat.choose (2 * m + 1) r →
          #(𝒟 # s) = Nat.choose (2 * m + 1) s) ∧
      (∀ ⦃r s : ℕ⦄, r ≤ s → s ≤ 2 * m + 1 →
        #(𝒟 # r) = 0 → #(𝒟 # s) = 0) ∧
      #(𝒟 # 0) = 1 ∧
      #(𝒟 # (2 * m + 1)) = 0 := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono, hfullPrefix, hzeroSuffix⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceCandidateData_intervalPropagation m
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  refine ⟨𝒟, hmin, hshadow, hshift, hmono, hfullPrefix, hzeroSuffix, ?_, ?_⟩
  · have hempty : (∅ : Finset (Fin (2 * m + 1))) ∈ 𝒟 :=
      empty_mem_of_nonempty_isDownSetFamily hmin.1 hne
    refine Finset.card_eq_one.mpr ?_
    refine ⟨∅, ?_⟩
    ext s
    rw [Finset.mem_slice]
    constructor
    · rintro ⟨hs𝒟, hsCard⟩
      have hsEmpty : s = ∅ := Finset.card_eq_zero.mp hsCard
      simpa [hsEmpty] using hs𝒟
    · intro hs
      have hsEmpty : s = ∅ := by simpa using hs
      subst hsEmpty
      exact ⟨hempty, by simp⟩
  · exact card_top_slice_eq_zero_of_isOddHalfCubeBoundaryGlobalMinimizer hmin

/-- The selected odd minimizer has a genuine transition window in its slice profile: a full
prefix, then a transition region, then a zero tail. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceTransitionWindow
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))), ∃ t u : ℕ,
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      t ≤ u ∧ u ≤ 2 * m + 1 ∧
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) ∧
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) := by
  obtain ⟨𝒟, hmin, hshadow, hshift, hmono, hfullPrefix, hzeroSuffix, h0, htop⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceTransitionEndpoints m
  have htopNotFull : #(𝒟 # (2 * m + 1)) ≠ Nat.choose (2 * m + 1) (2 * m + 1) := by
    simp [htop]
  let t :=
    Nat.find
      (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r from
        ⟨2 * m + 1, le_rfl, htopNotFull⟩)
  let u :=
    Nat.find
      (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) = 0 from
        ⟨2 * m + 1, le_rfl, htop⟩)
  have htSpec : t ≤ 2 * m + 1 ∧ #(𝒟 # t) ≠ Nat.choose (2 * m + 1) t := by
    exact Nat.find_spec
      (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r from
        ⟨2 * m + 1, le_rfl, htopNotFull⟩)
  have huSpec : u ≤ 2 * m + 1 ∧ #(𝒟 # u) = 0 := by
    exact Nat.find_spec
      (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) = 0 from
        ⟨2 * m + 1, le_rfl, htop⟩)
  have huNotFull : #(𝒟 # u) ≠ Nat.choose (2 * m + 1) u := by
    intro huFull
    have hchoosePos : 0 < Nat.choose (2 * m + 1) u := Nat.choose_pos huSpec.1
    omega
  have htu : t ≤ u := by
    exact Nat.find_min'
      (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r from
        ⟨2 * m + 1, le_rfl, htopNotFull⟩)
      ⟨huSpec.1, huNotFull⟩
  refine ⟨𝒟, t, u, hmin, htu, huSpec.1, ?_, ?_, ?_⟩
  · intro r hrt
    by_contra hnotFull
    have hrle : r ≤ 2 * m + 1 := by omega
    have htr : t ≤ r := by
      exact Nat.find_min'
        (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r from
          ⟨2 * m + 1, le_rfl, htopNotFull⟩)
        ⟨hrle, hnotFull⟩
    omega
  · intro r hur hrle
    exact hzeroSuffix hur hrle huSpec.2
  · intro r htr hru
    constructor
    · intro hrFull
      have hrle : r ≤ 2 * m + 1 := by omega
      have htFull : #(𝒟 # t) = Nat.choose (2 * m + 1) t :=
        hfullPrefix htr hrle hrFull
      exact htSpec.2 htFull
    · intro hrZero
      have hrle : r ≤ 2 * m + 1 := by omega
      have hur' : u ≤ r := by
        exact Nat.find_min'
          (show ∃ r : ℕ, r ≤ 2 * m + 1 ∧ #(𝒟 # r) = 0 from
            ⟨2 * m + 1, le_rfl, htop⟩)
          ⟨hrle, hrZero⟩
      omega

/-- The transition window of the selected odd minimizer must straddle the middle rank `m + 1`. -/
theorem exists_isOddHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow
    (m : ℕ) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))), ∃ t u : ℕ,
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 ∧
      t ≤ m + 1 ∧ m + 1 ≤ u ∧ u ≤ 2 * m + 1 ∧
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) ∧
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) := by
  obtain ⟨𝒟, t, u, hmin, htu, hu, hfull, hzero, hmid⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_sliceTransitionWindow m
  let n := 2 * m + 1
  let lowerMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
  let upperMass : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k))
  have hmle : m + 1 ≤ n + 1 := by
    dsimp [n]
    omega
  have hsumSlices :
      Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m) := by
    simpa [Nat.range_succ_eq_Iic, hmin.2.1] using (Finset.sum_card_slice 𝒟)
  have hsplitMass :
      lowerMass + upperMass = 2 ^ (2 * m) := by
    have hsplit :
        lowerMass + upperMass =
          Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
      simpa [lowerMass, upperMass] using
        (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
    exact hsplit.trans hsumSlices
  have hchooseHalf :
      Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) = 2 ^ (2 * m) := by
    dsimp [n]
    simpa [show 4 ^ m = 2 ^ (2 * m) by
      rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using Nat.sum_range_choose_halfway m
  have htmid : t ≤ m + 1 := by
    by_contra hgt
    have hlt : m + 1 < t := by omega
    have hlowerFull : lowerMass = 2 ^ (2 * m) := by
      calc
        lowerMass = Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hfull (lt_trans (Finset.mem_range.mp hk) hlt)
        _ = 2 ^ (2 * m) := hchooseHalf
    have hupperZero : upperMass = 0 := by
      omega
    have hmidFull : #(𝒟 # (m + 1)) = Nat.choose n (m + 1) := by
      exact hfull hlt
    have hmidPos : 0 < #(𝒟 # (m + 1)) := by
      rw [hmidFull]
      have hm1le : m + 1 ≤ n := by
        dsimp [n]
        omega
      exact Nat.choose_pos hm1le
    have hmidLe : #(𝒟 # (m + 1)) ≤ upperMass := by
      dsimp [upperMass]
      have hmem : m + 1 ∈ Finset.Ico (m + 1) (n + 1) := by
        exact Finset.mem_Ico.mpr ⟨le_rfl, by dsimp [n]; omega⟩
      exact
        Finset.single_le_sum (f := fun k => #(𝒟 # k))
          (fun _ _ => Nat.zero_le _) hmem
    omega
  have humid : m + 1 ≤ u := by
    by_contra hlt
    have hule : u ≤ m := by omega
    have hupperZero : upperMass = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklo : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkhi : k ≤ n := by
        exact Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
      have huk : u ≤ k := by
        omega
      exact hzero huk hkhi
    have hlowerEq : lowerMass = 2 ^ (2 * m) := by
      omega
    have hsliceMzero : #(𝒟 # m) = 0 := by
      have hmle' : m ≤ n := by
        dsimp [n]
        omega
      exact hzero hule hmle'
    have hlowerLe :
        Finset.sum (Finset.range m) (fun k => #(𝒟 # k)) ≤
          Finset.sum (Finset.range m) (fun k => Nat.choose n k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact card_slice_le_choose (𝒟 := 𝒟) (r := k)
    have hchooseMidPos : 0 < Nat.choose n m := by
      have hmle' : m ≤ n := by
        dsimp [n]
        omega
      exact Nat.choose_pos hmle'
    have hchooseRangeM :
        Finset.sum (Finset.range m) (fun k => Nat.choose n k) < 2 ^ (2 * m) := by
      have hsplitChoose :
          Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) =
            Finset.sum (Finset.range m) (fun k => Nat.choose n k) + Nat.choose n m := by
        rw [Finset.sum_range_succ]
      omega
    have hlowerLt : lowerMass < 2 ^ (2 * m) := by
      dsimp [lowerMass]
      rw [Finset.sum_range_succ, hsliceMzero]
      exact lt_of_le_of_lt hlowerLe hchooseRangeM
    omega
  refine ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩

/-- If the zero tail of a middle transition window starts exactly at the middle layer, then the
odd minimizer is the standard lower-half family. -/
theorem eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 ≤ u) (hu : u ≤ 2 * m + 1)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r)
    (hzero : ∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0)
    (huEq : u = m + 1) :
    𝒟 = oddLowerHalfFamily m := by
  let n := 2 * m + 1
  have hupper : ∀ r, m + 1 ≤ r → #(𝒟 # r) = 0 := by
    intro r hr
    by_cases hrn : r ≤ n
    · exact hzero (huEq ▸ hr) (by simpa [n] using hrn)
    · have hle := card_slice_le_choose (𝒟 := 𝒟) (r := r)
      have hchoose0 : Nat.choose n r = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hrn)
      rw [Finset.card_eq_zero]
      ext s
      constructor
      · intro hs
        have hsle : s.card ≤ n := by
          simpa [n] using (Finset.card_le_univ (s := s))
        rcases Finset.mem_slice.mp hs with ⟨_, hsCard⟩
        have hrle : r ≤ n := by
          simpa [hsCard] using hsle
        exact (hrn hrle).elim
      · intro hs
        simpa using hs
  have htEq : t = m + 1 := by
    by_contra hneq
    have hlt : t < m + 1 := lt_of_le_of_ne htmid hneq
    let lowerMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
    let upperMass : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k))
    have hmle : m + 1 ≤ n + 1 := by
      dsimp [n]
      omega
    have hsumSlices :
        Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m) := by
      simpa [Nat.range_succ_eq_Iic, hmin.2.1] using (Finset.sum_card_slice 𝒟)
    have hupperMass : upperMass = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact hupper k (Finset.mem_Ico.mp hk).1
    have hchooseHalf :
        Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) = 2 ^ (2 * m) := by
      dsimp [n]
      simpa [show 4 ^ m = 2 ^ (2 * m) by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using Nat.sum_range_choose_halfway m
    have hlowerEq : lowerMass = 2 ^ (2 * m) := by
      have hsplit :
          lowerMass + upperMass = 2 ^ (2 * m) := by
        have hsplit' :
            lowerMass + upperMass =
              Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
          simpa [lowerMass, upperMass] using
            (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
        exact hsplit'.trans hsumSlices
      rw [hupperMass, add_zero] at hsplit
      exact hsplit
    have hlowerLt : lowerMass < 2 ^ (2 * m) := by
      calc
        lowerMass < Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) := by
          refine Finset.sum_lt_sum (fun k hk => card_slice_le_choose (𝒟 := 𝒟) (r := k)) ?_
          have htmem : t ∈ Finset.range (m + 1) := Finset.mem_range.mpr hlt
          have hstrict : #(𝒟 # t) < Nat.choose n t := by
            exact lt_of_le_of_ne
              (card_slice_le_choose (𝒟 := 𝒟) (r := t))
              (hmid le_rfl (huEq ▸ hlt)).1
          exact ⟨t, htmem, hstrict⟩
        _ = 2 ^ (2 * m) := hchooseHalf
    omega
  have hlower : ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r := by
    intro r hr
    have hrt : r < t := by
      rw [htEq]
      exact Finset.mem_range.mp hr
    exact hfull hrt
  exact eq_oddLowerHalfFamily_of_exact_slice_profile hlower hupper

/-- Symmetric middle collapse criterion: if the full prefix reaches exactly the middle layer, then
the odd minimizer is already the standard lower-half family. -/
theorem eq_oddLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 ≤ u) (hu : u ≤ 2 * m + 1)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r)
    (hzero : ∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0)
    (htEq : t = m + 1) :
    𝒟 = oddLowerHalfFamily m := by
  by_cases huEq : u = m + 1
  · exact
      eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
        hmin htmid humid hu hfull hzero hmid huEq
  · let n := 2 * m + 1
    let lowerMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
    let upperMass : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k))
    have hmle : m + 1 ≤ n + 1 := by
      dsimp [n]
      omega
    have hsumSlices :
        Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m) := by
      simpa [Nat.range_succ_eq_Iic, hmin.2.1] using (Finset.sum_card_slice 𝒟)
    have hsplitMass :
        lowerMass + upperMass = 2 ^ (2 * m) := by
      have hsplit :
          lowerMass + upperMass =
            Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
        simpa [lowerMass, upperMass] using
          (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
      exact hsplit.trans hsumSlices
    have hchooseHalf :
        Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) = 2 ^ (2 * m) := by
      dsimp [n]
      simpa [show 4 ^ m = 2 ^ (2 * m) by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using Nat.sum_range_choose_halfway m
    have hlowerMass : lowerMass = 2 ^ (2 * m) := by
      calc
        lowerMass = Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < t := by
            simpa [htEq] using Finset.mem_range.mp hk
          exact hfull hklt
        _ = 2 ^ (2 * m) := hchooseHalf
    have hltu : m + 1 < u := lt_of_le_of_ne humid (Ne.symm huEq)
    have hslicePos : 0 < #(𝒟 # (m + 1)) := by
      exact Nat.pos_of_ne_zero (hmid (by simpa [htEq]) hltu).2
    have hupperPos : 0 < upperMass := by
      dsimp [upperMass]
      have hmem : m + 1 ∈ Finset.Ico (m + 1) (n + 1) := by
        exact Finset.mem_Ico.mpr ⟨le_rfl, by dsimp [n]; omega⟩
      have hle :
          #(𝒟 # (m + 1)) ≤
            Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k)) :=
        Finset.single_le_sum (f := fun k => #(𝒟 # k)) (fun _ _ => Nat.zero_le _) hmem
      exact lt_of_lt_of_le hslicePos hle
    omega

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
      Finset.sum (Finset.range (n + 1)) (fun r => #(𝒟 # r)) =
        𝒟.card := by
    simpa [n, Nat.range_succ_eq_Iic] using hsumNat'
  rw [Finset.sum_range_succ'] at hsumNat
  have hslice0_le : #(𝒟 # 0) ≤ 𝒟.card := by
    exact
      (Nat.le.intro (n := #(𝒟 # 0))
        (m := 𝒟.card)
        (k := Finset.sum (Finset.range n) (fun r => #(𝒟 # (r + 1))))
        (by simpa [Nat.add_comm] using hsumNat))
  symm
  exact (Nat.sub_eq_iff_eq_add hslice0_le).2 (by
    simpa [Nat.add_comm] using hsumNat.symm)

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
  · intro hs
    have hsEmpty : s = ∅ := by simpa using hs
    subst hsEmpty
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

/-- For down-sets, the upper-shadow-gap formulation is also a direct consequence of the boundary
theorem, since the gap equals the full positive-boundary cardinality. -/
theorem halfCubeUpperShadowGapLower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement) :
    HalfCubeUpperShadowGapLowerStatement := by
  intro α _ _ 𝒟 hn hne h𝒟 hcard
  have hCube' :
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ #(positiveBoundary 𝒟) :=
    hCube hn hne h𝒟 hcard
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hCube'

/-- The upper-shadow-gap and positive-boundary formulations are equivalent theorem surfaces on
down-sets. -/
theorem halfCubeBoundaryLower_iff_halfCubeUpperShadowGapLower :
    HalfCubeBoundaryLowerStatement ↔ HalfCubeUpperShadowGapLowerStatement := by
  constructor
  · exact halfCubeUpperShadowGapLower_of_halfCubeBoundaryLower
  · exact halfCubeBoundaryLower_of_halfCubeUpperShadowGapLower

/-- Odd-dimensional upper-shadow-gap reformulation of the balanced half-cube theorem. -/
def OddHalfCubeUpperShadowGapLowerStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      Nat.choose (2 * m + 1) m ≤ upperShadowGap 𝒟

/-- A possible replacement direct-route surface: if an odd half-cube down-set has larger
`totalSize` than the lower-half witness, then its upper-shadow gap is already strictly above the
middle binomial coefficient. -/
def OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Weighted-drop analogue of the odd larger-`totalSize` frontier: if an odd half-cube down-set
has larger `totalSize` than the lower-half witness, then the weighted-drop functional should
already be strictly above the middle binomial coefficient. This is the cleanest current
weighted-drop surface after reducing away the explicit slice-geometry hypotheses. -/
def OddHalfCubeLargerTotalSizeThanWitnessForcesStrictWeightedDropStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

/-- Local remaining even-cube frontier after the balanced branch has been reduced to the odd
larger-`totalSize` route: on an even half-cube global boundary minimizer, strict excess in the
coordinate-`0` free section together with larger `totalSize` than the witness should already force
strictly larger boundary than the middle binomial coefficient. -/
def EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))},
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      totalSize (evenLowerHalfFamily m) < totalSize 𝒟 →
      2 ^ (2 * m) < #(𝒟.nonMemberSubfamily 0) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary 𝒟)

/-- Odd two-sheet strict route for the remaining even local obstruction: if nested odd sheets with
positive excess package into a prism family with larger `totalSize` than the diagonal witness,
their visible pair-interface boundary should already beat the even middle binomial threshold. -/
def OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement :
    Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      totalSize (evenLowerHalfFamily m) < totalSize 𝒩 + totalSize ℳ + ℳ.card →
      Nat.choose (2 * m + 2) (m + 1) <
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ)

/-- Localized odd two-sheet strict route: it is enough to understand the first rank where the two
odd sheets genuinely separate. Before that rank, the sheets agree slice-by-slice; at that rank,
the upper sheet has strictly fewer sets than the lower sheet. -/
def OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ ⦃r : ℕ⦄, r < q → #(ℳ # r) = #(𝒩 # r)) →
      #(ℳ # q) < #(𝒩 # q) →
      totalSize (evenLowerHalfFamily m) < totalSize 𝒩 + totalSize ℳ + ℳ.card →
      Nat.choose (2 * m + 2) (m + 1) <
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ)

/-- Further-localized odd two-sheet strict route: it is enough to understand the first positive
slice of the gap family `𝒩 \ ℳ`. Equivalently, the sheets coincide on all lower ranks, and then
the first nonzero gap slice already forces strict pair-interface growth. -/
def OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q, #(((𝒩 \ ℳ) # s)) = 0) →
      0 < #(((𝒩 \ ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize 𝒩 + totalSize ℳ + ℳ.card →
      Nat.choose (2 * m + 2) (m + 1) <
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ)

/-- Narrowed odd direct-route surface: it is enough to prove strict upper-shadow-gap growth only
for the specific odd half-cube global minimizers with middle transition-window data isolated by the
compression/rigidity program. -/
def OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t ≤ m + 1 →
      m + 1 ≤ u →
      u ≤ 2 * m + 1 →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Further-localized odd direct-route surface: after the endpoint-collapse lemmas, it is enough to
handle only genuinely wide middle transition windows `t < m+1 < u`. -/
def OddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t < m + 1 →
      m + 1 < u →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Weighted-drop localization of the odd direct route: it is enough to prove strict weighted-drop
growth only for the specific odd half-cube global minimizers with middle transition-window data
isolated by the compression/rigidity program. -/
def OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDropStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t ≤ m + 1 →
      m + 1 ≤ u →
      u ≤ 2 * m + 1 →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

/-- Further-localized weighted-drop odd route: after the endpoint-collapse lemmas, it is enough to
handle only genuinely wide middle transition windows `t < m+1 < u`. -/
def OddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDropStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t < m + 1 →
      m + 1 < u →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

theorem oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
    (hGap : OddHalfCubeUpperShadowGapLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  have hGap' : Nat.choose (2 * m + 1) m ≤ upperShadowGap 𝒟 :=
    hGap h𝒟 hcard
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hGap'

theorem oddHalfCubeUpperShadowGapLower_of_oddHalfCubeBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  have hOdd' : Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
    hOdd h𝒟 hcard
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hOdd'

theorem oddHalfCubeBoundaryLower_iff_oddHalfCubeUpperShadowGapLower :
    OddHalfCubeBoundaryLowerStatement ↔ OddHalfCubeUpperShadowGapLowerStatement := by
  constructor
  · exact oddHalfCubeUpperShadowGapLower_of_oddHalfCubeBoundaryLower
  · exact oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower

/-- Direct strict-gap candidate for the odd balanced theorem: on a genuine odd half-cube global
boundary minimizer, any nonzero lower positive-boundary slice should already force the upper
shadow gap strictly above the middle binomial coefficient. Combined with the witness upper bound on
global minimizers, this would rule out lower boundary slices entirely. -/
def OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      (∃ r ∈ Finset.Icc 1 m, 0 < #((positiveBoundary 𝒟) # r)) →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Local version of the strict odd upper-shadow-gap target: if the initial segment of slices is
already full and the next slice is strictly deficient, then the full upper-shadow gap should jump
strictly above the middle binomial coefficient. This isolates the actual remaining direct-route gap
after the lower-slice propagation lemmas. -/
def OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      r < m →
      (∀ s, s ≤ r →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s) →
      #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1) →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Outside-slice form of the remaining local odd frontier: if the outside slices up to rank `r`
all vanish and the next outside slice is nonempty, then the upper-shadow gap is already strictly
above the middle binomial layer. This is the same local geometry as the current live route, but in
the exact language of the outside-slice/local-LYM machinery. -/
def OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      r < m →
      (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
      0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Further-localized odd route: it is enough to prove the first-positive-outside-slice strict-gap
statement only on actual odd half-cube global minimizers. -/
def OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement :
    Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      r < m →
      (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
      0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

/-- Even more local minimizer-only odd route: on a genuine odd half-cube global minimizer, the
outside slices cannot have a first positive level below the middle. This packages the witness upper
bound on global minimizers directly into the local target. -/
def OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      r < m →
      (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
      0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
      False

/-- Local odd contradiction surface behind the outside-slice route: on a genuine odd half-cube
global minimizer, one should not be able to have all slices up to `r` full and the next slice
strictly deficient. The wide-window/outside-slice geometry is only a way of manufacturing this
local configuration. -/
def OddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossibleStatement :
    Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      r < m →
      (∀ s, s ≤ r →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s) →
      #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1) →
      False

/-- Further localization of the live odd-side contradiction route: it is enough to rule out a
first positive outside slice only for the specific middle-transition-window global minimizers
produced by the compression/rigidity program. -/
def OddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t ≤ m + 1 →
      m + 1 ≤ u →
      u ≤ 2 * m + 1 →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      ∀ {r : ℕ}, r < m →
        (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
        0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
        False

/-- Further localization of the live odd-side contradiction route: after the endpoint-collapse
lemmas, it is enough to rule out a first positive outside slice only for genuine wide middle
windows `t < m+1 < u`. -/
def OddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement : Prop :=
  ∀ {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      t < m + 1 →
      m + 1 < u →
      (∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r) →
      (∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0) →
      (∀ ⦃r : ℕ⦄, t ≤ r → r < u →
        #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) →
      ∀ {r : ℕ}, r < m →
        (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
        0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
        False

/-- Closest local-LYM/weighted-drop formulation of the live odd frontier: on a genuine odd
half-cube global minimizer, a first positive outside slice below the middle should already force
the weighted-drop functional strictly above the middle binomial coefficient. Since weightedDrop is
always bounded above by the positive boundary, this immediately yields a contradiction. -/
def OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement :
    Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟 →
      r < m →
      (∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0) →
      0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

/-- Weighted-drop version of the local odd slice-deficit frontier: if the initial segment of
slices is full and the next slice is strictly deficient, then the weighted-drop functional should
already jump strictly above the middle binomial coefficient. This is the cleanest remaining
weighted-drop target after the outside-slice and transition-window reductions. -/
def OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      r < m →
      (∀ s, s ≤ r →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s) →
      #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1) →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

/-- Weighted-drop version of the first-bad-boundary-slice frontier. This is the direct bridge
from vanishing lower boundary slices plus a first positive boundary slice to the remaining
weighted-drop contradiction target. -/
def OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      r < m →
      (∀ s ∈ Finset.Icc 1 r, #((positiveBoundary 𝒟) # s) = 0) →
      0 < #((positiveBoundary 𝒟) # (r + 1)) →
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟)

theorem slice_zero_eq_powersetCard_zero_oddHalfCubeMinimalOutsideCounterexample :
    oddHalfCubeMinimalOutsideCounterexample # 0 =
      (Finset.univ : Finset (Fin 3)).powersetCard 0 := by
  decide

theorem card_slice_one_oddHalfCubeMinimalOutsideCounterexample :
    #(oddHalfCubeMinimalOutsideCounterexample # 1) = 2 := by
  decide

theorem not_OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement :
    ¬ OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement := by
  intro h
  have hstrict :
      Nat.choose 3 1 <
        weightedDrop (Fintype.card (Fin 3))
          (sliceDensity oddHalfCubeMinimalOutsideCounterexample) := by
    exact
      h (m := 1) (r := 0) (𝒟 := oddHalfCubeMinimalOutsideCounterexample)
        isDownSetFamily_oddHalfCubeMinimalOutsideCounterexample
        card_oddHalfCubeMinimalOutsideCounterexample
        (by omega)
        (by
          intro s hs
          have hs0 : s = 0 := by omega
          subst hs0
          simpa using slice_zero_eq_powersetCard_zero_oddHalfCubeMinimalOutsideCounterexample)
        (by
          rw [card_slice_one_oddHalfCubeMinimalOutsideCounterexample]
          decide)
  exact
    (not_lt_of_ge (le_of_lt hstrict))
      weightedDrop_lt_choose_middle_oddHalfCubeMinimalOutsideCounterexample

theorem not_OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement :
    ¬ OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement := by
  intro h
  have hstrict :
      Nat.choose 3 1 <
        weightedDrop (Fintype.card (Fin 3))
          (sliceDensity oddHalfCubeMinimalOutsideCounterexample) := by
    exact
      h (m := 1) (r := 0) (𝒟 := oddHalfCubeMinimalOutsideCounterexample)
        isDownSetFamily_oddHalfCubeMinimalOutsideCounterexample
        card_oddHalfCubeMinimalOutsideCounterexample
        (by omega)
        (by
          intro s hs
          exfalso
          simpa using hs)
        (by simpa using lower_boundary_slice_pos_oddHalfCubeMinimalOutsideCounterexample)
  exact
    (not_lt_of_ge (le_of_lt hstrict))
      weightedDrop_lt_choose_middle_oddHalfCubeMinimalOutsideCounterexample

/-- Intermediate local surface for the direct odd route: once one isolates the first nonzero lower
boundary slice, that first bad slice alone should force the global upper-shadow gap to be
strictly above the middle binomial coefficient. -/
def OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement : Prop :=
  ∀ {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))},
      IsDownSetFamily 𝒟 →
      𝒟.card = 2 ^ (2 * m) →
      r < m →
      (∀ s ∈ Finset.Icc 1 r, #((positiveBoundary 𝒟) # s) = 0) →
      0 < #((positiveBoundary 𝒟) # (r + 1)) →
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟

theorem oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeUpperShadowGapLower_and_positiveExcessPairInterfaceBoundaryLower :
    OddSectionPairInterfaceBoundaryLowerStatement ↔
      (OddHalfCubeUpperShadowGapLowerStatement ∧
        OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) := by
  constructor
  · intro hPair
    rcases
        oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeBoundaryLower_and_positiveExcessPairInterfaceBoundaryLower.mp
          hPair with ⟨hOdd, hPos⟩
    exact ⟨oddHalfCubeUpperShadowGapLower_of_oddHalfCubeBoundaryLower hOdd, hPos⟩
  · rintro ⟨hGap, hPos⟩
    exact
      oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
        (oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower hGap) hPos

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
    simpa [card_compls, hsymm] using hcard
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
    _ = #(positiveBoundary 𝒟) := by
      simpa using sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)

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
    exact Finset.sum_le_sum fun r hr => by
      have hlocal :=
        choose_sub_sub_card_slice_succ_le_card_positiveBoundary_slice_succ_of_card_slice_ge_choose_sub
          (𝒟 := 𝒟) h𝒟 (hj r hr) (Finset.mem_range.mp hr) (hcard r hr)
      omega
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
      have hpb :=
        sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)
      have hslice :=
        sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily hne h𝒟
      have hpb' :
          Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) =
            #(positiveBoundary 𝒟) := by
        simpa using hpb
      have hslice' :
          Finset.sum (Finset.range n) (fun r => #(𝒟 # (r + 1))) =
            𝒟.card - 1 := by
        simpa using hslice
      calc
        Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) +
            Finset.sum (Finset.range n) (fun r => #(𝒟 # (r + 1))) =
          #(positiveBoundary 𝒟) + Finset.sum (Finset.range n) (fun r => #(𝒟 # (r + 1))) := by
          rw [hpb']
        _ = #(positiveBoundary 𝒟) + (𝒟.card - 1) := by
          rw [hslice']
    _ ≤ #(positiveBoundary 𝒟) + 𝒟.card - 1 := by
      simpa [Nat.add_sub_assoc (Finset.one_le_card.mpr hne)]

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
  have hsum :
      Finset.sum s (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
        Finset.sum s
          (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := by
    exact Finset.sum_le_sum fun r hr => by
      have hlocal :=
        choose_sub_sub_card_slice_succ_le_card_positiveBoundary_slice_succ_of_card_slice_ge_choose_sub
          (𝒟 := 𝒟) h𝒟 (hj r hr) (Finset.mem_range.mp (hs hr)) (hcard r hr)
      omega
  have hboundary :
      Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1))) ≤
        #(positiveBoundary 𝒟) := by
    calc
      Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1))) ≤
        Finset.sum (Finset.range n) (fun r => #((positiveBoundary 𝒟) # (r + 1))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => Nat.zero_le _
      _ = #(positiveBoundary 𝒟) := by
        simpa using
          sum_card_positiveBoundary_slice_succ_eq_card_positiveBoundary_nat (𝒟 := 𝒟)
  calc
    Finset.sum s (fun r => Nat.choose (n - j r) (r - j r + 1)) ≤
      Finset.sum s
        (fun r => #((positiveBoundary 𝒟) # (r + 1)) + #(𝒟 # (r + 1))) := hsum
    _ =
        Finset.sum s (fun r => #((positiveBoundary 𝒟) # (r + 1))) +
          Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
      rw [Finset.sum_add_distrib]
    _ ≤ #(positiveBoundary 𝒟) + Finset.sum s (fun r => #(𝒟 # (r + 1))) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hboundary (Finset.sum s (fun r => #(𝒟 # (r + 1))))

/-- The lower-half shifted binomial sum in odd dimension. -/
theorem sum_range_choose_succ_halfway_odd (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) =
      2 ^ (2 * m) - 1 + Nat.choose (2 * m + 1) m := by
  have hhalf :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) =
        2 ^ (2 * m) := by
    simpa [show 4 ^ m = 2 ^ (2 * m) by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using
      Nat.sum_range_choose_halfway m
  have hshift :
      Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 1) r) =
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) + 1 := by
    simpa using
      (Finset.sum_range_succ' (f := fun r => Nat.choose (2 * m + 1) r) (n := m + 1))
  have hsucc :
      Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 1) r) =
        2 ^ (2 * m) + Nat.choose (2 * m + 1) (m + 1) := by
    rw [Finset.sum_range_succ]
    simpa [hhalf]
  have hmain :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) + 1 =
        2 ^ (2 * m) + Nat.choose (2 * m + 1) (m + 1) := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) + 1 =
        Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 1) r) := by
        symm
        exact hshift
      _ = 2 ^ (2 * m) + Nat.choose (2 * m + 1) (m + 1) := hsucc
  rw [Nat.choose_symm_half] at hmain
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  omega

/-- The doubled lower-half binomial sum in even dimension. -/
theorem two_mul_sum_range_choose_halfway_even (m : ℕ) :
    2 * Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) =
      2 ^ (2 * m) + Nat.choose (2 * m) m := by
  have hreflect :
      Finset.sum (Finset.Ico (m + 1) (2 * m + 1)) (fun r => Nat.choose (2 * m) r) =
        Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) := by
    calc
      Finset.sum (Finset.Ico (m + 1) (2 * m + 1)) (fun r => Nat.choose (2 * m) r) =
        Finset.sum (Finset.Ico (m + 1) (2 * m + 1)) (fun r => Nat.choose (2 * m) (2 * m - r)) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have hrle : r ≤ 2 * m := Nat.le_of_lt_succ (Finset.mem_Ico.mp hr).2
        symm
        exact Nat.choose_symm hrle
      _ = Finset.sum (Finset.range (2 * m - m)) (fun r => Nat.choose (2 * m) r) := by
        simpa [Nat.Ico_zero_eq_range] using
          (Finset.sum_Ico_reflect (f := fun r => Nat.choose (2 * m) r) (k := m + 1)
            (m := 2 * m + 1) (n := 2 * m) le_rfl)
      _ = Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) := by
        rw [show 2 * m - m = m by omega]
  have hsum :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) +
        Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) =
          2 ^ (2 * m) := by
    have hm : m + 1 ≤ 2 * m + 1 := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using
        Nat.add_le_add_right (Nat.le_add_left m m) 1
    calc
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) +
          Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) =
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) +
          Finset.sum (Finset.Ico (m + 1) (2 * m + 1)) (fun r => Nat.choose (2 * m) r) := by
        rw [hreflect]
      _ = Finset.sum (Finset.range (2 * m + 1)) (fun r => Nat.choose (2 * m) r) := by
        exact Finset.sum_range_add_sum_Ico (fun r => Nat.choose (2 * m) r) hm
      _ = 2 ^ (2 * m) := by
        simpa using Nat.sum_range_choose (2 * m)
  have hsucc :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) =
        Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) + Nat.choose (2 * m) m := by
    rw [Finset.sum_range_succ]
  calc
    2 * Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) =
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) +
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) := by
      rw [two_mul]
    _ =
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) +
        (Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m) r) +
          Nat.choose (2 * m) m) := by
      rw [hsucc]
    _ = 2 ^ (2 * m) + Nat.choose (2 * m) m := by
      rw [← add_assoc, hsum]

/-- The doubled interior lower-half binomial sum in even dimension. -/
theorem two_mul_sum_Icc_choose_even (m : ℕ) :
    2 * Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) =
      (2 ^ (2 * m) + Nat.choose (2 * m) m) - 2 := by
  have hsplit :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) =
        1 + Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) := by
    rw [show Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) by
      ext r
      constructor
      · intro hr
        rw [Finset.mem_insert, Finset.mem_Icc]
        by_cases h0 : r = 0
        · exact Or.inl h0
        · right
          exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0), Nat.le_of_lt_succ (Finset.mem_range.mp hr)⟩
      · intro hr
        rw [Finset.mem_insert, Finset.mem_Icc] at hr
        rcases hr with rfl | ⟨hr1, hrm⟩
        · exact Finset.mem_range.mpr (by positivity)
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hrm)]
    simp
  have hEq :
      2 * Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) + 2 =
        2 ^ (2 * m) + Nat.choose (2 * m) m := by
    calc
      2 * Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) + 2 =
        2 * (1 + Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r)) := by
        ring
      _ = 2 * Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m) r) := by
        rw [hsplit]
      _ = 2 ^ (2 * m) + Nat.choose (2 * m) m := two_mul_sum_range_choose_halfway_even m
  have htwo : 2 ≤ 2 ^ (2 * m) + Nat.choose (2 * m) m := by
    have hpow : 0 < 2 ^ (2 * m) := by
      positivity
    have hchoose : 0 < Nat.choose (2 * m) m := by
      exact Nat.choose_pos (by omega)
    omega
  omega

/-- The search-guided odd slice-threshold candidate already implies a concrete partial-sum boundary
inequality via the codimension-1 threshold lemmas. This is the current proved output of that route,
although it does not yet close the sharp odd half-cube theorem. -/
theorem sum_Icc_choose_even_le_card_positiveBoundary_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
    (hThr : OddHalfCubeSliceThresholdStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) ≤
      #(positiveBoundary 𝒟) + Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
  have hthr : ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m) r ≤ #(𝒟 # r) :=
    hThr h𝒟 hcard
  have hbase :
      Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) (r - 1 + 1)) ≤
        #(positiveBoundary 𝒟) + Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
    refine
      sum_choose_sub_le_card_positiveBoundary_add_sum_card_slice_succ_of_card_slice_ge_choose_sub_on
        (𝒟 := 𝒟) (s := Finset.Icc 1 m) (j := fun _ => 1) ?_ h𝒟 ?_ ?_
    · intro r hr
      exact Finset.mem_range.mpr (by
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hrm⟩
        omega)
    · intro r hr
      exact (Finset.mem_Icc.mp hr).1
    · intro r hr
      rcases Finset.mem_Icc.mp hr with ⟨hr1, hrm⟩
      have hrange : r ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hrm)
      have hmono : Nat.choose (2 * m) (r - 1) ≤ Nat.choose (2 * m) r := by
        have hrpred : r - 1 < (2 * m) / 2 := by
          omega
        simpa [Nat.sub_add_cancel hr1] using
          (Nat.choose_le_succ_of_lt_half_left (r := r - 1) (n := 2 * m) hrpred)
      exact hmono.trans (hthr r hrange)
  have hsumEq :
      Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) (r - 1 + 1)) =
        Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hr).1]
  rw [hsumEq] at hbase
  exact hbase

theorem sum_Icc_choose_even_le_upperShadowGap_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
    (hThr : OddHalfCubeSliceThresholdStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) ≤
      upperShadowGap 𝒟 + Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using
    sum_Icc_choose_even_le_card_positiveBoundary_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
      hThr h𝒟 hcard

theorem two_mul_sum_Icc_choose_even_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
    (hThr : OddHalfCubeSliceThresholdStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    2 * Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) ≤
      2 * upperShadowGap 𝒟 + 2 * Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using
    Nat.mul_le_mul_left 2
      (sum_Icc_choose_even_le_upperShadowGap_add_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
        hThr h𝒟 hcard)

theorem two_pow_add_choose_middle_even_sub_two_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
    (hThr : OddHalfCubeSliceThresholdStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    (2 ^ (2 * m) + Nat.choose (2 * m) m) - 2 ≤
      2 * upperShadowGap 𝒟 + 2 * Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
  calc
    (2 ^ (2 * m) + Nat.choose (2 * m) m) - 2 =
      2 * Finset.sum (Finset.Icc 1 m) (fun r => Nat.choose (2 * m) r) := by
      symm
      exact two_mul_sum_Icc_choose_even m
    _ ≤ 2 * upperShadowGap 𝒟 + 2 * Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) := by
      exact
        two_mul_sum_Icc_choose_even_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
          hThr h𝒟 hcard

theorem sum_Icc_card_slice_succ_add_sum_Icc_upper_tail_eq_card_sub_one_sub_card_slice_one_of_nonempty_isDownSetFamily
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) :
    Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) +
      Finset.sum (Finset.Icc (m + 1) (2 * m)) (fun r => #(𝒟 # (r + 1))) =
        𝒟.card - 1 - #(𝒟 # 1) := by
  let f : ℕ → ℕ := fun r => #(𝒟 # (r + 1))
  have hsplitRange : Finset.range (2 * m + 1) = insert 0 (Finset.Icc 1 (2 * m)) := by
    ext r
    constructor
    · intro hr
      rw [Finset.mem_insert, Finset.mem_Icc]
      by_cases h0 : r = 0
      · exact Or.inl h0
      · right
        exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0), Nat.le_of_lt_succ (Finset.mem_range.mp hr)⟩
    · intro hr
      rw [Finset.mem_insert, Finset.mem_Icc] at hr
      rcases hr with rfl | ⟨hr1, hrm⟩
      · exact Finset.mem_range.mpr (by positivity)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hrm)
  have hsumIcc :
      Finset.sum (Finset.Icc 1 (2 * m)) f = 𝒟.card - 1 - #(𝒟 # 1) := by
    have htotal :
        #(𝒟 # 1) + Finset.sum (Finset.Icc 1 (2 * m)) f = 𝒟.card - 1 := by
      have htotal' :=
        sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily hne h𝒟
      simpa [Fintype.card_fin, hsplitRange, f] using htotal'
    omega
  have hsplitIcc :
      Finset.Icc 1 (2 * m) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (2 * m) := by
    ext r
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (2 * m)) := by
    refine Finset.disjoint_left.mpr ?_
    intro r hr1 hr2
    rw [Finset.mem_Icc] at hr1 hr2
    omega
  calc
    Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1))) +
        Finset.sum (Finset.Icc (m + 1) (2 * m)) (fun r => #(𝒟 # (r + 1))) =
      Finset.sum (Finset.Icc 1 (2 * m)) f := by
        rw [hsplitIcc, Finset.sum_union hdisj]
    _ = 𝒟.card - 1 - #(𝒟 # 1) := hsumIcc

theorem choose_middle_even_add_two_mul_card_slice_one_add_two_mul_sum_card_slice_succ_upper_tail_le_two_mul_upperShadowGap_add_two_pow_of_oddHalfCubeSliceThreshold
    (hThr : OddHalfCubeSliceThresholdStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Nat.choose (2 * m) m + 2 * #(𝒟 # 1) +
      2 * Finset.sum (Finset.Icc (m + 1) (2 * m)) (fun r => #(𝒟 # (r + 1))) ≤
        2 * upperShadowGap 𝒟 + 2 ^ (2 * m) := by
  let S := Finset.sum (Finset.Icc 1 m) (fun r => #(𝒟 # (r + 1)))
  let T := Finset.sum (Finset.Icc (m + 1) (2 * m)) (fun r => #(𝒟 # (r + 1)))
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hcard] using hpow)
  have hsumTail :
      S + T =
          𝒟.card - 1 - #(𝒟 # 1) :=
    by
      simpa [S, T] using
        sum_Icc_card_slice_succ_add_sum_Icc_upper_tail_eq_card_sub_one_sub_card_slice_one_of_nonempty_isDownSetFamily
          hne h𝒟
  have hmain :
      (2 ^ (2 * m) + Nat.choose (2 * m) m) - 2 ≤
        2 * upperShadowGap 𝒟 + 2 * S :=
    two_pow_add_choose_middle_even_sub_two_le_upperShadowGap_double_add_two_mul_sum_card_slice_succ_of_oddHalfCubeSliceThreshold
      hThr h𝒟 hcard
  have htwoLe :
      2 ≤ 2 ^ (2 * m) + Nat.choose (2 * m) m := by
    have hchoose : 0 < Nat.choose (2 * m) m := by
      exact Nat.choose_pos (by omega)
    omega
  have hmain' :
      Nat.choose (2 * m) m + 2 ^ (2 * m) - 2 ≤
        2 * upperShadowGap 𝒟 + 2 * S := by
    omega
  have hsumTailAdd :
      S + T + #(𝒟 # 1) = 2 ^ (2 * m) - 1 := by
    have hsumTailAdd' : S + T + #(𝒟 # 1) = 𝒟.card - 1 := by
      have hle : #(𝒟 # 1) ≤ 𝒟.card - 1 := by
        calc
          #(𝒟 # 1) ≤ Finset.sum (Finset.range (2 * m + 1)) (fun r => #(𝒟 # (r + 1))) := by
            simpa using
              (Finset.single_le_sum
                (f := fun r => #(𝒟 # (r + 1)))
                (fun _ _ => Nat.zero_le _)
                (by simp : 0 ∈ Finset.range (2 * m + 1)))
          _ = 𝒟.card - 1 := by
            simpa [Fintype.card_fin] using
              sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily
                (α := Fin (2 * m + 1)) hne h𝒟
      calc
        S + T + #(𝒟 # 1) = (𝒟.card - 1 - #(𝒟 # 1)) + #(𝒟 # 1) := by
          rw [← hsumTail]
        _ = 𝒟.card - 1 := Nat.sub_add_cancel hle
    simpa [hcard] using hsumTailAdd'
  have htail :
      T + #(𝒟 # 1) = 2 ^ (2 * m) - 1 - S := by
    omega
  have htwoTail :
      2 * T + 2 * #(𝒟 # 1) = 2 * (2 ^ (2 * m) - 1 - S) := by
    omega
  calc
    Nat.choose (2 * m) m + 2 * #(𝒟 # 1) +
        2 * Finset.sum (Finset.Icc (m + 1) (2 * m)) (fun r => #(𝒟 # (r + 1))) =
      Nat.choose (2 * m) m + (2 * T + 2 * #(𝒟 # 1)) := by
        simp [T]
        ring
    _ = Nat.choose (2 * m) m + 2 * (2 ^ (2 * m) - 1 - S) := by
        rw [htwoTail]
    _ ≤ 2 * upperShadowGap 𝒟 + 2 ^ (2 * m) := by
        omega

/-- The full `r`-slice of the cube has full upper shadow in the next slice. -/
theorem upShadow_powersetCard_univ_eq_powersetCard_succ
    {n r : ℕ} :
    ∂⁺ ((Finset.univ : Finset (Fin n)).powersetCard r) =
      (Finset.univ : Finset (Fin n)).powersetCard (r + 1) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_upShadow_iff_erase_mem.mp hs with ⟨a, ha, hsErase⟩
    rw [Finset.mem_powersetCard] at hsErase ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    have hEraseCard : (s.erase a).card + 1 = s.card := by
      simpa using Finset.card_erase_add_one ha
    omega
  · intro hs
    rw [Finset.mem_powersetCard] at hs
    have hsPos : 0 < s.card := by
      omega
    rcases Finset.card_pos.mp hsPos with ⟨a, ha⟩
    rw [Finset.mem_upShadow_iff_erase_mem]
    refine ⟨a, ha, ?_⟩
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset a s |>.trans hs.1, ?_⟩
    have hEraseCard : (s.erase a).card + 1 = s.card := by
      simpa using Finset.card_erase_add_one ha
    omega

theorem slice_succ_eq_powersetCard_of_slice_eq_powersetCard_of_card_positiveBoundary_slice_succ_eq_zero
    {n r : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hslice : 𝒟 # r = (Finset.univ : Finset (Fin n)).powersetCard r)
    (hboundary : #((positiveBoundary 𝒟) # (r + 1)) = 0) :
    𝒟 # (r + 1) = (Finset.univ : Finset (Fin n)).powersetCard (r + 1) := by
  have hboundaryEmpty : ((positiveBoundary 𝒟) # (r + 1)) = ∅ :=
    Finset.card_eq_zero.mp hboundary
  calc
    𝒟 # (r + 1) = ∂⁺ (𝒟 # r) := by
      have hsplit :=
        upShadow_slice_eq_slice_succ_union_positiveBoundary_slice_succ_of_isDownSetFamily
          (𝒟 := 𝒟) h𝒟 r
      rw [hboundaryEmpty, Finset.union_empty] at hsplit
      exact hsplit.symm
    _ = ∂⁺ ((Finset.univ : Finset (Fin n)).powersetCard r) := by
      rw [hslice]
    _ = (Finset.univ : Finset (Fin n)).powersetCard (r + 1) :=
      upShadow_powersetCard_univ_eq_powersetCard_succ

/-- If all positive-boundary slices below the middle layer vanish, then the lower half of the family
is forced to be the full lower half of the odd cube. -/
theorem odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
    {m k : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) (hk : k ≤ m)
    (hvanish : ∀ r ∈ Finset.Icc 1 k, #((positiveBoundary 𝒟) # r) = 0) :
    ∀ r, r ≤ k →
      𝒟 # r = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard r := by
  intro r hr
  induction' r with r ihr
  · exact slice_eq_powersetCard_of_card_eq_choose (by
      rw [card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne h𝒟]
      simp)
  · have hr' : r ≤ k := Nat.le_of_succ_le hr
    have hprev := ihr hr'
    have hboundary : #((positiveBoundary 𝒟) # (r + 1)) = 0 :=
      hvanish (r + 1) (by
        rw [Finset.mem_Icc]
        omega)
    exact
      slice_succ_eq_powersetCard_of_slice_eq_powersetCard_of_card_positiveBoundary_slice_succ_eq_zero
        h𝒟 hprev hboundary

theorem odd_initial_slices_full_of_lower_boundary_slices_vanish_upto
    {m k : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) (hk : k ≤ m)
    (hvanish : ∀ r ∈ Finset.Icc 1 k, #((positiveBoundary 𝒟) # r) = 0) :
    ∀ r, r ≤ k → #(𝒟 # r) = Nat.choose (2 * m + 1) r := by
  intro r hr
  have hs :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto hne h𝒟 hk hvanish r hr
  simpa [Finset.card_powersetCard] using congrArg Finset.card hs

/-- If all positive-boundary slices below the middle layer vanish, then the lower half of the family
is forced to be the full lower half of the odd cube. -/
theorem odd_initial_slices_full_of_lower_boundary_slices_vanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r := by
  intro r hr
  have hrle : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  exact odd_initial_slices_full_of_lower_boundary_slices_vanish_upto hne h𝒟 le_rfl hvanish r hrle

theorem card_slice_succ_lt_choose_of_slice_eq_powersetCard_of_card_positiveBoundary_slice_succ_pos
    {n r : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hslice : 𝒟 # r = (Finset.univ : Finset (Fin n)).powersetCard r)
    (hboundaryPos : 0 < #((positiveBoundary 𝒟) # (r + 1))) :
    #(𝒟 # (r + 1)) < Nat.choose n (r + 1) := by
  have hshadow :
      #(∂⁺ (𝒟 # r)) = Nat.choose n (r + 1) := by
    calc
      #(∂⁺ (𝒟 # r)) = #(∂⁺ ((Finset.univ : Finset (Fin n)).powersetCard r)) := by
        rw [hslice]
      _ = #((Finset.univ : Finset (Fin n)).powersetCard (r + 1)) := by
        rw [upShadow_powersetCard_univ_eq_powersetCard_succ]
      _ = Nat.choose n (r + 1) := by
        simp
  have hsplit :=
    card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) h𝒟 r
  have hsum :
      Nat.choose n (r + 1) = #(𝒟 # (r + 1)) + #((positiveBoundary 𝒟) # (r + 1)) := by
    rw [← hshadow]
    exact hsplit
  have hlt :
      #(𝒟 # (r + 1)) < #(𝒟 # (r + 1)) + #((positiveBoundary 𝒟) # (r + 1)) :=
    Nat.lt_add_of_pos_right hboundaryPos
  simpa [hsum] using hlt

theorem card_positiveBoundary_slice_succ_eq_choose_sub_card_slice_succ_of_slice_eq_powersetCard
    {n r : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hslice : 𝒟 # r = (Finset.univ : Finset (Fin n)).powersetCard r) :
    #((positiveBoundary 𝒟) # (r + 1)) = Nat.choose n (r + 1) - #(𝒟 # (r + 1)) := by
  have hshadow :
      #(∂⁺ (𝒟 # r)) = Nat.choose n (r + 1) := by
    calc
      #(∂⁺ (𝒟 # r)) = #(∂⁺ ((Finset.univ : Finset (Fin n)).powersetCard r)) := by
        rw [hslice]
      _ = #((Finset.univ : Finset (Fin n)).powersetCard (r + 1)) := by
        rw [upShadow_powersetCard_univ_eq_powersetCard_succ]
      _ = Nat.choose n (r + 1) := by
        simp
  have hsplit :=
    card_upShadow_slice_eq_card_slice_succ_add_card_positiveBoundary_slice_succ_of_isDownSetFamily
      (𝒟 := 𝒟) h𝒟 r
  omega

theorem card_positiveBoundary_slice_eq_choose_sub_card_slice_of_pred_slice_eq_powersetCard
    {n s : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (hspos : 0 < s)
    (h𝒟 : IsDownSetFamily 𝒟)
    (hslicePred : 𝒟 # (s - 1) = (Finset.univ : Finset (Fin n)).powersetCard (s - 1)) :
    #((positiveBoundary 𝒟) # s) = Nat.choose n s - #(𝒟 # s) := by
  have hsucc : (s - 1) + 1 = s := Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)
  simpa [hsucc] using
    card_positiveBoundary_slice_succ_eq_choose_sub_card_slice_succ_of_slice_eq_powersetCard
      (𝒟 := 𝒟) (r := s - 1) h𝒟 hslicePred

theorem odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
    {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟) (hrm : r ≤ m)
    (hvanish : ∀ s ∈ Finset.Icc 1 r, #((positiveBoundary 𝒟) # s) = 0)
    (hboundaryPos : 0 < #((positiveBoundary 𝒟) # (r + 1))) :
    #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1) := by
  have hslice :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne h𝒟 hrm hvanish r le_rfl
  exact
    card_slice_succ_lt_choose_of_slice_eq_powersetCard_of_card_positiveBoundary_slice_succ_pos
      h𝒟 hslice hboundaryPos

theorem totalSize_oddLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit
    {m r : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hcard : 𝒟.card = 2 ^ (2 * m))
    (hrm : r < m)
    (hdeficit : #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1)) :
    totalSize (oddLowerHalfFamily m) < totalSize 𝒟 := by
  let n := 2 * m + 1
  let lowerMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
  let upperMass : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k))
  let lowerDeficit : ℕ :=
    Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k - #(𝒟 # k))
  let lowerWeightD : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => k * #(𝒟 # k))
  let upperWeightD : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => k * #(𝒟 # k))
  have hmle : m + 1 ≤ n + 1 := by
    dsimp [n]
    omega
  have hsumSlices :
      Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m) := by
    simpa [Nat.range_succ_eq_Iic, hcard] using (Finset.sum_card_slice 𝒟)
  have hsplitMass :
      lowerMass + upperMass = 2 ^ (2 * m) := by
    have hsplit :
        lowerMass + upperMass =
          Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
            simpa [lowerMass, upperMass] using
              (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
    exact hsplit.trans hsumSlices
  have hchooseHalf :
      Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) = 2 ^ (2 * m) := by
    dsimp [n]
    simpa [show 4 ^ m = 2 ^ (2 * m) by
      rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using Nat.sum_range_choose_halfway m
  have hsumTsub :
      lowerDeficit =
        Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) - lowerMass := by
    dsimp [lowerDeficit, lowerMass]
    rw [Finset.sum_tsub_distrib]
    intro k hk
    exact card_slice_le_choose (𝒟 := 𝒟) (r := k)
  have hlowerDeficit_eq_upperMass : lowerDeficit = upperMass := by
    rw [hsumTsub]
    omega
  have hsliceDeficitPos :
      0 < Nat.choose n (r + 1) - #(𝒟 # (r + 1)) := by
    dsimp [n] at hdeficit ⊢
    omega
  have hsliceDeficit_le_lowerDeficit :
      Nat.choose n (r + 1) - #(𝒟 # (r + 1)) ≤ lowerDeficit := by
    dsimp [lowerDeficit]
    simpa using
      (Finset.single_le_sum
        (f := fun k => Nat.choose n k - #(𝒟 # k))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.succ_lt_succ hrm)))
  have hupperMassPos : 0 < upperMass := by
    rw [← hlowerDeficit_eq_upperMass]
    exact lt_of_lt_of_le hsliceDeficitPos hsliceDeficit_le_lowerDeficit
  have hsplitTotalSize :
      totalSize 𝒟 = lowerWeightD + upperWeightD := by
    have hsumWeightAll :
        totalSize 𝒟 = Finset.sum (Finset.range (n + 1)) (fun k => k * #(𝒟 # k)) := by
          simpa [n] using totalSize_eq_sum_range_mul_card_slice 𝒟
    have hsplitWeight :
        lowerWeightD + upperWeightD =
          Finset.sum (Finset.range (n + 1)) (fun k => k * #(𝒟 # k)) := by
            simpa [lowerWeightD, upperWeightD] using
              (Finset.sum_range_add_sum_Ico (fun k => k * #(𝒟 # k)) hmle)
    exact hsumWeightAll.trans hsplitWeight.symm
  have hupperWeight_lower :
      (m + 1) * upperMass ≤ upperWeightD := by
    have hconst :
        (m + 1) * upperMass =
          Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => (m + 1) * #(𝒟 # k)) := by
            dsimp [upperMass]
            rw [Finset.mul_sum]
    calc
      (m + 1) * upperMass =
          Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => (m + 1) * #(𝒟 # k)) := hconst
      _ ≤ upperWeightD := by
            dsimp [upperWeightD]
            exact Finset.sum_le_sum fun k hk => by
              have hkge : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
              exact Nat.mul_le_mul_right #(𝒟 # k) hkge
  have hlowerWeight_upper :
      Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) ≤
        lowerWeightD + m * lowerDeficit := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k)
          =
        Finset.sum (Finset.range (m + 1))
          (fun k => k * #(𝒟 # k) + k * (Nat.choose n k - #(𝒟 # k))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hle : #(𝒟 # k) ≤ Nat.choose n k := card_slice_le_choose (𝒟 := 𝒟) (r := k)
            have hmul : k * #(𝒟 # k) ≤ k * Nat.choose n k := Nat.mul_le_mul_left k hle
            calc
              k * Nat.choose n k = k * #(𝒟 # k) + (k * Nat.choose n k - k * #(𝒟 # k)) := by
                exact (Nat.add_sub_of_le hmul).symm
              _ = k * #(𝒟 # k) + k * (Nat.choose n k - #(𝒟 # k)) := by
                rw [Nat.mul_sub_left_distrib]
      _ ≤
        Finset.sum (Finset.range (m + 1))
          (fun k => k * #(𝒟 # k) + m * (Nat.choose n k - #(𝒟 # k))) := by
            exact Finset.sum_le_sum fun k hk => by
              have hkle : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left
                  (Nat.mul_le_mul_right (Nat.choose n k - #(𝒟 # k)) hkle)
                  (k * #(𝒟 # k))
      _ =
        lowerWeightD + m * lowerDeficit := by
          dsimp [lowerWeightD, lowerDeficit]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htsWitness :
      totalSize (oddLowerHalfFamily m) =
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) := by
    have hsumWeightAll :
        totalSize (oddLowerHalfFamily m) =
          Finset.sum (Finset.range (n + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) := by
            simpa [n] using totalSize_eq_sum_range_mul_card_slice (oddLowerHalfFamily m)
    have hsplitWeight :
        Finset.sum (Finset.range (n + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) =
          Finset.sum (Finset.range (m + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) +
            Finset.sum (Finset.Ico (m + 1) (n + 1))
              (fun k => k * #((oddLowerHalfFamily m) # k)) := by
                symm
                simpa [n] using
                  (Finset.sum_range_add_sum_Ico (fun k => k * #((oddLowerHalfFamily m) # k)) hmle)
    have hlowerChoose :
        Finset.sum (Finset.range (m + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) =
          Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [card_slice_oddLowerHalfFamily_eq_choose (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    have hupperZero :
        Finset.sum (Finset.Ico (m + 1) (n + 1))
          (fun k => k * #((oddLowerHalfFamily m) # k)) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            rw [card_slice_oddLowerHalfFamily_eq_zero (Finset.mem_Ico.mp hk).1, Nat.mul_zero]
    calc
      totalSize (oddLowerHalfFamily m) =
        Finset.sum (Finset.range (n + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) := hsumWeightAll
      _ =
        Finset.sum (Finset.range (m + 1)) (fun k => k * #((oddLowerHalfFamily m) # k)) +
          Finset.sum (Finset.Ico (m + 1) (n + 1))
            (fun k => k * #((oddLowerHalfFamily m) # k)) := hsplitWeight
      _ =
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) +
          Finset.sum (Finset.Ico (m + 1) (n + 1))
            (fun k => k * #((oddLowerHalfFamily m) # k)) := by
              rw [hlowerChoose]
      _ = Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) := by
            rw [hupperZero, add_zero]
  have hmainLower :
      totalSize (oddLowerHalfFamily m) + upperMass ≤ totalSize 𝒟 := by
    rw [htsWitness, hsplitTotalSize]
    have hupperWeight' :
        lowerWeightD + (m + 1) * upperMass ≤ lowerWeightD + upperWeightD := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hupperWeight_lower lowerWeightD
    have hcompare :
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) + upperMass ≤
          lowerWeightD + (m + 1) * upperMass := by
      have hle1 :
          Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) ≤
            lowerWeightD + m * lowerDeficit := hlowerWeight_upper
      rw [hlowerDeficit_eq_upperMass] at hle1
      calc
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) + upperMass ≤
            (lowerWeightD + m * upperMass) + upperMass := by
              simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hle1 upperMass
        _ = lowerWeightD + (m + 1) * upperMass := by
              ring
    exact hcompare.trans hupperWeight'
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hupperMassPos) hmainLower

/-- A genuinely wide middle transition window forces strictly larger total size than the lower-half
model. This is the first quantitative penalty attached to a non-collapsed transition region. -/
theorem totalSize_oddLowerHalfFamily_lt_of_middleTransitionWindow_strict
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0)
    (htlt : t < m + 1) (hltu : m + 1 < u) :
    totalSize (oddLowerHalfFamily m) < totalSize 𝒟 := by
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 1) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hdeficit : #(𝒟 # t) < Nat.choose (2 * m + 1) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  have htsucc : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
  have hdeficit' : #(𝒟 # ((t - 1) + 1)) < Nat.choose (2 * m + 1) ((t - 1) + 1) := by
    simpa [htsucc] using hdeficit
  exact
    totalSize_oddLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit
      (hcard := hmin.2.1) (r := t - 1) (by omega) hdeficit'

/-- If a middle-transition-window odd minimizer has total size no larger than the lower-half
witness, then the transition window must already collapse and the minimizer is exactly the lower
half. This is the first clean rigidity package using the new strict middle-window penalty. -/
theorem eq_oddLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 ≤ u) (hu : u ≤ 2 * m + 1)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r)
    (hzero : ∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0)
    (hsize : totalSize 𝒟 ≤ totalSize (oddLowerHalfFamily m)) :
    𝒟 = oddLowerHalfFamily m := by
  by_cases htEq : t = m + 1
  · exact
      eq_oddLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle
        hmin htmid humid hu hfull hzero hmid htEq
  · by_cases huEq : u = m + 1
    · exact
        eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
          hmin htmid humid hu hfull hzero hmid huEq
    · exfalso
      have htlt : t < m + 1 := lt_of_le_of_ne htmid htEq
      have hltu : m + 1 < u := by
        exact lt_of_le_of_ne humid (by simpa [eq_comm] using huEq)
      have hstrict :
          totalSize (oddLowerHalfFamily m) < totalSize 𝒟 :=
        totalSize_oddLowerHalfFamily_lt_of_middleTransitionWindow_strict hmin hmid htlt hltu
      exact (not_lt_of_ge hsize) hstrict

theorem sum_range_choose_even_without_middle (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 2) r) =
      2 ^ (2 * m + 1) - Nat.choose (2 * m + 1) m := by
  have hprefixTwice :
      2 * Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 2) r) =
        2 ^ (2 * m + 2) + Nat.choose (2 * m + 2) (m + 1) := by
    simpa using two_mul_sum_range_choose_halfway_even (m + 1)
  have hsplit :
      Finset.sum (Finset.range (m + 2)) (fun r => Nat.choose (2 * m + 2) r) =
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 2) r) +
          Nat.choose (2 * m + 2) (m + 1) := by
    rw [Finset.sum_range_succ]
  have hmiddle :
      Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  have hpow :
      2 ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Nat.pow_succ]
    ring
  rw [hsplit, hmiddle] at hprefixTwice
  rw [hpow] at hprefixTwice
  omega

theorem totalSize_evenLowerHalfFamily_eq_weighted_lower_choose_add_middle (m : ℕ) :
    totalSize (evenLowerHalfFamily m) =
      Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose (2 * m + 2) k) +
        (m + 1) * Nat.choose (2 * m + 1) m := by
  have hsumAll :
      totalSize (evenLowerHalfFamily m) =
        Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := by
    simpa using totalSize_eq_sum_range_mul_card_slice (evenLowerHalfFamily m)
  have hsplit :
      Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range (m + 2))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
            (fun r => r * #((evenLowerHalfFamily m) # r)) := by
    symm
    exact Finset.sum_range_add_sum_Ico
      (fun r => r * #((evenLowerHalfFamily m) # r)) (by omega)
  have hupperZero :
      Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [card_slice_evenLowerHalfFamily_eq_zero (Finset.mem_Ico.mp hr).1, Nat.mul_zero]
  have hlowerSplit :
      Finset.sum (Finset.range (m + 2))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range (m + 1))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          (m + 1) * #((evenLowerHalfFamily m) # (m + 1)) := by
    rw [Finset.sum_range_succ]
  have hweightedLowerShift :
      Finset.sum (Finset.range (m + 1))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        Finset.sum (Finset.range m)
          (fun r => (r + 1) * #((evenLowerHalfFamily m) # (r + 1))) := by
    have hshift :=
      (Finset.sum_range_succ'
        (f := fun r => r * #((evenLowerHalfFamily m) # r)) (n := m))
    simpa using hshift
  have hweightedLowerChoose :
      Finset.sum (Finset.range (m + 1))
          (fun r => r * #((evenLowerHalfFamily m) # r)) =
        (2 * m + 2) *
          Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) := by
    rw [hweightedLowerShift]
    calc
      Finset.sum (Finset.range m)
          (fun r => (r + 1) * #((evenLowerHalfFamily m) # (r + 1)))
        =
          Finset.sum (Finset.range m)
            (fun r => (2 * m + 2) * Nat.choose (2 * m + 1) r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [card_slice_evenLowerHalfFamily_eq_choose
                (Nat.succ_le_of_lt (Finset.mem_range.mp hr))]
              simpa [Nat.mul_comm] using
                (Nat.add_one_mul_choose_eq (2 * m + 1) r).symm
      _ =
          (2 * m + 2) *
            Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) := by
              rw [Finset.mul_sum]
  have hweightedChoose :
      (2 * m + 2) * Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) =
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose (2 * m + 2) k) := by
    calc
      (2 * m + 2) * Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r)
        = Finset.sum (Finset.range (m + 1))
            (fun r => r * #((evenLowerHalfFamily m) # r)) := hweightedLowerChoose.symm
      _ =
          Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose (2 * m + 2) k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [card_slice_evenLowerHalfFamily_eq_choose
              (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  calc
    totalSize (evenLowerHalfFamily m)
      =
        Finset.sum (Finset.range (2 * m + 3))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := hsumAll
    _ =
        Finset.sum (Finset.range (m + 2))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          Finset.sum (Finset.Ico (m + 2) (2 * m + 3))
            (fun r => r * #((evenLowerHalfFamily m) # r)) := hsplit
    _ =
        Finset.sum (Finset.range (m + 2))
          (fun r => r * #((evenLowerHalfFamily m) # r)) := by
            rw [hupperZero, add_zero]
    _ =
        Finset.sum (Finset.range (m + 1))
            (fun r => r * #((evenLowerHalfFamily m) # r)) +
          (m + 1) * #((evenLowerHalfFamily m) # (m + 1)) := hlowerSplit
    _ =
        (2 * m + 2) * Finset.sum (Finset.range m) (fun r => Nat.choose (2 * m + 1) r) +
          (m + 1) * Nat.choose (2 * m + 1) m := by
            rw [hweightedLowerChoose, card_slice_evenLowerHalfFamily_eq_middle]
    _ =
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose (2 * m + 2) k) +
          (m + 1) * Nat.choose (2 * m + 1) m := by
            rw [hweightedChoose]

theorem totalSize_evenLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit
    {m s : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hspos : 0 < s)
    (hsm : s ≤ m)
    (hdeficit : #(𝒟 # s) < Nat.choose (2 * m + 2) s) :
    totalSize (evenLowerHalfFamily m) < totalSize 𝒟 := by
  let n := 2 * m + 2
  let middleMass : ℕ := Nat.choose (2 * m + 1) m
  let lowerMass : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => #(𝒟 # k))
  let upperMass : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => #(𝒟 # k))
  let lowerDeficit : ℕ :=
    Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k - #(𝒟 # k))
  let lowerWeightD : ℕ := Finset.sum (Finset.range (m + 1)) (fun k => k * #(𝒟 # k))
  let upperWeightD : ℕ := Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => k * #(𝒟 # k))
  have hmle : m + 1 ≤ n + 1 := by
    dsimp [n]
    omega
  have hsumSlices :
      Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) = 2 ^ (2 * m + 1) := by
    simpa [Nat.range_succ_eq_Iic, hcard] using (Finset.sum_card_slice 𝒟)
  have hsplitMass :
      lowerMass + upperMass = 2 ^ (2 * m + 1) := by
    have hsplit :
        lowerMass + upperMass =
          Finset.sum (Finset.range (n + 1)) (fun k => #(𝒟 # k)) := by
            simpa [lowerMass, upperMass] using
              (Finset.sum_range_add_sum_Ico (fun k => #(𝒟 # k)) hmle)
    exact hsplit.trans hsumSlices
  have hchoosePrefix :
      Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) =
        2 ^ (2 * m + 1) - middleMass := by
    dsimp [n, middleMass]
    simpa using sum_range_choose_even_without_middle m
  have hsumTsub :
      lowerDeficit =
        Finset.sum (Finset.range (m + 1)) (fun k => Nat.choose n k) - lowerMass := by
    dsimp [lowerDeficit, lowerMass]
    rw [Finset.sum_tsub_distrib]
    intro k hk
    exact card_slice_le_choose (𝒟 := 𝒟) (r := k)
  have hlowerDeficit_eq_upperExcess : lowerDeficit = upperMass - middleMass := by
    rw [hsumTsub, hchoosePrefix]
    omega
  have hsliceDeficitPos :
      0 < Nat.choose n s - #(𝒟 # s) := by
    dsimp [n] at hdeficit ⊢
    omega
  have hsliceDeficit_le_lowerDeficit :
      Nat.choose n s - #(𝒟 # s) ≤ lowerDeficit := by
    dsimp [lowerDeficit]
    simpa using
      (Finset.single_le_sum
        (f := fun k => Nat.choose n k - #(𝒟 # k))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hsm)))
  have hlowerDeficitPos : 0 < lowerDeficit := by
    exact lt_of_lt_of_le hsliceDeficitPos hsliceDeficit_le_lowerDeficit
  have hsplitTotalSize :
      totalSize 𝒟 = lowerWeightD + upperWeightD := by
    have hsumWeightAll :
        totalSize 𝒟 = Finset.sum (Finset.range (n + 1)) (fun k => k * #(𝒟 # k)) := by
          simpa [n] using totalSize_eq_sum_range_mul_card_slice 𝒟
    have hsplitWeight :
        lowerWeightD + upperWeightD =
          Finset.sum (Finset.range (n + 1)) (fun k => k * #(𝒟 # k)) := by
            simpa [lowerWeightD, upperWeightD] using
              (Finset.sum_range_add_sum_Ico (fun k => k * #(𝒟 # k)) hmle)
    exact hsumWeightAll.trans hsplitWeight.symm
  have hupperWeight_lower :
      (m + 1) * upperMass ≤ upperWeightD := by
    have hconst :
        (m + 1) * upperMass =
          Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => (m + 1) * #(𝒟 # k)) := by
            dsimp [upperMass]
            rw [Finset.mul_sum]
    calc
      (m + 1) * upperMass =
          Finset.sum (Finset.Ico (m + 1) (n + 1)) (fun k => (m + 1) * #(𝒟 # k)) := hconst
      _ ≤ upperWeightD := by
            dsimp [upperWeightD]
            exact Finset.sum_le_sum fun k hk => by
              have hkge : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
              exact Nat.mul_le_mul_right #(𝒟 # k) hkge
  have hlowerWeight_upper :
      Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) ≤
        lowerWeightD + m * lowerDeficit := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k)
          =
        Finset.sum (Finset.range (m + 1))
          (fun k => k * #(𝒟 # k) + k * (Nat.choose n k - #(𝒟 # k))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hle : #(𝒟 # k) ≤ Nat.choose n k := card_slice_le_choose (𝒟 := 𝒟) (r := k)
            have hmul : k * #(𝒟 # k) ≤ k * Nat.choose n k := Nat.mul_le_mul_left k hle
            calc
              k * Nat.choose n k = k * #(𝒟 # k) + (k * Nat.choose n k - k * #(𝒟 # k)) := by
                exact (Nat.add_sub_of_le hmul).symm
              _ = k * #(𝒟 # k) + k * (Nat.choose n k - #(𝒟 # k)) := by
                rw [Nat.mul_sub_left_distrib]
      _ ≤
        Finset.sum (Finset.range (m + 1))
          (fun k => k * #(𝒟 # k) + m * (Nat.choose n k - #(𝒟 # k))) := by
            exact Finset.sum_le_sum fun k hk => by
              have hkle : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left
                  (Nat.mul_le_mul_right (Nat.choose n k - #(𝒟 # k)) hkle)
                  (k * #(𝒟 # k))
      _ =
        lowerWeightD + m * lowerDeficit := by
          dsimp [lowerWeightD, lowerDeficit]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htsWitness :
      totalSize (evenLowerHalfFamily m) =
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) +
          (m + 1) * middleMass := by
    dsimp [n, middleMass]
    simpa using totalSize_evenLowerHalfFamily_eq_weighted_lower_choose_add_middle m
  have hmainLower :
      totalSize (evenLowerHalfFamily m) + lowerDeficit ≤ totalSize 𝒟 := by
    rw [htsWitness, hsplitTotalSize]
    have hcompare :
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) +
            (m + 1) * middleMass + lowerDeficit ≤
          lowerWeightD + ((m + 1) * middleMass + (m + 1) * lowerDeficit) := by
      calc
        Finset.sum (Finset.range (m + 1)) (fun k => k * Nat.choose n k) +
            (m + 1) * middleMass + lowerDeficit
            ≤ (lowerWeightD + m * lowerDeficit) + ((m + 1) * middleMass + lowerDeficit) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_right hlowerWeight_upper ((m + 1) * middleMass + lowerDeficit)
        _ = lowerWeightD + ((m + 1) * middleMass + (m + 1) * lowerDeficit) := by
              ring
    have hupperMassEq : upperMass = middleMass + lowerDeficit := by
      rw [hlowerDeficit_eq_upperExcess]
      omega
    have hupperWeight' :
        lowerWeightD + ((m + 1) * middleMass + (m + 1) * lowerDeficit) ≤
          lowerWeightD + upperWeightD := by
      calc
        lowerWeightD + ((m + 1) * middleMass + (m + 1) * lowerDeficit)
            = lowerWeightD + (m + 1) * upperMass := by rw [hupperMassEq]; ring
        _ ≤ lowerWeightD + upperWeightD := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left hupperWeight_lower lowerWeightD
    exact hcompare.trans hupperWeight'
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hlowerDeficitPos) hmainLower

theorem totalSize_evenLowerHalfFamily_lt_of_middleTransitionWindow_strict
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (htlt : t < m + 1) (hltu : m + 1 < u) :
    totalSize (evenLowerHalfFamily m) < totalSize 𝒟 := by
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m + 1))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 2) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hdeficit :
      #(𝒟 # t) < Nat.choose (2 * m + 2) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  exact
    totalSize_evenLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit
      hmin.2.1 htpos (Nat.le_of_lt_succ htlt) hdeficit

theorem t_eq_middle_of_middleTransitionWindow_of_totalSize_le_evenWitness
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hsize : totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m)) :
    t = m + 1 := by
  by_contra htNe
  have htlt : t < m + 1 := lt_of_le_of_ne htmid htNe
  have hstrict :
      totalSize (evenLowerHalfFamily m) < totalSize 𝒟 :=
    totalSize_evenLowerHalfFamily_lt_of_middleTransitionWindow_strict hmin hmid htlt humid
  exact (not_lt_of_ge hsize) hstrict

theorem eq_evenLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness_of_balancedZeroSections
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hsize : totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m))
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have htEq :
      t = m + 1 :=
    t_eq_middle_of_middleTransitionWindow_of_totalSize_le_evenWitness
      hmin htmid humid hmid hsize
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle_of_balancedZeroSections
      hmin hfull htEq hbal

theorem oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_of_largerTotalSizeThanWitness
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement) :
    OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement := by
  intro m r 𝒟 h𝒟 hcard hrm hfull hdeficit
  have hsizeStrict :
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 :=
    totalSize_oddLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit hcard hrm hdeficit
  exact hSize h𝒟 hcard hsizeStrict

theorem oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop_of_largerTotalSizeThanWitness
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictWeightedDropStatement) :
    OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement := by
  intro m r 𝒟 h𝒟 hcard hrm hfull hdeficit
  have hsizeStrict :
      totalSize (oddLowerHalfFamily m) < totalSize 𝒟 :=
    totalSize_oddLowerHalfFamily_lt_of_card_eq_half_cube_of_lower_slice_deficit hcard hrm hdeficit
  exact hSize h𝒟 hcard hsizeStrict

theorem oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement := by
  intro m r 𝒟 h𝒟 hcard hrm hfull hdeficit
  have houtZero : ∀ s ∈ Finset.range (r + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0 := by
    intro s hs
    have hsle : s ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hslice :
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := hfull s hsle
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # s)) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) s
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      simpa [hslice] using congrArg Finset.card hslice
    omega
  have houtPos : 0 < #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) := by
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) =
          Nat.choose (2 * m + 1) (r + 1) - #(𝒟 # (r + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) (r + 1)
    omega
  exact hOut (m := m) (r := r) (𝒟 := 𝒟) h𝒟 hcard hrm houtZero houtPos

theorem oddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement := by
  intro m r 𝒟 h𝒟 hcard hrm houtZero houtPos
  have hvanish : ∀ s ∈ Finset.Icc 1 r, #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    have hsRange : s ∈ Finset.range (r + 1) := by
      exact Finset.mem_range.mpr <|
        lt_of_le_of_lt (Finset.mem_Icc.mp hs).2 (Nat.lt_succ_self r)
    have hsubset :
        ((positiveBoundary 𝒟) # s) ⊆ (((Finset.univ.powerset) \ 𝒟) # s) :=
      positiveBoundary_slice_subset_outside_slice (𝒟 := 𝒟) (r := s)
    have hle :
        #((positiveBoundary 𝒟) # s) ≤ #((((Finset.univ.powerset) \ 𝒟) # s)) :=
      Finset.card_le_card hsubset
    have hzero := houtZero s hsRange
    omega
  have hrlt : r < Fintype.card (Fin (2 * m + 1)) := by
    simpa [Fintype.card_fin] using (show r < 2 * m + 1 by omega)
  have houtZero_r : #((((Finset.univ.powerset) \ 𝒟) # r)) = 0 := by
    exact houtZero r (by simpa using Nat.lt_succ_self r)
  have hsdiffLe :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) * (r + 1) ≤
        #((((Finset.univ.powerset) \ 𝒟) # r)) * (2 * m + 1 - r) := by
    simpa [Fintype.card_fin] using
      (card_outside_slice_succ_sdiff_boundary_slice_mul_le_card_outside_slice_mul
        (𝒟 := 𝒟) (r := r) hrlt)
  have hsdiffMulZero :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) * (r + 1) =
        0 := by
    have hle' := hsdiffLe
    rw [houtZero_r, zero_mul] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hsdiffZero :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) = 0 := by
    exact (Nat.mul_eq_zero.mp hsdiffMulZero).resolve_right (Nat.succ_ne_zero r)
  have hsubset :
      ((positiveBoundary 𝒟) # (r + 1)) ⊆ (((Finset.univ.powerset) \ 𝒟) # (r + 1)) :=
    positiveBoundary_slice_subset_outside_slice (𝒟 := 𝒟) (r := r + 1)
  have hdecomp :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) +
          #(((positiveBoundary 𝒟) # (r + 1))) =
        #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) := by
    exact Finset.card_sdiff_add_card_eq_card hsubset
  have hboundaryPos : 0 < #((positiveBoundary 𝒟) # (r + 1)) := by
    omega
  exact hFirstBad (m := m) (r := r) (𝒟 := 𝒟) h𝒟 hcard hrm hvanish hboundaryPos

theorem oddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement := by
  intro m r 𝒟 h𝒟 hcard hrm hvanish hboundaryPos
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hcard] using hpow)
  have hfull :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne h𝒟 (Nat.le_of_lt hrm) hvanish
  have hdeficit :=
    odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
      hne h𝒟 (Nat.le_of_lt hrm) hvanish hboundaryPos
  exact hDef h𝒟 hcard hrm hfull hdeficit

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 hmin hexists
  let p : ℕ → Prop :=
    fun r => r ∈ Finset.Icc 1 m ∧ 0 < #((positiveBoundary 𝒟) # r)
  have hp : ∃ r, p r := by
    rcases hexists with ⟨r, hr, hpos⟩
    exact ⟨r, hr, hpos⟩
  let rmin := Nat.find hp
  have hrmin : p rmin := Nat.find_spec hp
  have hrmin_mem : rmin ∈ Finset.Icc 1 m := hrmin.1
  have hrmin_pos : 0 < #((positiveBoundary 𝒟) # rmin) := hrmin.2
  have hrmin_pos' : 1 ≤ rmin := (Finset.mem_Icc.mp hrmin_mem).1
  have hrmin_le_m : rmin ≤ m := (Finset.mem_Icc.mp hrmin_mem).2
  have hvanish : ∀ s ∈ Finset.Icc 1 (rmin - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    by_contra hsne
    have hspos : 0 < #((positiveBoundary 𝒟) # s) := Nat.pos_of_ne_zero hsne
    have hs_mem : s ∈ Finset.Icc 1 m := by
      rw [Finset.mem_Icc] at hs ⊢
      omega
    have hsP : p s := ⟨hs_mem, hspos⟩
    have hmin_le_s : rmin ≤ s := Nat.find_min' hp hsP
    rw [Finset.mem_Icc] at hs
    omega
  have hrpred_lt_m : rmin - 1 < m := by
    omega
  have hrpred_pos : 0 < #((positiveBoundary 𝒟) # ((rmin - 1) + 1)) := by
    simpa [Nat.sub_add_cancel hrmin_pos'] using hrmin_pos
  exact hFirstBad hmin.1 hmin.2.1 hrpred_lt_m hvanish hrpred_pos

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
        hDef)

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
      (oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 hmin hexists
  let p : ℕ → Prop :=
    fun r => r ∈ Finset.Icc 1 m ∧ 0 < #((positiveBoundary 𝒟) # r)
  have hp : ∃ r, p r := by
    rcases hexists with ⟨r, hr, hpos⟩
    exact ⟨r, hr, hpos⟩
  let rmin := Nat.find hp
  have hrmin : p rmin := Nat.find_spec hp
  have hrmin_mem : rmin ∈ Finset.Icc 1 m := hrmin.1
  have hrmin_pos : 0 < #((positiveBoundary 𝒟) # rmin) := hrmin.2
  have hrmin_pos' : 1 ≤ rmin := (Finset.mem_Icc.mp hrmin_mem).1
  have hrmin_le_m : rmin ≤ m := (Finset.mem_Icc.mp hrmin_mem).2
  have hvanish : ∀ s ∈ Finset.Icc 1 (rmin - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    by_contra hsne
    have hspos : 0 < #((positiveBoundary 𝒟) # s) := Nat.pos_of_ne_zero hsne
    have hs_mem : s ∈ Finset.Icc 1 m := by
      rw [Finset.mem_Icc] at hs ⊢
      omega
    have hsP : p s := ⟨hs_mem, hspos⟩
    have hmin_le_s : rmin ≤ s := Nat.find_min' hp hsP
    rw [Finset.mem_Icc] at hs
    omega
  have hrpred_lt_m : rmin - 1 < m := by
    omega
  have hrpred_pos : 0 < #((positiveBoundary 𝒟) # ((rmin - 1) + 1)) := by
    simpa [Nat.sub_add_cancel hrmin_pos'] using hrmin_pos
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hfull :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish
  have hdeficit :=
    odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
      hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish hrpred_pos
  have houtZero :
      ∀ s ∈ Finset.range ((rmin - 1) + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0 := by
    intro s hs
    have hsle : s ≤ rmin - 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hslice :
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := hfull s hsle
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # s)) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) s
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      simpa [hslice] using congrArg Finset.card hslice
    omega
  have houtPos : 0 < #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) := by
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) =
          Nat.choose (2 * m + 1) ((rmin - 1) + 1) - #(𝒟 # ((rmin - 1) + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) ((rmin - 1) + 1)
    omega
  simpa [Nat.sub_add_cancel hrmin_pos'] using
    hOut (m := m) (r := rmin - 1) (𝒟 := 𝒟) hmin hrpred_lt_m houtZero houtPos

/-- Odd-dimensional reduction: once a half-cube down-set is known to contain every slice up to the
middle rank, the sharp boundary lower bound follows. -/
theorem choose_middle_le_card_positiveBoundary_of_odd_initial_slices_full
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hne : 𝒟.Nonempty) (h𝒟 : IsDownSetFamily 𝒟)
    (hhalf : 𝒟.card = 2 ^ (2 * m))
    (hfull : ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m + 1) r ≤ #(𝒟 # r)) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  have hs : Finset.range (m + 1) ⊆ Finset.range (2 * m + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hsum :=
    sum_choose_sub_le_card_positiveBoundary_add_sum_card_slice_succ_of_card_slice_ge_choose_sub_on
      (𝒟 := 𝒟) (s := Finset.range (m + 1)) (j := fun _ => 0) hs h𝒟
      (by intro r hr; simp)
      (by
        intro r hr
        simpa using hfull r hr)
  have hslice :
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # (r + 1))) ≤
        𝒟.card - 1 := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # (r + 1))) ≤
        Finset.sum (Finset.range (2 * m + 1)) (fun r => #(𝒟 # (r + 1))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => Nat.zero_le _
      _ = 𝒟.card - 1 := by
        simpa using sum_card_slice_succ_eq_card_sub_one_of_nonempty_isDownSetFamily hne h𝒟
  have hmain :
      2 ^ (2 * m) - 1 + Nat.choose (2 * m + 1) m ≤
        #(positiveBoundary 𝒟) + (2 ^ (2 * m) - 1) := by
    calc
      2 ^ (2 * m) - 1 + Nat.choose (2 * m + 1) m =
        Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) (r + 1)) := by
        symm
        exact sum_range_choose_succ_halfway_odd m
      _ ≤ #(positiveBoundary 𝒟) +
            Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # (r + 1))) := hsum
      _ ≤ #(positiveBoundary 𝒟) + (𝒟.card - 1) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hslice #(positiveBoundary 𝒟)
      _ = #(positiveBoundary 𝒟) + (2 ^ (2 * m) - 1) := by
        rw [hhalf]
  omega

/-- Vanishing lower boundary slices are already enough to close the sharp odd half-cube boundary
bound, via exact shadow propagation of the full lower cube. -/
theorem choose_middle_le_card_positiveBoundary_of_lower_boundary_slices_vanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hhalf : 𝒟.card = 2 ^ (2 * m))
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hhalf] using hpow)
  refine choose_middle_le_card_positiveBoundary_of_odd_initial_slices_full hne h𝒟 hhalf ?_
  intro r hr
  exact le_of_eq (odd_initial_slices_full_of_lower_boundary_slices_vanish hne h𝒟 hvanish r hr).symm

theorem choose_middle_le_upperShadowGap_of_lower_boundary_slices_vanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hhalf : 𝒟.card = 2 ^ (2 * m))
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    Nat.choose (2 * m + 1) m ≤ upperShadowGap 𝒟 := by
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using
    choose_middle_le_card_positiveBoundary_of_lower_boundary_slices_vanish h𝒟 hhalf hvanish

theorem card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 1) m := by
  have hle :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary (oddLowerHalfFamily m)) :=
    hmin.2.2 (𝒜 := oddLowerHalfFamily m)
      (isDownSetFamily_oddLowerHalfFamily m) (card_oddLowerHalfFamily_eq_half_cube m)
  simpa [card_positiveBoundary_oddLowerHalfFamily] using hle

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_lowerBoundarySliceForcesStrictUpperShadowGap
    (hStrict :
      OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement := by
  intro m 𝒟 hmin r hr
  by_contra hnonzero
  have hpos : 0 < #((positiveBoundary 𝒟) # r) := Nat.pos_of_ne_zero hnonzero
  have hgapStrict :
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟 :=
    hStrict hmin ⟨r, hr, hpos⟩
  have hgapLe :
      upperShadowGap 𝒟 ≤ Nat.choose (2 * m + 1) m := by
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1] using
      card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_lt_of_ge hgapLe) hgapStrict

theorem isOddHalfCubeBoundaryMinimizer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟 := by
  have hlower :
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
    choose_middle_le_card_positiveBoundary_of_lower_boundary_slices_vanish hmin.1 hmin.2.1 hvanish
  have hupper :
      #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 1) m :=
    card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact ⟨hmin.1, hmin.2.1, le_antisymm hupper hlower⟩

theorem oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  obtain ⟨𝒟min, hmin⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer m
  have hgapMin :
      Nat.choose (2 * m + 1) m ≤ upperShadowGap 𝒟min :=
    choose_middle_le_upperShadowGap_of_lower_boundary_slices_vanish hmin.1 hmin.2.1 (hVanish hmin)
  have hgapLe :
      upperShadowGap 𝒟min ≤ upperShadowGap 𝒟 := by
    have hbdryLe :
        #(positiveBoundary 𝒟min) ≤ #(positiveBoundary 𝒟) :=
      hmin.2.2 (𝒜 := 𝒟) h𝒟 hcard
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟min) hmin.1,
      upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hbdryLe
  exact hgapMin.trans hgapLe

theorem oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySlicesVanish hVanish)

theorem oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
    (hStrict :
      OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact
    oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_lowerBoundarySliceForcesStrictUpperShadowGap
        hStrict)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
    (hStrict :
      OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
        hStrict)

/-- Direct odd closure from the total-size route: if every odd half-cube family with larger
`totalSize` than the lower-half witness already has strictly larger upper-shadow gap, then the
odd half-cube boundary theorem follows. The new middle-window rigidity lets one apply this
directly to a chosen global minimizer. -/
theorem oddHalfCubeBoundaryLower_of_largerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  intro m 𝒜 h𝒜 hcard
  obtain ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow m
  have hsizeLe : totalSize 𝒟 ≤ totalSize (oddLowerHalfFamily m) := by
    by_contra hgt
    have hgt' : totalSize (oddLowerHalfFamily m) < totalSize 𝒟 := by
      omega
    have hgapStrict :
        Nat.choose (2 * m + 1) m < upperShadowGap 𝒟 :=
      hSize hmin.1 hmin.2.1 hgt'
    have hgapLe :
        upperShadowGap 𝒟 ≤ Nat.choose (2 * m + 1) m := by
      simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1] using
        card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
    exact (not_lt_of_ge hgapLe) hgapStrict
  have hEq : 𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness
      hmin htmid humid hu hfull hzero hmid hsizeLe
  have hminLe :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) :=
    hmin.2.2 (𝒜 := 𝒜) h𝒜 hcard
  calc
    Nat.choose (2 * m + 1) m = #(positiveBoundary 𝒟) := by
      simpa [hEq, card_positiveBoundary_oddLowerHalfFamily]
    _ ≤ #(positiveBoundary 𝒜) := hminLe

theorem oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGap_of_largerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement) :
    OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 t u hmin htmid humid hu hfull hzero hmid hsize
  exact hSize hmin.1 hmin.2.1 hsize

theorem oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGap_of_wideMiddleTransitionWindowForcesStrictUpperShadowGap
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGapStatement) :
    OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 t u hmin htmid humid hu hfull hzero hmid hsize
  by_cases htEq : t = m + 1
  · have hEq : 𝒟 = oddLowerHalfFamily m :=
      eq_oddLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle
        hmin htmid humid hu hfull hzero hmid htEq
    exfalso
    simpa [hEq] using hsize.ne'
  · by_cases huEq : u = m + 1
    · have hEq : 𝒟 = oddLowerHalfFamily m :=
        eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
          hmin htmid humid hu hfull hzero hmid huEq
      exfalso
      simpa [hEq] using hsize.ne'
    · have htlt : t < m + 1 := lt_of_le_of_ne htmid htEq
      have hltu : m + 1 < u := lt_of_le_of_ne humid (by simpa [eq_comm] using huEq)
      exact hWide hmin htlt hltu hfull hzero hmid hsize

/-- Further-localized odd closure: it is enough to prove strict upper-shadow-gap growth only for
the chosen global minimizer carrying middle transition-window data. -/
theorem oddHalfCubeBoundaryLower_of_middleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGap
    (hMid :
      OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  intro m 𝒜 h𝒜 hcard
  obtain ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow m
  have hsizeLe : totalSize 𝒟 ≤ totalSize (oddLowerHalfFamily m) := by
    by_contra hgt
    have hgt' : totalSize (oddLowerHalfFamily m) < totalSize 𝒟 := by
      omega
    have hgapStrict :
        Nat.choose (2 * m + 1) m < upperShadowGap 𝒟 :=
      hMid hmin htmid humid hu hfull hzero hmid hgt'
    have hgapLe :
        upperShadowGap 𝒟 ≤ Nat.choose (2 * m + 1) m := by
      simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1] using
        card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
    exact (not_lt_of_ge hgapLe) hgapStrict
  have hEq : 𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness
      hmin htmid humid hu hfull hzero hmid hsizeLe
  have hminLe :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) :=
    hmin.2.2 (𝒜 := 𝒜) h𝒜 hcard
  calc
    Nat.choose (2 * m + 1) m = #(positiveBoundary 𝒟) := by
      simpa [hEq, card_positiveBoundary_oddLowerHalfFamily]
    _ ≤ #(positiveBoundary 𝒜) := hminLe

theorem oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowForcesStrictUpperShadowGap
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_middleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGap
      (oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictUpperShadowGap_of_wideMiddleTransitionWindowForcesStrictUpperShadowGap
        hWide)

theorem oddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 t u hmin htlt hltu hfull hzero hmid hsize
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 1) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hrm : t - 1 < m := by
    omega
  have hfullSets :
      ∀ s, s ≤ t - 1 →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := by
    intro s hs
    apply slice_eq_powersetCard_of_card_eq_choose
    exact hfull (by omega)
  have hdeficit : #(𝒟 # t) < Nat.choose (2 * m + 1) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  have htsucc : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
  have hdeficit' : #(𝒟 # ((t - 1) + 1)) < Nat.choose (2 * m + 1) ((t - 1) + 1) := by
    simpa [htsucc] using hdeficit
  exact hDef hmin.1 hmin.2.1 hrm hfullSets hdeficit'

theorem oddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDrop_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement) :
    OddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDropStatement := by
  intro m 𝒟 t u hmin htlt hltu hfull hzero hmid hsize
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 1) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hrm : t - 1 < m := by
    omega
  have hfullSets :
      ∀ s, s ≤ t - 1 →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := by
    intro s hs
    apply slice_eq_powersetCard_of_card_eq_choose
    exact hfull (by omega)
  have hdeficit : #(𝒟 # t) < Nat.choose (2 * m + 1) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  have htsucc : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
  have hdeficit' : #(𝒟 # ((t - 1) + 1)) < Nat.choose (2 * m + 1) ((t - 1) + 1) := by
    simpa [htsucc] using hdeficit
  exact hDef hmin.1 hmin.2.1 hrm hfullSets hdeficit'

theorem oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficit_via_wideMiddleTransitionWindow
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowForcesStrictUpperShadowGap
      (oddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
        hDef)

theorem oddHalfCubeBoundaryLower_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficit_via_wideMiddleTransitionWindow
      (oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryLower_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap_via_globalMinimizer
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement := by
  intro m r 𝒟 hmin hrm houtZero houtPos
  have hstrict :
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟 :=
    hOut hmin hrm houtZero houtPos
  have hle :
      upperShadowGap 𝒟 ≤ Nat.choose (2 * m + 1) m := by
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1] using
      card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_lt_of_ge hle) hstrict

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement := by
  intro m 𝒟 hmin r hr
  by_contra hnonzero
  let p : ℕ → Prop :=
    fun t => t ∈ Finset.Icc 1 m ∧ 0 < #((positiveBoundary 𝒟) # t)
  have hp : ∃ t, p t := by
    exact ⟨r, hr, Nat.pos_of_ne_zero hnonzero⟩
  let rmin := Nat.find hp
  have hrmin : p rmin := Nat.find_spec hp
  have hrmin_mem : rmin ∈ Finset.Icc 1 m := hrmin.1
  have hrmin_pos : 0 < #((positiveBoundary 𝒟) # rmin) := hrmin.2
  have hrmin_pos' : 1 ≤ rmin := (Finset.mem_Icc.mp hrmin_mem).1
  have hrmin_le_m : rmin ≤ m := (Finset.mem_Icc.mp hrmin_mem).2
  have hvanish : ∀ s ∈ Finset.Icc 1 (rmin - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    by_contra hsne
    have hspos : 0 < #((positiveBoundary 𝒟) # s) := Nat.pos_of_ne_zero hsne
    have hs_mem : s ∈ Finset.Icc 1 m := by
      rw [Finset.mem_Icc] at hs ⊢
      omega
    have hsP : p s := ⟨hs_mem, hspos⟩
    have hmin_le_s : rmin ≤ s := Nat.find_min' hp hsP
    rw [Finset.mem_Icc] at hs
    omega
  have hrpred_lt_m : rmin - 1 < m := by
    omega
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hfull :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish
  have hdeficit :=
    odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
      hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish
      (by simpa [Nat.sub_add_cancel hrmin_pos'] using hrmin_pos)
  have houtZero :
      ∀ s ∈ Finset.range ((rmin - 1) + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0 := by
    intro s hs
    have hsle : s ≤ rmin - 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hslice :
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := hfull s hsle
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # s)) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) s
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      simpa [hslice] using congrArg Finset.card hslice
    omega
  have houtPos : 0 < #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) := by
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) =
          Nat.choose (2 * m + 1) ((rmin - 1) + 1) - #(𝒟 # ((rmin - 1) + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) ((rmin - 1) + 1)
    omega
  exact hImpossible (m := m) (r := rmin - 1) (𝒟 := 𝒟) hmin hrpred_lt_m houtZero houtPos

theorem oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceImpossible
        hImpossible)

theorem oddHalfCubeMiddleTransitionWindowLowerBoundarySlicesVanish_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))} {t u : ℕ}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 ≤ u) (hu : u ≤ 2 * m + 1)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 1) r)
    (hzero : ∀ ⦃r : ℕ⦄, u ≤ r → r ≤ 2 * m + 1 → #(𝒟 # r) = 0)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 1) r ∧ #(𝒟 # r) ≠ 0) :
    ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0 := by
  intro r hr
  by_contra hnonzero
  let p : ℕ → Prop :=
    fun t0 => t0 ∈ Finset.Icc 1 m ∧ 0 < #((positiveBoundary 𝒟) # t0)
  have hp : ∃ t0, p t0 := by
    exact ⟨r, hr, Nat.pos_of_ne_zero hnonzero⟩
  let rmin := Nat.find hp
  have hrmin : p rmin := Nat.find_spec hp
  have hrmin_mem : rmin ∈ Finset.Icc 1 m := hrmin.1
  have hrmin_pos : 0 < #((positiveBoundary 𝒟) # rmin) := hrmin.2
  have hrmin_pos' : 1 ≤ rmin := (Finset.mem_Icc.mp hrmin_mem).1
  have hrmin_le_m : rmin ≤ m := (Finset.mem_Icc.mp hrmin_mem).2
  have hvanish : ∀ s ∈ Finset.Icc 1 (rmin - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    by_contra hsne
    have hspos : 0 < #((positiveBoundary 𝒟) # s) := Nat.pos_of_ne_zero hsne
    have hs_mem : s ∈ Finset.Icc 1 m := by
      rw [Finset.mem_Icc] at hs ⊢
      omega
    have hsP : p s := ⟨hs_mem, hspos⟩
    have hmin_le_s : rmin ≤ s := Nat.find_min' hp hsP
    rw [Finset.mem_Icc] at hs
    omega
  have hrpred_lt_m : rmin - 1 < m := by
    omega
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hfullSlices :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish
  have houtZero :
      ∀ s ∈ Finset.range ((rmin - 1) + 1), #((((Finset.univ.powerset) \ 𝒟) # s)) = 0 := by
    intro s hs
    have hsle : s ≤ rmin - 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hslice :
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := hfullSlices s hsle
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # s)) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) s
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      simpa [hslice] using congrArg Finset.card hslice
    omega
  have houtPos : 0 < #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) := by
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # ((rmin - 1) + 1))) =
          Nat.choose (2 * m + 1) ((rmin - 1) + 1) - #(𝒟 # ((rmin - 1) + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) ((rmin - 1) + 1)
    have hdeficit :=
      odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
        hne hmin.1 (Nat.le_of_lt hrpred_lt_m) hvanish
        (by simpa [Nat.sub_add_cancel hrmin_pos'] using hrmin_pos)
    omega
  exact
    hImpossible hmin htmid humid hu hfull hzero hmid hrpred_lt_m houtZero houtPos

theorem oddHalfCubeUpperShadowGapLower_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  intro m 𝒜 h𝒜 hcard
  obtain ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow m
  have hgapMin :
      Nat.choose (2 * m + 1) m ≤ upperShadowGap 𝒟 := by
    exact
      choose_middle_le_upperShadowGap_of_lower_boundary_slices_vanish hmin.1 hmin.2.1
        (oddHalfCubeMiddleTransitionWindowLowerBoundarySlicesVanish_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
          hImpossible hmin htmid humid hu hfull hzero hmid)
  have hgapLe :
      upperShadowGap 𝒟 ≤ upperShadowGap 𝒜 := by
    have hbdryLe :
        #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) :=
      hmin.2.2 (𝒜 := 𝒜) h𝒜 hcard
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1,
      upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒜) h𝒜] using hbdryLe
  exact hgapMin.trans hgapLe

theorem oddHalfCubeBoundaryLower_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
        hImpossible)

theorem oddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossible_of_wideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement := by
  intro m 𝒟 t u hmin htmid humid hu hfull hzero hmid r hrm houtZero houtPos
  by_cases htEq : t = m + 1
  · have hEq : 𝒟 = oddLowerHalfFamily m :=
      eq_oddLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle
        hmin htmid humid hu hfull hzero hmid htEq
    have hsliceCard :
        #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1) := by
      simpa [hEq] using
        (oddLowerHalfFamily_has_exact_slice_profile m).1 (r + 1)
          (Finset.mem_range.mpr (Nat.succ_lt_succ hrm))
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) =
          Nat.choose (2 * m + 1) (r + 1) - #(𝒟 # (r + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) (r + 1)
    omega
  · by_cases huEq : u = m + 1
    · have hEq : 𝒟 = oddLowerHalfFamily m :=
        eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
          hmin htmid humid hu hfull hzero hmid huEq
      have hsliceCard :
          #(𝒟 # (r + 1)) = Nat.choose (2 * m + 1) (r + 1) := by
        simpa [hEq] using
          (oddLowerHalfFamily_has_exact_slice_profile m).1 (r + 1)
            (Finset.mem_range.mpr (Nat.succ_lt_succ hrm))
      have hOutside :
          #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) =
            Nat.choose (2 * m + 1) (r + 1) - #(𝒟 # (r + 1)) := by
        simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) (r + 1)
      omega
    · have htlt : t < m + 1 := lt_of_le_of_ne htmid htEq
      have hltu : m + 1 < u := lt_of_le_of_ne humid (by simpa [eq_comm] using huEq)
      exact hWide hmin htlt hltu hfull hzero hmid hrm houtZero houtPos

theorem oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_middleTransitionWindowFirstPositiveOutsideSliceImpossible
      (oddHalfCubeMiddleTransitionWindowFirstPositiveOutsideSliceImpossible_of_wideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible
        hWide)

theorem oddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible_of_globalMinimizerInitialFullSlicesStrictSliceDeficitImpossible
    (hLocal :
      OddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossibleStatement) :
    OddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossibleStatement := by
  intro m 𝒟 t u hmin htlt hltu hfull hzero hmid r hrm houtZero houtPos
  have hfullSlices :
      ∀ s, s ≤ r →
        𝒟 # s = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard s := by
    intro s hsle
    have hsZero : #((((Finset.univ.powerset) \ 𝒟) # s)) = 0 :=
      houtZero s (Finset.mem_range.mpr (Nat.lt_succ_of_le hsle))
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # s)) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) s
    have hsliceLe : #(𝒟 # s) ≤ Nat.choose (2 * m + 1) s := by
      exact card_slice_le_choose (𝒟 := 𝒟) (r := s)
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      omega
    exact slice_eq_powersetCard_of_card_eq_choose hsliceCard
  have hdeficit : #(𝒟 # (r + 1)) < Nat.choose (2 * m + 1) (r + 1) := by
    have hOutside :
        #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) =
          Nat.choose (2 * m + 1) (r + 1) - #(𝒟 # (r + 1)) := by
      simpa using card_outside_slice_eq_choose_sub_card_slice (𝒟 := 𝒟) (r + 1)
    omega
  exact hLocal hmin hrm hfullSlices hdeficit

theorem oddHalfCubeBoundaryLower_of_globalMinimizerInitialFullSlicesStrictSliceDeficitImpossible
    (hLocal :
      OddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossibleStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible
      (oddHalfCubeWideMiddleTransitionWindowFirstPositiveOutsideSliceImpossible_of_globalMinimizerInitialFullSlicesStrictSliceDeficitImpossible
        hLocal)

theorem oddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossible_of_initialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossibleStatement := by
  intro m r 𝒟 hmin hrm hfull hdeficit
  have hstrict :
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟) :=
    hDef hmin.1 hmin.2.1 hrm hfull hdeficit
  have hle :
      weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ Nat.choose (2 * m + 1) m := by
    calc
      weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ #(positiveBoundary 𝒟) := by
        simpa [Fintype.card_fin] using weightedDrop_le_card_positiveBoundary (𝒟 := 𝒟)
      _ ≤ Nat.choose (2 * m + 1) m := by
        exact_mod_cast
          card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_le_of_gt hstrict) hle

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
    (hDrop :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement := by
  intro m r 𝒟 hmin hrm houtZero houtPos
  have hstrict :
      Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟) :=
    hDrop hmin hrm houtZero houtPos
  have hle :
      weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ Nat.choose (2 * m + 1) m := by
    calc
      weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ #(positiveBoundary 𝒟) := by
        simpa [Fintype.card_fin] using weightedDrop_le_card_positiveBoundary (𝒟 := 𝒟)
      _ ≤ Nat.choose (2 * m + 1) m := by
        exact_mod_cast
          card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_le_of_gt hstrict) hle

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
    (hDrop :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceImpossible
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
        hDrop)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
    (hDrop :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
        hDrop)

theorem oddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDrop_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement) :
    OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement := by
  intro m r 𝒟 h𝒟 hcard hrm hvanish hboundaryPos
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hcard] using hpow)
  have hfull :=
    odd_initial_slices_eq_powersetCard_of_lower_boundary_slices_vanish_upto
      hne h𝒟 (Nat.le_of_lt hrm) hvanish
  have hdeficit :=
    odd_card_slice_succ_lt_choose_of_lower_boundary_slices_vanish_upto_and_boundary_slice_succ_pos
      hne h𝒟 (Nat.le_of_lt hrm) hvanish hboundaryPos
  exact hDef h𝒟 hcard hrm hfull hdeficit

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop_of_firstBadBoundarySliceForcesStrictWeightedDrop
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement := by
  intro m r 𝒟 hmin hrm houtZero houtPos
  have hvanish : ∀ s ∈ Finset.Icc 1 r, #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    have hsRange : s ∈ Finset.range (r + 1) := by
      exact Finset.mem_range.mpr <|
        lt_of_le_of_lt (Finset.mem_Icc.mp hs).2 (Nat.lt_succ_self r)
    have hsubset :
        ((positiveBoundary 𝒟) # s) ⊆ (((Finset.univ.powerset) \ 𝒟) # s) :=
      positiveBoundary_slice_subset_outside_slice (𝒟 := 𝒟) (r := s)
    have hle :
        #((positiveBoundary 𝒟) # s) ≤ #((((Finset.univ.powerset) \ 𝒟) # s)) :=
      Finset.card_le_card hsubset
    have hzero := houtZero s hsRange
    omega
  have hrlt : r < Fintype.card (Fin (2 * m + 1)) := by
    simpa [Fintype.card_fin] using (show r < 2 * m + 1 by omega)
  have houtZero_r : #((((Finset.univ.powerset) \ 𝒟) # r)) = 0 := by
    exact houtZero r (by simpa using Nat.lt_succ_self r)
  have hsdiffLe :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) * (r + 1) ≤
        #((((Finset.univ.powerset) \ 𝒟) # r)) * (2 * m + 1 - r) := by
    simpa [Fintype.card_fin] using
      (card_outside_slice_succ_sdiff_boundary_slice_mul_le_card_outside_slice_mul
        (𝒟 := 𝒟) (r := r) hrlt)
  have hsdiffMulZero :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) * (r + 1) =
        0 := by
    have hle' := hsdiffLe
    rw [houtZero_r, zero_mul] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hsdiffZero :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) = 0 := by
    exact (Nat.mul_eq_zero.mp hsdiffMulZero).resolve_right (Nat.succ_ne_zero r)
  have hsubset :
      ((positiveBoundary 𝒟) # (r + 1)) ⊆ (((Finset.univ.powerset) \ 𝒟) # (r + 1)) :=
    positiveBoundary_slice_subset_outside_slice (𝒟 := 𝒟) (r := r + 1)
  have hdecomp :
      #((((Finset.univ.powerset) \ 𝒟) # (r + 1)) \ (((positiveBoundary 𝒟) # (r + 1)))) +
          #(((positiveBoundary 𝒟) # (r + 1))) =
        #((((Finset.univ.powerset) \ 𝒟) # (r + 1))) := by
    exact Finset.card_sdiff_add_card_eq_card hsubset
  have hboundaryPos : 0 < #((positiveBoundary 𝒟) # (r + 1)) := by
    omega
  exact hFirstBad (m := m) (r := r) (𝒟 := 𝒟) hmin.1 hmin.2.1 hrm hvanish hboundaryPos

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop_of_initialFullSlicesStrictSliceDeficit
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDropStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop_of_firstBadBoundarySliceForcesStrictWeightedDrop
      (oddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDrop_of_initialFullSlicesStrictSliceDeficit
        hDef)

theorem oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerInitialFullSlicesStrictSliceDeficitImpossible
      (oddHalfCubeBoundaryGlobalMinimizerInitialFullSlicesStrictSliceDeficitImpossible_of_initialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop
        hDef)

theorem oddHalfCubeBoundaryLower_of_largerTotalSizeThanWitnessForcesStrictWeightedDrop
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop
      (oddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictWeightedDrop_of_largerTotalSizeThanWitness
        hSize)

theorem oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDrop_of_largerTotalSizeThanWitnessForcesStrictWeightedDrop
    (hSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictWeightedDropStatement) :
    OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDropStatement := by
  intro m 𝒟 t u hmin htmid humid hu hfull hzero hmid hsize
  exact hSize hmin.1 hmin.2.1 hsize

theorem oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDrop_of_wideMiddleTransitionWindowForcesStrictWeightedDrop
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDropStatement) :
    OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDropStatement := by
  intro m 𝒟 t u hmin htmid humid hu hfull hzero hmid hsize
  by_cases htEq : t = m + 1
  · have hEq : 𝒟 = oddLowerHalfFamily m :=
      eq_oddLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle
        hmin htmid humid hu hfull hzero hmid htEq
    exfalso
    simpa [hEq] using hsize.ne'
  · by_cases huEq : u = m + 1
    · have hEq : 𝒟 = oddLowerHalfFamily m :=
        eq_oddLowerHalfFamily_of_middleTransitionWindow_of_u_eq_middle
          hmin htmid humid hu hfull hzero hmid huEq
      exfalso
      simpa [hEq] using hsize.ne'
    · have htlt : t < m + 1 := lt_of_le_of_ne htmid htEq
      have hltu : m + 1 < u := lt_of_le_of_ne humid (by simpa [eq_comm] using huEq)
      exact hWide hmin htlt hltu hfull hzero hmid hsize

/-- Weighted-drop analogue of the middle-window odd closure: it is enough to prove strict
weighted-drop growth only for the chosen global minimizer carrying middle transition-window data. -/
theorem oddHalfCubeBoundaryLower_of_middleTransitionWindowLargerTotalSizeForcesStrictWeightedDrop
    (hMid :
      OddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  intro m 𝒜 h𝒜 hcard
  obtain ⟨𝒟, t, u, hmin, htmid, humid, hu, hfull, hzero, hmid⟩ :=
    exists_isOddHalfCubeBoundaryGlobalMinimizer_middleTransitionWindow m
  have hsizeLe : totalSize 𝒟 ≤ totalSize (oddLowerHalfFamily m) := by
    by_contra hgt
    have hgt' : totalSize (oddLowerHalfFamily m) < totalSize 𝒟 := by
      omega
    have hdropStrict :
        Nat.choose (2 * m + 1) m < weightedDrop (2 * m + 1) (sliceDensity 𝒟) :=
      hMid hmin htmid humid hu hfull hzero hmid hgt'
    have hdropLe :
        weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ Nat.choose (2 * m + 1) m := by
      calc
        weightedDrop (2 * m + 1) (sliceDensity 𝒟) ≤ #(positiveBoundary 𝒟) := by
          simpa [Fintype.card_fin] using weightedDrop_le_card_positiveBoundary (𝒟 := 𝒟)
        _ ≤ Nat.choose (2 * m + 1) m := by
          exact_mod_cast
            card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
    exact (not_lt_of_ge hdropLe) hdropStrict
  have hEq : 𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness
      hmin htmid humid hu hfull hzero hmid hsizeLe
  have hminLe :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) :=
    hmin.2.2 (𝒜 := 𝒜) h𝒜 hcard
  calc
    Nat.choose (2 * m + 1) m = #(positiveBoundary 𝒟) := by
      simpa [hEq, card_positiveBoundary_oddLowerHalfFamily]
    _ ≤ #(positiveBoundary 𝒜) := hminLe

theorem oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowForcesStrictWeightedDrop
    (hWide :
      OddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_middleTransitionWindowLargerTotalSizeForcesStrictWeightedDrop
      (oddHalfCubeMiddleTransitionWindowLargerTotalSizeForcesStrictWeightedDrop_of_wideMiddleTransitionWindowForcesStrictWeightedDrop
        hWide)

theorem oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_lowerBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGapStatement := by
  intro m 𝒟 t u hmin htlt hltu hfull hzero hmid hsize
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 1) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hrm : t - 1 < m := by
    omega
  have hvanish : ∀ s ∈ Finset.Icc 1 (t - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    have hsIcc := Finset.mem_Icc.mp hs
    have hspos : 0 < s := by
      omega
    have hslt : s < t := by
      omega
    have hslicePred :
        𝒟 # (s - 1) = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard (s - 1) := by
      apply slice_eq_powersetCard_of_card_eq_choose
      exact hfull (by omega)
    have hboundary :
        #((positiveBoundary 𝒟) # s) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      exact
        card_positiveBoundary_slice_eq_choose_sub_card_slice_of_pred_slice_eq_powersetCard
          hspos hmin.1 hslicePred
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      exact hfull hslt
    omega
  have hboundary :
      #((positiveBoundary 𝒟) # t) =
        Nat.choose (2 * m + 1) t - #(𝒟 # t) := by
    have hslicePred :
        𝒟 # (t - 1) = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard (t - 1) := by
      apply slice_eq_powersetCard_of_card_eq_choose
      exact hfull (by omega)
    exact
      card_positiveBoundary_slice_eq_choose_sub_card_slice_of_pred_slice_eq_powersetCard
        htpos hmin.1 hslicePred
  have hdeficit : #(𝒟 # t) < Nat.choose (2 * m + 1) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  have hboundaryPos : 0 < #((positiveBoundary 𝒟) # t) := by
    omega
  have htsucc : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
  have hboundaryPos' : 0 < #((positiveBoundary 𝒟) # ((t - 1) + 1)) := by
    simpa [htsucc] using hboundaryPos
  exact hFirstBad hmin.1 hmin.2.1 hrm hvanish hboundaryPos'

theorem oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictUpperShadowGap_via_wideMiddleTransitionWindow
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowForcesStrictUpperShadowGap
      (oddHalfCubeWideMiddleTransitionWindowForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
        hFirstBad)

theorem oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictUpperShadowGap
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
        hFirstBad)

theorem oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
        hDef)

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_firstBadBoundarySliceForcesStrictUpperShadowGap
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
      (by
        intro m r 𝒟 hmin hrm houtZero houtPos
        exact
          (oddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGap_of_firstBadBoundarySliceForcesStrictUpperShadowGap
            hFirstBad) hmin.1 hmin.2.1 hrm houtZero houtPos)

theorem oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictUpperShadowGap_via_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_firstBadBoundarySliceForcesStrictUpperShadowGap
        hFirstBad)

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_initialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_firstBadBoundarySliceForcesStrictUpperShadowGap
      (oddHalfCubeFirstBadBoundarySliceForcesStrictUpperShadowGap_of_initialFullSlicesStrictSliceDeficit
        hDef)

theorem oddHalfCubeBoundaryLower_of_initialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap_via_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hDef :
      OddHalfCubeInitialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_initialFullSlicesStrictSliceDeficitForcesStrictUpperShadowGap
        hDef)

theorem oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement := by
  intro m r 𝒟 hmin hrm houtZero houtPos
  have hstrict :
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒟 :=
    hOut hmin.1 hmin.2.1 hrm houtZero houtPos
  have hle :
      upperShadowGap 𝒟 ≤ Nat.choose (2 * m + 1) m := by
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) hmin.1] using
      card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_lt_of_ge hle) hstrict

theorem oddHalfCubeBoundaryLower_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap_via_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hOut :
      OddHalfCubeFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossible_of_firstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDrop_of_firstBadBoundarySliceForcesStrictWeightedDrop
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement) :
    OddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDropStatement := by
  intro m 𝒟 t u hmin htlt hltu hfull hzero hmid hsize
  have hne : 𝒟.Nonempty := by
    refine Finset.card_pos.mp ?_
    simpa [hmin.2.1] using (pow_pos (by decide : 0 < 2) (2 * m))
  have hslice0 : #(𝒟 # 0) = 1 := by
    exact card_slice_zero_eq_one_of_nonempty_isDownSetFamily hne hmin.1
  have htpos : 0 < t := by
    by_contra htz
    have ht0 : t = 0 := by omega
    have hnotFull0 : #(𝒟 # 0) ≠ Nat.choose (2 * m + 1) 0 := by
      exact (hmid (ht0 ▸ le_rfl) (ht0 ▸ lt_trans htlt hltu)).1
    simp [hslice0] at hnotFull0
  have hrm : t - 1 < m := by
    omega
  have hvanish : ∀ s ∈ Finset.Icc 1 (t - 1), #((positiveBoundary 𝒟) # s) = 0 := by
    intro s hs
    have hsIcc := Finset.mem_Icc.mp hs
    have hspos : 0 < s := by
      omega
    have hslt : s < t := by
      omega
    have hslicePred :
        𝒟 # (s - 1) = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard (s - 1) := by
      apply slice_eq_powersetCard_of_card_eq_choose
      exact hfull (by omega)
    have hboundary :
        #((positiveBoundary 𝒟) # s) =
          Nat.choose (2 * m + 1) s - #(𝒟 # s) := by
      exact
        card_positiveBoundary_slice_eq_choose_sub_card_slice_of_pred_slice_eq_powersetCard
          hspos hmin.1 hslicePred
    have hsliceCard : #(𝒟 # s) = Nat.choose (2 * m + 1) s := by
      exact hfull hslt
    omega
  have hboundary :
      #((positiveBoundary 𝒟) # t) =
        Nat.choose (2 * m + 1) t - #(𝒟 # t) := by
    have hslicePred :
        𝒟 # (t - 1) = (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard (t - 1) := by
      apply slice_eq_powersetCard_of_card_eq_choose
      exact hfull (by omega)
    exact
      card_positiveBoundary_slice_eq_choose_sub_card_slice_of_pred_slice_eq_powersetCard
        htpos hmin.1 hslicePred
  have hdeficit : #(𝒟 # t) < Nat.choose (2 * m + 1) t := by
    exact lt_of_le_of_ne (card_slice_le_choose (𝒟 := 𝒟) (r := t))
      (hmid le_rfl (lt_trans htlt hltu)).1
  have hboundaryPos : 0 < #((positiveBoundary 𝒟) # t) := by
    omega
  have htsucc : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
  have hboundaryPos' : 0 < #((positiveBoundary 𝒟) # ((t - 1) + 1)) := by
    simpa [htsucc] using hboundaryPos
  exact hFirstBad hmin.1 hmin.2.1 hrm hvanish hboundaryPos'

theorem oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictWeightedDrop_via_wideMiddleTransitionWindow
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_wideMiddleTransitionWindowForcesStrictWeightedDrop
      (oddHalfCubeWideMiddleTransitionWindowForcesStrictWeightedDrop_of_firstBadBoundarySliceForcesStrictWeightedDrop
        hFirstBad)

theorem oddHalfCubeBoundaryLower_of_firstBadBoundarySliceForcesStrictWeightedDrop
    (hFirstBad :
      OddHalfCubeFirstBadBoundarySliceForcesStrictWeightedDropStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop
      (oddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictWeightedDrop_of_firstBadBoundarySliceForcesStrictWeightedDrop
        hFirstBad)

theorem exact_slice_profile_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) := by
  have h𝒟 : IsDownSetFamily 𝒟 := hmin.1
  have hcard : 𝒟.card = 2 ^ (2 * m) := hmin.2.1
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hcard] using hpow)
  have hlower :
      ∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r :=
    odd_initial_slices_full_of_lower_boundary_slices_vanish hne h𝒟 hvanish
  have hsumAll :
      Finset.sum (Finset.range (2 * m + 2)) (fun r => #(𝒟 # r)) = 𝒟.card := by
    simpa [Nat.range_succ_eq_Iic, Fintype.card_fin] using (Finset.sum_card_slice 𝒟)
  have hsumLowerChoose :
      Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) = 2 ^ (2 * m) := by
    simpa [show 4 ^ m = 2 ^ (2 * m) by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]] using
      Nat.sum_range_choose_halfway m
  have hsumLower :
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # r)) = 2 ^ (2 * m) := by
    calc
      Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # r)) =
          Finset.sum (Finset.range (m + 1)) (fun r => Nat.choose (2 * m + 1) r) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            exact hlower r hr
      _ = 2 ^ (2 * m) := hsumLowerChoose
  have hmle : m + 1 ≤ 2 * m + 2 := by
    omega
  have hsumUpper :
      Finset.sum (Finset.Ico (m + 1) (2 * m + 2)) (fun r => #(𝒟 # r)) = 0 := by
    have hsplit :
        Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # r)) +
            Finset.sum (Finset.Ico (m + 1) (2 * m + 2)) (fun r => #(𝒟 # r)) =
          2 ^ (2 * m) := by
      calc
        Finset.sum (Finset.range (m + 1)) (fun r => #(𝒟 # r)) +
            Finset.sum (Finset.Ico (m + 1) (2 * m + 2)) (fun r => #(𝒟 # r)) =
          Finset.sum (Finset.range (2 * m + 2)) (fun r => #(𝒟 # r)) := by
            exact Finset.sum_range_add_sum_Ico (fun r => #(𝒟 # r)) hmle
        _ = 𝒟.card := hsumAll
        _ = 2 ^ (2 * m) := hcard
    have hleZero :
        Finset.sum (Finset.Ico (m + 1) (2 * m + 2)) (fun r => #(𝒟 # r)) ≤ 0 := by
      omega
    exact le_antisymm hleZero (Nat.zero_le _)
  refine ⟨hlower, ?_⟩
  intro r hmr
  by_cases hrle : r ≤ 2 * m + 1
  · have hrIco : r ∈ Finset.Ico (m + 1) (2 * m + 2) := by
      rw [Finset.mem_Ico]
      omega
    have hleTerm :
        #(𝒟 # r) ≤ Finset.sum (Finset.Ico (m + 1) (2 * m + 2)) (fun q => #(𝒟 # q)) := by
      simpa using
        (Finset.single_le_sum
          (f := fun q => #(𝒟 # q))
          (fun _ _ => Nat.zero_le _)
          hrIco)
    omega
  · have hrgt : 2 * m + 1 < r := by
      omega
    have hsubset : 𝒟 # r ⊆ (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard r :=
      Set.Sized.subset_powersetCard_univ (Finset.sized_slice (𝒜 := 𝒟) (r := r))
    have hleCard :
        #(𝒟 # r) ≤ #((Finset.univ : Finset (Fin (2 * m + 1))).powersetCard r) :=
      Finset.card_le_card hsubset
    have hzeroCard :
        #((Finset.univ : Finset (Fin (2 * m + 1))).powersetCard r) = 0 := by
      rw [Finset.card_powersetCard]
      simpa [Fintype.card_fin] using (Nat.choose_eq_zero_of_lt hrgt)
    omega

theorem exact_slice_profile_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
      (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) := by
  exact
    exact_slice_profile_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
      (isOddHalfCubeBoundaryMinimizer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
        hmin hvanish)
      hvanish

theorem eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    𝒟 = oddLowerHalfFamily m := by
  have hslices :
      (∀ r ∈ Finset.range (m + 1), #(𝒟 # r) = Nat.choose (2 * m + 1) r) ∧
        (∀ r, m + 1 ≤ r → #(𝒟 # r) = 0) :=
    exact_slice_profile_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
      hmin hvanish
  exact eq_oddLowerHalfFamily_of_exact_slice_profile hslices.1 hslices.2

theorem positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    positiveBoundary 𝒟 = oddMiddleLayer m := by
  have hEq :
      𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
      hmin hvanish
  simpa [hEq] using positiveBoundary_oddLowerHalfFamily m

theorem minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hvanish : ∀ r ∈ Finset.Icc 1 m, #((positiveBoundary 𝒟) # r) = 0) :
    minimalOutside 𝒟 = oddMiddleLayer m := by
  have hEq :
      𝒟 = oddLowerHalfFamily m :=
    eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
      hmin hvanish
  simpa [hEq] using minimalOutside_oddLowerHalfFamily m

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerLowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  intro m 𝒟 hmin
  rw [minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
      hmin (hVanish hmin)]
  exact le_of_eq (card_oddMiddleLayer m).symm

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceImpossible
        hImpossible)

theorem ncard_upperClosure_minimalOutside_eq_two_pow_of_card_eq_half_cube
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    (↑(upperClosure (minimalOutside 𝒟 : Set (Finset (Fin (2 * m + 1))))) :
      Set (Finset (Fin (2 * m + 1)))).ncard = 2 ^ (2 * m) := by
  rw [upperClosure_minimalOutside_eq_compl h𝒟, Set.ncard_compl]
  rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin, Set.ncard_coe_finset,
    hcard]
  rw [pow_succ, Nat.mul_comm, two_mul, Nat.add_sub_cancel_left]

theorem oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower
    (hAntichain : OddAntichainUpperClosureLowerStatement) :
    OddHalfCubeMinimalOutsideLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  exact hAntichain (isAntichain_minimalOutside 𝒟)
    (ncard_upperClosure_minimalOutside_eq_two_pow_of_card_eq_half_cube h𝒟 hcard)

theorem oddAntichainUpperClosureLower_of_minimalOutsideLower
    (hMinOut : OddHalfCubeMinimalOutsideLowerStatement) :
    OddAntichainUpperClosureLowerStatement := by
  intro m 𝒜 h𝒜 hupper
  classical
  let 𝒟 : Finset (Finset (Fin (2 * m + 1))) :=
    ((↑(upperClosure (𝒜 : Set (Finset (Fin (2 * m + 1))))) :
      Set (Finset (Fin (2 * m + 1)))).toFinset)ᶜ
  have h𝒟 :
      IsDownSetFamily 𝒟 := by
    change IsLowerSet (𝒟 : Set (Finset (Fin (2 * m + 1))))
    rw [show (𝒟 : Set (Finset (Fin (2 * m + 1)))) =
        ((↑(upperClosure (𝒜 : Set (Finset (Fin (2 * m + 1))))) :
          Set (Finset (Fin (2 * m + 1))))ᶜ) by
        simp [𝒟]]
    exact (upperClosure (𝒜 : Set (Finset (Fin (2 * m + 1))))).upper.compl
  have hcard𝒟 : 𝒟.card = 2 ^ (2 * m) := by
    rw [Finset.card_compl, ← Set.ncard_eq_toFinset_card', hupper]
    rw [Fintype.card_finset, Fintype.card_fin]
    rw [pow_succ, Nat.mul_comm, two_mul, Nat.add_sub_cancel_left]
  have hEq : minimalOutside 𝒟 = 𝒜 := by
    apply eq_of_upperClosure_eq_of_isAntichain
    · exact isAntichain_minimalOutside 𝒟
    · exact h𝒜
    · rw [upperClosure_minimalOutside_eq_compl h𝒟]
      ext s
      simp [𝒟]
  simpa [hEq] using hMinOut h𝒟 hcard𝒟

theorem oddAntichainUpperClosureLower_iff_oddHalfCubeMinimalOutsideLower :
    OddAntichainUpperClosureLowerStatement ↔ OddHalfCubeMinimalOutsideLowerStatement := by
  constructor
  · exact oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower
  · exact oddAntichainUpperClosureLower_of_minimalOutsideLower

theorem not_OddAntichainUpperClosureLowerStatement :
    ¬ OddAntichainUpperClosureLowerStatement := by
  intro hAntichain
  exact not_OddHalfCubeMinimalOutsideLowerStatement
    (oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower hAntichain)

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_antichainUpperClosureLower
    (hAntichain : OddAntichainUpperClosureLowerStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  intro m 𝒟 hmin
  exact oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower hAntichain hmin.1 hmin.2.1

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_minimalOutsideLower
    (hMinOut : OddHalfCubeMinimalOutsideLowerStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  intro m 𝒟 hmin
  exact hMinOut hmin.1 hmin.2.1

theorem isOddHalfCubeBoundaryMinimizer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hMinOut : Nat.choose (2 * m + 1) m ≤ #(minimalOutside 𝒟)) :
    IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟 := by
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hlower :
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
    hMinOut.trans
      (card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily hmin.1 hne)
  have hupper :
      #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 1) m :=
    card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
  exact ⟨hmin.1, hmin.2.1, le_antisymm hupper hlower⟩

theorem card_minimalOutside_eq_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hMinOut : Nat.choose (2 * m + 1) m ≤ #(minimalOutside 𝒟)) :
    #(minimalOutside 𝒟) = Nat.choose (2 * m + 1) m := by
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hupper :
      #(minimalOutside 𝒟) ≤ Nat.choose (2 * m + 1) m :=
    (card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily hmin.1 hne).trans
      (card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin)
  exact le_antisymm hupper hMinOut

theorem minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hMinOut : Nat.choose (2 * m + 1) m ≤ #(minimalOutside 𝒟)) :
    minimalOutside 𝒟 = positiveBoundary 𝒟 := by
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hsub :
      minimalOutside 𝒟 ⊆ positiveBoundary 𝒟 :=
    minimalOutside_subset_positiveBoundary_of_nonempty_isDownSetFamily hmin.1 hne
  apply Finset.eq_of_subset_of_card_le hsub
  have hsharp :
      IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟 :=
    isOddHalfCubeBoundaryMinimizer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
      hmin hMinOut
  have hcardMinOut :
      #(minimalOutside 𝒟) = Nat.choose (2 * m + 1) m :=
    card_minimalOutside_eq_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
      hmin hMinOut
  simpa [hsharp.2.2, hcardMinOut]

theorem oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerMinimalOutsideLower
    (hMinOut : OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement) :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement := by
  intro m 𝒟 hmin
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  refine ⟨?_, ?_⟩
  · rw [← minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryGlobalMinimizer_of_minimalOutsideLower
      hmin (hMinOut hmin)]
    exact isAntichain_minimalOutside 𝒟
  · have hupper :
        #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 1) m :=
      card_positiveBoundary_le_choose_middle_of_isOddHalfCubeBoundaryGlobalMinimizer hmin
    have hlower :
        Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
      (hMinOut hmin).trans
        (card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily hmin.1 hne)
    exact le_antisymm hupper hlower

theorem oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerPositiveBoundaryAntichain
    (hAnt :
      OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement) :
    OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  intro m 𝒟 hmin
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hEq :
      positiveBoundary 𝒟 = minimalOutside 𝒟 :=
    positiveBoundary_eq_minimalOutside_of_nonempty_isDownSetFamily_of_isAntichain
      hmin.1 hne (hAnt hmin).1
  rw [← hEq, (hAnt hmin).2]

theorem
    oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_iff_globalMinimizerMinimalOutsideLower :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement ↔
      OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement := by
  constructor
  · exact oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerPositiveBoundaryAntichain
  · exact oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerMinimalOutsideLower

theorem oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerLowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanishStatement) :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement := by
  intro m 𝒟 hmin
  have hEq :
      positiveBoundary 𝒟 = oddMiddleLayer m :=
    positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryGlobalMinimizer_of_lowerBoundarySlicesVanish
      hmin (hVanish hmin)
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact isAntichain_oddMiddleLayer m
  · rw [hEq, card_oddMiddleLayer]

theorem oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
    (hOut :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGapStatement) :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceForcesStrictUpperShadowGap
        hOut)

theorem oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerFirstPositiveOutsideSliceImpossible
    (hImpossible :
      OddHalfCubeBoundaryGlobalMinimizerFirstPositiveOutsideSliceImpossibleStatement) :
    OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement := by
  exact
    oddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichain_of_globalMinimizerLowerBoundarySlicesVanish
      (oddHalfCubeBoundaryGlobalMinimizerLowerBoundarySlicesVanish_of_globalMinimizerFirstPositiveOutsideSliceImpossible
        hImpossible)

theorem oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower
    (hMinOut : OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  obtain ⟨𝒟min, hmin⟩ := exists_isOddHalfCubeBoundaryGlobalMinimizer m
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟min.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hmin.2.1] using hpow)
  have hmoLe :
      #(minimalOutside 𝒟min) ≤ #(positiveBoundary 𝒟min) :=
    card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily hmin.1 hne
  have hbdryMin :
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟min) :=
    (hMinOut hmin).trans hmoLe
  have hbdryLe :
      #(positiveBoundary 𝒟min) ≤ #(positiveBoundary 𝒟) :=
    hmin.2.2 (𝒜 := 𝒟) h𝒟 hcard
  have hbdry :
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
    hbdryMin.trans hbdryLe
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hbdry

theorem oddHalfCubeUpperShadowGapLower_of_globalMinimizerPositiveBoundaryAntichain
    (hAnt : OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact
    oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower
      (oddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLower_of_globalMinimizerPositiveBoundaryAntichain
        hAnt)

theorem oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower
    (hMinOut : OddHalfCubeMinimalOutsideLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  have hpow : 0 < 2 ^ (2 * m) := by
    positivity
  have hne : 𝒟.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hcard] using hpow)
  have hbdry :
      Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) :=
    (hMinOut h𝒟 hcard).trans
      (card_minimalOutside_le_card_positiveBoundary_of_nonempty_isDownSetFamily h𝒟 hne)
  simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒟) h𝒟] using hbdry

theorem oddHalfCubeUpperShadowGapLower_of_antichainUpperClosureLower
    (hAntichain : OddAntichainUpperClosureLowerStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower
    (oddHalfCubeMinimalOutsideLower_of_antichainUpperClosureLower hAntichain)

theorem oddHalfCubeBoundaryLower_of_antichainUpperClosureLower
    (hAntichain : OddAntichainUpperClosureLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
    (oddHalfCubeUpperShadowGapLower_of_antichainUpperClosureLower hAntichain)

theorem oddHalfCubeBoundaryLower_of_minimalOutsideLower
    (hMinOut : OddHalfCubeMinimalOutsideLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
    (oddHalfCubeUpperShadowGapLower_of_minimalOutsideLower hMinOut)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerMinimalOutsideLower
    (hMinOut : OddHalfCubeBoundaryGlobalMinimizerMinimalOutsideLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_globalMinimizerMinimalOutsideLower hMinOut)

theorem oddHalfCubeBoundaryLower_of_globalMinimizerPositiveBoundaryAntichain
    (hAnt : OddHalfCubeBoundaryGlobalMinimizerPositiveBoundaryAntichainStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact
    oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower
      (oddHalfCubeUpperShadowGapLower_of_globalMinimizerPositiveBoundaryAntichain hAnt)

theorem oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement) :
    OddHalfCubeBoundaryMinimizerExactProfileStatement := by
  intro m 𝒟 h𝒟 hcard hbdry
  exact
    exact_slice_profile_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
      ⟨h𝒟, hcard, hbdry⟩
      (hVanish ⟨h𝒟, hcard, hbdry⟩)

theorem oddHalfCubeBoundaryMinimizerExactProfileStatement_iff_lowerBoundarySlicesVanishStatement :
    OddHalfCubeBoundaryMinimizerExactProfileStatement ↔
      OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement := by
  constructor
  · exact oddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanish_of_exactProfile
  · exact oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish

theorem eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    𝒟 = oddLowerHalfFamily m := by
  exact
    eq_oddLowerHalfFamily_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      (oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish hVanish) hmin

theorem positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    positiveBoundary 𝒟 = oddMiddleLayer m := by
  exact
    positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      (oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish hVanish) hmin

theorem minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    minimalOutside 𝒟 = positiveBoundary 𝒟 := by
  exact
    minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      (oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish hVanish) hmin

theorem minimalOutside_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    minimalOutside 𝒟 = oddMiddleLayer m := by
  rw [minimalOutside_eq_positiveBoundary_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
      hVanish hmin,
    positiveBoundary_eq_oddMiddleLayer_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
      hVanish hmin]

theorem oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_lowerBoundarySlicesVanish
    (hVanish : OddHalfCubeBoundaryMinimizerLowerBoundarySlicesVanishStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (hmin : IsOddHalfCubeBoundaryMinimizer (m := m) 𝒟) :
    ∀ r ∈ Finset.range (m + 1), Nat.choose (2 * m) r ≤ #(𝒟 # r) := by
  exact
    oddHalfCubeSliceThreshold_of_isOddHalfCubeBoundaryMinimizer_of_exactProfile
      (oddHalfCubeBoundaryMinimizerExactProfile_of_lowerBoundarySlicesVanish hVanish) hmin

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
  let 𝒩 : Finset (Finset (Fin n)) := predFamily (𝒟.nonMemberSubfamily 0)
  let ℳ : Finset (Finset (Fin n)) := predFamily (𝒟.memberSubfamily 0)
  have hcard' : 𝒟.card = 2 * 2 ^ (n - 1) := by
    calc
      𝒟.card = 2 ^ n := hcard
      _ = 2 * 2 ^ (n - 1) := by
        rw [← Nat.succ_pred_eq_of_pos hn]
        simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc]
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hmbal : #(𝒟.memberSubfamily 0) = 2 ^ (n - 1) := by
    omega
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using isDownSetFamily_predFamily_nonMemberSubfamily h𝒟
  have hℳdown : IsDownSetFamily ℳ := by
    simpa [ℳ] using isDownSetFamily_predFamily_memberSubfamily h𝒟
  have h𝒩card : 𝒩.card = 2 ^ (n - 1) := by
    simpa [𝒩, hbal] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have hℳcard : ℳ.card = 2 ^ (n - 1) := by
    simpa [ℳ, hmbal] using card_predFamily_memberSubfamily (𝒜 := 𝒟)
  have hpowpos : 0 < 2 ^ (n - 1) := by
    positivity
  have h𝒩ne : 𝒩.Nonempty := by
    exact Finset.card_pos.mp (by simpa [h𝒩card] using hpowpos)
  have hℳne : ℳ.Nonempty := by
    exact Finset.card_pos.mp (by simpa [hℳcard] using hpowpos)
  have hNbdry : Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒩) := by
    simpa using
      (hCube (α := Fin n) (𝒟 := 𝒩) (by simpa using hn) h𝒩ne h𝒩down (by simpa using h𝒩card))
  have hMbdry : Nat.choose n (n / 2) ≤ #(positiveBoundary ℳ) := by
    simpa using
      (hCube (α := Fin n) (𝒟 := ℳ) (by simpa using hn) hℳne hℳdown (by simpa using hℳcard))
  have hpair :
      2 * Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒩) + #(positiveBoundary ℳ) := by
    omega
  have hpair' :
      2 * Nat.choose n (n / 2) ≤
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
  exact hpair'.trans hbdry

theorem choose_middle_even_eq_two_mul_choose_middle_odd (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  rw [Nat.choose_succ_succ', Nat.choose_symm_half, two_mul]
  omega

theorem choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_even_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hhalf : (2 * m + 1) / 2 = m := by
    omega
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  simpa [hhalf] using
    (two_mul_choose_middle_le_card_positiveBoundary_of_balanced_zero_sections_of_halfCubeBoundaryLower
      hCube (n := 2 * m + 1) (by positivity) h𝒟 hcard hbal)

theorem zero_section_balanced_of_halfCube_of_totalSize_eq_max
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin (n + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ n)
    (htotal : totalSize 𝒟 = (n + 1) * 2 ^ (n - 1)) :
    #(𝒟.nonMemberSubfamily 0) = 2 ^ (n - 1) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (n - 1) := by
    calc
      𝒟.card = 2 ^ n := hcard
      _ = 2 * 2 ^ (n - 1) := by
        rw [← Nat.succ_pred_eq_of_pos hn]
        simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc]
  simpa using
    (card_nonMemberSubfamily_eq_half_of_card_eq_two_mul_of_totalSize_eq
      (α := Fin (n + 1)) h𝒟 hcard' (by simpa using htotal) 0)

theorem exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin (n + 1)))}
    (hcard : 𝒟.card = 2 ^ n)
    (htotal : totalSize 𝒟 < (n + 1) * 2 ^ (n - 1)) :
    ∃ a : Fin (n + 1), 2 ^ (n - 1) < #(𝒟.nonMemberSubfamily a) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (n - 1) := by
    calc
      𝒟.card = 2 ^ n := hcard
      _ = 2 * 2 ^ (n - 1) := by
        rw [← Nat.succ_pred_eq_of_pos hn]
        simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc]
  simpa using
    (exists_card_nonMemberSubfamily_gt_half_of_card_eq_two_mul_of_totalSize_lt
      (α := Fin (n + 1)) hcard' (by simpa using htotal))

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

theorem predFamily_union {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin (n + 1)))} :
    predFamily (𝒜 ∪ ℬ) = predFamily 𝒜 ∪ predFamily ℬ := by
  ext s
  constructor
  · intro hs
    rw [mem_union]
    rcases mem_predFamily.mp hs with ⟨t, ht, hts⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Or.inl <| mem_predFamily.mpr ⟨t, ht, hts⟩
    · exact Or.inr <| mem_predFamily.mpr ⟨t, ht, hts⟩
  · intro hs
    rw [mem_union] at hs
    rcases hs with hs | hs
    · rcases mem_predFamily.mp hs with ⟨t, ht, hts⟩
      exact mem_predFamily.mpr ⟨t, Finset.mem_union.mpr (Or.inl ht), hts⟩
    · rcases mem_predFamily.mp hs with ⟨t, ht, hts⟩
      exact mem_predFamily.mpr ⟨t, Finset.mem_union.mpr (Or.inr ht), hts⟩

theorem predFamily_sdiff_zeroFree {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin (n + 1)))}
    (h𝒜0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s)
    (hℬ0 : ∀ s ∈ ℬ, (0 : Fin (n + 1)) ∉ s) :
    predFamily (𝒜 \ ℬ) = predFamily 𝒜 \ predFamily ℬ := by
  ext s
  constructor
  · intro hs
    rw [mem_sdiff]
    rcases mem_predFamily.mp hs with ⟨t, ht, hts⟩
    refine ⟨mem_predFamily.mpr ⟨t, (mem_sdiff.mp ht).1, hts⟩, ?_⟩
    intro hsℬ
    rcases mem_predFamily.mp hsℬ with ⟨u, hu, hus⟩
    have ht𝒜 : t ∈ 𝒜 := (mem_sdiff.mp ht).1
    have ht0 : (0 : Fin (n + 1)) ∉ t := h𝒜0 t ht𝒜
    have hu0 : (0 : Fin (n + 1)) ∉ u := hℬ0 u hu
    have hpre :
        t.preimage Fin.succ (Fin.succ_injective n).injOn =
          u.preimage Fin.succ (Fin.succ_injective n).injOn := by
      rw [hts, hus]
    have htu : t = u := by
      ext x
      constructor <;> intro hx
      · have hx0 : x ≠ 0 := by
          intro hx0
          exact ht0 (hx0 ▸ hx)
        rcases Fin.exists_succ_eq_of_ne_zero hx0 with ⟨y, rfl⟩
        have hy : y ∈ t.preimage Fin.succ (Fin.succ_injective n).injOn := by
          simpa using hx
        have hy' : y ∈ u.preimage Fin.succ (Fin.succ_injective n).injOn := by
          rw [← hpre]
          exact hy
        simpa using hy'
      · have hx0 : x ≠ 0 := by
          intro hx0
          exact hu0 (hx0 ▸ hx)
        rcases Fin.exists_succ_eq_of_ne_zero hx0 with ⟨y, rfl⟩
        have hy : y ∈ u.preimage Fin.succ (Fin.succ_injective n).injOn := by
          simpa using hx
        have hy' : y ∈ t.preimage Fin.succ (Fin.succ_injective n).injOn := by
          rw [hpre]
          exact hy
        simpa using hy'
    exact (mem_sdiff.mp ht).2 (htu ▸ hu)
  · intro hs
    rw [mem_sdiff] at hs
    rcases hs with ⟨hs𝒜, hsℬ⟩
    rcases mem_predFamily.mp hs𝒜 with ⟨t, ht, hts⟩
    refine mem_predFamily.mpr ⟨t, mem_sdiff.mpr ⟨ht, ?_⟩, hts⟩
    intro htℬ
    exact hsℬ <| mem_predFamily.mpr ⟨t, htℬ, hts⟩

theorem predFamily_nonMemberSubfamily_positiveBoundary_eq_positiveBoundary_predFamily
    {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) :
    predFamily ((positiveBoundary 𝒜).nonMemberSubfamily 0) =
      positiveBoundary (predFamily 𝒜) := by
  calc
    predFamily ((positiveBoundary 𝒜).nonMemberSubfamily 0)
      = predFamily (succFamily (positiveBoundary (predFamily 𝒜))) := by
          rw [nonMemberSubfamily_positiveBoundary_eq_succFamily_positiveBoundary_predFamily h0]
    _ = positiveBoundary (predFamily 𝒜) := by
          rw [predFamily_succFamily]

theorem predFamily_memberSubfamily_positiveBoundary_eq_pairInterface_zero_sections
    {n : ℕ} {𝒟 : Finset (Finset (Fin (n + 1)))} :
    predFamily ((positiveBoundary 𝒟).memberSubfamily 0) =
      (predFamily (𝒟.nonMemberSubfamily 0) \ predFamily (𝒟.memberSubfamily 0)) ∪
        positiveBoundary (predFamily (𝒟.memberSubfamily 0)) := by
  have h0non : ∀ s ∈ 𝒟.nonMemberSubfamily 0, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact (mem_nonMemberSubfamily.mp hs).2
  have h0mem : ∀ s ∈ 𝒟.memberSubfamily 0, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  calc
    predFamily ((positiveBoundary 𝒟).memberSubfamily 0)
      = predFamily
          ((𝒟.nonMemberSubfamily 0 \ 𝒟.memberSubfamily 0) ∪
            (positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
              rw [memberSubfamily_positiveBoundary]
    _ = predFamily (𝒟.nonMemberSubfamily 0 \ 𝒟.memberSubfamily 0) ∪
          predFamily ((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
            rw [predFamily_union]
    _ = (predFamily (𝒟.nonMemberSubfamily 0) \ predFamily (𝒟.memberSubfamily 0)) ∪
          predFamily ((positiveBoundary (𝒟.memberSubfamily 0)).nonMemberSubfamily 0) := by
            rw [predFamily_sdiff_zeroFree h0non h0mem]
    _ = (predFamily (𝒟.nonMemberSubfamily 0) \ predFamily (𝒟.memberSubfamily 0)) ∪
          positiveBoundary (predFamily (𝒟.memberSubfamily 0)) := by
            rw [predFamily_nonMemberSubfamily_positiveBoundary_eq_positiveBoundary_predFamily h0mem]

theorem card_memberSubfamily_positiveBoundary_eq_card_pairInterface_zero_sections
    {n : ℕ} {𝒟 : Finset (Finset (Fin (n + 1)))} :
    #((positiveBoundary 𝒟).memberSubfamily 0) =
      #((predFamily (𝒟.nonMemberSubfamily 0) \ predFamily (𝒟.memberSubfamily 0)) ∪
        positiveBoundary (predFamily (𝒟.memberSubfamily 0))) := by
  have h0member : ∀ s ∈ (positiveBoundary 𝒟).memberSubfamily 0, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  calc
    #((positiveBoundary 𝒟).memberSubfamily 0)
      = #(predFamily ((positiveBoundary 𝒟).memberSubfamily 0)) := by
          symm
          exact card_predFamily h0member
    _ = #((predFamily (𝒟.nonMemberSubfamily 0) \ predFamily (𝒟.memberSubfamily 0)) ∪
          positiveBoundary (predFamily (𝒟.memberSubfamily 0))) := by
          rw [predFamily_memberSubfamily_positiveBoundary_eq_pairInterface_zero_sections]

theorem choose_middle_le_card_positiveBoundary_even_of_zero_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
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
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) :=
    hPair h𝒩down hℳdown hsubset h𝒩card hℳcard
  have hNterm : #(positiveBoundary 𝒩) = #((positiveBoundary 𝒟).nonMemberSubfamily 0) := by
    calc
      #(positiveBoundary 𝒩)
        = #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) := by
            simpa [𝒩] using card_positiveBoundary_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
      _ = #((positiveBoundary 𝒟).nonMemberSubfamily 0) := by
            rw [← nonMemberSubfamily_positiveBoundary (a := 0) (𝒜 := 𝒟)]
  have hMterm :
      #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) =
        #((positiveBoundary 𝒟).memberSubfamily 0) := by
    symm
    simpa [𝒩, ℳ] using
      card_memberSubfamily_positiveBoundary_eq_card_pairInterface_zero_sections (𝒟 := 𝒟)
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤
        #((positiveBoundary 𝒟).nonMemberSubfamily 0) +
          #((positiveBoundary 𝒟).memberSubfamily 0) := by
    calc
      2 * Nat.choose (2 * m + 1) m
        ≤ #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := hpair
      _ = #((positiveBoundary 𝒟).nonMemberSubfamily 0) +
            #((positiveBoundary 𝒟).memberSubfamily 0) := by
              rw [hNterm, hMterm]
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  calc
    2 * Nat.choose (2 * m + 1) m
      ≤ #((positiveBoundary 𝒟).nonMemberSubfamily 0) +
          #((positiveBoundary 𝒟).memberSubfamily 0) := hpair'
    _ = #(positiveBoundary 𝒟) := by
          rw [add_comm, Finset.card_memberSubfamily_add_card_nonMemberSubfamily]

theorem choose_middle_le_card_positiveBoundary_odd_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤
        #(positiveBoundary 𝒟) + #((𝒟 \ 𝒟) ∪ positiveBoundary 𝒟) :=
    hPair (e := 0) h𝒟 h𝒟 (by intro s hs; exact hs) (by simpa using hcard) (by simpa using hcard)
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤
        #(positiveBoundary 𝒟) + #(positiveBoundary 𝒟) := by
    calc
      2 * Nat.choose (2 * m + 1) m
        ≤ #(positiveBoundary 𝒟) + #((𝒟 \ 𝒟) ∪ positiveBoundary 𝒟) := hpair
      _ = #(positiveBoundary 𝒟) + #(positiveBoundary 𝒟) := by
            simp
  omega

theorem oddHalfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  intro m 𝒟 h𝒟 hcard
  exact choose_middle_le_card_positiveBoundary_odd_of_section_pairInterfaceBoundaryLower
    hPair h𝒟 hcard

/-- For nested sheets `ℳ ⊆ 𝒩`, this is the interface visible from the upper sheet:
the missing roof `𝒩 \ ℳ` together with the outer boundary of the upper sheet itself. -/
def twoSheetInterfaceBoundary {α : Type} [DecidableEq α] [Fintype α]
    (ℳ 𝒩 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒩 \ ℳ) ∪ positiveBoundary ℳ

/-- Total visible outer boundary of a two-sheet monotone region:
lower-sheet outer boundary plus upper-sheet interface boundary. -/
def twoSheetOuterBoundaryCard {α : Type} [DecidableEq α] [Fintype α]
    (ℳ 𝒩 : Finset (Finset α)) : ℕ :=
  #(positiveBoundary 𝒩) + #(twoSheetInterfaceBoundary ℳ 𝒩)

/-- Realize two nested sheets over `Fin n` as a single family in the prism `Fin (n+1)`,
with `𝒩` on the lower sheet and `ℳ` on the upper sheet. -/
def twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (n + 1))) :=
  let lower := succFamily 𝒩
  let upper := succFamily ℳ
  lower ∪ upper.image (insert 0)

theorem nonMemberSubfamily_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    (twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0 = succFamily 𝒩 := by
  let lower := succFamily 𝒩
  let upper := succFamily ℳ
  have hlower : ∀ s ∈ lower, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [twoSheetFamily, Finset.nonMemberSubfamily_union, nonMemberSubfamily_image_insert]
  simpa [lower, upper] using nonMemberSubfamily_eq_self_of_forall_not_mem
    (α := Fin (n + 1)) hlower

theorem memberSubfamily_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    (twoSheetFamily ℳ 𝒩).memberSubfamily 0 = succFamily ℳ := by
  let lower := succFamily 𝒩
  let upper := succFamily ℳ
  have hlower : ∀ s ∈ lower, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  have hupper : ∀ s ∈ upper, (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [twoSheetFamily, Finset.memberSubfamily_union]
  rw [memberSubfamily_eq_empty_of_forall_not_mem
    (α := Fin (n + 1)) (𝒜 := lower) hlower, empty_union]
  simpa [lower, upper] using Finset.memberSubfamily_image_insert hupper

theorem predFamily_nonMemberSubfamily_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    predFamily ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) = 𝒩 := by
  rw [nonMemberSubfamily_twoSheetFamily, predFamily_succFamily]

theorem predFamily_memberSubfamily_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    predFamily ((twoSheetFamily ℳ 𝒩).memberSubfamily 0) = ℳ := by
  rw [memberSubfamily_twoSheetFamily, predFamily_succFamily]

/-- Any family in the prism cube is determined exactly by its `0`-free and `0`-present sections. -/
theorem eq_twoSheetFamily_predFamily_sections {n : ℕ}
    (𝒟 : Finset (Finset (Fin (n + 1)))) :
    𝒟 =
      twoSheetFamily (predFamily (𝒟.memberSubfamily 0)) (predFamily (𝒟.nonMemberSubfamily 0)) := by
  have hnon :
      succFamily (predFamily (𝒟.nonMemberSubfamily 0)) = 𝒟.nonMemberSubfamily 0 := by
    apply succFamily_predFamily
    intro s hs
    exact (mem_nonMemberSubfamily.mp hs).2
  have hmem :
      succFamily (predFamily (𝒟.memberSubfamily 0)) = 𝒟.memberSubfamily 0 := by
    apply succFamily_predFamily
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  ext s
  by_cases hs0 : (0 : Fin (n + 1)) ∈ s
  · constructor
    · intro hs
      rw [twoSheetFamily, mem_union]
      right
      refine Finset.mem_image.mpr ?_
      refine ⟨s.erase 0, ?_, insert_erase hs0⟩
      have hsMem : s.erase 0 ∈ 𝒟.memberSubfamily 0 := by
        refine mem_memberSubfamily.mpr ⟨?_, notMem_erase 0 s⟩
        simpa [Finset.insert_erase hs0] using hs
      simpa [hmem] using hsMem
    · intro hs
      rw [twoSheetFamily, mem_union] at hs
      rcases hs with hsLower | hsUpper
      · have hsNon : s ∈ 𝒟.nonMemberSubfamily 0 := by
          simpa [hnon] using hsLower
        exact False.elim ((mem_nonMemberSubfamily.mp hsNon).2 hs0)
      · rcases Finset.mem_image.mp hsUpper with ⟨u, hu, rfl⟩
        have huMem : u ∈ 𝒟.memberSubfamily 0 := by
          simpa [hmem] using hu
        simpa using (mem_memberSubfamily.mp huMem).1
  · constructor
    · intro hs
      rw [twoSheetFamily, mem_union]
      left
      have hsNon : s ∈ 𝒟.nonMemberSubfamily 0 := mem_nonMemberSubfamily.mpr ⟨hs, hs0⟩
      simpa [hnon] using hsNon
    · intro hs
      rw [twoSheetFamily, mem_union] at hs
      rcases hs with hsLower | hsUpper
      · have hsNon : s ∈ 𝒟.nonMemberSubfamily 0 := by
          simpa [hnon] using hsLower
        exact (mem_nonMemberSubfamily.mp hsNon).1
      · rcases Finset.mem_image.mp hsUpper with ⟨u, hu, hsu⟩
        have hs0' : (0 : Fin (n + 1)) ∈ s := by
          rw [← hsu]
          exact mem_insert_self 0 u
        exact (hs0 hs0').elim

theorem card_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    (twoSheetFamily ℳ 𝒩).card = 𝒩.card + ℳ.card := by
  calc
    (twoSheetFamily ℳ 𝒩).card
      = #((twoSheetFamily ℳ 𝒩).memberSubfamily 0) +
          #((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) := by
            symm
            exact Finset.card_memberSubfamily_add_card_nonMemberSubfamily
              (a := 0) (𝒜 := twoSheetFamily ℳ 𝒩)
    _ = #(succFamily ℳ) + #(succFamily 𝒩) := by
          rw [memberSubfamily_twoSheetFamily, nonMemberSubfamily_twoSheetFamily]
    _ = ℳ.card + 𝒩.card := by rw [card_succFamily, card_succFamily]
    _ = 𝒩.card + ℳ.card := by omega

theorem card_slice_succ_twoSheetFamily {n r : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    #((twoSheetFamily ℳ 𝒩) # (r + 1)) = #(𝒩 # (r + 1)) + #(ℳ # r) := by
  calc
    #((twoSheetFamily ℳ 𝒩) # (r + 1))
      = #(((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) # (r + 1)) +
          #(((twoSheetFamily ℳ 𝒩).memberSubfamily 0) # r) := by
            exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    _ = #((succFamily 𝒩) # (r + 1)) + #((succFamily ℳ) # r) := by
          rw [nonMemberSubfamily_twoSheetFamily, memberSubfamily_twoSheetFamily]
    _ = #(𝒩 # (r + 1)) + #(ℳ # r) := by
          rw [card_slice_succFamily, card_slice_succFamily]

theorem card_slice_succ_twoSheetFamily_diag_eq_add_card_gap_slice
    {n r : ℕ} {ℳ 𝒩 : Finset (Finset (Fin n))} (hsub : ℳ ⊆ 𝒩) :
    #((twoSheetFamily 𝒩 𝒩) # (r + 1)) =
      #((twoSheetFamily ℳ 𝒩) # (r + 1)) + #((𝒩 \ ℳ) # r) := by
  have hgap :
      #(ℳ # r) + #((𝒩 \ ℳ) # r) = #(𝒩 # r) := by
    rw [slice_sdiff_eq_sdiff_slice]
    have hsliceSub : ℳ # r ⊆ 𝒩 # r := by
      intro s hs
      exact Finset.mem_slice.mpr ⟨hsub (Finset.mem_slice.mp hs).1, (Finset.mem_slice.mp hs).2⟩
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.card_sdiff_add_card_eq_card hsliceSub)
  calc
    #((twoSheetFamily 𝒩 𝒩) # (r + 1))
      = #(𝒩 # (r + 1)) + #(𝒩 # r) := by
          rw [card_slice_succ_twoSheetFamily]
    _ = #(𝒩 # (r + 1)) + (#(ℳ # r) + #((𝒩 \ ℳ) # r)) := by
          rw [hgap]
    _ = #((twoSheetFamily ℳ 𝒩) # (r + 1)) + #((𝒩 \ ℳ) # r) := by
          rw [card_slice_succ_twoSheetFamily]
          omega

theorem card_slice_succ_twoSheetFamily_lt_diag_of_gap_slice_pos
    {n r : ℕ} {ℳ 𝒩 : Finset (Finset (Fin n))} (hsub : ℳ ⊆ 𝒩)
    (hgap : 0 < #((𝒩 \ ℳ) # r)) :
    #((twoSheetFamily ℳ 𝒩) # (r + 1)) < #((twoSheetFamily 𝒩 𝒩) # (r + 1)) := by
  have hEq :
      #((twoSheetFamily 𝒩 𝒩) # (r + 1)) =
        #((twoSheetFamily ℳ 𝒩) # (r + 1)) + #((𝒩 \ ℳ) # r) :=
    card_slice_succ_twoSheetFamily_diag_eq_add_card_gap_slice hsub
  omega

theorem twoSheetFamily_slice_profile_matches_upper_diag_before_first_gap_and_drops_at_gap
    {n q : ℕ} {ℳ 𝒩 : Finset (Finset (Fin n))} (hsub : ℳ ⊆ 𝒩)
    (hzero : ∀ s ∈ Finset.range q, #((𝒩 \ ℳ) # s) = 0)
    (hpos : 0 < #((𝒩 \ ℳ) # q)) :
    (∀ s ∈ Finset.range q,
      #((twoSheetFamily ℳ 𝒩) # (s + 1)) = #((twoSheetFamily 𝒩 𝒩) # (s + 1))) ∧
      #((twoSheetFamily ℳ 𝒩) # (q + 1)) < #((twoSheetFamily 𝒩 𝒩) # (q + 1)) := by
  refine ⟨?_, card_slice_succ_twoSheetFamily_lt_diag_of_gap_slice_pos hsub hpos⟩
  intro s hs
  have hsZero : #((𝒩 \ ℳ) # s) = 0 := hzero s hs
  have hEq :
      #((twoSheetFamily 𝒩 𝒩) # (s + 1)) =
        #((twoSheetFamily ℳ 𝒩) # (s + 1)) + #((𝒩 \ ℳ) # s) :=
    card_slice_succ_twoSheetFamily_diag_eq_add_card_gap_slice hsub
  rw [hsZero, add_zero] at hEq
  exact hEq.symm

theorem card_twoSheetFamily_of_symmetric {m e : ℕ}
    {ℳ 𝒩 : Finset (Finset (Fin (2 * m + 1)))}
    (he : e ≤ 2 ^ (2 * m))
    (h𝒩 : 𝒩.card = 2 ^ (2 * m) + e)
    (hℳ : ℳ.card = 2 ^ (2 * m) - e) :
    (twoSheetFamily ℳ 𝒩).card = 2 ^ (2 * m + 1) := by
  rw [card_twoSheetFamily, h𝒩, hℳ]
  calc
    2 ^ (2 * m) + e + (2 ^ (2 * m) - e)
      = 2 ^ (2 * m) + (e + (2 ^ (2 * m) - e)) := by omega
    _ = 2 ^ (2 * m) + 2 ^ (2 * m) := by rw [Nat.add_sub_of_le he]
    _ = 2 ^ (2 * m) * 2 := by ring
    _ = 2 ^ (2 * m + 1) := by
          rw [show 2 * m + 1 = (2 * m) + 1 by omega, Nat.pow_succ]

/-- The prism realization records the lower-sheet mass, the upper-sheet mass, and one extra point
for each set on the upper sheet where `0` is inserted. -/
theorem totalSize_twoSheetFamily {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    totalSize (twoSheetFamily ℳ 𝒩) = totalSize 𝒩 + totalSize ℳ + ℳ.card := by
  calc
    totalSize (twoSheetFamily ℳ 𝒩)
      =
        totalSize ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) +
          totalSize ((twoSheetFamily ℳ 𝒩).memberSubfamily 0) +
          #((twoSheetFamily ℳ 𝒩).memberSubfamily 0) := by
            simpa using
              (totalSize_eq_totalSize_nonMemberSubfamily_add_totalSize_memberSubfamily_add_card_memberSubfamily
                (𝒜 := twoSheetFamily ℳ 𝒩) (a := (0 : Fin (n + 1))))
    _ = totalSize (succFamily 𝒩) + totalSize (succFamily ℳ) + #(succFamily ℳ) := by
          rw [nonMemberSubfamily_twoSheetFamily, memberSubfamily_twoSheetFamily]
    _ = totalSize 𝒩 + totalSize ℳ + ℳ.card := by
          rw [totalSize_succFamily, totalSize_succFamily, card_succFamily]

theorem evenLowerHalfFamily_eq_twoSheetFamily_oddLowerHalfFamily (m : ℕ) :
    evenLowerHalfFamily m =
      twoSheetFamily (oddLowerHalfFamily m) (oddLowerHalfFamily m) := by
  simp [evenLowerHalfFamily, twoSheetFamily]

theorem totalSize_evenLowerHalfFamily_eq_two_mul_totalSize_oddLowerHalfFamily_add_halfCube
    (m : ℕ) :
    totalSize (evenLowerHalfFamily m) =
      2 * totalSize (oddLowerHalfFamily m) + 2 ^ (2 * m) := by
  calc
    totalSize (evenLowerHalfFamily m)
      = totalSize (twoSheetFamily (oddLowerHalfFamily m) (oddLowerHalfFamily m)) := by
          rw [evenLowerHalfFamily_eq_twoSheetFamily_oddLowerHalfFamily]
    _ =
        totalSize (oddLowerHalfFamily m) + totalSize (oddLowerHalfFamily m) +
          (oddLowerHalfFamily m).card := by
            simpa using
              totalSize_twoSheetFamily (ℳ := oddLowerHalfFamily m) (𝒩 := oddLowerHalfFamily m)
    _ = 2 * totalSize (oddLowerHalfFamily m) + 2 ^ (2 * m) := by
          rw [card_oddLowerHalfFamily_eq_half_cube]
          ring

theorem isDownSetFamily_twoSheetFamily {n : ℕ} {ℳ 𝒩 : Finset (Finset (Fin n))}
    (hℳ : IsDownSetFamily ℳ) (h𝒩 : IsDownSetFamily 𝒩) (hsub : ℳ ⊆ 𝒩) :
    IsDownSetFamily (twoSheetFamily ℳ 𝒩) := by
  let lower := succFamily 𝒩
  let upper := succFamily ℳ
  have hlower : IsDownSetFamily lower := isDownSetFamily_succFamily h𝒩
  have hupper : IsDownSetFamily upper := isDownSetFamily_succFamily hℳ
  have hupperSub : upper ⊆ lower := by
    intro s hs
    rw [mem_succFamily_iff] at hs ⊢
    exact ⟨hs.1, hsub hs.2⟩
  intro s t hts hs
  change t ∈ twoSheetFamily ℳ 𝒩
  change s ∈ twoSheetFamily ℳ 𝒩 at hs
  rw [twoSheetFamily, mem_union] at hs ⊢
  rcases hs with hsLower | hsUpper
  · exact Or.inl (hlower hts hsLower)
  · rcases Finset.mem_image.mp hsUpper with ⟨u, hu, rfl⟩
    by_cases ht0 : (0 : Fin (n + 1)) ∈ t
    · right
      refine Finset.mem_image.mpr ⟨t.erase 0, ?_, insert_erase ht0⟩
      apply hupper
      · intro x hx
        have hxt : x ∈ t := Finset.mem_of_mem_erase hx
        have hsx : x ∈ insert 0 u := hts hxt
        rw [Finset.mem_insert] at hsx
        rcases hsx with hx0 | hxu
        · exact ((notMem_erase 0 t) (hx0 ▸ hx)).elim
        · exact hxu
      · exact hu
    · have htUpper : t ∈ upper := by
        apply hupper
        · intro x hx
          have hsx : x ∈ insert 0 u := hts hx
          rw [Finset.mem_insert] at hsx
          rcases hsx with hx0 | hxu
          · exact (ht0 (hx0 ▸ hx)).elim
          · exact hxu
        · exact hu
      exact Or.inl (hupperSub htUpper)

theorem twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily
    {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    twoSheetOuterBoundaryCard ℳ 𝒩 = #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := by
  have h𝒩term :
      #(positiveBoundary 𝒩) =
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0) := by
    calc
      #(positiveBoundary 𝒩)
        = #(positiveBoundary (predFamily ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0))) := by
            rw [predFamily_nonMemberSubfamily_twoSheetFamily]
      _ = #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) := by
            simpa using
              card_positiveBoundary_predFamily_nonMemberSubfamily (𝒜 := twoSheetFamily ℳ 𝒩)
      _ = #((positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0) := by
            rw [← nonMemberSubfamily_positiveBoundary (a := 0) (𝒜 := twoSheetFamily ℳ 𝒩)]
  have hℳterm :
      #(twoSheetInterfaceBoundary ℳ 𝒩) =
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) := by
    calc
      #(twoSheetInterfaceBoundary ℳ 𝒩)
        = #((predFamily ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) \
              predFamily ((twoSheetFamily ℳ 𝒩).memberSubfamily 0)) ∪
            positiveBoundary (predFamily ((twoSheetFamily ℳ 𝒩).memberSubfamily 0))) := by
              rw [predFamily_nonMemberSubfamily_twoSheetFamily, predFamily_memberSubfamily_twoSheetFamily,
                twoSheetInterfaceBoundary]
      _ = #((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) := by
            symm
            simpa using
              card_memberSubfamily_positiveBoundary_eq_card_pairInterface_zero_sections
                (𝒟 := twoSheetFamily ℳ 𝒩)
  calc
    twoSheetOuterBoundaryCard ℳ 𝒩
      = #(positiveBoundary 𝒩) + #(twoSheetInterfaceBoundary ℳ 𝒩) := rfl
    _ = #((positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0) +
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) := by
            rw [h𝒩term, hℳterm]
    _ = #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := by
          rw [add_comm, Finset.card_memberSubfamily_add_card_nonMemberSubfamily]

theorem predFamily_memberSubfamily_positiveBoundary_twoSheetFamily_eq_interface
    {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    predFamily ((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) =
      (𝒩 \ ℳ) ∪ positiveBoundary ℳ := by
  calc
    predFamily ((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0)
      =
        (predFamily ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) \
            predFamily ((twoSheetFamily ℳ 𝒩).memberSubfamily 0)) ∪
          positiveBoundary (predFamily ((twoSheetFamily ℳ 𝒩).memberSubfamily 0)) := by
            exact predFamily_memberSubfamily_positiveBoundary_eq_pairInterface_zero_sections
    _ = (𝒩 \ ℳ) ∪ positiveBoundary ℳ := by
          rw [predFamily_nonMemberSubfamily_twoSheetFamily, predFamily_memberSubfamily_twoSheetFamily]

theorem memberSubfamily_positiveBoundary_twoSheetFamily_eq_succFamily_interface
    {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    (positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0 =
      succFamily ((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := by
  have h0 :
      ∀ s ∈ (positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0,
        (0 : Fin (n + 1)) ∉ s := by
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  calc
    (positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0
      = succFamily (predFamily ((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0)) := by
          symm
          exact succFamily_predFamily h0
    _ = succFamily ((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := by
          rw [predFamily_memberSubfamily_positiveBoundary_twoSheetFamily_eq_interface]

theorem card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice
    {n r : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # r)) =
      #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) := by
  rw [memberSubfamily_positiveBoundary_twoSheetFamily_eq_succFamily_interface, card_slice_succFamily]

theorem nonMemberSubfamily_positiveBoundary_twoSheetFamily_eq_succFamily_positiveBoundary
    {n : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    (positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0 =
      succFamily (positiveBoundary 𝒩) := by
  calc
    (positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0
      = (positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0 := by
          rw [nonMemberSubfamily_positiveBoundary]
    _ = (positiveBoundary (succFamily 𝒩)).nonMemberSubfamily 0 := by
          rw [nonMemberSubfamily_twoSheetFamily]
    _ = succFamily (positiveBoundary 𝒩) := by
          simpa using nonMemberSubfamily_positiveBoundary_succFamily (𝒜 := 𝒩)

theorem card_slice_succ_nonMemberSubfamily_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice
    {n r : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0) # (r + 1))) =
      #(((positiveBoundary 𝒩) # (r + 1))) := by
  rw [nonMemberSubfamily_positiveBoundary_twoSheetFamily_eq_succFamily_positiveBoundary,
    card_slice_succFamily]

theorem
    card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
    {n r : ℕ} (ℳ 𝒩 : Finset (Finset (Fin n))) :
    #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
      #(((positiveBoundary 𝒩) # (r + 1))) + #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) := by
  calc
    #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1))
      = #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).nonMemberSubfamily 0) # (r + 1))) +
          #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # r)) := by
            exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    _ = #(((positiveBoundary 𝒩) # (r + 1))) + #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) := by
          rw [card_slice_succ_nonMemberSubfamily_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice,
            card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice]

theorem
    positiveBoundary_twoSheetFamily_slice_profile_matches_upper_boundary_before_first_interface_and_rises_at_interface
    {n q : ℕ} {ℳ 𝒩 : Finset (Finset (Fin n))}
    (hzero : ∀ s ∈ Finset.range q, #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # s)) = 0)
    (hpos : 0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q))) :
    (∀ s ∈ Finset.range q,
      #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
        #(((positiveBoundary 𝒩) # (s + 1)))) ∧
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    have hsZero : #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # s)) = 0 := hzero s hs
    have hEq :
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1))) + #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # s)) :=
      card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
        (ℳ := ℳ) (𝒩 := 𝒩)
    rw [hsZero, add_zero] at hEq
    exact hEq
  · have hEq :
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) =
          #(((positiveBoundary 𝒩) # (q + 1))) + #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) :=
      card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
        (ℳ := ℳ) (𝒩 := 𝒩)
    omega

/-- The first-positive-gap frontier in direct prism language: if nested odd sheets first separate
at the gap slice `q` and their prism realization has larger total size than the diagonal witness,
then the prism boundary itself should already beat the even middle layer. -/
def OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q, #(((𝒩 \ ℳ) # s)) = 0) →
      0 < #(((𝒩 \ ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Further-localized prism frontier: it is enough to understand the first positive slice of the
actual visible interface family `(𝒩 \ ℳ) ∪ positiveBoundary ℳ`, i.e. the `0`-member section of
the prism boundary after applying `predFamily`. -/
def OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q, #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # s)) = 0) →
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Lower witness-support reduction of the interface frontier: after peeling off every positive
interface slice outside the even witness support `{m, m + 1}`, only the support-silent middle
case with the first positive interface slice at rank `m` remains. -/
def OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r < m ∨ m + 2 ≤ r) →
        #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0) →
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Upper witness-support reduction of the interface frontier: after peeling off every positive
interface slice outside the even witness support `{m, m + 1}`, only the support-silent middle
case with the first positive interface slice at rank `m + 1` remains. -/
def OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m + 1 →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r ≤ m ∨ m + 2 ≤ r) →
        #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0) →
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Gap-source version of the lower support-silent interface frontier: after peeling off every
outside-support interface slice, it is enough that the first middle interface mass at rank `m`
comes from the missing-roof term `𝒩 \ ℳ`. -/
def OddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r < m ∨ m + 2 ≤ r) → #(((𝒩 \ ℳ) # r)) = 0) →
      0 < #(((𝒩 \ ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Upper-sheet-boundary version of the lower support-silent interface frontier: after peeling off
every outside-support interface slice, it is enough that the first middle interface mass at rank
`m` comes from `positiveBoundary ℳ`. -/
def OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r < m ∨ m + 2 ≤ r) → #((positiveBoundary ℳ) # r) = 0) →
      0 < #((positiveBoundary ℳ) # q) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Gap-source version of the upper support-silent interface frontier: after peeling off every
outside-support interface slice, it is enough that the first middle interface mass at rank
`m + 1` comes from the missing-roof term `𝒩 \ ℳ`. -/
def OddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m + 1 →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r ≤ m ∨ m + 2 ≤ r) → #(((𝒩 \ ℳ) # r)) = 0) →
      0 < #(((𝒩 \ ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Upper-sheet-boundary version of the upper support-silent interface frontier: after peeling off
every outside-support interface slice, it is enough that the first middle interface mass at rank
`m + 1` comes from `positiveBoundary ℳ`. -/
def OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m + 1 →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r ≤ m ∨ m + 2 ≤ r) → #((positiveBoundary ℳ) # r) = 0) →
      0 < #((positiveBoundary ℳ) # q) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Boundary-language version of the same frontier: it is enough to understand the first positive
slice of the `0`-member section of the prism boundary itself. This is the interface-family
statement written directly on the boundary section after erasing the pivot coordinate. -/
def OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # s)) = 0) →
      0 < #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Full prism-boundary slice version of the same frontier: it is enough to know that the prism
boundary agrees with the upper-sheet boundary through rank `q`, then rises strictly at rank
`q + 1`. This is the same local obstruction written directly on the full boundary profile. -/
def OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Case split for the remaining prism frontier: the first strict prism-boundary slice occurs
strictly below the two-rank support of the even witness boundary. -/
def OddSectionFirstStrictPrismBoundarySliceBelowEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q < m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Case split for the remaining prism frontier: the first strict prism-boundary slice occurs at
the lower witness-support rank `m + 1`. -/
def OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Lower witness-support version of the remaining prism frontier, after peeling off every case
where the prism boundary is already positive outside the even witness support `{m + 1, m + 2}`.
Only the support-silent middle branch remains. -/
def OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r ≤ m ∨ m + 3 ≤ r) →
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r) = 0) →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Case split for the remaining prism frontier: the first strict prism-boundary slice occurs at
the upper witness-support rank `m + 2`. -/
def OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m + 1 →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Upper witness-support version of the remaining prism frontier, after peeling off every case
where the prism boundary is already positive outside the even witness support `{m + 1, m + 2}`.
Only the support-silent middle branch remains. -/
def OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      q = m + 1 →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ r, (r ≤ m ∨ m + 3 ≤ r) →
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r) = 0) →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Case split for the remaining prism frontier: the first strict prism-boundary slice occurs
strictly above the two-rank support of the even witness boundary. -/
def OddSectionFirstStrictPrismBoundarySliceAboveEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      m + 2 ≤ q →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) →
      #(((positiveBoundary 𝒩) # (q + 1))) <
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Exterior-support version of the remaining prism frontier: it is enough to understand positive
prism-boundary mass outside the two-rank support `{m + 1, m + 2}` of the even witness boundary.
This packages the lower and upper tail cases into one local statement, leaving only the two middle
support ranks as separate frontiers. -/
def OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m r e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      (r ≤ m ∨ m + 3 ≤ r) →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Source-specific version of the exterior-support prism frontier: the positive prism-boundary
mass outside the witness support comes from the upper-sheet boundary term itself. -/
def OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m r e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      (r ≤ m ∨ m + 3 ≤ r) →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      0 < #((positiveBoundary 𝒩) # r) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- One-sheet reduction of the upper-sheet exterior-support frontier: it is enough to show that
the upper odd section already beats the strict excess target `#(positiveBoundary 𝒩) + 2 * e`,
because the prism boundary always dominates that quantity by the generic even excess bound. -/
def OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement :
    Prop :=
  ∀ {m r e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      (r ≤ m ∨ m + 3 ≤ r) →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      0 < #((positiveBoundary 𝒩) # r) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      2 * Nat.choose (2 * m + 1) m < #(positiveBoundary 𝒩) + 2 * e

/-- Complementary source-specific version of the exterior-support prism frontier: the positive
prism-boundary mass outside the witness support comes from the visible interface term. -/
def OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      (q < m ∨ m + 2 ≤ q) →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩))

/-- Interface-side reduction of the exterior-support frontier: it is enough to force the same
strict excess target `#(positiveBoundary 𝒩) + 2 * e`, since the prism boundary dominates it by the
generic even excess bound. -/
def OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement :
    Prop :=
  ∀ {m q e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
      (q < m ∨ m + 2 ≤ q) →
      0 < e →
      IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) →
      totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) →
      2 * Nat.choose (2 * m + 1) m < #(positiveBoundary 𝒩) + 2 * e

/-- Current leaf frontier for the prism program. Once these six odd local inputs are proved, the
remaining even minimizer reduction and witness-collapse chain is already formalized below. -/
def PrismTheoremCurrentLeafFrontierStatement : Prop :=
  OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement ∧
    OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement ∧
    OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement ∧
    OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement ∧
    OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement ∧
    OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement

/-- Balanced `0`-sections force an even global minimizer to be a diagonal prism
`twoSheetFamily 𝒜 𝒜`, where the common odd section `𝒜` is itself an odd global minimizer. This
packages the remaining even-cube obstruction as an odd-cube extremizer problem on one shared
section. -/
theorem
    isOddHalfCubeBoundaryGlobalMinimizer_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    IsOddHalfCubeBoundaryGlobalMinimizer (m := m) (predFamily (𝒟.nonMemberSubfamily 0)) ∧
      𝒟 =
        twoSheetFamily (predFamily (𝒟.nonMemberSubfamily 0))
          (predFamily (𝒟.nonMemberSubfamily 0)) := by
  let 𝒜 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  have hsplit :
      #(𝒟.memberSubfamily 0) + #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m + 1) := by
    simpa [hmin.2.1] using
      (Finset.card_memberSubfamily_add_card_nonMemberSubfamily (a := 0) (𝒜 := 𝒟))
  have hpow : 2 ^ (2 * m + 1) = 2 ^ (2 * m) + 2 ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, Nat.pow_succ]
    ring
  have hmbal : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) := by
    rw [hbal, hpow] at hsplit
    omega
  have hsub :
      𝒟.memberSubfamily 0 ⊆ 𝒟.nonMemberSubfamily 0 :=
    hmin.1.memberSubfamily_subset_nonMemberSubfamily (a := 0)
  have hsecEq :
      𝒟.memberSubfamily 0 = 𝒟.nonMemberSubfamily 0 := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [hmbal, hbal]
  have h𝒜down : IsDownSetFamily 𝒜 := by
    simpa [𝒜] using isDownSetFamily_predFamily_nonMemberSubfamily hmin.1
  have h𝒜card : 𝒜.card = 2 ^ (2 * m) := by
    simpa [𝒜, hbal] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have hdiag :
      𝒟 = twoSheetFamily 𝒜 𝒜 := by
    calc
      𝒟 =
          twoSheetFamily (predFamily (𝒟.memberSubfamily 0))
            (predFamily (𝒟.nonMemberSubfamily 0)) :=
        eq_twoSheetFamily_predFamily_sections 𝒟
      _ = twoSheetFamily 𝒜 𝒜 := by
        dsimp [𝒜]
        rw [hsecEq]
  refine ⟨⟨h𝒜down, h𝒜card, ?_⟩, hdiag⟩
  intro ℬ hℬdown hℬcard
  have hdiagDown : IsDownSetFamily (twoSheetFamily ℬ ℬ) := by
    exact isDownSetFamily_twoSheetFamily hℬdown hℬdown (by intro s hs; exact hs)
  have hdiagCard : (twoSheetFamily ℬ ℬ).card = 2 ^ (2 * m + 1) := by
    simpa [hℬcard] using
      (card_twoSheetFamily_of_symmetric (m := m) (e := 0) (by omega)
        (𝒩 := ℬ) (ℳ := ℬ) (by simpa using hℬcard) (by simpa using hℬcard))
  have hleEven :
      #(positiveBoundary 𝒟) ≤ #(positiveBoundary (twoSheetFamily ℬ ℬ)) :=
    hmin.2.2 hdiagDown hdiagCard
  have h𝒜bdry :
      #(positiveBoundary 𝒟) = 2 * #(positiveBoundary 𝒜) := by
    calc
      #(positiveBoundary 𝒟) = #(positiveBoundary (twoSheetFamily 𝒜 𝒜)) := by
        simpa [hdiag]
      _ = twoSheetOuterBoundaryCard 𝒜 𝒜 := by
        symm
        exact twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := 𝒜) (𝒩 := 𝒜)
      _ = #(positiveBoundary 𝒜) + #(twoSheetInterfaceBoundary 𝒜 𝒜) := rfl
      _ = #(positiveBoundary 𝒜) + #(positiveBoundary 𝒜) := by
        simp [twoSheetInterfaceBoundary]
      _ = 2 * #(positiveBoundary 𝒜) := by
        omega
  have hℬbdry :
      #(positiveBoundary (twoSheetFamily ℬ ℬ)) = 2 * #(positiveBoundary ℬ) := by
    calc
      #(positiveBoundary (twoSheetFamily ℬ ℬ)) = twoSheetOuterBoundaryCard ℬ ℬ := by
        symm
        exact twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := ℬ) (𝒩 := ℬ)
      _ = #(positiveBoundary ℬ) + #(twoSheetInterfaceBoundary ℬ ℬ) := rfl
      _ = #(positiveBoundary ℬ) + #(positiveBoundary ℬ) := by
        simp [twoSheetInterfaceBoundary]
      _ = 2 * #(positiveBoundary ℬ) := by
        omega
  rw [h𝒜bdry, hℬbdry] at hleEven
  dsimp [𝒜] at hleEven
  omega

theorem card_positiveBoundary_twoSheetFamily_diag {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    #(positiveBoundary (twoSheetFamily 𝒜 𝒜)) = 2 * #(positiveBoundary 𝒜) := by
  calc
    #(positiveBoundary (twoSheetFamily 𝒜 𝒜)) = twoSheetOuterBoundaryCard 𝒜 𝒜 := by
      symm
      exact twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := 𝒜) (𝒩 := 𝒜)
    _ = #(positiveBoundary 𝒜) + #(twoSheetInterfaceBoundary 𝒜 𝒜) := rfl
    _ = #(positiveBoundary 𝒜) + #(positiveBoundary 𝒜) := by
          simp [twoSheetInterfaceBoundary]
    _ = 2 * #(positiveBoundary 𝒜) := by
          omega

theorem
    totalSize_oddLowerHalfFamily_lt_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m))
    (hsize : totalSize (evenLowerHalfFamily m) < totalSize 𝒟) :
    totalSize (oddLowerHalfFamily m) < totalSize (predFamily (𝒟.nonMemberSubfamily 0)) := by
  let 𝒜 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  have hodd :
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 ∧
        𝒟 = twoSheetFamily 𝒜 𝒜 := by
    simpa [𝒜] using
      isOddHalfCubeBoundaryGlobalMinimizer_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections
        hmin hbal
  have h𝒜card : 𝒜.card = 2 ^ (2 * m) := by
    simpa [𝒜, hbal] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have h𝒜total :
      totalSize 𝒟 = 2 * totalSize 𝒜 + 2 ^ (2 * m) := by
    calc
      totalSize 𝒟 = totalSize (twoSheetFamily 𝒜 𝒜) := by rw [hodd.2]
      _ = totalSize 𝒜 + totalSize 𝒜 + 𝒜.card := by
            simpa using totalSize_twoSheetFamily (ℳ := 𝒜) (𝒩 := 𝒜)
      _ = 2 * totalSize 𝒜 + 2 ^ (2 * m) := by
            rw [h𝒜card]
            ring
  have hwitness :
      totalSize (evenLowerHalfFamily m) =
        2 * totalSize (oddLowerHalfFamily m) + 2 ^ (2 * m) :=
    totalSize_evenLowerHalfFamily_eq_two_mul_totalSize_oddLowerHalfFamily_add_halfCube m
  change totalSize (oddLowerHalfFamily m) < totalSize 𝒜
  omega

theorem
    exists_isOddHalfCubeBoundaryGlobalMinimizer_largerTotalSizeThanWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m))
    (hsize : totalSize (evenLowerHalfFamily m) < totalSize 𝒟) :
    ∃ 𝒜 : Finset (Finset (Fin (2 * m + 1))),
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 ∧
      totalSize (oddLowerHalfFamily m) < totalSize 𝒜 := by
  let 𝒜 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  have hodd :
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 ∧
        𝒟 = twoSheetFamily 𝒜 𝒜 := by
    simpa [𝒜] using
      isOddHalfCubeBoundaryGlobalMinimizer_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections
        hmin hbal
  have h𝒜card : 𝒜.card = 2 ^ (2 * m) := by
    simpa [𝒜, hbal] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have h𝒜total :
      totalSize 𝒟 = 2 * totalSize 𝒜 + 2 ^ (2 * m) := by
    calc
      totalSize 𝒟 = totalSize (twoSheetFamily 𝒜 𝒜) := by rw [hodd.2]
      _ = totalSize 𝒜 + totalSize 𝒜 + 𝒜.card := by
            simpa using totalSize_twoSheetFamily (ℳ := 𝒜) (𝒩 := 𝒜)
      _ = 2 * totalSize 𝒜 + 2 ^ (2 * m) := by
            rw [h𝒜card]
            ring
  have hwitness :
      totalSize (evenLowerHalfFamily m) =
        2 * totalSize (oddLowerHalfFamily m) + 2 ^ (2 * m) :=
    totalSize_evenLowerHalfFamily_eq_two_mul_totalSize_oddLowerHalfFamily_add_halfCube m
  refine ⟨𝒜, hodd.1, ?_⟩
  exact
    totalSize_oddLowerHalfFamily_lt_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness
      hmin hbal hsize

theorem
    choose_middle_lt_card_positiveBoundary_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m))
    (hsize : totalSize (evenLowerHalfFamily m) < totalSize 𝒟) :
    Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary 𝒟) := by
  let 𝒜 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  have h𝒜data :
      IsOddHalfCubeBoundaryGlobalMinimizer (m := m) 𝒜 ∧
        𝒟 = twoSheetFamily 𝒜 𝒜 := by
    simpa [𝒜] using
      isOddHalfCubeBoundaryGlobalMinimizer_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections
        hmin hbal
  have h𝒜size :
      totalSize (oddLowerHalfFamily m) < totalSize 𝒜 := by
    simpa [𝒜] using
      totalSize_oddLowerHalfFamily_lt_predFamily_nonMemberSubfamily_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness
        hmin hbal hsize
  have hdiag :
      𝒟 = twoSheetFamily 𝒜 𝒜 := by
    exact h𝒜data.2
  have hgap :
      Nat.choose (2 * m + 1) m < upperShadowGap 𝒜 :=
    hOddSize h𝒜data.1.1 h𝒜data.1.2.1 h𝒜size
  have hbdryA :
      Nat.choose (2 * m + 1) m < #(positiveBoundary 𝒜) := by
    simpa [upperShadowGap_eq_card_positiveBoundary_of_isDownSetFamily (𝒟 := 𝒜) h𝒜data.1.1] using hgap
  have hdouble :
      Nat.choose (2 * m + 2) (m + 1) < 2 * #(positiveBoundary 𝒜) := by
    rw [choose_middle_even_eq_two_mul_choose_middle_odd]
    exact Nat.mul_lt_mul_of_pos_left hbdryA (by decide : 0 < 2)
  calc
    Nat.choose (2 * m + 2) (m + 1) < 2 * #(positiveBoundary 𝒜) := hdouble
    _ = #(positiveBoundary (twoSheetFamily 𝒜 𝒜)) := by
          rw [card_positiveBoundary_twoSheetFamily_diag]
    _ = #(positiveBoundary 𝒟) := by rw [← hdiag]

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  by_contra hgt
  have hgt' : totalSize (evenLowerHalfFamily m) < totalSize 𝒟 := by
    omega
  have hstrict :
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary 𝒟) :=
    choose_middle_lt_card_positiveBoundary_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_totalSize_gt_evenWitness_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOddSize hmin hbal hgt'
  have hupper :
      #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 2) (m + 1) :=
    card_positiveBoundary_le_choose_middle_of_isEvenHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_lt_of_ge hupper) hstrict

theorem
    zeroSectionExcess_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_totalSize_gt_evenWitness_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (hsize : totalSize (evenLowerHalfFamily m) < totalSize 𝒟) :
    2 ^ (2 * m) < #(𝒟.nonMemberSubfamily 0) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hmin.2.1
  have hhalf :
      2 ^ (2 * m) ≤ #(𝒟.nonMemberSubfamily 0) :=
    half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul hmin.1 0 (2 ^ (2 * m)) hcard'
  by_cases hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)
  · have hle :
        totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) :=
      totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_balancedZeroSections_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
        hOddSize hmin hbal
    exact False.elim ((not_lt_of_ge hle) hsize)
  · exact lt_of_le_of_ne hhalf (by simpa [eq_comm] using hbal)

theorem
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstSeparation
    (hFirst :
      OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement) :
    OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  intro m e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hsize
  have hsum𝒩 :
      Finset.sum (Finset.range (2 * m + 2)) (fun r => #(𝒩 # r)) = 𝒩.card := by
    simpa [Nat.range_succ_eq_Iic, Fintype.card_fin] using (Finset.sum_card_slice 𝒩)
  have hsumℳ :
      Finset.sum (Finset.range (2 * m + 2)) (fun r => #(ℳ # r)) = ℳ.card := by
    simpa [Nat.range_succ_eq_Iic, Fintype.card_fin] using (Finset.sum_card_slice ℳ)
  have hsep :
      ∃ q, q ∈ Finset.range (2 * m + 2) ∧ #(ℳ # q) < #(𝒩 # q) := by
    by_contra hno
    have hslices :
        ∀ q ∈ Finset.range (2 * m + 2), #(ℳ # q) = #(𝒩 # q) := by
      intro q hq
      have hle : #(ℳ # q) ≤ #(𝒩 # q) :=
        card_slice_le_card_slice_of_subset hsub
      have hnotlt : ¬ #(ℳ # q) < #(𝒩 # q) := by
        intro hlt
        exact hno ⟨q, hq, hlt⟩
      exact Nat.le_antisymm hle (Nat.not_lt.mp hnotlt)
    have hcardEq : ℳ.card = 𝒩.card := by
      calc
        ℳ.card = Finset.sum (Finset.range (2 * m + 2)) (fun r => #(ℳ # r)) := by
          symm
          exact hsumℳ
        _ = Finset.sum (Finset.range (2 * m + 2)) (fun r => #(𝒩 # r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact hslices r hr
        _ = 𝒩.card := hsum𝒩
    have hcardNe : ℳ.card ≠ 𝒩.card := by
      intro hEq
      rw [hℳcard, h𝒩card] at hEq
      have hlt :
          2 ^ (2 * m) - e < 2 ^ (2 * m) + e := by
        calc
          2 ^ (2 * m) - e < 2 ^ (2 * m) := by
            exact Nat.sub_lt (pow_pos (by decide : 0 < 2) (2 * m)) he
          _ < 2 ^ (2 * m) + e := Nat.lt_add_of_pos_right he
      exact (ne_of_lt hlt) hEq
    exact (hcardNe hcardEq).elim
  let q : ℕ := Nat.find hsep
  have hqRange : q ∈ Finset.range (2 * m + 2) := (Nat.find_spec hsep).1
  have hqStrict : #(ℳ # q) < #(𝒩 # q) := (Nat.find_spec hsep).2
  have hbefore : ∀ ⦃r : ℕ⦄, r < q → #(ℳ # r) = #(𝒩 # r) := by
    intro r hr
    have hrRange : r ∈ Finset.range (2 * m + 2) := by
      exact Finset.mem_range.mpr (lt_trans hr (Finset.mem_range.mp hqRange))
    have hle : #(ℳ # r) ≤ #(𝒩 # r) :=
      card_slice_le_card_slice_of_subset hsub
    have hnotlt : ¬ #(ℳ # r) < #(𝒩 # r) := by
      intro hlt
      have hqle : q ≤ r := Nat.find_min' hsep ⟨hrRange, hlt⟩
      exact (Nat.not_le_of_gt hr) hqle
    exact Nat.le_antisymm hle (Nat.not_lt.mp hnotlt)
  exact hFirst he h𝒩 hℳ hsub h𝒩card hℳcard hbefore hqStrict hsize

theorem
    oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveGapSlice
    (hGap :
      OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement) :
    OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hbefore hqStrict hsize
  have hzero :
      ∀ s ∈ Finset.range q, #(((𝒩 \ ℳ) # s)) = 0 := by
    intro s hs
    have hsEq : #(ℳ # s) = #(𝒩 # s) := hbefore (Finset.mem_range.mp hs)
    rw [card_slice_sdiff_eq_card_slice_sub_card_slice_of_subset hsub, hsEq, Nat.sub_self]
  have hpos : 0 < #(((𝒩 \ ℳ) # q)) := by
    rw [card_slice_sdiff_eq_card_slice_sub_card_slice_of_subset hsub]
    exact Nat.sub_pos_of_lt hqStrict
  exact hGap he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize

theorem
    oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_largerPrism
    (hPrism :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize
  have hsize' : totalSize (evenLowerHalfFamily m) < totalSize (twoSheetFamily ℳ 𝒩) := by
    calc
      totalSize (evenLowerHalfFamily m) < totalSize 𝒩 + totalSize ℳ + ℳ.card := hsize
      _ = totalSize (twoSheetFamily ℳ 𝒩) := by
            symm
            simpa using totalSize_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)
  have hstrict :
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩)) :=
    hPrism he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize'
  calc
    Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := hstrict
    _ = twoSheetOuterBoundaryCard ℳ 𝒩 := by
          symm
          exact twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)
    _ = #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := by
          simp [twoSheetOuterBoundaryCard, twoSheetInterfaceBoundary]

theorem
    oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSlice
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize
  let 𝓘 : Finset (Finset (Fin (2 * m + 1))) := (𝒩 \ ℳ) ∪ positiveBoundary ℳ
  have h𝓘ne : 𝓘.Nonempty := by
    rcases Finset.card_pos.mp hpos with ⟨s, hs⟩
    refine ⟨s, Finset.mem_union.mpr ?_⟩
    exact Or.inl (Finset.mem_slice.mp hs).1
  have hsep : ∃ r, r ∈ Finset.range (2 * m + 2) ∧ 0 < #((𝓘) # r) := by
    by_contra hno
    have hslices : ∀ r ∈ Finset.range (2 * m + 2), #((𝓘) # r) = 0 := by
      intro r hr
      by_cases hlt : 0 < #((𝓘) # r)
      · exact False.elim (hno ⟨r, hr, hlt⟩)
      · exact Nat.eq_zero_of_not_pos hlt
    have hsum𝓘 :
        Finset.sum (Finset.range (2 * m + 2)) (fun r => #((𝓘) # r)) = 𝓘.card := by
      simpa [Nat.range_succ_eq_Iic, Fintype.card_fin] using (Finset.sum_card_slice 𝓘)
    have hcard𝓘 : 𝓘.card = 0 := by
      calc
        𝓘.card = Finset.sum (Finset.range (2 * m + 2)) (fun r => #((𝓘) # r)) := hsum𝓘.symm
        _ = 0 := by
              refine Finset.sum_eq_zero ?_
              intro r hr
              exact hslices r hr
    exact h𝓘ne.ne_empty (Finset.card_eq_zero.mp hcard𝓘)
  let r : ℕ := Nat.find hsep
  have hrRange : r ∈ Finset.range (2 * m + 2) := (Nat.find_spec hsep).1
  have hrPos : 0 < #((𝓘) # r) := (Nat.find_spec hsep).2
  have hbefore : ∀ s ∈ Finset.range r, #((𝓘) # s) = 0 := by
    intro s hs
    by_contra hsne
    have hspos : 0 < #((𝓘) # s) := Nat.pos_of_ne_zero hsne
    have hsRange : s ∈ Finset.range (2 * m + 2) := by
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hs) (Finset.mem_range.mp hrRange))
    have hrle : r ≤ s := Nat.find_min' hsep ⟨hsRange, hspos⟩
    exact (Nat.not_le_of_gt (Finset.mem_range.mp hs)) hrle
  exact hInterface he h𝒩 hℳ hsub h𝒩card hℳcard hbefore hrPos hsize

theorem
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveMemberBoundarySlice
    (hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize
  have hzero' :
      ∀ s ∈ Finset.range q,
        #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # s)) = 0 := by
    intro s hs
    rw [card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice]
    exact hzero s hs
  have hpos' :
      0 < #((((positiveBoundary (twoSheetFamily ℳ 𝒩)).memberSubfamily 0) # q)) := by
    rw [card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice]
    exact hpos
  exact hBoundary he h𝒩 hℳ hsub h𝒩card hℳcard hzero' hpos' hsize

theorem
    oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstStrictPrismBoundarySliceAboveUpperBoundary
    (hSlice :
      OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize
  have hzeroInterface :
      ∀ s ∈ Finset.range q, #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # s)) = 0 := by
    intro s hs
    rw [← card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice]
    exact hzero s hs
  have hposInterface :
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) := by
    rw [← card_slice_succ_memberSubfamily_positiveBoundary_twoSheetFamily_eq_card_interface_slice]
    exact hpos
  have hprofile :
      (∀ s ∈ Finset.range q,
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (s + 1)) =
          #(((positiveBoundary 𝒩) # (s + 1)))) ∧
        #(((positiveBoundary 𝒩) # (q + 1))) <
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) :=
    positiveBoundary_twoSheetFamily_slice_profile_matches_upper_boundary_before_first_interface_and_rises_at_interface
      (ℳ := ℳ) (𝒩 := 𝒩) hzeroInterface hposInterface
  exact hSlice he h𝒩 hℳ hsub h𝒩card hℳcard hprofile.1 hprofile.2 hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
    (hBelow :
      OddSectionFirstStrictPrismBoundarySliceBelowEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hAbove :
      OddSectionFirstStrictPrismBoundarySliceAboveEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
  by_cases hqm : q < m
  · exact hBelow hqm he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
  · by_cases hqeq : q = m
    · exact hLower hqeq he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
    · by_cases hqeq' : q = m + 1
      · exact hUpper hqeq' he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
      · have hqge : m + 2 ≤ q := by omega
        exact hAbove hqge he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize

theorem
    oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
    (hExcess :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement) :
    OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m r e 𝒩 ℳ houtside he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  have hele : e ≤ 2 ^ (2 * m) := by
    have hcard_le :
        𝒩.card ≤ 2 ^ (2 * m + 1) := by
      calc
        𝒩.card ≤ Fintype.card (Finset (Fin (2 * m + 1))) := Finset.card_le_univ 𝒩
        _ = 2 ^ (2 * m + 1) := by simp
    rw [h𝒩card, pow_succ'] at hcard_le
    omega
  have hprismDown : IsDownSetFamily (twoSheetFamily ℳ 𝒩) :=
    isDownSetFamily_twoSheetFamily hℳ h𝒩 hsub
  have hprismCard : (twoSheetFamily ℳ 𝒩).card = 2 ^ (2 * m + 1) := by
    exact card_twoSheetFamily_of_symmetric hele h𝒩card hℳcard
  have hambient :
      #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) ≤
        #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := by
    simpa [hprismCard] using
      (card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_pow
        (α := Fin (2 * m + 2)) (𝒜 := twoSheetFamily ℳ 𝒩) hprismDown
        (a := (0 : Fin (2 * m + 2))) (k := 2 * m) hprismCard)
  have h𝒩bdry :
      #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) =
        #(positiveBoundary 𝒩) := by
    rw [nonMemberSubfamily_twoSheetFamily, nonMemberSubfamily_positiveBoundary_succFamily,
      card_succFamily]
  have h𝒩sec :
      #((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) = 2 ^ (2 * m) + e := by
    rw [nonMemberSubfamily_twoSheetFamily, card_succFamily, h𝒩card]
  have hrewrite :
      #(positiveBoundary 𝒩) + 2 * e =
        #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := by
    rw [← h𝒩bdry, h𝒩sec, Nat.add_sub_cancel_left]
  have hstrictExcess :
      2 * Nat.choose (2 * m + 1) m <
        #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := by
    calc
      2 * Nat.choose (2 * m + 1) m < #(positiveBoundary 𝒩) + 2 * e :=
        hExcess houtside he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
      _ =
          #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
            2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := hrewrite
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact lt_of_lt_of_le hstrictExcess hambient

theorem
    oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
    (hExcess :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement) :
    OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ houtside he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  have hele : e ≤ 2 ^ (2 * m) := by
    have hcard_le :
        𝒩.card ≤ 2 ^ (2 * m + 1) := by
      calc
        𝒩.card ≤ Fintype.card (Finset (Fin (2 * m + 1))) := Finset.card_le_univ 𝒩
        _ = 2 ^ (2 * m + 1) := by simp
    rw [h𝒩card, pow_succ'] at hcard_le
    omega
  have hprismDown : IsDownSetFamily (twoSheetFamily ℳ 𝒩) :=
    isDownSetFamily_twoSheetFamily hℳ h𝒩 hsub
  have hprismCard : (twoSheetFamily ℳ 𝒩).card = 2 ^ (2 * m + 1) := by
    exact card_twoSheetFamily_of_symmetric hele h𝒩card hℳcard
  have hambient :
      #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) ≤
        #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := by
    simpa [hprismCard] using
      (card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_pow
        (α := Fin (2 * m + 2)) (𝒜 := twoSheetFamily ℳ 𝒩) hprismDown
        (a := (0 : Fin (2 * m + 2))) (k := 2 * m) hprismCard)
  have h𝒩bdry :
      #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) =
        #(positiveBoundary 𝒩) := by
    rw [nonMemberSubfamily_twoSheetFamily, nonMemberSubfamily_positiveBoundary_succFamily,
      card_succFamily]
  have h𝒩sec :
      #((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) = 2 ^ (2 * m) + e := by
    rw [nonMemberSubfamily_twoSheetFamily, card_succFamily, h𝒩card]
  have hrewrite :
      #(positiveBoundary 𝒩) + 2 * e =
        #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := by
    rw [← h𝒩bdry, h𝒩sec, Nat.add_sub_cancel_left]
  have hstrictExcess :
      2 * Nat.choose (2 * m + 1) m <
        #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
          2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := by
    calc
      2 * Nat.choose (2 * m + 1) m < #(positiveBoundary 𝒩) + 2 * e :=
        hExcess houtside he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
      _ =
          #((positiveBoundary ((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0)).nonMemberSubfamily 0) +
            2 * (#((twoSheetFamily ℳ 𝒩).nonMemberSubfamily 0) - 2 ^ (2 * m)) := hrewrite
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact lt_of_lt_of_le hstrictExcess hambient

theorem
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
    (hUpper :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterface :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m r e 𝒩 ℳ houtside he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  cases r with
  | zero =>
      have hzero :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # 0) = 0 :=
        card_positiveBoundary_slice_zero_eq_zero (𝒟 := twoSheetFamily ℳ 𝒩)
      omega
  | succ r' =>
      by_cases hUpperPos : 0 < #(((positiveBoundary 𝒩) # (r' + 1)))
      · exact
          hUpper (r := r' + 1) houtside he h𝒩 hℳ hsub h𝒩card hℳcard hUpperPos hsize
      · have hUpperZero : #(((positiveBoundary 𝒩) # (r' + 1))) = 0 :=
            Nat.eq_zero_of_not_pos hUpperPos
        have hsum :
            #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r' + 1)) =
              #(((positiveBoundary 𝒩) # (r' + 1))) +
                #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r')) :=
          card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
            (ℳ := ℳ) (𝒩 := 𝒩)
        have hInterfacePos :
            0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r')) := by
          omega
        have houtside' : r' < m ∨ m + 2 ≤ r' := by
          rcases houtside with hr | hr
          · left
            omega
          · right
            omega
        exact
          hInterface (q := r') houtside' he h𝒩 hℳ hsub h𝒩card hℳcard hInterfacePos hsize

theorem
    oddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
  have hzero : ∀ s ∈ Finset.range q, #(((𝒩 \ ℳ) # s)) = 0 := by
    intro s hs
    have hslt : s < m := by
      rw [hq] at hs
      exact Finset.mem_range.mp hs
    exact hsilent s (Or.inl hslt)
  exact hGap he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize

theorem
    oddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
  have hzero : ∀ s ∈ Finset.range q, #(((𝒩 \ ℳ) # s)) = 0 := by
    intro s hs
    have hsltq : s < q := Finset.mem_range.mp hs
    have hsle : s ≤ m := by
      rw [hq] at hsltq
      omega
    exact hsilent s (Or.inl hsle)
  exact hGap he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize

theorem
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
    (hGap :
      OddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundary :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
  have hGapSilent :
      ∀ r, (r < m ∨ m + 2 ≤ r) → #(((𝒩 \ ℳ) # r)) = 0 := by
    intro r hout
    exact
      card_slice_eq_zero_of_subset_of_card_slice_eq_zero
        (𝒜 := 𝒩 \ ℳ) (ℬ := (𝒩 \ ℳ) ∪ positiveBoundary ℳ)
        (by
          intro s hs
          exact Finset.mem_union.mpr (Or.inl hs))
        (hsilent r hout)
  have hBoundarySilent :
      ∀ r, (r < m ∨ m + 2 ≤ r) → #((positiveBoundary ℳ) # r) = 0 := by
    intro r hout
    exact
      card_slice_eq_zero_of_subset_of_card_slice_eq_zero
        (𝒜 := positiveBoundary ℳ) (ℬ := (𝒩 \ ℳ) ∪ positiveBoundary ℳ)
        (by
          intro s hs
          exact Finset.mem_union.mpr (Or.inr hs))
        (hsilent r hout)
  rcases Finset.card_pos.mp hpos with ⟨s, hs⟩
  rcases Finset.mem_slice.mp hs with ⟨hsUnion, hsCard⟩
  rcases Finset.mem_union.mp hsUnion with hsGap | hsBoundary
  · have hGapPos : 0 < #(((𝒩 \ ℳ) # q)) := by
      exact Finset.card_pos.mpr ⟨s, Finset.mem_slice.mpr ⟨hsGap, hsCard⟩⟩
    exact hGap hq he h𝒩 hℳ hsub h𝒩card hℳcard hGapSilent hGapPos hsize
  · have hBoundaryPos : 0 < #((positiveBoundary ℳ) # q) := by
      exact Finset.card_pos.mpr ⟨s, Finset.mem_slice.mpr ⟨hsBoundary, hsCard⟩⟩
    exact hBoundary hq he h𝒩 hℳ hsub h𝒩card hℳcard hBoundarySilent hBoundaryPos hsize

theorem
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundary :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      (oddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice
        hGap)
      hBoundary

theorem
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hGap :
      OddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundary :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
  have hGapSilent :
      ∀ r, (r ≤ m ∨ m + 2 ≤ r) → #(((𝒩 \ ℳ) # r)) = 0 := by
    intro r hout
    exact
      card_slice_eq_zero_of_subset_of_card_slice_eq_zero
        (𝒜 := 𝒩 \ ℳ) (ℬ := (𝒩 \ ℳ) ∪ positiveBoundary ℳ)
        (by
          intro s hs
          exact Finset.mem_union.mpr (Or.inl hs))
        (hsilent r hout)
  have hBoundarySilent :
      ∀ r, (r ≤ m ∨ m + 2 ≤ r) → #((positiveBoundary ℳ) # r) = 0 := by
    intro r hout
    exact
      card_slice_eq_zero_of_subset_of_card_slice_eq_zero
        (𝒜 := positiveBoundary ℳ) (ℬ := (𝒩 \ ℳ) ∪ positiveBoundary ℳ)
        (by
          intro s hs
          exact Finset.mem_union.mpr (Or.inr hs))
        (hsilent r hout)
  rcases Finset.card_pos.mp hpos with ⟨s, hs⟩
  rcases Finset.mem_slice.mp hs with ⟨hsUnion, hsCard⟩
  rcases Finset.mem_union.mp hsUnion with hsGap | hsBoundary
  · have hGapPos : 0 < #(((𝒩 \ ℳ) # q)) := by
      exact Finset.card_pos.mpr ⟨s, Finset.mem_slice.mpr ⟨hsGap, hsCard⟩⟩
    exact hGap hq he h𝒩 hℳ hsub h𝒩card hℳcard hGapSilent hGapPos hsize
  · have hBoundaryPos : 0 < #((positiveBoundary ℳ) # q) := by
      exact Finset.card_pos.mpr ⟨s, Finset.mem_slice.mpr ⟨hsBoundary, hsCard⟩⟩
    exact hBoundary hq he h𝒩 hℳ hsub h𝒩card hℳcard hBoundarySilent hBoundaryPos hsize

theorem
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundary :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      (oddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice
        hGap)
      hBoundary

theorem
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ he h𝒩 hℳ hsub h𝒩card hℳcard hzero hpos hsize
  by_cases hqm : q < m
  · exact hOutside (Or.inl hqm) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  · by_cases hqeq : q = m
    · by_cases hUpperOutsidePos : ∃ r, m + 2 ≤ r ∧ 0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r))
      · rcases hUpperOutsidePos with ⟨r, hr, hposr⟩
        exact hOutside (Or.inr hr) he h𝒩 hℳ hsub h𝒩card hℳcard hposr hsize
      · have hsilent :
            ∀ r, (r < m ∨ m + 2 ≤ r) →
              #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0 := by
          intro r hout
          rcases hout with hr | hr
          · exact hzero r (Finset.mem_range.mpr (by omega))
          · by_cases hposr : 0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r))
            · exact False.elim (hUpperOutsidePos ⟨r, hr, hposr⟩)
            · exact Nat.eq_zero_of_not_pos hposr
        exact hLower hqeq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
    · by_cases hqeq' : q = m + 1
      · by_cases hUpperOutsidePos : ∃ r, m + 2 ≤ r ∧ 0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r))
        · rcases hUpperOutsidePos with ⟨r, hr, hposr⟩
          exact hOutside (Or.inr hr) he h𝒩 hℳ hsub h𝒩card hℳcard hposr hsize
        · have hsilent :
              ∀ r, (r ≤ m ∨ m + 2 ≤ r) →
                #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0 := by
            intro r hout
            rcases hout with hr | hr
            · exact hzero r (Finset.mem_range.mpr (by omega))
            · by_cases hposr : 0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r))
              · exact False.elim (hUpperOutsidePos ⟨r, hr, hposr⟩)
              · exact Nat.eq_zero_of_not_pos hposr
          exact hUpper hqeq' he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hpos hsize
      · have hqge : m + 2 ≤ q := by omega
        exact hOutside (Or.inr hqge) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize

theorem
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_positiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGapLower :
      OddSectionPositiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGapUpper :
      OddSectionPositiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
      hOutside
      (oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
        hGapLower hBoundaryLower)
      (oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveGapSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hGapUpper hBoundaryUpper)

theorem
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
      hOutside
      (oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
        hGap hBoundaryLower)
      (oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hGap hBoundaryUpper)

theorem
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveInterfaceSlice
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstSeparation
      (oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveGapSlice
        (oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_largerPrism
          (oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSlice
            hInterface)))

theorem
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveInterfaceSlice
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)

theorem
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveInterfaceSlice
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hOutside hGap hBoundaryLower hBoundaryUpper)

theorem
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  rcases hFrontier with
    ⟨_hUpperOutside, hInterfaceOutside, hGap, hBoundaryLower, hBoundaryUpper, _hOddSize⟩
  exact
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
      hGap hBoundaryLower hBoundaryUpper

theorem
    oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_largerPrism
      (oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSlice
        (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
          hFrontier))

theorem
    oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveGapSlice
      (oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_prismTheoremCurrentLeafFrontier
        hFrontier)

theorem
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement := by
  exact
    oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstSeparation
      (oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_prismTheoremCurrentLeafFrontier
        hFrontier)

theorem
    oddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement := by
  rcases hFrontier with
    ⟨_hUpperOutside, _hInterfaceOutside, _hGap, _hBoundaryLower, _hBoundaryUpper, hOddSize⟩
  exact hOddSize

theorem
    oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hprof hstrict hsize
  have hsilentInterface :
      ∀ r, (r < m ∨ m + 2 ≤ r) →
        #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0 := by
    intro r hout
    rcases hout with hr | hr
    · have hrq : r ∈ Finset.range q := by
        rw [hq]
        exact Finset.mem_range.mpr hr
      have hsliceEq :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) :=
        hprof r hrq
      have hsum :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) +
              #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) :=
        card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
          (ℳ := ℳ) (𝒩 := 𝒩)
      omega
    · have hprismZero :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) = 0 := by
        exact hsilent (r + 1) (Or.inr (by omega))
      have hsum :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) +
              #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) :=
        card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
          (ℳ := ℳ) (𝒩 := 𝒩)
      omega
  have hposInterface :
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) := by
    have hsum :
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) =
          #(((positiveBoundary 𝒩) # (q + 1))) +
            #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) :=
      card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
        (ℳ := ℳ) (𝒩 := 𝒩)
    omega
  exact hLower hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilentInterface hposInterface hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hprof hstrict hsize
  have hsilentInterface :
      ∀ r, (r ≤ m ∨ m + 2 ≤ r) →
        #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) = 0 := by
    intro r hout
    rcases hout with hr | hr
    · have hrq : r ∈ Finset.range q := by
        rw [hq]
        exact Finset.mem_range.mpr (by omega)
      have hsliceEq :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) :=
        hprof r hrq
      have hsum :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) +
              #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) :=
        card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
          (ℳ := ℳ) (𝒩 := 𝒩)
      omega
    · have hprismZero :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) = 0 := by
        exact hsilent (r + 1) (Or.inr (by omega))
      have hsum :
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (r + 1)) =
            #(((positiveBoundary 𝒩) # (r + 1))) +
              #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # r)) :=
        card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
          (ℳ := ℳ) (𝒩 := 𝒩)
      omega
  have hposInterface :
      0 < #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) := by
    have hsum :
        #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) =
          #(((positiveBoundary 𝒩) # (q + 1))) +
            #((((𝒩 \ ℳ) ∪ positiveBoundary ℳ) # q)) :=
      card_slice_succ_positiveBoundary_twoSheetFamily_eq_card_positiveBoundary_slice_succ_add_card_interface_slice
        (ℳ := ℳ) (𝒩 := 𝒩)
    omega
  exact hUpper hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilentInterface hposInterface hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_outsideSupportSilent
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
  by_cases hOutsidePos :
      ∃ r, (r ≤ m ∨ m + 3 ≤ r) ∧
        0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r)
  · rcases hOutsidePos with ⟨r, hout, hpos⟩
    exact hOutside (r := r) hout he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  · have hsilent :
        ∀ r, (r ≤ m ∨ m + 3 ≤ r) →
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r) = 0 := by
      intro r hout
      by_cases hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r)
      · exact False.elim (hOutsidePos ⟨r, hout, hpos⟩)
      · exact Nat.eq_zero_of_not_pos hpos
    exact hLower hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hprof hstrict hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_outsideSupportSilent
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  intro m q e 𝒩 ℳ hq he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
  by_cases hOutsidePos :
      ∃ r, (r ≤ m ∨ m + 3 ≤ r) ∧
        0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r)
  · rcases hOutsidePos with ⟨r, hout, hpos⟩
    exact hOutside (r := r) hout he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  · have hsilent :
        ∀ r, (r ≤ m ∨ m + 3 ≤ r) →
          #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r) = 0 := by
      intro r hout
      by_cases hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # r)
      · exact False.elim (hOutsidePos ⟨r, hout, hpos⟩)
      · exact Nat.eq_zero_of_not_pos hpos
    exact hUpper hq he h𝒩 hℳ hsub h𝒩card hℳcard hsilent hprof hstrict hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  refine
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
      ?_
      (oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_outsideSupportSilent
        hOutside hLower)
      (oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_outsideSupportSilent
        hOutside hUpper)
      ?_
  · intro m q e 𝒩 ℳ hqm he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
    have hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) :=
      lt_of_le_of_lt (Nat.zero_le _) hstrict
    exact hOutside (r := q + 1) (Or.inl (by omega)) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  · intro m q e 𝒩 ℳ hqge he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
    have hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) :=
      lt_of_le_of_lt (Nat.zero_le _) hstrict
    exact hOutside (r := q + 1) (Or.inr (by omega)) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize

theorem
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
      hOutside
      (oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
        hLower)
      (oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hUpper)

theorem
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  exact
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hOutside
      (oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
        hGap hBoundaryLower)
      (oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hGap hBoundaryUpper)

theorem
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement := by
  refine
    oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
      ?_ hLower hUpper ?_
  · intro m q e 𝒩 ℳ hqm he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
    have hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) :=
      lt_of_le_of_lt (Nat.zero_le _) hstrict
    exact hOutside (r := q + 1) (Or.inl (by omega)) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize
  · intro m q e 𝒩 ℳ hqge he h𝒩 hℳ hsub h𝒩card hℳcard hprof hstrict hsize
    have hpos : 0 < #((positiveBoundary (twoSheetFamily ℳ 𝒩)) # (q + 1)) :=
      lt_of_le_of_lt (Nat.zero_le _) hstrict
    exact hOutside (r := q + 1) (Or.inr (by omega)) he h𝒩 hℳ hsub h𝒩card hℳcard hpos hsize

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
    (hPairSize :
      OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  let e := #(𝒟.nonMemberSubfamily 0) - 2 ^ (2 * m)
  let 𝒩 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  let ℳ : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.memberSubfamily 0)
  have hepos : 0 < e := by
    dsimp [e]
    exact Nat.sub_pos_of_lt hexcess
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using isDownSetFamily_predFamily_nonMemberSubfamily hmin.1
  have hℳdown : IsDownSetFamily ℳ := by
    simpa [ℳ] using isDownSetFamily_predFamily_memberSubfamily hmin.1
  have hsub : ℳ ⊆ 𝒩 := by
    simpa [𝒩, ℳ] using predFamily_memberSubfamily_subset_predFamily_nonMemberSubfamily hmin.1
  have hNcardSec : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) + e := by
    dsimp [e]
    omega
  have hcard : 𝒟.card = 2 ^ (2 * m + 1) := hmin.2.1
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hpow : 2 ^ (2 * m + 1) = 2 ^ (2 * m) + 2 ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, Nat.pow_succ]
    ring
  have hMcardSec : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) - e := by
    rw [hcard, hpow] at hsplit
    dsimp [e] at *
    omega
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) + e := by
    simpa [𝒩, hNcardSec] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have hℳcard : ℳ.card = 2 ^ (2 * m) - e := by
    simpa [ℳ, hMcardSec] using card_predFamily_memberSubfamily (𝒜 := 𝒟)
  have hdiag : 𝒟 = twoSheetFamily ℳ 𝒩 := by
    simpa [𝒩, ℳ] using eq_twoSheetFamily_predFamily_sections 𝒟
  have hsize' :
      totalSize (evenLowerHalfFamily m) < totalSize 𝒩 + totalSize ℳ + ℳ.card := by
    calc
      totalSize (evenLowerHalfFamily m) < totalSize 𝒟 := hsize
      _ = totalSize (twoSheetFamily ℳ 𝒩) := by rw [hdiag]
      _ = totalSize 𝒩 + totalSize ℳ + ℳ.card := by
            simpa using totalSize_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)
  have hstrict :
      Nat.choose (2 * m + 2) (m + 1) <
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) :=
    hPairSize hepos h𝒩down hℳdown hsub h𝒩card hℳcard hsize'
  have hNterm : #(positiveBoundary 𝒩) = #((positiveBoundary 𝒟).nonMemberSubfamily 0) := by
    calc
      #(positiveBoundary 𝒩)
        = #((positiveBoundary (𝒟.nonMemberSubfamily 0)).nonMemberSubfamily 0) := by
            simpa [𝒩] using card_positiveBoundary_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
      _ = #((positiveBoundary 𝒟).nonMemberSubfamily 0) := by
            rw [← nonMemberSubfamily_positiveBoundary (a := 0) (𝒜 := 𝒟)]
  have hMterm :
      #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) =
        #((positiveBoundary 𝒟).memberSubfamily 0) := by
    symm
    simpa [𝒩, ℳ] using
      card_memberSubfamily_positiveBoundary_eq_card_pairInterface_zero_sections (𝒟 := 𝒟)
  calc
    Nat.choose (2 * m + 2) (m + 1)
      < #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := hstrict
    _ = #((positiveBoundary 𝒟).nonMemberSubfamily 0) +
          #((positiveBoundary 𝒟).memberSubfamily 0) := by
            rw [hNterm, hMterm]
    _ = #(positiveBoundary 𝒟) := by
          simpa [add_comm] using
            (Finset.card_memberSubfamily_add_card_nonMemberSubfamily
              (a := 0) (𝒜 := positiveBoundary 𝒟))

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
    (hFirst :
      OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
      (oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstSeparation
        hFirst)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
    (hGap :
      OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
      (oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_firstPositiveGapSlice
        hGap)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
    (hPrism :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
      (oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_largerPrism
        hPrism)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary
    (hSlice :
      OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstStrictPrismBoundarySliceAboveUpperBoundary
      hSlice
  have hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveMemberBoundarySlice
      hBoundary
  have hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSlice
      hInterface
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
      hGap hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveInterfaceSlice
      hInterface
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
      hGap hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveInterfaceSliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hOutside)
      hLower hUpper

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary
    (hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveMemberBoundarySlice
        hBoundary)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hOutside hLower hUpper)
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
      hInterfaceOutside hLower hUpper
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
      hInterfaceOutside hLower hUpper
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
        hFrontier)

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
      hOutside hLower hUpper
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport
        hOutside hLower hUpper)
      hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary
      (oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
        hUpperOutside hInterfaceOutside)
      hLower hUpper hmin hsize hexcess

theorem
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement) :
    EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement := by
  intro m 𝒟 hmin hsize hexcess
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary
      hOutside hLower hUpper hmin hsize hexcess

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hZero :
      EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  by_contra hgt
  have hsize : totalSize (evenLowerHalfFamily m) < totalSize 𝒟 := by
    omega
  have hexcess :
      2 ^ (2 * m) < #(𝒟.nonMemberSubfamily 0) :=
    zeroSectionExcess_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_totalSize_gt_evenWitness_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOddSize hmin hsize
  have hstrict :
      Nat.choose (2 * m + 2) (m + 1) < #(positiveBoundary 𝒟) :=
    hZero hmin hsize hexcess
  have hupper :
      #(positiveBoundary 𝒟) ≤ Nat.choose (2 * m + 2) (m + 1) :=
    card_positiveBoundary_le_choose_middle_of_isEvenHalfCubeBoundaryGlobalMinimizer hmin
  exact (not_lt_of_ge hupper) hstrict

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hPairSize :
      OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hPairSize)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hFirst :
      OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hFirst)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hGap :
      OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hGap)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hPrism :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hPrism)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hInterface)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hBoundary)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hSlice :
      OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstStrictPrismBoundarySliceAboveUpperBoundary
        hSlice)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceSplitByEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hBelow :
      OddSectionFirstStrictPrismBoundarySliceBelowEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hAbove :
      OddSectionFirstStrictPrismBoundarySliceAboveEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
        hBelow hLower hUpper hAbove)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport
        hOutside hLower hUpper)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hOutside hLower hUpper)
      hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      hUpperOutside hInterfaceOutside
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hInterfaceOutside hLower hUpper hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hInterfaceOutside hLower hUpper hOddSize hmin

theorem
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) := by
  exact
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
        hFrontier)
      (oddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_prismTheoremCurrentLeafFrontier
        hFrontier)
      hmin

theorem
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hZero :
      EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hsize :
      totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) :=
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hZero hOddSize hmin
  exact
    t_eq_middle_of_middleTransitionWindow_of_totalSize_le_evenWitness
      hmin htmid humid hmid hsize

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hPairSize :
      OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hPairSize)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hFirst :
      OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hFirst)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hGap :
      OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hGap)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hPrism :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hPrism)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hInterface)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hBoundary)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hSlice :
      OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstStrictPrismBoundarySliceAboveUpperBoundary
        hSlice)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceSplitByEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hBelow :
      OddSectionFirstStrictPrismBoundarySliceBelowEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hAbove :
      OddSectionFirstStrictPrismBoundarySliceAboveEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
        hBelow hLower hUpper hAbove)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      hUpperOutside hInterfaceOutside
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hOutside hLower hUpper hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hInterfaceOutside hLower hUpper hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hInterfaceOutside hLower hUpper hOddSize hmin htmid humid hmid

theorem
    t_eq_middle_of_middleTransitionWindow_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0) :
    t = m + 1 := by
  exact
    t_eq_middle_of_middleTransitionWindow_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      (oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_prismTheoremCurrentLeafFrontier
        hFrontier)
      (oddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_prismTheoremCurrentLeafFrontier
        hFrontier)
      hmin htmid humid hmid

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hZero :
      EvenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hsize :
      totalSize 𝒟 ≤ totalSize (evenLowerHalfFamily m) :=
    totalSize_le_evenWitness_of_isEvenHalfCubeBoundaryGlobalMinimizer_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap
      hZero hOddSize hmin
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_totalSize_le_witness_of_balancedZeroSections
      hmin htmid humid hfull hmid hsize hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hPairSize :
      OddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveExcessLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hPairSize)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hFirst :
      OddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstSeparationLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hFirst)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hGap :
      OddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerTotalSizeThanEvenWitnessForcesStrictPairInterfaceBoundary
        hGap)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hPrism :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hPrism)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hInterface :
      OddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hInterface)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hBoundary :
      OddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_zeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (evenHalfCubeGlobalMinimizerZeroSectionExcessLargerTotalSizeThanWitnessForcesStrictBoundary_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary
        hBoundary)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hSlice :
      OddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (oddSectionFirstPositiveMemberBoundarySliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstStrictPrismBoundarySliceAboveUpperBoundary
        hSlice)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceSplitByEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hBelow :
      OddSectionFirstStrictPrismBoundarySliceBelowEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hAbove :
      OddSectionFirstStrictPrismBoundarySliceAboveEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_splitByEvenWitnessSupport
        hBelow hLower hUpper hAbove)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_middleSupportOutsideSilent
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      (oddSectionFirstStrictPrismBoundarySliceAboveUpperBoundaryLargerPrismThanEvenWitnessForcesStrictBoundary_of_positivePrismBoundarySliceOutsideEvenWitnessSupport_of_firstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilent_of_firstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
        hOutside hLower hUpper)
      hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      hUpperOutside hInterfaceOutside
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      hOutside hLower hUpper hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      hOutside hLower hUpper hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hLower :
      OddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hUpper :
      OddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hOutside :
      OddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_positiveUpperBoundarySliceOutsideEvenWitnessSupport_of_positiveInterfaceSliceOutsideEvenWitnessSupport
      (oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hUpperOutside)
      (oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_strictExcess
        hInterfaceOutside)
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositivePrismBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstStrictPrismBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      hOutside hLower hUpper hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      hInterfaceOutside hLower hUpper hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
    (hUpperOutside :
      OddSectionPositiveUpperBoundarySliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hInterfaceOutside :
      OddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcessStatement)
    (hGap :
      OddSectionFirstPositiveGapSliceLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryLower :
      OddSectionPositiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hBoundaryUpper :
      OddSectionPositiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement)
    (hOddSize :
      OddHalfCubeLargerTotalSizeThanWitnessForcesStrictUpperShadowGapStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have hLower :
      OddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtLowerEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryLower
  have hUpper :
      OddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundaryStatement :=
    oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_firstPositiveGapSlice_of_positiveUpperSheetBoundarySliceAtUpperEvenWitnessSupportWithOutsideSupportSilent
      hGap hBoundaryUpper
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_oddSectionPositiveInterfaceSliceOutsideEvenWitnessSupportLargerPrismThanEvenWitnessForcesStrictExcess_of_oddSectionFirstPositiveInterfaceSliceAtLowerEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddSectionFirstPositiveInterfaceSliceAtUpperEvenWitnessSupportWithOutsideSupportSilentLargerPrismThanEvenWitnessForcesStrictBoundary_of_oddLargerTotalSizeThanWitnessForcesStrictUpperShadowGap_of_balancedZeroSections
      hInterfaceOutside hLower hUpper hOddSize hmin htmid humid hfull hmid hbal

theorem
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_prismTheoremCurrentLeafFrontier_of_balancedZeroSections
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {t u : ℕ}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htmid : t ≤ m + 1) (humid : m + 1 < u)
    (hfull : ∀ ⦃r : ℕ⦄, r < t → #(𝒟 # r) = Nat.choose (2 * m + 2) r)
    (hmid : ∀ ⦃r : ℕ⦄, t ≤ r → r < u →
      #(𝒟 # r) ≠ Nat.choose (2 * m + 2) r ∧ #(𝒟 # r) ≠ 0)
    (hbal : #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m)) :
    𝒟 = evenLowerHalfFamily m := by
  have htEq :
      t = m + 1 :=
    t_eq_middle_of_middleTransitionWindow_of_prismTheoremCurrentLeafFrontier
      hFrontier hmin htmid humid hmid
  exact
    eq_evenLowerHalfFamily_of_middleTransitionWindow_of_t_eq_middle_of_balancedZeroSections
      hmin hfull htEq hbal

/-- Topological/two-sheet formulation of the current odd-dimensional frontier.

Interpret `ℳ ⊆ 𝒩` as two nested monotone sheets over the odd cube. The target lower bound is on
the total visible outer boundary: the outer boundary of the lower sheet `𝒩`, plus the visible
interface of the upper sheet `ℳ`. -/
def TopologicalOddSectionBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      2 * Nat.choose (2 * m + 1) m ≤ twoSheetOuterBoundaryCard ℳ 𝒩

/-- The topological two-sheet formulation is definitionally the same as the paired-interface
frontier used by the current proof program. -/
theorem topologicalOddSectionBoundaryLowerStatement_iff_pairInterface :
    TopologicalOddSectionBoundaryLowerStatement ↔
      OddSectionPairInterfaceBoundaryLowerStatement := by
  constructor
  · intro h m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
    simpa [twoSheetOuterBoundaryCard, twoSheetInterfaceBoundary] using
      h h𝒩 hℳ hsub h𝒩card hℳcard
  · intro h m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
    simpa [twoSheetOuterBoundaryCard, twoSheetInterfaceBoundary] using
      h h𝒩 hℳ hsub h𝒩card hℳcard

/-- The topological formulation already implies the odd half-cube theorem. -/
theorem oddHalfCubeBoundaryLower_of_topologicalOddSectionBoundaryLower
    (hTop : TopologicalOddSectionBoundaryLowerStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  exact oddHalfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
    ((topologicalOddSectionBoundaryLowerStatement_iff_pairInterface).mp hTop)

/-- Talk-level alias for the live Erdős #1 frontier. This is the current named theorem target:
two nested monotone sheets in the odd cube have visible outer boundary at least the middle
binomial threshold. -/
abbrev TwoSheetBoundaryTheorem : Prop :=
  TopologicalOddSectionBoundaryLowerStatement

theorem twoSheetBoundaryTheorem_iff_topologicalOddSectionBoundaryLowerStatement :
    TwoSheetBoundaryTheorem ↔ TopologicalOddSectionBoundaryLowerStatement := by
  rfl

/-- `TwoSheetBoundaryTheorem` is exactly the sharp middle-binomial boundary lower bound for the
prism family built from the two sheets. -/
theorem twoSheetBoundaryTheorem_iff_prismHalfCubeBoundary :
    TwoSheetBoundaryTheorem ↔
      ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
        IsDownSetFamily 𝒩 →
          IsDownSetFamily ℳ →
          ℳ ⊆ 𝒩 →
          𝒩.card = 2 ^ (2 * m) + e →
          ℳ.card = 2 ^ (2 * m) - e →
          Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary (twoSheetFamily ℳ 𝒩)) := by
  constructor
  · intro hTwo m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
    have hvis :
        2 * Nat.choose (2 * m + 1) m ≤ twoSheetOuterBoundaryCard ℳ 𝒩 :=
      hTwo h𝒩 hℳ hsub h𝒩card hℳcard
    simpa [choose_middle_even_eq_two_mul_choose_middle_odd,
      twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)] using hvis
  · intro hPrism m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
    have hbdry :
        Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary (twoSheetFamily ℳ 𝒩)) :=
      hPrism h𝒩 hℳ hsub h𝒩card hℳcard
    simpa [choose_middle_even_eq_two_mul_choose_middle_odd,
      twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)] using hbdry

/-- Prism-family form of the live frontier: the family built from two symmetric nested sheets is a
sharp half-cube candidate in the even cube. This is the exact extremal statement to target if one
wants to prove the Two-Sheet Boundary Theorem by compression/canonical minimizer methods. -/
def PrismHalfCubeBoundaryLowerStatement : Prop :=
  ∀ {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))},
    IsDownSetFamily 𝒩 →
      IsDownSetFamily ℳ →
      ℳ ⊆ 𝒩 →
      𝒩.card = 2 ^ (2 * m) + e →
      ℳ.card = 2 ^ (2 * m) - e →
      Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary (twoSheetFamily ℳ 𝒩))

theorem prismHalfCubeBoundaryLowerStatement_iff_twoSheetBoundaryTheorem :
    PrismHalfCubeBoundaryLowerStatement ↔ TwoSheetBoundaryTheorem := by
  simpa [PrismHalfCubeBoundaryLowerStatement] using
    twoSheetBoundaryTheorem_iff_prismHalfCubeBoundary.symm

theorem oddHalfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddHalfCubeBoundaryLowerStatement := by
  rcases hFrontier with
    ⟨_hUpperOutside, _hInterfaceOutside, _hGap, _hBoundaryLower, _hBoundaryUpper, hOddSize⟩
  exact oddHalfCubeBoundaryLower_of_largerTotalSizeThanWitnessForcesStrictUpperShadowGap hOddSize

theorem oddHalfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddHalfCubeUpperShadowGapLowerStatement := by
  exact oddHalfCubeUpperShadowGapLower_of_oddHalfCubeBoundaryLower
    (oddHalfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier hFrontier)

theorem
    oddSectionPairInterfaceBoundaryLower_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPos : OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    OddSectionPairInterfaceBoundaryLowerStatement := by
  exact
    (oddSectionPairInterfaceBoundaryLower_iff_oddHalfCubeUpperShadowGapLower_and_positiveExcessPairInterfaceBoundaryLower).mpr
      ⟨oddHalfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier hFrontier, hPos⟩

theorem
    twoSheetBoundaryTheorem_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPos : OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    TwoSheetBoundaryTheorem := by
  exact
    (topologicalOddSectionBoundaryLowerStatement_iff_pairInterface).mpr
      (oddSectionPairInterfaceBoundaryLower_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
        hFrontier hPos)

theorem
    prismHalfCubeBoundaryLowerStatement_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPos : OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    PrismHalfCubeBoundaryLowerStatement := by
  exact
    (prismHalfCubeBoundaryLowerStatement_iff_twoSheetBoundaryTheorem).mpr
      (twoSheetBoundaryTheorem_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
        hFrontier hPos)

/-- The prism family attached to two symmetric nested sheets is already a half-cube down-set.
This isolates the exact input data needed for a compression/extremizer proof. -/
theorem twoSheetFamily_halfCube_data
    {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒩 : IsDownSetFamily 𝒩)
    (hℳ : IsDownSetFamily ℳ)
    (hsub : ℳ ⊆ 𝒩)
    (he : e ≤ 2 ^ (2 * m))
    (h𝒩card : 𝒩.card = 2 ^ (2 * m) + e)
    (hℳcard : ℳ.card = 2 ^ (2 * m) - e) :
    IsDownSetFamily (twoSheetFamily ℳ 𝒩) ∧
      (twoSheetFamily ℳ 𝒩).card = 2 ^ (2 * m + 1) := by
  refine ⟨isDownSetFamily_twoSheetFamily hℳ h𝒩 hsub, ?_⟩
  exact card_twoSheetFamily_of_symmetric he h𝒩card hℳcard

/-- Boundary form of the prism extremal problem: after packaging the two sheets into one even-cube
family, the target lower bound is exactly the sharp half-cube middle-layer bound. -/
theorem choose_middle_le_card_positiveBoundary_twoSheetFamily
    (hPrism : PrismHalfCubeBoundaryLowerStatement)
    {m e : ℕ} {𝒩 ℳ : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒩 : IsDownSetFamily 𝒩)
    (hℳ : IsDownSetFamily ℳ)
    (hsub : ℳ ⊆ 𝒩)
    (h𝒩card : 𝒩.card = 2 ^ (2 * m) + e)
    (hℳcard : ℳ.card = 2 ^ (2 * m) - e) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary (twoSheetFamily ℳ 𝒩)) :=
  hPrism h𝒩 hℳ hsub h𝒩card hℳcard

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hbal :
      #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) :=
    zero_section_balanced_of_halfCube_of_totalSize_eq_max
      (n := 2 * m + 1) (by positivity) h𝒟 hcard htotal
  have hsum :
      #(𝒟.memberSubfamily 0) + #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m + 1) := by
    simpa [hcard] using
      (Finset.card_memberSubfamily_add_card_nonMemberSubfamily (a := 0) (𝒜 := 𝒟))
  have hpow : 2 ^ (2 * m + 1) = 2 ^ (2 * m) + 2 ^ (2 * m) := by
    rw [show 2 * m + 1 = 2 * m + 1 by omega, Nat.pow_succ]
    ring
  have hMcard : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) := by
    rw [hbal, hpow] at hsum
    omega
  exact
    choose_middle_le_card_positiveBoundary_even_of_zero_section_pairInterfaceBoundaryLower
      (hPair := hPair) (e := 0) h𝒟 (by simpa using hbal) (by simpa using hMcard)

theorem predAboveFamily_union {n : ℕ} {a : Fin (n + 1)}
    {𝒜 ℬ : Finset (Finset (Fin (n + 1)))} :
    predAboveFamily a (𝒜 ∪ ℬ) = predAboveFamily a 𝒜 ∪ predAboveFamily a ℬ := by
  ext s
  constructor
  · intro hs
    rw [mem_union]
    rcases mem_predAboveFamily.mp hs with ⟨t, ht, hts⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Or.inl <| mem_predAboveFamily.mpr ⟨t, ht, hts⟩
    · exact Or.inr <| mem_predAboveFamily.mpr ⟨t, ht, hts⟩
  · intro hs
    rw [mem_union] at hs
    rcases hs with hs | hs
    · rcases mem_predAboveFamily.mp hs with ⟨t, ht, hts⟩
      exact mem_predAboveFamily.mpr ⟨t, Finset.mem_union.mpr (Or.inl ht), hts⟩
    · rcases mem_predAboveFamily.mp hs with ⟨t, ht, hts⟩
      exact mem_predAboveFamily.mpr ⟨t, Finset.mem_union.mpr (Or.inr ht), hts⟩

theorem predAboveFamily_sdiff_pivotFree {n : ℕ} {a : Fin (n + 1)}
    {𝒜 ℬ : Finset (Finset (Fin (n + 1)))}
    (h𝒜a : ∀ s ∈ 𝒜, a ∉ s)
    (hℬa : ∀ s ∈ ℬ, a ∉ s) :
    predAboveFamily a (𝒜 \ ℬ) = predAboveFamily a 𝒜 \ predAboveFamily a ℬ := by
  ext s
  constructor
  · intro hs
    rw [mem_sdiff]
    rcases mem_predAboveFamily.mp hs with ⟨t, ht, hts⟩
    refine ⟨mem_predAboveFamily.mpr ⟨t, (mem_sdiff.mp ht).1, hts⟩, ?_⟩
    intro hsℬ
    rcases mem_predAboveFamily.mp hsℬ with ⟨u, hu, hus⟩
    have ht𝒜 : t ∈ 𝒜 := (mem_sdiff.mp ht).1
    have hta : a ∉ t := h𝒜a t ht𝒜
    have hua : a ∉ u := hℬa u hu
    have hpre :
        t.preimage a.succAbove a.succAboveEmb.injective.injOn =
          u.preimage a.succAbove a.succAboveEmb.injective.injOn := by
      rw [hts, hus]
    have htu : t = u := by
      ext x
      constructor <;> intro hx
      · have hxa : x ≠ a := by
          intro hxa
          exact hta (hxa ▸ hx)
        rcases Fin.exists_succAbove_eq hxa with ⟨y, rfl⟩
        have hy : y ∈ t.preimage a.succAbove a.succAboveEmb.injective.injOn := by
          simpa using hx
        have hy' : y ∈ u.preimage a.succAbove a.succAboveEmb.injective.injOn := by
          rw [← hpre]
          exact hy
        simpa using hy'
      · have hxa : x ≠ a := by
          intro hxa
          exact hua (hxa ▸ hx)
        rcases Fin.exists_succAbove_eq hxa with ⟨y, rfl⟩
        have hy : y ∈ u.preimage a.succAbove a.succAboveEmb.injective.injOn := by
          simpa using hx
        have hy' : y ∈ t.preimage a.succAbove a.succAboveEmb.injective.injOn := by
          rw [hpre]
          exact hy
        simpa using hy'
    exact (mem_sdiff.mp ht).2 (htu ▸ hu)
  · intro hs
    rw [mem_sdiff] at hs
    rcases hs with ⟨hs𝒜, hsℬ⟩
    rcases mem_predAboveFamily.mp hs𝒜 with ⟨t, ht, hts⟩
    refine mem_predAboveFamily.mpr ⟨t, mem_sdiff.mpr ⟨ht, ?_⟩, hts⟩
    intro htℬ
    exact hsℬ <| mem_predAboveFamily.mpr ⟨t, htℬ, hts⟩

theorem predAboveFamily_nonMemberSubfamily_positiveBoundary_eq_positiveBoundary_predAboveFamily
    {n : ℕ} {a : Fin (n + 1)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) :
    predAboveFamily a ((positiveBoundary 𝒜).nonMemberSubfamily a) =
      positiveBoundary (predAboveFamily a 𝒜) := by
  calc
    predAboveFamily a ((positiveBoundary 𝒜).nonMemberSubfamily a)
      = predAboveFamily a (succAboveFamily a (positiveBoundary (predAboveFamily a 𝒜))) := by
          rw [nonMemberSubfamily_positiveBoundary_eq_succAboveFamily_positiveBoundary_predAboveFamily ha]
    _ = positiveBoundary (predAboveFamily a 𝒜) := by
          rw [predAboveFamily_succAboveFamily]

theorem card_memberSubfamily_positiveBoundary_eq_card_pairInterface_sections
    {n : ℕ} {a : Fin (n + 1)} {𝒟 : Finset (Finset (Fin (n + 1)))} :
    #((positiveBoundary 𝒟).memberSubfamily a) =
      #((predAboveFamily a (𝒟.nonMemberSubfamily a) \ predAboveFamily a (𝒟.memberSubfamily a)) ∪
        positiveBoundary (predAboveFamily a (𝒟.memberSubfamily a))) := by
  have hamember : ∀ s ∈ (positiveBoundary 𝒟).memberSubfamily a, a ∉ s := by
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  have hanon : ∀ s ∈ 𝒟.nonMemberSubfamily a, a ∉ s := by
    intro s hs
    exact (mem_nonMemberSubfamily.mp hs).2
  have hamem : ∀ s ∈ 𝒟.memberSubfamily a, a ∉ s := by
    intro s hs
    exact (mem_memberSubfamily.mp hs).2
  calc
    #((positiveBoundary 𝒟).memberSubfamily a)
      = #(predAboveFamily a ((positiveBoundary 𝒟).memberSubfamily a)) := by
          symm
          exact card_predAboveFamily (a := a) hamember
    _ = #(predAboveFamily a
          ((𝒟.nonMemberSubfamily a \ 𝒟.memberSubfamily a) ∪
            (positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a)) := by
          rw [memberSubfamily_positiveBoundary]
    _ = #(predAboveFamily a (𝒟.nonMemberSubfamily a \ 𝒟.memberSubfamily a) ∪
          predAboveFamily a ((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a)) := by
          rw [predAboveFamily_union]
    _ = #((predAboveFamily a (𝒟.nonMemberSubfamily a) \ predAboveFamily a (𝒟.memberSubfamily a)) ∪
          predAboveFamily a ((positiveBoundary (𝒟.memberSubfamily a)).nonMemberSubfamily a)) := by
          rw [predAboveFamily_sdiff_pivotFree hanon hamem]
    _ = #((predAboveFamily a (𝒟.nonMemberSubfamily a) \ predAboveFamily a (𝒟.memberSubfamily a)) ∪
          positiveBoundary (predAboveFamily a (𝒟.memberSubfamily a))) := by
          rw [predAboveFamily_nonMemberSubfamily_positiveBoundary_eq_positiveBoundary_predAboveFamily hamem]

theorem choose_middle_le_card_positiveBoundary_even_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
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
    simpa [𝒩, ℳ] using predAboveFamily_memberSubfamily_subset_predAboveFamily_nonMemberSubfamily h𝒟
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) + e := by
    simpa [𝒩, hNcard] using
      (card_predAboveFamily (a := a)
        (𝒜 := 𝒟.nonMemberSubfamily a)
        (fun s hs => (mem_nonMemberSubfamily.mp hs).2))
  have hℳcard : ℳ.card = 2 ^ (2 * m) - e := by
    simpa [ℳ, hMcard] using
      (card_predAboveFamily (a := a)
        (𝒜 := 𝒟.memberSubfamily a)
        (fun s hs => (mem_memberSubfamily.mp hs).2))
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤
        #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) :=
    hPair h𝒩down hℳdown hsubset h𝒩card hℳcard
  have hNterm :
      #(positiveBoundary 𝒩) = #((positiveBoundary 𝒟).nonMemberSubfamily a) := by
    calc
      #(positiveBoundary 𝒩)
        = #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) := by
            symm
            simpa [𝒩] using
              (card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predAboveFamily
                (a := a) (𝒜 := 𝒟.nonMemberSubfamily a)
                (fun s hs => (mem_nonMemberSubfamily.mp hs).2))
      _ = #((positiveBoundary 𝒟).nonMemberSubfamily a) := by
            rw [← nonMemberSubfamily_positiveBoundary (a := a) (𝒜 := 𝒟)]
  have hMterm :
      #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) =
        #((positiveBoundary 𝒟).memberSubfamily a) := by
    symm
    simpa [𝒩, ℳ] using
      (card_memberSubfamily_positiveBoundary_eq_card_pairInterface_sections (a := a) (𝒟 := 𝒟))
  have hpair' :
      2 * Nat.choose (2 * m + 1) m ≤
        #((positiveBoundary 𝒟).nonMemberSubfamily a) +
          #((positiveBoundary 𝒟).memberSubfamily a) := by
    calc
      2 * Nat.choose (2 * m + 1) m
        ≤ #(positiveBoundary 𝒩) + #((𝒩 \ ℳ) ∪ positiveBoundary ℳ) := hpair
      _ = #((positiveBoundary 𝒟).nonMemberSubfamily a) +
            #((positiveBoundary 𝒟).memberSubfamily a) := by
              rw [hNterm, hMterm]
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  calc
    2 * Nat.choose (2 * m + 1) m
      ≤ #((positiveBoundary 𝒟).nonMemberSubfamily a) +
          #((positiveBoundary 𝒟).memberSubfamily a) := hpair'
    _ = #(positiveBoundary 𝒟) := by
          simpa [add_comm] using
            (Finset.card_memberSubfamily_add_card_nonMemberSubfamily
              (a := a) (𝒜 := positiveBoundary 𝒟))

theorem choose_middle_le_card_positiveBoundary_even_of_section_excess_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
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
  exact choose_middle_le_card_positiveBoundary_even_of_section_pairInterfaceBoundaryLower
    (m := m) (e := e) (a := a) hPair h𝒟 hNcard hMcard

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  rcases exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
      (n := 2 * m + 1) (by positivity) hcard htotal with ⟨a, hexcess⟩
  exact choose_middle_le_card_positiveBoundary_even_of_section_excess_of_section_pairInterfaceBoundaryLower
    (a := a) hPair h𝒟 hcard hexcess

theorem choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hcard
  have hhalf : ∀ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤ #(𝒟.nonMemberSubfamily a) := by
    intro a
    exact half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul h𝒟 a (2 ^ (2 * m)) hcard'
  have hsumLower :
      ∑ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤
        ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) := by
    exact Finset.sum_le_sum fun a _ => hhalf a
  have hconst :
      ∑ _a : Fin (2 * m + 2), 2 ^ (2 * m) = (2 * m + 2) * 2 ^ (2 * m) := by
    simp
  have hsumEq :
      ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) =
        (2 * m + 2) * (2 * 2 ^ (2 * m)) - totalSize 𝒟 := by
    simpa [hcard'] using
      (sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize (𝒜 := 𝒟))
  have hdouble :
      (2 * m + 2) * (2 * 2 ^ (2 * m)) =
        2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
    ring
  let x := (2 * m + 2) * 2 ^ (2 * m)
  have htotalUpper : totalSize 𝒟 ≤ 2 * x := by
    dsimp [x]
    unfold totalSize
    calc
      ∑ s ∈ 𝒟, s.card ≤ ∑ s ∈ 𝒟, (2 * m + 2) := by
        exact Finset.sum_le_sum fun s hs => by
          simpa using (Finset.card_le_univ (s := s))
      _ = 𝒟.card * (2 * m + 2) := by
        rw [Finset.sum_const_nat]
        intro x hx
        rfl
      _ = 2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
        rw [hcard']
        ring
  have htotalLe : totalSize 𝒟 ≤ (2 * m + 2) * 2 ^ (2 * m) := by
    rw [hconst, hsumEq, hdouble] at hsumLower
    have hsumLower' : x + totalSize 𝒟 ≤ 2 * x :=
      (Nat.le_sub_iff_add_le htotalUpper).1 hsumLower
    have hsumLower'' : x + totalSize 𝒟 ≤ x + x := by
      simpa [x, two_mul, add_assoc, add_left_comm, add_comm] using hsumLower'
    exact Nat.le_of_add_le_add_left hsumLower''
  by_cases htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)
  · exact choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_section_pairInterfaceBoundaryLower
      hPair h𝒟 hcard htotal
  · have hlt : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m) := lt_of_le_of_ne htotalLe htotal
    exact choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_section_pairInterfaceBoundaryLower
      hPair h𝒟 hcard hlt

/-- Direct `Fin n` closure from the odd section pair-interface inequality. This packages the
odd-dimensional theorem and the even-dimensional recursion through a single candidate frontier. -/
theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 0 < m := by
      omega
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
    have hdiv : (k + (k + 2)) / 2 = k + 1 := by
      omega
    simpa [two_mul, hdiv, add_assoc, add_left_comm, add_comm] using
      (choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
        hPair (m := k) h𝒟 (by
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hcard))
  · have hdiv : (2 * m + 1) / 2 = m := by
      omega
    simpa [hdiv] using
      (choose_middle_le_card_positiveBoundary_odd_of_section_pairInterfaceBoundaryLower
        hPair h𝒟 hcard)

theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_topologicalOddSectionBoundaryLower
    (hTop : TopologicalOddSectionBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
    ((topologicalOddSectionBoundaryLowerStatement_iff_pairInterface).mp hTop) hn h𝒟 hcard

theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_twoSheetBoundaryTheorem
    (hTwo : TwoSheetBoundaryTheorem)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_topologicalOddSectionBoundaryLower
    hTwo hn h𝒟 hcard

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

theorem choose_middle_le_card_positiveBoundary_even_of_section_excess_of_strictExcessOptimization
    (hOpt : OddSectionStrictExcessOptimizationStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))} {a : Fin (2 * m + 2)}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (hexcess : 2 ^ (2 * m) < #(𝒟.nonMemberSubfamily a)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  rcases hOpt with ⟨β, hβlower, hβbound⟩
  let e := #(𝒟.nonMemberSubfamily a) - 2 ^ (2 * m)
  let 𝒩 : Finset (Finset (Fin (2 * m + 1))) := predAboveFamily a (𝒟.nonMemberSubfamily a)
  have hepos : 0 < e := by
    dsimp [e]
    exact Nat.sub_pos_of_lt hexcess
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using
      (isDownSetFamily_predAboveFamily (a := a)
        (𝒜 := 𝒟.nonMemberSubfamily a)
        (fun s hs => (mem_nonMemberSubfamily.mp hs).2)
        (isDownSetFamily_nonMemberSubfamily h𝒟 a))
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) + e := by
    have hpred :
        #(predAboveFamily a (𝒟.nonMemberSubfamily a)) = #(𝒟.nonMemberSubfamily a) := by
      apply card_predAboveFamily (a := a)
      intro s hs
      exact (mem_nonMemberSubfamily.mp hs).2
    dsimp [𝒩, e] at hpred ⊢
    omega
  have hβN : β m e ≤ #(positiveBoundary 𝒩) :=
    hβlower hepos h𝒩down h𝒩card
  have h𝒩bdry :
      #(positiveBoundary 𝒩) =
        #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) := by
    symm
    exact card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predAboveFamily
      (a := a) (𝒜 := 𝒟.nonMemberSubfamily a)
      (fun s hs => (mem_nonMemberSubfamily.mp hs).2)
  have hambient :
      #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) + 2 * e ≤
        #(positiveBoundary 𝒟) := by
    simpa [e] using
      (card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_pow
        (α := Fin (2 * m + 2)) h𝒟 a (k := 2 * m) hcard)
  have hmain :
      2 * Nat.choose (2 * m + 1) m ≤
        #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) + 2 * e := by
    calc
      2 * Nat.choose (2 * m + 1) m ≤ β m e + 2 * e := hβbound m e hepos
      _ ≤ #(positiveBoundary 𝒩) + 2 * e := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hβN (2 * e)
      _ = #((positiveBoundary (𝒟.nonMemberSubfamily a)).nonMemberSubfamily a) + 2 * e := by
        rw [h𝒩bdry]
  rw [choose_middle_even_eq_two_mul_choose_middle_odd]
  exact hmain.trans hambient

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_strictExcessOptimization
    (hOpt : OddSectionStrictExcessOptimizationStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  rcases exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
      (n := 2 * m + 1) (by positivity) hcard htotal with ⟨a, hexcess⟩
  exact choose_middle_le_card_positiveBoundary_even_of_section_excess_of_strictExcessOptimization
    (a := a) hOpt h𝒟 hcard hexcess

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_oddHalfCubeBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  let 𝒩 : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.nonMemberSubfamily 0)
  let ℳ : Finset (Finset (Fin (2 * m + 1))) := predFamily (𝒟.memberSubfamily 0)
  have hNsec :
      #(𝒟.nonMemberSubfamily 0) = 2 ^ (2 * m) :=
    zero_section_balanced_of_halfCube_of_totalSize_eq_max
      (n := 2 * m + 1) (by positivity) h𝒟 hcard htotal
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hcard
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 𝒟
  have hMsec : #(𝒟.memberSubfamily 0) = 2 ^ (2 * m) := by
    omega
  have h𝒩down : IsDownSetFamily 𝒩 := by
    simpa [𝒩] using isDownSetFamily_predFamily_nonMemberSubfamily h𝒟
  have hℳdown : IsDownSetFamily ℳ := by
    simpa [ℳ] using isDownSetFamily_predFamily_memberSubfamily h𝒟
  have h𝒩card : 𝒩.card = 2 ^ (2 * m) := by
    simpa [𝒩, hNsec] using card_predFamily_nonMemberSubfamily (𝒜 := 𝒟)
  have hℳcard : ℳ.card = 2 ^ (2 * m) := by
    simpa [ℳ, hMsec] using card_predFamily_memberSubfamily (𝒜 := 𝒟)
  have hNbdry : Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒩) :=
    hOdd h𝒩down h𝒩card
  have hMbdry : Nat.choose (2 * m + 1) m ≤ #(positiveBoundary ℳ) :=
    hOdd hℳdown hℳcard
  have hpair :
      2 * Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒩) + #(positiveBoundary ℳ) := by
    omega
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

theorem choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hOpt : OddSectionStrictExcessOptimizationStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hcard
  have hhalf : ∀ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤ #(𝒟.nonMemberSubfamily a) := by
    intro a
    exact half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul h𝒟 a (2 ^ (2 * m)) hcard'
  have hsumLower :
      ∑ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤
        ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) := by
    exact Finset.sum_le_sum fun a _ => hhalf a
  have hconst :
      ∑ _a : Fin (2 * m + 2), 2 ^ (2 * m) = (2 * m + 2) * 2 ^ (2 * m) := by
    simp
  have hsumEq :
      ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) =
        (2 * m + 2) * (2 * 2 ^ (2 * m)) - totalSize 𝒟 := by
    simpa [hcard'] using
      (sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize (𝒜 := 𝒟))
  have hdouble :
      (2 * m + 2) * (2 * 2 ^ (2 * m)) =
        2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
    ring
  let x := (2 * m + 2) * 2 ^ (2 * m)
  have htotalUpper : totalSize 𝒟 ≤ 2 * x := by
    dsimp [x]
    unfold totalSize
    calc
      ∑ s ∈ 𝒟, s.card ≤ ∑ s ∈ 𝒟, (2 * m + 2) := by
        exact Finset.sum_le_sum fun s hs => by
          simpa using (Finset.card_le_univ (s := s))
      _ = 𝒟.card * (2 * m + 2) := by
        rw [Finset.sum_const_nat]
        intro x hx
        rfl
      _ = 2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
        rw [hcard']
        ring
  have htotalLe : totalSize 𝒟 ≤ (2 * m + 2) * 2 ^ (2 * m) := by
    rw [hconst, hsumEq, hdouble] at hsumLower
    have hsumLower' : x + totalSize 𝒟 ≤ 2 * x :=
      (Nat.le_sub_iff_add_le htotalUpper).1 hsumLower
    have hsumLower'' : x + totalSize 𝒟 ≤ x + x := by
      simpa [x, two_mul, add_assoc, add_left_comm, add_comm] using hsumLower'
    exact Nat.le_of_add_le_add_left hsumLower''
  by_cases htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)
  · exact choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_oddHalfCubeBoundaryLower
      hOdd h𝒟 hcard htotal
  · have hlt : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m) :=
      lt_of_le_of_ne htotalLe htotal
    exact choose_middle_le_card_positiveBoundary_even_of_totalSize_lt_max_of_strictExcessOptimization
      hOpt h𝒟 hcard hlt

theorem totalSize_le_max_of_isDownSetFamily_of_card_eq_half_cube_even
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    totalSize 𝒟 ≤ (2 * m + 2) * 2 ^ (2 * m) := by
  have hcard' : 𝒟.card = 2 * 2 ^ (2 * m) := by
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hcard
  have hhalf : ∀ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤ #(𝒟.nonMemberSubfamily a) := by
    intro a
    exact half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul h𝒟 a (2 ^ (2 * m)) hcard'
  have hsumLower :
      ∑ a : Fin (2 * m + 2), 2 ^ (2 * m) ≤
        ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) := by
    exact Finset.sum_le_sum fun a _ => hhalf a
  have hconst :
      ∑ _a : Fin (2 * m + 2), 2 ^ (2 * m) = (2 * m + 2) * 2 ^ (2 * m) := by
    simp
  have hsumEq :
      ∑ a : Fin (2 * m + 2), #(𝒟.nonMemberSubfamily a) =
        (2 * m + 2) * (2 * 2 ^ (2 * m)) - totalSize 𝒟 := by
    simpa [hcard'] using
      (sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize (𝒜 := 𝒟))
  have hdouble :
      (2 * m + 2) * (2 * 2 ^ (2 * m)) =
        2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
    ring
  let x := (2 * m + 2) * 2 ^ (2 * m)
  have htotalUpper : totalSize 𝒟 ≤ 2 * x := by
    dsimp [x]
    unfold totalSize
    calc
      ∑ s ∈ 𝒟, s.card ≤ ∑ s ∈ 𝒟, (2 * m + 2) := by
        exact Finset.sum_le_sum fun s hs => by
          simpa using (Finset.card_le_univ (s := s))
      _ = 𝒟.card * (2 * m + 2) := by
        rw [Finset.sum_const_nat]
        intro x hx
        rfl
      _ = 2 * ((2 * m + 2) * 2 ^ (2 * m)) := by
        rw [hcard']
        ring
  rw [hconst, hsumEq, hdouble] at hsumLower
  have hsumLower' : x + totalSize 𝒟 ≤ 2 * x :=
    (Nat.le_sub_iff_add_le htotalUpper).1 hsumLower
  have hsumLower'' : x + totalSize 𝒟 ≤ x + x := by
    simpa [x, two_mul, add_assoc, add_left_comm, add_comm] using hsumLower'
  exact Nat.le_of_add_le_add_left hsumLower''

/-- Active `Fin n` proof-program closure after rejecting the false paired-section branch. -/
theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hOpt : OddSectionStrictExcessOptimizationStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 0 < m := by
      omega
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
    have hdiv : (k + (k + 2)) / 2 = k + 1 := by
      omega
    simpa [two_mul, hdiv, add_assoc, add_left_comm, add_comm] using
      (choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization
        hOdd hOpt (m := k) h𝒟 (by
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hcard))
  · have hdiv : (2 * m + 1) / 2 = m := by
      omega
    simpa [hdiv] using hOdd h𝒟 hcard

/-- Direct `Fin n` closure from the odd half-cube theorem and the explicit strict-excess odd
section inequality. -/
theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_directStrictExcess
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hDirect : OddSectionDirectStrictExcessStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_strictExcessOptimization
      hOdd (oddSectionStrictExcessOptimization_of_directStrictExcess hDirect) hn h𝒟 hcard

theorem choose_middle_le_card_positiveBoundary_odd_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 1)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m)) :
    Nat.choose (2 * m + 1) m ≤ #(positiveBoundary 𝒟) := by
  exact False.elim (not_OddSectionPairBoundaryLowerStatement hPair)

theorem choose_middle_le_card_positiveBoundary_even_of_totalSize_eq_max_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1))
    (htotal : totalSize 𝒟 = (2 * m + 2) * 2 ^ (2 * m)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  exact False.elim (not_OddSectionPairBoundaryLowerStatement hPair)

theorem choose_middle_le_card_positiveBoundary_even_of_card_eq_half_cube_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (2 * m + 1)) :
    Nat.choose (2 * m + 2) (m + 1) ≤ #(positiveBoundary 𝒟) := by
  exact False.elim (not_OddSectionPairBoundaryLowerStatement hPair)

theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_section_pairBoundaryLower
    (hPair : OddSectionPairBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact False.elim (not_OddSectionPairBoundaryLowerStatement hPair)

section Relabel

variable {β : Type*} [DecidableEq β] [Fintype β]

theorem map_map_symm_equiv (e : α ≃ β) (s : Finset α) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  have hcomp : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl α := by
    ext x
    simp
  simpa [hcomp] using Finset.map_map e.toEmbedding e.symm.toEmbedding s

theorem map_map_equiv_symm (e : α ≃ β) (s : Finset β) :
    (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
  have hcomp : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl β := by
    ext x
    simp
  simpa [hcomp] using Finset.map_map e.symm.toEmbedding e.toEmbedding s

theorem image_positiveBoundary_map_equiv (e : α ≃ β) (𝒜 : Finset (Finset α)) :
    (positiveBoundary 𝒜).image (fun s => s.map e.toEmbedding) =
      positiveBoundary (𝒜.image fun s => s.map e.toEmbedding) := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
    rw [mem_positiveBoundary] at hs
    rcases hs with ⟨hsNotMem, a, ha, hsErase⟩
    rw [mem_positiveBoundary]
    refine ⟨?_, e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    · intro hsImage
      rcases Finset.mem_image.mp hsImage with ⟨u, hu, huEq⟩
      exact hsNotMem ((Finset.map_injective e.toEmbedding) huEq ▸ hu)
    · refine Finset.mem_image.mpr ⟨s.erase a, hsErase, ?_⟩
      rw [Finset.map_erase]
      rfl
  · intro ht
    rw [mem_positiveBoundary] at ht
    rcases ht with ⟨htNotImage, b, hb, htEraseImage⟩
    let s : Finset α := t.map e.symm.toEmbedding
    have hsMap : s.map e.toEmbedding = t := by
      simpa [s] using map_map_equiv_symm (e := e) t
    have hbPre : e.symm b ∈ s := by
      dsimp [s]
      exact Finset.mem_map.mpr ⟨b, hb, by simp⟩
    have hsNotMem : s ∉ 𝒜 := by
      intro hsMem
      exact htNotImage (Finset.mem_image.mpr ⟨s, hsMem, hsMap⟩)
    rcases Finset.mem_image.mp htEraseImage with ⟨u, hu, huEq⟩
    have hsEraseMap : (s.erase (e.symm b)).map e.toEmbedding = t.erase b := by
      calc
        (s.erase (e.symm b)).map e.toEmbedding = (s.map e.toEmbedding).erase (e (e.symm b)) := by
          rw [Finset.map_erase]
          rfl
        _ = t.erase b := by simpa [hsMap]
    have huEq' : u = s.erase (e.symm b) := by
      exact (Finset.map_injective e.toEmbedding) (huEq.trans hsEraseMap.symm)
    have hsEraseMem : s.erase (e.symm b) ∈ 𝒜 := by
      simpa [huEq'] using hu
    refine Finset.mem_image.mpr ⟨s, ?_, hsMap⟩
    rw [mem_positiveBoundary]
    exact ⟨hsNotMem, e.symm b, hbPre, hsEraseMem⟩

theorem isDownSetFamily_image_equiv {𝒜 : Finset (Finset α)} (e : α ≃ β)
    (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (𝒜.image fun s => s.map e.toEmbedding) := by
  intro s t hts hs
  rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
  have hpre : t.map e.symm.toEmbedding ⊆ u := by
    exact (Finset.map_symm_subset (t := t) (s := u) (f := e)).2 hts
  refine Finset.mem_image.mpr ⟨t.map e.symm.toEmbedding, h𝒜 hpre hu, ?_⟩
  simpa using map_map_equiv_symm (e := e) t

theorem card_image_map_equiv (e : α ≃ β) (𝒜 : Finset (Finset α)) :
    #(𝒜.image fun s => s.map e.toEmbedding) = #𝒜 := by
  exact Finset.card_image_of_injOn (by
    intro s hs t ht hEq
    exact (Finset.map_injective e.toEmbedding) hEq)

theorem totalSize_image_equiv (e : α ≃ β) (𝒜 : Finset (Finset α)) :
    totalSize (𝒜.image fun s => s.map e.toEmbedding) = totalSize 𝒜 := by
  unfold totalSize
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro s hs
    simp
  · intro s hs t ht hEq
    exact (Finset.map_injective e.toEmbedding) hEq

theorem nonMemberSubfamily_image_equiv (e : α ≃ β) (a : α) (𝒜 : Finset (Finset α)) :
    (𝒜.image fun s => s.map e.toEmbedding).nonMemberSubfamily (e a) =
      (𝒜.nonMemberSubfamily a).image fun s => s.map e.toEmbedding := by
  ext t
  constructor
  · intro ht
    rcases mem_nonMemberSubfamily.mp ht with ⟨htImg, hta⟩
    rcases Finset.mem_image.mp htImg with ⟨s, hsA, rfl⟩
    refine Finset.mem_image.mpr ⟨s, ?_, rfl⟩
    refine mem_nonMemberSubfamily.mpr ⟨hsA, ?_⟩
    intro ha
    exact hta (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨s, hsNon, rfl⟩
    refine mem_nonMemberSubfamily.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨s, (mem_nonMemberSubfamily.mp hsNon).1, rfl⟩
    · intro hea
      rcases Finset.mem_map.mp hea with ⟨x, hx, hxe⟩
      have hxa : x = a := e.injective hxe
      exact (mem_nonMemberSubfamily.mp hsNon).2 (hxa ▸ hx)

theorem card_positiveBoundary_image_equiv (e : α ≃ β) (𝒜 : Finset (Finset α)) :
    #(positiveBoundary (𝒜.image fun s => s.map e.toEmbedding)) = #(positiveBoundary 𝒜) := by
  calc
    #(positiveBoundary (𝒜.image fun s => s.map e.toEmbedding))
      = #((positiveBoundary 𝒜).image fun s => s.map e.toEmbedding) := by
          rw [← image_positiveBoundary_map_equiv (β := β) e 𝒜]
    _ = #(positiveBoundary 𝒜) := by
          simpa using card_image_map_equiv (β := β) e (positiveBoundary 𝒜)

theorem isEvenHalfCubeBoundaryGlobalMinimizer_image_equiv
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (e : Fin (2 * m + 2) ≃ Fin (2 * m + 2))
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟) :
    IsEvenHalfCubeBoundaryGlobalMinimizer (m := m)
      (𝒟.image fun s => s.map e.toEmbedding) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using isDownSetFamily_image_equiv e hmin.1
  · calc
      #(𝒟.image fun s => s.map e.toEmbedding) = #𝒟 := by
        simpa using card_image_map_equiv e 𝒟
      _ = 2 ^ (2 * m + 1) := hmin.2.1
  · intro 𝒜 h𝒜 h𝒜card
    let 𝒜' : Finset (Finset (Fin (2 * m + 2))) :=
      𝒜.image fun s => s.map e.symm.toEmbedding
    have h𝒜'down : IsDownSetFamily 𝒜' := by
      simpa [𝒜'] using isDownSetFamily_image_equiv e.symm h𝒜
    have h𝒜'card : 𝒜'.card = 2 ^ (2 * m + 1) := by
      calc
        𝒜'.card = 𝒜.card := by
          simpa [𝒜'] using card_image_map_equiv e.symm 𝒜
        _ = 2 ^ (2 * m + 1) := h𝒜card
    have hle := hmin.2.2 h𝒜'down h𝒜'card
    calc
      #(positiveBoundary (𝒟.image fun s => s.map e.toEmbedding)) = #(positiveBoundary 𝒟) := by
        simpa using card_positiveBoundary_image_equiv e 𝒟
      _ ≤ #(positiveBoundary 𝒜') := hle
      _ = #(positiveBoundary 𝒜) := by
        dsimp [𝒜']
        simpa using card_positiveBoundary_image_equiv e.symm 𝒜

theorem exists_isEvenHalfCubeBoundaryGlobalMinimizer_zeroSectionExcess_of_totalSize_lt_max_up_to_relabel
    {m : ℕ} {𝒟 : Finset (Finset (Fin (2 * m + 2)))}
    (hmin : IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟)
    (htotal : totalSize 𝒟 < (2 * m + 2) * 2 ^ (2 * m)) :
    ∃ 𝒟' : Finset (Finset (Fin (2 * m + 2))),
      IsEvenHalfCubeBoundaryGlobalMinimizer (m := m) 𝒟' ∧
      totalSize 𝒟' = totalSize 𝒟 ∧
      2 ^ (2 * m) < #(𝒟'.nonMemberSubfamily 0) := by
  rcases exists_coordinate_excess_of_halfCube_of_totalSize_lt_max
      (n := 2 * m + 1) (by positivity) hmin.2.1 htotal with ⟨a, hexcess⟩
  let e : Fin (2 * m + 2) ≃ Fin (2 * m + 2) := Equiv.swap a 0
  let 𝒟' : Finset (Finset (Fin (2 * m + 2))) := 𝒟.image fun s => s.map e.toEmbedding
  refine ⟨𝒟', isEvenHalfCubeBoundaryGlobalMinimizer_image_equiv e hmin, ?_, ?_⟩
  · dsimp [𝒟']
    simpa using totalSize_image_equiv e 𝒟
  · have he0 : e a = 0 := by
      simp [e]
    have hsec :
        #(𝒟'.nonMemberSubfamily 0) = #(𝒟.nonMemberSubfamily a) := by
      rw [← he0]
      dsimp [𝒟']
      rw [nonMemberSubfamily_image_equiv]
      simpa using card_image_map_equiv e (𝒟.nonMemberSubfamily a)
    rw [hsec]
    exact hexcess

theorem halfCubeBoundaryLower_of_finHalfCubeBoundaryLower
    (hFin :
      ∀ {n : ℕ}, 0 < n → ∀ {𝒟 : Finset (Finset (Fin n))},
        IsDownSetFamily 𝒟 →
          𝒟.card = 2 ^ (n - 1) →
            Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟)) :
    HalfCubeBoundaryLowerStatement := by
  intro α _ _ 𝒟 hn _ h𝒟 hcard
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let 𝒟' : Finset (Finset (Fin (Fintype.card α))) := 𝒟.image fun s => s.map e.toEmbedding
  have h𝒟'down : IsDownSetFamily 𝒟' := by
    simpa [𝒟'] using isDownSetFamily_image_equiv (β := Fin (Fintype.card α)) e h𝒟
  have h𝒟'card : 𝒟'.card = 2 ^ (Fintype.card α - 1) := by
    calc
      𝒟'.card = 𝒟.card := by
        simpa [𝒟'] using card_image_map_equiv (β := Fin (Fintype.card α)) e 𝒟
      _ = 2 ^ (Fintype.card α - 1) := hcard
  have hbound :
      Nat.choose (Fintype.card α) (Fintype.card α / 2) ≤ #(positiveBoundary 𝒟') := by
    simpa [𝒟'] using hFin (n := Fintype.card α) hn h𝒟'down h𝒟'card
  have hbdry :
      #(positiveBoundary 𝒟') = #(positiveBoundary 𝒟) := by
    calc
      #(positiveBoundary 𝒟') = #((positiveBoundary 𝒟).image fun s => s.map e.toEmbedding) := by
        rw [show 𝒟' = 𝒟.image (fun s => s.map e.toEmbedding) by rfl]
        rw [← image_positiveBoundary_map_equiv (β := Fin (Fintype.card α)) e 𝒟]
      _ = #(positiveBoundary 𝒟) := by
        simpa using card_image_map_equiv (β := Fin (Fintype.card α)) e (positiveBoundary 𝒟)
  rw [hbdry] at hbound
  exact hbound

end Relabel

theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
      (oddSectionPairInterfaceBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
        hOdd hPair)
      hn h𝒟 hcard

theorem halfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  refine halfCubeBoundaryLower_of_finHalfCubeBoundaryLower ?_
  intro n hn 𝒟 h𝒟 hcard
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_section_pairInterfaceBoundaryLower
      hPair hn h𝒟 hcard

theorem oddSectionPairInterfaceBoundaryLower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement) :
    OddSectionPairInterfaceBoundaryLowerStatement := by
  intro m e 𝒩 ℳ h𝒩 hℳ hsub h𝒩card hℳcard
  have he : e ≤ 2 ^ (2 * m) := by
    have hcard_le :
        𝒩.card ≤ 2 ^ (2 * m + 1) := by
      calc
        𝒩.card ≤ Fintype.card (Finset (Fin (2 * m + 1))) := Finset.card_le_univ 𝒩
        _ = 2 ^ (2 * m + 1) := by simp
    rw [h𝒩card, pow_succ'] at hcard_le
    omega
  have hdata :=
    twoSheetFamily_halfCube_data (m := m) (e := e) h𝒩 hℳ hsub he h𝒩card hℳcard
  have hne : (twoSheetFamily ℳ 𝒩).Nonempty := by
    apply Finset.card_pos.mp
    rw [hdata.2]
    positivity
  have hbound :
      Nat.choose (2 * m + 2) ((2 * m + 2) / 2) ≤
        #(positiveBoundary (twoSheetFamily ℳ 𝒩)) :=
    by
      simpa using
        (hCube (α := Fin (2 * m + 2)) (𝒟 := twoSheetFamily ℳ 𝒩)
          (by positivity) hne hdata.1 (by simpa using hdata.2))
  have hdiv : (2 * m + 2) / 2 = m + 1 := by
    omega
  rw [← twoSheetOuterBoundaryCard_eq_card_positiveBoundary_twoSheetFamily (ℳ := ℳ) (𝒩 := 𝒩)] at hbound
  simpa [hdiv, choose_middle_even_eq_two_mul_choose_middle_odd,
    twoSheetOuterBoundaryCard, twoSheetInterfaceBoundary] using hbound

theorem oddSectionPairInterfaceBoundaryLower_iff_halfCubeBoundaryLower :
    OddSectionPairInterfaceBoundaryLowerStatement ↔ HalfCubeBoundaryLowerStatement := by
  constructor
  · exact halfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
  · exact oddSectionPairInterfaceBoundaryLower_of_halfCubeBoundaryLower

theorem halfCubeBoundaryLower_of_topologicalOddSectionBoundaryLower
    (hTop : TopologicalOddSectionBoundaryLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  exact halfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
    ((topologicalOddSectionBoundaryLowerStatement_iff_pairInterface).mp hTop)

theorem halfCubeBoundaryLower_of_twoSheetBoundaryTheorem
    (hTwo : TwoSheetBoundaryTheorem) :
    HalfCubeBoundaryLowerStatement := by
  exact halfCubeBoundaryLower_of_topologicalOddSectionBoundaryLower hTwo

theorem twoSheetBoundaryTheorem_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement) :
    TwoSheetBoundaryTheorem := by
  exact
    (topologicalOddSectionBoundaryLowerStatement_iff_pairInterface).mpr
      (oddSectionPairInterfaceBoundaryLower_of_halfCubeBoundaryLower hCube)

theorem twoSheetBoundaryTheorem_iff_halfCubeBoundaryLower :
    TwoSheetBoundaryTheorem ↔ HalfCubeBoundaryLowerStatement := by
  constructor
  · exact halfCubeBoundaryLower_of_twoSheetBoundaryTheorem
  · exact twoSheetBoundaryTheorem_of_halfCubeBoundaryLower

theorem prismHalfCubeBoundaryLowerStatement_iff_halfCubeBoundaryLower :
    PrismHalfCubeBoundaryLowerStatement ↔ HalfCubeBoundaryLowerStatement := by
  rw [prismHalfCubeBoundaryLowerStatement_iff_twoSheetBoundaryTheorem]
  exact twoSheetBoundaryTheorem_iff_halfCubeBoundaryLower

theorem halfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  refine halfCubeBoundaryLower_of_finHalfCubeBoundaryLower ?_
  intro n hn 𝒟 h𝒟 hcard
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
      hOdd hPair hn h𝒟 hcard

theorem choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeUpperShadowGapLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
      (oddHalfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower hOdd) hPair hn h𝒟 hcard

theorem halfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeUpperShadowGapLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  refine halfCubeBoundaryLower_of_finHalfCubeBoundaryLower ?_
  intro n hn 𝒟 h𝒟 hcard
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
      hOdd hPair hn h𝒟 hcard

theorem halfCubeUpperShadowGapLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeUpperShadowGapLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    HalfCubeUpperShadowGapLowerStatement := by
  exact
    halfCubeUpperShadowGapLower_of_halfCubeBoundaryLower
      (halfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
        hOdd hPair)

theorem oddSectionPositiveExcessPairInterfaceBoundaryLower_of_halfCubeBoundaryLower
    (hCube : HalfCubeBoundaryLowerStatement) :
    OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement := by
  exact
    oddSectionPositiveExcessPairInterfaceBoundaryLower_of_section_pairInterfaceBoundaryLower
      (oddSectionPairInterfaceBoundaryLower_of_halfCubeBoundaryLower hCube)

theorem
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement)
    {n : ℕ} (hn : 0 < n) {𝒟 : Finset (Finset (Fin n))}
    (h𝒟 : IsDownSetFamily 𝒟)
    (hcard : 𝒟.card = 2 ^ (n - 1)) :
    Nat.choose n (n / 2) ≤ #(positiveBoundary 𝒟) := by
  exact
    choose_middle_le_card_positiveBoundary_of_card_eq_half_cube_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
      (oddHalfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier hFrontier)
      hPair hn h𝒟 hcard

theorem
    halfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    HalfCubeBoundaryLowerStatement := by
  exact
    halfCubeBoundaryLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
      (oddHalfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier hFrontier) hPair

theorem
    halfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement) :
    HalfCubeUpperShadowGapLowerStatement := by
  exact
    halfCubeUpperShadowGapLower_of_oddHalfCubeUpperShadowGapLower_of_positiveExcessPairInterfaceBoundaryLower
      (oddHalfCubeUpperShadowGapLower_of_prismTheoremCurrentLeafFrontier hFrontier) hPair

theorem
    oddSectionPositiveExcessPairInterfaceBoundaryLower_iff_halfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement ↔ HalfCubeBoundaryLowerStatement := by
  constructor
  · exact halfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier_of_positiveExcessPairInterfaceBoundaryLower hFrontier
  · exact oddSectionPositiveExcessPairInterfaceBoundaryLower_of_halfCubeBoundaryLower

theorem
    twoSheetBoundaryTheorem_iff_positiveExcessPairInterfaceBoundaryLower_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    TwoSheetBoundaryTheorem ↔ OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement := by
  exact
    twoSheetBoundaryTheorem_iff_halfCubeBoundaryLower.trans
      (oddSectionPositiveExcessPairInterfaceBoundaryLower_iff_halfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier
        hFrontier).symm

theorem
    prismHalfCubeBoundaryLowerStatement_iff_positiveExcessPairInterfaceBoundaryLower_of_prismTheoremCurrentLeafFrontier
    (hFrontier : PrismTheoremCurrentLeafFrontierStatement) :
    PrismHalfCubeBoundaryLowerStatement ↔
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement := by
  exact
    prismHalfCubeBoundaryLowerStatement_iff_halfCubeBoundaryLower.trans
      (oddSectionPositiveExcessPairInterfaceBoundaryLower_iff_halfCubeBoundaryLower_of_prismTheoremCurrentLeafFrontier
        hFrontier).symm

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

theorem subcubeHalfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
  exact
    subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower
      (halfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower hPair) h hA

theorem positiveBoundaryFamilyNat_lower_of_section_pairInterfaceBoundaryLower
    (hPair : OddSectionPairInterfaceBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card := by
  exact
    positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower
      (halfCubeBoundaryLower_of_section_pairInterfaceBoundaryLower hPair) h hA

theorem subcubeHalfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundary (negativeHalfFamilySubcubeNat A)).card := by
  exact
    subcubeHalfCubeBoundaryLower_of_halfCubeBoundaryLower
      (halfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
        hOdd hPair) h hA

theorem positiveBoundaryFamilyNat_lower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
    (hOdd : OddHalfCubeBoundaryLowerStatement)
    (hPair :
      OddSectionPositiveExcessPairInterfaceBoundaryLowerStatement)
    {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card := by
  exact
    positiveBoundaryFamilyNat_lower_of_halfCubeBoundaryLower
      (halfCubeBoundaryLower_of_oddHalfCubeBoundaryLower_of_positiveExcessPairInterfaceBoundaryLower
        hOdd hPair) h hA

end Erdos1
