import ErdosProblems.Problem1

namespace Erdos1

/--
The subsets of `A` whose subset sum lies strictly below half of the total sum of `A`.
This is the lower half of the cube used in the exact-middle-binomial argument.
-/
def negativeHalfFamilyNat (A : Finset ℕ) : Finset (Finset ℕ) :=
  (A.powerset).filter fun S => 2 * S.sum id < A.sum id

/--
The subsets of `A` whose subset sum lies strictly above half of the total sum of `A`.
-/
def positiveHalfFamilyNat (A : Finset ℕ) : Finset (Finset ℕ) :=
  (A.powerset).filter fun S => A.sum id < 2 * S.sum id

/--
The positive boundary of `negativeHalfFamilyNat`: these are subsets of `A` whose sum lies strictly
above half of `A.sum`, but becomes strictly below half after erasing some element.
-/
def positiveBoundaryFamilyNat (A : Finset ℕ) : Finset (Finset ℕ) :=
  (A.powerset).filter fun S =>
    A.sum id < 2 * S.sum id ∧ ∃ a ∈ S, 2 * (S.erase a).sum id < A.sum id

/--
The positive vertex boundary of a family `F ⊆ powerset(A)`: these are subsets of `A` that do not
lie in `F`, but reach `F` after deleting one element.
-/
def positiveVertexBoundaryNat (A : Finset ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (A.powerset).filter fun S => S ∉ F ∧ ∃ a ∈ S, S.erase a ∈ F

@[simp]
theorem mem_negativeHalfFamilyNat {A S : Finset ℕ} :
    S ∈ negativeHalfFamilyNat A ↔ S ⊆ A ∧ 2 * S.sum id < A.sum id := by
  simp [negativeHalfFamilyNat]

@[simp]
theorem mem_positiveHalfFamilyNat {A S : Finset ℕ} :
    S ∈ positiveHalfFamilyNat A ↔ S ⊆ A ∧ A.sum id < 2 * S.sum id := by
  simp [positiveHalfFamilyNat]

@[simp]
theorem mem_positiveBoundaryFamilyNat {A S : Finset ℕ} :
    S ∈ positiveBoundaryFamilyNat A ↔
      S ⊆ A ∧ A.sum id < 2 * S.sum id ∧ ∃ a ∈ S, 2 * (S.erase a).sum id < A.sum id := by
  simp [positiveBoundaryFamilyNat]

/--
The arithmetic definition of `positiveBoundaryFamilyNat` is equivalent to saying that `S` lies in
the strict upper half and one deletion lands in the strict lower half.
-/
theorem mem_positiveBoundaryFamilyNat_iff_mem_positiveHalf_and_exists_erase_negative
    {A S : Finset ℕ} :
    S ∈ positiveBoundaryFamilyNat A ↔
      S ∈ positiveHalfFamilyNat A ∧ ∃ a ∈ S, S.erase a ∈ negativeHalfFamilyNat A := by
  constructor
  · intro hS
    rcases mem_positiveBoundaryFamilyNat.mp hS with ⟨hSA, hgt, a, haS, hlt⟩
    refine ⟨mem_positiveHalfFamilyNat.mpr ⟨hSA, hgt⟩, a, haS, ?_⟩
    refine mem_negativeHalfFamilyNat.mpr ⟨?_, hlt⟩
    exact (S.erase_subset a).trans hSA
  · rintro ⟨hPos, a, haS, hNeg⟩
    rcases mem_positiveHalfFamilyNat.mp hPos with ⟨hSA, hgt⟩
    rcases mem_negativeHalfFamilyNat.mp hNeg with ⟨-, hlt⟩
    exact mem_positiveBoundaryFamilyNat.mpr ⟨hSA, hgt, a, haS, hlt⟩

@[simp]
theorem mem_positiveVertexBoundaryNat {A S : Finset ℕ} {F : Finset (Finset ℕ)} :
    S ∈ positiveVertexBoundaryNat A F ↔
      S ⊆ A ∧ S ∉ F ∧ ∃ a ∈ S, S.erase a ∈ F := by
  simp [positiveVertexBoundaryNat]

/-- Every positive-boundary set lies in the strict upper half. -/
theorem positiveBoundaryFamilyNat_subset_positiveHalfFamilyNat (A : Finset ℕ) :
    positiveBoundaryFamilyNat A ⊆ positiveHalfFamilyNat A := by
  intro S hS
  exact (mem_positiveBoundaryFamilyNat_iff_mem_positiveHalf_and_exists_erase_negative.mp hS).1

/-- A nonempty sum-distinct set cannot live in the degenerate ambient interval `{1, ..., 0}`. -/
theorem nonempty_of_isSumDistinctSet_ne_zero {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) : N ≠ 0 := by
  intro hN
  rcases hA with ⟨a, ha⟩
  have haIcc := h.1 ha
  rw [hN, Finset.Icc_eq_empty_of_lt (by omega)] at haIcc
  simp at haIcc

/-- Sum-distinctness gives injectivity of `sum` on `A.powerset`. -/
theorem sum_injOn_powerset {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) :
    Set.InjOn (fun S : Finset ℕ => S.sum id) A.powerset := by
  intro S hS T hT hsum
  let S' : {U : Finset ℕ // U ∈ A.powerset} := ⟨S, hS⟩
  let T' : {U : Finset ℕ // U ∈ A.powerset} := ⟨T, hT⟩
  have hEq : S' = T' := by
    exact (h.2) (by simpa [S', T'] using hsum)
  exact congrArg Subtype.val hEq

/--
For a nonempty sum-distinct set, no subset sum can be exactly half of the total sum.
-/
theorem two_mul_sum_ne_total_of_isSumDistinct {A S : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) (hS : S ⊆ A) :
    2 * S.sum id ≠ A.sum id := by
  intro hEq
  have hsum_sdiff : (A \ S).sum id + S.sum id = A.sum id := by
    simpa [add_comm] using (Finset.sum_sdiff (f := id) hS)
  have hsum_eq : S.sum id = (A \ S).sum id := by
    omega
  have hSetEq : S = A \ S := by
    exact sum_injOn_powerset h (Finset.mem_powerset.mpr hS)
      (Finset.mem_powerset.mpr Finset.sdiff_subset) hsum_eq
  have hAeqS : A = S := by
    calc
      A = (A \ S) ∪ S := by
        symm
        exact Finset.sdiff_union_of_subset hS
      _ = S ∪ S := by rw [← hSetEq]
      _ = S := by simp
  have hSEmpty : S = ∅ := by
    calc
      S = A \ S := hSetEq
      _ = S \ S := by rw [hAeqS]
      _ = ∅ := by simp
  have hAEmpty : A = ∅ := by simpa [hAeqS] using hSEmpty
  exact hA.ne_empty hAEmpty

/--
The arithmetic boundary family is exactly the positive vertex boundary of the strict lower half.
-/
theorem mem_positiveBoundaryFamilyNat_iff_boundary {A S : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    S ∈ positiveBoundaryFamilyNat A ↔
      S ∈ positiveVertexBoundaryNat A (negativeHalfFamilyNat A) := by
  constructor
  · intro hS
    rcases mem_positiveBoundaryFamilyNat_iff_mem_positiveHalf_and_exists_erase_negative.mp hS with
      ⟨hPos, a, haS, hNeg⟩
    rcases mem_positiveHalfFamilyNat.mp hPos with ⟨hSA, hgt⟩
    refine mem_positiveVertexBoundaryNat.mpr ⟨hSA, ?_, a, haS, hNeg⟩
    intro hNegSelf
    rcases mem_negativeHalfFamilyNat.mp hNegSelf with ⟨-, hlt⟩
    omega
  · intro hS
    rcases mem_positiveVertexBoundaryNat.mp hS with ⟨hSA, hNotNeg, a, haS, hNeg⟩
    have hneq : 2 * S.sum id ≠ A.sum id :=
      two_mul_sum_ne_total_of_isSumDistinct h hA hSA
    have hgt : A.sum id < 2 * S.sum id := by
      by_contra hle
      exact hNotNeg (mem_negativeHalfFamilyNat.mpr ⟨hSA, by omega⟩)
    exact (mem_positiveBoundaryFamilyNat_iff_mem_positiveHalf_and_exists_erase_negative).mpr
      ⟨mem_positiveHalfFamilyNat.mpr ⟨hSA, hgt⟩, a, haS, hNeg⟩

/-- The arithmetic positive-boundary family equals the positive vertex boundary of the strict lower
half family. -/
theorem positiveBoundaryFamilyNat_eq_positiveBoundary {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    positiveBoundaryFamilyNat A = positiveVertexBoundaryNat A (negativeHalfFamilyNat A) := by
  ext S
  exact mem_positiveBoundaryFamilyNat_iff_boundary h hA

/-- Complement in `A` sends the strict lower half to the strict upper half. -/
theorem sdiff_mem_positiveHalfFamilyNat {A S : Finset ℕ}
    (hS : S ∈ negativeHalfFamilyNat A) : A \ S ∈ positiveHalfFamilyNat A := by
  rcases mem_negativeHalfFamilyNat.mp hS with ⟨hSA, hlt⟩
  refine mem_positiveHalfFamilyNat.mpr ⟨Finset.sdiff_subset, ?_⟩
  have hsum_sdiff : (A \ S).sum id + S.sum id = A.sum id := by
    simpa [add_comm] using (Finset.sum_sdiff (f := id) hSA)
  omega

/-- Complement in `A` sends the strict upper half to the strict lower half. -/
theorem sdiff_mem_negativeHalfFamilyNat {A S : Finset ℕ}
    (hS : S ∈ positiveHalfFamilyNat A) : A \ S ∈ negativeHalfFamilyNat A := by
  rcases mem_positiveHalfFamilyNat.mp hS with ⟨hSA, hlt⟩
  refine mem_negativeHalfFamilyNat.mpr ⟨Finset.sdiff_subset, ?_⟩
  have hsum_sdiff : (A \ S).sum id + S.sum id = A.sum id := by
    simpa [add_comm] using (Finset.sum_sdiff (f := id) hSA)
  omega

/-- Complement in `A` identifies the strict lower half with the strict upper half. -/
theorem image_sdiff_negativeHalfFamilyNat (A : Finset ℕ) :
    (negativeHalfFamilyNat A).image (fun S : Finset ℕ => A \ S) = positiveHalfFamilyNat A := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    exact sdiff_mem_positiveHalfFamilyNat hT
  · intro hS
    refine Finset.mem_image.mpr ⟨A \ S, sdiff_mem_negativeHalfFamilyNat hS, ?_⟩
    rcases mem_positiveHalfFamilyNat.mp hS with ⟨hSA, -⟩
    rw [Finset.sdiff_sdiff_eq_self hSA]

/-- The strict lower and strict upper halves have the same cardinality. -/
theorem negativeHalfFamilyNat_card_eq_positiveHalfFamilyNat_card (A : Finset ℕ) :
    (negativeHalfFamilyNat A).card = (positiveHalfFamilyNat A).card := by
  calc
    (negativeHalfFamilyNat A).card
      = ((negativeHalfFamilyNat A).image fun S : Finset ℕ => A \ S).card := by
          symm
          exact Finset.card_image_of_injOn (by
            intro S hS T hT hEq
            rcases mem_negativeHalfFamilyNat.mp hS with ⟨hSA, -⟩
            rcases mem_negativeHalfFamilyNat.mp hT with ⟨hTA, -⟩
            calc
              S = A \ (A \ S) := by symm; exact Finset.sdiff_sdiff_eq_self hSA
              _ = A \ (A \ T) := by simpa using congrArg (fun U : Finset ℕ => A \ U) hEq
              _ = T := Finset.sdiff_sdiff_eq_self hTA)
    _ = (positiveHalfFamilyNat A).card := by
      rw [image_sdiff_negativeHalfFamilyNat]

/--
For a nonempty sum-distinct set, the strict lower half contains exactly half of the power set.
-/
theorem negativeHalfFamilyNat_card {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hA : A.Nonempty) :
    (negativeHalfFamilyNat A).card = 2 ^ (A.card - 1) := by
  have hNotFilterEq :
      {S ∈ A.powerset | ¬ 2 * S.sum id < A.sum id} = positiveHalfFamilyNat A := by
    ext S
    by_cases hS : S ∈ A.powerset
    · have hSA : S ⊆ A := Finset.mem_powerset.mp hS
      have hneq : 2 * S.sum id ≠ A.sum id :=
        two_mul_sum_ne_total_of_isSumDistinct h hA hSA
      constructor
      · intro hMem
        have hnotlt : ¬ 2 * S.sum id < A.sum id := by
          simpa [hS] using (Finset.mem_filter.mp hMem).2
        refine mem_positiveHalfFamilyNat.mpr ⟨hSA, ?_⟩
        omega
      · intro hMem
        have hlt : A.sum id < 2 * S.sum id := (mem_positiveHalfFamilyNat.mp hMem).2
        exact Finset.mem_filter.mpr ⟨hS, by omega⟩
    · simp [positiveHalfFamilyNat, hS]
  have hsplit :
      (negativeHalfFamilyNat A).card + (positiveHalfFamilyNat A).card = A.powerset.card := by
    rw [negativeHalfFamilyNat, ← hNotFilterEq]
    exact Finset.card_filter_add_card_filter_not (s := A.powerset)
      (p := fun S : Finset ℕ => 2 * S.sum id < A.sum id)
  have hEqCards :
      (negativeHalfFamilyNat A).card = (positiveHalfFamilyNat A).card :=
    negativeHalfFamilyNat_card_eq_positiveHalfFamilyNat_card A
  have hdouble : (negativeHalfFamilyNat A).card + (negativeHalfFamilyNat A).card = 2 ^ A.card := by
    simpa [hEqCards, Finset.card_powerset] using hsplit
  have hcard_ne : A.card ≠ 0 := by
    exact Finset.card_ne_zero.mpr hA
  rcases Nat.exists_eq_succ_of_ne_zero hcard_ne with ⟨m, hm⟩
  have hpow : 2 ^ A.card = (2 : ℕ) * 2 ^ m := by
    rw [hm, pow_succ]
    ring
  have hfinal : (negativeHalfFamilyNat A).card = 2 ^ m := by
    rw [hpow, two_mul] at hdouble
    omega
  simpa [hm] using hfinal

/--
Every subset in the positive boundary has sum in an interval of exactly `N` consecutive integers:
`(A.sum / 2, A.sum / 2 + N]`.
-/
theorem sum_mem_Icc_of_mem_positiveBoundaryFamilyNat {A S : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : S ∈ positiveBoundaryFamilyNat A) :
    S.sum id ∈ Finset.Icc (A.sum id / 2 + 1) (A.sum id / 2 + N) := by
  rcases (mem_positiveBoundaryFamilyNat.mp hS) with ⟨hSA, hgt, a, haS, herase⟩
  have haN : a ≤ N := (Finset.mem_Icc.mp (hA (hSA haS))).2
  have hsumErase : S.sum id = (S.erase a).sum id + a := by
    simpa [add_comm] using (S.sum_erase_add (f := id) haS).symm
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · omega
  · omega

/--
The positive boundary injects into an interval of length `N`, so its cardinality is at most `N`.
This is the constructive counting half of the exact Dubroff-Fox-Xu lower bound.
-/
theorem positiveBoundaryFamilyNat_card_le {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) : (positiveBoundaryFamilyNat A).card ≤ N := by
  have hInjOn : Set.InjOn (fun S : Finset ℕ => S.sum id) (positiveBoundaryFamilyNat A) := by
    intro S hS T hT hsum
    exact sum_injOn_powerset h (Finset.mem_powerset.mpr (mem_positiveBoundaryFamilyNat.mp hS).1)
      (Finset.mem_powerset.mpr (mem_positiveBoundaryFamilyNat.mp hT).1) hsum
  have hImg :
      (positiveBoundaryFamilyNat A).image (fun S : Finset ℕ => S.sum id) ⊆
        Finset.Icc (A.sum id / 2 + 1) (A.sum id / 2 + N) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
    exact sum_mem_Icc_of_mem_positiveBoundaryFamilyNat h.1 hS
  calc
    (positiveBoundaryFamilyNat A).card
      = ((positiveBoundaryFamilyNat A).image fun S : Finset ℕ => S.sum id).card := by
          symm
          exact Finset.card_image_of_injOn hInjOn
    _ ≤ (Finset.Icc (A.sum id / 2 + 1) (A.sum id / 2 + N)).card := Finset.card_le_card hImg
    _ = N := by simp [Nat.card_Icc]

/--
If one proves the Harper-style lower bound
`choose(|A|, floor(|A|/2)) <= |positiveBoundaryFamilyNat A|`,
then the exact Dubroff-Fox-Xu lower theorem follows immediately.
-/
theorem choose_middle_le_of_boundary_lower {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N)
    (hBoundary : Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card) :
    Nat.choose A.card (A.card / 2) ≤ N :=
  hBoundary.trans (positiveBoundaryFamilyNat_card_le h)

/--
Non-core frontier input: the missing Harper-style lower bound on the size of the positive boundary
family attached to a sum-distinct set.
-/
axiom positiveBoundaryMiddleLower_frontier :
  ∀ ⦃N : ℕ⦄ ⦃A : Finset ℕ⦄, IsSumDistinctSet A N → A.Nonempty →
    Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card

/--
Public theorem surface for the positive-boundary middle lower bound.
It is currently routed through the non-core frontier input above.
-/
theorem PositiveBoundaryMiddleLower :
    ∀ ⦃N : ℕ⦄ ⦃A : Finset ℕ⦄, IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ (positiveBoundaryFamilyNat A).card :=
  positiveBoundaryMiddleLower_frontier

/--
Once `PositiveBoundaryMiddleLower` is available, the exact Dubroff-Fox-Xu integer lower theorem
follows from the already formalized interval-counting argument for nonempty `A`.
-/
theorem erdos_1_lower_bound_exact_of_positiveBoundaryMiddleLower
    :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N := by
  intro N A hA hAne
  exact choose_middle_le_of_boundary_lower hA (PositiveBoundaryMiddleLower hA hAne)

end Erdos1
