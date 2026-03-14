import ErdosProblems.Problem1

namespace Erdos1

/--
OEIS A276661 example witness for `a(9) = 161`.

The exact optimality statement `least_N_9` remains separate; this file only records the explicit
existence witness.
-/
def oeisWitness_9_161 : Finset ℕ := {77, 117, 137, 148, 154, 157, 159, 160, 161}

/--
OEIS A276661 example witness for `a(10) = 309`.

As above, this is an existence witness, not an optimality proof.
-/
def oeisWitness_10_309 : Finset ℕ := {148, 225, 265, 285, 296, 302, 305, 307, 308, 309}

/-- The OEIS witness at `(n, N) = (9, 161)` is sum-distinct. -/
theorem isSumDistinctSet_oeisWitness_9_161 :
    IsSumDistinctSet oeisWitness_9_161 161 := by
  native_decide

/-- The OEIS witness at `(n, N) = (10, 309)` is sum-distinct. -/
theorem isSumDistinctSet_oeisWitness_10_309 :
    IsSumDistinctSet oeisWitness_10_309 309 := by
  native_decide

/-- Explicit certified existence of a 9-element sum-distinct set in `{1, ..., 161}`. -/
theorem hasSumDistinctSetCard_nine_161 : HasSumDistinctSetCard 161 9 := by
  refine ⟨oeisWitness_9_161, isSumDistinctSet_oeisWitness_9_161, ?_⟩
  native_decide

/-- Explicit certified existence of a 10-element sum-distinct set in `{1, ..., 309}`. -/
theorem hasSumDistinctSetCard_ten_309 : HasSumDistinctSetCard 309 10 := by
  refine ⟨oeisWitness_10_309, isSumDistinctSet_oeisWitness_10_309, ?_⟩
  native_decide

/-- Public exact-value upper witness at the OEIS ambient size for `n = 9`. -/
theorem erdos_1.variants.exists_N_9 : ∃ A, IsSumDistinctSet A 161 ∧ A.card = 9 :=
  hasSumDistinctSetCard_nine_161

/-- Public exact-value upper witness at the OEIS ambient size for `n = 10`. -/
theorem erdos_1.variants.exists_N_10 : ∃ A, IsSumDistinctSet A 309 ∧ A.card = 10 :=
  hasSumDistinctSetCard_ten_309

end Erdos1
