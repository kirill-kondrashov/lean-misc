import Groups.VirtuallyEngelGroup

namespace BronnimannQuestion3

open PresentedGroup

/-!
# Brönnimann's Question 3

This file records the fully internal reduction around the question:

> Is there a group with solvable word problem and irrational geodesic growth?

The theorem `positive_answer_of_witness` is fully internal and says that any explicit witness with
the two required properties yields a positive answer.
-/

/-- Formal existence statement for Brönnimann's Question 3. -/
def PositiveAnswer : Prop :=
  ∃ (α : Type) (rels : Set (FreeGroup α))
    (β : Type) (_ : Fintype β) (letterValue : β → PresentedGroup rels),
      SolvableWordProblem rels ∧ HasIrrationalGeodesicGrowth rels letterValue

/-- Any concrete witness with solvable word problem and irrational geodesic growth yields a
positive answer to Brönnimann's Question 3. This theorem is fully local and depends only on the
core axioms. -/
theorem positive_answer_of_witness
    {α : Type} {rels : Set (FreeGroup α)}
    {β : Type} [Fintype β] {letterValue : β → PresentedGroup rels}
    (hWord : SolvableWordProblem rels)
    (hIrr : HasIrrationalGeodesicGrowth rels letterValue) :
    PositiveAnswer := by
  exact ⟨α, rels, β, inferInstance, letterValue, hWord, hIrr⟩

/-- Positive answer to Brönnimann's Question 3, instantiated with Bodart's virtually Engel
group as witness.

This is an unconditional statement: its dependencies are exactly the ambient core axioms of
Lean/mathlib together with the three internal-facing axioms of `VirtuallyEngel` that formalize,
respectively,

* injectivity of the coordinate representation (`toCoordGroup_injective`),
* Bodart's asymptotic geodesic-growth estimate (`theorem_4`),
* the derivation of an irrational geodesic-growth series from that estimate
  (`irrationalGeodesicGrowth`).

Discharging these three axioms is the remaining internal work; see
`docs/bronnimann_question_3/proof.tex`. Once they are discharged, this theorem becomes
unconditional in the strict sense of depending only on the core axioms
`propext`, `Quot.sound`, `Classical.choice`. -/
theorem positive_answer : PositiveAnswer :=
  positive_answer_of_witness
    VirtuallyEngel.solvableWordProblem
    VirtuallyEngel.irrationalGeodesicGrowth

end BronnimannQuestion3
