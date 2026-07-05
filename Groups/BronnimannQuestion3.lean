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
  ∃ (α : Type) (_ : Primcodable α) (rels : Set (FreeGroup α))
    (β : Type) (_ : Fintype β) (letterValue : β → PresentedGroup rels),
      SolvableWordProblem rels ∧ HasIrrationalGeodesicGrowth rels letterValue

/-- Any concrete witness with solvable word problem and irrational geodesic growth yields a
positive answer to Brönnimann's Question 3. This theorem is fully local and depends only on the
core axioms. -/
theorem positive_answer_of_witness
    {α : Type} [Primcodable α] {rels : Set (FreeGroup α)}
    {β : Type} [Fintype β] {letterValue : β → PresentedGroup rels}
    (hWord : SolvableWordProblem rels)
    (hIrr : HasIrrationalGeodesicGrowth rels letterValue) :
    PositiveAnswer := by
  exact ⟨α, inferInstance, rels, β, inferInstance, letterValue, hWord, hIrr⟩

end BronnimannQuestion3
