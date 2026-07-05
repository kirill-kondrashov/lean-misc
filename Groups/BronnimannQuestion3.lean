import Groups.VirtuallyEngelGroup

namespace BronnimannQuestion3

open PresentedGroup

/-!
# Brönnimann's Question 3

This file records a positive answer to the question:

> Is there a group with solvable word problem and irrational geodesic growth?

The witness is Bodart's virtually Engel group.
-/

/-- Formal existence statement for Brönnimann's Question 3. -/
def PositiveAnswer : Prop :=
  ∃ (α : Type) (_ : Primcodable α) (rels : Set (FreeGroup α))
    (β : Type) (_ : Fintype β) (letterValue : β → PresentedGroup rels),
      SolvableWordProblem rels ∧ HasIrrationalGeodesicGrowth rels letterValue

/-- Bodart's virtually Engel example gives a positive answer to Brönnimann's Question 3. -/
theorem positive_answer : PositiveAnswer := by
  refine ⟨VirtuallyEngel.Generator, inferInstance, VirtuallyEngel.relators,
    VirtuallyEngel.Letter, inferInstance, VirtuallyEngel.letterValue, ?_⟩
  exact ⟨VirtuallyEngel.solvableWordProblem, VirtuallyEngel.irrationalGeodesicGrowth⟩

end BronnimannQuestion3
