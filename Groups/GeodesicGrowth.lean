import Mathlib

universe u v

namespace PresentedGroup

/-- The element of a presented group represented by a finite word in generators and formal
inverses. -/
abbrev evalWord {α : Type u} (rels : Set (FreeGroup α)) (w : List (α × Bool)) :
    PresentedGroup rels :=
  mk rels (FreeGroup.mk w)

/-- A presentation has solvable word problem when equality of represented finite words is
decidable. This is the classical textbook definition: a decision procedure exists in principle
(any decidable predicate on a countable type is Turing-computable via its indicator function). -/
def SolvableWordProblem {α : Type u} (rels : Set (FreeGroup α)) : Prop :=
  Nonempty (DecidablePred fun p : List (α × Bool) × List (α × Bool) =>
    evalWord rels p.1 = evalWord rels p.2)

/-- A length-`n` word over the finite alphabet `β`, encoded as a tuple of letters. -/
abbrev WordTuple (β : Type v) (n : ℕ) : Type v :=
  Fin n → β

/-- Evaluate a finite word in an arbitrary alphabet whose letters already have values in the
presented group. -/
def evalWordOver {α : Type u} {β : Type v} (rels : Set (FreeGroup α))
    (letterValue : β → PresentedGroup rels) (w : List β) : PresentedGroup rels :=
  w.foldl (fun g a => g * letterValue a) 1

/-- A finite word in the alphabet `β` is geodesic when no shorter word over the same alphabet
represents the same element of the presented group. -/
def IsGeodesicWordOver {α : Type u} {β : Type v} (rels : Set (FreeGroup α))
    (letterValue : β → PresentedGroup rels) (w : List β) : Prop :=
  ∀ v, evalWordOver rels letterValue v = evalWordOver rels letterValue w → w.length ≤ v.length

/-- A tuple word is geodesic when its underlying finite word is geodesic. -/
def IsGeodesicTupleWordOver {α : Type u} {β : Type v} (rels : Set (FreeGroup α))
    (letterValue : β → PresentedGroup rels) {n : ℕ} (w : WordTuple β n) : Prop :=
  IsGeodesicWordOver rels letterValue (List.ofFn w)

/-- The geodesic growth function of a presented group with respect to a finite alphabet `β`
mapping into the group. -/
noncomputable abbrev geodesicGrowth {α : Type u} {β : Type v} [Fintype β]
    (rels : Set (FreeGroup α)) (letterValue : β → PresentedGroup rels) (n : ℕ) : ℕ :=
  Nat.card {w : WordTuple β n // IsGeodesicTupleWordOver rels letterValue w}

/-- A coarse polynomial upper bound for geodesic growth. -/
def HasPolynomialGeodesicGrowth {α : Type u} {β : Type v} [Fintype β]
    (rels : Set (FreeGroup α)) (letterValue : β → PresentedGroup rels) : Prop :=
  ∃ C d : ℕ, ∀ n, geodesicGrowth rels letterValue n ≤ C * (n + 1) ^ d

/-- An integer sequence satisfies an eventual linear recurrence with constant coefficients. -/
def SatisfiesLinearRecurrence (f : ℕ → ℤ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ coeffs : Fin d → ℤ, ∀ᶠ n : ℕ in Filter.atTop,
    f (n + d) = ∑ i : Fin d, coeffs i * f (n + i)

/-- A geodesic-growth sequence is rational when it satisfies an eventual linear recurrence with
constant coefficients. -/
def HasRationalGeodesicGrowth {α : Type u} {β : Type v} [Fintype β]
    (rels : Set (FreeGroup α)) (letterValue : β → PresentedGroup rels) : Prop :=
  SatisfiesLinearRecurrence fun n => (geodesicGrowth rels letterValue n : ℤ)

/-- Irrational geodesic growth means failure of the eventual-linear-recurrence criterion for a
rational generating function. -/
def HasIrrationalGeodesicGrowth {α : Type u} {β : Type v} [Fintype β]
    (rels : Set (FreeGroup α)) (letterValue : β → PresentedGroup rels) : Prop :=
  ¬HasRationalGeodesicGrowth rels letterValue

end PresentedGroup

/-- A finite word is geodesic for the presentation with relators `rels` if no shorter finite word
represents the same element of the presented group. A letter is represented by `(a, true)`, and
the formal inverse letter by `(a, false)`. -/
def IsGeodesicWord {α : Type u} (rels : Set (FreeGroup α)) (w : List (α × Bool)) : Prop :=
  ∀ v, PresentedGroup.evalWord rels v = PresentedGroup.evalWord rels w → w.length ≤ v.length
