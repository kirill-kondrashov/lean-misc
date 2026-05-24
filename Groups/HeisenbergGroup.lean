import Mathlib

namespace PresentedGroup

/-- The element of a presented group represented by a finite word. -/
abbrev evalWord {α : Type*} (rels : Set (FreeGroup α)) (w : List (α × Bool)) :
    PresentedGroup rels :=
  mk rels (FreeGroup.mk w)

end PresentedGroup

/-- A finite word is geodesic for the presentation with relators `rels` if no shorter finite word
represents the same element of the presented group. A letter is represented by `(a, true)`, and the
formal inverse letter by `(a, false)`. -/
def IsGeodesicWord {α : Type*} (rels : Set (FreeGroup α)) (w : List (α × Bool)) : Prop :=
  ∀ v, PresentedGroup.evalWord rels v = PresentedGroup.evalWord rels w → w.length ≤ v.length

namespace Heisenberg

/-!
# The discrete Heisenberg group

Discrete Heisenberg group by the two-generator presentation
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`.
-/

/-- The two generators in the standard presentation of the discrete Heisenberg group. -/
inductive Generator where
  | x
  | y
  deriving DecidableEq

/-- The free-group word corresponding to the generator `x`. -/
abbrev X : FreeGroup Generator :=
  FreeGroup.of Generator.x

/-- The free-group word corresponding to the generator `y`. -/
abbrev Y : FreeGroup Generator :=
  FreeGroup.of Generator.y

/-- The relators `[[x, y], x]` and `[[x, y], y]` for the standard presentation. -/
abbrev relators : Set (FreeGroup Generator) :=
  {⁅⁅X, Y⁆, X⁆, ⁅⁅X, Y⁆, Y⁆}

/-- The discrete Heisenberg group, presented as
`⟨x, y | [[x, y], x] = 1, [[x, y], y] = 1⟩`. -/
abbrev Group : Type :=
  PresentedGroup relators

/-- Geodesic finite words for the standard presentation of the discrete Heisenberg group. -/
abbrev IsGeodesic (w : List (Generator × Bool)) : Prop :=
  IsGeodesicWord relators w

/-- A letter in the alphabet `{x, y, x⁻¹, y⁻¹}`.  The boolean records whether the generator
is used positively. -/
abbrev Letter : Type :=
  Generator × Bool

/-- A finite word over the alphabet `{x, y, x⁻¹, y⁻¹}`. -/
abbrev Word : Type :=
  List Letter

/-- A one-sided infinite word over the alphabet `{x, y, x⁻¹, y⁻¹}`. -/
abbrev InfiniteWord : Type :=
  ℕ → Letter

/-- The formal inverse of a letter. -/
def inverseLetter : Letter → Letter
  | (g, positive) => (g, !positive)

/-- A block containing `n` copies of a letter. -/
def letterPow (a : Letter) (n : ℕ) : Word :=
  List.replicate n a

/-- The finite subword of length `len` starting at position `start` in a one-sided infinite word. -/
def segment (w : InfiniteWord) (start len : ℕ) : Word :=
  (List.range len).map fun i => w (start + i)

/-- A one-sided infinite word obtained by appending an infinite constant tail to a finite prefix. -/
def finiteThenConstant (pref : Word) (tail : Letter) : InfiniteWord :=
  fun n => if h : n < pref.length then pref.get ⟨n, h⟩ else tail

/-- A one-sided infinite word is geodesic when each finite subword is geodesic. -/
def IsInfiniteGeodesic (w : InfiniteWord) : Prop :=
  ∀ start len, IsGeodesic (segment w start len)

/-- Two letters are not a mutually inverse pair. -/
def NotMutuallyInverse (a b : Letter) : Prop :=
  inverseLetter a ≠ b ∧ inverseLetter b ≠ a

/-- A finite word uses only letters from a given set. -/
def UsesOnly (allowed : Set Letter) (w : Word) : Prop :=
  ∀ a ∈ w, a ∈ allowed

/-- One adjacent transposition in a finite word. -/
def AdjacentSwap (u v : Word) : Prop :=
  ∃ pref a b suffix,
    u = pref ++ a :: b :: suffix ∧
    v = pref ++ b :: a :: suffix

/-- Reachability by exactly `n` adjacent transpositions. -/
inductive AdjacentSwapReach : ℕ → Word → Word → Prop
  | zero (w : Word) : AdjacentSwapReach 0 w w
  | succ {n : ℕ} {u v z : Word} :
      AdjacentSwap u v → AdjacentSwapReach n v z → AdjacentSwapReach (n + 1) u z

/-- `V` can be brought to a block `aⁱbʲ` using fewer than `m` adjacent transpositions. -/
def ReducesToBlockInLessThan (a b : Letter) (m : ℕ) (V : Word) : Prop :=
  ∃ swaps < m, ∃ i j, AdjacentSwapReach swaps V (letterPow a i ++ letterPow b j)

/-- Class A from Theorem 1.1 of Vershik--Malyutin: infinite words containing no mutually
inverse letters. -/
def ClassA (w : InfiniteWord) : Prop :=
  ∀ i j, w j ≠ inverseLetter (w i)

/-- The first normal form in class B from Theorem 1.1:
`V a b^m a⁻¹ b^{+∞}`. -/
def ClassBFirstForm (w : InfiniteWord) : Prop :=
  ∃ a b V m,
    NotMutuallyInverse a b ∧
    0 < m ∧
    UsesOnly {a, b} V ∧
    ReducesToBlockInLessThan a b m V ∧
    w = finiteThenConstant (V ++ [a] ++ letterPow b m ++ [inverseLetter a]) b

/-- The second normal form in class B from Theorem 1.1:
`a^n b⁻¹ a^m b V b^{+∞}`. -/
def ClassBSecondForm (w : InfiniteWord) : Prop :=
  ∃ a b V n m,
    NotMutuallyInverse a b ∧
    0 < m ∧
    UsesOnly {a, b} V ∧
    ReducesToBlockInLessThan a b m V ∧
    w = finiteThenConstant
      (letterPow a n ++ [inverseLetter b] ++ letterPow a m ++ [b] ++ V) b

/-- Class B from Theorem 1.1 of Vershik--Malyutin. -/
def ClassB (w : InfiniteWord) : Prop :=
  ClassBFirstForm w ∨ ClassBSecondForm w

/-- The formal statement of Theorem 1.1 in
Vershik--Malyutin, "Infinite geodesics in the discrete Heisenberg group", Zapiski Nauchnykh
Seminarov POMI 462 (2017), for the standard presentation of the discrete Heisenberg group. -/
def theorem_1_1_statement : Prop :=
  ∀ w : InfiniteWord, IsInfiniteGeodesic w ↔ ClassA w ∨ ClassB w

/-- Theorem 1.1 of Vershik--Malyutin, imported as a literature axiom.

It classifies one-sided infinite geodesic words in the standard generators of the discrete
Heisenberg group as the union of class A and class B. -/
axiom theorem_1_1 : theorem_1_1_statement

end Heisenberg
