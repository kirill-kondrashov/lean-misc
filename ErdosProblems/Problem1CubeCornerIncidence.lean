import ErdosProblems.Problem1CubeRepairLocality
import ErdosProblems.Problem1CubeShiftedInstantiation

open Finset
open scoped Finset

namespace Erdos1

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Concrete repair-pair type for cube families. -/
abbrev CubeRepairPair (α : Type*) := Finset α × Finset α

/-- Positive-boundary atoms created by a concrete repair pair. -/
def repairNewBoundaryAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) : Finset (Finset α) :=
  positiveBoundary (familyRepair F k.1 k.2) \ positiveBoundary F

/-- Positive-boundary atoms removed by a concrete repair pair. -/
def repairOldBoundaryAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) : Finset (Finset α) :=
  positiveBoundary F \ positiveBoundary (familyRepair F k.1 k.2)

/-- Family atoms created by a concrete repair pair. -/
def repairNewFamilyAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) : Finset (Finset α) :=
  familyRepair F k.1 k.2 \ F

/-- Family atoms removed by a concrete repair pair. -/
def repairOldFamilyAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) : Finset (Finset α) :=
  F \ familyRepair F k.1 k.2

/-- The local neighborhood controlling all bad/good atoms of a repair pair. -/
def repairLocalNeighborhood (k : CubeRepairPair α) : Finset (Finset α) :=
  (positiveBoundary ({k.1} : Finset (Finset α)) ∪ ({k.2} : Finset (Finset α))) ∪
    (positiveBoundary ({k.2} : Finset (Finset α)) ∪ ({k.1} : Finset (Finset α)))

/-- Tagged bad atoms for one repair pair: new boundary atoms or deleted family atoms. -/
def repairBadAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (Sum (Finset α) (Finset α)) :=
  (repairNewBoundaryAtoms F k).map Function.Embedding.inl ∪
    (repairOldFamilyAtoms F k).map Function.Embedding.inr

/-- Tagged good atoms for one repair pair: old boundary atoms or inserted family atoms. -/
def repairGoodAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (Sum (Finset α) (Finset α)) :=
  (repairOldBoundaryAtoms F k).map Function.Embedding.inl ∪
    (repairNewFamilyAtoms F k).map Function.Embedding.inr

/-- Forget the bad/good tag and keep only the underlying cube atom. -/
def atomOfTaggedAtom : Sum (Finset α) (Finset α) → Finset α :=
  Sum.elim id id

/-- Canonical local role of an atom relative to a repair corner. -/
inductive CornerRole
  | newBoundary
  | oldBoundary
  | newFamily
  | oldFamily
  deriving DecidableEq, Fintype

/-- Atom set attached to one canonical local role of a repair corner. -/
def repairRoleAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) : CornerRole → Finset (Finset α)
  | CornerRole.newBoundary => repairNewBoundaryAtoms F k
  | CornerRole.oldBoundary => repairOldBoundaryAtoms F k
  | CornerRole.newFamily => repairNewFamilyAtoms F k
  | CornerRole.oldFamily => repairOldFamilyAtoms F k

/-- Structured local atoms of a repair corner, refined by their canonical role. -/
def repairStructuredAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (CornerRole × Finset α) :=
  ({CornerRole.newBoundary} : Finset CornerRole).product (repairNewBoundaryAtoms F k) ∪
    ({CornerRole.oldBoundary} : Finset CornerRole).product (repairOldBoundaryAtoms F k) ∪
      ({CornerRole.newFamily} : Finset CornerRole).product (repairNewFamilyAtoms F k) ∪
        ({CornerRole.oldFamily} : Finset CornerRole).product (repairOldFamilyAtoms F k)

/-- Forget the role tag and keep only the underlying cube atom. -/
def atomOfCornerRoleAtom : CornerRole × Finset α → Finset α :=
  Prod.snd

theorem mem_repairStructuredAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : CornerRole × Finset α} :
    u ∈ repairStructuredAtoms F k ↔
      (u.1 = CornerRole.newBoundary ∧ u.2 ∈ repairNewBoundaryAtoms F k) ∨
        (u.1 = CornerRole.oldBoundary ∧ u.2 ∈ repairOldBoundaryAtoms F k) ∨
          (u.1 = CornerRole.newFamily ∧ u.2 ∈ repairNewFamilyAtoms F k) ∨
            (u.1 = CornerRole.oldFamily ∧ u.2 ∈ repairOldFamilyAtoms F k) := by
  rcases u with ⟨r, s⟩
  cases r <;>
    simp [repairStructuredAtoms, Finset.mem_union, Finset.mem_product, and_left_comm, and_assoc]

theorem repairNewFamilyAtoms_subset_singleton (F : Finset (Finset α)) (k : CubeRepairPair α) :
    repairNewFamilyAtoms F k ⊆ ({k.1} : Finset (Finset α)) := by
  intro s hs
  rw [mem_singleton]
  exact mem_sdiff_of_twoAtomRepair hs

theorem repairOldFamilyAtoms_subset_singleton (F : Finset (Finset α)) (k : CubeRepairPair α) :
    repairOldFamilyAtoms F k ⊆ ({k.2} : Finset (Finset α)) := by
  intro s hs
  rw [mem_singleton]
  exact mem_sdiff_twoAtomRepair hs

theorem repairNewBoundaryAtoms_subset_localLeft (F : Finset (Finset α)) (k : CubeRepairPair α) :
    repairNewBoundaryAtoms F k ⊆
      positiveBoundary ({k.1} : Finset (Finset α)) ∪ ({k.2} : Finset (Finset α)) := by
  simpa [repairNewBoundaryAtoms] using
    sdiff_positiveBoundary_twoAtomRepair_subset_local (F := F) (x := k.1) (z := k.2)

theorem repairOldBoundaryAtoms_subset_localRight (F : Finset (Finset α)) (k : CubeRepairPair α) :
    repairOldBoundaryAtoms F k ⊆
      positiveBoundary ({k.2} : Finset (Finset α)) ∪ ({k.1} : Finset (Finset α)) := by
  simpa [repairOldBoundaryAtoms] using
    sdiff_positiveBoundary_of_twoAtomRepair_subset_local (F := F) (x := k.1) (z := k.2)

theorem atomOfTaggedAtom_mem_repairBadAtoms_local {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairBadAtoms F k) :
    atomOfTaggedAtom u ∈ repairLocalNeighborhood k := by
  simp only [repairBadAtoms, repairLocalNeighborhood] at hu ⊢
  rw [mem_union] at hu ⊢
  rcases hu with hu | hu
  · rcases mem_map.mp hu with ⟨s, hs, rfl⟩
    exact Or.inl (repairNewBoundaryAtoms_subset_localLeft F k hs)
  · rcases mem_map.mp hu with ⟨s, hs, rfl⟩
    exact Or.inl (Finset.mem_union.mpr (Or.inr (repairOldFamilyAtoms_subset_singleton F k hs)))

theorem atomOfTaggedAtom_mem_repairGoodAtoms_local {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairGoodAtoms F k) :
    atomOfTaggedAtom u ∈ repairLocalNeighborhood k := by
  simp only [repairGoodAtoms, repairLocalNeighborhood] at hu ⊢
  rw [mem_union] at hu ⊢
  rcases hu with hu | hu
  · rcases mem_map.mp hu with ⟨s, hs, rfl⟩
    exact Or.inr (repairOldBoundaryAtoms_subset_localRight F k hs)
  · rcases mem_map.mp hu with ⟨s, hs, rfl⟩
    exact by
      simpa [repairLocalNeighborhood, atomOfTaggedAtom] using
        (Or.inr (Finset.mem_union.mpr (Or.inr (by
          rw [mem_singleton]
          exact mem_sdiff_of_twoAtomRepair hs))) :
          s ∈ positiveBoundary ({k.1} : Finset (Finset α)) ∪ ({k.2} : Finset (Finset α)) ∨
            s ∈ positiveBoundary ({k.2} : Finset (Finset α)) ∪ ({k.1} : Finset (Finset α)))

theorem atomOfCornerRoleAtom_mem_repairStructuredAtoms_local {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : CornerRole × Finset α} (hu : u ∈ repairStructuredAtoms F k) :
    atomOfCornerRoleAtom u ∈ repairLocalNeighborhood k := by
  rw [mem_repairStructuredAtoms_iff] at hu
  rcases u with ⟨r, s⟩
  rcases hu with ⟨hr, hs⟩ | hu
  · subst hr
    have hu' : Sum.inl s ∈ repairBadAtoms F k := by
      simpa [repairBadAtoms] using hs
    simpa [atomOfCornerRoleAtom, atomOfTaggedAtom] using
      (atomOfTaggedAtom_mem_repairBadAtoms_local (k := k) (u := Sum.inl s) hu')
  · rcases hu with ⟨hr, hs⟩ | hu
    · subst hr
      have hu' : Sum.inl s ∈ repairGoodAtoms F k := by
        simpa [repairGoodAtoms] using hs
      simpa [atomOfCornerRoleAtom, atomOfTaggedAtom] using
        (atomOfTaggedAtom_mem_repairGoodAtoms_local (k := k) (u := Sum.inl s) hu')
    · rcases hu with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · subst hr
        have hu' : Sum.inr s ∈ repairGoodAtoms F k := by
          simpa [repairGoodAtoms] using hs
        simpa [atomOfCornerRoleAtom, atomOfTaggedAtom] using
          (atomOfTaggedAtom_mem_repairGoodAtoms_local (k := k) (u := Sum.inr s) hu')
      · subst hr
        have hu' : Sum.inr s ∈ repairBadAtoms F k := by
          simpa [repairBadAtoms] using hs
        simpa [atomOfCornerRoleAtom, atomOfTaggedAtom] using
          (atomOfTaggedAtom_mem_repairBadAtoms_local (k := k) (u := Sum.inr s) hu')

/-- Structured incidence set for a finite repair family. -/
def repairStructuredIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × (CornerRole × Finset α)) :=
  K.biUnion fun k => ({k} : Finset (CubeRepairPair α)).product (repairStructuredAtoms F k)

/-- Canonical refinement of a bad tagged atom to a structured local role. -/
def refineBadTaggedAtom : Sum (Finset α) (Finset α) → CornerRole × Finset α
  | Sum.inl s => (CornerRole.newBoundary, s)
  | Sum.inr s => (CornerRole.oldFamily, s)

/-- Canonical refinement of a good tagged atom to a structured local role. -/
def refineGoodTaggedAtom : Sum (Finset α) (Finset α) → CornerRole × Finset α
  | Sum.inl s => (CornerRole.oldBoundary, s)
  | Sum.inr s => (CornerRole.newFamily, s)

/-- Canonical refinement of a bad incidence to a structured incidence. -/
def refineBadIncidence (p : CubeRepairPair α × Sum (Finset α) (Finset α)) :
    CubeRepairPair α × (CornerRole × Finset α) :=
  (p.1, refineBadTaggedAtom p.2)

/-- Canonical refinement of a good incidence to a structured incidence. -/
def refineGoodIncidence (p : CubeRepairPair α × Sum (Finset α) (Finset α)) :
    CubeRepairPair α × (CornerRole × Finset α) :=
  (p.1, refineGoodTaggedAtom p.2)

theorem refineBadTaggedAtom_mem_repairStructuredAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairBadAtoms F k) :
    refineBadTaggedAtom u ∈ repairStructuredAtoms F k := by
  cases u with
  | inl s =>
      have hs : s ∈ repairNewBoundaryAtoms F k := by
        simpa [repairBadAtoms] using hu
      exact (mem_repairStructuredAtoms_iff (u := (CornerRole.newBoundary, s))).2 (Or.inl ⟨rfl, hs⟩)
  | inr s =>
      have hs : s ∈ repairOldFamilyAtoms F k := by
        simpa [repairBadAtoms] using hu
      exact (mem_repairStructuredAtoms_iff (u := (CornerRole.oldFamily, s))).2
        (Or.inr (Or.inr (Or.inr ⟨rfl, hs⟩)))

theorem refineGoodTaggedAtom_mem_repairStructuredAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairGoodAtoms F k) :
    refineGoodTaggedAtom u ∈ repairStructuredAtoms F k := by
  cases u with
  | inl s =>
      have hs : s ∈ repairOldBoundaryAtoms F k := by
        simpa [repairGoodAtoms] using hu
      exact (mem_repairStructuredAtoms_iff (u := (CornerRole.oldBoundary, s))).2
        (Or.inr (Or.inl ⟨rfl, hs⟩))
  | inr s =>
      have hs : s ∈ repairNewFamilyAtoms F k := by
        simpa [repairGoodAtoms] using hu
      exact (mem_repairStructuredAtoms_iff (u := (CornerRole.newFamily, s))).2
        (Or.inr (Or.inr (Or.inl ⟨rfl, hs⟩)))

/-- Bad incidence set for a finite repair family. -/
def repairBadIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × Sum (Finset α) (Finset α)) :=
  K.biUnion fun k => ({k} : Finset (CubeRepairPair α)).product (repairBadAtoms F k)

/-- Good incidence set for a finite repair family. -/
def repairGoodIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × Sum (Finset α) (Finset α)) :=
  K.biUnion fun k => ({k} : Finset (CubeRepairPair α)).product (repairGoodAtoms F k)

theorem atomOfTaggedAtom_mem_repairBadIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairBadIncidences F K) :
    atomOfTaggedAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  rcases p with ⟨pk, pu⟩
  unfold repairBadIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' : pk ∈ ({k} : Finset (CubeRepairPair α)) ∧ pu ∈ repairBadAtoms F k := by
    have hp'' : pu ∈ repairBadAtoms F k ∧ k = pk := by
      have hp''' : pu ∈ repairBadAtoms F k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact hp'''
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfTaggedAtom_mem_repairBadAtoms_local hp'.2

theorem atomOfTaggedAtom_mem_repairGoodIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairGoodIncidences F K) :
    atomOfTaggedAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  rcases p with ⟨pk, pu⟩
  unfold repairGoodIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' : pk ∈ ({k} : Finset (CubeRepairPair α)) ∧ pu ∈ repairGoodAtoms F k := by
    have hp'' : pu ∈ repairGoodAtoms F k ∧ k = pk := by
      have hp''' : pu ∈ repairGoodAtoms F k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact hp'''
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfTaggedAtom_mem_repairGoodAtoms_local hp'.2

theorem atomOfCornerRoleAtom_mem_repairStructuredIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × (CornerRole × Finset α)} (hp : p ∈ repairStructuredIncidences F K) :
    atomOfCornerRoleAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  rcases p with ⟨pk, pu⟩
  unfold repairStructuredIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' : pk ∈ ({k} : Finset (CubeRepairPair α)) ∧ pu ∈ repairStructuredAtoms F k := by
    have hp'' : pu ∈ repairStructuredAtoms F k ∧ k = pk := by
      have hp''' : pu ∈ repairStructuredAtoms F k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact hp'''
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfCornerRoleAtom_mem_repairStructuredAtoms_local hp'.2

theorem refineBadIncidence_mem_repairStructuredIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairBadIncidences F K) :
    refineBadIncidence p ∈ repairStructuredIncidences F K := by
  rcases p with ⟨pk, pu⟩
  unfold repairBadIncidences at hp
  unfold repairStructuredIncidences
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' : pk ∈ ({k} : Finset (CubeRepairPair α)) ∧ pu ∈ repairBadAtoms F k := by
    have hp'' : pu ∈ repairBadAtoms F k ∧ k = pk := by
      have hp''' : pu ∈ repairBadAtoms F k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact hp'''
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  refine mem_biUnion.mpr ⟨pk, hk, ?_⟩
  have hmem : refineBadTaggedAtom pu ∈ repairStructuredAtoms F pk :=
    refineBadTaggedAtom_mem_repairStructuredAtoms hp'.2
  have hpair : refineBadTaggedAtom pu ∈ repairStructuredAtoms F pk ∧ pk = pk := ⟨hmem, rfl⟩
  simpa [refineBadIncidence, Finset.mem_product] using hpair

theorem refineGoodIncidence_mem_repairStructuredIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairGoodIncidences F K) :
    refineGoodIncidence p ∈ repairStructuredIncidences F K := by
  rcases p with ⟨pk, pu⟩
  unfold repairGoodIncidences at hp
  unfold repairStructuredIncidences
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' : pk ∈ ({k} : Finset (CubeRepairPair α)) ∧ pu ∈ repairGoodAtoms F k := by
    have hp'' : pu ∈ repairGoodAtoms F k ∧ k = pk := by
      have hp''' : pu ∈ repairGoodAtoms F k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact hp'''
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  refine mem_biUnion.mpr ⟨pk, hk, ?_⟩
  have hmem : refineGoodTaggedAtom pu ∈ repairStructuredAtoms F pk :=
    refineGoodTaggedAtom_mem_repairStructuredAtoms hp'.2
  have hpair : refineGoodTaggedAtom pu ∈ repairStructuredAtoms F pk ∧ pk = pk := ⟨hmem, rfl⟩
  simpa [refineGoodIncidence, Finset.mem_product] using hpair

section TwoLayer

variable {n m : ℕ}

/-- Underlying concrete subset represented by a two-layer atom. -/
def twoLayerAtomSet : TwoLayerSlice (n + 1) m → Finset (Fin (n + 1))
  | Sum.inl s => s.1
  | Sum.inr s => s.1

/-- Concrete family corresponding to a two-layer `C/U` state. -/
def concreteTwoLayerFamily (C U : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin (n + 1))) :=
  C ∪ U

/-- Canonical raw repair-pair finset for the selected nearest template. This is the Lean avatar of
`K(F)` used by the uniform-corner plan. -/
noncomputable def selectedTemplateRawRepairPairs (F : Finset (TwoLayerSlice (n + 1) m)) :
    Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) :=
  by
    classical
    exact
      (Finset.univ : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))).filter
        fun k =>
          IsRawExposedRepairPair (twoLayerShiftedLT (n := n + 1) (m := m))
            F (selectedTwoLayerTemplate n m F) k.1 k.2

theorem mem_selectedTemplateRawRepairPairs {F : Finset (TwoLayerSlice (n + 1) m)}
    {k : (TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)} :
    k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F ↔
      IsRawExposedRepairPair (twoLayerShiftedLT (n := n + 1) (m := m))
        F (selectedTwoLayerTemplate n m F) k.1 k.2 := by
  classical
  simp [selectedTemplateRawRepairPairs]

/-- Project an abstract two-layer repair pair to the concrete subset pair used by boundary/locality
arguments in the original cube family. -/
def projectedRepairPair
    (k : (TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) :
    CubeRepairPair (Fin (n + 1)) :=
  (twoLayerAtomSet (n := n) (m := m) k.1, twoLayerAtomSet (n := n) (m := m) k.2)

/-- Canonical bad incidences for the selected-template repair set. -/
noncomputable def selectedTemplateBadIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))) :=
  by
    classical
    exact
      (selectedTemplateRawRepairPairs (n := n) (m := m) F).biUnion fun k =>
        ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))).product
          (repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Canonical good incidences for the selected-template repair set. -/
noncomputable def selectedTemplateGoodIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))) :=
  by
    classical
    exact
      (selectedTemplateRawRepairPairs (n := n) (m := m) F).biUnion fun k =>
        ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))).product
          (repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Canonical structured local incidences for the selected-template repair set. -/
noncomputable def selectedTemplateStructuredIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :=
  by
    classical
    exact
      (selectedTemplateRawRepairPairs (n := n) (m := m) F).biUnion fun k =>
        ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))).product
          (repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

theorem atomOfTaggedAtom_mem_selectedTemplateBadIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateBadIncidences (n := n) (m := m) F 𝒜) :
    atomOfTaggedAtom p.2 ∈ repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  classical
  rcases p with ⟨pk, pu⟩
  unfold selectedTemplateBadIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' :
      pk ∈ ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))) ∧
        pu ∈ repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) := by
    have hp'' : pu ∈ repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) ∧ k = pk := by
      simpa [Finset.mem_product, and_left_comm, and_assoc] using hp
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfTaggedAtom_mem_repairBadAtoms_local hp'.2

theorem atomOfTaggedAtom_mem_selectedTemplateGoodIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateGoodIncidences (n := n) (m := m) F 𝒜) :
    atomOfTaggedAtom p.2 ∈ repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  classical
  rcases p with ⟨pk, pu⟩
  unfold selectedTemplateGoodIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' :
      pk ∈ ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))) ∧
        pu ∈ repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) := by
    have hp'' : pu ∈ repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) ∧ k = pk := by
      simpa [Finset.mem_product, and_left_comm, and_assoc] using hp
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfTaggedAtom_mem_repairGoodAtoms_local hp'.2

theorem atomOfCornerRoleAtom_mem_selectedTemplateStructuredIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateStructuredIncidences (n := n) (m := m) F 𝒜) :
    atomOfCornerRoleAtom p.2 ∈ repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  classical
  rcases p with ⟨pk, pu⟩
  unfold selectedTemplateStructuredIncidences at hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' :
      pk ∈ ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))) ∧
        pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) := by
    have hp'' : pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) ∧ k = pk := by
      simpa [Finset.mem_product, and_left_comm, and_assoc] using hp
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  exact atomOfCornerRoleAtom_mem_repairStructuredAtoms_local hp'.2

/-- Canonical refinement of a selected-template bad incidence to structured local corner data. -/
def refineSelectedTemplateBadIncidence
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1))) :=
  (p.1, refineBadTaggedAtom p.2)

/-- Canonical refinement of a selected-template good incidence to structured local corner data. -/
def refineSelectedTemplateGoodIncidence
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1))) :=
  (p.1, refineGoodTaggedAtom p.2)

theorem refineSelectedTemplateBadIncidence_mem_structured
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateBadIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateBadIncidence p ∈
      selectedTemplateStructuredIncidences (n := n) (m := m) F 𝒜 := by
  classical
  rcases p with ⟨pk, pu⟩
  unfold selectedTemplateBadIncidences at hp
  unfold selectedTemplateStructuredIncidences
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' :
      pk ∈ ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))) ∧
        pu ∈ repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) := by
    have hp'' : pu ∈ repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) ∧ k = pk := by
      simpa [Finset.mem_product, and_left_comm, and_assoc] using hp
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  refine mem_biUnion.mpr ⟨pk, hk, ?_⟩
  have hmem :
      refineBadTaggedAtom pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) :=
    refineBadTaggedAtom_mem_repairStructuredAtoms hp'.2
  have hpair :
      refineBadTaggedAtom pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) ∧
        pk = pk := ⟨hmem, rfl⟩
  simpa [refineSelectedTemplateBadIncidence, Finset.mem_product, and_left_comm, and_assoc] using hpair

theorem refineSelectedTemplateGoodIncidence_mem_structured
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateGoodIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateGoodIncidence p ∈
      selectedTemplateStructuredIncidences (n := n) (m := m) F 𝒜 := by
  classical
  rcases p with ⟨pk, pu⟩
  unfold selectedTemplateGoodIncidences at hp
  unfold selectedTemplateStructuredIncidences
  rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
  have hp' :
      pk ∈ ({k} : Finset ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m))) ∧
        pu ∈ repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) := by
    have hp'' : pu ∈ repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) ∧ k = pk := by
      simpa [Finset.mem_product, and_left_comm, and_assoc] using hp
    exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
  have hkEq : pk = k := by simpa using hp'.1
  subst hkEq
  refine mem_biUnion.mpr ⟨pk, hk, ?_⟩
  have hmem :
      refineGoodTaggedAtom pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) :=
    refineGoodTaggedAtom_mem_repairStructuredAtoms hp'.2
  have hpair :
      refineGoodTaggedAtom pu ∈ repairStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) ∧
        pk = pk := ⟨hmem, rfl⟩
  simpa [refineSelectedTemplateGoodIncidence, Finset.mem_product, and_left_comm, and_assoc] using hpair

theorem selectedTemplateRawRepairPairs_nonempty_of_twoLayerState_balanced_nonTemplate
    (C : Finset (Finset (Fin (n + 1)))) (U : Finset (Finset (Fin (n + 1))))
    (hC : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ C → s.card = m)
    (hU : ∀ ⦃s : Finset (Fin (n + 1))⦄, s ∈ U → s.card = m + 1)
    (hCLower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m)) (rankSliceFamily C hC))
    (hULower : IsRelLowerSet (RankSlice.shiftedLT (n := n + 1) (r := m + 1)) (rankSliceFamily U hU))
    (hCbound : #C ≤ Nat.choose (n + 1) m)
    (hbal : #U = Nat.choose (n + 1) m - #C)
    (hneFull : twoLayerState C U hC hU ≠ twoLayerFullTemplate (n + 1) m)
    (hneStar : twoLayerState C U hC hU ≠ twoLayerStarTemplate n m) :
    (selectedTemplateRawRepairPairs (n := n) (m := m) (twoLayerState C U hC hU)).Nonempty := by
  classical
  rcases exists_rawExposedRepairPair_preserving_lower_of_twoLayerState_balanced_nonTemplate
      (n := n) (m := m) C U hC hU hCLower hULower hCbound hbal hneFull hneStar with
    ⟨x, z, hraw, -⟩
  exact ⟨(x, z), by simpa [selectedTemplateRawRepairPairs] using hraw⟩

end TwoLayer

end Erdos1
