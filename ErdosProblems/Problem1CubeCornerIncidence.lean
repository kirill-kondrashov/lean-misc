import ErdosProblems.Problem1CubeRepairLocality
import ErdosProblems.Problem1CubeShiftedInstantiation

open Finset
open scoped Finset

namespace Erdos1

section FiberIncidence

variable {κ β γ : Type*} [DecidableEq κ] [DecidableEq β] [DecidableEq γ]

/-- Disjoint-union incidence finset built fiberwise over a finite parameter set. -/
def fiberIncidences (K : Finset κ) (A : κ → Finset β) : Finset (κ × β) :=
  K.biUnion fun k => ({k} : Finset κ).product (A k)

theorem mem_fiberIncidences_iff {K : Finset κ} {A : κ → Finset β} {p : κ × β} :
    p ∈ fiberIncidences K A ↔ p.1 ∈ K ∧ p.2 ∈ A p.1 := by
  rcases p with ⟨pk, pu⟩
  constructor
  · intro hp
    unfold fiberIncidences at hp
    rcases mem_biUnion.mp hp with ⟨k, hk, hp⟩
    have hp' : pk ∈ ({k} : Finset κ) ∧ pu ∈ A k := by
      have hp'' : pu ∈ A k ∧ k = pk := by
        simpa [Finset.mem_product] using hp
      exact ⟨by simpa [mem_singleton] using hp''.2.symm, hp''.1⟩
    have hkEq : pk = k := by simpa using hp'.1
    subst hkEq
    exact ⟨hk, hp'.2⟩
  · intro hp
    unfold fiberIncidences
    refine mem_biUnion.mpr ⟨pk, hp.1, ?_⟩
    have hpair : pu ∈ A pk ∧ pk = pk := ⟨hp.2, rfl⟩
    simpa [Finset.mem_product] using hpair

/-- Apply a fiberwise transport map to an incidence while preserving the base corner. -/
def liftFiberwise (φ : κ → β → γ) (p : κ × β) : κ × γ :=
  (p.1, φ p.1 p.2)

theorem liftFiberwise_mem_fiberIncidences {K : Finset κ} {A : κ → Finset β} {B : κ → Finset γ}
    {φ : κ → β → γ}
    (hmap : ∀ ⦃k u⦄, k ∈ K → u ∈ A k → φ k u ∈ B k)
    {p : κ × β} (hp : p ∈ fiberIncidences K A) :
    liftFiberwise φ p ∈ fiberIncidences K B := by
  exact (mem_fiberIncidences_iff).2 ⟨(mem_fiberIncidences_iff.mp hp).1,
    hmap (mem_fiberIncidences_iff.mp hp).1 (mem_fiberIncidences_iff.mp hp).2⟩

theorem injOn_liftFiberwise_of_local {K : Finset κ} {A : κ → Finset β} {φ : κ → β → γ}
    (hinj : ∀ ⦃k u v⦄, k ∈ K → u ∈ A k → v ∈ A k → φ k u = φ k v → u = v) :
    Set.InjOn (liftFiberwise φ) ↑(fiberIncidences K A) := by
  intro p hp q hq hpq
  rcases p with ⟨pk, pu⟩
  rcases q with ⟨qk, qu⟩
  have hp' := mem_fiberIncidences_iff.mp hp
  have hq' := mem_fiberIncidences_iff.mp hq
  have hkEq : pk = qk := by
    simpa [liftFiberwise] using congrArg Prod.fst hpq
  subst qk
  have huEq : φ pk pu = φ pk qu := by
    simpa [liftFiberwise] using congrArg Prod.snd hpq
  have : pu = qu := hinj hp'.1 hp'.2 hq'.2 huEq
  subst this
  rfl

theorem card_fiberIncidences_le_card_of_local {K : Finset κ} {A : κ → Finset β} {B : κ → Finset γ}
    {φ : κ → β → γ}
    (hmap : ∀ ⦃k u⦄, k ∈ K → u ∈ A k → φ k u ∈ B k)
    (hinj : ∀ ⦃k u v⦄, k ∈ K → u ∈ A k → v ∈ A k → φ k u = φ k v → u = v) :
    #(fiberIncidences K A) ≤ #(fiberIncidences K B) := by
  exact Finset.card_le_card_of_injOn (liftFiberwise φ)
    (fun _ hp => liftFiberwise_mem_fiberIncidences hmap hp)
    (fun _ hp _ hq heq => injOn_liftFiberwise_of_local hinj hp hq heq)

end FiberIncidence

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

/-- Structured bad atoms keep only the roles contributing positively to defect drift. -/
def repairBadStructuredAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (CornerRole × Finset α) :=
  ({CornerRole.newBoundary} : Finset CornerRole).product (repairNewBoundaryAtoms F k) ∪
    ({CornerRole.oldFamily} : Finset CornerRole).product (repairOldFamilyAtoms F k)

/-- Structured good atoms keep only the roles contributing negatively to defect drift. -/
def repairGoodStructuredAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (CornerRole × Finset α) :=
  ({CornerRole.oldBoundary} : Finset CornerRole).product (repairOldBoundaryAtoms F k) ∪
    ({CornerRole.newFamily} : Finset CornerRole).product (repairNewFamilyAtoms F k)

/-- Boundary witness data: either the special changed atom, or a cover witness `(s, a)` with
`s.erase a` equal to the changed atom. -/
abbrev BoundaryWitnessAtom (α : Type*) := Sum (Finset α) (Finset α × α)

/-- Forget the witness and keep only the boundary atom. -/
def atomOfBoundaryWitnessAtom : BoundaryWitnessAtom α → Finset α :=
  Sum.elim id Prod.fst

/-- Witness-carrying refinement of newly created boundary atoms. -/
noncomputable def repairNewBoundaryWitnessAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (BoundaryWitnessAtom α) :=
  (({k.2} : Finset (Finset α)).filter fun s => s ∈ repairNewBoundaryAtoms F k).map
      Function.Embedding.inl ∪
    (((repairNewBoundaryAtoms F k).product (Finset.univ : Finset α)).filter fun sa =>
      sa.2 ∈ sa.1 ∧ sa.1.erase sa.2 = k.1).map Function.Embedding.inr

/-- Witness-carrying refinement of removed boundary atoms. -/
noncomputable def repairOldBoundaryWitnessAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (BoundaryWitnessAtom α) :=
  (({k.1} : Finset (Finset α)).filter fun s => s ∈ repairOldBoundaryAtoms F k).map
      Function.Embedding.inl ∪
    (((repairOldBoundaryAtoms F k).product (Finset.univ : Finset α)).filter fun sa =>
      sa.2 ∈ sa.1 ∧ sa.1.erase sa.2 = k.2).map Function.Embedding.inr

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

theorem mem_repairBadStructuredAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : CornerRole × Finset α} :
    u ∈ repairBadStructuredAtoms F k ↔
      (u.1 = CornerRole.newBoundary ∧ u.2 ∈ repairNewBoundaryAtoms F k) ∨
        (u.1 = CornerRole.oldFamily ∧ u.2 ∈ repairOldFamilyAtoms F k) := by
  rcases u with ⟨r, s⟩
  cases r <;> simp [repairBadStructuredAtoms, Finset.mem_union, Finset.mem_product]

theorem mem_repairGoodStructuredAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : CornerRole × Finset α} :
    u ∈ repairGoodStructuredAtoms F k ↔
      (u.1 = CornerRole.oldBoundary ∧ u.2 ∈ repairOldBoundaryAtoms F k) ∨
        (u.1 = CornerRole.newFamily ∧ u.2 ∈ repairNewFamilyAtoms F k) := by
  rcases u with ⟨r, s⟩
  cases r <;> simp [repairGoodStructuredAtoms, Finset.mem_union, Finset.mem_product]

theorem atomOfBoundaryWitnessAtom_mem_repairNewBoundaryAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α} (hu : u ∈ repairNewBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u ∈ repairNewBoundaryAtoms F k := by
  rw [repairNewBoundaryWitnessAtoms, Finset.mem_union] at hu
  rcases hu with hu | hu
  · rcases Finset.mem_map.mp hu with ⟨s, hs, rfl⟩
    exact (Finset.mem_filter.mp hs).2
  · rcases Finset.mem_map.mp hu with ⟨sa, hs, rfl⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hs).1).1

theorem atomOfBoundaryWitnessAtom_mem_repairOldBoundaryAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α} (hu : u ∈ repairOldBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u ∈ repairOldBoundaryAtoms F k := by
  rw [repairOldBoundaryWitnessAtoms, Finset.mem_union] at hu
  rcases hu with hu | hu
  · rcases Finset.mem_map.mp hu with ⟨s, hs, rfl⟩
    exact (Finset.mem_filter.mp hs).2
  · rcases Finset.mem_map.mp hu with ⟨sa, hs, rfl⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hs).1).1

theorem atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_new {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α} (hu : u ∈ repairNewBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u ∈ repairLocalNeighborhood k := by
  exact Finset.mem_union.mpr <| Or.inl <| by
    simpa [repairNewBoundaryAtoms] using
      sdiff_positiveBoundary_twoAtomRepair_subset_local (F := F) (x := k.1) (z := k.2)
        (atomOfBoundaryWitnessAtom_mem_repairNewBoundaryAtoms hu)

theorem atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_old {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α} (hu : u ∈ repairOldBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u ∈ repairLocalNeighborhood k := by
  exact Finset.mem_union.mpr <| Or.inr <| by
    simpa [repairOldBoundaryAtoms] using
      sdiff_positiveBoundary_of_twoAtomRepair_subset_local (F := F) (x := k.1) (z := k.2)
        (atomOfBoundaryWitnessAtom_mem_repairOldBoundaryAtoms hu)

theorem exists_repairNewBoundaryWitnessAtom_of_mem {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairNewBoundaryAtoms F k) :
    ∃ u ∈ repairNewBoundaryWitnessAtoms F k, atomOfBoundaryWitnessAtom u = s := by
  rcases mem_sdiff_positiveBoundary_twoAtomRepair_local (by simpa [repairNewBoundaryAtoms] using hs) with
    hsEq | ⟨a, ha, hErase⟩
  · refine ⟨Sum.inl k.2, ?_, hsEq.symm⟩
    rw [repairNewBoundaryWitnessAtoms, Finset.mem_union]
    left
    exact Finset.mem_map.mpr ⟨k.2, Finset.mem_filter.mpr ⟨by simp, by simpa [hsEq] using hs⟩, rfl⟩
  · refine ⟨Sum.inr (s, a), ?_, by rfl⟩
    rw [repairNewBoundaryWitnessAtoms, Finset.mem_union]
    right
    refine Finset.mem_map.mpr ⟨(s, a), ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_product.mpr ⟨hs, by simpa [ha]⟩, ⟨ha, hErase⟩⟩

theorem exists_repairOldBoundaryWitnessAtom_of_mem {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairOldBoundaryAtoms F k) :
    ∃ u ∈ repairOldBoundaryWitnessAtoms F k, atomOfBoundaryWitnessAtom u = s := by
  rcases mem_sdiff_positiveBoundary_of_twoAtomRepair_local (by simpa [repairOldBoundaryAtoms] using hs) with
    hsEq | ⟨a, ha, hErase⟩
  · refine ⟨Sum.inl k.1, ?_, hsEq.symm⟩
    rw [repairOldBoundaryWitnessAtoms, Finset.mem_union]
    left
    exact Finset.mem_map.mpr ⟨k.1, Finset.mem_filter.mpr ⟨by simp, by simpa [hsEq] using hs⟩, rfl⟩
  · refine ⟨Sum.inr (s, a), ?_, by rfl⟩
    rw [repairOldBoundaryWitnessAtoms, Finset.mem_union]
    right
    refine Finset.mem_map.mpr ⟨(s, a), ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_product.mpr ⟨hs, by simpa [ha]⟩, ⟨ha, hErase⟩⟩

/-- Deterministic chosen witness for a new boundary atom. -/
noncomputable def chooseRepairNewBoundaryWitnessAtom {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairNewBoundaryAtoms F k) : BoundaryWitnessAtom α :=
  Classical.choose (exists_repairNewBoundaryWitnessAtom_of_mem hs)

theorem chooseRepairNewBoundaryWitnessAtom_mem {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairNewBoundaryAtoms F k) :
    chooseRepairNewBoundaryWitnessAtom hs ∈ repairNewBoundaryWitnessAtoms F k :=
  (Classical.choose_spec (exists_repairNewBoundaryWitnessAtom_of_mem hs)).1

theorem atomOf_chooseRepairNewBoundaryWitnessAtom {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairNewBoundaryAtoms F k) :
    atomOfBoundaryWitnessAtom (chooseRepairNewBoundaryWitnessAtom hs) = s :=
  (Classical.choose_spec (exists_repairNewBoundaryWitnessAtom_of_mem hs)).2

/-- Deterministic chosen witness for an old boundary atom. -/
noncomputable def chooseRepairOldBoundaryWitnessAtom {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairOldBoundaryAtoms F k) : BoundaryWitnessAtom α :=
  Classical.choose (exists_repairOldBoundaryWitnessAtom_of_mem hs)

theorem chooseRepairOldBoundaryWitnessAtom_mem {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairOldBoundaryAtoms F k) :
    chooseRepairOldBoundaryWitnessAtom hs ∈ repairOldBoundaryWitnessAtoms F k :=
  (Classical.choose_spec (exists_repairOldBoundaryWitnessAtom_of_mem hs)).1

theorem atomOf_chooseRepairOldBoundaryWitnessAtom {F : Finset (Finset α)} {k : CubeRepairPair α}
    {s : Finset α} (hs : s ∈ repairOldBoundaryAtoms F k) :
    atomOfBoundaryWitnessAtom (chooseRepairOldBoundaryWitnessAtom hs) = s :=
  (Classical.choose_spec (exists_repairOldBoundaryWitnessAtom_of_mem hs)).2

/-- Witness-refined local corner atoms, where boundary atoms carry a concrete cover witness. -/
inductive WitnessedCornerAtom (α : Type*)
  | newBoundary : BoundaryWitnessAtom α → WitnessedCornerAtom α
  | oldBoundary : BoundaryWitnessAtom α → WitnessedCornerAtom α
  | newFamily : Finset α → WitnessedCornerAtom α
  | oldFamily : Finset α → WitnessedCornerAtom α
  deriving DecidableEq

namespace WitnessedCornerAtom

def newBoundaryEmb : BoundaryWitnessAtom α ↪ WitnessedCornerAtom α :=
  ⟨WitnessedCornerAtom.newBoundary, by intro a b h; cases h; rfl⟩

def oldBoundaryEmb : BoundaryWitnessAtom α ↪ WitnessedCornerAtom α :=
  ⟨WitnessedCornerAtom.oldBoundary, by intro a b h; cases h; rfl⟩

def newFamilyEmb : Finset α ↪ WitnessedCornerAtom α :=
  ⟨WitnessedCornerAtom.newFamily, by intro a b h; cases h; rfl⟩

def oldFamilyEmb : Finset α ↪ WitnessedCornerAtom α :=
  ⟨WitnessedCornerAtom.oldFamily, by intro a b h; cases h; rfl⟩

end WitnessedCornerAtom

/-- Forget witness/role decoration and keep only the underlying cube atom. -/
def atomOfWitnessedCornerAtom : WitnessedCornerAtom α → Finset α
  | WitnessedCornerAtom.newBoundary u => atomOfBoundaryWitnessAtom u
  | WitnessedCornerAtom.oldBoundary u => atomOfBoundaryWitnessAtom u
  | WitnessedCornerAtom.newFamily s => s
  | WitnessedCornerAtom.oldFamily s => s

/-- Witness-refined bad atoms: new boundary atoms carry witnesses, deleted family atoms stay plain. -/
noncomputable def repairBadWitnessedAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (WitnessedCornerAtom α) :=
  (repairNewBoundaryWitnessAtoms F k).map WitnessedCornerAtom.newBoundaryEmb ∪
    (repairOldFamilyAtoms F k).map WitnessedCornerAtom.oldFamilyEmb

/-- Witness-refined good atoms: old boundary atoms carry witnesses, inserted family atoms stay plain. -/
noncomputable def repairGoodWitnessedAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (WitnessedCornerAtom α) :=
  (repairOldBoundaryWitnessAtoms F k).map WitnessedCornerAtom.oldBoundaryEmb ∪
    (repairNewFamilyAtoms F k).map WitnessedCornerAtom.newFamilyEmb

theorem mem_repairBadWitnessedAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : WitnessedCornerAtom α} :
    u ∈ repairBadWitnessedAtoms F k ↔
      (∃ w ∈ repairNewBoundaryWitnessAtoms F k, u = WitnessedCornerAtom.newBoundary w) ∨
        (∃ s ∈ repairOldFamilyAtoms F k, u = WitnessedCornerAtom.oldFamily s) := by
  constructor
  · intro hu
    rw [repairBadWitnessedAtoms, Finset.mem_union] at hu
    rcases hu with hu | hu
    · rcases Finset.mem_map.mp hu with ⟨w, hw, rfl⟩
      exact Or.inl ⟨w, hw, rfl⟩
    · rcases Finset.mem_map.mp hu with ⟨s, hs, rfl⟩
      exact Or.inr ⟨s, hs, rfl⟩
  · intro hu
    rw [repairBadWitnessedAtoms, Finset.mem_union]
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact Or.inr (Finset.mem_map.mpr ⟨s, hs, rfl⟩)

theorem mem_repairGoodWitnessedAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : WitnessedCornerAtom α} :
    u ∈ repairGoodWitnessedAtoms F k ↔
      (∃ w ∈ repairOldBoundaryWitnessAtoms F k, u = WitnessedCornerAtom.oldBoundary w) ∨
        (∃ s ∈ repairNewFamilyAtoms F k, u = WitnessedCornerAtom.newFamily s) := by
  constructor
  · intro hu
    rw [repairGoodWitnessedAtoms, Finset.mem_union] at hu
    rcases hu with hu | hu
    · rcases Finset.mem_map.mp hu with ⟨w, hw, rfl⟩
      exact Or.inl ⟨w, hw, rfl⟩
    · rcases Finset.mem_map.mp hu with ⟨s, hs, rfl⟩
      exact Or.inr ⟨s, hs, rfl⟩
  · intro hu
    rw [repairGoodWitnessedAtoms, Finset.mem_union]
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact Or.inr (Finset.mem_map.mpr ⟨s, hs, rfl⟩)

theorem atomOfWitnessedCornerAtom_mem_repairLocalNeighborhood {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : WitnessedCornerAtom α} (hu : u ∈ repairBadWitnessedAtoms F k ∪ repairGoodWitnessedAtoms F k) :
    atomOfWitnessedCornerAtom u ∈ repairLocalNeighborhood k := by
  rw [Finset.mem_union] at hu
  rcases hu with hu | hu
  · rw [mem_repairBadWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · simpa [atomOfWitnessedCornerAtom] using atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_new hw
    · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <| by
            rw [mem_singleton]
            exact mem_sdiff_twoAtomRepair hs
  · rw [mem_repairGoodWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · simpa [atomOfWitnessedCornerAtom] using atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_old hw
    · exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <| by
            rw [mem_singleton]
            exact mem_sdiff_of_twoAtomRepair hs

/-- Canonical lift from bad structured atoms to witness-refined bad atoms. -/
noncomputable def refineBadStructuredAtom (F : Finset (Finset α)) (k : CubeRepairPair α)
    (u : CornerRole × Finset α) : WitnessedCornerAtom α :=
  match u with
  | (CornerRole.newBoundary, s) =>
      if hs : s ∈ repairNewBoundaryAtoms F k then
        WitnessedCornerAtom.newBoundary (chooseRepairNewBoundaryWitnessAtom hs)
      else
        WitnessedCornerAtom.oldFamily s
  | (CornerRole.oldFamily, s) => WitnessedCornerAtom.oldFamily s
  | (_, s) => WitnessedCornerAtom.oldFamily s

/-- Canonical lift from good structured atoms to witness-refined good atoms. -/
noncomputable def refineGoodStructuredAtom (F : Finset (Finset α)) (k : CubeRepairPair α)
    (u : CornerRole × Finset α) : WitnessedCornerAtom α :=
  match u with
  | (CornerRole.oldBoundary, s) =>
      if hs : s ∈ repairOldBoundaryAtoms F k then
        WitnessedCornerAtom.oldBoundary (chooseRepairOldBoundaryWitnessAtom hs)
      else
        WitnessedCornerAtom.newFamily s
  | (CornerRole.newFamily, s) => WitnessedCornerAtom.newFamily s
  | (_, s) => WitnessedCornerAtom.newFamily s

theorem refineBadStructuredAtom_mem_witnessed {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : CornerRole × Finset α} (hu : u ∈ repairBadStructuredAtoms F k) :
    refineBadStructuredAtom F k u ∈ repairBadWitnessedAtoms F k := by
  rw [mem_repairBadStructuredAtoms_iff] at hu
  rcases u with ⟨r, s⟩
  rcases hu with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · subst hr
    rw [mem_repairBadWitnessedAtoms_iff]
    left
    exact ⟨chooseRepairNewBoundaryWitnessAtom hs, chooseRepairNewBoundaryWitnessAtom_mem hs, by
      simp [refineBadStructuredAtom, hs]⟩
  · subst hr
    rw [mem_repairBadWitnessedAtoms_iff]
    right
    exact ⟨s, hs, by simp [refineBadStructuredAtom]⟩

theorem refineGoodStructuredAtom_mem_witnessed {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : CornerRole × Finset α} (hu : u ∈ repairGoodStructuredAtoms F k) :
    refineGoodStructuredAtom F k u ∈ repairGoodWitnessedAtoms F k := by
  rw [mem_repairGoodStructuredAtoms_iff] at hu
  rcases u with ⟨r, s⟩
  rcases hu with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · subst hr
    rw [mem_repairGoodWitnessedAtoms_iff]
    left
    exact ⟨chooseRepairOldBoundaryWitnessAtom hs, chooseRepairOldBoundaryWitnessAtom_mem hs, by
      simp [refineGoodStructuredAtom, hs]⟩
  · subst hr
    rw [mem_repairGoodWitnessedAtoms_iff]
    right
    exact ⟨s, hs, by simp [refineGoodStructuredAtom]⟩

/-- Boundary-face geometry remembered by a boundary witness: either the changed apex atom itself
or a codimension-1 facet specified by the erased coordinate. -/
inductive BoundaryFacetGeometry (α : Type*)
  | apex
  | erase (a : α)
  deriving DecidableEq

/-- Geometry class of a witnessed corner atom, separating boundary apex/facet cases from family
roles. -/
inductive WitnessedCornerGeometry (α : Type*)
  | newBoundary : BoundaryFacetGeometry α → WitnessedCornerGeometry α
  | oldBoundary : BoundaryFacetGeometry α → WitnessedCornerGeometry α
  | newFamily
  | oldFamily
  deriving DecidableEq

/-- The boundary-face geometry carried by a concrete boundary witness. -/
def geometryOfBoundaryWitnessAtom : BoundaryWitnessAtom α → BoundaryFacetGeometry α
  | Sum.inl _ => BoundaryFacetGeometry.apex
  | Sum.inr (_, a) => BoundaryFacetGeometry.erase a

/-- Canonical local geometry attached to a witnessed corner atom. -/
def geometryOfWitnessedCornerAtom : WitnessedCornerAtom α → WitnessedCornerGeometry α
  | WitnessedCornerAtom.newBoundary u =>
      WitnessedCornerGeometry.newBoundary (geometryOfBoundaryWitnessAtom u)
  | WitnessedCornerAtom.oldBoundary u =>
      WitnessedCornerGeometry.oldBoundary (geometryOfBoundaryWitnessAtom u)
  | WitnessedCornerAtom.newFamily _ => WitnessedCornerGeometry.newFamily
  | WitnessedCornerAtom.oldFamily _ => WitnessedCornerGeometry.oldFamily

/-- Geometry-refined witnessed atoms keep both the local geometry class and the witnessed atom. -/
abbrev GeometricWitnessedCornerAtom (α : Type*) := WitnessedCornerGeometry α × WitnessedCornerAtom α

/-- Forget the geometric tag and keep the underlying cube atom. -/
def atomOfGeometricWitnessedCornerAtom : GeometricWitnessedCornerAtom α → Finset α :=
  atomOfWitnessedCornerAtom ∘ Prod.snd

/-- Canonical refinement of a witnessed atom by its local geometric case. -/
def refineWitnessedCornerAtom (u : WitnessedCornerAtom α) : GeometricWitnessedCornerAtom α :=
  (geometryOfWitnessedCornerAtom u, u)

def refineWitnessedCornerAtomEmb : WitnessedCornerAtom α ↪ GeometricWitnessedCornerAtom α :=
  ⟨refineWitnessedCornerAtom, by
    intro u v h
    exact congrArg Prod.snd h⟩

/-- Geometry-refined bad witnessed atoms. -/
noncomputable def repairBadGeometricWitnessedAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (GeometricWitnessedCornerAtom α) :=
  (repairBadWitnessedAtoms F k).map refineWitnessedCornerAtomEmb

/-- Geometry-refined good witnessed atoms. -/
noncomputable def repairGoodGeometricWitnessedAtoms (F : Finset (Finset α)) (k : CubeRepairPair α) :
    Finset (GeometricWitnessedCornerAtom α) :=
  (repairGoodWitnessedAtoms F k).map refineWitnessedCornerAtomEmb

/-- The canonical concrete atom attached to a geometric local class for a fixed repair pair. -/
def atomOfWitnessedCornerGeometry (k : CubeRepairPair α) : WitnessedCornerGeometry α → Finset α
  | WitnessedCornerGeometry.newBoundary BoundaryFacetGeometry.apex => k.2
  | WitnessedCornerGeometry.newBoundary (BoundaryFacetGeometry.erase a) => insert a k.1
  | WitnessedCornerGeometry.oldBoundary BoundaryFacetGeometry.apex => k.1
  | WitnessedCornerGeometry.oldBoundary (BoundaryFacetGeometry.erase a) => insert a k.2
  | WitnessedCornerGeometry.newFamily => k.1
  | WitnessedCornerGeometry.oldFamily => k.2

/-- Canonical geometry-refined witnessed atom attached to a local geometry class. -/
def canonicalGeometricWitnessedCornerAtom (k : CubeRepairPair α) :
    WitnessedCornerGeometry α → GeometricWitnessedCornerAtom α
  | WitnessedCornerGeometry.newBoundary BoundaryFacetGeometry.apex =>
      (WitnessedCornerGeometry.newBoundary BoundaryFacetGeometry.apex,
        WitnessedCornerAtom.newBoundary (Sum.inl k.2))
  | WitnessedCornerGeometry.newBoundary (BoundaryFacetGeometry.erase a) =>
      (WitnessedCornerGeometry.newBoundary (BoundaryFacetGeometry.erase a),
        WitnessedCornerAtom.newBoundary (Sum.inr (insert a k.1, a)))
  | WitnessedCornerGeometry.oldBoundary BoundaryFacetGeometry.apex =>
      (WitnessedCornerGeometry.oldBoundary BoundaryFacetGeometry.apex,
        WitnessedCornerAtom.oldBoundary (Sum.inl k.1))
  | WitnessedCornerGeometry.oldBoundary (BoundaryFacetGeometry.erase a) =>
      (WitnessedCornerGeometry.oldBoundary (BoundaryFacetGeometry.erase a),
        WitnessedCornerAtom.oldBoundary (Sum.inr (insert a k.2, a)))
  | WitnessedCornerGeometry.newFamily =>
      (WitnessedCornerGeometry.newFamily, WitnessedCornerAtom.newFamily k.1)
  | WitnessedCornerGeometry.oldFamily =>
      (WitnessedCornerGeometry.oldFamily, WitnessedCornerAtom.oldFamily k.2)

@[simp] theorem fst_canonicalGeometricWitnessedCornerAtom (k : CubeRepairPair α)
    (g : WitnessedCornerGeometry α) :
    (canonicalGeometricWitnessedCornerAtom k g).1 = g := by
  cases g with
  | newBoundary h =>
      cases h <;> rfl
  | oldBoundary h =>
      cases h <;> rfl
  | newFamily =>
      rfl
  | oldFamily =>
      rfl

theorem mem_repairBadGeometricWitnessedAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : GeometricWitnessedCornerAtom α} :
    u ∈ repairBadGeometricWitnessedAtoms F k ↔
      (∃ w ∈ repairNewBoundaryWitnessAtoms F k,
        u = (WitnessedCornerGeometry.newBoundary (geometryOfBoundaryWitnessAtom w),
          WitnessedCornerAtom.newBoundary w)) ∨
        (∃ s ∈ repairOldFamilyAtoms F k,
          u = (WitnessedCornerGeometry.oldFamily, WitnessedCornerAtom.oldFamily s)) := by
  constructor
  · intro hu
    rcases Finset.mem_map.mp hu with ⟨v, hv, rfl⟩
    rw [mem_repairBadWitnessedAtoms_iff] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩
  · intro hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Finset.mem_map.mpr ⟨WitnessedCornerAtom.newBoundary w,
        (mem_repairBadWitnessedAtoms_iff).2 (Or.inl ⟨w, hw, rfl⟩), rfl⟩
    · exact Finset.mem_map.mpr ⟨WitnessedCornerAtom.oldFamily s,
        (mem_repairBadWitnessedAtoms_iff).2 (Or.inr ⟨s, hs, rfl⟩), rfl⟩

theorem mem_repairGoodGeometricWitnessedAtoms_iff {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u : GeometricWitnessedCornerAtom α} :
    u ∈ repairGoodGeometricWitnessedAtoms F k ↔
      (∃ w ∈ repairOldBoundaryWitnessAtoms F k,
        u = (WitnessedCornerGeometry.oldBoundary (geometryOfBoundaryWitnessAtom w),
          WitnessedCornerAtom.oldBoundary w)) ∨
        (∃ s ∈ repairNewFamilyAtoms F k,
          u = (WitnessedCornerGeometry.newFamily, WitnessedCornerAtom.newFamily s)) := by
  constructor
  · intro hu
    rcases Finset.mem_map.mp hu with ⟨v, hv, rfl⟩
    rw [mem_repairGoodWitnessedAtoms_iff] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩
  · intro hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Finset.mem_map.mpr ⟨WitnessedCornerAtom.oldBoundary w,
        (mem_repairGoodWitnessedAtoms_iff).2 (Or.inl ⟨w, hw, rfl⟩), rfl⟩
    · exact Finset.mem_map.mpr ⟨WitnessedCornerAtom.newFamily s,
        (mem_repairGoodWitnessedAtoms_iff).2 (Or.inr ⟨s, hs, rfl⟩), rfl⟩

theorem atomOfGeometricWitnessedCornerAtom_mem_repairLocalNeighborhood {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairBadGeometricWitnessedAtoms F k ∪ repairGoodGeometricWitnessedAtoms F k) :
    atomOfGeometricWitnessedCornerAtom u ∈ repairLocalNeighborhood k := by
  rw [Finset.mem_union] at hu
  rcases hu with hu | hu
  · rw [mem_repairBadGeometricWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · simpa [atomOfGeometricWitnessedCornerAtom] using
        atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_new hw
    · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <| by
            rw [mem_singleton]
            exact mem_sdiff_twoAtomRepair hs
  · rw [mem_repairGoodGeometricWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · simpa [atomOfGeometricWitnessedCornerAtom] using
        atomOfBoundaryWitnessAtom_mem_repairLocalNeighborhood_of_old hw
    · exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <| by
            rw [mem_singleton]
            exact mem_sdiff_of_twoAtomRepair hs

theorem atomOfBoundaryWitnessAtom_eq_of_new_geometry {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α}
    (hu : u ∈ repairNewBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u =
      match geometryOfBoundaryWitnessAtom u with
      | BoundaryFacetGeometry.apex => k.2
      | BoundaryFacetGeometry.erase a => insert a k.1 := by
  cases u with
  | inl s =>
      rw [repairNewBoundaryWitnessAtoms, Finset.mem_union] at hu
      rcases hu with hu | hu
      · rcases Finset.mem_map.mp hu with ⟨t, ht, hEq⟩
        cases hEq
        have hs : s ∈ ({k.2} : Finset (Finset α)) := (Finset.mem_filter.mp ht).1
        have hsEq : s = k.2 := by simpa [mem_singleton] using hs
        simp [atomOfBoundaryWitnessAtom, geometryOfBoundaryWitnessAtom, hsEq]
      · rcases Finset.mem_map.mp hu with ⟨sa, -, hEq⟩
        cases hEq
  | inr sa =>
      rcases sa with ⟨s, a⟩
      rw [repairNewBoundaryWitnessAtoms, Finset.mem_union] at hu
      rcases hu with hu | hu
      · rcases Finset.mem_map.mp hu with ⟨t, -, hEq⟩
        cases hEq
      · rcases Finset.mem_map.mp hu with ⟨ta, hta, hEq⟩
        rcases ta with ⟨t, b⟩
        cases hEq
        have hfilter := Finset.mem_filter.mp hta
        rcases hfilter.2 with ⟨ha, hErase⟩
        calc
          atomOfBoundaryWitnessAtom (Sum.inr (s, a)) = s := by
            simp [atomOfBoundaryWitnessAtom]
          _ = insert a (s.erase a) := by
            rw [Finset.insert_erase ha]
          _ = insert a k.1 := by rw [hErase]

theorem atomOfBoundaryWitnessAtom_eq_of_old_geometry {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : BoundaryWitnessAtom α}
    (hu : u ∈ repairOldBoundaryWitnessAtoms F k) :
    atomOfBoundaryWitnessAtom u =
      match geometryOfBoundaryWitnessAtom u with
      | BoundaryFacetGeometry.apex => k.1
      | BoundaryFacetGeometry.erase a => insert a k.2 := by
  cases u with
  | inl s =>
      rw [repairOldBoundaryWitnessAtoms, Finset.mem_union] at hu
      rcases hu with hu | hu
      · rcases Finset.mem_map.mp hu with ⟨t, ht, hEq⟩
        cases hEq
        have hs : s ∈ ({k.1} : Finset (Finset α)) := (Finset.mem_filter.mp ht).1
        have hsEq : s = k.1 := by simpa [mem_singleton] using hs
        simp [atomOfBoundaryWitnessAtom, geometryOfBoundaryWitnessAtom, hsEq]
      · rcases Finset.mem_map.mp hu with ⟨sa, -, hEq⟩
        cases hEq
  | inr sa =>
      rcases sa with ⟨s, a⟩
      rw [repairOldBoundaryWitnessAtoms, Finset.mem_union] at hu
      rcases hu with hu | hu
      · rcases Finset.mem_map.mp hu with ⟨t, -, hEq⟩
        cases hEq
      · rcases Finset.mem_map.mp hu with ⟨ta, hta, hEq⟩
        rcases ta with ⟨t, b⟩
        cases hEq
        have hfilter := Finset.mem_filter.mp hta
        rcases hfilter.2 with ⟨ha, hErase⟩
        calc
          atomOfBoundaryWitnessAtom (Sum.inr (s, a)) = s := by
            simp [atomOfBoundaryWitnessAtom]
          _ = insert a (s.erase a) := by
            rw [Finset.insert_erase ha]
          _ = insert a k.2 := by rw [hErase]

theorem atomOfGeometricWitnessedCornerAtom_eq_atomOfWitnessedCornerGeometry_of_mem
    {F : Finset (Finset α)} {k : CubeRepairPair α} {u : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairBadGeometricWitnessedAtoms F k ∪ repairGoodGeometricWitnessedAtoms F k) :
    atomOfGeometricWitnessedCornerAtom u = atomOfWitnessedCornerGeometry k u.1 := by
  rw [Finset.mem_union] at hu
  rcases hu with hu | hu
  · rw [mem_repairBadGeometricWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · cases w with
      | inl t =>
          simpa [atomOfGeometricWitnessedCornerAtom, atomOfWitnessedCornerGeometry]
            using atomOfBoundaryWitnessAtom_eq_of_new_geometry (k := k) hw
      | inr sa =>
          simpa [atomOfGeometricWitnessedCornerAtom, atomOfWitnessedCornerGeometry]
            using atomOfBoundaryWitnessAtom_eq_of_new_geometry (k := k) hw
    · rw [mem_sdiff_twoAtomRepair hs]
      rfl
  · rw [mem_repairGoodGeometricWitnessedAtoms_iff] at hu
    rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
    · cases w with
      | inl t =>
          simpa [atomOfGeometricWitnessedCornerAtom, atomOfWitnessedCornerGeometry]
            using atomOfBoundaryWitnessAtom_eq_of_old_geometry (k := k) hw
      | inr sa =>
          simpa [atomOfGeometricWitnessedCornerAtom, atomOfWitnessedCornerGeometry]
            using atomOfBoundaryWitnessAtom_eq_of_old_geometry (k := k) hw
    · rw [mem_sdiff_of_twoAtomRepair hs]
      rfl

theorem eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad
    {F : Finset (Finset α)} {k : CubeRepairPair α} {u : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairBadGeometricWitnessedAtoms F k) :
    u = canonicalGeometricWitnessedCornerAtom k u.1 := by
  rw [mem_repairBadGeometricWitnessedAtoms_iff] at hu
  rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
  · cases w with
    | inl t =>
        have ht : t = k.2 := by
          simpa [geometryOfBoundaryWitnessAtom, atomOfBoundaryWitnessAtom] using
            atomOfBoundaryWitnessAtom_eq_of_new_geometry (k := k) hw
        simp [canonicalGeometricWitnessedCornerAtom, geometryOfBoundaryWitnessAtom, ht]
    | inr sa =>
        rcases sa with ⟨t, a⟩
        have hEq := atomOfBoundaryWitnessAtom_eq_of_new_geometry (k := k) hw
        simp [canonicalGeometricWitnessedCornerAtom, geometryOfBoundaryWitnessAtom,
          atomOfBoundaryWitnessAtom] at hEq ⊢
        exact hEq
  · rw [mem_sdiff_twoAtomRepair hs]
    rfl

theorem eq_canonicalGeometricWitnessedCornerAtom_of_mem_good
    {F : Finset (Finset α)} {k : CubeRepairPair α} {u : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairGoodGeometricWitnessedAtoms F k) :
    u = canonicalGeometricWitnessedCornerAtom k u.1 := by
  rw [mem_repairGoodGeometricWitnessedAtoms_iff] at hu
  rcases hu with ⟨w, hw, rfl⟩ | ⟨s, hs, rfl⟩
  · cases w with
    | inl t =>
        have ht : t = k.1 := by
          simpa [geometryOfBoundaryWitnessAtom, atomOfBoundaryWitnessAtom] using
            atomOfBoundaryWitnessAtom_eq_of_old_geometry (k := k) hw
        simp [canonicalGeometricWitnessedCornerAtom, geometryOfBoundaryWitnessAtom, ht]
    | inr sa =>
        rcases sa with ⟨t, a⟩
        have hEq := atomOfBoundaryWitnessAtom_eq_of_old_geometry (k := k) hw
        simp [canonicalGeometricWitnessedCornerAtom, geometryOfBoundaryWitnessAtom,
          atomOfBoundaryWitnessAtom] at hEq ⊢
        exact hEq
  · rw [mem_sdiff_of_twoAtomRepair hs]
    rfl

theorem eq_of_geometry_eq_of_mem_repairBadGeometricWitnessedAtoms
    {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u v : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairBadGeometricWitnessedAtoms F k)
    (hv : v ∈ repairBadGeometricWitnessedAtoms F k)
    (hgeom : u.1 = v.1) :
    u = v := by
  rw [eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad hu,
    eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad hv, hgeom]

theorem eq_of_geometry_eq_of_mem_repairGoodGeometricWitnessedAtoms
    {F : Finset (Finset α)} {k : CubeRepairPair α}
    {u v : GeometricWitnessedCornerAtom α}
    (hu : u ∈ repairGoodGeometricWitnessedAtoms F k)
    (hv : v ∈ repairGoodGeometricWitnessedAtoms F k)
    (hgeom : u.1 = v.1) :
    u = v := by
  rw [eq_canonicalGeometricWitnessedCornerAtom_of_mem_good hu,
    eq_canonicalGeometricWitnessedCornerAtom_of_mem_good hv, hgeom]

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

/-- Structured bad incidences fiber the bad roles over the repair family. -/
def repairBadStructuredIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × (CornerRole × Finset α)) :=
  fiberIncidences K (fun k => repairBadStructuredAtoms F k)

/-- Structured good incidences fiber the good roles over the repair family. -/
def repairGoodStructuredIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × (CornerRole × Finset α)) :=
  fiberIncidences K (fun k => repairGoodStructuredAtoms F k)

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

theorem refineBadTaggedAtom_mem_repairBadStructuredAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairBadAtoms F k) :
    refineBadTaggedAtom u ∈ repairBadStructuredAtoms F k := by
  cases u with
  | inl s =>
      have hs : s ∈ repairNewBoundaryAtoms F k := by
        simpa [repairBadAtoms] using hu
      exact (mem_repairBadStructuredAtoms_iff (u := (CornerRole.newBoundary, s))).2 (Or.inl ⟨rfl, hs⟩)
  | inr s =>
      have hs : s ∈ repairOldFamilyAtoms F k := by
        simpa [repairBadAtoms] using hu
      exact (mem_repairBadStructuredAtoms_iff (u := (CornerRole.oldFamily, s))).2
        (Or.inr ⟨rfl, hs⟩)

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

theorem refineGoodTaggedAtom_mem_repairGoodStructuredAtoms {F : Finset (Finset α)}
    {k : CubeRepairPair α} {u : Sum (Finset α) (Finset α)} (hu : u ∈ repairGoodAtoms F k) :
    refineGoodTaggedAtom u ∈ repairGoodStructuredAtoms F k := by
  cases u with
  | inl s =>
      have hs : s ∈ repairOldBoundaryAtoms F k := by
        simpa [repairGoodAtoms] using hu
      exact (mem_repairGoodStructuredAtoms_iff (u := (CornerRole.oldBoundary, s))).2
        (Or.inl ⟨rfl, hs⟩)
  | inr s =>
      have hs : s ∈ repairNewFamilyAtoms F k := by
        simpa [repairGoodAtoms] using hu
      exact (mem_repairGoodStructuredAtoms_iff (u := (CornerRole.newFamily, s))).2
        (Or.inr ⟨rfl, hs⟩)

/-- Bad incidence set for a finite repair family. -/
def repairBadIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × Sum (Finset α) (Finset α)) :=
  K.biUnion fun k => ({k} : Finset (CubeRepairPair α)).product (repairBadAtoms F k)

/-- Good incidence set for a finite repair family. -/
def repairGoodIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × Sum (Finset α) (Finset α)) :=
  K.biUnion fun k => ({k} : Finset (CubeRepairPair α)).product (repairGoodAtoms F k)

/-- Witness-refined bad incidences fiber the witnessed bad atoms over the repair family. -/
noncomputable def repairBadWitnessedIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × WitnessedCornerAtom α) :=
  fiberIncidences K (fun k => repairBadWitnessedAtoms F k)

/-- Witness-refined good incidences fiber the witnessed good atoms over the repair family. -/
noncomputable def repairGoodWitnessedIncidences (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × WitnessedCornerAtom α) :=
  fiberIncidences K (fun k => repairGoodWitnessedAtoms F k)

/-- Geometry-refined bad witnessed incidences over the repair family. -/
noncomputable def repairBadGeometricWitnessedIncidences
    (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × GeometricWitnessedCornerAtom α) :=
  fiberIncidences K (fun k => repairBadGeometricWitnessedAtoms F k)

/-- Geometry-refined good witnessed incidences over the repair family. -/
noncomputable def repairGoodGeometricWitnessedIncidences
    (F : Finset (Finset α)) (K : Finset (CubeRepairPair α)) :
    Finset (CubeRepairPair α × GeometricWitnessedCornerAtom α) :=
  fiberIncidences K (fun k => repairGoodGeometricWitnessedAtoms F k)

/-- Canonical refinement of a bad structured incidence to a witness-refined bad incidence. -/
noncomputable def refineBadStructuredIncidence (F : Finset (Finset α))
    (p : CubeRepairPair α × (CornerRole × Finset α)) :
    CubeRepairPair α × WitnessedCornerAtom α :=
  (p.1, refineBadStructuredAtom F p.1 p.2)

/-- Canonical refinement of a good structured incidence to a witness-refined good incidence. -/
noncomputable def refineGoodStructuredIncidence (F : Finset (Finset α))
    (p : CubeRepairPair α × (CornerRole × Finset α)) :
    CubeRepairPair α × WitnessedCornerAtom α :=
  (p.1, refineGoodStructuredAtom F p.1 p.2)

/-- Canonical refinement of a bad witnessed incidence to a geometry-refined witnessed incidence. -/
def refineBadWitnessedIncidence
    (p : CubeRepairPair α × WitnessedCornerAtom α) :
    CubeRepairPair α × GeometricWitnessedCornerAtom α :=
  (p.1, refineWitnessedCornerAtom p.2)

/-- Canonical refinement of a good witnessed incidence to a geometry-refined witnessed incidence. -/
def refineGoodWitnessedIncidence
    (p : CubeRepairPair α × WitnessedCornerAtom α) :
    CubeRepairPair α × GeometricWitnessedCornerAtom α :=
  (p.1, refineWitnessedCornerAtom p.2)

theorem refineBadStructuredIncidence_mem_repairBadWitnessedIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × (CornerRole × Finset α)} (hp : p ∈ repairBadStructuredIncidences F K) :
    refineBadStructuredIncidence F p ∈ repairBadWitnessedIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      simpa [refineBadStructuredIncidence] using
        refineBadStructuredAtom_mem_witnessed ((mem_fiberIncidences_iff.mp hp).2)⟩

theorem refineGoodStructuredIncidence_mem_repairGoodWitnessedIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × (CornerRole × Finset α)} (hp : p ∈ repairGoodStructuredIncidences F K) :
    refineGoodStructuredIncidence F p ∈ repairGoodWitnessedIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      simpa [refineGoodStructuredIncidence] using
        refineGoodStructuredAtom_mem_witnessed ((mem_fiberIncidences_iff.mp hp).2)⟩

theorem refineBadWitnessedIncidence_mem_repairBadGeometricWitnessedIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × WitnessedCornerAtom α} (hp : p ∈ repairBadWitnessedIncidences F K) :
    refineBadWitnessedIncidence p ∈ repairBadGeometricWitnessedIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      exact Finset.mem_map.mpr ⟨pu, (mem_fiberIncidences_iff.mp hp).2, rfl⟩⟩

theorem refineGoodWitnessedIncidence_mem_repairGoodGeometricWitnessedIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × WitnessedCornerAtom α} (hp : p ∈ repairGoodWitnessedIncidences F K) :
    refineGoodWitnessedIncidence p ∈ repairGoodGeometricWitnessedIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      exact Finset.mem_map.mpr ⟨pu, (mem_fiberIncidences_iff.mp hp).2, rfl⟩⟩

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

theorem atomOfWitnessedCornerAtom_mem_repairBadWitnessedIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × WitnessedCornerAtom α} (hp : p ∈ repairBadWitnessedIncidences F K) :
    atomOfWitnessedCornerAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inl hp'.2)

theorem atomOfWitnessedCornerAtom_mem_repairGoodWitnessedIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × WitnessedCornerAtom α} (hp : p ∈ repairGoodWitnessedIncidences F K) :
    atomOfWitnessedCornerAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inr hp'.2)

theorem atomOfGeometricWitnessedCornerAtom_mem_repairBadGeometricWitnessedIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × GeometricWitnessedCornerAtom α}
    (hp : p ∈ repairBadGeometricWitnessedIncidences F K) :
    atomOfGeometricWitnessedCornerAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfGeometricWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inl hp'.2)

theorem atomOfGeometricWitnessedCornerAtom_mem_repairGoodGeometricWitnessedIncidences_local
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × GeometricWitnessedCornerAtom α}
    (hp : p ∈ repairGoodGeometricWitnessedIncidences F K) :
    atomOfGeometricWitnessedCornerAtom p.2 ∈ repairLocalNeighborhood p.1 := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfGeometricWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inr hp'.2)

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

theorem refineBadIncidence_mem_repairBadStructuredIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairBadIncidences F K) :
    refineBadIncidence p ∈ repairBadStructuredIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp (by
        simpa [repairBadIncidences, fiberIncidences] using hp : (pk, pu) ∈ fiberIncidences K (fun k => repairBadAtoms F k))).1,
      by
        have hp' : pu ∈ repairBadAtoms F pk := by
          exact (mem_fiberIncidences_iff.mp (by
            simpa [repairBadIncidences, fiberIncidences] using hp :
              (pk, pu) ∈ fiberIncidences K (fun k => repairBadAtoms F k))).2
        simpa [refineBadIncidence] using refineBadTaggedAtom_mem_repairBadStructuredAtoms hp'⟩

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

theorem refineGoodIncidence_mem_repairGoodStructuredIncidences
    {F : Finset (Finset α)} {K : Finset (CubeRepairPair α)}
    {p : CubeRepairPair α × Sum (Finset α) (Finset α)} (hp : p ∈ repairGoodIncidences F K) :
    refineGoodIncidence p ∈ repairGoodStructuredIncidences F K := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp (by
        simpa [repairGoodIncidences, fiberIncidences] using hp : (pk, pu) ∈ fiberIncidences K (fun k => repairGoodAtoms F k))).1,
      by
        have hp' : pu ∈ repairGoodAtoms F pk := by
          exact (mem_fiberIncidences_iff.mp (by
            simpa [repairGoodIncidences, fiberIncidences] using hp :
              (pk, pu) ∈ fiberIncidences K (fun k => repairGoodAtoms F k))).2
        simpa [refineGoodIncidence] using refineGoodTaggedAtom_mem_repairGoodStructuredAtoms hp'⟩

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

/-- Structured bad incidences on the selected-template repair family. -/
noncomputable def selectedTemplateBadStructuredIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Structured good incidences on the selected-template repair family. -/
noncomputable def selectedTemplateGoodStructuredIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairGoodStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Witness-refined bad incidences on the selected-template repair family. -/
noncomputable def selectedTemplateBadWitnessedIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairBadWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Witness-refined good incidences on the selected-template repair family. -/
noncomputable def selectedTemplateGoodWitnessedIncidences (F : Finset (TwoLayerSlice (n + 1) m))
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairGoodWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Geometry-refined bad witnessed incidences on the selected-template repair family. -/
noncomputable def selectedTemplateBadGeometricWitnessedIncidences
    (F : Finset (TwoLayerSlice (n + 1) m)) (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

/-- Geometry-refined good witnessed incidences on the selected-template repair family. -/
noncomputable def selectedTemplateGoodGeometricWitnessedIncidences
    (F : Finset (TwoLayerSlice (n + 1) m)) (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))) :=
  fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
    (fun k => repairGoodGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))

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

theorem atomOfWitnessedCornerAtom_mem_selectedTemplateBadWitnessedIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateBadWitnessedIncidences (n := n) (m := m) F 𝒜) :
    atomOfWitnessedCornerAtom p.2 ∈
      repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inl hp'.2)

theorem atomOfWitnessedCornerAtom_mem_selectedTemplateGoodWitnessedIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateGoodWitnessedIncidences (n := n) (m := m) F 𝒜) :
    atomOfWitnessedCornerAtom p.2 ∈
      repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inr hp'.2)

theorem atomOfGeometricWitnessedCornerAtom_mem_selectedTemplateBadGeometricWitnessedIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) :
    atomOfGeometricWitnessedCornerAtom p.2 ∈
      repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfGeometricWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inl hp'.2)

theorem atomOfGeometricWitnessedCornerAtom_mem_selectedTemplateGoodGeometricWitnessedIncidences_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) :
    atomOfGeometricWitnessedCornerAtom p.2 ∈
      repairLocalNeighborhood (projectedRepairPair (n := n) (m := m) p.1) := by
  have hp' := mem_fiberIncidences_iff.mp hp
  exact atomOfGeometricWitnessedCornerAtom_mem_repairLocalNeighborhood
    (Finset.mem_union.mpr <| Or.inr hp'.2)

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

theorem refineSelectedTemplateBadIncidence_mem_badStructured
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateBadIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateBadIncidence p ∈
      selectedTemplateBadStructuredIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp (by
        simpa [selectedTemplateBadIncidences, fiberIncidences] using hp :
          (pk, pu) ∈ fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
            (fun k => repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k)))).1,
      by
        have hp' : pu ∈ repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) := by
          exact (mem_fiberIncidences_iff.mp (by
            simpa [selectedTemplateBadIncidences, fiberIncidences] using hp :
              (pk, pu) ∈ fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
                (fun k => repairBadAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k)))).2
        simpa [refineSelectedTemplateBadIncidence] using
          refineBadTaggedAtom_mem_repairBadStructuredAtoms hp'⟩

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

theorem refineSelectedTemplateGoodIncidence_mem_goodStructured
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      Sum (Finset (Fin (n + 1))) (Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateGoodIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateGoodIncidence p ∈
      selectedTemplateGoodStructuredIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp (by
        simpa [selectedTemplateGoodIncidences, fiberIncidences] using hp :
          (pk, pu) ∈ fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
            (fun k => repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k)))).1,
      by
        have hp' : pu ∈ repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) := by
          exact (mem_fiberIncidences_iff.mp (by
            simpa [selectedTemplateGoodIncidences, fiberIncidences] using hp :
              (pk, pu) ∈ fiberIncidences (selectedTemplateRawRepairPairs (n := n) (m := m) F)
                (fun k => repairGoodAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k)))).2
        simpa [refineSelectedTemplateGoodIncidence] using
          refineGoodTaggedAtom_mem_repairGoodStructuredAtoms hp'⟩

/-- Canonical refinement of a selected-template bad structured incidence to witness-refined data. -/
noncomputable def refineSelectedTemplateBadStructuredIncidence
    (F : Finset (Finset (Fin (n + 1))))
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1)) :=
  (p.1, refineBadStructuredAtom F (projectedRepairPair (n := n) (m := m) p.1) p.2)

/-- Canonical refinement of a selected-template good structured incidence to witness-refined data. -/
noncomputable def refineSelectedTemplateGoodStructuredIncidence
    (F : Finset (Finset (Fin (n + 1))))
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1)) :=
  (p.1, refineGoodStructuredAtom F (projectedRepairPair (n := n) (m := m) p.1) p.2)

theorem refineSelectedTemplateBadStructuredIncidence_mem_badWitnessed
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateBadStructuredIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateBadStructuredIncidence (n := n) (m := m) 𝒜 p ∈
      selectedTemplateBadWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      simpa [refineSelectedTemplateBadStructuredIncidence] using
        refineBadStructuredAtom_mem_witnessed ((mem_fiberIncidences_iff.mp hp).2)⟩

theorem refineSelectedTemplateGoodStructuredIncidence_mem_goodWitnessed
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateGoodStructuredIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateGoodStructuredIncidence (n := n) (m := m) 𝒜 p ∈
      selectedTemplateGoodWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      simpa [refineSelectedTemplateGoodStructuredIncidence] using
        refineGoodStructuredAtom_mem_witnessed ((mem_fiberIncidences_iff.mp hp).2)⟩

/-- Canonical refinement of a selected-template bad witnessed incidence to geometric local data. -/
def refineSelectedTemplateBadWitnessedIncidence
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1)) :=
  (p.1, refineWitnessedCornerAtom p.2)

/-- Canonical refinement of a selected-template good witnessed incidence to geometric local data. -/
def refineSelectedTemplateGoodWitnessedIncidence
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1)) :=
  (p.1, refineWitnessedCornerAtom p.2)

theorem refineSelectedTemplateBadWitnessedIncidence_mem_badGeometricWitnessed
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateBadWitnessedIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateBadWitnessedIncidence p ∈
      selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      exact Finset.mem_map.mpr ⟨pu, (mem_fiberIncidences_iff.mp hp).2, rfl⟩⟩

theorem refineSelectedTemplateGoodWitnessedIncidence_mem_goodGeometricWitnessed
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      WitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateGoodWitnessedIncidences (n := n) (m := m) F 𝒜) :
    refineSelectedTemplateGoodWitnessedIncidence p ∈
      selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  exact (mem_fiberIncidences_iff).2
    ⟨(mem_fiberIncidences_iff.mp hp).1, by
      exact Finset.mem_map.mpr ⟨pu, (mem_fiberIncidences_iff.mp hp).2, rfl⟩⟩

/-- Transport induced by a local map on geometry classes, using the canonical representative of the
target class. -/
def selectedTemplateGeometryClassTransport
    (ψ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      WitnessedCornerGeometry (Fin (n + 1)) → WitnessedCornerGeometry (Fin (n + 1)))
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1)) :=
  (p.1, canonicalGeometricWitnessedCornerAtom
    (projectedRepairPair (n := n) (m := m) p.1) (ψ p.1 p.2.1))

theorem selectedTemplateGeometryClassTransport_mem_good_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {ψ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      WitnessedCornerGeometry (Fin (n + 1)) → WitnessedCornerGeometry (Fin (n + 1))}
    (hmap : ∀ ⦃k g⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) g ∈
          repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) (ψ k g) ∈
              repairGoodGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) :
    selectedTemplateGeometryClassTransport (n := n) (m := m) ψ p ∈
      selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  rcases p with ⟨pk, pu⟩
  refine (mem_fiberIncidences_iff).2 ?_
  have hp' := mem_fiberIncidences_iff.mp hp
  refine ⟨hp'.1, ?_⟩
  have hcanon : canonicalGeometricWitnessedCornerAtom
      (projectedRepairPair (n := n) (m := m) pk) pu.1 ∈
        repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) := by
    rw [← eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad hp'.2]
    exact hp'.2
  simpa [selectedTemplateGeometryClassTransport] using hmap hp'.1 hcanon

theorem selectedTemplateGeometryClassTransport_injOn_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {ψ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      WitnessedCornerGeometry (Fin (n + 1)) → WitnessedCornerGeometry (Fin (n + 1))}
    (hinj : ∀ ⦃k g h⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) g ∈
          repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) h ∈
              repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
                ψ k g = ψ k h → g = h) :
    Set.InjOn (selectedTemplateGeometryClassTransport (n := n) (m := m) ψ)
      ↑(selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) := by
  intro p hp q hq heq
  rcases p with ⟨pk, pu⟩
  rcases q with ⟨qk, qu⟩
  have hp' := mem_fiberIncidences_iff.mp hp
  have hq' := mem_fiberIncidences_iff.mp hq
  have hk : pk = qk := by simpa [selectedTemplateGeometryClassTransport] using congrArg Prod.fst heq
  subst hk
  have hpu : canonicalGeometricWitnessedCornerAtom
      (projectedRepairPair (n := n) (m := m) pk) pu.1 ∈
        repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) := by
    rw [← eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad hp'.2]
    exact hp'.2
  have hqu : canonicalGeometricWitnessedCornerAtom
      (projectedRepairPair (n := n) (m := m) pk) qu.1 ∈
        repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) pk) := by
    rw [← eq_canonicalGeometricWitnessedCornerAtom_of_mem_bad hq'.2]
    exact hq'.2
  have hclass : ψ pk pu.1 = ψ pk qu.1 := by
    have hclass' := congrArg (fun r => r.2.1) heq
    simpa [selectedTemplateGeometryClassTransport] using hclass'
  have hgeom : pu.1 = qu.1 := hinj hp'.1 hpu hqu hclass
  have huEq : pu = qu :=
    eq_of_geometry_eq_of_mem_repairBadGeometricWitnessedAtoms hp'.2 hq'.2 hgeom
  exact by cases huEq; rfl

theorem card_selectedTemplateBadGeometricWitnessedIncidences_le_card_selectedTemplateGoodGeometricWitnessedIncidences_of_geometryClassMap
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {ψ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      WitnessedCornerGeometry (Fin (n + 1)) → WitnessedCornerGeometry (Fin (n + 1))}
    (hmap : ∀ ⦃k g⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) g ∈
          repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) (ψ k g) ∈
              repairGoodGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    (hinj : ∀ ⦃k g h⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) g ∈
          repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            canonicalGeometricWitnessedCornerAtom (projectedRepairPair (n := n) (m := m) k) h ∈
              repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
                ψ k g = ψ k h → g = h) :
    #(selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) ≤
      #(selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) := by
  exact Finset.card_le_card_of_injOn
    (selectedTemplateGeometryClassTransport (n := n) (m := m) ψ)
    (fun _ hp => selectedTemplateGeometryClassTransport_mem_good_of_local hmap hp)
    (fun _ hp _ hq heq => selectedTemplateGeometryClassTransport_injOn_of_local hinj hp hq heq)

/-- Global transport induced by a fiberwise map on geometry-refined witnessed selected-template
incidences. -/
def selectedTemplateGeometricWitnessedTransport
    (φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      GeometricWitnessedCornerAtom (Fin (n + 1)) → GeometricWitnessedCornerAtom (Fin (n + 1)))
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1)) :=
  liftFiberwise φ p

theorem selectedTemplateGeometricWitnessedTransport_mem_good_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      GeometricWitnessedCornerAtom (Fin (n + 1)) → GeometricWitnessedCornerAtom (Fin (n + 1))}    
    (hmap : ∀ ⦃k u⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          φ k u ∈ repairGoodGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hp : p ∈ selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) :
    selectedTemplateGeometricWitnessedTransport (n := n) (m := m) φ p ∈
      selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜 := by
  exact liftFiberwise_mem_fiberIncidences hmap hp

theorem selectedTemplateGeometricWitnessedTransport_injOn_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      GeometricWitnessedCornerAtom (Fin (n + 1)) → GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hinj : ∀ ⦃k u v⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          v ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            φ k u = φ k v → u = v) :
    Set.InjOn (selectedTemplateGeometricWitnessedTransport (n := n) (m := m) φ)
      ↑(selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) := by
  exact injOn_liftFiberwise_of_local hinj

theorem card_selectedTemplateBadGeometricWitnessedIncidences_le_card_selectedTemplateGoodGeometricWitnessedIncidences_of_local_inj
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      GeometricWitnessedCornerAtom (Fin (n + 1)) → GeometricWitnessedCornerAtom (Fin (n + 1))}
    (hmap : ∀ ⦃k u⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          φ k u ∈ repairGoodGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    (hinj : ∀ ⦃k u v⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          v ∈ repairBadGeometricWitnessedAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            φ k u = φ k v → u = v) :
    #(selectedTemplateBadGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) ≤
      #(selectedTemplateGoodGeometricWitnessedIncidences (n := n) (m := m) F 𝒜) := by
  exact card_fiberIncidences_le_card_of_local hmap hinj

/-- Global transport induced by a fiberwise structured local map on selected-template corners. -/
def selectedTemplateStructuredTransport
    (φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      (CornerRole × Finset (Fin (n + 1))) → (CornerRole × Finset (Fin (n + 1))))
    (p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))) :
    ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1))) :=
  liftFiberwise φ p

theorem selectedTemplateStructuredTransport_mem_good_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      (CornerRole × Finset (Fin (n + 1))) → (CornerRole × Finset (Fin (n + 1)))}
    (hmap : ∀ ⦃k u⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          φ k u ∈ repairGoodStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    {p : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) ×
      (CornerRole × Finset (Fin (n + 1)))}
    (hp : p ∈ selectedTemplateBadStructuredIncidences (n := n) (m := m) F 𝒜) :
    selectedTemplateStructuredTransport (n := n) (m := m) φ p ∈
      selectedTemplateGoodStructuredIncidences (n := n) (m := m) F 𝒜 := by
  exact liftFiberwise_mem_fiberIncidences hmap hp

theorem selectedTemplateStructuredTransport_injOn_of_local
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      (CornerRole × Finset (Fin (n + 1))) → (CornerRole × Finset (Fin (n + 1)))}
    (hinj : ∀ ⦃k u v⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          v ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            φ k u = φ k v → u = v) :
    Set.InjOn (selectedTemplateStructuredTransport (n := n) (m := m) φ)
      ↑(selectedTemplateBadStructuredIncidences (n := n) (m := m) F 𝒜) := by
  exact injOn_liftFiberwise_of_local hinj

theorem card_selectedTemplateBadStructuredIncidences_le_card_selectedTemplateGoodStructuredIncidences_of_local_inj
    {F : Finset (TwoLayerSlice (n + 1) m)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    {φ : ((TwoLayerSlice (n + 1) m) × (TwoLayerSlice (n + 1) m)) →
      (CornerRole × Finset (Fin (n + 1))) → (CornerRole × Finset (Fin (n + 1)))}
    (hmap : ∀ ⦃k u⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          φ k u ∈ repairGoodStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k))
    (hinj : ∀ ⦃k u v⦄,
      k ∈ selectedTemplateRawRepairPairs (n := n) (m := m) F →
        u ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
          v ∈ repairBadStructuredAtoms 𝒜 (projectedRepairPair (n := n) (m := m) k) →
            φ k u = φ k v → u = v) :
    #(selectedTemplateBadStructuredIncidences (n := n) (m := m) F 𝒜) ≤
      #(selectedTemplateGoodStructuredIncidences (n := n) (m := m) F 𝒜) := by
  exact card_fiberIncidences_le_card_of_local hmap hinj

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
