import Groups.VirtuallyEngelGroup
import Groups.GeodesicGrowth

/-!
# Geodesic growth of Bodart's virtually Engel group — foundations

This file begins the fully internal, from-scratch proof of Bodart's Theorem 4 (the axiom
`VirtuallyEngel.theorem_4`):
`γ_geod(n) ≍ exp(n^{3/5} · log n)` for the virtually Engel group with respect to the alphabet
`S = {a, a⁻¹, t}`.

The very first step is to move the counting problem out of the abstract `PresentedGroup relators`
and into the concrete, computable coordinate model `CoordGroup = EngelCoords ⋊ Symmetry`. This is
justified by injectivity of the coordinate homomorphism `toCoordGroup` (the discharged axiom A1,
`toCoordGroup_injective`): two alphabet words represent the same group element **iff** they
evaluate to the same coordinate-model element. Consequently a word is geodesic iff it is a
minimal-length word evaluating to its coordinate image, and geodesic growth equals the number of
such minimal words counted directly in the model.

All later analytic and combinatorial work (Stoll-metric comparison, the Theorem 1 upper bound, and
the Section 4 lower-bound construction) can then be phrased entirely inside `CoordGroup`.
-/

open Filter PresentedGroup

namespace VirtuallyEngel

/-- The Bodart alphabet `S = {a, a⁻¹, t}` interpreted directly in the computable coordinate
model. -/
def coordLetterValue : Letter → CoordGroup
  | .a => coordA
  | .aInv => coordA⁻¹
  | .t => coordT

theorem toCoordGroup_letterValue (ℓ : Letter) :
    toCoordGroup (letterValue ℓ) = coordLetterValue ℓ := by
  cases ℓ <;>
    simp only [letterValue, coordLetterValue, map_inv, toCoordGroup]
  all_goals first
    | rfl
    | (rw [PresentedGroup.toGroup_mk]; rfl)
    | (rw [map_inv, PresentedGroup.toGroup_mk]; rfl)

/-- Evaluate a word over the Bodart alphabet directly in the coordinate model. -/
def evalCoordWord (w : List Letter) : CoordGroup :=
  w.foldl (fun g a => g * coordLetterValue a) 1

theorem toCoordGroup_evalWordOver (w : List Letter) :
    toCoordGroup (PresentedGroup.evalWordOver relators letterValue w) = evalCoordWord w := by
  have gen : ∀ (acc : Group) (w : List Letter),
      toCoordGroup (w.foldl (fun g a => g * letterValue a) acc)
        = w.foldl (fun g a => g * coordLetterValue a) (toCoordGroup acc) := by
    intro acc w
    induction w generalizing acc with
    | nil => simp
    | cons a w ih =>
        simp only [List.foldl_cons]
        rw [ih (acc * letterValue a), map_mul, toCoordGroup_letterValue]
  have := gen 1 w
  simpa [PresentedGroup.evalWordOver, evalCoordWord, map_one] using this

/-- Word equality reduces to equality in the computable model, by injectivity of
`toCoordGroup` (axiom A1, now a theorem). -/
theorem evalWordOver_eq_iff (v w : List Letter) :
    PresentedGroup.evalWordOver relators letterValue v
      = PresentedGroup.evalWordOver relators letterValue w
    ↔ evalCoordWord v = evalCoordWord w := by
  rw [← toCoordGroup_evalWordOver v, ← toCoordGroup_evalWordOver w]
  exact ⟨fun h => by rw [h], fun h => toCoordGroup_injective h⟩

/-- A word over the Bodart alphabet is **coordinate-geodesic** when no shorter word evaluates to
the same coordinate-model element. -/
def CoordGeodesic (w : List Letter) : Prop :=
  ∀ v, evalCoordWord v = evalCoordWord w → w.length ≤ v.length

/-- Geodesicity of an alphabet word is equivalent to coordinate-geodesicity. -/
theorem isGeodesic_iff_coord (w : List Letter) :
    PresentedGroup.IsGeodesicWordOver relators letterValue w ↔ CoordGeodesic w := by
  unfold PresentedGroup.IsGeodesicWordOver CoordGeodesic
  constructor
  · intro h v hv
    exact h v ((evalWordOver_eq_iff v w).mpr hv)
  · intro h v hv
    exact h v ((evalWordOver_eq_iff v w).mp hv)

/-- **Geodesic growth as a coordinate-model count.** The geodesic growth function equals the
number of length-`n` alphabet words that are minimal representatives of their coordinate image. -/
theorem geodesicGrowth_eq_coordCount (n : ℕ) :
    geodesicGrowth n
      = Nat.card {w : WordTuple Letter n // CoordGeodesic (List.ofFn w)} := by
  unfold geodesicGrowth PresentedGroup.geodesicGrowth
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun w => ?_)
  unfold PresentedGroup.IsGeodesicTupleWordOver
  exact isGeodesic_iff_coord (List.ofFn w)

/-- Evaluating a concatenated coordinate word is the product of the evaluations. -/
theorem evalCoordWord_append (v w : List Letter) :
    evalCoordWord (v ++ w) = evalCoordWord v * evalCoordWord w := by
  unfold evalCoordWord
  rw [List.foldl_append]
  have gen : ∀ (acc : CoordGroup) (w : List Letter),
      w.foldl (fun g a => g * coordLetterValue a) acc
        = acc * w.foldl (fun g a => g * coordLetterValue a) 1 := by
    intro acc w
    induction w generalizing acc with
    | nil => simp
    | cons b w ih =>
        rw [List.foldl_cons, List.foldl_cons, ih (acc * coordLetterValue b),
          ih (1 * coordLetterValue b)]
        simp [mul_assoc]
  exact gen _ w

/-- Evaluating a single-letter word yields that letter's coordinate value. -/
theorem evalCoordWord_single (x : Letter) : evalCoordWord [x] = coordLetterValue x := by
  simp [evalCoordWord]

/-- A single generator step moves the planar endpoint `(u, v)` by at most one unit in the
`ℓ¹` sense, under any symmetry action. -/
theorem letterStep_le_one (x : Letter) (s : Symmetry) :
    ((symmetryAction s) (coordLetterValue x).left).u.natAbs
      + ((symmetryAction s) (coordLetterValue x).left).v.natAbs ≤ 1 := by
  cases x <;> cases s <;> decide

/-- **Reachability box (planar coordinates).** After a word of length `n`, the `ℓ¹` size of the
planar endpoint `(u, v)` of the coordinate image is at most `n`. -/
theorem endpoint_le_length (w : List Letter) :
    (evalCoordWord w).left.u.natAbs + (evalCoordWord w).left.v.natAbs ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [evalCoordWord]
  | append_singleton xs x ih =>
      rw [evalCoordWord_append, evalCoordWord_single, List.length_append]
      have hleft : ((evalCoordWord xs) * coordLetterValue x).left
          = (evalCoordWord xs).left
            * (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left := rfl
      rw [hleft]
      set g := (evalCoordWord xs).left
      set c := (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left
      have hc : c.u.natAbs + c.v.natAbs ≤ 1 := letterStep_le_one x (evalCoordWord xs).right
      have hu : (g * c).u = g.u + c.u := EngelCoords.mul_u g c
      have hv : (g * c).v = g.v + c.v := EngelCoords.mul_v g c
      have tu : (g.u + c.u).natAbs ≤ g.u.natAbs + c.u.natAbs := Int.natAbs_add_le _ _
      have tv : (g.v + c.v).natAbs ≤ g.v.natAbs + c.v.natAbs := Int.natAbs_add_le _ _
      rw [hu, hv, List.length_cons, List.length_nil]
      omega

/-- A single generator step adds `0` to the signed-area coordinate (its own area is zero). -/
theorem letterStep_area_zero (x : Letter) (s : Symmetry) :
    ((symmetryAction s) (coordLetterValue x).left).area = 0 := by
  cases x <;> cases s <;> decide

/-- A single generator step adds `0` to the `bary3` coordinate (its own `bary3` is zero). -/
theorem letterStep_bary3_zero (x : Letter) (s : Symmetry) :
    ((symmetryAction s) (coordLetterValue x).left).bary3 = 0 := by
  cases x <;> cases s <;> decide

/-- The determinant cross-term produced by a single generator step is bounded by the current
`ℓ¹` planar size. -/
theorem letterStep_det2_le (g : EngelCoords) (x : Letter) (s : Symmetry) :
    (EngelCoords.det2 g ((symmetryAction s) (coordLetterValue x).left)).natAbs
      ≤ g.u.natAbs + g.v.natAbs := by
  have huv : ((symmetryAction s) (coordLetterValue x).left).u.natAbs
      + ((symmetryAction s) (coordLetterValue x).left).v.natAbs ≤ 1 :=
    letterStep_le_one x s
  set c := (symmetryAction s) (coordLetterValue x).left
  unfold EngelCoords.det2
  have h1 : (g.v * c.u - g.u * c.v).natAbs ≤ (g.v * c.u).natAbs + (g.u * c.v).natAbs :=
    Int.natAbs_sub_le _ _
  rw [Int.natAbs_mul, Int.natAbs_mul] at h1
  nlinarith [Nat.zero_le g.u.natAbs, Nat.zero_le g.v.natAbs, huv,
    Nat.mul_le_mul_left g.v.natAbs (show c.u.natAbs ≤ 1 by omega),
    Nat.mul_le_mul_left g.u.natAbs (show c.v.natAbs ≤ 1 by omega)]

/-- The linear pre-factor of the `bary3` update in a single generator step is bounded by twice
the current `ℓ¹` planar size plus one. -/
theorem letterStep_bfactor_le (g : EngelCoords) (x : Letter) (s : Symmetry) :
    (2 * (g.u - g.v)
        + (((symmetryAction s) (coordLetterValue x).left).u
            - ((symmetryAction s) (coordLetterValue x).left).v)).natAbs
      ≤ 2 * (g.u.natAbs + g.v.natAbs) + 1 := by
  have huv : ((symmetryAction s) (coordLetterValue x).left).u.natAbs
      + ((symmetryAction s) (coordLetterValue x).left).v.natAbs ≤ 1 :=
    letterStep_le_one x s
  set c := (symmetryAction s) (coordLetterValue x).left
  have e1 : (2 * (g.u - g.v) + (c.u - c.v)).natAbs
      ≤ (2 * (g.u - g.v)).natAbs + (c.u - c.v).natAbs := Int.natAbs_add_le _ _
  have e2 : (2 * (g.u - g.v)).natAbs ≤ 2 * (g.u - g.v).natAbs := by
    rw [Int.natAbs_mul]; simp
  have e3 : (g.u - g.v).natAbs ≤ g.u.natAbs + g.v.natAbs := Int.natAbs_sub_le _ _
  have e4 : (c.u - c.v).natAbs ≤ c.u.natAbs + c.v.natAbs := Int.natAbs_sub_le _ _
  omega

/-- **Reachability box (signed area).** After a word of length `n`, the signed-area coordinate
of the coordinate image has magnitude at most `n²`. -/
theorem area_le_length_sq (w : List Letter) :
    (evalCoordWord w).left.area.natAbs ≤ w.length * w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [evalCoordWord]
  | append_singleton xs x ih =>
      rw [evalCoordWord_append, evalCoordWord_single]
      have hleft : ((evalCoordWord xs) * coordLetterValue x).left
          = (evalCoordWord xs).left
            * (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left := rfl
      rw [hleft]
      set g := (evalCoordWord xs).left
      set c := (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left
      have hca : c.area = 0 := letterStep_area_zero x (evalCoordWord xs).right
      have harea : (g * c).area = g.area + EngelCoords.det2 g c := by
        rw [EngelCoords.mul_area, hca]; ring
      have hdet : (EngelCoords.det2 g c).natAbs ≤ g.u.natAbs + g.v.natAbs :=
        letterStep_det2_le g x (evalCoordWord xs).right
      have hend : g.u.natAbs + g.v.natAbs ≤ xs.length := endpoint_le_length xs
      have ht : (g.area + EngelCoords.det2 g c).natAbs
          ≤ g.area.natAbs + (EngelCoords.det2 g c).natAbs := Int.natAbs_add_le _ _
      rw [harea, List.length_append, List.length_cons, List.length_nil]
      have hn : g.area.natAbs ≤ xs.length * xs.length := ih
      nlinarith [ht, hdet, hend, hn, Nat.zero_le xs.length]

/-- **Reachability box (third barycentric coordinate).** After a word of length `n`, the
`bary3` coordinate of the coordinate image has magnitude at most `3·n³`. -/
theorem bary3_le_length_cube (w : List Letter) :
    (evalCoordWord w).left.bary3.natAbs ≤ 3 * (w.length * w.length * w.length) := by
  induction w using List.reverseRecOn with
  | nil => simp [evalCoordWord]
  | append_singleton xs x ih =>
      rw [evalCoordWord_append, evalCoordWord_single]
      have hleft : ((evalCoordWord xs) * coordLetterValue x).left
          = (evalCoordWord xs).left
            * (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left := rfl
      rw [hleft]
      set g := (evalCoordWord xs).left
      set c := (symmetryAction (evalCoordWord xs).right) (coordLetterValue x).left
      have hca : c.area = 0 := letterStep_area_zero x (evalCoordWord xs).right
      have hcb : c.bary3 = 0 := letterStep_bary3_zero x (evalCoordWord xs).right
      have hbary : (g * c).bary3
          = g.bary3 + (2 * (g.u - g.v) + (c.u - c.v)) * EngelCoords.det2 g c := by
        rw [EngelCoords.mul_bary3, hca, hcb]; ring
      set B := 2 * (g.u - g.v) + (c.u - c.v)
      set D := EngelCoords.det2 g c
      have hD : D.natAbs ≤ g.u.natAbs + g.v.natAbs :=
        letterStep_det2_le g x (evalCoordWord xs).right
      have hB : B.natAbs ≤ 2 * (g.u.natAbs + g.v.natAbs) + 1 :=
        letterStep_bfactor_le g x (evalCoordWord xs).right
      have hend : g.u.natAbs + g.v.natAbs ≤ xs.length := endpoint_le_length xs
      have ht : (g.bary3 + B * D).natAbs ≤ g.bary3.natAbs + (B * D).natAbs :=
        Int.natAbs_add_le _ _
      have hBD : (B * D).natAbs = B.natAbs * D.natAbs := Int.natAbs_mul _ _
      rw [hbary, List.length_append, List.length_cons, List.length_nil]
      have hn : g.bary3.natAbs ≤ 3 * (xs.length * xs.length * xs.length) := ih
      have hBDle : B.natAbs * D.natAbs ≤ (2 * xs.length + 1) * xs.length := by
        have h5 : B.natAbs ≤ 2 * xs.length + 1 := by omega
        have h6 : D.natAbs ≤ xs.length := by omega
        exact Nat.mul_le_mul h5 h6
      nlinarith [ht, hBD, hBDle, hn, Nat.zero_le xs.length]

end VirtuallyEngel
