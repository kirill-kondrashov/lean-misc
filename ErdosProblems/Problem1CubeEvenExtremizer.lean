import ErdosProblems.Problem1CubeOddExtremizer
import ErdosProblems.Problem1CubeDownset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Preimage

open Finset
open scoped FinsetFamily

namespace Erdos1

/-- Lift a family on `Fin n` into the nonzero coordinates of `Fin (n+1)`. -/
def succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  𝒜.map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding

/-- Pull a family on `Fin (n+1)` back to `Fin n` by deleting the `0` coordinate. -/
noncomputable def predFamily {n : ℕ} (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (Finset (Fin n)) :=
  𝒜.image fun s => s.preimage Fin.succ (Fin.succ_injective n).injOn

@[simp]
theorem mem_predFamily {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))} {s : Finset (Fin n)} :
    s ∈ predFamily 𝒜 ↔
      ∃ t ∈ 𝒜, t.preimage Fin.succ (Fin.succ_injective n).injOn = s := by
  unfold predFamily
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

@[simp]
theorem card_succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    #(succFamily 𝒜) = #𝒜 := by
  simp [succFamily]

@[simp]
theorem preimage_map_succEmb {n : ℕ} (s : Finset (Fin n)) :
    (s.map (Fin.succEmb n)).preimage Fin.succ (Fin.succ_injective n).injOn = s := by
  ext x
  simp

theorem predFamily_succFamily {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    predFamily (succFamily 𝒜) = 𝒜 := by
  ext s
  constructor
  · intro hs
    rcases mem_predFamily.mp hs with ⟨t, ht, hts⟩
    rcases Finset.mem_map.mp ht with ⟨u, hu, rfl⟩
    have hmap : (Finset.mapEmbedding (Fin.succEmb n)) u = u.map (Fin.succEmb n) := rfl
    have hpreu :
        ((Finset.mapEmbedding (Fin.succEmb n)).toEmbedding u).preimage Fin.succ
            (Fin.succ_injective n).injOn = u := by
      rw [show ((Finset.mapEmbedding (Fin.succEmb n)).toEmbedding u) = u.map (Fin.succEmb n) by
        exact hmap]
      exact preimage_map_succEmb (n := n) u
    have hsu : s = u := by
      exact hts.symm.trans hpreu
    simpa [hsu] using hu
  · intro hs
    refine mem_predFamily.mpr ⟨s.map (Fin.succEmb n), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨s, hs, rfl⟩
    · simpa using preimage_map_succEmb (n := n) s

theorem zero_not_mem_of_mem_succFamily {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} (hs : s ∈ succFamily 𝒜) :
    (0 : Fin (n + 1)) ∉ s := by
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change (0 : Fin (n + 1)) ∉ t.map (Fin.succEmb n)
  simp

theorem mem_succFamily_iff {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} :
    s ∈ succFamily 𝒜 ↔
      (0 : Fin (n + 1)) ∉ s ∧
      s.preimage Fin.succ (Fin.succ_injective n).injOn ∈ 𝒜 := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨t, ht, hts0⟩
    have hts : t.map (Fin.succEmb n) = s := by
      simpa [Finset.mapEmbedding_apply] using hts0
    constructor
    · exact zero_not_mem_of_mem_succFamily (𝒜 := 𝒜) (s := s) hs
    · have hpre : s.preimage Fin.succ (Fin.succ_injective n).injOn = t := by
        rw [← hts]
        simpa using preimage_map_succEmb (n := n) t
      simpa [hpre] using ht
  · rintro ⟨h0, ht⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨s.preimage Fin.succ (Fin.succ_injective n).injOn, ht, ?_⟩
    have hsImage : (s.preimage Fin.succ (Fin.succ_injective n).injOn).image Fin.succ = s := by
      rw [Finset.image_preimage Fin.succ s (Fin.succ_injective n).injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Fin.exists_succ_eq_of_ne_zero (by
        intro hx0
        exact h0 (hx0 ▸ hx)) with ⟨y, rfl⟩
      exact Set.mem_range_self y
    change (s.preimage Fin.succ (Fin.succ_injective n).injOn).map (Fin.succEmb n) = s
    simpa [Finset.map_eq_image] using hsImage

theorem succFamily_predFamily {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) :
    succFamily (predFamily 𝒜) = 𝒜 := by
  ext s
  constructor
  · intro hs
    rw [mem_succFamily_iff] at hs
    rcases mem_predFamily.mp hs.2 with ⟨t, ht, hts⟩
    have ht0 : (0 : Fin (n + 1)) ∉ t := h0 t ht
    have hsImage : (s.preimage Fin.succ (Fin.succ_injective n).injOn).image Fin.succ = s := by
      rw [Finset.image_preimage Fin.succ s (Fin.succ_injective n).injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Fin.exists_succ_eq_of_ne_zero (by
        intro hx0
        exact hs.1 (hx0 ▸ hx)) with ⟨y, rfl⟩
      exact Set.mem_range_self y
    have htImage : (t.preimage Fin.succ (Fin.succ_injective n).injOn).image Fin.succ = t := by
      rw [Finset.image_preimage Fin.succ t (Fin.succ_injective n).injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Fin.exists_succ_eq_of_ne_zero (by
        intro hx0
        exact ht0 (hx0 ▸ hx)) with ⟨y, rfl⟩
      exact Set.mem_range_self y
    have hEq : s = t := by
      simpa [hsImage, htImage] using
        congrArg (fun u : Finset (Fin n) => u.image Fin.succ) hts.symm
    simpa [hEq] using ht
  · intro hs
    rw [mem_succFamily_iff]
    exact ⟨h0 s hs, mem_predFamily.mpr ⟨s, hs, rfl⟩⟩

theorem card_predFamily {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) :
    #(predFamily 𝒜) = #𝒜 := by
  rw [← card_succFamily (predFamily 𝒜), succFamily_predFamily h0]

theorem predFamily_mono {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin (n + 1)))}
    (hAB : 𝒜 ⊆ ℬ) :
    predFamily 𝒜 ⊆ predFamily ℬ := by
  intro s hs
  rcases mem_predFamily.mp hs with ⟨t, ht, rfl⟩
  exact mem_predFamily.mpr ⟨t, hAB ht, rfl⟩

theorem card_preimage_succ {n : ℕ} {s : Finset (Fin (n + 1))}
    (h0 : (0 : Fin (n + 1)) ∉ s) :
    #(s.preimage Fin.succ (Fin.succ_injective n).injOn) = #s := by
  rw [Finset.card_preimage]
  have hfilter : {x ∈ s | x ∈ Set.range Fin.succ} = s := by
    apply Finset.filter_true_of_mem
    intro x hx
    rcases Fin.exists_succ_eq_of_ne_zero (by
      intro hx0
      exact h0 (hx0 ▸ hx)) with ⟨y, rfl⟩
    exact Set.mem_range_self y
  rw [hfilter]

theorem nonMemberSubfamily_eq_self_of_forall_not_mem {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} {a : α} (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    𝒜.nonMemberSubfamily a = 𝒜 := by
  ext s
  rw [mem_nonMemberSubfamily]
  constructor
  · exact fun hs => hs.1
  · intro hs
    exact ⟨hs, h𝒜 s hs⟩

theorem memberSubfamily_eq_empty_of_forall_not_mem {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} {a : α} (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    𝒜.memberSubfamily a = ∅ := by
  ext s
  rw [mem_memberSubfamily]
  constructor
  · intro hs
    exact (h𝒜 _ hs.1 (mem_insert_self _ _)).elim
  · simp

theorem isDownSetFamily_predFamily {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (predFamily 𝒜) := by
  intro s t hts hs
  rcases mem_predFamily.mp hs with ⟨u, hu, hus⟩
  have hu0 : (0 : Fin (n + 1)) ∉ u := h0 u hu
  have huImage : (u.preimage Fin.succ (Fin.succ_injective n).injOn).image Fin.succ = u := by
    rw [Finset.image_preimage Fin.succ u (Fin.succ_injective n).injOn]
    apply Finset.filter_true_of_mem
    intro x hx
    rcases Fin.exists_succ_eq_of_ne_zero (by
      intro hx0
      exact hu0 (hx0 ▸ hx)) with ⟨y, rfl⟩
    exact Set.mem_range_self y
  have huEq : s.map (Fin.succEmb n) = u := by
    simpa [Finset.map_eq_image, huImage] using
      congrArg (fun v : Finset (Fin n) => v.image Fin.succ) hus.symm
  refine mem_predFamily.mpr ⟨t.map (Fin.succEmb n), ?_, by
    simpa using preimage_map_succEmb (n := n) t⟩
  apply h𝒜
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyu : (Fin.succEmb n) y ∈ u := by
      have hys : (Fin.succEmb n) y ∈ s.map (Fin.succEmb n) :=
        Finset.mem_map.mpr ⟨y, hts hy, rfl⟩
      simpa [huEq] using hys
    exact hyu
  · exact hu

/-- Lift a family on `Fin n` into `Fin (n+1)` while skipping a pivot coordinate `a`. -/
def succAboveFamily {n : ℕ} (a : Fin (n + 1)) (𝒜 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (n + 1))) :=
  𝒜.map (Finset.mapEmbedding (Fin.succAboveEmb a)).toEmbedding

/-- Pull a family on `Fin (n+1)` back to `Fin n` by deleting a pivot coordinate `a`. -/
noncomputable def predAboveFamily {n : ℕ} (a : Fin (n + 1)) (𝒜 : Finset (Finset (Fin (n + 1)))) :
    Finset (Finset (Fin n)) :=
  𝒜.image fun s => s.preimage a.succAbove a.succAboveEmb.injective.injOn

@[simp]
theorem mem_predAboveFamily {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin (n + 1)))} {s : Finset (Fin n)} :
    s ∈ predAboveFamily a 𝒜 ↔
      ∃ t ∈ 𝒜, t.preimage a.succAbove a.succAboveEmb.injective.injOn = s := by
  unfold predAboveFamily
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

@[simp]
theorem card_succAboveFamily {n : ℕ} (a : Fin (n + 1)) (𝒜 : Finset (Finset (Fin n))) :
    #(succAboveFamily a 𝒜) = #𝒜 := by
  simp [succAboveFamily]

@[simp]
theorem preimage_map_succAboveEmb {n : ℕ} (a : Fin (n + 1)) (s : Finset (Fin n)) :
    (s.map (Fin.succAboveEmb a)).preimage a.succAbove a.succAboveEmb.injective.injOn = s := by
  ext x
  simp

theorem pivot_not_mem_of_mem_succAboveFamily {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin n))} {s : Finset (Fin (n + 1))}
    (hs : s ∈ succAboveFamily a 𝒜) :
    a ∉ s := by
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change a ∉ t.map (Fin.succAboveEmb a)
  simp [Fin.succAbove_ne]

theorem mem_succAboveFamily_iff {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin n))} {s : Finset (Fin (n + 1))} :
    s ∈ succAboveFamily a 𝒜 ↔
      a ∉ s ∧
      s.preimage a.succAbove a.succAboveEmb.injective.injOn ∈ 𝒜 := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨t, ht, hts0⟩
    have hts : t.map (Fin.succAboveEmb a) = s := by
      simpa [Finset.mapEmbedding_apply] using hts0
    constructor
    · exact pivot_not_mem_of_mem_succAboveFamily (a := a) hs
    · have hpre : s.preimage a.succAbove a.succAboveEmb.injective.injOn = t := by
        rw [← hts]
        simpa using preimage_map_succAboveEmb a t
      simpa [hpre] using ht
  · rintro ⟨ha, hsA⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨s.preimage a.succAbove a.succAboveEmb.injective.injOn, hsA, ?_⟩
    have hsImage :
        (s.preimage a.succAbove a.succAboveEmb.injective.injOn).image a.succAbove = s := by
      rw [Finset.image_preimage a.succAbove s a.succAboveEmb.injective.injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        exact ha (hxa ▸ hx)
      simpa [Set.mem_range] using (Fin.exists_succAbove_eq_iff (x := a) (y := x)).2 hxa
    change (s.preimage a.succAbove a.succAboveEmb.injective.injOn).map (Fin.succAboveEmb a) = s
    simpa [Finset.map_eq_image] using hsImage

theorem predAboveFamily_succAboveFamily {n : ℕ} (a : Fin (n + 1))
    (𝒜 : Finset (Finset (Fin n))) :
    predAboveFamily a (succAboveFamily a 𝒜) = 𝒜 := by
  ext s
  constructor
  · intro hs
    rcases mem_predAboveFamily.mp hs with ⟨t, ht, hts⟩
    rcases Finset.mem_map.mp ht with ⟨u, hu, rfl⟩
    have hmap : (Finset.mapEmbedding (Fin.succAboveEmb a)) u = u.map (Fin.succAboveEmb a) := rfl
    have hpreu :
        ((Finset.mapEmbedding (Fin.succAboveEmb a)).toEmbedding u).preimage a.succAbove
            a.succAboveEmb.injective.injOn = u := by
      rw [show ((Finset.mapEmbedding (Fin.succAboveEmb a)).toEmbedding u) = u.map (Fin.succAboveEmb a) by
        exact hmap]
      exact preimage_map_succAboveEmb a u
    have hsu : s = u := by
      exact hts.symm.trans hpreu
    simpa [hsu] using hu
  · intro hs
    refine mem_predAboveFamily.mpr ⟨s.map (Fin.succAboveEmb a), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨s, hs, rfl⟩
    · simpa using preimage_map_succAboveEmb a s

theorem succAboveFamily_predAboveFamily {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) :
    succAboveFamily a (predAboveFamily a 𝒜) = 𝒜 := by
  ext s
  constructor
  · intro hs
    rw [mem_succAboveFamily_iff (a := a)] at hs
    rcases mem_predAboveFamily.mp hs.2 with ⟨t, ht, hts⟩
    have hta : a ∉ t := ha t ht
    have hsImage :
        (s.preimage a.succAbove a.succAboveEmb.injective.injOn).image a.succAbove = s := by
      rw [Finset.image_preimage a.succAbove s a.succAboveEmb.injective.injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        exact hs.1 (hxa ▸ hx)
      simpa [Set.mem_range] using (Fin.exists_succAbove_eq_iff (x := a) (y := x)).2 hxa
    have htImage :
        (t.preimage a.succAbove a.succAboveEmb.injective.injOn).image a.succAbove = t := by
      rw [Finset.image_preimage a.succAbove t a.succAboveEmb.injective.injOn]
      apply Finset.filter_true_of_mem
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        exact hta (hxa ▸ hx)
      simpa [Set.mem_range] using (Fin.exists_succAbove_eq_iff (x := a) (y := x)).2 hxa
    have hEq : s = t := by
      simpa [hsImage, htImage] using
        congrArg (fun u : Finset (Fin n) => u.image a.succAbove) hts.symm
    simpa [hEq] using ht
  · intro hs
    rw [mem_succAboveFamily_iff (a := a)]
    exact ⟨ha s hs, mem_predAboveFamily.mpr ⟨s, hs, rfl⟩⟩

theorem card_predAboveFamily {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) :
    #(predAboveFamily a 𝒜) = #𝒜 := by
  rw [← card_succAboveFamily a (predAboveFamily a 𝒜), succAboveFamily_predAboveFamily ha]

theorem predAboveFamily_mono {n : ℕ} {a : Fin (n + 1)}
    {𝒜 ℬ : Finset (Finset (Fin (n + 1)))}
    (hAB : 𝒜 ⊆ ℬ) :
    predAboveFamily a 𝒜 ⊆ predAboveFamily a ℬ := by
  intro s hs
  rcases mem_predAboveFamily.mp hs with ⟨t, ht, rfl⟩
  exact mem_predAboveFamily.mpr ⟨t, hAB ht, rfl⟩

theorem preimage_erase_succAbove {n : ℕ} (a : Fin (n + 1)) (s : Finset (Fin (n + 1)))
    (i : Fin n) :
    (s.erase (a.succAbove i)).preimage a.succAbove a.succAboveEmb.injective.injOn =
      (s.preimage a.succAbove a.succAboveEmb.injective.injOn).erase i := by
  ext x
  simp [Fin.succAbove_right_inj]

theorem isDownSetFamily_predAboveFamily {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (predAboveFamily a 𝒜) := by
  intro s t hts hs
  rcases mem_predAboveFamily.mp hs with ⟨u, hu, hus⟩
  have hua : a ∉ u := ha u hu
  have huImage :
      (u.preimage a.succAbove a.succAboveEmb.injective.injOn).image a.succAbove = u := by
    rw [Finset.image_preimage a.succAbove u a.succAboveEmb.injective.injOn]
    apply Finset.filter_true_of_mem
    intro x hx
    have hxa : x ≠ a := by
      intro hxa
      exact hua (hxa ▸ hx)
    simpa [Set.mem_range] using (Fin.exists_succAbove_eq_iff (x := a) (y := x)).2 hxa
  have huEq : s.map (Fin.succAboveEmb a) = u := by
    simpa [Finset.map_eq_image, huImage] using
      congrArg (fun v : Finset (Fin n) => v.image a.succAbove) hus.symm
  refine mem_predAboveFamily.mpr ⟨t.map (Fin.succAboveEmb a), ?_, by
    simpa using preimage_map_succAboveEmb a t⟩
  apply h𝒜
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyu : a.succAboveEmb y ∈ u := by
      have hys : a.succAboveEmb y ∈ s.map (Fin.succAboveEmb a) :=
        Finset.mem_map.mpr ⟨y, hts hy, rfl⟩
      simpa [huEq] using hys
    exact hyu
  · exact hu

theorem mem_positiveBoundary_succAboveFamily_iff {n : ℕ} {a : Fin (n + 1)}
    {𝒜 : Finset (Finset (Fin n))} {s : Finset (Fin (n + 1))} (ha : a ∉ s) :
    s ∈ positiveBoundary (succAboveFamily a 𝒜) ↔
      s.preimage a.succAbove a.succAboveEmb.injective.injOn ∈ positiveBoundary 𝒜 := by
  constructor
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, b, hb, hsErase⟩
    have hba : b ≠ a := by
      intro hba
      exact ha (hba ▸ hb)
    rcases Fin.exists_succAbove_eq hba with ⟨c, rfl⟩
    refine mem_positiveBoundary.mpr ⟨?_, c, ?_, ?_⟩
    · intro hsPre
      exact hsNot ((mem_succAboveFamily_iff (a := a) (s := s)).2 ⟨ha, hsPre⟩)
    · simpa using hb
    · have hsErase' :=
        (mem_succAboveFamily_iff (a := a) (s := s.erase (a.succAbove c))).1 hsErase
      simpa [preimage_erase_succAbove] using hsErase'.2
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, c, hc, hsErase⟩
    refine mem_positiveBoundary.mpr ⟨?_, a.succAbove c, ?_, ?_⟩
    · intro hsSucc
      exact hsNot ((mem_succAboveFamily_iff (a := a) (s := s)).1 hsSucc).2
    · simpa using hc
    · refine (mem_succAboveFamily_iff (a := a) (s := s.erase (a.succAbove c))).2 ⟨?_, ?_⟩
      · intro hmem
        exact ha (Finset.mem_of_mem_erase hmem)
      · simpa [preimage_erase_succAbove] using hsErase

theorem nonMemberSubfamily_positiveBoundary_succAboveFamily {n : ℕ}
    (a : Fin (n + 1)) (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succAboveFamily a 𝒜)).nonMemberSubfamily a =
      succAboveFamily a (positiveBoundary 𝒜) := by
  ext s
  constructor
  · intro hs
    rw [mem_nonMemberSubfamily] at hs
    rw [mem_succAboveFamily_iff (a := a)]
    exact ⟨hs.2, (mem_positiveBoundary_succAboveFamily_iff (a := a) hs.2).1 hs.1⟩
  · intro hs
    rw [mem_succAboveFamily_iff (a := a)] at hs
    rw [mem_nonMemberSubfamily]
    exact ⟨(mem_positiveBoundary_succAboveFamily_iff (a := a) hs.1).2 hs.2, hs.1⟩

theorem memberSubfamily_positiveBoundary_succAboveFamily {n : ℕ}
    (a : Fin (n + 1)) (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succAboveFamily a 𝒜)).memberSubfamily a =
      succAboveFamily a 𝒜 := by
  ext s
  rw [mem_memberSubfamily, mem_succAboveFamily_iff (a := a)]
  constructor
  · intro hs
    have hsa : a ∉ s := hs.2
    rcases mem_positiveBoundary.mp hs.1 with ⟨hsNot, b, hb, hsErase⟩
    have hba : b = a := by
      by_contra hba
      have hba' : a ≠ b := by simpa [eq_comm] using hba
      have haErase : a ∈ (insert a s).erase b := by
        simp [hsa, hba']
      exact (pivot_not_mem_of_mem_succAboveFamily (a := a) hsErase) haErase
    have hsSucc : s ∈ succAboveFamily a 𝒜 := by
      simpa [hba, hsa] using hsErase
    exact ⟨hsa, (mem_succAboveFamily_iff (a := a) (s := s)).1 hsSucc |>.2⟩
  · rintro ⟨hsa, hsA⟩
    refine ⟨?_, hsa⟩
    refine mem_positiveBoundary.mpr ⟨?_, a, by simp, ?_⟩
    · intro hsInsert
      exact (pivot_not_mem_of_mem_succAboveFamily (a := a) hsInsert) (mem_insert_self _ _)
    · have hsSucc : s ∈ succAboveFamily a 𝒜 :=
        (mem_succAboveFamily_iff (a := a) (s := s)).2 ⟨hsa, hsA⟩
      simpa [hsa] using hsSucc

theorem nonMemberSubfamily_positiveBoundary_eq_succAboveFamily_positiveBoundary_predAboveFamily
    {n : ℕ} {a : Fin (n + 1)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) :
    (positiveBoundary 𝒜).nonMemberSubfamily a =
      succAboveFamily a (positiveBoundary (predAboveFamily a 𝒜)) := by
  simpa [succAboveFamily_predAboveFamily (a := a) ha] using
    (nonMemberSubfamily_positiveBoundary_succAboveFamily a (predAboveFamily a 𝒜))

theorem card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predAboveFamily
    {n : ℕ} {a : Fin (n + 1)} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (ha : ∀ s ∈ 𝒜, a ∉ s) :
    #((positiveBoundary 𝒜).nonMemberSubfamily a) =
      #(positiveBoundary (predAboveFamily a 𝒜)) := by
  rw [nonMemberSubfamily_positiveBoundary_eq_succAboveFamily_positiveBoundary_predAboveFamily ha,
    card_succAboveFamily]

theorem predAboveFamily_memberSubfamily_subset_predAboveFamily_nonMemberSubfamily {n : ℕ}
    {a : Fin (n + 1)} {𝒜 : Finset (Finset (Fin (n + 1)))} (h𝒜 : IsDownSetFamily 𝒜) :
    predAboveFamily a (𝒜.memberSubfamily a) ⊆ predAboveFamily a (𝒜.nonMemberSubfamily a) := by
  apply predAboveFamily_mono
  exact h𝒜.memberSubfamily_subset_nonMemberSubfamily (a := a)

theorem preimage_erase_succ {n : ℕ} (s : Finset (Fin (n + 1))) (i : Fin n) :
    (s.erase i.succ).preimage Fin.succ (Fin.succ_injective n).injOn =
      (s.preimage Fin.succ (Fin.succ_injective n).injOn).erase i := by
  ext x
  simp

theorem mem_positiveBoundary_succFamily_iff {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    {s : Finset (Fin (n + 1))} (h0 : (0 : Fin (n + 1)) ∉ s) :
    s ∈ positiveBoundary (succFamily 𝒜) ↔
      s.preimage Fin.succ (Fin.succ_injective n).injOn ∈ positiveBoundary 𝒜 := by
  constructor
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, b, hb, hsErase⟩
    have hb0 : b ≠ 0 := by
      intro hb0
      exact h0 (hb0 ▸ hb)
    rcases Fin.exists_succ_eq_of_ne_zero hb0 with ⟨c, rfl⟩
    refine mem_positiveBoundary.mpr ⟨?_, c, ?_, ?_⟩
    · intro hsPre
      exact hsNot ((mem_succFamily_iff).2 ⟨h0, hsPre⟩)
    · simpa using hb
    · have hsErase' := (mem_succFamily_iff (s := s.erase c.succ)).1 hsErase
      simpa [preimage_erase_succ] using hsErase'.2
  · intro hs
    rcases mem_positiveBoundary.mp hs with ⟨hsNot, c, hc, hsErase⟩
    refine mem_positiveBoundary.mpr ⟨?_, c.succ, ?_, ?_⟩
    · intro hsSucc
      exact hsNot ((mem_succFamily_iff (s := s)).1 hsSucc).2
    · simpa using hc
    · refine (mem_succFamily_iff (s := s.erase c.succ)).2 ⟨?_, ?_⟩
      · intro hmem
        exact h0 (Finset.mem_of_mem_erase hmem)
      · simpa [preimage_erase_succ] using hsErase

theorem nonMemberSubfamily_positiveBoundary_succFamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succFamily 𝒜)).nonMemberSubfamily 0 = succFamily (positiveBoundary 𝒜) := by
  ext s
  by_cases h0 : (0 : Fin (n + 1)) ∈ s
  · simp [mem_nonMemberSubfamily, h0, mem_succFamily_iff]
  · rw [mem_nonMemberSubfamily, mem_succFamily_iff]
    simp [h0, mem_positiveBoundary_succFamily_iff h0]

theorem memberSubfamily_positiveBoundary_succFamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin n))) :
    (positiveBoundary (succFamily 𝒜)).memberSubfamily 0 = succFamily 𝒜 := by
  ext s
  rw [mem_memberSubfamily, mem_succFamily_iff]
  constructor
  · rintro ⟨hsPb, h0⟩
    rcases mem_positiveBoundary.mp hsPb with ⟨-, b, hb, hsErase⟩
    have hb0 : b = 0 := by
      by_contra hne
      have hmem0 : (0 : Fin (n + 1)) ∈ (insert 0 s).erase b := by
        rw [mem_erase]
        exact ⟨fun h => hne h.symm, mem_insert_self 0 s⟩
      exact zero_not_mem_of_mem_succFamily hsErase hmem0
    subst hb0
    have hsSucc : s ∈ succFamily 𝒜 := by
      simpa [h0] using hsErase
    exact (mem_succFamily_iff).1 hsSucc
  · rintro ⟨h0, hsA⟩
    refine ⟨mem_positiveBoundary.mpr ?_, h0⟩
    refine ⟨?_, 0, mem_insert_self 0 s, ?_⟩
    · intro hsInsert
      exact (mem_succFamily_iff.mp hsInsert).1 (mem_insert_self 0 s)
    · have hsSucc : s ∈ succFamily 𝒜 := (mem_succFamily_iff).2 ⟨h0, hsA⟩
      simpa [h0] using hsSucc

theorem card_positiveBoundary_succFamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin n))) :
    #(positiveBoundary (succFamily 𝒜)) = #(positiveBoundary 𝒜) + #𝒜 := by
  rw [← Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0
    (positiveBoundary (succFamily 𝒜))]
  rw [memberSubfamily_positiveBoundary_succFamily,
    nonMemberSubfamily_positiveBoundary_succFamily,
    card_succFamily, card_succFamily]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem nonMemberSubfamily_positiveBoundary_eq_succFamily_positiveBoundary_predFamily
    {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) :
    (positiveBoundary 𝒜).nonMemberSubfamily 0 =
      succFamily (positiveBoundary (predFamily 𝒜)) := by
  simpa [succFamily_predFamily h0] using
    (nonMemberSubfamily_positiveBoundary_succFamily (predFamily 𝒜))

theorem card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predFamily
    {n : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))}
    (h0 : ∀ s ∈ 𝒜, (0 : Fin (n + 1)) ∉ s) :
    #((positiveBoundary 𝒜).nonMemberSubfamily 0) =
      #(positiveBoundary (predFamily 𝒜)) := by
  rw [nonMemberSubfamily_positiveBoundary_eq_succFamily_positiveBoundary_predFamily h0,
    card_succFamily]

theorem card_predFamily_nonMemberSubfamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    #(predFamily (𝒜.nonMemberSubfamily 0)) = #(𝒜.nonMemberSubfamily 0) := by
  apply card_predFamily
  intro s hs
  exact (mem_nonMemberSubfamily.mp hs).2

theorem card_predFamily_memberSubfamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    #(predFamily (𝒜.memberSubfamily 0)) = #(𝒜.memberSubfamily 0) := by
  apply card_predFamily
  intro s hs
  exact (mem_memberSubfamily.mp hs).2

theorem isDownSetFamily_predFamily_nonMemberSubfamily {n : ℕ}
    {𝒜 : Finset (Finset (Fin (n + 1)))} (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (predFamily (𝒜.nonMemberSubfamily 0)) := by
  apply isDownSetFamily_predFamily
  · intro s hs
    exact (mem_nonMemberSubfamily.mp hs).2
  · exact isDownSetFamily_nonMemberSubfamily h𝒜 0

theorem isDownSetFamily_predFamily_memberSubfamily {n : ℕ}
    {𝒜 : Finset (Finset (Fin (n + 1)))} (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (predFamily (𝒜.memberSubfamily 0)) := by
  apply isDownSetFamily_predFamily
  · intro s hs
    exact (mem_memberSubfamily.mp hs).2
  · exact isDownSetFamily_memberSubfamily h𝒜 0

theorem card_positiveBoundary_predFamily_nonMemberSubfamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    #(positiveBoundary (predFamily (𝒜.nonMemberSubfamily 0))) =
      #((positiveBoundary (𝒜.nonMemberSubfamily 0)).nonMemberSubfamily 0) := by
  symm
  apply card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predFamily
  intro s hs
  exact (mem_nonMemberSubfamily.mp hs).2

theorem card_positiveBoundary_predFamily_memberSubfamily {n : ℕ}
    (𝒜 : Finset (Finset (Fin (n + 1)))) :
    #(positiveBoundary (predFamily (𝒜.memberSubfamily 0))) =
      #((positiveBoundary (𝒜.memberSubfamily 0)).nonMemberSubfamily 0) := by
  symm
  apply card_nonMemberSubfamily_positiveBoundary_eq_card_positiveBoundary_predFamily
  intro s hs
  exact (mem_memberSubfamily.mp hs).2

theorem predFamily_memberSubfamily_subset_predFamily_nonMemberSubfamily {n : ℕ}
    {𝒜 : Finset (Finset (Fin (n + 1)))} (h𝒜 : IsDownSetFamily 𝒜) :
    predFamily (𝒜.memberSubfamily 0) ⊆ predFamily (𝒜.nonMemberSubfamily 0) := by
  apply predFamily_mono
  exact h𝒜.memberSubfamily_subset_nonMemberSubfamily (a := 0)

theorem slice_succFamily {n r : ℕ} {𝒜 : Finset (Finset (Fin n))} :
    (succFamily 𝒜) # r = succFamily (𝒜 # r) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_slice.mp hs with ⟨hsSucc, hsCard⟩
    rw [mem_succFamily_iff] at hsSucc ⊢
    refine ⟨hsSucc.1, ?_⟩
    rw [Finset.mem_slice]
    refine ⟨hsSucc.2, ?_⟩
    simpa [card_preimage_succ hsSucc.1] using hsCard
  · intro hs
    rw [mem_succFamily_iff] at hs
    rw [Finset.mem_slice]
    refine ⟨?_, ?_⟩
    · exact (mem_succFamily_iff).2 ⟨hs.1, (Finset.mem_slice.mp hs.2).1⟩
    · have hpre := (Finset.mem_slice.mp hs.2).2
      simpa [card_preimage_succ hs.1] using hpre

theorem card_slice_succFamily {n r : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    #((succFamily 𝒜) # r) = #(𝒜 # r) := by
  rw [slice_succFamily, card_succFamily]

theorem nonMemberSubfamily_slice {n r : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))} :
    (𝒜 # r).nonMemberSubfamily 0 = (𝒜.nonMemberSubfamily 0) # r := by
  ext s
  constructor
  · intro hs
    rcases mem_nonMemberSubfamily.mp hs with ⟨hsSlice, hs0⟩
    rcases Finset.mem_slice.mp hsSlice with ⟨hsA, hsCard⟩
    exact Finset.mem_slice.mpr ⟨mem_nonMemberSubfamily.mpr ⟨hsA, hs0⟩, hsCard⟩
  · intro hs
    rcases Finset.mem_slice.mp hs with ⟨hsNon, hsCard⟩
    rcases mem_nonMemberSubfamily.mp hsNon with ⟨hsA, hs0⟩
    exact mem_nonMemberSubfamily.mpr ⟨Finset.mem_slice.mpr ⟨hsA, hsCard⟩, hs0⟩

theorem memberSubfamily_slice_succ {n r : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))} :
    (𝒜 # (r + 1)).memberSubfamily 0 = (𝒜.memberSubfamily 0) # r := by
  ext s
  constructor
  · intro hs
    rcases mem_memberSubfamily.mp hs with ⟨hsSlice, hs0⟩
    rcases Finset.mem_slice.mp hsSlice with ⟨hsA, hsCard⟩
    refine Finset.mem_slice.mpr ⟨mem_memberSubfamily.mpr ⟨hsA, hs0⟩, ?_⟩
    rw [Finset.card_insert_of_notMem hs0] at hsCard
    omega
  · intro hs
    rcases Finset.mem_slice.mp hs with ⟨hsMember, hsCard⟩
    rcases mem_memberSubfamily.mp hsMember with ⟨hsA, hs0⟩
    refine mem_memberSubfamily.mpr ⟨Finset.mem_slice.mpr ⟨hsA, ?_⟩, hs0⟩
    have hsCard' : s.card + 1 = r + 1 := by
      omega
    simpa [Finset.card_insert_of_notMem hs0, add_comm] using hsCard'

theorem card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    {n r : ℕ} {𝒜 : Finset (Finset (Fin (n + 1)))} :
    #(𝒜 # (r + 1)) =
      #((𝒜.nonMemberSubfamily 0) # (r + 1)) + #((𝒜.memberSubfamily 0) # r) := by
  calc
    #(𝒜 # (r + 1)) =
      #(((𝒜 # (r + 1)).memberSubfamily 0)) + #(((𝒜 # (r + 1)).nonMemberSubfamily 0)) := by
        symm
        exact Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0 (𝒜 # (r + 1))
    _ = #((𝒜.memberSubfamily 0) # r) + #((𝒜.nonMemberSubfamily 0) # (r + 1)) := by
        rw [memberSubfamily_slice_succ, nonMemberSubfamily_slice]
    _ = #((𝒜.nonMemberSubfamily 0) # (r + 1)) + #((𝒜.memberSubfamily 0) # r) := by
        ac_rfl

theorem card_one_slice_succFamily_powerset (n : ℕ) :
    #((succFamily ((Finset.univ : Finset (Fin n)).powerset)) # 1) = n := by
  have hslice :
      (((Finset.univ : Finset (Fin n)).powerset) # 1) =
        (Finset.univ : Finset (Fin n)).powersetCard 1 := by
    ext s
    rw [Finset.mem_slice, Finset.mem_powersetCard]
    simp
  rw [card_slice_succFamily]
  rw [hslice, Finset.card_powersetCard]
  simpa using (Finset.card_univ : #(Finset.univ : Finset (Fin n)) = n)

theorem exists_odd_halfCube_downSet_with_nonfull_one_slice (m : ℕ) (hm : 0 < m) :
    ∃ 𝒟 : Finset (Finset (Fin (2 * m + 1))),
      𝒟.Nonempty ∧
      IsDownSetFamily 𝒟 ∧
      𝒟.card = 2 ^ (2 * m) ∧
      #(𝒟 # 1) < Nat.choose (2 * m + 1) 1 := by
  refine ⟨succFamily ((Finset.univ : Finset (Fin (2 * m))).powerset), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcard : 0 < #(succFamily ((Finset.univ : Finset (Fin (2 * m))).powerset)) := by
      rw [card_succFamily, Finset.card_powerset]
      positivity
    exact Finset.card_pos.mp hcard
  · intro s t hts hs
    change s ∈ succFamily ((Finset.univ : Finset (Fin (2 * m))).powerset) at hs
    change t ∈ succFamily ((Finset.univ : Finset (Fin (2 * m))).powerset)
    have hsData := mem_succFamily_iff.mp hs
    refine (mem_succFamily_iff).2 ⟨fun ht0 => hsData.1 (hts ht0), ?_⟩
    simp
  · rw [card_succFamily, Finset.card_powerset]
    simpa using congrArg (fun k => 2 ^ k)
      (Finset.card_univ : #(Finset.univ : Finset (Fin (2 * m))) = 2 * m)
  · rw [card_one_slice_succFamily_powerset, Nat.choose_one_right]
    omega

theorem isDownSetFamily_succFamily {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsDownSetFamily 𝒜) :
    IsDownSetFamily (succFamily 𝒜) := by
  intro s t hts hs
  change t ∈ succFamily 𝒜
  change s ∈ succFamily 𝒜 at hs
  have hsData := mem_succFamily_iff.mp hs
  have ht0 : (0 : Fin (n + 1)) ∉ t := by
    intro ht0
    exact hsData.1 (hts ht0)
  refine (mem_succFamily_iff).2 ⟨ht0, ?_⟩
  exact h𝒜 ((Finset.monotone_preimage (Fin.succ_injective n)) hts) hsData.2

theorem sized_succFamily {n r : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r) :
    (succFamily 𝒜 : Set (Finset (Fin (n + 1)))).Sized r := by
  intro s hs
  rcases mem_succFamily_iff.mp hs with ⟨h0, hsA⟩
  simpa [card_preimage_succ h0] using h𝒜 hsA

theorem isAntichain_succFamily_oddMiddleLayer (m : ℕ) :
    IsAntichain (· ⊆ ·) (succFamily (oddMiddleLayer m) : Set (Finset (Fin (2 * m + 2)))) := by
  exact (sized_succFamily (n := 2 * m + 1) (r := m + 1)
    (by
      simpa [oddMiddleLayer] using
        (Set.sized_powersetCard (Finset.univ : Finset (Fin (2 * m + 1))) (m + 1)))).isAntichain

/-- A sharp half-cube witness in even dimension: two disjoint copies of the odd lower half, split
according to whether the distinguished coordinate `0` is absent or present. -/
def evenLowerHalfFamily (m : ℕ) : Finset (Finset (Fin (2 * m + 2))) :=
  let base := succFamily (oddLowerHalfFamily m)
  base ∪ base.image (insert 0)

theorem nonMemberSubfamily_evenLowerHalfFamily (m : ℕ) :
    (evenLowerHalfFamily m).nonMemberSubfamily 0 = succFamily (oddLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [evenLowerHalfFamily, Finset.nonMemberSubfamily_union, nonMemberSubfamily_image_insert]
  simpa [base] using nonMemberSubfamily_eq_self_of_forall_not_mem hbase

theorem memberSubfamily_evenLowerHalfFamily (m : ℕ) :
    (evenLowerHalfFamily m).memberSubfamily 0 = succFamily (oddLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  rw [evenLowerHalfFamily, Finset.memberSubfamily_union]
  rw [memberSubfamily_eq_empty_of_forall_not_mem hbase, empty_union]
  simpa [base] using Finset.memberSubfamily_image_insert hbase

theorem mem_evenLowerHalfFamily_iff_of_zero_not_mem (m : ℕ) {s : Finset (Fin (2 * m + 2))}
    (hs0 : (0 : Fin (2 * m + 2)) ∉ s) :
    s ∈ evenLowerHalfFamily m ↔
      s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈ oddLowerHalfFamily m := by
  rw [evenLowerHalfFamily, mem_union, mem_succFamily_iff]
  constructor
  · intro hs
    rcases hs with hsBase | hsInsert
    · exact hsBase.2
    · rcases Finset.mem_image.mp hsInsert with ⟨t, -, hts⟩
      exact (hs0 (hts ▸ mem_insert_self 0 t)).elim
  · intro hs
    left
    exact ⟨hs0, hs⟩

theorem isDownSetFamily_evenLowerHalfFamily (m : ℕ) :
    IsDownSetFamily (evenLowerHalfFamily m) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : IsDownSetFamily base :=
    isDownSetFamily_succFamily (isDownSetFamily_oddLowerHalfFamily m)
  intro s t hts hs
  change t ∈ evenLowerHalfFamily m
  change s ∈ evenLowerHalfFamily m at hs
  rw [evenLowerHalfFamily, mem_union] at hs ⊢
  rcases hs with hsBase | hsInsert
  · exact Or.inl (hbase hts hsBase)
  · rcases Finset.mem_image.mp hsInsert with ⟨u, hu, rfl⟩
    by_cases ht0 : (0 : Fin (2 * m + 2)) ∈ t
    · right
      refine Finset.mem_image.mpr ⟨t.erase 0, ?_, insert_erase ht0⟩
      apply hbase
      · intro x hx
        have hxt : x ∈ t := Finset.mem_of_mem_erase hx
        have hsx : x ∈ insert 0 u := hts hxt
        rw [Finset.mem_insert] at hsx
        rcases hsx with hx0 | hxu
        · exact ((notMem_erase 0 t) (hx0 ▸ hx)).elim
        · exact hxu
      · exact hu
    · left
      apply hbase
      · intro x hx
        have hsx : x ∈ insert 0 u := hts hx
        rw [Finset.mem_insert] at hsx
        rcases hsx with hx0 | hxu
        · exact (ht0 (hx0 ▸ hx)).elim
        · exact hxu
      · exact hu

theorem card_evenLowerHalfFamily_eq_half_cube (m : ℕ) :
    (evenLowerHalfFamily m).card = 2 ^ (2 * m + 1) := by
  let base := succFamily (oddLowerHalfFamily m)
  have hbase : ∀ s ∈ base, (0 : Fin (2 * m + 2)) ∉ s := by
    intro s hs
    exact zero_not_mem_of_mem_succFamily hs
  have hdisj : Disjoint base (base.image (insert 0)) := by
    refine Finset.disjoint_left.mpr ?_
    intro s hsBase hsImage
    have hnot : (0 : Fin (2 * m + 2)) ∉ s := hbase s hsBase
    rcases Finset.mem_image.mp hsImage with ⟨t, ht, rfl⟩
    exact hnot (mem_insert_self _ _)
  rw [evenLowerHalfFamily, Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_image_of_injOn]
  · dsimp [base]
    rw [card_succFamily, card_oddLowerHalfFamily_eq_half_cube]
    ring_nf
  · intro s hs t ht hst
    have hs0 : (0 : Fin (2 * m + 2)) ∉ s := hbase s hs
    have ht0 : (0 : Fin (2 * m + 2)) ∉ t := hbase t ht
    have hErase := congrArg (fun u : Finset (Fin (2 * m + 2)) => u.erase 0) hst
    simpa [hs0, ht0] using hErase

theorem card_slice_evenLowerHalfFamily_eq_choose {m r : ℕ} (hr : r ≤ m) :
    #((evenLowerHalfFamily m) # r) = Nat.choose (2 * m + 2) r := by
  cases r with
  | zero =>
      rw [Nat.choose_zero_right]
      refine Finset.card_eq_one.mpr ?_
      refine ⟨∅, ?_⟩
      ext s
      rw [Finset.mem_slice]
      constructor
      · rintro ⟨_, hsCard⟩
        have hsEmpty : s = ∅ := Finset.card_eq_zero.mp hsCard
        simpa [hsEmpty]
      · intro hs
        have hempty : (∅ : Finset (Fin (2 * m + 2))) ∈ evenLowerHalfFamily m := by
          rw [evenLowerHalfFamily, mem_union]
          left
          rw [mem_succFamily_iff]
          refine ⟨by simp, ?_⟩
          simpa [mem_oddLowerHalfFamily]
        have hsEmpty : s = ∅ := by simpa using hs
        subst hsEmpty
        exact ⟨hempty, by simp⟩
  | succ r' =>
      calc
        #((evenLowerHalfFamily m) # (r' + 1))
          = #(((evenLowerHalfFamily m).nonMemberSubfamily 0) # (r' + 1)) +
              #(((evenLowerHalfFamily m).memberSubfamily 0) # r') := by
                exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
        _ = #((oddLowerHalfFamily m) # (r' + 1)) + #((oddLowerHalfFamily m) # r') := by
              rw [nonMemberSubfamily_evenLowerHalfFamily, memberSubfamily_evenLowerHalfFamily,
                card_slice_succFamily, card_slice_succFamily]
        _ = Nat.choose (2 * m + 1) (r' + 1) + Nat.choose (2 * m + 1) r' := by
              rw [card_slice_oddLowerHalfFamily_eq_choose hr,
                card_slice_oddLowerHalfFamily_eq_choose (by omega)]
        _ = Nat.choose (2 * m + 1) r' + Nat.choose (2 * m + 1) (r' + 1) := by
              ac_rfl
        _ = Nat.choose (2 * m + 2) (r' + 1) := by
              have hpascal :
                  Nat.choose (2 * m + 2) (r' + 1) =
                    Nat.choose (2 * m + 1) r' + Nat.choose (2 * m + 1) (r' + 1) := by
                rw [Nat.choose_succ_succ']
              exact hpascal.symm

theorem card_slice_evenLowerHalfFamily_eq_middle (m : ℕ) :
    #((evenLowerHalfFamily m) # (m + 1)) = Nat.choose (2 * m + 1) m := by
  calc
    #((evenLowerHalfFamily m) # (m + 1))
      = #(((evenLowerHalfFamily m).nonMemberSubfamily 0) # (m + 1)) +
          #(((evenLowerHalfFamily m).memberSubfamily 0) # m) := by
            exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    _ = #((oddLowerHalfFamily m) # (m + 1)) + #((oddLowerHalfFamily m) # m) := by
          rw [nonMemberSubfamily_evenLowerHalfFamily, memberSubfamily_evenLowerHalfFamily,
            card_slice_succFamily, card_slice_succFamily]
    _ = 0 + Nat.choose (2 * m + 1) m := by
          rw [card_slice_oddLowerHalfFamily_eq_zero (by omega),
            card_slice_oddLowerHalfFamily_eq_choose le_rfl]
    _ = Nat.choose (2 * m + 1) m := by simp

theorem card_slice_evenLowerHalfFamily_eq_zero {m r : ℕ} (hr : m + 2 ≤ r) :
    #((evenLowerHalfFamily m) # r) = 0 := by
  cases r with
  | zero =>
      omega
  | succ r' =>
      have hr' : m + 1 ≤ r' := by
        omega
      calc
        #((evenLowerHalfFamily m) # (r' + 1))
          = #(((evenLowerHalfFamily m).nonMemberSubfamily 0) # (r' + 1)) +
              #(((evenLowerHalfFamily m).memberSubfamily 0) # r') := by
                exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
        _ = #((oddLowerHalfFamily m) # (r' + 1)) + #((oddLowerHalfFamily m) # r') := by
              rw [nonMemberSubfamily_evenLowerHalfFamily, memberSubfamily_evenLowerHalfFamily,
                card_slice_succFamily, card_slice_succFamily]
        _ = 0 + 0 := by
              rw [card_slice_oddLowerHalfFamily_eq_zero (by omega),
                card_slice_oddLowerHalfFamily_eq_zero hr']
        _ = 0 := by simp

theorem evenLowerHalfFamily_has_exact_slice_profile (m : ℕ) :
    (∀ r ∈ Finset.range (m + 1), #((evenLowerHalfFamily m) # r) = Nat.choose (2 * m + 2) r) ∧
      #((evenLowerHalfFamily m) # (m + 1)) = Nat.choose (2 * m + 1) m ∧
      (∀ r, m + 2 ≤ r → #((evenLowerHalfFamily m) # r) = 0) := by
  refine ⟨?_, card_slice_evenLowerHalfFamily_eq_middle m, ?_⟩
  · intro r hr
    exact card_slice_evenLowerHalfFamily_eq_choose (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
  · intro r hr
    exact card_slice_evenLowerHalfFamily_eq_zero hr

theorem nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    (positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0 =
      succFamily (oddMiddleLayer m) := by
  rw [nonMemberSubfamily_positiveBoundary (a := 0) (𝒜 := evenLowerHalfFamily m)]
  rw [nonMemberSubfamily_evenLowerHalfFamily, nonMemberSubfamily_positiveBoundary_succFamily]
  rw [positiveBoundary_oddLowerHalfFamily]

theorem memberSubfamily_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    (positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0 =
      succFamily (oddMiddleLayer m) := by
  rw [memberSubfamily_positiveBoundary]
  rw [nonMemberSubfamily_evenLowerHalfFamily, memberSubfamily_evenLowerHalfFamily]
  simp [nonMemberSubfamily_positiveBoundary_succFamily, positiveBoundary_oddLowerHalfFamily]

theorem card_slice_oddMiddleLayer_eq_middle (m : ℕ) :
    #((oddMiddleLayer m) # (m + 1)) = Nat.choose (2 * m + 1) m := by
  have hEq : (oddMiddleLayer m) # (m + 1) = oddMiddleLayer m := by
    ext s
    constructor
    · intro hs
      exact (Finset.mem_slice.mp hs).1
    · intro hs
      refine Finset.mem_slice.mpr ⟨hs, ?_⟩
      simpa [mem_oddMiddleLayer] using hs
  rw [hEq, card_oddMiddleLayer]

theorem card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even
    {m r : ℕ} (hr : r ≠ m + 1) :
    #((oddMiddleLayer m) # r) = 0 := by
  refine Finset.card_eq_zero.mpr ?_
  ext s
  constructor
  · intro hs
    exfalso
    rcases Finset.mem_slice.mp hs with ⟨hsMid, hsCard⟩
    have hsCard' : s.card = m + 1 := by
      simpa [mem_oddMiddleLayer] using hsMid
    exact hr (hsCard.symm.trans hsCard')
  · intro hs
    simpa using hs

theorem card_slice_positiveBoundary_evenLowerHalfFamily_eq_middle_left (m : ℕ) :
    #((positiveBoundary (evenLowerHalfFamily m)) # (m + 1)) =
      Nat.choose (2 * m + 1) m := by
  calc
    #((positiveBoundary (evenLowerHalfFamily m)) # (m + 1))
      = #(((positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0) # (m + 1)) +
          #(((positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0) # m) := by
            exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    _ = #((oddMiddleLayer m) # (m + 1)) + #((oddMiddleLayer m) # m) := by
          rw [nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
            memberSubfamily_positiveBoundary_evenLowerHalfFamily,
            card_slice_succFamily, card_slice_succFamily]
    _ = Nat.choose (2 * m + 1) m + 0 := by
          rw [card_slice_oddMiddleLayer_eq_middle,
            card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega)]
    _ = Nat.choose (2 * m + 1) m := by simp

theorem card_slice_positiveBoundary_evenLowerHalfFamily_eq_middle_right (m : ℕ) :
    #((positiveBoundary (evenLowerHalfFamily m)) # (m + 2)) =
      Nat.choose (2 * m + 1) m := by
  calc
    #((positiveBoundary (evenLowerHalfFamily m)) # (m + 2))
      = #(((positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0) # (m + 2)) +
          #(((positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0) # (m + 1)) := by
            exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
    _ = #((oddMiddleLayer m) # (m + 2)) + #((oddMiddleLayer m) # (m + 1)) := by
          rw [nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
            memberSubfamily_positiveBoundary_evenLowerHalfFamily,
            card_slice_succFamily, card_slice_succFamily]
    _ = 0 + Nat.choose (2 * m + 1) m := by
          rw [card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega),
            card_slice_oddMiddleLayer_eq_middle]
    _ = Nat.choose (2 * m + 1) m := by simp

theorem card_slice_positiveBoundary_evenLowerHalfFamily_eq_zero_of_lt_middle
    {m r : ℕ} (hr : r ≤ m) :
    #((positiveBoundary (evenLowerHalfFamily m)) # r) = 0 := by
  cases r with
  | zero =>
      refine Finset.card_eq_zero.mpr ?_
      ext s
      constructor
      · intro hs
        have hsEmpty : s = ∅ := Finset.card_eq_zero.mp (Finset.mem_slice.mp hs).2
        subst hsEmpty
        have hmem : (∅ : Finset (Fin (2 * m + 2))) ∈ positiveBoundary (evenLowerHalfFamily m) :=
          (Finset.mem_slice.mp hs).1
        rw [mem_positiveBoundary] at hmem
        simpa using hmem.2
      · intro hs
        simpa using hs
  | succ r' =>
      have hr' : r' < m := by omega
      calc
        #((positiveBoundary (evenLowerHalfFamily m)) # (r' + 1))
          = #(((positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0) # (r' + 1)) +
              #(((positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0) # r') := by
                exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
        _ = #((oddMiddleLayer m) # (r' + 1)) + #((oddMiddleLayer m) # r') := by
              rw [nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
                memberSubfamily_positiveBoundary_evenLowerHalfFamily,
                card_slice_succFamily, card_slice_succFamily]
        _ = 0 + 0 := by
              rw [card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega),
                card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega)]
        _ = 0 := by simp

theorem card_slice_positiveBoundary_evenLowerHalfFamily_eq_zero_of_gt_upper_middle
    {m r : ℕ} (hr : m + 3 ≤ r) :
    #((positiveBoundary (evenLowerHalfFamily m)) # r) = 0 := by
  cases r with
  | zero =>
      omega
  | succ r' =>
      have hr' : m + 2 ≤ r' := by omega
      calc
        #((positiveBoundary (evenLowerHalfFamily m)) # (r' + 1))
          = #(((positiveBoundary (evenLowerHalfFamily m)).nonMemberSubfamily 0) # (r' + 1)) +
              #(((positiveBoundary (evenLowerHalfFamily m)).memberSubfamily 0) # r') := by
                exact card_slice_succ_eq_card_nonMemberSubfamily_slice_succ_add_card_memberSubfamily_slice
        _ = #((oddMiddleLayer m) # (r' + 1)) + #((oddMiddleLayer m) # r') := by
              rw [nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
                memberSubfamily_positiveBoundary_evenLowerHalfFamily,
                card_slice_succFamily, card_slice_succFamily]
        _ = 0 + 0 := by
              rw [card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega),
                card_slice_oddMiddleLayer_eq_zero_of_ne_middle_even (by omega)]
        _ = 0 := by simp

theorem positiveBoundary_evenLowerHalfFamily_has_exact_slice_profile (m : ℕ) :
    (∀ r ∈ Finset.range (m + 1),
      #((positiveBoundary (evenLowerHalfFamily m)) # r) = 0) ∧
      #((positiveBoundary (evenLowerHalfFamily m)) # (m + 1)) =
        Nat.choose (2 * m + 1) m ∧
      #((positiveBoundary (evenLowerHalfFamily m)) # (m + 2)) =
        Nat.choose (2 * m + 1) m ∧
      (∀ r, m + 3 ≤ r → #((positiveBoundary (evenLowerHalfFamily m)) # r) = 0) := by
  refine ⟨?_, card_slice_positiveBoundary_evenLowerHalfFamily_eq_middle_left m,
    card_slice_positiveBoundary_evenLowerHalfFamily_eq_middle_right m, ?_⟩
  · intro r hr
    exact card_slice_positiveBoundary_evenLowerHalfFamily_eq_zero_of_lt_middle
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
  · intro r hr
    exact card_slice_positiveBoundary_evenLowerHalfFamily_eq_zero_of_gt_upper_middle hr

theorem card_positiveBoundary_evenLowerHalfFamily (m : ℕ) :
    #(positiveBoundary (evenLowerHalfFamily m)) = Nat.choose (2 * m + 2) (m + 1) := by
  rw [← Finset.card_memberSubfamily_add_card_nonMemberSubfamily 0
    (positiveBoundary (evenLowerHalfFamily m))]
  rw [memberSubfamily_positiveBoundary_evenLowerHalfFamily,
    nonMemberSubfamily_positiveBoundary_evenLowerHalfFamily,
    card_succFamily, card_oddMiddleLayer]
  rw [Nat.choose_succ_succ', Nat.choose_symm_half]

theorem upperClosure_succFamily_oddMiddleLayer_eq_compl_evenLowerHalfFamily (m : ℕ) :
    (↑(upperClosure (succFamily (oddMiddleLayer m) : Set (Finset (Fin (2 * m + 2))))) :
      Set (Finset (Fin (2 * m + 2)))) = (evenLowerHalfFamily m : Set (Finset (Fin (2 * m + 2))))ᶜ := by
  ext s
  constructor
  · intro hs hsEven
    rcases mem_upperClosure.mp hs with ⟨t, ht, hts⟩
    change t ∈ succFamily (oddMiddleLayer m) at ht
    have htEven : t ∈ evenLowerHalfFamily m := isDownSetFamily_evenLowerHalfFamily m hts hsEven
    have ht0 : (0 : Fin (2 * m + 2)) ∉ t := zero_not_mem_of_mem_succFamily ht
    have htMid : #(t.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn) = m + 1 := by
      simpa [mem_oddMiddleLayer] using (mem_succFamily_iff.mp ht).2
    have htLow : t.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈ oddLowerHalfFamily m := by
      rw [← mem_evenLowerHalfFamily_iff_of_zero_not_mem m ht0]
      exact htEven
    rw [mem_oddLowerHalfFamily] at htLow
    omega
  · intro hs
    by_cases hs0 : (0 : Fin (2 * m + 2)) ∈ s
    · have hsOddNot : (s.erase 0).preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∉
          oddLowerHalfFamily m := by
        intro hsLow
        have hsBase : s.erase 0 ∈ succFamily (oddLowerHalfFamily m) :=
          (mem_succFamily_iff).2 ⟨notMem_erase 0 s, hsLow⟩
        have hsImage : s ∈ (succFamily (oddLowerHalfFamily m)).image (insert 0) :=
          Finset.mem_image.mpr ⟨s.erase 0, hsBase, insert_erase hs0⟩
        exact hs <| by
          change s ∈ evenLowerHalfFamily m
          rw [evenLowerHalfFamily, mem_union]
          exact Or.inr hsImage
      have hsUpper : (s.erase 0).preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈
          (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
            Set (Finset (Fin (2 * m + 1)))) := by
        rw [upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily]
        simpa [Set.mem_compl_iff, mem_coe] using hsOddNot
      rcases mem_upperClosure.mp hsUpper with ⟨u, hu, hus⟩
      refine mem_upperClosure.mpr ⟨u.map (Fin.succEmb (2 * m + 1)), ?_, ?_⟩
      · change u.map (Fin.succEmb (2 * m + 1)) ∈ succFamily (oddMiddleLayer m)
        change u ∈ oddMiddleLayer m at hu
        exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Finset.mem_of_mem_erase (Finset.mem_preimage.mp (hus hy))
    · have hsOddNot : s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∉
          oddLowerHalfFamily m := by
        rw [← mem_evenLowerHalfFamily_iff_of_zero_not_mem m hs0]
        exact hs
      have hsUpper : s.preimage Fin.succ (Fin.succ_injective (2 * m + 1)).injOn ∈
          (↑(upperClosure (oddMiddleLayer m : Set (Finset (Fin (2 * m + 1))))) :
            Set (Finset (Fin (2 * m + 1)))) := by
        rw [upperClosure_oddMiddleLayer_eq_compl_oddLowerHalfFamily]
        simpa [Set.mem_compl_iff, mem_coe] using hsOddNot
      rcases mem_upperClosure.mp hsUpper with ⟨u, hu, hus⟩
      refine mem_upperClosure.mpr ⟨u.map (Fin.succEmb (2 * m + 1)), ?_, ?_⟩
      · change u.map (Fin.succEmb (2 * m + 1)) ∈ succFamily (oddMiddleLayer m)
        change u ∈ oddMiddleLayer m at hu
        exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Finset.mem_preimage.mp (hus hy)

theorem minimalOutside_evenLowerHalfFamily (m : ℕ) :
    minimalOutside (evenLowerHalfFamily m) = succFamily (oddMiddleLayer m) := by
  apply eq_of_upperClosure_eq_of_isAntichain
  · exact isAntichain_minimalOutside _
  · exact isAntichain_succFamily_oddMiddleLayer _
  · rw [upperClosure_minimalOutside_eq_compl (isDownSetFamily_evenLowerHalfFamily m),
      upperClosure_succFamily_oddMiddleLayer_eq_compl_evenLowerHalfFamily]

theorem card_minimalOutside_evenLowerHalfFamily (m : ℕ) :
    #(minimalOutside (evenLowerHalfFamily m)) = Nat.choose (2 * m + 1) m := by
  rw [minimalOutside_evenLowerHalfFamily, card_succFamily, card_oddMiddleLayer]

end Erdos1
