import ErdosProblems.Problem1CubeBoundary
import Mathlib.Combinatorics.SetFamily.HarrisKleitman

open Finset
open scoped FinsetFamily

namespace Erdos1

variable {α : Type*} [DecidableEq α]

/-- Total cardinality weight of a finset family. -/
def totalSize (𝒜 : Finset (Finset α)) : ℕ :=
  ∑ s ∈ 𝒜, s.card

/-- Lower-set view of a cube family. This is the natural target object for Phase A5. -/
abbrev IsDownSetFamily (𝒜 : Finset (Finset α)) : Prop :=
  IsLowerSet (𝒜 : Set (Finset α))

/-- Re-export down-compression under the Erdos1 cube-boundary namespace. -/
abbrev downCompression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝓓 a 𝒜

@[simp]
theorem card_downCompression (a : α) (𝒜 : Finset (Finset α)) :
    #(downCompression a 𝒜) = #𝒜 := by
  simp [downCompression]

theorem nonMemberSubfamily_downCompression (a : α) (𝒜 : Finset (Finset α)) :
    (downCompression a 𝒜).nonMemberSubfamily a =
      𝒜.nonMemberSubfamily a ∪ 𝒜.memberSubfamily a := by
  ext s
  rw [mem_nonMemberSubfamily, mem_union, downCompression, Down.mem_compression,
    mem_nonMemberSubfamily, mem_memberSubfamily]
  constructor
  · rintro ⟨hsComp, ha⟩
    rw [Finset.erase_eq_of_notMem ha] at hsComp
    rcases hsComp with ⟨hsA, -⟩ | ⟨hsNotA, hsInsert⟩
    · exact Or.inl ⟨hsA, ha⟩
    · exact Or.inr ⟨hsInsert, ha⟩
  · intro hs
    rcases hs with hsNon | hsMem
    · exact ⟨Or.inl ⟨hsNon.1, by simpa [hsNon.2] using hsNon.1⟩, hsNon.2⟩
    · rcases hsMem with ⟨hsInsert, ha⟩
      by_cases hsA : s ∈ 𝒜
      · exact ⟨Or.inl ⟨hsA, by simpa [ha] using hsA⟩, ha⟩
      · exact ⟨Or.inr ⟨hsA, hsInsert⟩, ha⟩

theorem memberSubfamily_downCompression (a : α) (𝒜 : Finset (Finset α)) :
    (downCompression a 𝒜).memberSubfamily a =
      𝒜.memberSubfamily a ∩ 𝒜.nonMemberSubfamily a := by
  ext s
  rw [mem_memberSubfamily, mem_inter, downCompression, Down.mem_compression,
    mem_memberSubfamily, mem_nonMemberSubfamily]
  constructor
  · rintro ⟨hsCompInsert, ha⟩
    rw [Finset.erase_insert ha] at hsCompInsert
    rcases hsCompInsert with ⟨hsInsert, hsA⟩ | ⟨hsNotInsert, hsInsertInsert⟩
    · exact ⟨⟨hsInsert, ha⟩, ⟨hsA, ha⟩⟩
    · exact (hsNotInsert (by simpa using hsInsertInsert)).elim
  · rintro ⟨hsMem, hsNon⟩
    exact ⟨Or.inl ⟨hsMem.1, by simpa [hsMem.2] using hsNon.1⟩, hsMem.2⟩

theorem totalSize_eq_totalSize_nonMemberSubfamily_add_totalSize_memberSubfamily_add_card_memberSubfamily
    (a : α) (𝒜 : Finset (Finset α)) :
    totalSize 𝒜 =
      totalSize (𝒜.nonMemberSubfamily a) +
        totalSize (𝒜.memberSubfamily a) +
        #(𝒜.memberSubfamily a) := by
  classical
  have hnon :
      ∑ s ∈ 𝒜 with ¬a ∈ s, s.card = totalSize (𝒜.nonMemberSubfamily a) := by
    simp [totalSize, Finset.nonMemberSubfamily]
  have hcardMember :
      #(𝒜.memberSubfamily a) = #({s ∈ 𝒜 | a ∈ s} : Finset (Finset α)) := by
    rw [Finset.memberSubfamily, Finset.card_image_of_injOn]
    exact (Finset.erase_injOn' a).mono fun s hs => (Finset.mem_filter.mp hs).2
  have hsumMember :
      ∑ s ∈ 𝒜 with a ∈ s, s.card =
        totalSize (𝒜.memberSubfamily a) + #(𝒜.memberSubfamily a) := by
    calc
      ∑ s ∈ 𝒜 with a ∈ s, s.card
        = ∑ s ∈ 𝒜 with a ∈ s, ((s.erase a).card + 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have ha : a ∈ s := (Finset.mem_filter.mp hs).2
            exact (Finset.card_erase_add_one ha).symm
      _ = (∑ s ∈ 𝒜 with a ∈ s, (s.erase a).card) + ∑ s ∈ 𝒜 with a ∈ s, 1 := by
            rw [Finset.sum_add_distrib]
      _ = totalSize (𝒜.memberSubfamily a) +
            #({s ∈ 𝒜 | a ∈ s} : Finset (Finset α)) := by
            rw [show (∑ s ∈ 𝒜 with a ∈ s, (s.erase a).card) = totalSize (𝒜.memberSubfamily a) by
              unfold totalSize
              rw [Finset.memberSubfamily, Finset.sum_image]
              exact (Finset.erase_injOn' a).mono fun s hs => (Finset.mem_filter.mp hs).2]
            simp
      _ = totalSize (𝒜.memberSubfamily a) + #(𝒜.memberSubfamily a) := by rw [hcardMember]
  calc
    totalSize 𝒜
      = (∑ s ∈ 𝒜 with a ∈ s, s.card) + ∑ s ∈ 𝒜 with ¬a ∈ s, s.card := by
          unfold totalSize
          symm
          exact Finset.sum_filter_add_sum_filter_not
            (s := 𝒜) (p := fun s => a ∈ s) (f := fun s : Finset α => s.card)
    _ = (totalSize (𝒜.memberSubfamily a) + #(𝒜.memberSubfamily a)) +
          totalSize (𝒜.nonMemberSubfamily a) := by
            rw [hsumMember, hnon]
    _ = totalSize (𝒜.nonMemberSubfamily a) +
          totalSize (𝒜.memberSubfamily a) +
          #(𝒜.memberSubfamily a) := by ac_rfl

theorem totalSize_union_add_totalSize_inter (𝒜 ℬ : Finset (Finset α)) :
    totalSize (𝒜 ∪ ℬ) + totalSize (𝒜 ∩ ℬ) = totalSize 𝒜 + totalSize ℬ := by
  unfold totalSize
  simpa using (Finset.sum_union_inter (s₁ := 𝒜) (s₂ := ℬ) (f := fun s : Finset α => s.card))

theorem downCompression_eq_self_iff_memberSubfamily_subset_nonMemberSubfamily
    (a : α) (𝒜 : Finset (Finset α)) :
    downCompression a 𝒜 = 𝒜 ↔ 𝒜.memberSubfamily a ⊆ 𝒜.nonMemberSubfamily a := by
  constructor
  · intro h s hs
    have hsComp : s ∈ (downCompression a 𝒜).memberSubfamily a := by simpa [h] using hs
    rw [memberSubfamily_downCompression] at hsComp
    rw [mem_inter] at hsComp
    exact hsComp.2
  · intro hsub
    ext s
    rw [downCompression, Down.mem_compression]
    constructor
    · rintro (⟨hsA, -⟩ | ⟨hsNotA, hsInsert⟩)
      · exact hsA
      · have ha : a ∉ s := by
          intro hsa
          exact hsNotA (by simpa [Finset.insert_eq_of_mem hsa] using hsInsert)
        have hsNon : s ∈ 𝒜.nonMemberSubfamily a :=
          hsub (mem_memberSubfamily.mpr ⟨hsInsert, ha⟩)
        exact (mem_nonMemberSubfamily.mp hsNon).1
    · intro hsA
      by_cases hErase : s.erase a ∈ 𝒜
      · exact Or.inl ⟨hsA, hErase⟩
      · by_cases ha : a ∈ s
        · exact False.elim <|
            hErase ((mem_nonMemberSubfamily.mp
              (hsub (mem_memberSubfamily.mpr
                ⟨by simpa [Finset.insert_erase ha], notMem_erase _ _⟩))).1)
        · exact Or.inl ⟨hsA, by simpa [ha] using hsA⟩

theorem totalSize_downCompression_eq_totalSize_sub_card_sdiff (a : α) (𝒜 : Finset (Finset α)) :
    totalSize (downCompression a 𝒜) =
      totalSize 𝒜 - #(𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a) := by
  let N := 𝒜.nonMemberSubfamily a
  let M := 𝒜.memberSubfamily a
  have hA :=
    totalSize_eq_totalSize_nonMemberSubfamily_add_totalSize_memberSubfamily_add_card_memberSubfamily
      a 𝒜
  have hC :=
    totalSize_eq_totalSize_nonMemberSubfamily_add_totalSize_memberSubfamily_add_card_memberSubfamily
      a (downCompression a 𝒜)
  rw [nonMemberSubfamily_downCompression, memberSubfamily_downCompression] at hC
  have hSdiff : #(M \ N) + #(M ∩ N) = #M := Finset.card_sdiff_add_card_inter M N
  have hCardInter : #(M ∩ N) = #M - #(M \ N) := by
    omega
  have hUnionInter :
      totalSize (N ∪ M) + totalSize (M ∩ N) = totalSize N + totalSize M := by
    simpa [Finset.inter_comm, add_comm] using totalSize_union_add_totalSize_inter N M
  calc
    totalSize (downCompression a 𝒜)
      = totalSize (N ∪ M) + totalSize (M ∩ N) + #(M ∩ N) := by simpa [N, M] using hC
    _ = (totalSize (N ∪ M) + totalSize (M ∩ N)) + #(M ∩ N) := by ac_rfl
    _ = (totalSize N + totalSize M) + #(M ∩ N) := by rw [hUnionInter]
    _ = totalSize N + totalSize M + #(M ∩ N) := by ac_rfl
    _ = totalSize N + totalSize M + (#M - #(M \ N)) := by rw [hCardInter]
    _ = totalSize 𝒜 - #(M \ N) := by
          rw [show totalSize 𝒜 = totalSize N + totalSize M + #M by simpa [N, M] using hA]
          omega
    _ = totalSize 𝒜 - #(𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a) := by rfl

theorem card_memberSubfamily_eq_card_filter_mem (a : α) (𝒜 : Finset (Finset α)) :
    #(𝒜.memberSubfamily a) = #({s ∈ 𝒜 | a ∈ s} : Finset (Finset α)) := by
  rw [Finset.memberSubfamily, Finset.card_image_of_injOn]
  exact (Finset.erase_injOn' a).mono fun s hs => (Finset.mem_filter.mp hs).2

theorem sum_card_memberSubfamily_eq_totalSize [Fintype α] (𝒜 : Finset (Finset α)) :
    ∑ a, #(𝒜.memberSubfamily a) = totalSize 𝒜 := by
  calc
    ∑ a, #(𝒜.memberSubfamily a)
      = ∑ a, ∑ s in ({s ∈ 𝒜 | a ∈ s} : Finset (Finset α)), 1 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [card_memberSubfamily_eq_card_filter_mem, Finset.card_eq_sum_ones]
    _ = ∑ s in 𝒜, ∑ a in s, 1 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro s hs
          simp
    _ = totalSize 𝒜 := by
          simp [totalSize]

theorem sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize [Fintype α]
    (𝒜 : Finset (Finset α)) :
    ∑ a, #(𝒜.nonMemberSubfamily a) = Fintype.card α * 𝒜.card - totalSize 𝒜 := by
  have hsplit :
      ∑ a, #(𝒜.memberSubfamily a) + ∑ a, #(𝒜.nonMemberSubfamily a) =
        ∑ a : α, 𝒜.card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro a ha
    exact Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜
  rw [sum_card_memberSubfamily_eq_totalSize] at hsplit
  simpa using hsplit.symm

theorem card_nonMemberSubfamily_eq_half_of_card_eq_two_mul_of_totalSize_eq
    [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) {m : ℕ}
    (hcard : 𝒜.card = 2 * m)
    (htotal : totalSize 𝒜 = Fintype.card α * m) (a : α) :
    #(𝒜.nonMemberSubfamily a) = m := by
  have hsum :
      ∑ b, #(𝒜.nonMemberSubfamily b) = Fintype.card α * m := by
    rw [sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize, hcard, htotal]
    omega
  have hhalf : ∀ b : α, m ≤ #(𝒜.nonMemberSubfamily b) := by
    intro b
    exact half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul h𝒜 b m hcard
  by_contra hne
  have hgt : m + 1 ≤ #(𝒜.nonMemberSubfamily a) := by
    have hmle := hhalf a
    omega
  have hrest :
      (Finset.univ.erase a).sum (fun b : α => m) ≤
        (Finset.univ.erase a).sum (fun b : α => #(𝒜.nonMemberSubfamily b)) := by
    exact Finset.sum_le_sum fun b hb => hhalf b
  have hbig :
      Fintype.card α * m + 1 ≤ ∑ b, #(𝒜.nonMemberSubfamily b) := by
    rw [Finset.sum_erase_add _ (Finset.mem_univ a)]
    have hrest' :
        (Fintype.card α - 1) * m ≤
          (Finset.univ.erase a).sum (fun b : α => #(𝒜.nonMemberSubfamily b)) := by
      calc
        (Fintype.card α - 1) * m = (Finset.univ.erase a).sum (fun b : α => m) := by
          simp
        _ ≤ (Finset.univ.erase a).sum (fun b : α => #(𝒜.nonMemberSubfamily b)) := hrest
    omega
  omega

theorem exists_card_nonMemberSubfamily_gt_half_of_card_eq_two_mul_of_totalSize_lt
    [Fintype α] {𝒜 : Finset (Finset α)} {m : ℕ}
    (hcard : 𝒜.card = 2 * m)
    (htotal : totalSize 𝒜 < Fintype.card α * m) :
    ∃ a : α, m < #(𝒜.nonMemberSubfamily a) := by
  by_contra hnone
  have hle : ∀ a : α, #(𝒜.nonMemberSubfamily a) ≤ m := by
    intro a
    exact le_of_not_gt (by simpa using hnone a)
  have hsumle :
      ∑ a, #(𝒜.nonMemberSubfamily a) ≤ ∑ _a : α, m := by
    exact Finset.sum_le_sum fun a ha => hle a
  have hsumgt :
      Fintype.card α * m < ∑ a, #(𝒜.nonMemberSubfamily a) := by
    rw [sum_card_nonMemberSubfamily_eq_card_mul_sub_totalSize, hcard]
    omega
  omega

theorem totalSize_downCompression_lt_totalSize_of_ne {a : α} {𝒜 : Finset (Finset α)}
    (hneq : downCompression a 𝒜 ≠ 𝒜) :
    totalSize (downCompression a 𝒜) < totalSize 𝒜 := by
  have hnot : ¬ 𝒜.memberSubfamily a ⊆ 𝒜.nonMemberSubfamily a := by
    intro hsub
    exact hneq
      ((downCompression_eq_self_iff_memberSubfamily_subset_nonMemberSubfamily a 𝒜).2 hsub)
  have hpos : 0 < #(𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a) := by
    by_contra hpos
    apply hnot
    intro s hsMem
    by_contra hsNon
    have hsDiff : s ∈ 𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a := by
      simp [mem_sdiff, hsMem, hsNon]
    exact hpos (Finset.card_pos.mpr ⟨s, hsDiff⟩)
  rw [totalSize_downCompression_eq_totalSize_sub_card_sdiff]
  have hsdiffle : #(𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a) ≤ totalSize 𝒜 := by
    calc
      #(𝒜.memberSubfamily a \ 𝒜.nonMemberSubfamily a)
        ≤ #(𝒜.memberSubfamily a) := by
            exact Finset.card_le_card (Finset.sdiff_subset : _)
      _ ≤ totalSize 𝒜 := by
        have hA :=
          totalSize_eq_totalSize_nonMemberSubfamily_add_totalSize_memberSubfamily_add_card_memberSubfamily
            a 𝒜
        rw [show totalSize 𝒜 =
          totalSize (𝒜.nonMemberSubfamily a) + totalSize (𝒜.memberSubfamily a) +
            #(𝒜.memberSubfamily a) by simpa using hA]
        omega
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hpos hsdiffle) hpos

theorem downCompression_eq_self_of_isDownSetFamily {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    downCompression a 𝒜 = 𝒜 := by
  ext s
  rw [downCompression, Down.mem_compression]
  constructor
  · rintro (⟨hs𝒜, -⟩ | ⟨hsNot𝒜, hsInsert⟩)
    · exact hs𝒜
    · exact h𝒜 (subset_insert _ _) hsInsert
  · intro hs𝒜
    exact Or.inl ⟨hs𝒜, h𝒜 (Finset.erase_subset a s) hs𝒜⟩

theorem mem_of_subset_of_downCompression_eq_self_all {𝒜 : Finset (Finset α)}
    (hfix : ∀ a : α, downCompression a 𝒜 = 𝒜)
    {t s : Finset α} (hts : t ⊆ s) (hs𝒜 : s ∈ 𝒜) :
    t ∈ 𝒜 := by
  classical
  have hmain : ∀ u : Finset α, Disjoint t u → t ∪ u ∈ 𝒜 → t ∈ 𝒜 := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro hdisj hu
        simpa using hu
    | @insert a u ha ihu =>
        intro hdisj hu
        rw [Finset.disjoint_insert_right] at hdisj
        have hat : a ∉ t := hdisj.1
        have hdisj' : Disjoint t u := hdisj.2
        have huComp : t ∪ insert a u ∈ downCompression a 𝒜 := by
          rw [hfix a]
          exact hu
        have huEraseComp : (t ∪ insert a u).erase a ∈ downCompression a 𝒜 :=
          Down.erase_mem_compression_of_mem_compression huComp
        have huErase : (t ∪ insert a u).erase a ∈ 𝒜 := by
          rw [hfix a] at huEraseComp
          exact huEraseComp
        have hEraseEq : (t ∪ insert a u).erase a = t ∪ u := by
          rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hat, Finset.erase_insert ha]
        rw [hEraseEq] at huErase
        exact ihu hdisj' huErase
  have hsUnion : t ∪ (s \ t) ∈ 𝒜 := by
    simpa [Finset.union_sdiff_of_subset hts] using hs𝒜
  exact hmain (s \ t) Finset.disjoint_sdiff hsUnion

theorem isDownSetFamily_of_downCompression_eq_self_all {𝒜 : Finset (Finset α)}
    (hfix : ∀ a : α, downCompression a 𝒜 = 𝒜) :
    IsDownSetFamily 𝒜 := by
  intro t s hts hs𝒜
  exact mem_of_subset_of_downCompression_eq_self_all hfix hts hs𝒜

theorem isDownSetFamily_iff_downCompression_eq_self_all {𝒜 : Finset (Finset α)} :
    IsDownSetFamily 𝒜 ↔ ∀ a : α, downCompression a 𝒜 = 𝒜 := by
  constructor
  · intro h𝒜 a
    exact downCompression_eq_self_of_isDownSetFamily h𝒜 a
  · intro hfix
    exact isDownSetFamily_of_downCompression_eq_self_all hfix

theorem exists_downCompression_lt_totalSize_of_not_isDownSetFamily {𝒜 : Finset (Finset α)}
    (h𝒜 : ¬ IsDownSetFamily 𝒜) :
    ∃ a : α, totalSize (downCompression a 𝒜) < totalSize 𝒜 := by
  classical
  by_contra hNo
  apply h𝒜
  rw [isDownSetFamily_iff_downCompression_eq_self_all]
  intro a
  by_contra hneq
  exact hNo ⟨a, totalSize_downCompression_lt_totalSize_of_ne hneq⟩

/-- Every finite cube family can be reduced, by iterated down-compressions, to a down-set of the
same cardinality. -/
theorem exists_downSetFamily_card_eq (𝒜 : Finset (Finset α)) :
    ∃ 𝒟 : Finset (Finset α), IsDownSetFamily 𝒟 ∧ #𝒟 = #𝒜 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ ℬ : Finset (Finset α), totalSize ℬ = n →
      ∃ 𝒟 : Finset (Finset α), IsDownSetFamily 𝒟 ∧ #𝒟 = #ℬ
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih ℬ hsize
    by_cases hℬ : IsDownSetFamily ℬ
    · exact ⟨ℬ, hℬ, rfl⟩
    · rcases exists_downCompression_lt_totalSize_of_not_isDownSetFamily hℬ with ⟨a, ha⟩
      have hlt : totalSize (downCompression a ℬ) < n := by simpa [hsize] using ha
      rcases ih (totalSize (downCompression a ℬ)) hlt (downCompression a ℬ) rfl with ⟨𝒟, h𝒟, hcard⟩
      exact ⟨𝒟, h𝒟, by rw [hcard, card_downCompression]⟩
  exact hP (totalSize 𝒜) 𝒜 rfl

omit [DecidableEq α] in
theorem empty_mem_of_nonempty_isDownSetFamily {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) (hne : 𝒜.Nonempty) :
    ∅ ∈ 𝒜 := by
  rcases hne with ⟨s, hs⟩
  exact h𝒜 (Finset.empty_subset s) hs

theorem exists_nonempty_downSetFamily_card_eq {𝒜 : Finset (Finset α)} (hne : 𝒜.Nonempty) :
    ∃ 𝒟 : Finset (Finset α), 𝒟.Nonempty ∧ IsDownSetFamily 𝒟 ∧ #𝒟 = #𝒜 := by
  rcases exists_downSetFamily_card_eq 𝒜 with ⟨𝒟, h𝒟, hcard⟩
  have hcardpos : 0 < #𝒟 := by
    rw [hcard]
    exact Finset.card_pos.mpr hne
  exact ⟨𝒟, Finset.card_pos.mp hcardpos, h𝒟, hcard⟩

theorem exists_downSetFamily_card_eq_le_positiveBoundary [Fintype α]
    (hstep : ∀ a : α, ∀ 𝒜 : Finset (Finset α),
      #(positiveBoundary (downCompression a 𝒜)) ≤ #(positiveBoundary 𝒜))
    (𝒜 : Finset (Finset α)) :
    ∃ 𝒟 : Finset (Finset α),
      IsDownSetFamily 𝒟 ∧ #𝒟 = #𝒜 ∧ #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ ℬ : Finset (Finset α), totalSize ℬ = n →
      ∃ 𝒟 : Finset (Finset α),
        IsDownSetFamily 𝒟 ∧ #𝒟 = #ℬ ∧ #(positiveBoundary 𝒟) ≤ #(positiveBoundary ℬ)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih ℬ hsize
    by_cases hℬ : IsDownSetFamily ℬ
    · exact ⟨ℬ, hℬ, rfl, le_rfl⟩
    · rcases exists_downCompression_lt_totalSize_of_not_isDownSetFamily hℬ with ⟨a, ha⟩
      have hlt : totalSize (downCompression a ℬ) < n := by
        simpa [hsize] using ha
      rcases ih (totalSize (downCompression a ℬ)) hlt (downCompression a ℬ) rfl with
          ⟨𝒟, h𝒟, hcard, hbdry⟩
      exact ⟨𝒟, h𝒟, by rw [hcard, card_downCompression],
        hbdry.trans (hstep a ℬ)⟩
  exact hP (totalSize 𝒜) 𝒜 rfl

theorem exists_nonempty_downSetFamily_card_eq_le_positiveBoundary [Fintype α]
    (hstep : ∀ a : α, ∀ 𝒜 : Finset (Finset α),
      #(positiveBoundary (downCompression a 𝒜)) ≤ #(positiveBoundary 𝒜))
    {𝒜 : Finset (Finset α)} (hne : 𝒜.Nonempty) :
    ∃ 𝒟 : Finset (Finset α),
      𝒟.Nonempty ∧ IsDownSetFamily 𝒟 ∧ #𝒟 = #𝒜 ∧ #(positiveBoundary 𝒟) ≤ #(positiveBoundary 𝒜) := by
  rcases exists_downSetFamily_card_eq_le_positiveBoundary hstep 𝒜 with
    ⟨𝒟, h𝒟, hcard, hbdry⟩
  have hne𝒟 : 𝒟.Nonempty := by
    have hcardpos : 0 < #𝒟 := by
      rw [hcard]
      exact Finset.card_pos.mpr hne
    exact Finset.card_pos.mp hcardpos
  exact ⟨𝒟, hne𝒟, h𝒟, hcard, hbdry⟩

theorem isDownSetFamily_nonMemberSubfamily {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    IsDownSetFamily (𝒜.nonMemberSubfamily a) :=
  h𝒜.nonMemberSubfamily

theorem isDownSetFamily_memberSubfamily {𝒜 : Finset (Finset α)}
    (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    IsDownSetFamily (𝒜.memberSubfamily a) :=
  h𝒜.memberSubfamily

theorem card_memberSubfamily_le_card_nonMemberSubfamily
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    #(𝒜.memberSubfamily a) ≤ #(𝒜.nonMemberSubfamily a) :=
  Finset.card_le_card (h𝒜.memberSubfamily_subset_nonMemberSubfamily (a := a))

theorem half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul
    {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) (m : ℕ)
    (hcard : #𝒜 = 2 * m) :
    m ≤ #(𝒜.nonMemberSubfamily a) := by
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜
  have hle := card_memberSubfamily_le_card_nonMemberSubfamily h𝒜 a
  omega

theorem card_nonMemberSubfamily_sub_memberSubfamily_le_memberSubfamily_positiveBoundary
    [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    #(𝒜.nonMemberSubfamily a) - #(𝒜.memberSubfamily a) ≤
      #((positiveBoundary 𝒜).memberSubfamily a) := by
  rw [← Finset.card_sdiff_of_subset (h𝒜.memberSubfamily_subset_nonMemberSubfamily (a := a))]
  exact card_sdiff_subfamily_le_memberSubfamily_positiveBoundary 𝒜

theorem card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_gap
    [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) :
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        (#(𝒜.nonMemberSubfamily a) - #(𝒜.memberSubfamily a)) ≤
      #(positiveBoundary 𝒜) := by
  rw [← Finset.card_sdiff_of_subset (h𝒜.memberSubfamily_subset_nonMemberSubfamily (a := a))]
  exact card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_card_sdiff a 𝒜

theorem card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_two_mul
    [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) {m : ℕ}
    (hcard : #𝒜 = 2 * m) :
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        2 * (#(𝒜.nonMemberSubfamily a) - m) ≤
      #(positiveBoundary 𝒜) := by
  have hhalf : m ≤ #(𝒜.nonMemberSubfamily a) :=
    half_card_le_card_nonMemberSubfamily_of_card_eq_two_mul h𝒜 a m hcard
  have hgap :=
    card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_gap h𝒜 a
  have hsplit := Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜
  omega

theorem card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_pow
    [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsDownSetFamily 𝒜) (a : α) {k : ℕ}
    (hcard : #𝒜 = 2 ^ (k + 1)) :
    #((positiveBoundary (𝒜.nonMemberSubfamily a)).nonMemberSubfamily a) +
        2 * (#(𝒜.nonMemberSubfamily a) - 2 ^ k) ≤
      #(positiveBoundary 𝒜) := by
  simpa [pow_succ', two_mul] using
    card_positiveBoundary_ge_card_nonMemberSubfamily_positiveBoundary_add_two_mul_excess_of_card_eq_two_mul
      h𝒜 a (m := 2 ^ k) hcard

end Erdos1
