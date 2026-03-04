import Mathlib

namespace TaoExercises
namespace TaoBook
namespace Chapter2

/-- Tao, Problem 2.6 (Shklarsky et al. 1962, p. 14):
if `k` is odd, then `1^k + 2^k + · · · + n^k` is divisible by `1 + 2 + · · · + n`.

We formalize both sums as `range (n + 1)` sums; the `0` term is `0` on each side. -/
theorem exercise_2_6 {k n : ℕ} (hk : Odd k) :
    (∑ i ∈ Finset.range (n + 1), i) ∣ ∑ i ∈ Finset.range (n + 1), i ^ k := by
  let S : ℕ := ∑ i ∈ Finset.range (n + 1), i ^ k
  have hkpos : 0 < k := hk.pos

  have h_n_dvd_twoS : n ∣ 2 * S := by
    have hreflect : (∑ i ∈ Finset.range (n + 1), (n - i) ^ k) = S := by
      simpa [S] using (Finset.sum_range_reflect (fun i => i ^ k) (n + 1))
    have hsum :
        2 * S = ∑ i ∈ Finset.range (n + 1), (i ^ k + (n - i) ^ k) := by
      calc
        2 * S = S + S := by rw [two_mul]
        _ = (∑ i ∈ Finset.range (n + 1), i ^ k) +
            (∑ i ∈ Finset.range (n + 1), (n - i) ^ k) := by
              simp [S, hreflect]
        _ = ∑ i ∈ Finset.range (n + 1), (i ^ k + (n - i) ^ k) := by
          rw [Finset.sum_add_distrib]
    rw [hsum]
    refine Finset.dvd_sum ?_
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    have hterm : i + (n - i) ∣ i ^ k + (n - i) ^ k := hk.nat_add_dvd_pow_add_pow i (n - i)
    have hidx : i + (n - i) = n := by omega
    simpa [hidx] using hterm

  let T : ℕ := ∑ i ∈ Finset.range n, (i + 1) ^ k
  have hS_eq_T : S = T := by
    calc
      S = T + 0 ^ k := by
        simpa [S, T] using (Finset.sum_range_succ' (fun i => i ^ k) n)
      _ = T := by simp [Nat.zero_pow hkpos]

  have h_np1_dvd_twoS : n + 1 ∣ 2 * S := by
    have hreflect : (∑ i ∈ Finset.range n, (n - 1 - i + 1) ^ k) = T := by
      simpa [T] using (Finset.sum_range_reflect (fun i => (i + 1) ^ k) n)
    have hsum :
        2 * T = ∑ i ∈ Finset.range n, ((i + 1) ^ k + (n - 1 - i + 1) ^ k) := by
      calc
        2 * T = T + T := by rw [two_mul]
        _ = (∑ i ∈ Finset.range n, (i + 1) ^ k) +
            (∑ i ∈ Finset.range n, (n - 1 - i + 1) ^ k) := by
              simp [T, hreflect]
        _ = ∑ i ∈ Finset.range n, ((i + 1) ^ k + (n - 1 - i + 1) ^ k) := by
          rw [Finset.sum_add_distrib]
    rw [hS_eq_T, hsum]
    refine Finset.dvd_sum ?_
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hterm : (i + 1) + (n - 1 - i + 1) ∣ (i + 1) ^ k + (n - 1 - i + 1) ^ k :=
      hk.nat_add_dvd_pow_add_pow (i + 1) (n - 1 - i + 1)
    have hidx : (i + 1) + (n - 1 - i + 1) = n + 1 := by omega
    simpa [hidx] using hterm

  have hcop : Nat.Coprime n (n + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right n
  have h_mul_dvd_twoS : n * (n + 1) ∣ 2 * S :=
    hcop.mul_dvd_of_dvd_of_dvd h_n_dvd_twoS h_np1_dvd_twoS

  have h_two_sum : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Finset.sum_range_id_mul_two (n + 1))
  have htwo : 2 * (∑ i ∈ Finset.range (n + 1), i) ∣ 2 * S := by
    rw [h_two_sum]
    exact h_mul_dvd_twoS

  exact (Nat.dvd_of_mul_dvd_mul_left (Nat.succ_pos 1) htwo)

end Chapter2
end TaoBook
end TaoExercises
