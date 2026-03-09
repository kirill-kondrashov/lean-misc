import ErdosProblems.Problem1Gap
import ErdosProblems.Problem1Real
import ErdosProblems.Problem1ExactValues
import ErdosProblems.Problem1CubeHalfLowerFrontier

open Filter
open scoped Topology Real

namespace Erdos1

/--
Bridge object connecting the original `Problem1.lean` surface to the current split codebase.

The fields record where the original public statements now live: the proved weaker theorem, the
open integer/real exponential targets, the currently known lower-bound theory, the bundled gap
surfaces, the current exact-lower frontier route, and the exact-value witness branch.
-/
structure OriginalSurfaceBridge where
  weaker :
    ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
      IsSumDistinctSet A N → N ≠ 0 → C * 2 ^ A.card / A.card < N
  integer_open_target : OpenIntegerExponentialVariant
  integer_known_lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
        (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N
  integer_known_lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
        (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N
  integer_known_gap : KnownIntegerGapTheory
  real_open_target : OpenRealExponentialVariant
  real_known_lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
        (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N
  real_known_lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
        (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N
  real_known_theory : KnownRealSpacingTheory
  exact_integer_lower_frontier_backed :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N
  exact_witness_N_9 : ∃ A, IsSumDistinctSet A 161 ∧ A.card = 9
  exact_witness_N_10 : ∃ A, IsSumDistinctSet A 309 ∧ A.card = 10

/-- Explicit bridge from the original `Problem1.lean` surface into the current split modules. -/
theorem originalSurfaceBridge_from_currentCodebase : OriginalSurfaceBridge := by
  refine
    { weaker := erdos_1.variants.weaker
      integer_open_target := openIntegerExponentialVariant_axiom
      integer_known_lb := erdos_1.variants.proved.lb
      integer_known_lb_strong := erdos_1.variants.proved.lb_strong
      integer_known_gap := knownIntegerGapTheory_from_imports
      real_open_target := openRealExponentialVariant_axiom
      real_known_lb := erdos_1.variants.proved.real_lb
      real_known_lb_strong := erdos_1.variants.proved.real_lb_strong
      real_known_theory := knownRealSpacingTheory_from_imports
      exact_integer_lower_frontier_backed := by
        intro N A hA hAne
        exact erdos_1_lower_bound_exact_of_subcubeHalfCubeBoundaryLower N A hA hAne
      exact_witness_N_9 := erdos_1.variants.exists_N_9
      exact_witness_N_10 := erdos_1.variants.exists_N_10 }

/-- Short theorem alias exposing the full bridge under the original problem namespace. -/
theorem erdos_1.current.bridge : OriginalSurfaceBridge :=
  originalSurfaceBridge_from_currentCodebase

/-- Current lower-theory replacement for the original placeholder `erdos_1.variants.lb`. -/
theorem erdos_1.variants.current.lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
        (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1.variants.proved.lb

/-- Current sharp lower-theory replacement for the original placeholder `erdos_1.variants.lb_strong`. -/
theorem erdos_1.variants.current.lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
        (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1.variants.proved.lb_strong

/-- Current real lower-theory replacement separated from the open exponential real variant. -/
theorem erdos_1.variants.current.real_lb :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
        (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1.variants.proved.real_lb

/-- Current sharp real lower-theory replacement separated from the open exponential real variant. -/
theorem erdos_1.variants.current.real_lb_strong :
    ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
        (Real.sqrt (2 / Real.pi) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N :=
  erdos_1.variants.proved.real_lb_strong

/-- Explicit bridge alias for the open integer exponential target carried by `Problem1.lean`. -/
theorem erdos_1.current.open_integer_target : OpenIntegerExponentialVariant :=
  openIntegerExponentialVariant_axiom

/-- Explicit bridge alias for the open real exponential target carried by `Problem1.lean`. -/
theorem erdos_1.variants.current.real_open_target : OpenRealExponentialVariant :=
  openRealExponentialVariant_axiom

/--
Frontier-backed exact integer lower theorem obtained by combining the positive-boundary middle
lower theorem with the already formalized interval-counting argument.
-/
theorem erdos_1.variants.current.exact_integer_lower_frontier_backed :
    ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.Nonempty →
      Nat.choose A.card (A.card / 2) ≤ N :=
by
  intro N A hA hAne
  exact erdos_1_lower_bound_exact_of_subcubeHalfCubeBoundaryLower N A hA hAne

end Erdos1
