# Lean Experiments

Lean formalization experiments and problem-focused developments, using a project structure modeled after:
<https://github.com/kirill-kondrashov/yoccos-theorem>.

## Current contents

- `Erdos1.erdos_1`:
  Erdős Problem 1 and several sum-distinct variants, following the statement layer from
  DeepMind's `formal-conjectures`; the main open and literature statements are currently
  imported as local axioms, while the exact finite benchmark `least_N_3` is proved in
  [ErdosProblems/Problem1.lean](./ErdosProblems/Problem1.lean).

- `TaoExercises.TaoBook.Chapter2.exercise_2_3`:
  Terence Tao, *Solving mathematical problems: a personal perspective*, Exercise 2.3
  (`x^4 + 131 = 3y^4` has no integer solutions in integers).

- `TaoExercises.TaoBook.Chapter2.exercise_2_6`:
  Problem 2.6 (Shklarsky et al. 1962, p. 14):
  if `k` is odd, then `1^k + 2^k + · · · + n^k` is divisible by `1 + 2 + · · · + n`.

- `ErdosProblems` (Erdős #142 family):
  statement, explicit-profile strengthening, and gap decomposition are present under
  `Erdos142` (`erdos_problem_142`, `erdos_problem_142_explicit`, `Problem142Gap`)
  with `erdos_problem_142_iff_deepmind`, `erdos_problem_142_explicit_iff_deepmind`,
  and the current plan series in `plan/` (`PLAN_erdos_problem_142.md` and follow-on files).

## Toolchain and dependencies

- Lean: `leanprover/lean4:v4.27.0`
- mathlib: `v4.27.0`
- doc-gen4: `v4.27.0`

## Build

```bash
lake build
lake exe check_axioms
```

## Verification

All solved exercises are checked to ensure they:

- do not use `sorry`
- depend only on the base axioms `propext`, `Quot.sound`, and `Classical.choice`
- build the top-level `ErdosProblems` library, including the `Erdos1` modules
- include the checked `Erdos1` theorems
  (`Erdos1.erdos_1.variants.weaker`, `Erdos1.choose_middle_isEquivalent`,
  and the temporary-axiom wrapper `Erdos1.erdos_1_solution_axiom`)
- include the Problem #142 DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_iff_deepmind`)
- include the strengthened explicit-profile DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_explicit_iff_deepmind`)
- keep checker output explicit about temporary axiom frontier debt where present

The checker now imports the top-level `ErdosProblems` library, so `Erdos1` is built as part of
`make check`. It currently reports two `Erdos1` theorems that are fully local and base-axiom
clean: `Erdos1.erdos_1.variants.weaker` and `Erdos1.choose_middle_isEquivalent`.
It also reports the open-problem wrapper `Erdos1.erdos_1_solution_axiom`, with the placeholder
axiom `Erdos1.erdos_1` treated as temporary allowed axiom debt in the same style as the current
`Erdos142` frontier checks.
The exact-value theorems proved by `native_decide` are still excluded from this checker because the
current policy treats `Lean.ofReduceBool` / `Lean.trustCompiler` as non-base axioms.

Run:

```bash
make check
make verify
```

Expected Output:

```text
✅ The proof of 'TaoExercises.TaoBook.Chapter2.exercise_2_3' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'TaoExercises.TaoBook.Chapter2.exercise_2_6' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos1.erdos_1.variants.weaker' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos1.choose_middle_isEquivalent' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
🟡 The proof of 'Erdos1.erdos_1_solution_axiom' is free of 'sorry' but relies on temporary allowed axiom debt.
Axioms used:
- propext
- Quot.sound
- Classical.choice
- Erdos1.erdos_1
Temporarily allowed non-base axioms (must be proved later):
- Erdos1.erdos_1
✅ The proof of 'Erdos142.erdos_problem_142_iff_deepmind' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos142.erdos_problem_142_explicit_iff_deepmind' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos142.erdos_problem_142_solution_axiom' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
🟡 The proof of 'Erdos142.erdos_problem_142_of_mainSplitGap_and_frontier' is free of 'sorry' but relies on temporary allowed axiom debt.
Axioms used:
- propext
- Quot.sound
- Classical.choice
- Erdos142.splitGap_k3_upper_exponent_gt_half_frontier
- Erdos142.splitGap_k4_profile_dominance_frontier
- Erdos142.splitGap_kge5_profile_dominance_frontier
Temporarily allowed non-base axioms (must be proved later):
- Erdos142.splitGap_k3_upper_exponent_gt_half_frontier
- Erdos142.splitGap_k4_profile_dominance_frontier
- Erdos142.splitGap_kge5_profile_dominance_frontier
✅ All checked items are free of 'sorry'. Temporary Erdős #1/#142 axiom debt is explicitly allowed.
```

## Useful Make targets

```bash
make cache      # fetch Mathlib cache
make build      # lake build
make check      # lake exe check_axioms
make verify     # compare make check output with README expected output
make auto-build # cache refresh + build + check
make docs       # build API docs
```

## CI workflow (GitHub Actions)

- `.github/workflows/lean_action_ci.yml`
- Pull requests, pushes, and manual runs all execute a single `leanprover/lean-action` build job.
- Docs are not generated/deployed in CI.
- Workflow concurrency is enabled with `cancel-in-progress: true`.

## Erdős #1: current status

The local formalization of Erdős Problem #1 is in
[ErdosProblems/Problem1.lean](./ErdosProblems/Problem1.lean). It introduces:

- `Erdos1.IsSumDistinctSet` for sum-distinct subsets of `{1, ..., N}`.
- `Erdos1.IsSumDistinctRealSet` for the real-valued spacing variant on `(0, N]`.
- `Erdos1.erdos_1` and the upstream variant family under `Erdos1.erdos_1.variants`.

Current proof status:

- `Erdos1.erdos_1` remains a local axiom-level placeholder for the open exponential conjecture.
- `Erdos1.erdos_1.variants.weaker` is now proved from elementary counting on `Finset.subsetSum`.
- `Erdos1.erdos_1.variants.least_N_3` and `Erdos1.erdos_1.variants.least_N_5` are proved exactly
  by finite verification.
- `Erdos1.erdos_1.variants.least_N_9` remains axiomatized.
- [ErdosProblems/Problem1ExactValues.lean](./ErdosProblems/Problem1ExactValues.lean) now records
  certified OEIS witness sets for `HasSumDistinctSetCard 161 9` and `HasSumDistinctSetCard 309 10`,
  exposed as `Erdos1.erdos_1.variants.exists_N_9` and `Erdos1.erdos_1.variants.exists_N_10`.
- [ErdosProblems/Problem1Literature.lean](./ErdosProblems/Problem1Literature.lean) now contains:
  the exact imported Dubroff-Fox-Xu lower bound, its real-valued analogue, a Bohman
  upper-construction surface, and derived lower-bound packages
  `erdos_1_variants_lb_strong_from_choose_middle_asymptotic`,
  `erdos_1_variants_lb_from_choose_middle_asymptotic`,
  `dubroffFoxXuSharpLowerBoundReal_from_imports`, and
  `bestKnownIntegerGap_from_imports`.
- [ErdosProblems/Problem1Derived.lean](./ErdosProblems/Problem1Derived.lean) now exposes
  non-axiomatic downstream aliases
  `Erdos1.erdos_1.variants.proved.lb`,
  `Erdos1.erdos_1.variants.proved.lb_strong`,
  `Erdos1.erdos_1.variants.proved.real_lb`,
  `Erdos1.erdos_1.variants.proved.real_lb_strong`, and
  `Erdos1.erdos_1.known.best_known_integer_gap`.
- [ErdosProblems/Problem1Integer.lean](./ErdosProblems/Problem1Integer.lean) now bundles the
  currently known integer lower theory into
  `IntegerLowerBound`,
  `IntegerLowerBoundStrong`,
  `KnownIntegerLowerTheory`,
  `integer_lower_bound_exact_imported`, and
  `integer_lower_bound_avg`.
- [ErdosProblems/Problem1Gap.lean](./ErdosProblems/Problem1Gap.lean) now makes the current integer
  gap explicit as API:
  `OpenIntegerExponentialVariant`,
  `KnownIntegerGapTheory`, and
  `knownIntegerGapTheory_from_imports`.
- [ErdosProblems/Problem1Real.lean](./ErdosProblems/Problem1Real.lean) now separates the
  real-valued branch into:
  `RealSpacingLowerBound`,
  `RealSpacingLowerBoundStrong`,
  `KnownRealSpacingTheory`,
  `real_spacing_lower_bound_avg`, and the explicit open-conjecture alias
  `OpenRealExponentialVariant`.
- The sharp middle-binomial asymptotic is now proved locally; the remaining Problem #1 bottlenecks
  are the imported literature axioms for the exact Dubroff-Fox-Xu/Bohman results together with the
  still-public placeholder surfaces in [ErdosProblems/Problem1.lean](./ErdosProblems/Problem1.lean).

## Erdős #142: current status and references

- As of March 7, 2026, Problem #142 remains open; this repository keeps the full matched-profile route behind the temporary frontier axioms `Erdos142.splitGap_k3_upper_exponent_gt_half_frontier`, `Erdos142.splitGap_k4_profile_dominance_frontier`, and `Erdos142.splitGap_kge5_profile_dominance_frontier`, while the strongest honest local $k=3$ endpoint is now the source-backed split package `Erdos142.K3SourceBackedSplitGap`, built from Kelley-Meka's explicit $\beta = 1 / 12$ upper witness together with Behrend lower data and the true compatibility direction `k3_behrend_lower_template =O k3_upper_profile`.

Exact formulation of Erdős Problem #142 in this repository:

First define the extremal function:

```math
r_k(N)=\max\bigl\{|A| : A \subseteq \{1,\dots,N\},\ A \text{ contains no non-trivial } k\text{-term arithmetic progression}\bigr\}.
```

Then the problem asks:

```math
\forall k \ge 3,\ \exists f_k : \mathbb{N} \to \mathbb{R}
\text{ such that }
r_k(N)=\Theta(f_k(N)) \qquad (N \to \infty).
```

Equivalently: for each fixed $k \ge 3$, the function $r_k(N)$ has an asymptotic formula up to multiplicative constants.

In the local Lean formalization, this is exactly the statement `ErdosProblems.erdos_problem_142`; see [ErdosProblems/Problem142.lean#L267](./ErdosProblems/Problem142.lean#L267) and [ErdosProblems/Problem142.lean#L283](./ErdosProblems/Problem142.lean#L283).

What is already proven in this repository:

- The exact problem statement and its explicit variant are formalized in [ErdosProblems/Problem142.lean](./ErdosProblems/Problem142.lean).
- The $k = 3$ branch already has a source-backed split package `K3SourceBackedSplitWitness`; see [ErdosProblems/Problem142Literature.lean#L446](./ErdosProblems/Problem142Literature.lean#L446).
- In that $k = 3$ package, the upper-side exponent is fixed explicitly at $\beta = 1/12$, matching the current Kelley-Meka-based import; see [ErdosProblems/Problem142Literature.lean#L448](./ErdosProblems/Problem142Literature.lean#L448).
- The formalization also proves the true $k = 3$ comparison in the source-backed direction,
  $L_3(N)=O(U_3(N))$, packaged as `lower_isBigO_upper`; see [ErdosProblems/Problem142Literature.lean#L453](./ErdosProblems/Problem142Literature.lean#L453).
- This is exposed at the gap layer as `K3SourceBackedSplitGap`; see [ErdosProblems/Problem142Gap.lean#L127](./ErdosProblems/Problem142Gap.lean#L127).
- Therefore, in the active post-pivot formalization, the remaining unresolved mathematical frontier is no longer the $k = 3$ branch. It is the higher-branch profile-matching content for $k = 4$ and for each fixed $k \ge 5$.

Progress toward a proof in this repository:

1. The repository formalizes the exact asymptotic-formula target for Problem #142, and also a stronger explicit-profile variant; see [ErdosProblems/Problem142.lean#L251](./ErdosProblems/Problem142.lean#L251) and [ErdosProblems/Problem142.lean#L267](./ErdosProblems/Problem142.lean#L267).
2. It reduces the proof burden to explicit branchwise profile witnesses: superpolylogarithmic for $k = 3$, polylogarithmic for $k = 4$, and iterated-logarithmic for fixed $k \ge 5$; see [ErdosProblems/Problem142.lean#L323](./ErdosProblems/Problem142.lean#L323) through [ErdosProblems/Problem142.lean#L380](./ErdosProblems/Problem142.lean#L380).
3. It proves the honest source-backed $k = 3$ comparison in the true direction
   ```math
   L_3(N)=O(U_3(N)),
   ```
   under the imported exponent regime $\beta < 1/2$; the transport and comparison theorems are in [ErdosProblems/Problem142Literature.lean#L1078](./ErdosProblems/Problem142Literature.lean#L1078), [ErdosProblems/Problem142Literature.lean#L1151](./ErdosProblems/Problem142Literature.lean#L1151), and [ErdosProblems/Problem142Literature.lean#L1196](./ErdosProblems/Problem142Literature.lean#L1196).
4. It packages that result into a first-class source-backed $k = 3$ split witness with explicit exponent $\beta = 1/12$; see [ErdosProblems/Problem142Literature.lean#L1391](./ErdosProblems/Problem142Literature.lean#L1391).
5. It reorganizes the downstream gap so that $k = 3$ is no longer part of the active unresolved matched-profile frontier; the active post-pivot target is [ErdosProblems/Problem142Gap.lean#L239](./ErdosProblems/Problem142Gap.lean#L239), and the remaining coupling debt is isolated in [ErdosProblems/Problem142Gap.lean#L363](./ErdosProblems/Problem142Gap.lean#L363).
6. It also proves that the old stronger $k = 3$ route would need an exponent threshold $\beta > 1/2$; see [ErdosProblems/Problem142Literature.lean#L1060](./ErdosProblems/Problem142Literature.lean#L1060). The current source-backed import does not provide that, so this route has been closed rather than left vague.

The active missing mathematical theorems are now the higher-branch profile-matching statements.

Definition of Landau asymptotic domination:

For real-valued functions $f(N)$ and $g(N)$, the statement

```math
f(N)=O(g(N)) \qquad (N \to \infty)
```

means that there exist constants $A > 0$ and $N_0$ such that

```math
|f(N)| \le A\,|g(N)| \qquad \text{for all } N \ge N_0.
```

In this section, every occurrence of $=O$ is used in exactly this sense.

Likewise,

```math
f(N)=\Theta(g(N))
```

means both

```math
f(N)=O(g(N))
\qquad \text{and} \qquad
g(N)=O(f(N)).
```

**1. Theorem target for $k = 4$.**

**Given**

Assume the following two hypotheses.

Upper-side input:

```math
r_4(N)=O\!\left(\frac{C_u N}{(\log(N+2))^{c_u}}\right).
```

Lower-side input:

```math
\frac{C_\ell N}{(\log(N+2))^{c_\ell}}=O(r_4(N)).
```

**Where**

- $r_4(N)$ is the maximal size of a $4$-term arithmetic-progression-free subset of $\{1,\dots,N\}$.
- $N$ is the ambient interval size.
- $C_u, C_\ell$ are positive constants independent of $N$.
- $c_u, c_\ell$ are positive polylogarithmic decay exponents.
- $\log$ is the natural logarithm.
- $=O$ is Landau asymptotic domination as $N \to \infty$.
- $N+2$ is a harmless positive shift used so the logarithm is always defined in the formal model.

**What to prove**

Prove the comparison theorem:

```math
\frac{C_u N}{(\log(N+2))^{c_u}}
=
O\!\left(\frac{C_\ell N}{(\log(N+2))^{c_\ell}}\right).
```

**Where**

- $C_u N / (\log(N+2))^{c_u}$ is the current split upper-profile template.
- $C_\ell N / (\log(N+2))^{c_\ell}$ is the current split lower-profile template.
- $=O$ is the desired eventual dominance needed to turn the split $k = 4$ data into one matched `K4ProfileWitness`.

**2. Theorem target for each fixed $k \ge 5$.**

**Given**

For each fixed $k \ge 5$, assume the following two hypotheses.

Upper-side input:

```math
r_k(N)=O\!\left(\frac{C_u(k)\,N}{(\log\log(N+3))^{c_u(k)}}\right).
```

Lower-side input:

```math
\frac{C_\ell(k)\,N}{(\log\log(N+3))^{c_\ell(k)}}=O(r_k(N)).
```

**Where**

- $r_k(N)$ is the maximal size of a $k$-term arithmetic-progression-free subset of $\{1,\dots,N\}$.
- $k$ is a fixed integer with $k \ge 5$.
- $N$ is the ambient interval size.
- $C_u(k), C_\ell(k)$ are positive constants that may depend on $k$ but not on $N$.
- $c_u(k), c_\ell(k)$ are positive iterated-log decay exponents that may depend on $k$.
- $\log\log$ is the iterated natural logarithm.
- $=O$ is Landau asymptotic domination as $N \to \infty$ for each fixed $k$.
- $N+3$ is a harmless positive shift used so both logarithms are defined in the formal model.

**What to prove**

Prove the comparison theorem for each fixed $k \ge 5$:

```math
\frac{C_u(k)\,N}{(\log\log(N+3))^{c_u(k)}}
=
O\!\left(\frac{C_\ell(k)\,N}{(\log\log(N+3))^{c_\ell(k)}}\right)
\qquad (k \ge 5).
```

**Where**

- $C_u(k)\,N / (\log\log(N+3))^{c_u(k)}$ is the current split upper-profile template in the $k \ge 5$ branch.
- $C_\ell(k)\,N / (\log\log(N+3))^{c_\ell(k)}$ is the current split lower-profile template in the $k \ge 5$ branch.
- $k \ge 5$ means the theorem is needed uniformly as a family over all higher branches.
- $=O$ is the desired eventual dominance needed to turn the split $k \ge 5$ data into matched `Kge5ProfileWitness` packages.

Geometric illustration (schematic; common factor $N$ suppressed):

![Schematic profile-matching frontier for the k=4 and k>=5 branches](./assets/erdos142/profile_matching_frontier.png)

The figure is schematic only. It is not plotting computed data for $r_k(N)$; it is drawing the profile templates from Theorem `1` and Theorem `2` after suppressing the common factor $N$.

Left panel: the $k = 4$ branch.

Blue curve: the upper template from Theorem `1`.

```math
U_4(N)=\frac{C_u N}{(\log(N+2))^{c_u}}
```

Red curve: the lower template from Theorem `1`.

```math
L_4(N)=\frac{C_\ell N}{(\log(N+2))^{c_\ell}}
```

Dashed dark-red curve: a comparison envelope for a schematic constant $A > 0$.

```math
A\,L_4(N)
```

Shaded red region: the part where the desired domination has not yet been achieved.

```math
U_4(N)>A\,L_4(N)
```

Dashed vertical line labeled $N_0$: a schematic threshold after which the picture shows

```math
U_4(N)\le A\,L_4(N) \qquad (N \ge N_0).
```

What is actually drawn is $U_4(N)/N$, $L_4(N)/N$, and $A\,L_4(N)/N$, so only the decay part in $\log(N)$ is visible.

Right panel: the $k \ge 5$ branch.

Blue curve: the upper template from Theorem `2`.

```math
U_k(N)=\frac{C_u(k)\,N}{(\log\log(N+3))^{c_u(k)}}
```

Red curve: the lower template from Theorem `2`.

```math
L_k(N)=\frac{C_\ell(k)\,N}{(\log\log(N+3))^{c_\ell(k)}}
```

Dashed dark-red curve: a comparison envelope for a schematic constant $A > 0$.

```math
A\,L_k(N)
```

Shaded red region: the part where the desired domination has not yet been achieved.

```math
U_k(N)>A\,L_k(N)
```

Dashed vertical line labeled $N_0$: a schematic threshold after which the picture shows

```math
U_k(N)\le A\,L_k(N) \qquad (N \ge N_0).
```

What is actually drawn is $U_k(N)/N$, $L_k(N)/N$, and $A\,L_k(N)/N$, so only the decay part in $\log\log(N)$ is visible.

In both panels, the point of the picture is to visualize the missing theorem: eventually, the blue curve should lie below the dashed comparison envelope, which is itself a constant multiple of the red curve. That is exactly the dominance statement

```math
\text{upper profile} = O(\text{lower profile})
```

up to a multiplicative constant.

References:

- Erdős Problems #142 (status/discussion): <https://www.erdosproblems.com/142>
- Kelley, Z.; Meka, R. (2023), *Strong Bounds for 3-Progressions*:
  <https://arxiv.org/abs/2302.05537>
- Green, B.; Tao, T. (2017), *New bounds for Szemerédi's theorem, III: a polylogarithmic bound
  for r_4(N)* (Mathematika): <https://ora.ox.ac.uk/objects/uuid:1d09eef3-01e2-4ce0-ab9d-2892019812c8>
- Leng, J.; Sah, A.; Sawhney, M. (2024), *Improved bounds for Szemerédi's theorem*:
  <https://arxiv.org/abs/2402.17995>
