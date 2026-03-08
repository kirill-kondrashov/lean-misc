# Lean Experiments

Lean formalization experiments and problem-focused developments, using a project structure modeled after:
<https://github.com/kirill-kondrashov/yoccos-theorem>.

## Current contents

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
- include the Problem #142 DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_iff_deepmind`)
- include the strengthened explicit-profile DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_explicit_iff_deepmind`)
- keep checker output explicit about temporary axiom frontier debt where present

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
✅ All checked items are free of 'sorry'. Temporary Erdős #142 axiom debt is explicitly allowed.
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

## Erdős #142: current status and references

- As of March 7, 2026, Problem #142 remains open; this repository keeps the full matched-profile route behind the temporary frontier axioms `Erdos142.splitGap_k3_upper_exponent_gt_half_frontier`, `Erdos142.splitGap_k4_profile_dominance_frontier`, and `Erdos142.splitGap_kge5_profile_dominance_frontier`, now packaged as the stronger off-path object `Erdos142.Problem142MatchedProfileFrontier`. The active honest route instead uses source-backed split packages for every branch, with practical target `Erdos142.MainAllSourceBackedSplitGap`, named internal endpoint `Erdos142.Problem142AllSourceBackedSplitData`, and statement-level theorem surface `Erdos142.SourceBackedSplitRoute`. On that active practical route, there is no remaining coupling debt.

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
- The $k = 4$ branch now also has a source-backed split package `K4SourceBackedSplitWitness`; see [ErdosProblems/Problem142Literature.lean](./ErdosProblems/Problem142Literature.lean).
- The $k = 5$ branch now also has a source-backed split package `K5SourceBackedSplitWitness`, and every fixed $k \ge 6$ has the tail-family source-backed split package `Kge6SourceBackedSplitWitness`; see [ErdosProblems/Problem142Literature.lean](./ErdosProblems/Problem142Literature.lean).
- These are exposed at the gap layer as `K3SourceBackedSplitGap`, `K4SourceBackedSplitGap`, `K5SourceBackedSplitGap`, and the tail family `Kge6SourceBackedSplitGap`, with practical target `MainAllSourceBackedSplitGap`; they are also exported to the statement-level theorem surface `SourceBackedSplitRoute`; see [ErdosProblems/Problem142Gap.lean](./ErdosProblems/Problem142Gap.lean).
- Therefore, on the active post-pivot route, the repository now has explicit source-backed split control for every branch. The stronger unresolved content is no longer on the practical route; it survives only in the off-path matched-profile theorem family, including the stronger local target $U_4(N)=O(L_4(N))$.

Progress toward a proof in this repository:

1. The repository formalizes the exact asymptotic-formula target for Problem #142, and also a stronger explicit-profile variant; see [ErdosProblems/Problem142.lean#L251](./ErdosProblems/Problem142.lean#L251) and [ErdosProblems/Problem142.lean#L267](./ErdosProblems/Problem142.lean#L267).
2. It reduces the proof burden to explicit branchwise profile witnesses: superpolylogarithmic for $k = 3$, polylogarithmic for $k = 4$, and iterated-logarithmic for fixed $k \ge 5$; see [ErdosProblems/Problem142.lean#L323](./ErdosProblems/Problem142.lean#L323) through [ErdosProblems/Problem142.lean#L380](./ErdosProblems/Problem142.lean#L380).
3. It proves the honest source-backed $k = 3$ comparison in the true direction
   ```math
   L_3(N)=O(U_3(N)),
   ```
   under the imported exponent regime $\beta < 1/2$; the transport and comparison theorems are in [ErdosProblems/Problem142Literature.lean#L1078](./ErdosProblems/Problem142Literature.lean#L1078), [ErdosProblems/Problem142Literature.lean#L1151](./ErdosProblems/Problem142Literature.lean#L1151), and [ErdosProblems/Problem142Literature.lean#L1196](./ErdosProblems/Problem142Literature.lean#L1196).
4. It packages that result into a first-class source-backed $k = 3$ split witness with explicit exponent $\beta = 1/12$; see [ErdosProblems/Problem142Literature.lean#L1391](./ErdosProblems/Problem142Literature.lean#L1391).
5. It first reorganizes the downstream gap so that $k = 3$ and then $k = 4$ are no longer part of the active unresolved matched-profile frontier, and then refines the route further so that $k = 5$ and finally every fixed $k \ge 6$ are also handled by explicit source-backed split packages on the practical target `MainAllSourceBackedSplitGap`.
6. It packages the resulting practical route into the named endpoint `Problem142AllSourceBackedSplitData`, exports it to the statement-level theorem surface `SourceBackedSplitRoute`, and provides the theorem `all_source_backed_split_data_of_mainAllSourceBackedSplitGap`, which gives all upper variants together with correct branchwise split data for $k = 3$, $k = 4$, $k = 5$, and every fixed $k \ge 6$; see [ErdosProblems/Problem142Gap.lean](./ErdosProblems/Problem142Gap.lean).
7. It also packages the stronger conjectural route into the named off-path object `Problem142MatchedProfileFrontier`, which cleanly isolates the full matched-profile debt from the practical split route; see [ErdosProblems/Problem142Gap.lean](./ErdosProblems/Problem142Gap.lean).
8. It also proves that the old stronger $k = 3$ route would need an exponent threshold $\beta > 1/2$; see [ErdosProblems/Problem142Literature.lean#L1060](./ErdosProblems/Problem142Literature.lean#L1060). The current source-backed import does not provide that, so this route has been closed rather than left vague.

The active missing mathematical theorems now live only on the stronger off-path matched-profile route. The practical route has been stabilized at source-backed split strength for every branch.

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
