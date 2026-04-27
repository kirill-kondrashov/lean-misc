# Plan: Erdős #1 Additive Stability Program

This is the master plan for the active Erdős #1 work.

The goal is **not** to solve the full exponential Erdős conjecture. The goal is to improve the
accepted approximation beyond the current middle-binomial benchmark.

## External Baseline

The refreshed literature note is:

- [NOTE_erdos1_position_against_current_literature.md](./NOTE_erdos1_position_against_current_literature.md)

As of **April 24, 2026**, the accepted all-`n` original-problem lower bound is

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

The Erdős Problems page still marks the original problem open, and the April 2026 search did not
find an accepted published all-`n` improvement beyond Dubroff-Fox-Xu.

## Active Target

The first target worth pursuing is the additive improvement

```math
N \ge \binom{n}{\lfloor n/2\rfloor}
    + \left\lfloor\frac{n-1}{2}\right\rfloor.
```

For `n = 2m + 1`, this is

```math
N \ge \binom{2m+1}{m} + m.
```

The target is tracked in:

- [PLAN_first_additive_improvement_beyond_middle_binomial.md](./PLAN_first_additive_improvement_beyond_middle_binomial.md)
- [PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md)

## Current Mathematical Form

The active model is the balanced two-layer family

```math
F = C \cup U,
\qquad
C \subseteq \binom{[2m+1]}{m},
\qquad
U \subseteq \binom{[2m+1]}{m+1},
\qquad
|U| = \left|\binom{[2m+1]}{m}\setminus C\right|.
```

Define

```math
\Delta(F) := |\partial^+F| - |C|.
```

The exact middle-binomial bottleneck is `Delta(F) >= 0`. That is no longer the active research
endpoint, because proving it only recovers the known published bound.

The active stronger endpoint is the shifted stability gap

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\Longrightarrow
\Delta(F) \ge m.
```

Here

```math
F_{\mathrm{full}} = \binom{[2m+1]}{m},
```

and

```math
F_\star
=
\{A \in \binom{[2m+1]}{m}: 0 \in A\}
\cup
\{B \in \binom{[2m+1]}{m+1}: 0 \in B\}.
```

## Half-Cube Stability Form

The two-layer family lifts to

```math
G = L_{m-1} \cup C \cup U,
\qquad
|G| = 2^{2m}.
```

The two model templates lift to Hamming balls

```math
B(\varnothing,m)
\qquad\text{and}\qquad
B(\{0\},m).
```

The active half-cube target is therefore

```math
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\Longrightarrow
|\partial^+G| \ge \binom{2m+1}{m} + m
```

inside the restricted lifted shifted class. The bridge is recorded in:

- [PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md)
- [PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md](./PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md)

## Active Reduction Chain

The current proof architecture is:

1. first-shell theorem around the two templates:
   [PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md)
2. reduction of equality / `+m` stability to subcritical inward descent:
   [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md)
3. discrete-Morse route for subcritical descent:
   [PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md)
4. average inward-move reduction:
   [PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
5. atom-balance reformulation:
   [PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
6. conditional gradient theorem:
   [PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md)
7. template-relative exposed-corner parametrization:
   [PROOF_template_relative_corner_parametrization.md](./PROOF_template_relative_corner_parametrization.md)
8. current sharp local target after shifted-template instantiation gives raw corners:
   [PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md](./PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md)

## Current Blocker

The abstract finite lower-set mismatch lemma is now formalized in
`ErdosProblems/Problem1CubeExposedRepair.lean`. It states the following with the current unbundled
relation API, using `WellFounded lt` and `WellFounded (fun a b => lt b a)` for the two
minimal/maximal choices.

```math
\begin{gathered}
F,T\text{ are lower sets},\qquad |F|=|T|,\qquad F\ne T
\\
\Longrightarrow
\exists x\in T\setminus F,\ \exists z\in F\setminus T
\text{ such that }(x,z)\text{ is a raw exposed repair pair.}
\end{gathered}
```

Proof shape: choose `x` minimal in `T\F` and `z` maximal in `F\T`. Minimality gives `(REST)`;
maximality plus lower-set closure gives `(DEL)`; if `z<x`, lower-set closure of `T` gives
`z in T`, contradicting `z in F\T`, so `(COMP)` is automatic.

The abstract consequences of a supplied raw repair pair are formalized in
`ErdosProblems/Problem1CubeExposedRepair.lean`: preservation of the lower-set property,
one-add/one-delete cardinality preservation, and exact fixed/global template-distance drop.
The immediate remaining theorem is to instantiate this mismatch lemma to the shifted rank posets
and the selected nearest template `T(F)`, proving `K(F)` is nonempty for every shifted balanced
non-template state. The hypothesis `\Delta(F)<m` is not needed for raw-corner existence; it
belongs to the later average-defect step.

After `K(F)\ne\varnothing` is proved, the next local theorem is the incidence step:

```math
\text{construct a local bad-to-good incidence injection for uniform corner weights.}
```

More explicitly, prove an injection

```math
\Phi_F : \mathcal B(F) \hookrightarrow \mathcal G(F),
```

where bad incidences are created boundary atoms plus lost lower atoms, and good incidences are
destroyed boundary atoms plus gained lower atoms.

This would imply the uniform-corner average inequality, hence subcritical inward descent, hence
shifted equality classification and the global `+m` gap.

## Background Only

The exact middle-binomial two-layer inequality remains useful background:

- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)

It is not an active plan because it does not by itself improve the published state of the art.

## Commit Gate

The next useful commit should advance one of:

- the uniform-corner incidence injection;
- the shifted-template instantiation of the lower-set mismatch lemma;
- the shifted zero-defect classification;
- the shifted global `+m` gap;
- the transport step proving that the sum-distinct families relevant to Erdős #1 avoid the two
  equality balls.

Do not add new brute-force search branches unless they falsify or prove one of these theorem
shapes. The existing low-dimensional enumeration is already sufficient for theorem design.
