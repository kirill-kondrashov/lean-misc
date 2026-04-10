# Plan: First Additive Improvement Beyond The Middle-Binomial Bound

This note records the first explicit target beyond the current published lower bound

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

## Target Bound

The active stronger target is

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

For odd `n = 2m+1`, this is

```math
N \ge \binom{2m+1}{m} + m.
```

## Why This Is The Right First Improvement

On the shifted two-layer model, the first-shell law is now rigid:

```math
d(F)=2 \Longrightarrow \Delta(F)=m,
\qquad
\Delta(F):=|\partial^+F|-|C|.
```

That first-shell identity has exact computational support through shifted `n = 25`, and the
template-local zero-defect exclusion has exact support through shifted `n = 17`.

This is enough to justify `+m` as the first serious approximation target. Larger-`n` scans are
now frozen support, not active objectives.

## Half-Cube Form

By
[PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md),
the additive target becomes the restricted half-cube inequality

```math
|\partial^+G| \ge \binom{n}{m} + m
```

for lifted families

```math
G = L_{m-1} \cup C \cup U.
```

The two model templates become the Hamming balls

```math
B(\varnothing,m)
\qquad\text{and}\qquad
B(\{0\},m).
```

So the active global theorem is now exactly the restricted stability statement isolated in
[PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md).

## Current Proof Reduction

The stronger branch is no longer about extending shell computations. It is now blocked by one
global theorem in shifted form:

```math
F \notin \{F_{\mathrm{full}},F_\star\}
\Longrightarrow
\Delta(F)\ge m.
```

The current theorem-first reduction of that statement is:

- [PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md)
- [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md)
- [PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md)
- [PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
- [PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
- [PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md)

The sharp current blocker is:

```math
\text{construct a canonical local weight scheme on admissible inward moves}
```

that proves the signed multiplicity-balance inequality, hence a discrete gradient on the
subcritical shifted region.

## Commit Gate

The next commit on the additive route should land only if it advances one of:

- shifted equality classification
  ```math
  \Delta(F)=0 \Longrightarrow F \in \{F_{\mathrm{full}},F_\star\};
  ```
- shifted global `+m` gap
  ```math
  F \notin \{F_{\mathrm{full}},F_\star\} \Longrightarrow \Delta(F)\ge m;
  ```
- the canonical-weight local theorem reducing those two blockers.
