# Research Plan: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note is the master index for the current Erdős #1 route.

## Active Files

The active documentation set is now:

- [PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md)
- [PLAN_first_additive_improvement_beyond_middle_binomial.md](./PLAN_first_additive_improvement_beyond_middle_binomial.md)
- [PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md)
- [PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md)
- [PROOF_two_layer_middle_boundary_inequality.md](./PROOF_two_layer_middle_boundary_inequality.md)
- [PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md)
- [PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md](./PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md)
- [PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md)
- [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md)
- [PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
- [PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
- [PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md)
- [NOTE_erdos1_position_against_current_literature.md](./NOTE_erdos1_position_against_current_literature.md)
- [STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md](./STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md)

Everything else should be treated as archival only and compressed into
[STUCK_PLANS.md](./STUCK_PLANS.md).

## External Baseline

The current published baseline is:

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

The literature note
[NOTE_erdos1_position_against_current_literature.md](./NOTE_erdos1_position_against_current_literature.md)
now distinguishes:

- published results;
- preprints and unestablished claims;
- GitHub / database status pages.

So the repo should now be read as aiming first at a better **approximation bound**, not at a full
resolution of Erdős #1.

## Exact Bottleneck

Fix

\[
n := 2m+1,
\qquad
P_m := \binom{[n]}{m},
\qquad
C := P_m \setminus V,
\qquad
F := C \cup U.
\]

The remaining exact theorem is

\[
|\partial^+F| \ge |C|.
\]

This is the direct two-layer bottleneck isolated in
[PLAN_two_layer_middle_boundary_inequality.md](./PLAN_two_layer_middle_boundary_inequality.md).

Via
[PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md),
it is equivalent to the lifted half-cube estimate

\[
|\partial^+G| \ge \binom{n}{m}
\]

for the balanced half-cube lift

\[
G := L_{m-1} \cup C \cup U.
\]

## Active Approximation Target

The first explicit improvement target is

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

This is recorded in
[PLAN_first_additive_improvement_beyond_middle_binomial.md](./PLAN_first_additive_improvement_beyond_middle_binomial.md).

Under the half-cube bridge, the stronger route becomes the restricted stability statement

\[
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\Longrightarrow
|\partial^+G| \ge \binom{n}{m} + m.
\]

This is isolated in
[PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md).

The corresponding two-layer form is:

\[
\Delta(F) := |\partial^+F| - |C|,
\]
\[
\Delta(F)=0 \Longrightarrow F \in \{F_{\mathrm{full}},F_\star\},
\]
\[
F \notin \{F_{\mathrm{full}},F_\star\} \Longrightarrow \Delta(F)\ge m.
\]

## Current Local Blocker

The active proof architecture for the stronger branch is the discrete-Morse route in
[PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md).

Its strongest rigorous current reduction is:

- subcritical descent:
  [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md)
- average inward-move inequality:
  [PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
- signed atom balance:
  [PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
- conditional discrete gradient:
  [PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md)

So the live local theorem is now explicit:

\[
\text{construct a canonical local weight scheme on admissible inward moves}
\]

that proves the signed multiplicity-balance inequality and therefore yields a discrete gradient on
the subcritical shifted region.

## Commit Gate

The next commit should land only if it advances one of:

- the exact bottleneck
  \[
  |\partial^+F| \ge |C|;
  \]
- shifted equality classification
  \[
  \Delta(F)=0 \Longrightarrow F \in \{F_{\mathrm{full}},F_\star\};
  \]
- shifted global `+m` gap
  \[
  F \notin \{F_{\mathrm{full}},F_\star\} \Longrightarrow \Delta(F)\ge m;
  \]
- or the canonical-weight local theorem reducing those stronger blockers.
