# Plan: Restricted Half-Cube Hamming-Ball Stability

This note isolates the cleanest current global theorem candidate behind the additive improvement

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

## Setting

Let

```math
n = 2m+1.
```

Define the lifted half-cube class

```math
\mathcal H_m
:=
\left\{
G = L_{m-1} \cup C \cup U :
C \subseteq \binom{[n]}{m},\
U \subseteq \binom{[n]}{m+1},\
|U| = \left|\binom{[n]}{m}\setminus C\right|
\right\}.
```

Every `G in H_m` has size

```math
|G| = 2^{n-1}.
```

The two model extremizers in this class are

```math
G_{\mathrm{full}} = B(\varnothing,m),
\qquad
G_\star = B(\{0\},m).
```

## Exact And Stronger Forms

The exact bottleneck is

```math
G \in \mathcal H_m
\Longrightarrow
|\partial^+G| \ge \binom{n}{m}.
```

The stronger additive target is:

```math
G \notin \{G_{\mathrm{full}}, G_\star\}
\Longrightarrow
|\partial^+G| \ge \binom{n}{m} + m.
\tag{HC+}
```

This is the cleanest current global theorem candidate for improving the published approximation.
It should be read together with
[NOTE_erdos1_position_against_current_literature.md](./NOTE_erdos1_position_against_current_literature.md):
the repo is aiming to improve the accepted bound, not to claim a full solution of Erdős #1.

## Exact Reduction Back To Two Layers

By
[PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md](./PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md),
the two lifted blockers are exactly:

- zero-defect classification
  ```math
  \Delta(F)=0 \Longrightarrow F \in \{F_{\mathrm{full}},F_\star\};
  ```
- global `+m` gap
  ```math
  F \notin \{F_{\mathrm{full}},F_\star\}
  \Longrightarrow
  \Delta(F)\ge m.
  ```

So the half-cube language is a geometric wrapper around the same two-layer blockers.

## What Is Already Done

The first-shell theorem is already proved on paper in this lifted language:

```math
|G \triangle G_{\mathrm{full}}| = 2
\quad\text{or}\quad
|G \triangle G_\star| = 2
\Longrightarrow
|\partial^+G| = \binom{n}{m} + m.
```

There is also exact local exclusion evidence near the two balls:
within template distance at most `10`, no extra shifted equality families appear in the checked
cases `n = 7, 9, 11, 13, 15, 17`.

That evidence is now sufficient for theorem-shaping purposes. It is no longer an active brute-force
objective.

## What Is Still Missing

The remaining stronger route has three pieces:

1. prove that the shifted equality set in `H_m` is exactly
   ```math
   \{G_{\mathrm{full}},G_\star\};
   ```
2. prove `(HC+)`, namely
   ```math
   G \notin \{G_{\mathrm{full}},G_\star\}
   \Longrightarrow
   |\partial^+G| \ge \binom{n}{m} + m;
   ```
3. prove that the transported sum-distinct families do not land in the two equality balls.

## Current Local Blocker

The stronger route is currently reduced to the discrete-Morse program:

- [PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md)
- [PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md)
- [PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
- [PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
- [PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md)
- [PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md](./PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md)

So the real live local theorem is now:

```math
\text{construct a local bad-to-good incidence injection for the uniform corner weights.}
```

This is sharper than an arbitrary canonical-weight existence statement: the weights are fixed to be
uniform on the canonical exposed corners, so the remaining problem is a concrete local incidence
transport inequality.

## Commit Gate

The next commit on this stronger branch should land only if it advances one of:

1. equality classification in the shifted lifted class:
   ```math
   \mathcal E_{\mathrm{shifted}}(\mathcal H_m)
   =
   \{B(\varnothing,m), B(\{0\},m)\};
   ```
2. global restricted half-cube stability:
   ```math
   G \notin \{B(\varnothing,m), B(\{0\},m)\}
   \Longrightarrow
   |\partial^+G| \ge \binom{n}{m} + m.
   ```
3. uniform-corner local incidence transport:
   ```math
   \Phi_G : \mathcal B(G) \hookrightarrow \mathcal G(G).
   ```
