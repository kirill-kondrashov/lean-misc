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

Every \(G \in \mathcal H_m\) has size

```math
|G| = 2^{n-1}.
```

The two model extremizers in this class are

```math
G_{\mathrm{full}} = B(\varnothing,m),
\qquad
G_\star = B(\{0\},m).
```

These are exactly the two lifted two-layer templates identified in
[PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md).

## Exact Theorem In Half-Cube Form

The current exact bottleneck is equivalent to:

```math
G \in \mathcal H_m
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m}.
```

This is just the half-cube lift of the two-layer theorem

```math
|\partial^+F| \ge |C|.
```

## Stronger Additive Target In Half-Cube Form

The current additive target is equivalent to the following shifted half-cube stability theorem.

### Restricted Half-Cube Hamming-Ball Stability

For shifted \(G \in \mathcal H_m\),

```math
G \notin \{G_{\mathrm{full}}, G_\star\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m.
\tag{HC+}
```

Equivalently,

```math
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m
```

inside the lifted shifted class \(\mathcal H_m\).

This is the cleanest current global theorem candidate for the stronger branch.

The closest literature template for this theorem is recorded in
[NOTE_restricted_half_cube_stability_literature_bridge.md](./NOTE_restricted_half_cube_stability_literature_bridge.md):
it is a restricted one-sided half-cube analogue of the Harper/Keevash–Long local-stability
paradigm around two Hamming balls.

The exact reduction of these lifted blockers back to the underlying two-layer gap problem is now
recorded in
[PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md](./PROOF_restricted_half_cube_stability_reduces_to_two_layer_gap.md).
That note shows that the two lifted blockers are equivalent to:

- shifted two-layer zero-defect classification
  ```math
  \Delta(F)=0 \Longrightarrow F \in \{F_{\mathrm{full}}, F_\star\};
  ```
- shifted two-layer global `+m` gap
  ```math
  F \notin \{F_{\mathrm{full}}, F_\star\}
  \Longrightarrow
  \Delta(F)\ge m.
  ```

## What Is Already Done

The local first-shell theorem is now proved at the model-template level.

If \(G \in \mathcal H_m\) is shifted and

```math
|G \triangle G_{\mathrm{full}}| = 2
\quad\text{or}\quad
|G \triangle G_\star| = 2,
```

then

```math
|\partial^+G| = \binom{n}{m} + m.
```

This comes from the proved two-layer first-shell theorem plus the exact half-cube bridge.

There is now a second blocker-facing local exclusion result as well: the dedicated local
zero-defect summary in `tools/problem1_odd_profile_search.py` shows that, within template
distance at most `10`, there are no extra shifted equality families beyond the two balls in

- `n = 7`, with minimal positive margin `3`;
- `n = 9`, with minimal positive margin `4`;
- `n = 11`, with minimal positive margin `5`;
- `n = 13`, with minimal positive margin `6`.
- `n = 15`, with minimal positive margin `7`;
- `n = 17`, with minimal positive margin `8`.

So blocker `1` now has exact local support on a sizable neighborhood of the two Hamming-ball
templates, not just on the first shell.

That local evidence is now sufficient for theorem-shaping purposes. Further neighborhood scans are
out of scope unless they directly settle a structural sublemma for a live blocker.

## What Is Still Missing

The remaining global gap has three pieces.

### 1. Equality Classification In The Shifted Lifted Class

Prove that the shifted equality set in \(\mathcal H_m\) is exactly

```math
\{G_{\mathrm{full}}, G_\star\}.
```

At the moment this is strongly supported by exact shifted computation, but not yet proved.

### 2. Global Stability Away From The Two Balls

Prove \((HC+)\), namely:

```math
G \notin \{G_{\mathrm{full}}, G_\star\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m
```

for shifted \(G \in \mathcal H_m\).

This is the real global theorem still missing on the stronger branch.

### 3. Transport Exclusion

Show that the half-cube families produced by the sum-distinct transport cannot land in the two
equality balls \(G_{\mathrm{full}}\) and \(G_\star\), and ideally stay at positive distance from
them.

Once that is done, the additive improvement follows through the existing closure route.

The revised theorem-first program for doing this is now recorded in
[PLAN_improved_bound_theorem_first_program.md](./PLAN_improved_bound_theorem_first_program.md).
More sharply, the current preferred two-layer reduction is now written out in
[PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md):
the unconditional inward-descent theorem is false, but the weaker subcritical counterexample-
descent theorem in the shifted class would still imply both equality classification and the global
`+m` gap.
The active proof sketch for that subcritical theorem is now the discrete-Morse route in
[PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md),
with the local defect step further isolated as an average inward-move inequality in
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md).
That local inequality is now reduced further to a signed multiplicity balance on created/destroyed
boundary and lower atoms in
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md).

## Commit Gate

The next commit on this stronger branch should land only if it advances one of the following two
items:

1. equality classification in the shifted lifted class:
   ```math
   \mathcal E_{\mathrm{shifted}}(\mathcal H_m)
   =
   \{B(\varnothing,m), B(\{0\},m)\};
   ```
2. global restricted half-cube stability:
   ```math
   G \notin \{B(\varnothing,m), B(\{0\},m)\}
   \quad\Longrightarrow\quad
   |\partial^+G| \ge \binom{n}{m} + m
   ```
   for shifted \(G \in \mathcal H_m\).

So this note is now the hard gate for future progress claims on the additive route.

In particular, further larger-`n` shell or neighborhood scans are not a reason to commit unless
they directly reduce one of the two items above.

## Why This Plan Is Better

This formulation removes two sources of ambiguity:

- the stronger branch is no longer phrased only as a two-layer defect problem;
- the extremizers are no longer ad hoc templates, but explicit Hamming balls.

So the active stronger route is now best read as:

1. a restricted half-cube vertex-isoperimetric stability theorem around two Hamming balls;
2. plus an exclusion theorem for the transported sum-distinct families.
