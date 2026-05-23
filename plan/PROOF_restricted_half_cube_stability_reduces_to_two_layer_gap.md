# Proof Note: Restricted Half-Cube Stability Reduces To Two-Layer Gap

This note records the exact equivalence between the current half-cube stability blockers and the
corresponding two-layer gap statements.

## Setup

Let

```math
n = 2m+1,
\qquad
P_m := \binom{[n]}{m},
\qquad
P_{m+1} := \binom{[n]}{m+1}.
```

Let

```math
F = C \cup U,
\qquad
C \subseteq P_m,
\qquad
U \subseteq P_{m+1},
\qquad
|U| = |P_m \setminus C|.
```

Define the two-layer defect

```math
\Delta(F) := |\partial^+F| - |C|.
```

Let

```math
G := L_{m-1} \cup C \cup U.
```

Define the lifted half-cube defect

```math
\Delta_{\mathrm{hc}}(G) := |\partial^+G| - \binom{n}{m}.
```

By
[PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md),
we have the exact identity

```math
\Delta_{\mathrm{hc}}(G) = \Delta(F).
\tag{*}
```

Let the two model two-layer templates be

```math
F_{\mathrm{full}} = P_m,
\qquad
F_\star
=
\{A \in P_m : 0 \in A\}
\cup
\{B \in P_{m+1} : 0 \in B\},
```

and let the corresponding lifted half-cube templates be

```math
G_{\mathrm{full}} = B(\varnothing,m),
\qquad
G_\star = B(\{0\},m).
```

## Equality Classification Reduces Exactly

The shifted lifted equality-classification blocker is:

```math
\mathcal E_{\mathrm{shifted}}(\mathcal H_m)
=
\{G_{\mathrm{full}}, G_\star\}.
\tag{HC-EQ}
```

Using \((*)\), this is equivalent to the shifted two-layer zero-defect classification:

```math
\Delta(F)=0
\quad\Longrightarrow\quad
F \in \{F_{\mathrm{full}}, F_\star\},
\tag{TL-EQ}
```

within the same shifted/lifted correspondence.

Indeed:

- \(G = G_{\mathrm{full}}\) if and only if \(F = F_{\mathrm{full}}\);
- \(G = G_\star\) if and only if \(F = F_\star\);
- and \(\Delta_{\mathrm{hc}}(G)=0\) if and only if \(\Delta(F)=0\).

So proving equality classification in the lifted class is exactly the same as proving equality
classification for the two-layer defect.

## Global `+m` Stability Reduces Exactly

The shifted lifted stability blocker is:

```math
G \notin \{G_{\mathrm{full}}, G_\star\}
\quad\Longrightarrow\quad
\Delta_{\mathrm{hc}}(G) \ge m.
\tag{HC+}
```

Again by \((*)\), this is equivalent to the shifted two-layer gap theorem

```math
F \notin \{F_{\mathrm{full}}, F_\star\}
\quad\Longrightarrow\quad
\Delta(F) \ge m.
\tag{TL+}
```

because the two exceptional families correspond exactly under the lift and the defects agree
exactly.

So the global restricted half-cube Hamming-ball stability theorem is not a separate third problem.
It is precisely the lifted form of the shifted two-layer `+m` gap theorem.

## Consequence For The Active Plan

The two current stronger-branch blockers can therefore be read without ambiguity as:

1. shifted two-layer zero-defect classification:
   ```math
   \Delta(F)=0
   \quad\Longrightarrow\quad
   F \in \{F_{\mathrm{full}}, F_\star\};
   ```
2. shifted two-layer global `+m` gap:
   ```math
   F \notin \{F_{\mathrm{full}}, F_\star\}
   \quad\Longrightarrow\quad
   \Delta(F)\ge m.
   ```

The half-cube language remains valuable because it matches the surrounding isoperimetric
literature, but mathematically the live blocker is exactly those two-layer statements.
