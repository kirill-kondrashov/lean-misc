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

## Why This Plan Is Better

This formulation removes two sources of ambiguity:

- the stronger branch is no longer phrased only as a two-layer defect problem;
- the extremizers are no longer ad hoc templates, but explicit Hamming balls.

So the active stronger route is now best read as:

1. a restricted half-cube vertex-isoperimetric stability theorem around two Hamming balls;
2. plus an exclusion theorem for the transported sum-distinct families.
