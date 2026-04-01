# Proof Note: Two-Layer To Half-Cube Vertex-Boundary Bridge

This note records an exact reformulation of the active two-layer boundary problem as a one-sided
vertex-boundary problem for a half-cube family of size `2^(n-1)`.

## Setup

Let

```math
n = 2m+1,
\qquad
P_r := \binom{[n]}{r}.
```

Let

```math
U \subseteq P_{m+1},
\qquad
V \subseteq P_m,
\qquad
|U| = |V|.
```

Define

```math
C := P_m \setminus V,
\qquad
F := C \cup U.
```

The active exact two-layer theorem is

```math
|\partial^+F| \ge |C|.
\tag{B}
```

## Half-Cube Lift

Define the lower strict half

```math
L_{m-1} := \{A \subseteq [n] : |A| \le m-1\},
```

and then define the lifted family

```math
G := L_{m-1} \cup F = L_{m-1} \cup C \cup U.
```

So \(G\) is a family in the odd cube supported on all levels up to \(m-1\), together with a
two-layer perturbation on levels \(m\) and \(m+1\).

## Size Of The Lifted Family

Because \(n = 2m+1\), we have

```math
\sum_{r=0}^{m-1} \binom{n}{r} + \binom{n}{m} = 2^{n-1}.
```

Also

```math
|F| = |C| + |U| = (|P_m|-|V|) + |U| = |P_m| = \binom{n}{m}.
```

Therefore

```math
|G|
=
\sum_{r=0}^{m-1} \binom{n}{r} + |F|
=
\sum_{r=0}^{m-1} \binom{n}{r} + \binom{n}{m}
=
2^{n-1}.
```

So every equal-size two-layer pair \((C,U)\) lifts to a family \(G\) of exact half-cube size.

## Positive Boundary Decomposition

Since all levels below \(m\) are already full in \(G\), the only positive-boundary contributions of
\(G\) occur in ranks \(m\), \(m+1\), and \(m+2\).

More precisely:

- the rank-\(m\) part of \(\partial^+G\) is exactly the missing middle layer
  ```math
  P_m \setminus C = V;
  ```
- the rank-\(m+1\) part is exactly
  ```math
  \partial^\uparrow C \setminus U;
  ```
- the rank-\(m+2\) part is exactly
  ```math
  \partial^\uparrow U.
  ```

Hence

```math
\partial^+G
=
(P_m \setminus C)
\sqcup
(\partial^\uparrow C \setminus U)
\sqcup
\partial^\uparrow U
=
(P_m \setminus C) \sqcup \partial^+F.
```

Therefore

```math
|\partial^+G|
=
|P_m \setminus C| + |\partial^+F|
=
|U| + |\partial^+F|.
```

## Exact Equivalence

Because

```math
|U| + |C| = |P_m| = \binom{n}{m},
```

the active two-layer theorem \((B)\) is equivalent to

```math
|\partial^+G| \ge \binom{n}{m}.
\tag{H}
```

Indeed:

```math
|\partial^+F| \ge |C|
\quad\Longleftrightarrow\quad
|U| + |\partial^+F| \ge |U| + |C|
\quad\Longleftrightarrow\quad
|\partial^+G| \ge \binom{n}{m}.
```

So the exact route can be read as:

> every lifted half-cube family \(G\) of the special form
> ```math
> G = L_{m-1} \cup C \cup U,
> \qquad
> C \subseteq P_m,\quad U \subseteq P_{m+1},\quad |U| = |P_m \setminus C|,
> ```
> has positive boundary at least \(\binom{n}{m}\).

## Stronger Additive Target

The active stronger target is

```math
|\partial^+F| \ge |C| + m.
```

By the same calculation, this is equivalent to

```math
|\partial^+G| \ge \binom{n}{m} + m.
\tag{H+}
```

So the first additive improvement

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2}\right\rfloor
```

is naturally a half-cube positive-boundary gap theorem.

## Model Templates In The Lifted Picture

The two model templates on the two-layer side become the following half-cube families.

### Full-lower template

If

```math
F = P_m,
```

then

```math
G = L_m.
```

This is the ordinary lower half of the odd cube.

### Principal-star template

If

```math
F = C_\star \cup U_\star
=
\{A \in P_m : 0 \in A\}
\cup
\{B \in P_{m+1} : 0 \in B\},
```

then

```math
G
=
L_{m-1}
\cup
\{A \in P_m : 0 \in A\}
\cup
\{B \in P_{m+1} : 0 \in B\}.
```

So the two-template shifted theory may be read as a two-extremizer half-cube theory.

## Identification As Hamming Balls

For \(x \subseteq [n]\), write

```math
B(x,m) := \{A \subseteq [n] : |A \triangle x| \le m\}
```

for the Hamming ball of radius \(m\) around \(x\).

### Full-lower template

Take \(x = \varnothing\). Then

```math
|A \triangle \varnothing| = |A|,
```

so

```math
B(\varnothing,m) = \{A \subseteq [n] : |A| \le m\} = L_m.
```

Thus the lifted full-lower template is exactly the radius-\(m\) Hamming ball around the empty
vertex.

### Principal-star template

Take \(x = \{0\}\). Then

- if \(0 \in A\), we have
  ```math
  |A \triangle \{0\}| = |A| - 1;
  ```
- if \(0 \notin A\), we have
  ```math
  |A \triangle \{0\}| = |A| + 1.
  ```

Therefore

```math
A \in B(\{0\},m)
\quad\Longleftrightarrow\quad
\bigl(0 \in A \text{ and } |A| \le m+1\bigr)
\ \text{or}\
\bigl(0 \notin A \text{ and } |A| \le m-1\bigr).
```

But this is exactly

```math
L_{m-1}
\cup
\{A \in P_m : 0 \in A\}
\cup
\{B \in P_{m+1} : 0 \in B\}
=
G.
```

So the lifted principal-star template is exactly the radius-\(m\) Hamming ball around the vertex
\(\{0\}\).

## Consequence For The Active Stability Program

The two model templates are therefore not merely convenient shifted examples. They are exactly the
two Hamming balls

```math
B(\varnothing,m)
\qquad\text{and}\qquad
B(\{0\},m)
```

of size `2^(n-1)` in the odd cube.

So the active stronger target can be read as follows:

> among the special lifted half-cube families
> ```math
> G = L_{m-1} \cup C \cup U,
> \qquad
> |G| = 2^{n-1},
> ```
> prove a one-sided boundary gap away from the two radius-\(m\) Hamming balls
> \(B(\varnothing,m)\) and \(B(\{0\},m)\).

This is the cleanest current formulation of the route as a local half-cube vertex-isoperimetric
stability problem.

## Transfer Of The First-Shell `+m` Law

Write

```math
G_{\mathrm{full}} := B(\varnothing,m) = L_m,
\qquad
G_\star := B(\{0\},m).
```

For a lifted family

```math
G = L_{m-1} \cup C \cup U,
```

define its half-cube defect by

```math
\Delta_{\mathrm{hc}}(G) := |\partial^+G| - \binom{n}{m}.
```

By the exact equivalence proved above,

```math
\Delta_{\mathrm{hc}}(G) = |\partial^+F| - |C| = \Delta(F).
```

Also, because every lifted family contains the same common lower part \(L_{m-1}\), symmetric
difference from the lifted templates is preserved:

```math
|G \triangle G_{\mathrm{full}}|
=
|F \triangle F_{\mathrm{full}}|,
```
```math
|G \triangle G_\star|
=
|F \triangle F_\star|.
```

Therefore the model-template first-shell theorem on the two-layer side transfers verbatim to the
half-cube side:

> if \(G\) is a lifted shifted family and
> ```math
> |G \triangle G_{\mathrm{full}}| = 2
> \quad\text{or}\quad
> |G \triangle G_\star| = 2,
> ```
> then
> ```math
> \Delta_{\mathrm{hc}}(G) = m,
> ```
> equivalently
> ```math
> |\partial^+G| = \binom{n}{m} + m.
> ```

So the local first-shell theorem already proved on paper may now be read entirely in half-cube
language:

- the first shell around the two Hamming balls \(B(\varnothing,m)\) and \(B(\{0\},m)\),
  restricted to the lifted family class, has exact boundary gap \(m\);
- the five symbolic two-layer shell classes are exactly the five lifted first-shell classes
  around those two Hamming balls.

## Global Half-Cube Stability Form Of The Active Target

The remaining stronger theorem can now be stated in the following clean form.

Let \(G\) range over lifted shifted families

```math
G = L_{m-1} \cup C \cup U,
\qquad
|G| = 2^{n-1}.
```

Then the active global target is:

```math
G \notin \{G_{\mathrm{full}}, G_\star\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m.
\tag{H+_{\mathrm{shifted}}}
```

Equivalently,

```math
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m
```

within the lifted shifted class.

This is the cleanest current global theorem toward the additive improvement:
first prove \((H+_{\mathrm{shifted}})\), then show the transported sum-distinct families avoid the
two equality balls.

## Why This Bridge Matters

This reformulation does not solve the active theorem by itself, but it sharpens the proof search.

The remaining exact and stronger targets are now:

- exact:
  ```math
  |\partial^+G| \ge \binom{n}{m};
  ```
- additive:
  ```math
  |\partial^+G| \ge \binom{n}{m} + m;
  ```

for half-cube families \(G\) of the special lifted form above.

This brings the active route much closer in shape to the cube vertex-isoperimetric stability
literature: the problem is now visibly a local/stability statement around two special half-cube
extremizers, rather than only a two-layer bookkeeping problem.
