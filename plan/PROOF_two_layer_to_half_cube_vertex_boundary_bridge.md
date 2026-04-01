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
