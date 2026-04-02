# Note: Restricted Half-Cube Stability And The Harper Local-Stability Paradigm

This note records the closest current literature template for the active stronger branch.

## The Published Model

Keevash and Long proved a local stability theorem for Harper's vertex-isoperimetric inequality in
the cube:

- if a family \(A \subseteq \{0,1\}^n\) has the same size as a Hamming ball and boundary close to
  minimal, then \(A\) is close to a Hamming ball;
- more sharply, if \(A\) differs from a Hamming ball by `2D` points, then its vertex boundary is
  bounded below by an explicit benchmark family \(J\).

Primary source:

- Peter Keevash, Eoin Long, *Stability for vertex isoperimetry in the cube*,
  J. Combin. Theory Ser. B 145 (2020), 83–115.
  PDF: <https://people.maths.ox.ac.uk/keevash/papers/VIP.pdf>
  DOI: <https://doi.org/10.1016/j.jctb.2020.04.009>

At the half-cube size `2^(n-1)` in odd dimension `n = 2m+1`, the two relevant Hamming balls are

```math
B(\varnothing,m)
\qquad\text{and}\qquad
B(\{0\},m).
```

These are exactly the two model templates on the current branch.

## Our Restricted Variant

The active stronger route does **not** ask for full Harper stability on all subsets of
\(\{0,1\}^n\) of size `2^(n-1)`.

Instead, it asks for a one-sided boundary theorem on the restricted lifted class

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

Within this class, the exact route is

```math
|\partial^+G| \ge \binom{n}{m},
```

and the active stronger target is

```math
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m
```

for shifted \(G \in \mathcal H_m\).

So our theorem is a **restricted one-sided half-cube analogue** of the Harper local-stability
problem.

## Why The Comparison Is Useful

The Keevash–Long theorem suggests the right proof shape:

1. identify the extremizers;
2. classify the first local shell around them;
3. compare every nearby family to an explicit benchmark family;
4. deduce a quantitative boundary gap from distance to the extremizers.

This is exactly the structure our current branch has reached:

- the two model extremizers are now identified as the half-cube Hamming balls
  `B(emptyset,m)` and `B({0},m)`;
- the distance-`2` shell around them is already proved on paper in the restricted lifted class;
- every such first-shell family has boundary exactly
  ```math
  |\partial^+G| = \binom{n}{m} + m.
  ```

So the missing theorem is no longer a vague “stronger bound” problem. It is now a local stability
problem in the precise Harper/Keevash–Long style, but with:

- a restricted family class `\mathcal H_m`,
- one-sided positive boundary `\partial^+`,
- and the target gap `+m`.

## The Concrete Next Theorem Shape

The cleanest next theorem candidate is:

```math
\text{for shifted } G \in \mathcal H_m,\qquad
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\Longrightarrow
|\partial^+G| \ge \binom{n}{m} + m.
```

That is the restricted half-cube Hamming-ball stability theorem recorded in
[PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md).

So the current state of the project is:

- exact route: one explicit two-layer / half-cube theorem still open;
- stronger route: one explicit restricted local-stability theorem still open;
- and both are now formulated in the same geometric language as the closest current literature.
