# Proof Note: Subcritical Discrete Gradient Conditional On A Canonical Weight Scheme

This note records the strongest rigorous statement currently obtained on the Morse-theoretic route.

The goal is to prove that the subcritical shifted region admits a discrete gradient toward the two
model templates. The purpose of this note is:

1. to state a clean conditional theorem that really gives such a gradient; and
2. to identify the exact blocker left after the current reductions.

## Morse-Theoretic Setup

Fix

```math
n = 2m+1.
```

Let `X_m` be the finite set of shifted balanced two-layer families

```math
F = C \cup U,
\qquad
C \subseteq \binom{[n]}{m},
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
|U| = \left|\binom{[n]}{m}\setminus C\right|.
```

Define the defect

```math
E(F) := \Delta(F) := |\partial^+F| - |C|.
```

Let the two model templates be

```math
p_0 := F_{\mathrm{full}},
\qquad
p_1 := F_\star.
```

Define the radial function

```math
r(F) := d(F) := \min\bigl(|F \triangle p_0|,\ |F \triangle p_1|\bigr).
```

Define the subcritical region

```math
X_{<m} := \{F \in X_m : E(F) < m\}.
```

## Admissible Inward Moves

For `F \in X_m` with `r(F)\ge 4`, write

```math
M_{\mathrm{in}}(F)
:=
\{F' \in X_m : r(F') = r(F)-2\}.
```

These are the admissible inward moves toward the template set.

## First-Shell Input

By
[PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md),
the following first-shell theorem is already proved on paper:

```math
r(F)=2 \Longrightarrow E(F)=m.
\tag{FS}
```

So no family in the subcritical region `X_{<m}` can lie at radius `2`.

## Why The Bare Averaging Reduction Is Not Yet A Real Reduction

The previous note
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
showed that the descent statement would follow if, for each `F`, one could find a probability
distribution `\mu_F` on `M_{\mathrm{in}}(F)` such that

```math
\sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F')\,E(F') \le E(F).
\tag{AVG}_\mu
```

However, taken with completely arbitrary existential weights, `(AVG)_\mu` is logically equivalent
to the direct existence of a non-increasing move:

```math
\exists \mu_F \text{ satisfying } (AVG)_\mu
\quad\Longleftrightarrow\quad
\exists F' \in M_{\mathrm{in}}(F)\text{ with }E(F') \le E(F).
```

Indeed:

- if such an `F'` exists, take the Dirac measure at `F'`;
- conversely, if every `F'` had `E(F') > E(F)`, then every convex combination would also be
  `> E(F)`.

So the bare averaging statement is not yet an actual simplification of the problem.

## The Correct Local Target: A Canonical Weight Scheme

To get a genuine reduction, one must specify a weight rule in advance.

A **canonical weight scheme** is a rule assigning to each `F` with `r(F)\ge 4` a probability
distribution

```math
\mu_F : M_{\mathrm{in}}(F) \to [0,1]
```

determined functorially from the local Ferrers / corner geometry of `F`, rather than by choosing a
best move after the fact.

The intended examples are:

- uniform weights on the outer corners;
- weights proportional to a local corner multiplicity;
- or any explicit local formula depending only on the move rectangles.

## Conditional Discrete-Gradient Theorem

Assume:

1. **First shell** `(FS)`:
   ```math
   r(F)=2 \Longrightarrow E(F)=m.
   ```

2. **Inward-move existence**:
   for every `F \in X_m` with `F \notin \{p_0,p_1\}` and `r(F)\ge 4`,
   the set `M_{\mathrm{in}}(F)` is nonempty.

3. **Canonical average inequality**:
   there exists a canonical weight scheme `\mu_F` such that for every
   `F \in X_{<m}` with `F \notin \{p_0,p_1\}` and `r(F)\ge 4`,
   one has
   ```math
   \sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F')\,E(F') \le E(F).
   \tag{CAVG}
   ```

Then `X_{<m}` admits a discrete gradient toward `{p_0,p_1}`.

### More Explicitly

There exists a map

```math
g : X_{<m}\setminus\{p_0,p_1\} \to X_{<m}
```

such that for every `F` in its domain,

```math
r(g(F)) = r(F)-2.
```

Hence:

- `r` strictly decreases along every gradient edge `F -> g(F)`;
- there are no directed cycles;
- every gradient path starting in `X_{<m}` terminates at one of `p_0,p_1`.

### Proof

Fix `F \in X_{<m}\setminus\{p_0,p_1\}`.

By `(FS)`, `r(F)` cannot equal `2`, so necessarily `r(F)\ge 4`.

By the inward-move existence hypothesis, `M_{\mathrm{in}}(F)` is nonempty.
By `(CAVG)` and the inequality `E(F)<m`, not every `F' \in M_{\mathrm{in}}(F)` can satisfy

```math
E(F') \ge m.
```

Otherwise the weighted average in `(CAVG)` would also be at least `m`, contradiction.

So there exists at least one `F' \in M_{\mathrm{in}}(F)` with

```math
E(F')<m.
```

Choose `g(F)` to be the lexicographically least such `F'` under any fixed total order on `X_m`.
Then

```math
g(F) \in X_{<m}
\qquad\text{and}\qquad
r(g(F)) = r(F)-2.
```

This defines the desired discrete gradient.

Since `r` strictly decreases along every edge, directed cycles are impossible.
Every gradient path therefore terminates.
It cannot terminate at radius `2` by `(FS)`, because `r(F)=2` forces `E(F)=m`, while all states in
the path lie in `X_{<m}`.
Hence only the radius-`0` states `p_0,p_1` can be terminal.

This proves the claim.

## Sharp Current Blocker

The theorem above isolates the precise missing ingredient:

```math
\text{construct a canonical weight scheme } \mu_F \text{ and prove } (CAVG).
```

By
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md),
this is equivalent to proving a signed local atom-balance inequality for that same canonical
weighting.
The current preferred canonical weighting is now the uniform measure on exposed corners, isolated
in
[PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md](./PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md).

So the active blocker is no longer just “find some inward move”.
It is:

- instantiate the now-defined canonical exposed-corner parametrisation to prove `K(F)\ne\varnothing`
  for shifted balanced non-template states;
- prove the locality package for the canonical bad/good incidence sets attached to those corners;
- prove the uniform-corner bad-incidence set injects into the uniform-corner good-incidence set.

## Why This Is The PhD-Level Obstruction

At this point the remaining gap is not a matter of reformulation.

The state space, radial function, first-shell barrier, and conditional gradient theorem are all in
place. What is still missing is a genuinely new combinatorial inequality:

```math
\text{a local bad-to-good incidence transport for admissible inward moves.}
```

That is the exact place where the current program stops.
