# Plan: First Additive Improvement Beyond The Middle-Binomial Bound

This note records the first concrete strengthening target beyond the current literature-level
benchmark

```math
N \ge \binom{n}{\lfloor n/2\rfloor}.
```

## Proposed Next Bound

The current best explicit next target is

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

For odd `n = 2m+1`, this is

```math
N \ge \binom{2m+1}{m} + m.
```

This is the smallest nontrivial strengthening currently suggested by the shifted-shell data that
also appears dimension-stable.

The current theorem-candidate note for the first rigid shell is:

- [PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md)

The exact half-cube bridge for this target is now recorded in
[PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md](./PROOF_two_layer_to_half_cube_vertex_boundary_bridge.md).
Under that lift, the additive `+m` target becomes the half-cube one-sided boundary inequality

```math
|\partial^+G| \ge \binom{n}{m} + m.
```

More sharply, that bridge note now identifies the two model templates with the two radius-`m`
Hamming balls

```math
B(\varnothing,m)
\qquad\text{and}\qquad
B(\{0\},m)
```

of size `2^(n-1)`. So the active stronger target is now best read as a local stability/gap
theorem around those two half-cube Hamming balls, restricted to the special lifted family class.

More sharply again, that same note now transfers the proved first-shell law into half-cube
language:

```math
|G \triangle B(\varnothing,m)| = 2
\ \text{or}\
|G \triangle B(\{0\},m)| = 2
\quad\Longrightarrow\quad
|\partial^+G| = \binom{n}{m} + m
```

for lifted shifted families `G`.

The resulting global theorem candidate is now split out in
[PLAN_restricted_half_cube_hamming_ball_stability.md](./PLAN_restricted_half_cube_hamming_ball_stability.md).
That note isolates the exact statement still missing on the stronger branch:
within the lifted shifted class, every family other than the two balls
`B(emptyset,m)` and `B({0},m)` should satisfy

```math
|\partial^+G| \ge \binom{n}{m} + m.
```

From this point on, that restricted half-cube note should be treated as the commit gate for the
additive route: the next commit should land only if it advances either

- the proof that the shifted equality set in the lifted class is exactly those two balls, or
- the proof of the global inequality above.

## Why This Is The Right Next Target

On the stronger two-layer branch, the first nontrivial shifted shell is the template-distance `2`
shell. Its exact minimum gap is now:

- shifted `n = 5`:
  ```math
  |\partial^+F| - |C| = 2;
  ```
- shifted `n = 7`:
  ```math
  |\partial^+F| - |C| = 3;
  ```
- shifted `n = 9`:
  ```math
  |\partial^+F| - |C| = 4;
  ```
- shifted `n = 11`:
  ```math
  |\partial^+F| - |C| = 5.
  ```
- shifted `n = 13`:
  ```math
  |\partial^+F| - |C| = 6.
  ```
- shifted `n = 15`:
  ```math
  |\partial^+F| - |C| = 7.
  ```
- shifted `n = 17`:
  ```math
  |\partial^+F| - |C| = 8.
  ```
- shifted `n = 19`:
  ```math
  |\partial^+F| - |C| = 9.
  ```
- shifted `n = 21`:
  ```math
  |\partial^+F| - |C| = 10.
  ```
- shifted `n = 23`:
  ```math
  |\partial^+F| - |C| = 11.
  ```
- shifted `n = 25`:
  ```math
  |\partial^+F| - |C| = 12.
  ```

So the first-shell minimum gap currently matches

```math
m = \frac{n-1}{2}.
```

This is stronger than the earlier fallback target

```math
\binom{n}{\lfloor n/2\rfloor} + 1,
```

and is the first additive improvement that now looks structurally plausible across several
dimensions.

The current computational frontier for this first-shell check is now:

- exact support through shifted `n = 25`;
- the old `n = 15` slowdown was removed by replacing full comparability in the local shifted
  generator by immediate cover relations in the shifted poset;
- shifted `n = 27` does not return on a short/medium run with the current first-shell probe;
- so the current exact computational frontier on this narrow branch is `n = 25`.

## Conjectural Two-Layer Form

Let

```math
F := \left(\binom{[n]}{m}\setminus V\right)\cup U,
\qquad
n = 2m+1,
\qquad
|U| = |V|.
```

Let `\mathcal E` be the two shifted equality templates:

1. the full lower layer;
2. the principal-star two-layer family.

The current first concrete conjecture is:

```math
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| \ge |C| + m.
```

At the shifted level, this can be broken into two increasingly realistic statements.

### Shifted Version A

For shifted `F`,

```math
\operatorname{dist}(F,\mathcal E) = 2
\quad\Longrightarrow\quad
|\partial^+F| - |C| = m.
```

### Shifted Version B

For shifted `F`,

```math
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| - |C| \ge m.
```

Version A is directly supported by exact data in `n = 5,7,9,11,13`. Version B is the actual
target needed for the first additive literature improvement.
Version A is now directly supported through shifted `n = 25`.
More sharply, the new local zero-defect summary now shows that in shifted `n = 7,9,11,13`, every
template-local family with distance at most `10` from the two model templates already has
strictly positive defect unless it is one of the templates themselves.
In the lifted half-cube language, Version B becomes:

```math
G \notin \{B(\varnothing,m), B(\{0\},m)\}
\quad\Longrightarrow\quad
|\partial^+G| \ge \binom{n}{m} + m
```

within the lifted shifted class.

## How This Connects To The Sum-Distinct Transport

The current formal route already reduces the middle-binomial benchmark to the exact two-layer
theorem

```math
|\partial^+F| \ge |C|.
```

So the additive improvement program is:

1. prove the stronger two-layer estimate
   ```math
   |\partial^+F| \ge |C| + m
   ```
   on the transported family class, or at least on shifted families first;
2. prove that the transported sum-distinct families never realize the equality templates;
3. use the same arithmetic closure mechanism to upgrade the endpoint to
   ```math
   N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
   ```

## Immediate Research Program

### Step 1. Prove Shifted Equality Classification

Promote the two shifted equality templates from computational evidence to theorem status.

### Step 2. Prove The Shifted First-Shell Formula

Prove:

```math
\operatorname{dist}(F,\mathcal E)=2
\quad\Longrightarrow\quad
|\partial^+F|-|C| = m.
```

This is the most concrete theorem now strongly suggested by exact data.
It is also the current best-supported theorem that points directly to the additive `+m` target.
Moreover, the exact shifted first shell still has the same template split in every newly checked
dimension:

```math
d=2:\ 1\ \text{full-lower orbit} + 4\ \text{principal-star orbits},
```

with all five shifted orbit representatives having margin exactly `m`.

The new local decomposition summary sharpens this further in shifted
`n = 7, 9, 11, 13, 15, 17, 19, 21`:

- the full-lower side is always a single `(1,1)` move type;
- the principal-star side always splits into exactly three move types
  ```math
  (0,2),\ (1,1),\ (2,0),
  ```
  with multiplicities `1, 2, 1`;
- every one of those four principal-star representatives still has margin exactly `m`.

So the current first-shell theorem candidate is now not just a scalar gap law, but a rigid local
move classification.

The sharper move-type statement is recorded separately in
[PROOF_shifted_first_shell_move_type_theorem_candidate.md](./PROOF_shifted_first_shell_move_type_theorem_candidate.md).

That note now identifies all five first-shell shifted orbits symbolically through `n = 21`:

- `1` full-lower orbit;
- `4` principal-star orbits, namely the move types
  ```math
  (0,2),\ (1,1)_{\mathrm{lower\ add / upper\ remove}},\ (1,1)_{\mathrm{lower\ remove / upper\ add}},\ (2,0).
  ```

Equivalently, the principal-star first shell now has a clean four-class split:

- pure upper;
- mixed lower-add / upper-remove;
- mixed lower-remove / upper-add;
- pure lower.

More sharply, the proof note now gives direct boundary counts for those five symbolic classes and
proves, for each of them individually,

```math
\Delta(F)=m.
```

More sharply again, that proof note now proves the shifted classification statement around the two
model templates:

- every shifted family at distance `2` from the full-lower template is the unique full-lower shell
  class;
- every shifted family at distance `2` from the principal-star template is one of the four
  principal-star shell classes;
- consequently, every shifted family at distance `2` from one of the two model templates satisfies
  ```math
  \Delta(F)=m.
  ```

This sharper decomposition branch is currently exact through shifted `n = 21`.
The next dimension `n = 23` now returns at the aggregate level as well:
the decomposition probe reports `entry_count = 6` and `pair_count = 7`, consistent with the same
`2` equality entries plus `4` distance-`2` move-type entries.
What is still missing is a clean row-level extraction of those exact `n = 23` move rows:
even after the compact delta-signature refactor, `n = 23` is still not a short/medium-run
computation at the full decomposition level, even though the coarser first-shell gap law already
returns exactly through shifted `n = 25`.
What is also still missing mathematically is the global bridge from the two model templates to the
actual shifted equality set: the note now proves the whole first shell around
`F_{\mathrm{full}}` and `F_\star`, but Step 1 still has to show that these are exactly the
shifted equality templates.

### Step 3. Prove Shifted Lower Bounds Beyond The First Shell

Prove:

```math
\operatorname{dist}(F,\mathcal E)\ge 2
\quad\Longrightarrow\quad
|\partial^+F|-|C| \ge m.
```

This is weaker than a full shell-envelope formula, but already enough for the additive target.

### Step 4. Exclude Equality Templates For Transported Families

Show the transported two-layer family coming from a sum-distinct set cannot be one of the equality
templates. Since template distance changes in even steps, that should force

```math
\operatorname{dist}(F,\mathcal E)\ge 2.
```

### Step 5. Close The First Additive Improvement

Combine Steps 3 and 4 with the existing formal endpoint route to obtain

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

## Why We Focus On This Instead Of A Larger Target

There may be stronger true bounds. But this one has three advantages:

- it is already suggested by exact data in four odd dimensions;
- it is naturally tied to the first nontrivial shell around the equality templates;
- it is strong enough to be a genuine literature improvement while still looking reachable from
  the current two-layer route.

So this is now the best explicit “next theorem” target beyond the current middle-binomial
benchmark.
