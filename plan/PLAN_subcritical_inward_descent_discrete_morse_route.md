# Plan: Subcritical Counterexample Descent Via Discrete Morse Theory

This note records the new active proof route for the improved-bound branch.

The live theorem candidate is the subcritical counterexample-descent statement from
[PROOF_shifted_gap_reduces_to_inward_descent.md](./PROOF_shifted_gap_reduces_to_inward_descent.md):

```math
F \notin \{F_{\mathrm{full}},F_\star\},
\qquad
d(F)\ge 4,
\qquad
\Delta(F)<m
\Longrightarrow
\exists F'
\text{ shifted such that }
d(F')=d(F)-2
\text{ and }
\Delta(F')<m.
```

The point of this note is to make that theorem constructive enough to attack.

## Why Discrete Morse Theory Fits

The shifted balanced two-layer families form a finite combinatorial state space.

The desired theorem says that every subcritical state

```math
\Delta(F)<m
```

admits an inward move toward the template set

```math
\{F_{\mathrm{full}},F_\star\}
```

that stays below the threshold `m`.

That is exactly the shape of a discrete gradient-flow statement:

- vertices: shifted balanced two-layer families;
- subcritical predicate:
  ```math
  \Delta(F)<m;
  ```
- radial coordinate:
  ```math
  d(F);
  ```
- critical cells: the two templates;
- gradient move: an inward corner move reducing `d(F)` by `2` while preserving
  `\Delta(F)<m`.

So the intended topological slogan is:

```math
\{\text{shifted }F : \Delta(F)<m\}
```

should collapse inward onto the two templates.

## State Space

Let

```math
n=2m+1,
\qquad
F=C\cup U,
\qquad
C\subseteq \binom{[n]}{m},
\qquad
U\subseteq \binom{[n]}{m+1},
\qquad
|U|=\left|\binom{[n]}{m}\setminus C\right|.
```

Restrict to shifted families.

Relative to either template `F_full` or `F_star`, a shifted family can be encoded by two order
ideals / Ferrers-type diagrams:

- a lower defect diagram recording which template lower vertices are missing;
- an upper excess diagram recording which non-template upper vertices are present.

Because the family is shifted, these diagrams are monotone and admit outer-corner / inner-corner
moves.

## Candidate Gradient Move

Fix the nearer template `T(F)` achieving `d(F)`.

The candidate move `F -> F'` is:

1. choose the outermost misplaced lower or upper corner of `F` relative to `T(F)`;
2. move it one step inward toward `T(F)`;
3. rebalance the paired layer so that total size stays fixed;
4. re-shift if needed, but only inside the same local shape class.

In the Ferrers picture, this is a corner slide toward the template.

The intended outcome is:

```math
d(F')=d(F)-2.
```

The theorem will follow if this move can also be shown to satisfy

```math
\Delta(F')<m.
```

The current preferred route to that local inequality is now the averaging reduction in
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md):
it is enough to show that admissible inward moves exist and have non-increasing average defect.

## Proof Strategy

### Step 1. Template-Relative Ferrers Encoding

Encode every shifted family relative to the nearer template `T(F)` by a finite shape

```math
\Sigma(F).
```

Requirements:

- `\Sigma(F)` determines `d(F)`;
- `\Sigma(F)` has a well-defined set of outer corners;
- distance `2` corresponds exactly to the five already-classified first-shell shapes.

Proof sketch:

- for `F_full`, identify `C` with an order ideal in colex/lex rank order and `U` with an order
  ideal in the opposite upper rank order;
- for `F_star`, use the same construction inside the star/non-star splitting;
- prove the shifted condition is exactly the order-ideal condition in those coordinates.

### Step 2. Local Corner-Move Lemma

Show that if `d(F)\ge 4`, then `\Sigma(F)` has an outer corner whose inward slide preserves the
shifted balanced class.

Proof sketch:

- because `d(F)` counts symmetric-difference boxes relative to the nearer template, distance at
  least `4` means at least two boxes are misplaced;
- in a finite order ideal, some misplaced box is exposed as an outer corner;
- the balance constraint means the lower and upper diagrams differ by the same total amount, so
  an inward paired move exists.

### Step 3. Distance-Reduction Lemma

Show that the chosen corner move satisfies

```math
d(F')=d(F)-2.
```

Proof sketch:

- one misplaced template cell is repaired;
- one paired compensating cell is removed from the wrong side;
- no new misplacements are created outside the local move rectangle.

This is the clean combinatorial heart of the radial part of the gradient.

### Step 4. Average Inward-Move Inequality

Show that the admissible inward moves satisfy a uniform or weighted average inequality

```math
\sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F')\,\Delta(F')
\le
\Delta(F),
```

where `M_{\mathrm{in}}(F)` is the set of admissible inward moves and `\mu_F` is a probability
distribution on it.

Proof sketch:

- write `\Delta(F')-\Delta(F)` as a sum of local boundary changes inside the move rectangle;
- sum that expression over all admissible inward moves, or over a canonical weighted family of
  such moves;
- prove that the total drift is non-positive.

This is the key lemma. Discrete Morse theory organizes the proof, but this local
average-drift estimate is the real engine.

### Step 5. Subcritical-Preservation For One Move

Deduce from Step 4 that under the subcritical hypothesis `\Delta(F)<m`, some admissible inward
move satisfies

```math
\Delta(F')<m.
```

Proof sketch:

- if every admissible inward move had defect at least `m`, then any uniform or weighted average of
  those defects would also be at least `m`;
- Step 4 rules this out when `\Delta(F)<m`.

### Step 6. Discrete Gradient / Collapse

Once Steps 2-5 are proved, orient every shifted subcritical non-template family toward one chosen
inward move.

Then:

- `d(F)` strictly decreases along every directed edge;
- hence there are no cycles;
- every directed path terminates at distance `2` or `0`.

Distance `0` is a template.
Distance `2` is handled by the already-proved first-shell theorem:

```math
d(F)=2 \Longrightarrow \Delta(F)=m.
```

So subcritical families cannot terminate at distance `2`, which proves the two live blockers.

## What Has To Be Proved

This route is valid only if the following lemmas are established:

1. template-relative Ferrers encoding for shifted two-layer families;
2. existence of an inward balanced corner move when `d(F)\ge 4`;
3. exact distance drop `d(F')=d(F)-2`;
4. a local average inward-move inequality;
5. the deduction of one subcritical-preserving inward move from that average inequality.

Among these, Lemma 4 is the real unknown.

## Why This Is Better Than More Enumeration

This route turns the current problem into a finite list of proof obligations on local moves.

That is better than more brute-force because:

- the first-shell theorem is already known;
- the false unconditional inward-descent theorem showed that shell data alone is misleading;
- the remaining issue is genuinely structural: identify which local moves are forced to preserve
  subcriticality below the threshold `m`.

So the next useful commit on this branch should either:

- prove one of the four lemmas above, or
- sharpen the corner-move / local-boundary formalism so that one of those lemmas becomes
  realistically attackable.
