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
More sharply, the new note
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md)
rewrites that average inequality as a signed local multiplicity balance on created/destroyed
boundary atoms and created/destroyed lower atoms.
The new rigorous conditional gradient theorem is now recorded in
[PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md):
the Morse-theoretic route really closes once one has a canonical weight scheme satisfying the
local average inequality.
The sharpest current candidate fixes that scheme to be uniform on the canonical exposed corners;
see
[PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md](./PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md).
The exposed-corner set itself is now defined in
[PROOF_template_relative_corner_parametrization.md](./PROOF_template_relative_corner_parametrization.md);
that note also proves that every raw exposed repair pair automatically satisfies the global
distance drop `d(F_k)=d(F)-2`, and the abstract distance algebra is formalized in
`ErdosProblems/Problem1CubeTemplateDistance.lean`.

The abstract supplied-corner preservation layer is formalized in
`ErdosProblems/Problem1CubeExposedRepair.lean`: a raw exposed pair preserves the relevant
lower-set property, preserves cardinality by adding one atom and deleting one atom, and triggers
the fixed/global template-distance drop.

The remaining pre-injection issue should now be attacked as a pure finite-poset lemma. If `F` and
the selected template `T(F)` are lower sets in the same shifted rank poset, have the same
cardinality, and differ, then minimal elements of `T(F)\F` and maximal elements of `F\T(F)` form a
compatible raw exposed repair pair. In Lean, with the current unbundled relation API, the clean
abstract assumptions are `WellFounded lt` and `WellFounded (fun a b => lt b a)`; finiteness plus
acyclicity of the shifted rank posets should discharge these on instantiation. This does not use
`\Delta(F)<m`; subcriticality is only needed later, when the average-defect inequality is used to
select a move preserving `\Delta<m`.

The abstract finite-poset lemma itself is now formalized in
`ErdosProblems/Problem1CubeExposedRepair.lean`; the remaining pre-injection tasks are the shifted
rank-poset instantiation and the explicit locality bridge from a corner move to the canonical
bad/good incidence sets used in the uniform-corner transport note.

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
- the exposed corners agree with the admissible repair pairs `K(F)` defined in
  [PROOF_template_relative_corner_parametrization.md](./PROOF_template_relative_corner_parametrization.md).

Proof sketch:

- for `F_full`, identify `C` with an order ideal in colex/lex rank order and `U` with an order
  ideal in the opposite upper rank order;
- for `F_star`, use the same construction inside the star/non-star splitting;
- prove the shifted condition is exactly the order-ideal condition in those coordinates.

### Step 2. Lower-Set Mismatch Lemma

Prove the abstract finite strict-poset statement. In the first Lean version, use the assumptions
`WellFounded lt` and `WellFounded (fun a b => lt b a)` to obtain minimal and maximal mismatch
atoms from `WellFounded.has_min`.

```math
F,T\text{ lower},\qquad |F|=|T|,\qquad F\ne T
\Longrightarrow
\exists(x,z)\text{ raw exposed from }F\text{ toward }T.
```

Proof sketch:

- `T\F` and `F\T` are nonempty because the lower sets have equal cardinality and differ;
- choose `x` minimal in `T\F`;
- choose `z` maximal in `F\T`;
- minimality of `x`, together with lower-set closure of `T`, gives `(REST)`;
- maximality of `z`, together with lower-set closure of both `F` and `T`, gives `(DEL)`;
- `(COMP)` is automatic: if `z<x`, then `x in T` and lower-set closure of `T` imply `z in T`,
  contradicting `z in F\T`.

This replaces the previous vague Ferrers-corner slide with a concrete order-theoretic theorem.
This step is formalized in `ErdosProblems/Problem1CubeExposedRepair.lean` as
`exists_rawExposedRepairPair_of_lower_eq_card_ne` and
`exists_rawExposedRepairPair_preserving_lower_of_lower_eq_card_ne`.

### Step 3. Shifted Instantiation

Instantiate Step 2 to the shifted rank posets for the two-layer model and the selected nearest
template `T(F)`.

Required checks:

- shifted rank-uniform families are lower sets in the shifted order;
- the template slices are lower sets in the same order;
- balancedness gives the equal-cardinality hypothesis for the total two-layer state;
- if `F` is not one of the two templates, then `F\ne T(F)`.

### Step 4. Distance-Reduction Lemma

Show that the chosen corner move satisfies

```math
d(F')=d(F)-2.
```

Proof sketch:

- one misplaced template cell is repaired;
- one paired compensating cell is removed from the wrong side;
- no new misplacements are created outside the local move rectangle.

This is the clean combinatorial heart of the radial part of the gradient.

This step is already covered abstractly by `ErdosProblems/Problem1CubeTemplateDistance.lean` and
`ErdosProblems/Problem1CubeExposedRepair.lean` once a raw pair is supplied.

### Step 5. Average Inward-Move Inequality

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
The newest sharpening is that this average drift is equivalent to a concrete atom-count inequality,
so the remaining local task is now a weighted multiplicity comparison, not an abstract defect
estimate.

### Step 6. Subcritical-Preservation For One Move

Deduce from Step 5 that under the subcritical hypothesis `\Delta(F)<m`, some admissible inward
move satisfies

```math
\Delta(F')<m.
```

Proof sketch:

- if every admissible inward move had defect at least `m`, then any uniform or weighted average of
  those defects would also be at least `m`;
- Step 5 rules this out when `\Delta(F)<m`.

### Step 7. Discrete Gradient / Collapse

Once Steps 2-6 are proved, orient every shifted subcritical non-template family toward one chosen
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
2. exposed repair-corner parametrization of admissible inward moves;
3. abstract finite lower-set mismatch gives a compatible raw exposed repair pair; formalized in
   `ErdosProblems/Problem1CubeExposedRepair.lean`;
4. shifted-template instantiation of that mismatch lemma, giving `K(F)\ne\varnothing` for shifted
   balanced non-template states;
5. exact distance drop `d(F')=d(F)-2`;
6. incidence-locality: the atoms counted by `B_new(k)`, `B_old(k)`, `C_new(k)`, and `C_old(k)` are
   controlled by the local cover-neighborhood of the two changed atoms;
7. a local average inward-move inequality, in its sharp current form the uniform-corner incidence
   transport theorem;
8. the deduction of one subcritical-preserving inward move from that average inequality.

Among these, Lemmas 6-7 are the real local unknown.
In its sharpest current form, Lemma 7 is the signed local multiplicity balance from
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md).
Equivalently, by
[PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md),
the real missing object is a canonical weight scheme on admissible inward moves. The current
preferred candidate is the uniform-corner scheme, whose remaining theorem is a local bad-to-good
incidence injection. Before that injection can be proved without hidden assumptions, finish the
shifted-template instantiation of the lower-set mismatch lemma and isolate the incidence-locality
bridge showing that the canonical bad/good incidence sets are genuinely local to a corner move.
These preliminary obligations should not mention `\Delta(F)<m`; radial exactness is already proved
for every supplied raw pair.

## Why This Is Better Than More Enumeration

This route turns the current problem into a finite list of proof obligations on local moves.

That is better than more brute-force because:

- the first-shell theorem is already known;
- the false unconditional inward-descent theorem showed that shell data alone is misleading;
- the remaining issue is genuinely structural: identify which local moves are forced to preserve
  subcriticality below the threshold `m`.

So the next useful commit on this branch should either:

- prove one of the eight lemmas above, or
- prove the shifted-template instantiation of the lower-set mismatch lemma, or
- prove the incidence-locality bridge for the canonical bad/good incidence sets, or
- construct the uniform-corner incidence injection needed for the local average inequality.
