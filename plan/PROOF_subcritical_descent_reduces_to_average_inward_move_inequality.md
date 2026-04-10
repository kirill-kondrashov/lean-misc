# Proof Note: Subcritical Counterexample Descent Reduces To An Average Inward-Move Inequality

This note isolates a cleaner local theorem candidate inside the active discrete-Morse route.

The live stronger-branch goal is the subcritical counterexample-descent statement from
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
\tag{CED}_{<m}
```

The purpose of this note is to show that `(CED)_{<m}` follows from a purely local averaging
statement on admissible inward moves.

## Admissible Inward Moves

Fix a shifted balanced two-layer family `F` with

```math
F \notin \{F_{\mathrm{full}},F_\star\},
\qquad
d(F)\ge 4.
```

Let `M_{\mathrm{in}}(F)` denote the finite set of admissible inward moves from `F`, meaning the
shifted balanced two-layer families `F'` such that

```math
d(F') = d(F)-2.
```

This suppresses the combinatorial construction of the move itself; the point is only that every
element of `M_{\mathrm{in}}(F)` is one legal one-step repair of two units of template distance.

The discrete-Morse plan in
[PLAN_subcritical_inward_descent_discrete_morse_route.md](./PLAN_subcritical_inward_descent_discrete_morse_route.md)
is exactly aimed at proving that `M_{\mathrm{in}}(F)` is nonempty and sufficiently well behaved.

## Uniform Average Version

The simplest local theorem candidate is:

```math
\frac{1}{|M_{\mathrm{in}}(F)|}
\sum_{F' \in M_{\mathrm{in}}(F)} \Delta(F')
\le
\Delta(F).
\tag{AVG}_{\mathrm{unif}}
```

In words: the average defect over all admissible inward moves does not exceed the current defect.

## Weighted Version

More flexibly, it is enough to construct a probability distribution

```math
\mu_F : M_{\mathrm{in}}(F) \to [0,1],
\qquad
\sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F') = 1,
```

such that

```math
\sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F')\,\Delta(F')
\le
\Delta(F).
\tag{AVG}_\mu
```

This weighted form is the more realistic proof target: the natural corner moves need not contribute
symmetrically, so a canonical biased distribution may be easier to control than the uniform one.

## Reduction To Counterexample Descent

Assume the following two facts:

1. for every shifted non-template `F` with `d(F)\ge 4`, the move set `M_{\mathrm{in}}(F)` is
   nonempty;
2. for every such `F`, either `(AVG)_{\mathrm{unif}}` or the weighted version `(AVG)_\mu` holds.

Then `(CED)_{<m}` follows.

### Proof

Let `F` be shifted, non-template, with

```math
d(F)\ge 4,
\qquad
\Delta(F)<m.
```

Assume first `(AVG)_{\mathrm{unif}}`. If every `F' \in M_{\mathrm{in}}(F)` satisfied

```math
\Delta(F') \ge m,
```

then their average would also satisfy

```math
\frac{1}{|M_{\mathrm{in}}(F)|}
\sum_{F' \in M_{\mathrm{in}}(F)} \Delta(F')
\ge
m,
```

contradicting `(AVG)_{\mathrm{unif}}` together with `\Delta(F)<m`.

So at least one admissible inward move satisfies

```math
\Delta(F')<m.
```

Because `F' \in M_{\mathrm{in}}(F)`, it also satisfies

```math
d(F')=d(F)-2.
```

This is exactly `(CED)_{<m}`.

The same argument works for `(AVG)_\mu`: if every admissible `F'` had `\Delta(F')\ge m`, then any
convex combination of those defects would also be at least `m`, contradicting `(AVG)_\mu` and the
hypothesis `\Delta(F)<m`.

## Why This Helps

This reduction isolates the real local analytic task:

- not to choose a single perfect inward move by hand,
- but to prove that the admissible inward moves have non-positive average defect drift.

That is a better fit for the discrete-Morse viewpoint, because the average can often be controlled
by pairing/canceling local boundary changes across all corners at once.

So the active stronger route now naturally splits into:

1. prove admissible inward moves exist for every shifted non-template family with `d(F)\ge 4`;
2. prove an average inward-move inequality `(AVG)`;
3. conclude subcritical counterexample descent `(CED)_{<m}`;
4. combine with the first-shell theorem to get shifted equality classification and the global
   shifted `+m` gap.

## Proof Sketch For `(AVG)`

The intended local proof shape is:

1. write `\Delta(F')-\Delta(F)` as a sum of local boundary changes inside the move rectangle;
2. sum that expression over all admissible inward moves, or over a canonical weighted family of
   such moves;
3. show the positive local contributions telescope against the negative ones, leaving total drift
   `\le 0`.

So the theorem-first program is now sharply focused on a local averaging inequality, rather than on
finding a single globally monotone move by inspection.

This local averaging step is now sharpened further in
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md):
the average inequality is equivalent to a signed multiplicity balance between

- created boundary atoms and lost lower atoms, versus
- destroyed boundary atoms and gained lower atoms.

One important logical caveat is now recorded separately in
[PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md):
if the weights `\mu_F` are allowed to be chosen arbitrarily after seeing the best move, then the
weighted average inequality is equivalent to the original existence of a non-increasing move.
So the genuinely useful theorem is not mere existence of some weights, but existence of a
canonical locally defined weight scheme.
