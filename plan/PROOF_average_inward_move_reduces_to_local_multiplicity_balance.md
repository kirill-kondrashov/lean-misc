# Proof Note: Average Inward-Move Inequality Reduces To Local Multiplicity Balance

This note sharpens the current local blocker on the improved-bound branch.

The preceding note
[PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md](./PROOF_subcritical_descent_reduces_to_average_inward_move_inequality.md)
showed that the live subcritical counterexample-descent theorem follows from an average defect
inequality over admissible inward moves. The purpose of this note is to rewrite that average
inequality in a concrete signed form using the actual defect atoms of the two-layer problem.

## Setup

Let

```math
F = C \cup U,
\qquad
C \subseteq \binom{[n]}{m},
\qquad
U \subseteq \binom{[n]}{m+1},
```

be a shifted balanced two-layer family, and write

```math
\Delta(F) := |\partial^+F| - |C|.
```

Fix an admissible inward move `F -> F'`, where `F' = C' \cup U'` is shifted and

```math
d(F') = d(F)-2.
```

For this move, define:

```math
B_{\mathrm{new}} := \partial^+F' \setminus \partial^+F,
\qquad
B_{\mathrm{old}} := \partial^+F \setminus \partial^+F',
```

and

```math
C_{\mathrm{new}} := C' \setminus C,
\qquad
C_{\mathrm{old}} := C \setminus C'.
```

So:

- `B_new` are the positive-boundary cells created by the move;
- `B_old` are the positive-boundary cells destroyed by the move;
- `C_new` are the lower cells gained by the move;
- `C_old` are the lower cells lost by the move.

## Exact Drift Formula

The defect drift of the move is

```math
\Delta(F')-\Delta(F)
=
\bigl(|B_{\mathrm{new}}|-|B_{\mathrm{old}}|\bigr)
-\bigl(|C_{\mathrm{new}}|-|C_{\mathrm{old}}|\bigr).
```

Equivalently,

```math
\Delta(F')-\Delta(F)
=
\bigl(|B_{\mathrm{new}}|+|C_{\mathrm{old}}|\bigr)
-\bigl(|B_{\mathrm{old}}|+|C_{\mathrm{new}}|\bigr).
\tag{DRIFT}
```

This is just the tautological signed expansion of

```math
|\partial^+F'|-|\partial^+F|
\qquad\text{and}\qquad
|C'|-|C|.
```

## Interpretation

Formula `(DRIFT)` splits the move into:

- bad events:
  ```math
  B_{\mathrm{new}} \cup C_{\mathrm{old}},
  ```
  meaning new boundary exposed or old lower mass lost;
- good events:
  ```math
  B_{\mathrm{old}} \cup C_{\mathrm{new}},
  ```
  meaning old boundary removed or new lower mass gained.

So an inward move is defect-nonincreasing exactly when its good events dominate its bad events.

## Weighted Average Form

Now fix a probability distribution

```math
\mu_F : M_{\mathrm{in}}(F) \to [0,1]
```

on the admissible inward moves.

The average inward-move inequality

```math
\sum_{F' \in M_{\mathrm{in}}(F)} \mu_F(F')\,\Delta(F')
\le
\Delta(F)
\tag{AVG}_\mu
```

is equivalent, by averaging `(DRIFT)`, to

```math
\sum_{F'} \mu_F(F')
\bigl(|B_{\mathrm{new}}(F')|+|C_{\mathrm{old}}(F')|\bigr)
\le
\sum_{F'} \mu_F(F')
\bigl(|B_{\mathrm{old}}(F')|+|C_{\mathrm{new}}(F')|\bigr).
\tag{BAL}
```

So the active local theorem target is now a signed multiplicity balance.

## Atomwise Multiplicity Version

Define weighted creation/destruction multiplicities

```math
\alpha_F(x)
:=
\sum_{F'} \mu_F(F')\,1_{x \in B_{\mathrm{new}}(F')},
\qquad
\beta_F(x)
:=
\sum_{F'} \mu_F(F')\,1_{x \in B_{\mathrm{old}}(F')},
```

for upper-layer / boundary atoms `x`, and

```math
\gamma_F(a)
:=
\sum_{F'} \mu_F(F')\,1_{a \in C_{\mathrm{new}}(F')},
\qquad
\delta_F(a)
:=
\sum_{F'} \mu_F(F')\,1_{a \in C_{\mathrm{old}}(F')},
```

for lower-layer atoms `a`.

Then `(BAL)` is exactly

```math
\sum_x \alpha_F(x) + \sum_a \delta_F(a)
\le
\sum_x \beta_F(x) + \sum_a \gamma_F(a).
\tag{ATOM}
```

So it is enough to prove that, in weighted total, created boundary plus lost lower mass is no
larger than destroyed boundary plus gained lower mass.

## Why This Is Better

This is a real sharpening because `(ATOM)` is no longer an abstract inequality on full defects.
It is a concrete combinatorial counting problem on the four local atom types affected by a move.

That suggests the next proof task:

1. describe the admissible inward moves in terms of local move rectangles;
2. compute which boundary atoms and lower atoms each rectangle creates or destroys;
3. choose weights `\mu_F` so that the bad multiplicities are dominated by the good ones.

In particular, the remaining local unknown is now:

```math
\text{construct }\mu_F\text{ so that }(ATOM)\text{ holds for every shifted }F.
```

## Proof Sketch For The Next Step

The natural candidate is to group admissible inward moves by outer corners of the Ferrers data
`\Sigma(F)`. Then:

- each corner move affects only one small rectangle in the lower/upper diagrams;
- every affected boundary atom or lower atom belongs to only a small number of such rectangles;
- one tries to weight corners so that every bad atom is paid for by at least one good atom in the
  same local neighborhood.

So the current active local barrier can now be stated concretely:

```math
\text{prove the signed local multiplicity balance }(ATOM).
```
