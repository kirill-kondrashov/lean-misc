# Proof Note: Uniform Corner Weights Reduce The Canonical Scheme To Local Incidence Transport

This note pushes the current discrete-Morse route one level further.

The current local blocker, as stated in
[PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md](./PROOF_subcritical_discrete_gradient_conditional_on_canonical_weights.md),
is to construct a canonical weight scheme on admissible inward moves and prove the corresponding
average defect inequality. The purpose of this note is to isolate the cleanest natural candidate
for that weight scheme and to identify the exact local statement needed for it to work.

## Setup

Let

```math
F = C \cup U,
\qquad
C \subseteq \binom{[n]}{m},
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
|U| = \left|\binom{[n]}{m}\setminus C\right|.
```

Assume `F` is shifted and

```math
d(F)\ge 4.
```

Use the canonical exposed-corner set defined in
[PROOF_template_relative_corner_parametrization.md](./PROOF_template_relative_corner_parametrization.md).
That note defines a finite set of exposed admissible repair corners

```math
K(F),
```

such that:

1. every `k \in K(F)` determines one admissible inward move
   ```math
   F \rightsquigarrow F_k;
   ```
2. every admissible inward move arises from exactly one such corner; and
3. for every `k \in K(F)`,
   ```math
   d(F_k)=d(F)-2.
   ```

So `K(F)` is now the canonical parametrization of the admissible inward moves. The parametrization
note proves that every raw corner already has `d(F_k)=d(F)-2`. The abstract lower-set mismatch
lemma is now formalized, so the remaining precondition is its shifted-template instantiation:
prove `K(F)` is nonempty for every shifted balanced non-template state. This should not require
the subcritical hypothesis `\Delta(F)<m`.

For each `k \in K(F)`, write

```math
B_{\mathrm{new}}(k) := \partial^+F_k \setminus \partial^+F,
\qquad
B_{\mathrm{old}}(k) := \partial^+F \setminus \partial^+F_k,
```

and

```math
C_{\mathrm{new}}(k) := C_k \setminus C,
\qquad
C_{\mathrm{old}}(k) := C \setminus C_k.
```

As in
[PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md](./PROOF_average_inward_move_reduces_to_local_multiplicity_balance.md),
the defect drift of the `k`-move is

```math
\Delta(F_k)-\Delta(F)
=
\bigl(|B_{\mathrm{new}}(k)|+|C_{\mathrm{old}}(k)|\bigr)
-
\bigl(|B_{\mathrm{old}}(k)|+|C_{\mathrm{new}}(k)|\bigr).
\tag{DRIFT}_k
```

## Canonical Uniform Corner Weights

Assume from here through the averaging argument that `K(F)` is nonempty.

The first canonical weight candidate is the uniform distribution on `K(F)`:

```math
\mu_F(k) := \frac{1}{|K(F)|}
\qquad
(k \in K(F)).
\tag{UNI}
```

This is genuinely canonical once the corner parametrization is fixed: it does not depend on
choosing a good move after the fact.

Under `(UNI)`, the desired average inequality becomes

```math
\frac{1}{|K(F)|}\sum_{k \in K(F)} \Delta(F_k)
\le
\Delta(F).
\tag{AVG}_{\mathrm{corner}}
```

## Incidence Sets

Define the bad-incidence set

```math
\mathcal B(F)
:=
\bigsqcup_{k \in K(F)}
\Bigl(
\{k\}\times B_{\mathrm{new}}(k)
\;\sqcup\;
\{k\}\times C_{\mathrm{old}}(k)
\Bigr),
```

and the good-incidence set

```math
\mathcal G(F)
:=
\bigsqcup_{k \in K(F)}
\Bigl(
\{k\}\times B_{\mathrm{old}}(k)
\;\sqcup\;
\{k\}\times C_{\mathrm{new}}(k)
\Bigr).
```

Thus:

- `\mathcal B(F)` records all move-atom incidences contributing positively to the defect drift;
- `\mathcal G(F)` records all move-atom incidences contributing negatively to the defect drift.

Their cardinalities are

```math
|\mathcal B(F)|
=
\sum_{k \in K(F)}
\bigl(
|B_{\mathrm{new}}(k)| + |C_{\mathrm{old}}(k)|
\bigr),
```

and

```math
|\mathcal G(F)|
=
\sum_{k \in K(F)}
\bigl(
|B_{\mathrm{old}}(k)| + |C_{\mathrm{new}}(k)|
\bigr).
```

## Exact Uniform-Weight Reformulation

### Lemma

Assume `K(F)` is nonempty. Then `(AVG)_{\mathrm{corner}}` is equivalent to

```math
|\mathcal B(F)| \le |\mathcal G(F)|.
\tag{INC}
```

### Proof

By averaging `(DRIFT)_k` over `k \in K(F)`, we obtain

```math
\frac{1}{|K(F)|}\sum_{k \in K(F)} \bigl(\Delta(F_k)-\Delta(F)\bigr)
=
\frac{1}{|K(F)|}
\Bigl(
|\mathcal B(F)|-|\mathcal G(F)|
\Bigr).
```

So

```math
\frac{1}{|K(F)|}\sum_{k \in K(F)} \Delta(F_k) \le \Delta(F)
```

holds if and only if

```math
|\mathcal B(F)|-|\mathcal G(F)| \le 0,
```

which is exactly `(INC)`.

## Injection Criterion

The incidence inequality `(INC)` will follow from any injection

```math
\Phi_F : \mathcal B(F) \hookrightarrow \mathcal G(F).
\tag{INJ}
```

### Corollary

If `K(F)` is nonempty, `(INJ)` implies `(AVG)_{\mathrm{corner}}`.

### Proof

An injection `\Phi_F : \mathcal B(F) \hookrightarrow \mathcal G(F)` gives

```math
|\mathcal B(F)| \le |\mathcal G(F)|.
```

By the lemma above, this is exactly `(AVG)_{\mathrm{corner}}`.

## Why This Is A Real Sharpening

This is stronger than the previous “some canonical weights” formulation in one very specific
sense:

- the weight candidate is no longer unspecified;
- the remaining theorem is no longer an average inequality in the abstract;
- it is now a concrete incidence-transport problem for the uniform corner measure.

At the level of proof notes, the local blocker can now be read as:

```math
\text{construct a canonical injection }
\Phi_F : \mathcal B(F) \hookrightarrow \mathcal G(F).
```

## Why The Naive “Next Step” Is Too Coarse

The sentence “construct a canonical injection `\Phi_F`” is correct as an eventual target but too
coarse as an immediate implementation step.

The reason is that locality alone does not determine a transport. The current Lean layer records
only:

- a raw repair pair `k=(x,z)`;
- the canonical bad/good incidence finsets attached to that pair; and
- the fact that every such incidence lies in the local neighborhood generated by `x` and `z`.

That is not yet enough to define a canonical reassignment map. In particular, the present Lean
avatar of `K(F)` does **not** yet encode the move-rectangle / Ferrers-corner data alluded to in the
informal discussion below, nor does it yet prove that every selected-template raw repair pair comes
from a unique local corner geometry. Without that stronger structure, “use locality to define the
injection” is underspecified.

So there is a missing intermediate theorem layer:

```math
\text{refine each } k\in K(F) \text{ to a canonical structured local corner datum.}
```

Only after that refinement can one hope to classify the incidences in `\mathcal B(F)` and
`\mathcal G(F)` into a finite list of local cases and then define `\Phi_F` canonically.

## Locality Of The Remaining Problem

The reason this is still compatible with the discrete-Morse strategy is that each corner move is
local: it changes `F` only inside one move rectangle of the Ferrers data. Therefore each incidence
in `\mathcal B(F)` or `\mathcal G(F)` is attached to one corner and one local atom.

So if one can prove that every bad incidence can be reassigned to a good incidence using only the
bounded local corner-neighborhood around that move rectangle, then `(INJ)` becomes a finite local
configuration problem rather than a global shell computation.

That is the eventual theorem candidate on the stronger branch, but it is not yet the immediate Lean
task.

The immediate next theorem candidate should instead be:

```math
\text{recover the structured local corner geometry underlying the selected-template raw repair set.}
```

Concretely, this means proving that the current Lean `K(F)` object carries enough canonical local
data to determine the relevant move rectangle and to partition bad/good incidences into finitely
many corner-local roles.

Only after that layer is in place should the project attempt the actual transport statement:

```math
\text{prove a local bad-to-good incidence injection for uniform corner weights.}
```

## Present Blocker

This note does not prove `(INJ)`. It proves only that, for the corner set `K(F)` defined in
[PROOF_template_relative_corner_parametrization.md](./PROOF_template_relative_corner_parametrization.md),
the natural canonical weight scheme `(UNI)` works if and only if one can solve the corresponding
incidence-transport problem.

So the current blocker is now sharper than before:

- first instantiate the lower-set mismatch lemma to get `K(F)\ne\varnothing` for shifted balanced
  non-template states;
- then isolate the locality package showing that the incidences in `\mathcal B(F)` and
  `\mathcal G(F)` are controlled by the corner-neighborhood of the two changed atoms;
- then prove that the selected-template repair-pair parametrization remembers enough **structured
  corner geometry** to make a canonical local transport well-defined;
- then prove
  ```math
  \text{prove the uniform-corner incidence injection } \Phi_F.
  ```
