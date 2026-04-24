# Proof Note: Template-Relative Corner Parametrization

This note removes the hidden assumption in the uniform-corner route: what exactly is the
canonical set of inward corners?

It does not prove the local incidence injection. Its job is narrower and prior: give a precise
definition of admissible exposed repair corners and isolate the remaining nontrivial existence
and locality obligations.

## Ambient Poset

Let

```math
n = 2m+1,
\qquad
F=C\cup U,
\qquad
C\subseteq \binom{[n]}m,
\qquad
U\subseteq \binom{[n]}{m+1},
```

with

```math
|C|+|U|=\binom nm.
```

This is equivalent to the balanced condition

```math
|U|=\left|\binom{[n]}m\setminus C\right|.
```

On each uniform rank use the standard shifted order:
for

```math
A=\{a_1<\cdots<a_r\},
\qquad
B=\{b_1<\cdots<b_r\},
```

write

```math
A\le_{\mathrm{sh}} B
\quad\Longleftrightarrow\quad
a_i\le b_i\text{ for all }i.
```

A rank-uniform family is shifted exactly when it is a down-set in this order.

## Templates And Distances

The two template families are

```math
F_{\mathrm{full}}=
\binom{[n]}m
```

and

```math
F_\star
=
\{A\in\binom{[n]}m:0\in A\}
\cup
\{B\in\binom{[n]}{m+1}:0\in B\}.
```

For a fixed template

```math
T=T_C\cup T_U,
```

define the template-relative distance

```math
d_T(F)
:=
|C\triangle T_C|+|U\triangle T_U|.
```

The radial distance used by the global plan is

```math
d(F):=\min(d_{F_{\mathrm{full}}}(F),d_{F_\star}(F)).
```

When a deterministic nearest template is needed, use the tie-break

```math
T(F)=
\begin{cases}
F_{\mathrm{full}},
&d_{F_{\mathrm{full}}}(F)\le d_{F_\star}(F),\\
F_\star,
&d_{F_\star}(F)<d_{F_{\mathrm{full}}}(F).
\end{cases}
```

The tie-break is only a convention. The proof obligations below are invariant under replacing it
by any fixed deterministic rule.

## Misplaced Atoms

For the chosen template `T=T(F)`, write

```math
M^-(F;T):=T\setminus F,
\qquad
M^+(F;T):=F\setminus T.
```

Layerwise, these are

```math
R_C:=T_C\setminus C,
\qquad
R_U:=T_U\setminus U,
\qquad
A_C:=C\setminus T_C,
\qquad
A_U:=U\setminus T_U.
```

Because both `F` and `T` have size `binom(n,m)`,

```math
|M^-(F;T)|=|M^+(F;T)|,
\qquad
d_T(F)=2|M^-(F;T)|.
```

So a one-atom repair must restore one atom from `M^-` and delete one atom from `M^+`.

## Exposed Repair Atoms

For a rank `r` layer, an atom

```math
x\in T_r\setminus F_r
```

is `restorable` if adding it preserves shiftedness in that rank:

```math
y<_{\mathrm{sh}}x
\Longrightarrow
y\in F_r
\quad
\text{for every rank-}r\text{ atom }y.
\tag{REST}
```

Equivalently, `x` is a minimal missing template atom in the shifted-order complement of `F_r`.

An atom

```math
z\in F_r\setminus T_r
```

is `deletable` if deleting it preserves shiftedness in that rank:

```math
z<_{\mathrm{sh}}y
\Longrightarrow
y\notin F_r
\quad
\text{for every rank-}r\text{ atom }y.
\tag{DEL}
```

Equivalently, `z` is a maximal present non-template atom of `F_r`.

These two definitions are local Ferrers-corner conditions. They use only cover relations in the
shifted rank poset after transitive closure is eliminated.

## Raw Exposed Repair Pairs

A raw exposed repair pair is a pair

```math
k=(x,z)
```

such that:

```math
x\in M^-(F;T(F)),
\qquad
z\in M^+(F;T(F)),
```

`x` is restorable in its rank, and `z` is deletable in its rank.

If `x` and `z` lie in the same rank, require the additional compatibility condition

```math
\neg(z<_{\mathrm{sh}}x).
\tag{COMP}
```

Equivalently, deleting `z` does not remove a predecessor needed to add `x`.

The associated repaired family is

```math
F_k:=(F\cup\{x\})\setminus\{z\}.
```

This operation preserves the balanced two-layer class, because it changes neither the total
cardinality `|C|+|U|` nor the allowed rank support.

It also preserves shiftedness by `(REST)` in the rank containing `x` and `(DEL)` in the rank
containing `z`. If `x` and `z` lie in different ranks, the two rank checks are independent. If
they lie in the same rank, `(COMP)` is exactly the extra condition needed to ensure the deleted
atom is not a predecessor of the restored atom, so the final rank family is still a down-set.

## Exact Template-Relative Distance Drop

For every raw exposed repair pair `k=(x,z)`,

```math
d_{T(F)}(F_k)=d_{T(F)}(F)-2.
\tag{TDROP}
```

Proof:
`x` belongs to `T(F)\setminus F`, so adding `x` removes exactly one atom from
`F\triangle T(F)`. Similarly, `z` belongs to `F\setminus T(F)`, so deleting `z` removes exactly
one atom from `F\triangle T(F)`. No other atom changes membership. Hence the symmetric difference
with the fixed template drops by exactly `2`.

This proves the radial algebra for the fixed template. The only extra issue is that the global
distance is the minimum of the two template distances.

## Canonical Admissible Corner Set

Define

```math
K(F)
:=
\{k:\ k\text{ is a raw exposed repair pair and }d(F_k)=d(F)-2\}.
\tag{K}
```

Thus `K(F)` is the canonical set of exposed inward moves used by the uniform-corner plan.

This definition deliberately bakes in the global radial exactness required by the current
discrete-Morse reduction. If one proves a separate radial exactness theorem saying every raw
exposed repair pair has `d(F_k)=d(F)-2` in the subcritical region, then the final condition in
`(K)` can be removed.

## Parametrization Lemma

With `K(F)` defined by `(K)`, every `k in K(F)` determines one admissible inward move

```math
F\rightsquigarrow F_k
```

satisfying:

```math
F_k\text{ is shifted and balanced},
\qquad
d(F_k)=d(F)-2.
```

Conversely, every admissible exposed one-repair move relative to the chosen nearest template
arises from a unique element of `K(F)`.

Proof:
The forward direction is the definition of `K(F)` plus `(REST)`, `(DEL)`, and `(TDROP)`.
For uniqueness, the changed atoms are recovered from the move itself:

```math
x\in F_k\setminus F,
\qquad
z\in F\setminus F_k.
```

So two repair pairs producing the same `F_k` must have the same restored atom and the same deleted
atom.

## What Remains Nontrivial

This note proves that there is no ambiguity in the corner parametrization once exposed repair
pairs are adopted. It does not prove that useful corners always exist.

The remaining theorem needed before the incidence injection is:

```math
F\text{ shifted},
\quad
F\notin\{F_{\mathrm{full}},F_\star\},
\quad
d(F)\ge 4,
\quad
\Delta(F)<m
\Longrightarrow
K(F)\ne\varnothing.
\tag{EXIST}
```

There are two viable ways to prove `(EXIST)`:

1. Prove raw-corner nonemptiness from the Ferrers skew shape and then prove radial exactness for
   the raw corners in the subcritical region.
2. Prove nonemptiness directly for the filtered set `(K)` by showing at least one exposed repair
   pair does not cross the bisector between the two templates.

After `(EXIST)`, the active local target remains exactly the one in the uniform-corner note:

```math
\Phi_F:\mathcal B(F)\hookrightarrow\mathcal G(F).
```

The incidence injection should now be read with `K(F)` as defined in `(K)`.

## Local Proof Obligations

The next rigorous sublemmas are:

1. `SHIFTED-CORNERS`: In any nonempty mismatch region between two shifted rank families, minimal
   missing template atoms and maximal extra atoms are exposed in the sense of `(REST)` and `(DEL)`,
   and compatible pairs satisfying `(COMP)` exist when the repair is same-rank.
2. `BALANCED-PAIR`: For the balanced two-layer state space, restoring one missing template atom
   and deleting one extra non-template atom preserves balance.
3. `RADIAL-EXACT`: In the subcritical region, at least one raw exposed repair pair satisfies the
   global condition `d(F_k)=d(F)-2`.
4. `INCIDENCE-LOCALITY`: For `k in K(F)`, all atoms in
   `B_new(k)`, `B_old(k)`, `C_new(k)`, and `C_old(k)` are supported in the cover-neighborhood of
   the two changed atoms.
5. `INJ`: Construct the local bad-to-good incidence injection for this `K(F)`.

Only after these five items are proved does the discrete-Morse route close the proposed `+m`
additive improvement.
