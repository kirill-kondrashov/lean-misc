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

This proves the radial algebra for the fixed template.

## Exact Global Distance Drop

For every raw exposed repair pair `k=(x,z)`,

```math
d(F_k)=d(F)-2.
\tag{GDROP}
```

Proof:
Let `T=T(F)` be the chosen nearest template. By definition of `T(F)`,

```math
d_T(F)=d(F).
```

By `(TDROP)`,

```math
d_T(F_k)=d_T(F)-2=d(F)-2.
```

Therefore

```math
d(F_k)\le d(F)-2.
```

For the opposite template `S`, the move from `F` to `F_k` changes exactly two atoms. Symmetric
difference distance to any fixed template is therefore `2`-Lipschitz:

```math
d_S(F_k)\ge d_S(F)-2.
```

Since `T` was nearest, `d_S(F)\ge d(F)`, and hence

```math
d_S(F_k)\ge d(F)-2.
```

Both template distances from `F_k` are now at least `d(F)-2`, and the distance to `T` is exactly
`d(F)-2`. Thus the minimum of the two template distances is exactly `d(F)-2`.

So the anticipated bisector obstruction does not exist: radial exactness is automatic for every
raw exposed repair pair relative to the chosen nearest template.

## Canonical Admissible Corner Set

Define

```math
K(F)
:=
\{k:\ k\text{ is a raw exposed repair pair}\}.
\tag{K}
```

Thus `K(F)` is the canonical set of exposed inward moves used by the uniform-corner plan.
The global radial condition is not part of the definition because it is already proved by
`(GDROP)`.

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
The forward direction is the definition of `K(F)` plus `(REST)`, `(DEL)`, `(TDROP)`, and
`(GDROP)`.
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
\text{there is at least one raw exposed repair pair, equivalently }K(F)\ne\varnothing.
\tag{EXIST}
```

So `(EXIST)` is now a pure exposed-corner nonemptiness theorem. It no longer has a separate radial
or bisector component.

After `(EXIST)`, the active local target remains exactly the one in the uniform-corner note:

```math
\Phi_F:\mathcal B(F)\hookrightarrow\mathcal G(F).
```

The incidence injection should now be read with `K(F)` as defined in `(K)`.

## Computational Sanity Check

The script

```bash
python3 tools/problem1_odd_profile_search.py --shifted-two-layer-exposed-corner-summary ...
```

now checks this exact exposed-corner definition on local shifted template shells. For each checked
state with `d(F)>=4`, it counts:

- raw exposed repair pairs satisfying `(REST)`, `(DEL)`, and `(COMP)`;
- `K`-corners satisfying the global condition `d(F_k)=d(F)-2`.

The runs

```bash
python3 tools/problem1_odd_profile_search.py \
  --shifted-two-layer-exposed-corner-summary 7 9 \
  --template-shell-max-distance 8

python3 tools/problem1_odd_profile_search.py \
  --shifted-two-layer-exposed-corner-summary 11 13 \
  --template-shell-max-distance 10
```

found that every checked local shifted state with `d(F)>=4` has at least one raw exposed repair
pair and at least one `K`-corner. In these local windows there were no subcritical states
`Delta(F)<m`, so the check is not evidence for the subcritical nonemptiness theorem itself. Its
value is narrower: it validates the corner definition and agrees with `(GDROP)`, including across
the template tie-break.

## Local Proof Obligations

The next rigorous sublemmas are:

1. `SHIFTED-CORNERS`: In any nonempty mismatch region between two shifted rank families, minimal
   missing template atoms and maximal extra atoms are exposed in the sense of `(REST)` and `(DEL)`,
   and compatible pairs satisfying `(COMP)` exist when the repair is same-rank.
2. `BALANCED-PAIR`: For the balanced two-layer state space, restoring one missing template atom
   and deleting one extra non-template atom preserves balance.
3. `RAW-NONEMPTY`: Under the shifted subcritical hypotheses, at least one compatible restorable /
   deletable raw repair pair exists.
4. `INCIDENCE-LOCALITY`: For `k in K(F)`, all atoms in
   `B_new(k)`, `B_old(k)`, `C_new(k)`, and `C_old(k)` are supported in the cover-neighborhood of
   the two changed atoms.
5. `INJ`: Construct the local bad-to-good incidence injection for this `K(F)`.

Only after these five items are proved does the discrete-Morse route close the proposed `+m`
additive improvement.
