# Scenario: Hyperbolic Residual Finiteness Counterexample Worker 02

This is the arithmetic finite-kernel audit requested after
[SCENARIO_hyperbolic_residual_finiteness_worker_01.md](./SCENARIO_hyperbolic_residual_finiteness_worker_01.md).

The conclusion is negative: the arithmetic route gives a clean conditional theorem-to-counterexample
mechanism, but no unconditional word-hyperbolic non-residually finite group.

## Candidate family audited

Use cocompact arithmetic lattices of the first kind in `SU(d,1)`, `d >= 2`.

Let `k` be a CM field of degree `[k:Q]=2e`, and let `J` be a Hermitian matrix over `k`
with signature `(d,1)` at one complex place and definite signature at the other complex
places. The corresponding `Q`-group satisfies

```math
\mathbb G(\mathbb R) \cong SU(d,1)\times SU(d+1)^{e-1}.
```

For `[k:Q] > 2`, the associated arithmetic subgroups in the `SU(d,1)` factor are cocompact.
For `[k:Q]=2`, they have cusps. This distinction is explicit in Hill's cusp paper, which
recalls that the `[k:Q]>2` case is cocompact and the `[k:Q]=2` case has cusps.

Primary source:

- Richard M. Hill, "Residual finiteness of extensions of arithmetic subgroups of
  `SU(d,1)` with cusps", Rend. Circ. Mat. Palermo 72 (2023), 2771--2788,
  <https://link.springer.com/article/10.1007/s12215-022-00793-0>.

## Audit questions

### 1. Is the base lattice word-hyperbolic?

For the cocompact `[k:Q]>2` family, yes.

Reason: a torsion-free finite-index subgroup `Gamma < SU(d,1)` acts properly discontinuously
and cocompactly by isometries on complex hyperbolic space `CH^d`, a proper geodesic negatively
curved symmetric space. By the Švarc--Milnor lemma, `Gamma` is quasi-isometric to `CH^d`;
since `CH^d` is Gromov-hyperbolic, `Gamma` is word-hyperbolic.

For the `[k:Q]=2` cusp family, no in dimensions `d >= 2` for the present purpose. The cusp
subgroups are lattices in Heisenberg groups; in particular they are not virtually cyclic.
Thus these lattices are relatively hyperbolic but not word-hyperbolic. Hill describes the cusp
cross-sections explicitly as circle bundles over abelian varieties, with Heisenberg unipotent
radical.

### 2. What exact central extension is constructed, and is its kernel finite?

There are two different constructions that must not be conflated.

#### Connected-cover extensions of `SU(d,1)`

The universal cover of `SU(d,1)` gives

```math
1 \to \mathbb Z \to \widetilde{SU(d,1)} \to SU(d,1) \to 1.
```

For each `n >= 1`, the unique connected `n`-fold cover is

```math
\widetilde{SU(d,1)}/n\mathbb Z \to SU(d,1),
```

and the preimage of an arithmetic subgroup `Gamma` gives

```math
1 \to \mathbb Z/n \to \widetilde{\Gamma}^{(n)} \to \Gamma \to 1.
```

This is a finite central extension. The universal-cover preimage has infinite central kernel
`\mathbb Z`; that one is not a finite-kernel extension.

Primary source:

- Hill, "Residual finiteness of extensions of arithmetic subgroups of `SU(d,1)` with cusps",
  Introduction, <https://link.springer.com/article/10.1007/s12215-022-00793-0>.

#### Flach/Hill finite extensions from finite congruence kernel

Richard Hill's "Non-residually finite extensions of arithmetic groups" proves a different
finite-kernel construction. If `G/Q` is simple, algebraically simply connected, has positive
real rank, and has finite congruence kernel, then every arithmetic subgroup `Gamma` admits a
finite abelian extension

```math
1 \to A \to \widetilde{\Gamma} \to \Gamma \to 1
```

that is not residually finite. More sharply, for every `n` there is a finite-index subgroup
`Delta < Gamma` and a central extension

```math
1 \to \mathbb Z/n \to \widetilde{\Delta} \to \Delta \to 1
```

such that every finite-index subgroup of `\widetilde{\Delta}` contains the subgroup `\mathbb Z/n`.

Primary source:

- Richard M. Hill, "Non-residually finite extensions of arithmetic groups", Res. Number Theory
  5 (2019), article 2, <https://link.springer.com/article/10.1007/s40993-018-0140-z>.

### 3. Why does the Flach/Hill extension fail residual finiteness?

For the finite central extension

```math
1 \to \mathbb Z/n \to \widetilde{\Delta} \to \Delta \to 1,
```

Hill proves the stronger statement:

```math
\text{every finite-index subgroup of } \widetilde{\Delta}
\text{ contains } \mathbb Z/n.
```

Therefore every nontrivial element of the central kernel `\mathbb Z/n` lies in the finite
residual

```math
R_f(\widetilde{\Delta})
=
\bigcap_{[\widetilde{\Delta}:N]<\infty,\ N\triangleleft \widetilde{\Delta}} N.
```

This is the exact finite-residual witness. It is not merely a failure to find finite quotients.

For Deligne's original higher-rank construction, the extension

```math
1 \to \mathbb Z \to \widetilde{\Gamma} \to Sp_{2n}(\mathbb Z) \to 1
```

has infinite kernel, and every finite-index subgroup contains `2Z`. Thus any nonzero element
of `2Z` is killed by all finite quotients. This is not a finite-kernel extension until one
pushes out modulo some `m`; in any case the base is higher-rank arithmetic, not word-hyperbolic.

### 4. Does the non-RF construction require a finite congruence kernel?

Yes. The finite-kernel non-RF theorem used here requires finite congruence kernel.

Hill defines the arithmetic completion and congruence kernel through the exact sequence

```math
1 \to \mathrm{Cong}(G) \to \widehat{G(\mathbb Q)} \to G(\mathbb A_f) \to 1.
```

The hypotheses of the non-RF finite-extension theorem include:

1. `G` algebraically simply connected;
2. positive real rank;
3. finite congruence kernel.

For real rank one, Hill states Serre's conjecture in the opposite direction:

```math
G/\mathbb Q \text{ simple simply connected of real rank }1
\Longrightarrow
\mathrm{Cong}(G) \text{ is infinite}.
```

Hill further proves that if every Gromov-hyperbolic group is residually finite, then this
rank-one congruence-kernel conjecture follows. Equivalently for this audit: finding a compact
rank-one arithmetic group with finite congruence kernel would activate Hill's theorem and
produce a hyperbolic non-RF finite extension, but that missing input is itself a major open
congruence-subgroup problem.

### 5. Does the extension remain word-hyperbolic?

For a finite-kernel extension of a cocompact rank-one lattice, yes.

If

```math
1 \to A \to \widetilde{\Gamma} \to \Gamma \to 1
```

has finite `A` and `Gamma` is finitely generated, then the quotient map
`\widetilde{\Gamma} -> \Gamma` is a quasi-isometry for word metrics. Word-hyperbolicity is
quasi-isometry invariant among finitely generated groups. Thus a finite extension of a
word-hyperbolic group is word-hyperbolic.

This step is valid only for finite kernel. The universal-cover preimage of `Gamma < SU(d,1)`
has infinite central kernel `Z`; it is not quasi-isometric to `Gamma` and is not the finite-kernel
object requested here.

### 6. Are known residual-finiteness or linearity theorems ruling out the candidate?

For the most concrete connected-cover candidates in cocompact `SU(d,1)` of first kind, yes:
they are known residually finite.

Stover--Toledo prove that for cocompact arithmetic lattices `Gamma < PU(n,1)` of simple type,
the preimage of `Gamma` in any connected cover of `PU(n,1)` is residually finite. The arXiv
abstract states this directly, including the universal cover. Hill's cusp paper recalls the
same result as Theorem 1 for arithmetic subgroups of `SU(d,1)` of the first kind constructed
from a CM field with `[k:Q] > 2`, and says both `\widetilde{\Gamma}` and
`\widetilde{\Gamma}^{(n)}` are residually finite.

Primary sources:

- Matthew Stover and Domingo Toledo, "Residual finiteness for central extensions of lattices
  in `PU(n,1)` and negatively curved projective varieties", arXiv:2108.12404,
  <https://arxiv.org/abs/2108.12404>.
- Hill, "Residual finiteness of extensions of arithmetic subgroups of `SU(d,1)` with cusps",
  Theorem 1, <https://link.springer.com/article/10.1007/s12215-022-00793-0>.

For nonuniform `SU(d,1)` with cusps, Hill proves residual finiteness of the universal and finite
connected-cover preimages under a nonzero first inner cohomology hypothesis. These groups are
not word-hyperbolic for `d >= 2`, so even a negative result there would not solve the present
problem.

For real hyperbolic `SO(n,1)` / `Spin(n,1)` connected-cover candidates:

- `SO_0(n,1)` has only a finite topological cover for `n >= 3`, namely the spin double cover.
  The corresponding lifted arithmetic groups are linear in the spin group, hence residually
  finite by Malcev.
- This does not rule out an abstract finite central extension of such a lattice coming from
  Hill's cohomological construction, but again that construction needs finite rank-one
  congruence kernel.

## Status of the arithmetic route

The arithmetic implication is exact:

```math
\begin{array}{c}
\text{compact rank-one arithmetic lattice } \Gamma \\
+\ \text{finite congruence kernel for the ambient } G/\mathbb Q
\end{array}
\Longrightarrow
\begin{array}{c}
\text{finite central/finite abelian extension } \widetilde{\Gamma} \\
\text{that is word-hyperbolic and not residually finite.}
\end{array}
```

The proof of the implication is:

1. compact rank-one lattice `Gamma` is word-hyperbolic;
2. Hill's finite-congruence-kernel theorem gives a finite-kernel non-RF extension;
3. finite-kernel extension preserves word-hyperbolicity by quasi-isometry.

The missing input is:

```math
\mathrm{Cong}(G) \text{ finite for a compact real-rank-one arithmetic } G/\mathbb Q.
```

This is not known and is contrary to Serre's rank-one congruence-kernel conjecture as stated
by Hill. Therefore this route cannot currently produce an unconditional counterexample.

## Comparison with the quasiconvex-nonseparability route

The arithmetic route is attractive because it would produce an explicit finite-residual element:
any nontrivial element of the finite central kernel. But its missing input is not a local
calculation inside a known hyperbolic group; it is essentially a rank-one congruence-kernel
breakthrough.

The quasiconvex-nonseparability route is formally equivalent to the original problem by
Agol--Groves--Manning. It asks for a certificate

```math
(G,H,g),\qquad
G\ \text{hyperbolic},\quad
H<G\ \text{quasiconvex},\quad
g\notin H,
```

with `g` in the profinite closure of `H`. This route is not easier in principle, but it has a
more finite and inspectable witness than a global congruence-kernel conjecture. It also aligns
better with computational finite-quotient searches in short-presentation property-(T) hyperbolic
groups.

## Single most promising next prompt

Worker 03 should audit the quasiconvex-nonseparability route in explicit non-virtually-special
candidate families:

```text
Find or falsify a concrete witness (G,H,g) with G hyperbolic, H quasiconvex, g not in H,
and g in the profinite closure of H. Prioritize short property-(T) hyperbolic presentations
and generalized triangle groups; for each candidate, separately certify hyperbolicity,
quasiconvexity of H, non-membership g notin H, low-index/profinite evidence, and absence of
known virtual-special/cubulation theorems.
```

Arithmetic route remains conditional on: finite congruence kernel for a compact real-rank-one
arithmetic group, equivalently a failure of Serre's rank-one congruence-kernel expectation strong
enough to activate Hill's finite-extension theorem.
