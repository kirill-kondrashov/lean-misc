# Scenario: Hyperbolic Residual Finiteness Counterexample Worker 03

This note audits the explicit quasiconvex-nonseparability route requested after
[SCENARIO_hyperbolic_residual_finiteness_worker_01.md](./SCENARIO_hyperbolic_residual_finiteness_worker_01.md)
and
[SCENARIO_hyperbolic_residual_finiteness_worker_02.md](./SCENARIO_hyperbolic_residual_finiteness_worker_02.md).

No unconditional witness is found.

## Target certificate

The desired certificate is:

```math
G\ \text{word-hyperbolic},\qquad
H<G\ \text{quasiconvex},\qquad
g\notin H,
```

such that

```math
\forall \phi:G\to F\ \text{finite},\qquad \phi(g)\in \phi(H).
```

Equivalently, `g` lies in the profinite closure of `H` in `G`, but not in `H`.

Agol--Groves--Manning prove the governing equivalence: existence of a non-residually finite
word-hyperbolic group is equivalent to existence of a nonseparable quasiconvex subgroup of a
word-hyperbolic group. Thus a genuine explicit `(G,H,g)` witness is already a solution of the
open residual-finiteness problem for hyperbolic groups.

Primary source:

- I. Agol, D. Groves, J. F. Manning, "Residual finiteness, QCERF and fillings of hyperbolic
  groups", Geom. Topol. 13 (2009), 1043--1073,
  <https://www.alphaxiv.org/abs/0802.0709>.

## Strong blocking theorem

The strongest practical obstruction is the virtual-special filter:

```math
G\ \text{hyperbolic virtually special}
\Longrightarrow
\text{every quasiconvex subgroup of }G\text{ is separable}.
```

This excludes every candidate whose ambient group is known to be hyperbolic virtually special.
In particular, it eliminates:

- compact special / virtually special hyperbolic cube-complex groups;
- hyperbolic Coxeter groups, since finitely generated Coxeter groups are virtually special and
  hyperbolic Coxeter groups have separable quasiconvex subgroups;
- hyperbolic 3-manifold groups after Agol--Wise technology;
- many cubulated small-cancellation and hierarchy examples.

Primary sources:

- F. Haglund and D. Wise, "Special cube complexes", Geom. Funct. Anal. 17 (2008), 1551--1620,
  especially the word-hyperbolic quasiconvex subgroup separability result,
  <https://paperzz.com/doc/8264477/f.-haglund-and-d.-wise--special-cube-complexes>.
- F. Haglund and D. Wise, "Coxeter groups are virtually special", Adv. Math. 224 (2010),
  1890--1903, <https://www.sciencedirect.com/science/article/pii/S0001870810000307>.
- I. Agol, "The virtual Haken conjecture", Doc. Math. 18 (2013), 1045--1087,
  <https://arxiv.org/abs/1204.2810>.

## Candidate class A: short property-(T) hyperbolic groups

### Candidate source

Caprace--Conder--Kaluba--Witzel construct explicit infinite hyperbolic groups with Kazhdan's
property `(T)`, including very short presentations among nonpositively curved generalized
triangle groups. They also show that some of these groups have finite simple quotients of
arbitrarily large rank.

Primary source:

- P.-E. Caprace, M. Conder, M. Kaluba, S. Witzel, "Hyperbolic generalized triangle groups,
  property (T) and finite simple quotients", J. London Math. Soc. 106 (2022), 3577--3637,
  <https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.12668>.

### Audit against the certificate

- Finite presentation: yes, explicit short finite presentations.
- Word-hyperbolicity: yes for the groups certified in the paper.
- Quasiconvex subgroup `H`: no explicit nonseparable quasiconvex subgroup is supplied.
- Element `g notin H`: no explicit profinite-closure witness is supplied.
- Nonseparability theorem: absent. The paper studies property `(T)` and finite simple quotients,
  not subgroup separability witnesses.
- Virtual-special exclusion: property `(T)` makes these groups good places to look outside
  cocompact cubulation methods, but property `(T)` itself neither proves nor disproves residual
  finiteness. Finite groups have property `(T)`, and property `(T)` groups can have many finite
  quotients.

Status: **insufficient**.

The useful information is negative/strategic: these are plausible ambient groups for future
search because many virtual-special methods are unavailable. But no current theorem turns them
into nonseparable-quasiconvex examples.

## Candidate class B: generalized triangle groups and finite quotient scarcity

Caprace--Conder--Kaluba--Witzel also formulate a representation-variety approach to finite
quotients of hyperbolic quotients of `PSL_2(Z)`. Their Question 5.17 asks, in effect, whether
certain coordinate rings attached to finite-dimensional representations are nonzero. They note
that the question is formally equivalent to residual finiteness of all hyperbolic groups, via
Kapovich--Wise and Olshanskii common-quotient technology.

This is not a quasiconvex nonseparability witness. It is a different algebraic packaging of the
same residual-finiteness problem.

Audit:

- Finite presentation and hyperbolicity: available for many generalized triangle examples.
- Quasiconvex subgroup: not specified.
- `g notin H`: not specified.
- Profinite nonseparability proof: not supplied.
- Known positive evidence: some groups in their census have abundant finite simple quotients,
  including alternating quotients in large ranks.

Status: **reduces to original conjecture**, not a witness.

## Candidate class C: Rips-type groups

Rips constructions produce short exact sequences

```math
1\to N\to G\to Q\to 1
```

with `G` small-cancellation and hyperbolic and `N` finitely generated. This is a standard source
of pathological finitely generated subgroups of hyperbolic groups.

However, the Rips kernel `N` is normal. If `G` is non-elementary hyperbolic and an infinite
normal subgroup `N` is quasiconvex, then `N` has finite index in `G`. One way to see the
obstruction is through finite-width/height phenomena for quasiconvex subgroups, or directly
through the theorem that infinite quasiconvex subgroups have finite index in their normalizers.
Since `N` is normal, its normalizer is all of `G`; hence quasiconvex `N` forces finite index.
Then the quotient `Q` is finite, and the pathological Rips quotient disappears.

Primary sources:

- E. Rips, "Subgroups of small cancellation groups", Bull. London Math. Soc. 14 (1982), 45--47.
- Rita Gitik, Mahan Mitra, Eliyahu Rips, Michah Sageev, "Widths of subgroups", Trans. Amer.
  Math. Soc. 350 (1998), 321--329,
  <https://cris.huji.ac.il/en/publications/widths-of-subgroups/>.
- M. Gromov/Kapovich--Short style normalizer obstruction in the form recorded by Short:
  H. Short, "Quasiconvex subgroups of negatively curved groups", J. Pure Appl. Algebra 95
  (1994), 297--301,
  <https://www.sciencedirect.com/science/article/pii/0022404994900639>.

Audit:

- Finite presentation and hyperbolicity: yes for standard small-cancellation Rips output.
- Subgroup nonseparability/pathology: often yes for finitely generated subgroups.
- Quasiconvexity: fails for the normal Rips kernel unless the quotient is finite.
- Explicit `g`: not relevant without quasiconvexity.

Status: **blocked at quasiconvexity**.

## Candidate class D: known nonseparable subgroups in nearby groups

There are classical non-LERF examples near geometric group theory:

- Burns--Karrass--Solitar give finitely generated nonseparable subgroups in an infinite cyclic
  extension of a finitely generated free group.
- Niblo--Wise give non-subgroup-separable knot/link and graph-manifold examples.

Primary sources:

- R. G. Burns, A. Karrass, D. Solitar, "A note on groups with separable finitely generated
  subgroups", Bull. Austral. Math. Soc. 36 (1987), 153--160,
  <https://cir.nii.ac.jp/crid/1361137045617402880>.
- G. A. Niblo, D. T. Wise, "Subgroup separability, knot groups, and graph manifolds",
  Proc. Amer. Math. Soc. 129 (2001), 685--693,
  <https://eprints.soton.ac.uk/29816/>.

Audit:

- Ambient hyperbolicity: generally absent or must be checked case-by-case.
- If the ambient group is a modern hyperbolic free-by-cyclic group, current virtual-special
  results push in the positive direction for quasiconvex subgroup separability.
- Known nonseparable subgroups in these examples are not supplied with quasiconvexity proofs.
  In mapping-torus-style examples, the most natural distorted fiber-type subgroups are not
  quasiconvex in a hyperbolic ambient group.

Status: **insufficient / usually outside the target category**.

## Candidate class E: explicit non-quasiconvex subgroups of hyperbolic groups

Kapovich constructed a torsion-free word-hyperbolic group with a finitely presented
non-quasiconvex subgroup having exotic limit-set behavior. Dani--Levcovitz later gave explicit
methods for constructing non-quasiconvex subgroups of hyperbolic right-angled Coxeter groups.

Primary sources:

- I. Kapovich, "A non-quasiconvex subgroup of a hyperbolic group with an exotic limit set",
  New York J. Math. 1 (1995), 184--195,
  <https://eudml.org/doc/119161>.
- P. Dani, I. Levcovitz, "Non-quasiconvex subgroups of hyperbolic groups via Stallings-like
  techniques", Trans. Amer. Math. Soc. 376 (2023), 1427--1444,
  <https://repository.lsu.edu/mathematics_pubs/1475/>.

Audit:

- Ambient hyperbolicity: yes.
- Explicit subgroup: yes.
- Quasiconvexity: explicitly no.
- Separability: not the relevant property for the AGM witness.
- Virtual-special filter: Dani--Levcovitz examples are in hyperbolic right-angled Coxeter
  groups, which are virtually special; all quasiconvex subgroups there are separable. Their
  non-quasiconvex subgroups may be interesting, but cannot serve as AGM witnesses.

Status: **falsified for this route**.

## Candidate class F: hyperbolic 3-manifold groups

Before Agol--Wise, 3-manifold groups were a tempting source because immersed surfaces and
subgroup separability questions were central. After virtual specialness, the quasiconvex part
is no longer a source of counterexamples.

For closed hyperbolic 3-manifold groups, Agol's theorem plus Bergeron--Wise/Kahn--Markovic
cubulation gives virtual specialness. Hence quasiconvex subgroups are separable. Non-quasiconvex
fiber subgroups in fibered hyperbolic 3-manifolds are not candidates.

Status: **blocked by virtual specialness for quasiconvex subgroups**.

## What would count as a genuine advance?

For a fixed explicit presentation `G`, a finite search through quotients is not enough. To
advance the problem, one needs a certificate covering all finite quotients. A credible finite
subproblem is:

1. choose a named hyperbolic property-`(T)` generalized triangle group `G` from
   Caprace--Conder--Kaluba--Witzel whose hyperbolicity proof is published;
2. choose a finitely generated subgroup `H<G` with a machine-checkable quasiconvexity certificate
   such as an automatic-structure/Stallings-graph certificate;
3. choose `g` and certify `g notin H` using the word/membership algorithms for quasiconvex
   subgroups of hyperbolic groups;
4. prove an all-finite-quotients obstruction, for example by proving that every homomorphism
   from `G` to a finite group satisfying the relators sends `g` into the image of `H`.

The hard part is item 4. It cannot be replaced by searching finite quotients up to a bound. A
real certificate would have to use a structural theorem on finite quotients of the chosen
presentation, or an algebraic-geometry certificate proving emptiness of the relevant
representation varieties in every dimension. That last condition is close to the
Caprace--Conder--Kaluba--Witzel representation-variety reformulation and is therefore likely as
hard as the original problem unless the chosen `H,g` introduce extra structure.

## Strongest surviving next step

The strongest surviving route is a narrowed property-`(T)` generalized-triangle-group project:

```text
Pick one explicit infinite hyperbolic property-(T) generalized triangle group from
Caprace--Conder--Kaluba--Witzel. Do not begin with finite quotient enumeration. First construct
a small quasiconvex subgroup H with a formal quasiconvexity certificate and an element g notin H.
Then attempt to prove a structural all-finite-quotient statement for the pair (H,g), ideally via
the finite simple quotient/representation-variety machinery already developed for that class.
```

This is stronger than searching arbitrary hyperbolic groups because:

- hyperbolicity and property `(T)` are already certified for the ambient group;
- virtual-special separability methods are not expected to apply directly;
- the same literature already contains finite-simple-quotient and representation-variety tools.

No unconditional witness found; surviving obstruction: every explicit candidate class either is
known to have separable quasiconvex subgroups by virtual specialness, supplies only
non-quasiconvex nonseparable/pathological subgroups, or reduces to the original open problem of
finding a non-residually finite hyperbolic group.
