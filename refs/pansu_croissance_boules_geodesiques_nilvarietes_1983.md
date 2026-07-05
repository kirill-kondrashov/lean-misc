# Pansu (1983) — reference stub (paywalled primary; PDF not redistributable)

**Pierre Pansu.** *Croissance des boules et des géodésiques fermées dans les
nilvariétés.* Ergodic Theory and Dynamical Systems, **3** (1983), no. 3, 415–445.
DOI: [10.1017/S0143385700002054](https://doi.org/10.1017/S0143385700002054)

> **Note on availability.** This is a copyrighted journal article behind a paywall
> (Cambridge University Press). No free author-hosted PDF exists on Pierre Pansu's
> homepage (`imo.universite-paris-saclay.fr/~pierre.pansu/fpub.html` lists only
> recent works). We therefore do **not** redistribute the PDF here. An openly
> available surrogate that states and generalizes Pansu's result is included in
> this folder: `breuillard_polynomial_growth_shape_of_large_balls_2014.pdf`
> (E. Breuillard, arXiv:0704.0095). The precise statement we depend on is recorded
> below, sourced from Bodart §1 (arXiv:2306.10381v3, in this folder).

## What we need from Pansu (as used by Bodart §1, and Breuillard)

- **Pansu's volume-growth theorem.** For a finitely generated (virtually)
  nilpotent group `G` with finite generating set `S`, the ball-counting /
  growth function satisfies an *exact* leading-order asymptotic
  `β_{(G,S)}(n) = c_{(G,S)}·n^d + o(n^d)`,
  where `d` is the homogeneous dimension `d = Σ_i i·dim(G_i/G_{i+1})` of the
  associated graded (Carnot) group, and `c_{(G,S)} > 0` is a constant. This is
  the "celebrated result" quoted by Bodart at the top of §1. Equivalently
  (Breuillard, generalizing Pansu): rescaled balls `(1/n)·B(n)` converge in the
  Gromov–Hausdorff sense to a fixed convex body in the tangent Carnot group,
  whose volume gives `c_{(G,S)}`.

- **Consequence used here.** Volume growth of the word-metric ball is
  *polynomial* of degree `d`. For our virtually Engel example this is the
  polynomial box already made elementary and explicit in
  `Groups/EngelGeodesicGrowth.lean` (endpoint O(n), area O(n²), bary3 O(n³) ⇒
  image in an O(n⁶) lattice box).

## Role in the formalization program

Pansu polynomial volume growth is the counting backbone of `theorem_4_upper`:
the geodesic-word count is controlled by (number of endpoints) × (geodesics per
endpoint); the endpoint factor is Pansu-polynomial, and the superpolynomial
`exp(n^{3/5} log n)` factor comes from the Stoll-metric multiplicity of geodesics
to a fixed endpoint. See `Groups/StollPansu.lean` for the Lean scaffold of this
decomposition.
