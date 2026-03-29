# Plan: Geometric Enrichment Of The Two-Layer Boundary Route

This note records the non-discrete geometric heuristics that now guide the remaining proof search
for the two-layer inequality.

## Core Discrete Object

Let

\[
n := 2m+1,
\qquad
U \subseteq \binom{[n]}{m+1},
\qquad
V \subseteq \binom{[n]}{m},
\qquad
|U| = |V|.
\]

Define

\[
C := \binom{[n]}{m}\setminus V,
\qquad
F := C \cup U.
\]

The active theorem is

\[
|\partial^+F| \ge |C|.
\tag{B}
\]

Here \(F\) is supported on the two middle layers
\[
\binom{[n]}{m}\sqcup \binom{[n]}{m+1},
\]
so it should be thought of as a discrete hypersurface near the equator of the odd cube.

## Geometric Reading

The family \(F\) is a discrete membrane, and \(\partial^+F\) is its outward-facing side. Thus
\((B)\) is a one-sided isoperimetric statement:

> a balanced equatorial membrane cannot expose less outer area than the amount of lower sheet that
> survives.

This suggests importing proof shapes from continuous geometry, even though the theorem itself is
purely discrete.

## Path A: Symmetrization / Discrete Mean Curvature

The first enrichment is to interpret layer-preserving shifts as discrete Steiner symmetrizations.
The target is:

\[
|\partial^+(S_{ij}F)| \le |\partial^+F|
\]

for every layer-preserving compression \(S_{ij}\).

If true, this would say that symmetrizing the membrane does not increase its outer area. Then the
proof of \((B)\) reduces to shifted families, where the equality cases are expected to be the
flattest interfaces:

\[
F = \binom{[n]}{m}
\qquad\text{and}\qquad
F = \{A \in \binom{[n]}{m} : 0 \in A\}\cup \{B \in \binom{[n]}{m+1} : 0 \in B\}.
\]

This is the discrete mean-curvature picture: minimizers should be the most symmetric or flat
interfaces.

## Path B: Flux / Calibration

The second enrichment is to replace matching-style arguments by a fractional transport.

Seek weights \(w_{A,B}\) indexed by
\[
A \in C,
\qquad
B \in \partial^+F,
\qquad
A \subset B,
\qquad
|B| = |A|+1 \text{ or } |A|+2,
\]
such that

\[
\sum_{B} w_{A,B} = 1
\qquad\text{for every } A \in C,
\]

and

\[
\sum_{A} w_{A,B} \le 1
\qquad\text{for every } B \in \partial^+F.
\]

Then summing gives

\[
|C| \le |\partial^+F|.
\]

This is the discrete divergence/calibration version of the theorem. It is weaker than demanding a
literal injection \(C \hookrightarrow \partial^+F\), and so it may succeed even though the stronger
Hall-type surrogate routes already failed.

## Path C: Coarea / Sectioning

The third enrichment is the discrete coarea idea already partly implemented in the proof notes.
Section the membrane by one coordinate and write

\[
|\partial^+F|
\ge
|\partial^+(A\cup D)| + |\partial^+(B\cup E)|.
\]

This remains geometrically informative, but not as a standalone proof route: both the unrestricted
even adjacent-layer theorem and the corrected coupled section theorem are false. So sectioning is
best treated as a source of structural intuition and exact identities, not as the current active
reduction theorem.

## Hypersimplex Viewpoint

The two middle layers
\[
\binom{[n]}{m}\sqcup \binom{[n]}{m+1}
\]
form a two-slab between adjacent hypersimplices. In this language, \(F\) is a subcomplex of that
slab and \(\partial^+F\) counts the exposed top faces. This suggests shelling or discrete Morse
arguments: exposed upper faces should dominate the surviving lower faces.

## Recommended Use

These geometric heuristics are not separate theorems yet. They are proof-design guides for the two
active concrete routes:

- [PLAN_two_layer_flux_calibration_route.md](./PLAN_two_layer_flux_calibration_route.md)

The archived section branch is recorded in
[PLAN_even_adjacent_layer_section_route.md](./PLAN_even_adjacent_layer_section_route.md).
