# Plan: Flux / Calibration Route For The Two-Layer Boundary Inequality

This note records the most promising new route suggested by the geometric interpretation of the
last frontier.

## Target

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

The target theorem is

\[
|\partial^+F| \ge |C|.
\tag{B}
\]

## Idea

Interpret \(C\) as the lower sheet of a membrane and \(\partial^+F\) as the outward side of that
membrane. Instead of proving \((B)\) by an injection or by compression first, try to prove it by a
fractional transport / divergence principle.

## Desired Calibration Statement

Seek weights

\[
w_{A,B} \ge 0
\]

for pairs

\[
A \in C,
\qquad
B \in \partial^+F,
\]

such that:

1. each lower-sheet cell sends one unit of mass:
   \[
   \sum_{B} w_{A,B} = 1
   \qquad
   (A \in C);
   \]
2. each boundary cell receives at most one unit:
   \[
   \sum_{A} w_{A,B} \le 1
   \qquad
   (B \in \partial^+F).
   \]

Summing over \(A\) and \(B\) would give

\[
|C| \le |\partial^+F|.
\]

## Why This Route Is Plausible

- The Hall-shadow route failed because it asked for too rigid a matching surrogate.
- A calibration is weaker than a matching and closer to how continuous minimal-surface arguments
  work.
- The equality candidates already suggested by shifted search
  \[
  F = \binom{[n]}{m}
  \qquad\text{and}\qquad
  F = \{A \in \binom{[n]}{m}: 0\in A\}\cup \{B \in \binom{[n]}{m+1}: 0\in B\}
  \]
  are exactly the sort of rigid shapes where a flux proof might be sharp.

## Current Exact Evidence

- The codimension-`1` local transport graph is too small: exact `n = 5` already finds a Hall
  failure at `e = 3`.
- The codimension-`2` local transport graph survives exact `n = 5`: every equal-size middle-layer
  pair admits a Hall-satisfying local transport graph when each lower cell is allowed to connect to
  boundary cells one or two ranks above it.
- The same qualitative split now survives in the shifted `n = 7` model:
  the codimension-`1` local Hall graph fails with worst deficiency `-15` at `e = 20`, while the
  codimension-`2` local Hall graph survives across all shifted pairs.
- The simplest codimension-`2` weighting rule is still too naive:
  equal-split transport already overloads a boundary cell in exact `n = 5`, and also in shifted
  `n = 7`.
- The next natural local rule also fails:
  inverse-degree weighting already overloads a boundary cell in exact `n = 5`, and also in shifted
  `n = 7`.

So the first viable local candidate is not the pure upward-edge graph, but the codimension-`2`
transport graph suggested by the geometry of the odd boundary. However, it needs a genuinely
nonuniform weighting rule.

There is now a sharper exact pattern behind that graph. Let
\[
\nu_1(F)
\]
be the maximum matching size in the codimension-`1` local graph, and let
\[
\delta_1(F):=|C|-\nu_1(F)
\]
be the codimension-`1` Hall deficiency. Then exact `n = 5` and shifted `n = 7` both satisfy:
\[
\min\{\text{number of codim-2 edges in a perfect local matching}\} = \delta_1(F).
\]
So the surviving codimension-`2` route is no longer just “some perfect matching exists.” On the
tested domains, the codimension-`2` usage is exactly the amount forced by the codimension-`1`
defect.

The first naive explanation of that defect is now archived. Exact `n = 5` and shifted `n = 7`
both show that
\[
\delta_1(F)
\]
can be strictly larger than the number of lower cells with no codimension-`1` neighbor in the
local graph. So the matching-cost identity is not just measuring isolated lower cells; it is a
more genuinely global Hall obstruction.

The first geometric cut explanation is archived too. Exact `n = 5` and shifted `n = 7` both show
that
\[
\delta_1(F)
\]
can be strictly larger than the best deficiency obtained from any single-coordinate contain/avoid
cut on the lower sheet. So \(\delta_1(F)\) is not captured by a single principal-star cut either.

But the shifted route now has a positive Hall witness theorem candidate. In shifted `n = 5` and
shifted `n = 7`, the codimension-`1` Hall deficiency is always witnessed by a shifted lower
subfamily. So while \(\delta_1(F)\) is more global than a single cut, it still appears compatible
with compression on the shifted subproblem.

The next canonical strengthening is now partly archived. Exact shifted diagnostics show:

- a colex-prefix witness theorem is false already in shifted `n = 5`;
- a lex-prefix witness theorem survives shifted `n = 5` but is false in shifted `n = 7`.
- an initial-principal-star witness theorem survives shifted `n = 5` but is false in shifted
  `n = 7`.

So the shifted Hall witness can be canonicalized to a shifted lower subfamily, but not all the way
to a simple lex/colex prefix or initial principal star of the lower sheet.

## Concrete Program

### 1. Choose The Right Transport Graph

The basic candidate graph has left side \(C\) and right side \(\partial^+F\). Connect \(A \in C\)
to \(B \in \partial^+F\) when \(A\) is a codimension-1 or codimension-2 predecessor of \(B\).

The point is not to insist on single-step adjacency only; the section decomposition suggests that
two kinds of upward exposure may have to be combined.

### 2. Find A Canonical Local Weight Rule

Look for a local rule depending only on ranks and local predecessor counts, for example weights of
the form

\[
w_{A,B} = \frac{1}{d_F(A)} \cdot \lambda(A,B),
\]

where \(d_F(A)\) counts available outward directions from \(A\), and \(\lambda(A,B)\) splits mass
among exposed upper cells.

The equal-split rule
\[
w_{A,B} = \frac{1}{d_F(A)}
\]
on the codimension-`2` graph is now archived: it overloads a boundary point already in exact
`n = 5`, and also in shifted `n = 7`.

The inverse-degree rule
\[
w_{A,B} \propto \frac{1}{\deg(B)}
\]
is now archived as well: it overloads already in exact `n = 5`, and also in shifted `n = 7`.

The first finite family of canonical greedy matching rules is archived too. Testing all eight
priority combinations given by:

- left order ascending / descending,
- codimension priority ascending / descending,
- boundary order ascending / descending,

shows that every such rule fails already in exact `n = 5`. One rule,
\[
\texttt{left-desc-codim-asc-boundary-desc},
\]
does survive across all shifted pairs in `n = 7`, but it still fails in exact `n = 5`, so it is
not a viable global route.

### 3. Test The Rule On Equality Models

The calibration should be exact on:

- the full lower layer \(F=\binom{[n]}{m}\),
- the principal-star two-layer family.

If the candidate weighting is not sharp there, it is likely the wrong object.

### 4. Push Through Shifted Families First

Because shifted extremizers are the only equality cases known in `n = 5` and `n = 7`, first seek a
proof on shifted \(F\). The current computational checkpoint is now:

\[
\text{codim-1 fails in shifted } n=7,\qquad \text{codim-2 survives in shifted } n=7.
\]

So the next proof target on this branch is no longer “some local flux graph,” but specifically:

- prove the codimension-`2` Hall/matching property for shifted \(F\);
- prove the sharpened codimension-`2` matching-cost theorem
  \[
  \min\{\text{codim-2 edges in a perfect local matching}\} = \delta_1(F)
  \]
  first for shifted \(F\);
- prove that for shifted \(F\), the codimension-`1` Hall deficiency \(\delta_1(F)\) is witnessed
  by a shifted lower subfamily;
- do not try to strengthen that immediately to a lex/colex-prefix witness theorem:
  colex-prefix is already falsified in shifted `n = 5`, and lex-prefix is already falsified in
  shifted `n = 7`;
- do not try to replace the shifted witness theorem by a single initial-principal-star theorem
  either: that survives shifted `n = 5` but is already falsified in shifted `n = 7`;
- understand \(\delta_1(F)\) itself as a genuinely global obstruction, not just a zero-degree
  count;
- and not just the best one-coordinate contain/avoid cut deficiency;
- then convert that matching into an actual fractional calibration;
- equivalently, find a genuinely nontrivial codimension-`2` weighting rule, since both the
  equal-split and inverse-degree local rules are already falsified;
- or find a genuinely non-greedy explicit injection, since the first finite family of canonical
  greedy rules is now archived;
- then either extend the calibration to arbitrary \(F\), or combine it with compression.

After that either:

- extend the calibration to arbitrary \(F\), or
- combine it with the compression route once the latter is formalized.

### 5. Avoid The Archived Even Adjacent-Layer Detour

The unrestricted even adjacent-layer theorem
\[
|\partial^+G| \ge |G_r|
\]
is false, and the corrected coupled section theorem is false as well. So the calibration should be
designed directly for the odd two-layer family \(F=C\cup U\), not via an auxiliary lower-
dimensional theorem.

If sectioning is used at all, it should enter only as an exact identity or as a way to guess the
right cross-term bookkeeping for the flux, not as a separate reduction target.

## Success Criterion

This route succeeds once a concrete weighting rule is found and checked to imply \((B)\), first on
shifted odd two-layer families and then in the full odd two-layer setting.
