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

### 3. Test The Rule On Equality Models

The calibration should be exact on:

- the full lower layer \(F=\binom{[n]}{m}\),
- the principal-star two-layer family.

If the candidate weighting is not sharp there, it is likely the wrong object.

### 4. Push Through Shifted Families First

Because shifted extremizers are the only equality cases known in `n = 5` and `n = 7`, first seek a
proof on shifted \(F\). Then either:

- extend the calibration to arbitrary \(F\), or
- combine it with the compression route once the latter is formalized.

### 5. Relate To The Even Adjacent-Layer Theorem

The calibration should also be reformulated for

\[
G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1},
\]

with target

\[
|\partial^+G| \ge |G_r|.
\]

That even-dimensional statement is the cleanest place to search for the correct flux law.

## Success Criterion

This route succeeds once a concrete weighting rule is found and checked to imply \((B)\), first in
the shifted even-dimensional adjacent-layer setting and then in the full odd two-layer setting.
