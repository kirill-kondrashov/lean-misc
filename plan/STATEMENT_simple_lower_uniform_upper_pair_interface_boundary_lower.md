# Statement: `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement`

This note records the mathematical formulation of
`SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement` in standard notation.

## Standard Notation

Let

\[
n := 2m+1,
\qquad
L_m := \{S \subseteq [n] : |S| \le m\}.
\]

Let

\[
V \subseteq \binom{[n]}{m},
\qquad
U \cap L_m = \varnothing,
\qquad
|U| = |V|,
\qquad
\forall s \in U,\ |s| = m+1.
\]

Define the simple-lower pair

\[
M := L_m \setminus V,
\qquad
N := L_m \cup U.
\]

Then `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement` says:

\[
|\partial^+ N|
+
\left|(N \setminus M)\cup \partial^+ M\right|
\ge
2\binom{2m+1}{m}.
\]

Since

\[
N \setminus M = (L_m \cup U)\setminus(L_m \setminus V)=U \cup V,
\]

this is equivalently

\[
\left|\partial^+(L_m \cup U)\right|
+
\left|(U \cup V)\cup \partial^+(L_m \setminus V)\right|
\ge
2\binom{2m+1}{m}.
\]

## Plain English

Start from the odd lower half \(L_m\). Remove some middle-layer sets \(V\), and add the same
number of new sets \(U\), all lying exactly in the next layer of size \(m+1\). Then the resulting
simple-lower pair always has pair-interface boundary at least the middle-layer target

\[
2\binom{2m+1}{m}.
\]

So a strict pair-interface boundary defect cannot occur if the added upper family stays entirely in
the middle layer.

## Relation To The Main Bottleneck

The Lean file proves

\[
\texttt{SimpleLowerPairInterfaceBoundaryDefectForcesUpperCardAboveMiddleStatement}
\iff
\texttt{SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement}.
\]

So this statement is the clean contrapositive form of the last remaining simple-lower theorem in
the current prism route.

## Status

A complete proof is not written here, because this statement is still the live mathematical
bottleneck in the current development. What is available is the exact reduction of the theorem to a
pure middle-layer inequality.

## Exact Reduction

Assume

\[
U \subseteq \binom{[n]}{m+1}.
\]

Define

\[
\Phi(U,V)
:=
\left|\partial^+(L_m \cup U)\right|
+
\left|(U \cup V)\cup \partial^+(L_m \setminus V)\right|.
\]

Then the theorem is exactly the claim

\[
\Phi(U,V)\ge 2\binom{n}{m}.
\]

Now:

1. Since \(L_m\) contains every set of size at most \(m\), the positive boundary of \(L_m \cup U\)
   consists of:
   - every missing \((m+1)\)-set,
   - together with every \((m+2)\)-set containing some member of \(U\).

   So if
   \[
   \partial^\uparrow U
   :=
   \{T \in \tbinom{[n]}{m+2} : \exists s \in U,\ s \subset T\},
   \]
   then
   \[
   \partial^+(L_m \cup U)
   =
   \left(\binom{[n]}{m+1}\setminus U\right)\sqcup \partial^\uparrow U,
   \]
   and therefore
   \[
   \left|\partial^+(L_m \cup U)\right|
   =
   \binom{n}{m+1} - |U| + |\partial^\uparrow U|.
   \]

2. Define
   \[
   T(V)
   :=
   \left\{B \in \binom{[n]}{m+1} : \binom{B}{m}\subseteq V\right\}.
   \]
   A set \(B \in \binom{[n]}{m+1}\) lies in \(\partial^+(L_m \setminus V)\) iff it has at least one
   \(m\)-subset outside \(V\), i.e. iff \(B \notin T(V)\). Hence
   \[
   \partial^+(L_m \setminus V)
   =
   \binom{[n]}{m+1}\setminus T(V).
   \]
   Since this boundary lies entirely in rank \(m+1\), we get
   \[
   \left|(U \cup V)\cup \partial^+(L_m \setminus V)\right|
   =
   |V| + \left|U \cup \left(\binom{[n]}{m+1}\setminus T(V)\right)\right|.
   \]
   Therefore
   \[
   \left|(U \cup V)\cup \partial^+(L_m \setminus V)\right|
   =
   |V| + \binom{n}{m+1} - |T(V)\setminus U|.
   \]

3. Since \(|U|=|V|\) and \(\binom{n}{m+1}=\binom{n}{m}\) for \(n=2m+1\), adding the two formulas
   gives
   \[
   \Phi(U,V)
   =
   2\binom{n}{m}
   +
   |\partial^\uparrow U|
   -
   |T(V)\setminus U|.
   \]

So `SimpleLowerUniformUpperPairInterfaceBoundaryLowerStatement` is equivalent to the inequality

\[
|\partial^\uparrow U| \ge |T(V)\setminus U|.
\]

## What Would Finish The Proof

It would suffice to prove the following purely middle-layer statement:

> For every
> \[
> U \subseteq \binom{[2m+1]}{m+1},
> \qquad
> V \subseteq \binom{[2m+1]}{m},
> \qquad
> |U|=|V|,
> \]
> one has
> \[
> |\partial^\uparrow U| \ge |T(V)\setminus U|.
> \]

This is the exact compression/isoperimetric lemma now blocking the proof.
