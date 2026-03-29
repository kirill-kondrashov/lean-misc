# Plan: Stronger-Than-Middle-Binomial Lower Bound Via A Two-Layer Gap

This note records the new research direction beyond the current exact middle-binomial route.

## Objective

The current formal route is designed to recover the exact lower bound
\[
N \ge \binom{n}{\lfloor n/2\rfloor}.
\]

That is already the published Dubroff-Fox-Xu benchmark. The new goal is to go further and prove a
strictly stronger lower bound of the form
\[
N \ge \binom{n}{\lfloor n/2\rfloor} + g(n),
\qquad g(n) > 0,
\]
or, more ambitiously, a multiplicative/stability strengthening that moves toward
\[
N \gg 2^n.
\]

## Connection To The Current Route

The active exact route reduces the remaining work to the two-layer theorem
\[
|\partial^+F| \ge |C|,
\qquad
F := \left(\binom{[n]}{m}\setminus V\right)\cup U,
\qquad
n=2m+1,
\qquad
|U|=|V|.
\]

This route is valuable even for the stronger problem because any quantitative strengthening of this
boundary inequality feeds the same arithmetic closure mechanism.

The right strengthened target is therefore not a different theorem, but a strengthened version of
the same theorem:
\[
|\partial^+F| \ge |C| + \Gamma(F),
\]
where \(\Gamma(F)\ge 0\) is a gap term that vanishes only on genuine equality templates.

If one can prove
\[
\Gamma(F) \ge g(n)
\]
for the particular two-layer families arising from the sum-distinct transport, then the exact same
formal endpoint route should upgrade
\[
\binom{n}{\lfloor n/2\rfloor} \le N
\]
to
\[
\binom{n}{\lfloor n/2\rfloor} + g(n) \le N.
\]

## Critical Review Of The Existing Exact Plan

The current active exact plan has three strengths:

- it isolates one concrete combinatorial theorem;
- it has strong exact support for weak compression and shifted rigidity;
- it already exposes the expected equality templates in the shifted world.

But it also has a decisive limitation:

- even a complete proof of the current exact theorem would only re-prove the literature-level
  middle-binomial lower bound.

So the exact plan should now be treated as *infrastructure*. The publishable/new-content target is
the next layer:

- classify equality;
- prove a positive gap away from equality;
- show the transported sum-distinct families are never equality templates, and in fact stay a
  positive distance away.

## Equality Templates

The exact shifted evidence currently points to exactly two equality templates:

1. the full lower layer
   \[
   F = \binom{[n]}{m};
   \]
2. the principal-star two-layer family
   \[
   F =
   \{A\in \binom{[n]}{m} : 0\in A\}
   \;\cup\;
   \{B\in \binom{[n]}{m+1} : 0\in B\},
   \]
   up to permutation.

The strengthened program should start by promoting this from computational evidence to a theorem,
at least first in the shifted world.

## Current Shifted Gap Profile

The first strict-gap diagnostic is now exact in the shifted world for `n = 5` and `n = 7`.

- shifted `n = 5`: the only equality orbits are the two templates above, and every other shifted
  pair satisfies
  \[
  |\partial^+F| \ge |C| + 2;
  \]
- shifted `n = 7`: the same two equality templates are the only equality orbits, and every other
  shifted pair satisfies
  \[
  |\partial^+F| \ge |C| + 3.
  \]

So the shifted evidence is already stronger than the original additive `+1` target. The current
paper-level task is therefore not just “prove some positive gap,” but:

\[
\text{prove a uniform strict gap off the two equality templates, first in the shifted world.}
\]

## Current Shifted Distance Profile

The gap data is now refined by exact distance-to-template diagnostics in the shifted world.

- shifted `n = 5`: the nearest non-equality pairs occur at template distance `2`, and their
  boundary gap is exactly `2`;
- shifted `n = 7`: the nearest non-equality pairs again occur at template distance `2`, but their
  boundary gap is already `3`.

So the first stability signal is:

\[
\text{near-template shifted pairs already pay at least a distance-}2\text{ penalty,}
\]

and in `n = 7` the boundary gap is strictly stronger than that first template distance.

This makes the next theorem target more geometric than the earlier additive-gap phrasing:

\[
|\partial^+F| - |C|
\quad\text{should be controlled from below by a genuine distance-from-template functional.}
\]

## Current Global First-Gap Orbit Profile

The first strict-gap orbit set is now exact in the shifted world.

- shifted `n = 5`: the global strict gap `2` is attained by exactly `7` orbit types;
- shifted `n = 7`: the global strict gap `3` is attained by exactly `5` orbit types.

More importantly, the shifted `n = 7` extremal picture is already rigid:

- every global first-gap orbit lies at template distance `2` from one of the two equality
  templates.
- more sharply, the entire shifted distance-`2` shell has now been checked exactly:
  it consists of `5` orbit types, every one has boundary gap `3`, and these are exactly the
  `5` global first-gap orbit types.

This shell picture is not dimension-free evidence: in shifted `n = 5`, the distance-`2` shell has
only `5` orbit types while the global first-gap set has `7` orbit types, so the exact
distance-`2` characterization is false there.

So the first nontrivial shifted stability theorem now has a sharper candidate shape:

\[
\text{from at least the first genuinely nontrivial shifted dimension onward, the minimal}
\]
\[
\text{strict-gap configurations should be exactly the codimension-}2
\text{ perturbations of the equality templates.}
\]

That is still only evidence, but it is much sharper than a bare “positive gap off equality”
statement.

## Main Gap Program

### Step 1. Prove Shifted Equality Classification

Prove in the shifted setting:
\[
|\partial^+F| = |C|
\]
if and only if \(F\) is one of the two equality templates above.

This is the minimal structural theorem needed before any gap theorem can be honest.

### Step 2. Prove A Shifted Stability / Gap Theorem

After equality is classified, prove a quantitative strengthening such as
\[
|\partial^+F| - |C| \ge \operatorname{dist}(F,\mathcal E),
\]
or at least
\[
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| \ge |C| + 1,
\]
where \(\mathcal E\) is the set of equality templates.

The first realistic goal is the qualitative additive gap `+1`. That alone would already beat the
exact middle-binomial lower bound.

The shifted diagnostics now suggest the first honest target is stronger:
\[
F \notin \mathcal E
\quad\Longrightarrow\quad
|\partial^+F| \ge |C| + 2
\]
in the shifted odd two-layer problem, with `n = 5` and `n = 7` as exact supporting cases.

### Step 3. Show Sum-Distinct Transported Families Avoid Equality

The stronger lower bound will not follow from a generic two-layer theorem alone. One must use the
extra structure of the transported family coming from sum-distinct sets.

The key exclusion problem is:

> show that the two-layer family produced by the current subcube/half-cube transport can never be
> one of the equality templates, except in trivial or forbidden cases.

A stronger version would quantify its distance from those templates.

This is where the current formal route should help most: the transport is already explicit, and
the equality templates are very rigid.

### Step 4. Convert Exclusion Into A Stronger Lower Bound

Once Step 2 and Step 3 are available, deduce
\[
|\partial^+F| \ge |C| + 1
\]
for all transported sum-distinct families, hence
\[
N \ge \binom{n}{\lfloor n/2\rfloor} + 1.
\]

After that, the program can be iterated:

- classify near-equality shifted families;
- prove stronger stability inequalities;
- prove the transported families stay quantitatively far from the equality templates;
- upgrade the additive `+1` gap to a larger explicit function \(g(n)\).

## Concrete Near-Term Tasks

1. Write down the exact shifted equality classification conjecture as a standalone theorem target.
2. Promote the exact shifted gap profile from evidence to a theorem:
   for shifted `n = 5` and shifted `n = 7`, the first strict gap off the equality templates is
   `2` and `3` respectively.
3. Formulate the weakest nontrivial theorem that matches the current data:
   the shifted odd two-layer problem should satisfy an additive `+2` gap off the equality
   templates, and plausibly a distance-sensitive lower bound stronger than bare additive `+2`
   near the principal-star template.
4. Promote the new orbit evidence into a theorem-shaped conjecture:
   in the shifted `n = 7` model, the global first-gap families are precisely the full
   distance-`2` shell around the two equality templates.
   The `n = 5` computation shows this should be treated as a higher-dimensional phenomenon, not as
   a statement expected in every odd dimension.
5. Identify what the transported subcube families would have to look like in order to realize the
   two equality templates, and try to rule that out directly.
6. Only then move back into Lean:
   first with a stronger shifted theorem, then with an exclusion theorem for the transported
   family class, then with the upgraded endpoint.

## Recommended Formal Targets

The exact Lean names can wait, but the mathematical targets should look like:

- shifted equality classification for the two-layer boundary theorem;
- shifted strict gap off equality templates;
- transported-family exclusion from the equality templates;
- final stronger arithmetic endpoint
  \[
  \binom{n}{\lfloor n/2\rfloor} + g(n) \le N.
  \]

## Interpretation

The current exact plan remains essential. But from this point onward, its role is:

- give the correct geometric object \(F\),
- identify the equality templates,
- and provide the closure graph from a stronger boundary theorem to a stronger Erdős #1 lower
  bound.

The genuinely new mathematical step is no longer “prove the middle-binomial theorem.” It is:

\[
\text{prove a positive stability gap beyond the middle-binomial theorem on the transported family class.}
\]
