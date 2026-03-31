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

## Current Shifted Shell-Ladder Profile

The shifted gap picture is now refined beyond the first shell.

- shifted `n = 5`: the full template-shell profile is now exact:
  - distance `0`: gap `0`
  - distance `2`: every shifted pair has gap `2`
  - distance `4`: every shifted pair has gap `3`
  - distance `6`: shell gaps range from `2` to `4`
  - distance `8`: every shifted pair has gap `5`
- shifted `n = 7`: the low shells are now exact:
  - distance `2`: all `5` shell orbits have gap `3`
  - distance `4`: all `10` shell orbits have gap `5`
  - distance `6`: the `40` shell orbits have gaps ranging from `6` to `7`

So the shifted higher-dimensional picture is sharper again:

\[
\text{the first two nontrivial shells in shifted } n = 7 \text{ are rigid,}
\]
\[
\text{but shell rigidity already breaks by distance } 6.
\]

The full shifted `n = 7` shell-profile enumeration is now computationally saturated with the
current tool, so the next step has to be theorem-level work, not deeper brute-force shell scans.

## Current Template-Attribution Split

The new shell-attribution diagnostic shows that the low shifted shells are not symmetric between
the two equality templates.

- shifted `n = 5`:
  - distance `2`: `1` shell pair is nearest the full-lower template, `4` are nearest the
    principal-star template;
  - distance `4`: `1` shell pair is nearest the full-lower template, `7` are nearest the
    principal-star template;
  - distance `6` and `8` already introduce tied families, so the low-shell picture is not cleanly
    template-separated.
- shifted `n = 7`:
  - distance `2`: `1` shell pair is nearest the full-lower template, `4` are nearest the
    principal-star template;
  - distance `4`: `1` shell pair is nearest the full-lower template, `9` are nearest the
    principal-star template;
  - distance `6`: `4` shell pairs are nearest the full-lower template, `36` are nearest the
    principal-star template.

So the first shifted shells are now known to be heavily concentrated near the principal-star
template, not the full-lower template.

\[
\text{near-equality in the shifted world is dominated by the principal-star side.}
\]

That changes the exclusion problem: a future transported-family theorem does not just need to
avoid both equality templates abstractly; it likely needs to rule out the principal-star
neighborhood first, because that is where almost all of the low-shell shifted near-extremizers
live in the first nontrivial tested dimension.

The full shifted shell-attribution profile is now exact in `n = 7`, and it strengthens that
picture substantially:

- every positive shell from distance `2` through distance `18` splits only into
  `full-lower` and `principal-star` classes;
- tied classes do not appear until distance `20`;
- in every positive shell, the principal-star class is much larger than the full-lower class.

For example:

- distance `8`: `9` full-lower pairs versus `98` principal-star pairs;
- distance `12`: `25` full-lower pairs versus `398` principal-star pairs;
- distance `18`: `100` full-lower pairs versus `970` principal-star pairs.

So the principal-star side does not merely dominate the first few shells; it dominates the entire
observed pre-tied regime in shifted `n = 7`.

\[
\text{the full-lower template contributes a thin exceptional strand,}
\]
\[
\text{while the principal-star template governs the bulk of shifted near-equality.}
\]

There is now a second, more surprising, structural refinement:

- in shifted `n = 7`, for every shell distance from `0` through `18`,
  the `full-lower` and `principal-star` strands have exactly the same shell margin envelope;
- explicitly, at each such shell distance, both strands have the same minimum and maximum values
  of \(|\partial^+F|-|C|\);
- the asymmetry is therefore only in multiplicity, not in the shell gap interval itself.

For example:

- distance `8`: both strands have gap interval `[5,9]`;
- distance `12`: both strands have gap interval `[8,12]`;
- distance `18`: both strands have gap interval `[7,15]`.

This exact envelope symmetry breaks only when tied classes first appear, starting at distance `20`.

\[
\text{before tied shells appear, the two template strands have the same gap envelope,}
\]
\[
\text{but radically different multiplicities.}
\]

So the current stronger route is sharper in two different senses:

- the principal-star strand dominates the count of near-extremizers;
- but the shell-by-shell gap envelope appears to depend only on distance, not on which template
  strand one is on, throughout the observed pre-tied regime.

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

There is now also a sharper computational bottleneck diagnosis behind this shell program:

- a new local shell probe, restricted to shifted pairs within bounded template distance, exactly
  reproduces the known `n = 7` low-shell strand data through distance `6`;
- but the same probe still does not return quickly at `n = 9`, even for distance bound `4`,
  because it still enumerates *all* shifted middle-rank families before filtering to the local
  shell.

So the next computational step is no longer “add another shell statistic,” but:

\[
\text{build a genuinely template-local shifted generator, not a filtered global enumerator.}
\]

That is now the cleanest route to testing whether the shell-envelope phenomenon persists in
dimension `9` and beyond.

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

The current shell-envelope evidence suggests that this stability theorem may itself split into two
subtheorems:

- a distance-only shell-envelope theorem, controlling the possible gap interval as a function of
  distance from the equality-template set;
- a template-attribution theorem, controlling which of the two equality strands dominates the
  count of near-extremizers.

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
5. Promote the new shell-ladder evidence into a stronger stability conjecture:
   in the shifted `n = 7` model, the distance-`4` shell is also rigid with exact gap `5`,
   while the distance-`6` shell already splits with gaps `6` and `7`.
   So a realistic next theorem is not “every shell is rigid”, but “the first few shells admit
   exact gap formulas before higher-shell splitting begins”.
6. Promote the new attribution split into a theorem-shaped conjecture:
   in the shifted odd two-layer problem, the principal-star template should control most of the
   low-shell near-extremizers, while the full-lower template contributes only a thin exceptional
   strand.
   If true, the transported-family exclusion problem should focus first on ruling out the
   principal-star neighborhood.
7. Strengthen the conjecture using the full shifted `n = 7` attribution profile:
   before tied shells appear, every positive shell should decompose into a thin full-lower strand
   and a dominant principal-star bulk.
   A realistic first theorem is therefore not symmetric template stability, but
   principal-star-dominated stability with an explicit exceptional full-lower family.
8. Add the new shell-envelope symmetry conjecture:
   in the shifted odd two-layer problem, throughout the pre-tied regime, the full-lower and
   principal-star strands should share the same shell gap interval, even though their multiplicities
   are very different.
   If true, the right theorem may split into:
   - a distance-only shell envelope theorem;
   - and a separate multiplicity / template-attribution theorem.
9. Identify what the transported subcube families would have to look like in order to realize the
   two equality templates, and try to rule that out directly.
10. Only then move back into Lean:
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
