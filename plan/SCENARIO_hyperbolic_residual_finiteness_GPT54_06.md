# Scenario: Hyperbolic residual finiteness, GPT54_06

This note audits the random / graded-small-cancellation route to a counterexample to

```text
Every word-hyperbolic group is residually finite.
```

The target would be a **single finitely presented word-hyperbolic group** together with a proof that some nontrivial element dies in every finite quotient, or equivalently that the group has no nontrivial finite quotients. The audited question is whether the literature on random groups at density

```text
1/3 < d < 1/2
```

or on graded / graphical small cancellation already provides such an example.

## 1. Random groups in the density model: what is actually proved

### 1.1 Finite presentation

A random group in the classical Gromov density model is, by definition, given by a finite presentation of fixed relator length `ℓ` and about `(2m-1)^{dℓ}` relators. So for each chosen random presentation one certainly gets a finitely presented group.

Thus item (1) on the prompt checklist is satisfied **for each sampled presentation**.

### 1.2 Infinitude and word-hyperbolicity below density `1/2`

Ollivier’s survey *A January 2005 invitation to random groups* states the sharp phase transition:

```text
If d < 1/2, then with overwhelming probability G is infinite, hyperbolic,
torsion-free, of geometric dimension 2.
If d > 1/2, then with overwhelming probability G is trivial (or Z/2Z if ℓ is even).
```

In the extracted survey text this appears as Theorem 11 / the density `1/2` phase transition. So for `1/3 < d < 1/2`, infinitude and word-hyperbolicity are established with overwhelming probability.

Ashcroft’s paper on random quotients of hyperbolic groups also summarizes the same fact for the classical density model: at density `d < 1/2`, random groups are infinite, non-elementary hyperbolic, and torsion-free.

So item (2) is available in the random-group route.

### 1.3 Property `(T)` above density `1/3`

Kotowski–Kotowski, *Random groups and property (T): Żuk’s theorem revisited*, prove that random groups in the Gromov density model satisfy property `(T)` with overwhelming probability for `d > 1/3`.

Their introduction states explicitly that, combined with Gromov’s hyperbolicity theorem, this yields many infinite hyperbolic groups with property `(T)` for densities between `1/3` and `1/2`.

Ollivier’s survey also states the same threshold in Theorem 27, and Ashcroft extends the property-`(T)` theorem to random quotients of arbitrary non-elementary hyperbolic groups at density `>1/3`.

Therefore, for

```text
1/3 < d < 1/2,
```

the combination

```text
finite presentation + infinitude + hyperbolicity + property (T)
```

is indeed proved with overwhelming probability.

## 2. The missing step: no theorem gives absence of all finite quotients for density-model random groups

The crucial question is not hyperbolicity or property `(T)`, but the universal finite-quotient statement.

The audited primary sources do **not** prove that a random group in the classical density model at `1/3 < d < 1/2` has no nontrivial finite quotients.

What Ollivier’s survey says is much weaker and points in a different direction:

- for any **fixed** finite group `H`, it is easy to show that a random group with sufficiently long defining relators will not map onto `H`;
- but one would have to **exchange the limits** to deduce absence of **all** finite quotients, and the survey presents this only as a heuristic/open direction, not a theorem.

The survey’s exact discussion in §IV.e says:

```text
For any finite group H fixed in advance, it is easy to show that a random group
with large enough defining relators will not map onto H. Exchanging the limits
would provide hyperbolic groups without finite quotients.
```

This is the decisive obstruction.

So the literature does support:

```text
for each fixed finite H,   P(random group surjects onto H) → 0.
```

But it does **not** support:

```text
P(random group has some nontrivial finite quotient) → 0.
```

Those are very different statements, because the second must control a countable union over all finite groups whose size grows with `ℓ`.

Hence item (4) in the prompt checklist fails exactly here: the primary-source theorem rules out quotients of any preassigned bounded size, but not all finite quotients simultaneously.

## 3. Probabilistic existence versus an explicit deterministic group

Even if one had a correct theorem of the form

```text
with overwhelming probability, a density-model random group at 1/3<d<1/2
is infinite hyperbolic and has no nontrivial finite quotients,
```

one would still need to extract either:

- a rigorous existence theorem for some deterministic finite presentation; or
- an explicit presentation itself.

The audited literature does not provide such a theorem here, because the no-finite-quotients statement itself is missing.

Thus item (5) also remains unresolved: there is no explicit deterministic finitely presented hyperbolic group from the density model in the audited sources with a proved universal finite-quotient obstruction.

## 4. The all-length / temperature model does kill finite quotients, but loses finite presentation and hyperbolicity of a single group

Ollivier’s survey discusses Gromov’s “temperature model” (also called the every-length / all-length density model). This is the place where a universal no-finite-quotients theorem **is** stated.

For densities `d >= 0`, the model chooses relators independently at every length, so the resulting presentation is almost surely infinite. Ollivier states explicitly:

```text
for any d >= 0, with probability 1 the group G has no finite quotient.
```

The proof idea is that for any finite quotient `π : G → H`, random relators almost surely hit every coset of `ker π`, forcing `H` to be trivial.

However, the same discussion immediately records the obstruction relevant here:

- the presentation is infinite for `d >= 0`;
- if the conjectural picture holds, the group is expected only to be a **direct limit** of infinite hyperbolic groups;
- Ollivier explicitly says that at `d >= 0` the group will admit **no finite presentation**.

The survey states:

```text
At d < 0 ... the presentation for G is finite with probability 1 ... and the group is even hyperbolic.
But at d >= 0 the presentation is infinite, and if the conjecture indeed holds the group
will admit no finite presentation.
```

So the temperature model gives exactly the wrong tradeoff for the present task:

- **yes** to “no finite quotients”;
- **no** to finite presentation of the resulting group;
- and the expected geometric conclusion is a direct limit of hyperbolic groups, not a single finitely presented word-hyperbolic group.

This is not a counterexample to residual finiteness inside the class of finitely presented hyperbolic groups.

## 5. Low-density cubulation results go in the opposite direction

For completeness, the random-group literature also contains strong positive finiteness results at low density.

Ashcroft summarizes that random groups in the density model are virtually special for `d < 1/6`, citing Ollivier–Wise together with Agol. That means residual finiteness is known in that regime, not failure of residual finiteness.

So the random route splits into two verified regions:

- `d < 1/6`: cubulation / virtual specialness, hence residual finiteness;
- `1/3 < d < 1/2`: hyperbolic and property `(T)`, but no audited theorem excluding all finite quotients.

There is no verified bridge from the latter region to non-residual-finiteness.

## 6. Why the familiar graded-small-cancellation “kill all finite quotients” construction does not preserve the desired conclusion

The standard Olʹshanskii-style strategy for producing groups with no nontrivial finite quotients is inherently **graded** or **iterated**:

1. start from a hyperbolic group;
2. enumerate finite groups or finite quotient data;
3. at stage `n`, add new relators killing maps to the `n`-th finite group or killing a chosen element in all quotient maps of the current stage;
4. continue indefinitely.

This can force the final direct limit to have no nontrivial finite quotients.

But the prompt asks whether this mechanism can be built into a **finite** small-cancellation presentation while retaining word hyperbolicity.

The obstruction is structural.

### 6.1 Enumeration of all finite quotients is an infinite task

To kill **every** finite quotient by diagonalization, one must handle infinitely many targets. The standard construction therefore requires infinitely many rounds of added relations.

A finite presentation can only encode finitely many relators. Without some separate uniform theorem collapsing the infinite family of quotient obstructions to finitely many conditions, a finite presentation cannot simply “enumerate all finite groups and all homomorphisms” by hand.

No such finite-collapse theorem was found in the audited primary sources.

### 6.2 Infinite graded presentations need not define hyperbolic groups

Word-hyperbolicity is a property of a single finitely generated group with a finite generating set whose Cayley graph is δ-hyperbolic. An **inductive limit** of hyperbolic groups need not itself be hyperbolic.

In the graded-small-cancellation constructions, each stage may be hyperbolic, but the final direct limit generally loses the uniform linear isoperimetric control needed for hyperbolicity of the limit group.

Ollivier’s discussion of the temperature model makes exactly this distinction: one may expect a direct limit of infinite hyperbolic groups, but not a finitely presented hyperbolic group. That is the same failure mode relevant to graded diagonal constructions.

Thus one must not confuse:

```text
each finite stage is hyperbolic
```

with

```text
the limit group is word-hyperbolic.
```

They are different claims, and the second is not supplied by the familiar quotient-killing machinery.

### 6.3 Graphical / graded small cancellation can preserve hyperbolicity at each finite stage, not necessarily in the infinite limit

Graphical and small-cancellation methods often prove that a quotient by a **finite** or suitably controlled family of long relators remains hyperbolic. But once one stacks infinitely many stages to kill all finite quotients, the output is usually an infinitely presented monster or a direct limit object.

That is exactly why these constructions are useful for producing exotic finitely generated groups, but do not automatically yield a single finitely presented hyperbolic group with no finite quotients.

## 7. Exact status of the random / small-cancellation route

The audited primary-source picture is therefore:

### What is proved

- In the density model, every sampled random group is finitely presented.
- For `d < 1/2`, random groups are with overwhelming probability infinite and word-hyperbolic.
- For `d > 1/3`, random groups are with overwhelming probability property `(T)`.
- In the all-length / temperature model with `d >= 0`, the resulting random group has no finite quotients with probability 1.

### What is **not** proved in the audited sources

- No primary-source theorem located here proves that classical density-model random groups at `1/3 < d < 1/2` have **no nontrivial finite quotients**.
- The available statement only excludes surjections onto any **fixed** finite group; it does not control all finite groups uniformly.
- No audited theorem converts the temperature-model no-finite-quotients phenomenon into a **finitely presented** hyperbolic group.
- No audited graded-small-cancellation theorem produces a **single finitely presented word-hyperbolic group** with all finite quotients trivial by carrying out the infinite diagonal killing in finitely many relators.

## 8. Strongest exact obstruction

The random route almost gives the desired package but misses the universal quotient step:

```text
finite presentation + hyperbolicity + property (T)    yes,
no nontrivial finite quotients                         not proved.
```

The all-length / graded route almost gives the universal quotient conclusion but loses the geometric finiteness package:

```text
no nontrivial finite quotients                         yes / plausible in limit models,
finite presentation + single hyperbolic group         lost.
```

So the two halves of the desired counterexample occur in different constructions, and the audited literature does not bridge them.

No such counterexample is known; exact obstruction: density-model random groups at `1/3 < d < 1/2` are indeed finitely presented and are w.o.p. infinite word-hyperbolic with property `(T)`, but the audited primary sources only show that surjections to each fixed finite group disappear asymptotically, not that **all** nontrivial finite quotients are absent, while the all-length / graded small-cancellation constructions that do kill every finite quotient use infinitely many relators and yield at best an infinitely presented/direct-limit object rather than a single finitely presented word-hyperbolic group.
