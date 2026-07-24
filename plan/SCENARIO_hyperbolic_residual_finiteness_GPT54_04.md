# Scenario: Hyperbolic residual finiteness, GPT54_04

This note audits one concrete candidate from Caprace–Conder–Kaluba–Witzel (CCKW) for the hoped-for Agol–Groves–Manning witness

```text
G hyperbolic,
H < G quasiconvex,
g ∉ H,
and for every finite quotient φ : G → F,
φ(g) ∈ φ(H).
```

I chose the explicit KMS group

```text
G = 𝒢_{HB_2^{(2)}}(7)
```

because CCKW prove simultaneously:

- an exact finite presentation;
- infinitude;
- word-hyperbolicity;
- property-(T);
- existence of many finite simple quotients (indeed arbitrarily large rank).

That makes it an especially good stress test for the hoped-for profinite-nonseparability route.

## 1. Exact finite presentation

From CCKW, Theorem 1.2 / Theorem `\ref{thm:KMS:intro}`, for any odd prime `p`:

```text
𝒢_{HB_2^{(2)}}(p)
= < a,b,c |
    a^p, b^p, c^p,
    [a,b,a], [a,b,b],
    [c,b,c], [c,b,b,c], [c,b,b,b],
    [c,a,c], [c,a,a,c], [c,a,a,a] >.
```

Therefore the audited candidate is

```text
G = 𝒢_{HB_2^{(2)}}(7)
  = < a,b,c |
      a^7, b^7, c^7,
      [a,b,a], [a,b,b],
      [c,b,c], [c,b,b,c], [c,b,b,b],
      [c,a,c], [c,a,a,c], [c,a,a,a] >.
```

Here `[x,y,z]` means the left-normed commutator `[[x,y],z]`, etc., as in the paper.

## 2. Infinitude and property-(T)

CCKW prove in Theorem `\ref{thm:KMS:intro}` that for every odd prime `p`, the groups

```text
𝒢_{HC_2^{(1)}}(p), 𝒢_{HB_2^{(2)}}(p), Ẑ𝒢_{HBC_2^{(3)}}(p)
```

are infinite hyperbolic, and for `p >= 7` the first two have property `(T)`.

More structurally, in Theorem `\ref{label:thm:KMS}` they show for every KMS group of half-girth type `(r0,r1,r2)`:

- the group is infinite;
- it is hyperbolic when `1/r0 + 1/r1 + 1/r2 < 1`;
- for type `(3,4,4)` it has property `(T)` for all `p >= 7`.

Our group `𝒢_{HB_2^{(2)}}(7)` has type `(3,4,4)`, so

```text
1/3 + 1/4 + 1/4 = 5/6 < 1,
```

hence it is infinite, word-hyperbolic, and has property `(T)`.

## 3. Word-hyperbolicity

This is proved unconditionally in CCKW via the geometry of generalized triangle groups. The relevant chain is:

- the KMS group is the fundamental group of a nonpositively curved `p`-fold triangle of finite groups;
- its half-girth type here is `(3,4,4)`;
- by Theorem `\ref{label:thm:KMS}`, any KMS group with `1/r0+1/r1+1/r2<1` is hyperbolic.

So `G` is a bona fide word-hyperbolic finitely presented group.

## 4. Is `G` already known virtually special or otherwise residually finite?

This is exactly where the candidate stops being usable as a witness.

What CCKW prove positively is much stronger than mere existence of some finite quotient: by Theorem `\ref{thm:KMS:intro:2}`, for every odd prime `p`, the group `𝒢_{HB_2^{(2)}}(p)` has finite simple quotients of arbitrarily large rank.

So the ambient group is emphatically **not** a "finite-quotient desert" candidate.

More importantly, CCKW show in Section 7.3 that every hyperbolic KMS group over `F_p` surjects onto

```text
𝒢_{Ã_2}(p),
```

and Corollary `\ref{cor:SL(3,q)-quotients}` states that for every `q=p^e` with `e>=3`, each of the six hyperbolic KMS groups over `F_p` has a quotient `SL_3(F_q)` and an infinite pro-`p` completion. In particular, our `G` has infinitely many finite quotients of Lie type.

This does **not** prove residual finiteness of `G`, and I found no theorem in CCKW proving that `G` is virtually special or residually finite. But it does show that any hoped-for universal obstruction

```text
for every finite quotient φ : G → F, φ(g) ∈ φ(H)
```

cannot come from a paucity of finite quotients. One would need a very specific subgroup-pair theorem, not a quotient-existence theorem.

So the correct status is:

- not known here to be virtually special;
- not known here to be residually finite;
- but known to have abundant finite simple quotients, making a universal profinite-nonseparability argument highly nontrivial.

## 5. Explicit subgroup `H`

A natural explicit subgroup is

```text
H = <a,b>.
```

By construction of the KMS triangle of groups, the rank-2 vertex subgroup on `a,b` is the finite unipotent group `𝒰_3(7)`. CCKW encode this by the relations

```text
a^7, b^7, [a,b,a], [a,b,b],
```

and identify the relevant rank-2 vertex groups with `𝒰_3(p)` or `𝒰_4(p)` depending on the edge type. For `HB_2^{(2)}`, the pair `<a,b>` is one of the `𝒰_3(7)` vertex groups.

Hence `H` is explicit and finite.

## 6. Genuine quasiconvexity proof for `H`

Yes: since `H` is finite, it is quasiconvex in every word-hyperbolic group.

So for this audited candidate we may take

```text
H = <a,b> ≅ 𝒰_3(7),
```

and quasiconvexity is immediate.

## 7. Explicit proof that `g ∉ H`

The most obvious choice is `g = c`.

To prove `c ∉ H`, it is enough to use the canonical action of the generalized triangle group on its Bass–Serre/complex-of-groups universal cover. Vertex groups embed in the fundamental group, and the three designated rank-2 vertex groups are distinct finite local groups. The subgroup `<a,b>` is one vertex group, while `c` belongs to the other two designated vertex groups `<b,c>` and `<c,a>` but is not an element of `<a,b>`.

Equivalently: in the triangle-of-groups normal form, elements of the local group `<a,b>` are represented by words in `a,b` alone; the generator `c` is not in that local subgroup. Since CCKW's presentation is the fundamental group of that triangle of groups, the local injections are faithful, so `c ∉ <a,b>`.

Thus

```text
g = c,
H = <a,b>,
g ∉ H.
```

## 8. All-finite-quotient proof of profinite nonseparability

This is where the route fails completely.

To obtain the desired witness we would need a theorem of the form

```text
for every finite quotient φ : G → F,
φ(c) ∈ φ(<a,b>).
```

I found no such theorem in CCKW, and in fact the available positive quotient results point the other way:

- `G` has many nontrivial finite simple quotients;
- indeed it has quotients `SL_3(F_{7^e})` for all `e>=3`.

Those facts do not by themselves separate `c` from `H`, but they show that universal inclusion of `φ(c)` in `φ(H)` would require a very rigid subgroup-image statement across all those finite quotients.

No such theorem is provided in the source, and no replacement argument appears available from the audited literature.

Worse, there is not even a good candidate mechanism presently visible:

- taking `H` finite makes quasiconvexity easy, but then one usually expects many finite quotients to separate `c` from `H`, not the reverse;
- taking a more sophisticated infinite quasiconvex subgroup would require a new independent quasiconvexity proof;
- the CCKW representation-variety machinery is explicitly framed as a reformulation connected to the general residual-finiteness problem, not as a solved subgroup-separability theorem for these groups.

So there is **no universal finite-quotient proof** here.

## Strongest exact obstruction

For the explicit hyperbolic property-(T) candidate

```text
G = 𝒢_{HB_2^{(2)}}(7),
H = <a,b>,
g = c,
```

items (1)–(3), (5), (6), (7) can be certified:

- exact presentation: yes;
- infinitude/property-(T): yes;
- word-hyperbolicity: yes;
- explicit subgroup: yes;
- quasiconvexity: yes, because `H` is finite;
- explicit nonmembership `g ∉ H`: yes.

But item (8) is entirely missing:

```text
there is no theorem proving that c lies in the profinite closure of <a,b>.
```

In fact the audited paper proves that `G` has plentiful finite simple quotients, including `SL_3(F_{7^e})` for all `e>=3)`, so any such universal statement would have to be a subtle, quotient-by-quotient subgroup-image theorem not presently available.

## Strongest genuine next step

The best next theorem to aim for is not more bounded finite-quotient search. It is a structural statement such as:

```text
For one explicit hyperbolic KMS group G = 𝒢_{HB_2^{(2)}}(p),
classify the images of the three distinguished vertex groups
<a,b>, <b,c>, <c,a>
in every finite quotient of G.
```

A usable advance would be any proved statement of the form:

```text
in every finite quotient of G,
the image of one distinguished generator lies in the image of a specified vertex group,
or else all finite quotients factor through a controlled family.
```

Without such a theorem, finite computations are only evidence.

No unconditional witness; precise obstruction: for the explicit infinite hyperbolic property-(T) generalized triangle group `G = 𝒢_{HB_2^{(2)}}(7)`, one can take the explicit quasiconvex subgroup `H = <a,b>` and `g = c` with `g ∉ H`, but there is no theorem proving the required universal statement `φ(g) ∈ φ(H)` for every finite quotient, and the audited source instead proves that `G` has abundant finite simple quotients (indeed quotients `SL_3(F_{7^e})` for all `e >= 3`), so the profinite nonseparability step remains completely open.
