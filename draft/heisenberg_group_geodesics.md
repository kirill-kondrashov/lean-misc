# Geodesics in the Discrete Heisenberg Group

The papers [AM'19] and [VM'17] describe finite and infinite geodesics in the
discrete Heisenberg group

$$
\mathbb{H}(\mathbb{Z}) \cong
\left\langle a, b \mid [[a,b],a] = 1,\ [[a,b],b] = 1 \right\rangle .
$$

The standard two-element generating set is $\{a,b\}$, with geodesic words
written over the alphabet $\{a^{\pm 1}, b^{\pm 1}\}$.

## Rationality of the Geodesic Growth Series

Determine the geodesic growth series of $\mathbb H(\mathbb Z)$ for the standard
generating alphabet $S = \{a,a^{-1},b,b^{-1}\}$. That is, for

$$
\gamma(n) =
\#\{w \in S^\ast \mid |w| = n,\ w \text{ is geodesic}\},
$$

study the generating function

$$
\Gamma_{\mathrm{geo}}(z) = \sum_{n \ge 0} \gamma(n)z^n.
$$

The main question is whether $\Gamma_{\mathrm{geo}}(z)$ is rational; if not,
one can ask whether it is algebraic, D-finite, or transcendental. The description
of geodesic words in [AM'19, Proposition 1.2, Theorem 1.3, Proposition 1.6]
reduces this to a concrete enumeration problem involving prefixes of dead-end
words and minimal-perimeter polyominoes, but it does not by itself give the
generating function.

There is also a related endpoint-counting literature for geodesics in the
standard Heisenberg generators. Vershik-Malyutin [VM'19, Theorem 1] prove an
asymptotic stability result for the number $\dim(g)$ of shortest paths from the
identity to a positive-cone element:

> $\frac{\dim([x,y]^{k+1}y^nx^m)}{\dim([x,y]^ky^nx^m)} \to 1.$

Malyutin [M'23] summarizes the Young-diagram interpretation behind this:

> the number of geodesic paths between two given points is equal to the number
> of restricted partitions

These results concern geodesics with a fixed endpoint, especially in the positive
cone, so they do not directly determine the all-word series
$\Gamma_{\mathrm{geo}}(z)$. They do, however, point to the same restricted
partition and Young-diagram enumeration that one would have to control in a
full solution.

This is the Heisenberg-specific version of a broader formal-geodesic-growth
question raised by Brönnimann [Bro'16, Appendix A, Question 3]:

> Is there a group with solvable Word Problem and irrational geodesic growth?

In the following list of possible sources, Brönnimann includes:

> The Heisenberg group $H_2$.

Some surrounding results clarify what is still open.

For finitely generated nilpotent groups, Bridson-Burillo-Elder-Šunić
[BBES'12, Proposition 12] give the relevant growth-type result:

> Let $G$ be a finitely generated nilpotent group. If $G$ is not virtually
> cyclic, then it has exponential growth with respect to every finite generating
> set.

Thus, for $\mathbb H(\mathbb Z)$, the open issue is not the growth type but the
formal nature of $\Gamma_{\mathrm{geo}}(z)$.

Duchin-Shapiro [DS'19, Theorem 1] prove rationality for ordinary growth:

> The Heisenberg group has rational growth for all generating sets.

This counts group elements rather than all geodesic representatives, so it does
not decide $\Gamma_{\mathrm{geo}}(z)$.

For virtually abelian groups, Bishop [B'21, Theorem 6.5] proves:

> Let $G$ be a virtually abelian group with a finite (weighted monoid)
> generating set $S$. Then either the geodesic growth with respect to $S$ is
> polynomial with rational geodesic growth series; or the geodesic growth with
> respect to $S$ is exponential with holonomic geodesic growth series.

This removes one of Brönnimann's proposed sources of irrational examples.

Bishop-Elder [BE'22, Theorem 1] construct a virtually Heisenberg group with
polynomial geodesic growth:

> The geodesic growth function of $vH$ with respect to
> $S = \{a,a^{-1},t\}$ is bounded from above by a polynomial of degree 8.

The same paper [BE'22, Section 2, Question 2 and the following paragraph]
reports experimental evidence suggesting that this geodesic growth sequence is
not rational.

Bodart [Bod'25, Theorem 1] gives a criterion for virtually nilpotent groups:

> If no two elements of $A(S)$ lie on a common facet of $P(S)$, then the
> geodesic growth is subexponential. [...] Otherwise the geodesic growth is
> exponential.

Bodart [Bod'25, Theorem 4] then constructs a virtually Engel example:

> The geodesic growth of the group $vE$ with generating set $S = \{a^{\pm1},t\}$
> satisfies $\gamma_{\mathrm{geo}}(n) \asymp \exp(n^{3/5}\log n)$.

This settles the broad search for a non-rational geodesic-growth example with
solvable word problem, but it leaves the standard discrete Heisenberg series
above as a separate and natural enumeration problem.

## Formal Question

Let

$$
\operatorname{Geo}_S =
\{w \in S^\ast \mid |w| = d_S(1,\overline w)\}
$$

be the full geodesic language of $\mathbb H(\mathbb Z)$, where
$S = \{a,a^{-1},b,b^{-1}\}$ and $\overline w$ denotes the element represented by
$w$. Let

$$
\operatorname{DE}_S =
\{w \in \operatorname{Geo}_S \mid
   \overline w = [a,b]^k \text{ for some } k \in \mathbb Z \setminus \{0\}\}
$$

be the language of dead-end words. Combining [AM'19, Proposition 1.2] with
[AM'19, Theorem 1.3] gives the exact language identity

$$
\operatorname{Geo}_S = \operatorname{Pref}(\operatorname{DE}_S),
$$

where $\operatorname{Pref}(L)$ denotes the set of finite prefixes of words in
$L$. By [AM'19, Proposition 1.6], $\operatorname{DE}_S$ is equivalently the
language read on oriented boundaries of minimal-perimeter polyominoes whose
boundary contains the origin. Thus the concrete formal question is:

$$
\text{Is }
\Gamma_{\mathrm{geo}}(z)
=
\sum_{n \ge 0}
\#\bigl(\operatorname{Pref}(\operatorname{DE}_S) \cap S^n\bigr)z^n
\text{ a rational function in } z?
$$

Equivalently, does the sequence

$$
\gamma(n)=\#\bigl(\operatorname{Pref}(\operatorname{DE}_S) \cap S^n\bigr)
$$

satisfy an eventual linear recurrence with constant coefficients?

## Literature Status and Connections

A literature search on May 31, 2026 did not locate a citable source that states
or solves the exact rationality question above in the prefix-counting form
$\operatorname{Geo}_S=\operatorname{Pref}(\operatorname{DE}_S)$. The closest
source is Alekseev-Magdiev [AM'19]. They explicitly quote Brönnimann's
irrational-geodesic-growth question in [AM'19, Question 1.1], point to
$\mathbb H(\mathbb Z)$ as the expected test case in the following paragraph, and
then prove the finite-language classification that makes the formal question
above possible. Thus the question is not new as motivation, but the exact
generating-function formulation appears to be a precise consequence of
[AM'19, Proposition 1.2, Theorem 1.3, Proposition 1.6] rather than a separately
stated theorem or problem in that paper.

The first connection is to Brönnimann's broad problem [Bro'16, Appendix A,
Question 3]. A negative answer to the formal question would show that the
standard discrete Heisenberg group has irrational geodesic growth, giving an
especially natural nilpotent example with solvable word problem. A positive
answer would show that the Alekseev-Magdiev polyomino-prefix description still
has enough finite recurrence to produce a rational counting series.

The second connection is to the contrast between ordinary growth and geodesic
growth. Duchin-Shapiro [DS'19, Theorem 1] prove rationality of ordinary growth
for all finite generating sets of $\mathbb H(\mathbb Z)$, while their discussion of
standard generators recalls that Shapiro's work gives no regular geodesic
language in the standard metric [DS'19, Section 3.1]. The present question asks
whether the full geodesic language can nevertheless have a rational counting
series.

The third connection is to the known boundary of rationality results. Bishop
[B'21, Theorem 6.5] settles the virtually abelian case, so the standard
Heisenberg group is the next basic nilpotent test case outside that theorem.
Bishop-Elder [BE'22, Theorem 1 and Section 2] then show that a virtually
Heisenberg group can have polynomial geodesic growth and record experimental
evidence suggesting non-rationality of its geodesic growth sequence. Bodart
[Bod'25, Theorem 4] gives an intermediate-growth virtually nilpotent example,
so the broad existence problem for non-rational geodesic growth is no longer the
main issue. What remains here is the sharper two-step nilpotent enumeration
problem for the standard discrete Heisenberg generators.

## Strategy Hypotheses

The most optimistic strategy hypothesis is a finite polyhedral decomposition:
after choosing finitely many boundary types, prefix positions, and symmetries, the
admissible minimal-perimeter polyomino data can be encoded by integer parameters
satisfying only finitely many linear equalities, inequalities, and congruences. If
this decomposition can be made injective on prefixes, or corrected by a finite
inclusion-exclusion, then the same kind of rational-polyhedral enumeration used in
ordinary Heisenberg growth would suggest rationality of
$\Gamma_{\mathrm{geo}}(z)$.

A possible obstruction is that the prefix count may retain genuinely
two-dimensional restricted-partition data. The endpoint-counting results
[VM'19, Theorem 1] and [M'23] show that fixed-endpoint geodesics already involve
Young diagrams in rectangles. If those restricted-partition contributions survive
in the all-prefix count in a way that is not reducible to finitely many polyhedral
families, one should instead expect non-rationality, perhaps detectable by showing
that $\gamma(n)$ cannot satisfy an eventual linear recurrence.

A practical intermediate hypothesis is to first compute a canonical, nonredundant
prefix parametrization. In this form, two questions become testable: whether the
parameter set is eventually semilinear, and whether the resulting sequence
$\gamma(n)$ has asymptotics compatible with a rational generating function. A
negative answer to either question would give a concrete route toward proving that
the standard Heisenberg geodesic growth series is not rational.

## References

- [AM'19] I. Alekseev and R. Magdiev, "The Language of Geodesics for the Discrete
   Heisenberg Group." [Local PDF](../refs/1905.03226v1.pdf),
   [arXiv:1905.03226](https://arxiv.org/abs/1905.03226).
- [B'21] A. Bishop, "Geodesic Growth in Virtually Abelian Groups."
   [Local PDF](../refs/bishop_geodesic_growth_virtually_abelian_2019.pdf),
   [arXiv:1908.07294](https://arxiv.org/abs/1908.07294).
- [BE'22] A. Bishop and M. Elder, "A Virtually 2-Step Nilpotent Group with
   Polynomial Geodesic Growth."
   [Local PDF](../refs/bishop_elder_virtually_2_step_nilpotent_polynomial_geodesic_growth_2022.pdf),
   [journal PDF](https://admjournal.luguniv.edu.ua/index.php/adm/article/viewFile/1667/pdf).
- [Bod'25] C. Bodart, "Intermediate Geodesic Growth in Virtually Nilpotent
   Groups."
   [Local PDF](../refs/bodart_intermediate_geodesic_growth_virtually_nilpotent_2025.pdf),
   [arXiv:2306.10381](https://arxiv.org/abs/2306.10381),
   [EMS](https://ems.press/journals/ggd/articles/14298929).
- [BBES'12] M. R. Bridson, J. Burillo, M. Elder, and Z. Šunić, "On Groups
   Whose Geodesic Growth Is Polynomial."
   [Local PDF](../refs/bridson_burillo_elder_sunic_polynomial_geodesic_growth_2012.pdf),
   [author PDF](https://web.mat.upc.edu/pep.burillo/Papers/geogro.pdf).
- [Bro'16] J. M. Brönnimann, "Geodesic Growth of Groups."
   [Local PDF](../refs/bronnimann_geodesic_growth_of_groups_2016.pdf),
   [University of Neuchatel record](https://libra.unine.ch/entities/publication/26df3766-1b6c-47db-8f96-d75aa5cbd5db).
- [DS'19] M. Duchin and M. Shapiro, "The Heisenberg Group Is Pan-Rational."
   [Local PDF](../refs/duchin_shapiro_heisenberg_pan_rational_2019.pdf),
   [arXiv:1411.4201](https://arxiv.org/abs/1411.4201).
- [M'23] A. Malyutin, "The (Discrete) Heisenberg Group and (Restricted)
   Young's Lattices."
   [Local PDF](../refs/malyutin_heisenberg_young_lattices_2023.pdf).
- [VM'17] A. M. Vershik and A. V. Malyutin, "Infinite Geodesics in the Discrete
   Heisenberg Group." [Local PDF](../refs/znsl6495.pdf),
   [MathNet](https://www.mathnet.ru/eng/znsl6495).
- [VM'19] A. M. Vershik and A. V. Malyutin, "Asymptotics of the Number of
   Geodesics in the Discrete Heisenberg Group."
   [Local PDF](../refs/vershik_malyutin_asymptotic_geodesics_heisenberg_2018.pdf).
