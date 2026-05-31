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

## References

- [AM'19] I. Alekseev and R. Magdiev, "The Language of Geodesics for the Discrete
   Heisenberg Group." [Local PDF](../refs/1905.03226v1.pdf),
   [arXiv:1905.03226](https://arxiv.org/abs/1905.03226).
- [VM'17] A. M. Vershik and A. V. Malyutin, "Infinite Geodesics in the Discrete
   Heisenberg Group." [Local PDF](../refs/znsl6495.pdf),
   [MathNet](https://www.mathnet.ru/eng/znsl6495).
- [Bro'16] J. M. Brönnimann, "Geodesic Growth of Groups."
   [Local PDF](../refs/bronnimann_geodesic_growth_of_groups_2016.pdf),
   [University of Neuchatel record](https://libra.unine.ch/entities/publication/26df3766-1b6c-47db-8f96-d75aa5cbd5db).
- [BBES'12] M. R. Bridson, J. Burillo, M. Elder, and Z. Šunić, "On Groups
   Whose Geodesic Growth Is Polynomial."
   [Local PDF](../refs/bridson_burillo_elder_sunic_polynomial_geodesic_growth_2012.pdf),
   [author PDF](https://web.mat.upc.edu/pep.burillo/Papers/geogro.pdf).
- [DS'19] M. Duchin and M. Shapiro, "The Heisenberg Group Is Pan-Rational."
   [Local PDF](../refs/duchin_shapiro_heisenberg_pan_rational_2019.pdf),
   [arXiv:1411.4201](https://arxiv.org/abs/1411.4201).
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
