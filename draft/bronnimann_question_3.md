# Brönnimann Question 3 via Bodart's Virtually Engel Group

Brönnimann asks in Appendix A, Question 3 of [Bro'16]:

> Is there a group with solvable word problem and irrational geodesic growth?

For the current repository direction, the main witness is Bodart's virtually
Engel group from [Bod'25]. The key asymptotic statement is:

> The geodesic growth of the group
> $vE$ with generating set $S = \{a^{\pm1},t\}$
> satisfies $\gamma_{\mathrm{geo}}(n) \asymp \exp(n^{3/5}\log n)$.

This is enough to answer the broad existence question positively, once combined
with the standard background fact that finitely generated virtually nilpotent
groups have solvable word problem.

## Formalization Target

The current Lean target is statement-level and witness-oriented:

1. define a computability-theoretic notion of solvable word problem for a
   presented group;
2. define rational / irrational geodesic growth via eventual linear
   recurrences;
3. record Bodart's virtually Engel presentation and imported witness facts;
4. prove the abstract implication that any such witness yields a positive answer to Question 3.

This is now implemented by:

- `Groups.GeodesicGrowth`
- `Groups.VirtuallyEngelGroup`
- `Groups.BronnimannQuestion3`

## Current Lean Surface

The main formal statement is:

```lean
BronnimannQuestion3.PositiveAnswer
```

The fully local witness-packaging theorem is:

```lean
BronnimannQuestion3.positive_answer_of_witness
```

The imported witness facts currently exposed in Lean are:

```lean
VirtuallyEngel.solvableWordProblem
VirtuallyEngel.irrationalGeodesicGrowth
```

The theorem checked in the base-axiom verifier is conditional because
`positive_answer_of_witness` takes these properties as hypotheses. Hypotheses are not counted as
new axioms by the checker. No unconditional Bodart-based theorem is claimed at present.

## Next Steps

The main mathematical debt is to replace imported literature axioms by internal
proof layers. The most natural sequence is:

1. formalize the implication from Bodart's asymptotic estimate to
   non-rationality of the geodesic-growth series;
2. formalize that finitely generated virtually nilpotent groups have solvable
   word problem;
3. instantiate `BronnimannQuestion3.positive_answer_of_witness` from those derived witness facts.

## References

- [Bod'25] C. Bodart, "Intermediate Geodesic Growth in Virtually Nilpotent
  Groups." [Local PDF](../refs/bodart_intermediate_geodesic_growth_virtually_nilpotent_2025.pdf),
  [arXiv:2306.10381](https://arxiv.org/abs/2306.10381).
- [Bro'16] J. M. Brönnimann, "Geodesic Growth of Groups."
  [Local PDF](../refs/bronnimann_geodesic_growth_of_groups_2016.pdf),
  [University of Neuchatel record](https://libra.unine.ch/entities/publication/26df3766-1b6c-47db-8f96-d75aa5cbd5db).
