# Notes: `k = 3` Explicit `1/8` Source Audit (2026-03-08)

## Objective

Decide whether the explicit post-Behrend target

```math
r_3(N)=O\!\left(N\exp\!\bigl(-c(\log(N+2))^{1/8}\bigr)\right)
```

is currently backed by an audited published source, or only by source-motivated remarks about an
omitted optimization.

## Primary Sources Checked

1. Bloom--Sisask, "An improvement to the Kelley--Meka bounds on three-term arithmetic
   progressions" (`arXiv:2309.02353`)
   - abstract page: https://arxiv.org/abs/2309.02353
   - HTML rendering checked through ar5iv: https://ar5iv.org/html/2309.02353
2. Kelley--Meka, "Strong bounds for 3-progressions" (`arXiv:2302.05537`)
   - abstract page: https://arxiv.org/abs/2302.05537
3. Bloom--Sisask, "Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions"
   (`arXiv:2007.03528`)
   - abstract page: https://arxiv.org/abs/2007.03528

## Findings

### A. Published theorem level visible in the audited sources

- Bloom--Sisask (`arXiv:2309.02353`) states an upper bound with exponent `1/9`, not `1/8`.
- Kelley--Meka (`arXiv:2302.05537`) gives a theorem of the shape

  ```math
  r_3(N)\le N\exp\!\bigl(-c(\log N)^\beta\bigr)
  ```

  for some positive `\beta`; the currently extracted repository import remains the explicitly
  source-backed `\beta = 1/12` layer.
- Bloom--Sisask (`arXiv:2007.03528`) is weaker still, on a polylogarithmic scale.

### B. What the `1/8` evidence actually says

The Bloom--Sisask 2023 note does contain evidence that the `1/9` exponent is not the end of the
present architecture. In the ar5iv HTML rendering:

- near line 17 it states that a more elaborate version of one lemma permits a further exponent
  improvement;
- near lines 118-119 it says that this optimization is omitted because it would require a lengthy
  technical detour.

This is evidence for a plausible omitted optimization, not a displayed theorem statement proving
the `1/8` bound.

## Verdict

```text
No audited published source was found that states the explicit `1/8` theorem as a proved result.
The current evidence supports treating `1/8` as a conjectural/import-only target motivated by
source remarks, not as a source-backed theorem layer already available to this repository.
```

## Repository Consequence

1. `LiteratureK3OneEighthSourceAssumptions` should be read as optional conjectural scaffolding,
   not as an instantiated source-backed import surface.
2. The `1/8` positive route is therefore not the primary active theorem program.
3. The primary active follow-up should pivot to the negative/bottleneck route recorded in
   `NOTES_problem142_k3_negative_bottleneck_target_2026-03-08.md`.
