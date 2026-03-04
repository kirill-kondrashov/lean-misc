# Plan: Erdős Problem #142 (`r_k(N)` asymptotic formula)

## Problem statement

Let `r_k(N)` be the largest cardinality of a subset of `{1, ..., N}` with no non-trivial
`k`-term arithmetic progression. The target asks for an asymptotic formula for `r_k(N)`.

In this repository, the main statement is:

- `ErdosProblems.erdos_problem_142`

## Reality check (as of March 4, 2026)

- The problem is still open.
- No full asymptotic formula is known, even for `k = 3`.
- So there is no "real solved theorem" to formalize today.

Reference summary (from the Erdős problems page discussion):

- Best known upper bounds cited there:
  - Kelley-Meka (for `k = 3`)
  - Green-Tao (for `k = 4`)
  - Leng-Sah-Sawhney (for `k ≥ 5`)
- The page explicitly says an asymptotic formula is still far out of reach.

## Practical objective for this repo

Build a mathematically honest formalization program that:

1. captures the exact problem statement and equivalent formulations, and
2. formalizes rigorous known bounds and infrastructure,
3. without falsely claiming the open problem is solved.

## Achievable track (formalization plan)

1. Stabilize core API for AP-free sets and `r_k(N)` (done in part)
- Keep definitions in `ErdosProblems/Problem142.lean`.
- Maintain equivalence theorem with DeepMind-style shape:
  - `Erdos142.erdos_problem_142_iff_deepmind`.

2. Expand elementary finite combinatorics layer
- Add reusable lemmas for:
  - monotonicity of AP-freeness under subset,
  - transport under affine maps on `ℕ`,
  - interval truncation and cardinality monotonicity.
- Prove more unconditional facts about `rk`:
  - monotonicity in `N`,
  - basic sandwich bounds,
  - exact values for very small `N` and selected `k`.

3. Introduce bound statements as formal targets (no fake proofs)
- Add theorem declarations for known bound forms:
  - lower-bound templates (`Ω` / explicit constructions),
  - upper-bound templates (`O` / `o` statements).
- Keep them clearly marked as:
  - proved in Lean when elementary,
  - or imported as assumptions with precise provenance when deep.

4. Literature-to-Lean bridge
- For each deep result, add:
  - bibliographic identifier,
  - precise Lean statement,
  - dependency notes (what prior machinery is needed).
- Prefer a layered approach:
  - `Foundations` -> `QuantitativeBounds` -> `AsymptoticConsequences`.

5. Honest "best known consequences" module
- Derive clean corollaries from assumed/proved bounds:
  - e.g. explicit upper/lower asymptotic envelopes.
- Provide the strongest currently justified Lean statement that is true today.

## Non-achievable track (true full solution)

To actually solve #142 in full, one would need fundamentally new mathematics, not just
formalization effort. Treat this as a long-horizon research program, not an implementation task.

## Definition of done (current phase)

- [x] Correct statement formalized.
- [x] DeepMind-shape equivalence formalized.
- [ ] Comprehensive AP-free/rk API completed.
- [ ] Best-known upper/lower bounds encoded with full provenance.
- [ ] Strongest currently-known asymptotic corollaries formalized.
- [ ] (Open research) full asymptotic formula theorem proved.

## Immediate next actions

1. Add a dedicated section in `ErdosProblems/Problem142.lean` for bound target theorems
   (`k=3`, `k=4`, `k≥5`) with source tags.
2. Formalize and prove a first nontrivial unconditional bound/corollary that does not rely
   on deep external machinery.
3. Introduce a structured assumptions namespace for deep imported results, so the dependency
   surface is explicit and auditable.

## Possible breakthrough directions (research, speculative)

1. Stronger inverse theorems with quantitative control
- A route to full asymptotics likely needs much tighter quantitative inverse results for
  higher-order uniformity norms than currently available.

2. Density-increment schemes with dramatically reduced losses
- Existing increment frameworks lose too much at each scale.
- A qualitatively new increment architecture could be required.

3. Near-extremizer structure/classification for AP-free sets
- If near-maximal AP-free sets have rigid structure, that could force a concrete asymptotic
  template for `r_k(N)`.

4. Better matching lower-bound constructions
- Progress toward asymptotics also needs lower bounds that track upper bounds much more closely.
- New pseudorandom/algebraic constructions may be necessary.

5. Hybrid transference + arithmetic regularity approaches
- A successful strategy may combine transference principles, regularity decomposition, and
  additive energy control in a new way.

6. Explicit finite-to-asymptotic bridge
- Even with improved bounds, turning them into a true asymptotic formula requires a mechanism
  to prove convergence to a specific profile, not only envelope bounds.

## External references to anchor this plan

- Problem status and context: <https://www.erdosproblems.com/142>
- `k=3` benchmark: Kelley-Meka (2023), <https://arxiv.org/abs/2302.05537>
- `k=4` benchmark: Green-Tao (2017), <https://ora.ox.ac.uk/objects/uuid:1d09eef3-01e2-4ce0-ab9d-2892019812c8>
- `k≥5` benchmark: Leng-Sah-Sawhney (2024), <https://arxiv.org/abs/2402.17995>
