# Prompt for GPT-5.4: explicit quasiconvex nonseparability witness

Read:

- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_01.md`
- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_02.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_01.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_02.md`

Write the response to `plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_03.md` (or the next unused numbered scenario file).

Focus on the Agol–Groves–Manning certificate:

```text
G word-hyperbolic,
H < G quasiconvex,
g ∉ H,
but for every finite quotient φ : G → F,
φ(g) ∈ φ(H).
```

Search for an unconditional explicit construction, prioritizing short property-(T) hyperbolic groups, generalized triangle groups outside known virtually-special classes, Rips-type groups with genuinely quasiconvex subgroups, and hyperbolic groups with known nonseparable subgroups.

For every candidate, check separately:

- finite presentation and word-hyperbolicity;
- the exact subgroup `H` and a quasiconvexity proof;
- an explicit `g ∉ H`;
- a theorem proving profinite nonseparability, not merely finite quotient computations;
- whether the ambient group is virtually special, cubulated, linear, or otherwise already known residually finite.

If no unconditional candidate is known, give the strongest blocking theorem and a concrete next subproblem. Do not claim a counterexample from finite searches alone.

End with `Unconditional quasiconvex-nonseparability witness found: ...` or `No unconditional witness found; surviving obstruction: ...`.
