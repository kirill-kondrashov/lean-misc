# Prompt for GPT-5.4: property-(T) generalized triangle-group witness

Read:

- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_01.md`
- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_02.md`
- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_03.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_01.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_02.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_03.md`

We are investigating the conjecture that every word-hyperbolic group is residually finite.

Focus narrowly on the following possible route:

Find an explicit infinite hyperbolic property-(T) generalized triangle group, preferably from Caprace–Conder–Kaluba–Witzel, together with a subgroup `H < G` and element `g ∉ H` such that:

```text
G is word-hyperbolic,
H is quasiconvex,
g ∉ H,
and for every finite quotient φ : G → F,
φ(g) ∈ φ(H).
```

Such a triple would give a nonseparable quasiconvex subgroup and hence a non-residually finite hyperbolic group by Agol–Groves–Manning.

Audit one concrete candidate completely. Check:

1. the exact finite presentation;
2. infinitude and property-(T);
3. word-hyperbolicity;
4. whether the group is already virtually special or otherwise known residually finite;
5. an explicit subgroup `H`;
6. a genuine quasiconvexity proof;
7. an explicit proof that `g ∉ H`;
8. an all-finite-quotient proof of profinite nonseparability.

Finite quotient computations up to any bound are only evidence, not a proof. Do not claim a counterexample unless the universal quantifier over all finite quotients is established by a theorem.

If the route fails, identify the exact obstruction and formulate the strongest next theorem or computation that would genuinely advance the problem. Do not invent a candidate or treat an unpublished claim as established.

Do not modify Lean or source files. Write the result to:

`plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_04.md`

End with exactly one of:

- `Unconditional witness found: ...`
- `No unconditional witness; precise obstruction: ...`
