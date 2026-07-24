# Prompt for GPT-5.4: audit the arithmetic finite-kernel route

Read:

- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_01.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_worker_01.md`

Write the response to `plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_02.md` (or the next unused numbered scenario file).

Audit this proposed route from primary sources:

```text
compact rank-one arithmetic lattice Γ
        + finite central/non-residually-finite extension
        => hyperbolic non-residually-finite group
```

For a concrete uniform lattice family, preferably in `Spin(n,1)` or `SU(n,1)`, check:

1. whether the base lattice is word-hyperbolic;
2. the exact central extension and whether its kernel is finite;
3. the explicit finite-residual witness proving failure of residual finiteness;
4. whether the construction requires a finite or infinite congruence kernel;
5. whether the extension remains word-hyperbolic;
6. whether residual-finiteness or linearity theorems rule it out.

Do not conflate higher-rank Deligne extensions with rank-one lattices, nonuniform relatively hyperbolic lattices with word-hyperbolic groups, or infinite central kernels with finite ones.

If no unconditional candidate survives, state the exact named theorem or conjecture that is missing, compare this route with quasiconvex nonseparability, and propose the next prompt.

End with `Arithmetic route yields an unconditional candidate: ...` or `Arithmetic route remains conditional on: ...`.
