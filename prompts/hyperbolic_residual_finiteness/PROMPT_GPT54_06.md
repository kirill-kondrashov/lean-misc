# Prompt for GPT-5.4: random and graded-small-cancellation counterexample route

Read:

- `plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_01.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_05.md`
- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_01.md`

The previous KMS candidate is falsified: an explicit finite `SL_3(F_{7^3})` quotient separates
`c` from `<a,b>`. Do not revisit it.

Investigate the following construction route for a genuinely non-residually finite hyperbolic group:

```text
finite-presentation random or small-cancellation hyperbolic group
       + mechanism excluding every nontrivial finite quotient
       => hyperbolic non-residually finite group.
```

Audit the density model and graded/graphical small-cancellation literature. In particular, determine precisely whether any theorem proves, or even makes plausible, that a random group at density

```text
1/3 < d < 1/2
```

is simultaneously infinite word-hyperbolic, property-(T), and has no nontrivial finite quotients.

For each claim, separate:

1. finite presentation;
2. infinitude and word-hyperbolicity;
3. property-(T), if used;
4. absence of finite quotients of bounded size versus absence of all finite quotients;
5. fixed-density random statements versus an explicit deterministic group.

Then analyze whether an enumeration of finite groups and homomorphisms can be built into a *finite* small-cancellation presentation. Explain exactly why the familiar graded-small-cancellation construction of groups with no finite quotients does or does not preserve word hyperbolicity; do not confuse a direct limit of hyperbolic groups with a word-hyperbolic group.

The desired output is either:

- an unconditional finite presentation with a fully cited proof of hyperbolicity and a nontrivial element killed by every finite quotient; or
- a rigorous obstruction showing where all known random/graded-small-cancellation approaches lose finite presentation, hyperbolicity, or the universal finite-quotient conclusion.

Use primary sources. Do not make probabilistic heuristics into theorems. Do not modify Lean or source files. Write the result to:

`plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_06.md`

End with exactly one of:

- `An unconditional random/small-cancellation counterexample exists: ...`
- `No such counterexample is known; exact obstruction: ...`
