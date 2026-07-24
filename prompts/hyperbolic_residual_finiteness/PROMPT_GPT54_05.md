# Prompt for GPT-5.4: explicitly test the KMS finite quotient

Read:

- `prompts/hyperbolic_residual_finiteness/PROMPT_GPT54_04.md`
- `plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_04.md`

The previous scenario chose

```text
G = 𝒢_{HB_2^{(2)}}(7),    H = <a,b>,    g = c.
```

It observed that CCKW provide finite simple quotients `SL_3(F_{7^e})` for `e >= 3`, but it did not perform the decisive test: whether one of those explicit quotient maps separates `c` from `<a,b>`.

Audit this exact issue from the published CCKW paper and its cited finite-quotient construction.

1. Locate the explicit homomorphism or matrix realization

   ```text
   ρ : G → SL_3(F_{7^e})
   ```

   for one concrete `e >= 3`. Give the images `ρ(a), ρ(b), ρ(c)` exactly, with a source location.

2. Verify directly that the defining relators of `G` hold for those matrices, and that the image is the claimed finite quotient.

3. Determine rigorously whether

   ```text
   ρ(c) ∈ <ρ(a), ρ(b)>.
   ```

   Prefer a structural proof using invariant flags, root groups, orders, or matrix-entry constraints. A GAP/Magma/Sage calculation may support the result, but the final conclusion must be independently checkable from the displayed matrices.

4. If `ρ(c) ∉ <ρ(a),ρ(b)>`, record that the specific triple

   ```text
   (G, <a,b>, c)
   ```

   is `falsified` as a profinite-nonseparability witness, since this finite quotient separates it.

5. If instead `ρ(c) ∈ <ρ(a),ρ(b)>` for the available quotient family, explain whether this is a theorem for every finite quotient or only an artifact of that family. Do not upgrade it to the desired universal statement without proof.

Do not search for a different construction until this concrete triple has been conclusively classified. Do not modify Lean or source files. Write the result to:

`plan/SCENARIO_hyperbolic_residual_finiteness_GPT54_05.md`

End with exactly one of:

- `The KMS triple is falsified by the quotient: ...`
- `The KMS quotient family does not separate the triple, but universality remains unproved: ...`
