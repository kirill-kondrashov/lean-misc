# Plan: `k = 3` Negative/Bottleneck Program

Date: 2026-03-08

Revision: introduce an explicit adversarial critic for the negative route.

## Objective

Make the negative route explicit and pressure-test it:

```text
show that the presently extracted Kelley--Meka / Bloom--Sisask architecture,
modeled by the current recurrence class,
cannot by itself yield a Behrend-scale upper bound.

Then actively try to break that conclusion by searching for ways the real proof line
could escape the recurrence template.
```

## Status

- Barrier cycle: `██████` `6 / 6`
- Critic cycle: `██████` `6 / 6`
- Active progress: `██████` `6 / 6`

## Deliverable

The operative negative statement is:

```text
for the recurrence class isolated from the current modern proof line,
the propagated exponent is
theta(a,b) = 1 / max(a+3, b+1),
so the current published regime gives 1/9,
the first source-motivated local refinement gives 1/8,
and this architecture class does not reach 1/2.
```

The revised deliverable is stronger:

```text
either the barrier survives an explicit template-escape critic,
or the critic isolates the exact place where the negative route is overclaiming.
```

## New Critic

Name:

```text
Template-Escape Critic
```

Mandate:

```text
do not accept the negative-route barrier merely because the recurrence notes look clean;
try to find concrete ways the real Kelley--Meka / Bloom--Sisask line could escape
the template theta(a,b) = 1 / max(a+3, b+1).
```

Working note:

- `NOTES_problem142_k3_negative_template_escape_critic_2026-03-08.md`

## Milestones

1. `[x]` Freeze the exact negative target as a repository-level mathematical statement.
   - note: `NOTES_problem142_k3_negative_bottleneck_target_2026-03-08.md`

2. `[x]` Derive the generic exponent propagated by the extracted recurrence class.
   - note: `NOTES_problem142_k3_negative_architecture_barrier_2026-03-08.md`
   - formula: `theta(a,b) = 1 / max(a+3, b+1)`
   - Lean schema:
     `K3ArchitectureBarrierParams`,
     `K3ArchitectureBarrierParams.lossExponent`,
     `K3ArchitectureBarrierParams.propagatedExponent`

3. `[x]` Verify that the current published source-backed recurrence fits the template.
   - input: `a = 6`, `b = 7`
   - consequence: exponent `1/9`

4. `[x]` Verify that the first source-motivated local improvement still fits the template.
   - input: `a = 5`, `b = 6`
   - consequence: exponent `1/8`

5. `[x]` Convert the generic formula into an explicit barrier against the Behrend target.
   - Behrend scale would require `max(a+3, b+1) = 2`
   - under nonnegative loss exponents this is impossible

6. `[x]` Record the route consequence in the active pivot docs.
   - the `1/8` route remains conjectural scaffolding
   - the negative/bottleneck route is the primary active theorem program

## Critic Cycle Milestones

1. `[x]` Introduce an explicit critic with permission to attack the recurrence template itself.
   - note: `NOTES_problem142_k3_negative_template_escape_critic_2026-03-08.md`

2. `[x]` Freeze the list of plausible template-escape routes.
   - step-count escape
   - parameter-localization escape
   - endgame escape
   - integer-transfer escape

3. `[x]` Test whether the use of one global `L = log(2/α)` is too coarse.
   - critic question: must the real iteration be analyzed with `L_j = log(2/α_j)` instead?
   - note: `NOTES_problem142_k3_negative_parameter_localization_test_2026-03-08.md`
   - verdict: no exponent-order escape detected inside the same recurrence template

4. `[x]` Test whether the terminal contradiction `|B_m| << 1` is the wrong endgame.
   - critic question: could a supersaturation/counting endgame beat the current template?
   - note: `NOTES_problem142_k3_negative_endgame_escape_test_2026-03-08.md`
   - verdict: not within the same constant-density terminal architecture

5. `[x]` Test whether the integer-case Bohr loss can be bypassed by a different transfer route.
   - critic question: is the barrier only for the current Bohr-set transport, rather than for the
     broader architecture?
   - note: `NOTES_problem142_k3_negative_integer_transfer_escape_test_2026-03-08.md`
   - verdict: no alternate source-backed transport escape found in the audited source set

6. `[x]` Record a final critic verdict.
   - outcome A: barrier survives and the negative route is stable
   - outcome B: critic finds a real escape and forces another plan revision
   - current outcome: A

## Current Verdict

```text
Barrier cycle complete:
the repository has an explicit architecture-level reason that the present route is off-path
for Behrend scale, and that reason is now encoded both in notes and in a Lean-side schema.

Critic cycle complete:
no tested template-escape route has yet broken the current barrier abstraction.

Current active stance:
the negative/bottleneck route is stable as the honest research surface, subject to reopening if a
future source audit uncovers a genuinely different integer transfer or another template escape.
```

## Successor Plan

The next packaging/stabilization cycle is:

- `PLAN_erdos_problem_142_k3_negative_route_stabilization_2026-03-08.md`
