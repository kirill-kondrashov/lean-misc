# Notes: `k = 3` Negative-Route Endgame Escape Test (2026-03-08)

## Objective

Run the second live test from the `Template-Escape Critic`:

```text
is the current barrier only a consequence of using the crude terminal statement
|B_m| << 1,
or would the same exponent order survive if one rewrote the endgame in counting/supersaturation
language?
```

## Current Extracted Endgame

The recurrence extraction note records the terminal step as follows:

1. after the density-increment iteration, one reaches a structured set `B_m`;
2. on `B_m`, the restricted set has the expected number of three-term progressions;
3. because the original set is `3`-AP-free, only trivial progressions remain;
4. therefore `|B_m| << 1`.

So the present contradiction is already a counting contradiction, compressed into the final line

```math
|B_m| \ll 1.
```

## What A Genuine Endgame Escape Would Need

To beat the current barrier without changing the recurrence body, a stronger endgame would need to
extract more than “`B_m` has bounded size”.

In particular, it would need a terminal statement of the form

```math
\text{size lower bound on } B_m
\Longrightarrow
\text{nontrivial 3-AP contradiction at a scale stronger than } |B_m| \gg 1.
```

If the endgame still only yields

```math
|B_m| = O(1),
```

then the recurrence-to-exponent calculation is unchanged:

```math
\exp(-O(L^\gamma))N \ll 1
\quad\Longrightarrow\quad
L^\gamma \gg \log N.
```

## Counting Reformulation

Suppose the terminal stage gives a subset `A_m \subseteq B_m` of density

```math
\alpha_m \asymp 1
```

with a counting theorem saying that `A_m` contains roughly the expected number of 3-term
progressions on `B_m`.

In a random-model heuristic, the number of 3-term progressions at constant density is of order

```math
|B_m|^2,
```

while the number of trivial progressions is only

```math
O(|B_m|).
```

Therefore any terminal theorem of the shape

```math
T_3(A_m) \ge c|B_m|^2
```

for some absolute `c > 0` immediately contradicts 3-AP-freeness unless

```math
|B_m| = O(1).
```

So replacing the final line by an explicit supersaturation/counting formulation does not by itself
improve the exponent order. It just makes the same bounded-size contradiction more explicit.

## Verdict For This Escape Route

Within the same architecture, the `endgame escape` fails unless the critic can produce a terminal
theorem that is qualitatively stronger than:

```text
constant-density + expected progression count
  -> bounded ambient structured set size.
```

The current extracted endgame is already of that type, so rewriting it in counting language does
**not** currently break the barrier template.

## Scope Of This Verdict

This does **not** rule out all endgame improvements. It rules out only the following move:

```text
replace the shorthand |B_m| << 1 by an equivalent supersaturation/counting statement
while keeping the same recurrence body and the same terminal constant-density regime.
```

An actual escape would require at least one of these stronger changes:

1. a terminal theorem that contradicts 3-AP-freeness before the density reaches the constant
   regime;
2. a counting theorem whose quantitative dependence feeds back into the recurrence with a better
   power of `L`;
3. a different architecture where the endgame is not merely a bounded-size consequence.

## Critic Verdict

```text
No endgame escape has been found inside the current recurrence architecture.
The present barrier remains intact against the “just rewrite the endgame as supersaturation”
objection.
```
