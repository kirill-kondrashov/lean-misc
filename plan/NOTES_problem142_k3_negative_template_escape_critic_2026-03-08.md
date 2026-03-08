# Notes: `k = 3` Negative-Route Template-Escape Critic (2026-03-08)

## Objective

Introduce an explicit critic for the active negative route.

This critic is not supposed to defend the barrier. Its job is the opposite:

```text
try to show that the recurrence barrier
theta(a,b) = 1 / max(a+3, b+1)
does not actually control the real modern proof line as strongly as the current notes suggest.
```

## Critic Name

```text
Template-Escape Critic
```

## Mandate

The critic is allowed to challenge any of the following.

1. The recurrence template itself.
2. The use of one frozen parameter `L = log(2/α)` across the full iteration.
3. The claim that `m = O(L)` is the right effective iteration count.
4. The claim that the endgame must pass through `|B_m| << 1`.
5. The claim that the integer-case Bohr-set loss is intrinsic to the architecture rather than to
   one transport implementation.

The critic is **not** allowed to propose a completely different theorem technology and then claim
the barrier is false. The point is to test the current architecture honestly, not to switch
architectures mid-argument.

## Main Escape Routes To Test

### 1. Step-count escape

Question:

```text
Could the real iteration terminate in o(L) effective steps after a more careful use of local
densities α_j, invalidating the coarse m = O(L) summary?
```

Why it matters:

```text
If the number of effective steps drops, then the exponent formula
theta(a,b) = 1 / max(a+3, b+1)
may overstate the true cumulative loss.
```

## 2. Parameter-localization escape

Question:

```text
Is the use of one global L too coarse?
Should the true recurrence be written with L_j = log(2/α_j),
so that later stages are cheaper than the current coarse summation records?
```

Why it matters:

```text
The current barrier note treats the worst-case L as fixed across the whole run.
That is safe as an upper bound, but it may not be sharp enough for a negative theorem.
```

Status:

```text
tested in NOTES_problem142_k3_negative_parameter_localization_test_2026-03-08.md
```

Preliminary verdict:

```text
within the same recurrence template, localizing to L_j does not change the exponent order;
the dominant loss remains max(a+3, b+1).
```

## 3. Endgame escape

Question:

```text
Must the contradiction route really be |B_m| << 1,
or could a supersaturation/counting endgame convert the same iteration into a stronger exponent?
```

Why it matters:

```text
If the endgame changes, then the barrier may be a barrier only for one closure mechanism,
not for the whole architecture.
```

Status:

```text
tested in NOTES_problem142_k3_negative_endgame_escape_test_2026-03-08.md
```

Preliminary verdict:

```text
rewriting the same terminal constant-density contradiction in supersaturation/counting language
does not improve the exponent order; it still collapses to |B_m| = O(1).
```

## 4. Integer-transfer escape

Question:

```text
Is the extra Bohr-set loss an unavoidable feature of the integer case,
or only a feature of the currently extracted transport path?
```

Why it matters:

```text
If a different transfer to the integers removes the extra loss,
then the negative route is too strong as currently worded.
```

Status:

```text
tested in NOTES_problem142_k3_negative_integer_transfer_escape_test_2026-03-08.md
```

Preliminary verdict:

```text
no source-backed alternate integer transfer has been identified in the audited source set;
the integer-case loss remains a real recorded obstruction, not an already-escaped artifact.
```

## Evidence Standard

The critic succeeds only if it produces one of the following.

1. A concrete recurrence refinement that invalidates the current `theta(a,b)` formula.
2. A source-backed endgame or transport variant that is still recognizably within the same modern
   architecture but escapes the current template.
3. A precise statement showing that one of the note-level abstractions is not justified by the
   cited sources.

Mere optimism does not count.

## Final Critic Verdict

```text
After the current critic pass:
- parameter localization did not change the exponent order;
- endgame reformulation did not improve the exponent order inside the same terminal regime;
- no alternate integer transfer has been identified in the audited source set.

So the barrier survives all currently tested template-escape objections.
That does not make it final mathematics, but it does make the negative route stable enough to be
treated as the current honest research surface.
```
