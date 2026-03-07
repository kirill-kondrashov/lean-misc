# Plan: Erdős Problem #1 (`sum-distinct` sets) from current literature (2026-03-07)

## Problem statement

Let `A ⊆ {1, ..., N}` be a finite set of naturals such that all subset sums
`∑_{a ∈ S} a` are distinct. Writing `n = |A|`, Erdős Problem #1 asks for an absolute
constant `c > 0` such that

```math
N \ge c \, 2^n
```

for every such `A`.

In this repository, the current statement layer is in `ErdosProblems/Problem1.lean`:

- `Erdos1.IsSumDistinctSet`
- `Erdos1.IsSumDistinctRealSet`
- `Erdos1.erdos_1`
- `Erdos1.erdos_1.variants.*`

## Reality check (as of March 7, 2026)

- The original problem is still open.
- The Erdős Problems page for Problem 1, last edited on January 23, 2026, still presents the
  exponential lower bound `N ≫ 2^n` as open.
- The best published lower bound listed there is due to Dubroff, Fox, and Xu (2021):

  ```math
  N \ge \binom{n}{\lfloor n/2 \rfloor},
  ```

  which yields the asymptotic lower bound

  ```math
  N \ge \left(\sqrt{2/\pi} - o(1)\right)\frac{2^n}{\sqrt{n}}.
  ```

- The same problem page states that the second Dubroff-Fox-Xu proof also yields the same
  `2^n / sqrt(n)`-scale lower bound for the real-valued spacing variant.
- Steinerberger (2023) gives another proof of the same lower bound via an integral inequality,
  together with an equality characterization. This is mathematically relevant because it suggests a
  continuous/analytic route rather than only the original combinatorial proof.
- The best published upper construction cited by the same January 23, 2026 problem page remains
  Bohman (1998), which gives sum-distinct sets with largest element asymptotically at most
  `0.22002 * 2^n`.
- I did not find a post-2023 paper improving the main lower or upper bounds for the original
  integer problem. This is an inference from the literature search on March 7, 2026 together with
  the January 23, 2026 state of the Erdős Problems page.
- For exact small values, OEIS A276661, last modified on February 8, 2026, records
  `a(3) = 4`, `a(5) = 13`, `a(9) = 161`, and `a(10) = 309`.

## Local status in this repo

- `Erdos1.erdos_1` is currently an axiom-level statement placeholder.
- `Erdos1.erdos_1.variants.weaker` is now proved by the elementary counting argument on
  `Finset.subsetSum`.
- The public statement names `Erdos1.erdos_1.variants.lb` and
  `Erdos1.erdos_1.variants.lb_strong` are still axiomatized, but the repo now also contains
  derived versions from a single asymptotic middle-binomial input:
  `erdos_1_variants_lb_from_choose_middle_asymptotic` and
  `erdos_1_variants_lb_strong_from_choose_middle_asymptotic`.
- `Erdos1.erdos_1.variants.real` is currently axiomatized as an exponential real-valued analogue,
  but the repo now also contains exact and asymptotic lower-bound surfaces for the known
  `2^n / sqrt(n)`-scale regime.
- `Erdos1.erdos_1.variants.least_N_3` is already proved.
- `Erdos1.erdos_1.variants.least_N_5` is now proved by finite verification.
- `Erdos1.erdos_1.variants.least_N_9` is still an axiom.

## Practical objective for this repo

Do not pretend the open problem is solved. The realistic target is:

1. formalize the exact problem statement cleanly,
2. formalize the strongest currently published lower and upper results with precise provenance,
3. prove the elementary local facts that do not need imported deep mathematics,
4. and isolate the remaining genuine open gap as explicitly as possible.

## Feasible formalization track

1. **Refactor onto mathlib's subset-sum API**
   - `Mathlib.Combinatorics.Additive.SubsetSum` already defines `Finset.subsetSum`.
   - Add equivalence lemmas showing that `Erdos1.IsSumDistinctSet A N` can be re-expressed as
     `A ⊆ Finset.Icc 1 N` together with a cardinality statement such as
     `A.subsetSum.card = 2 ^ A.card`.
   - This should replace the current raw injectivity definition with an interface that matches
     existing mathlib combinatorics.

2. **Prove the elementary weaker lower bound locally**
   - The trivial argument is: all subset sums are distinct integers in an interval of length
     at most `A.card * N`, so

     ```math
     2^{|A|} \le |A| N + 1.
     ```

   - From this, derive a concrete constant-form theorem replacing the axiom
     `Erdos1.erdos_1.variants.weaker`.
   - This should be the first non-axiomatic upgrade after the statement layer.

3. **Turn the sharp lower bound into one exact imported theorem**
   - The central imported theorem should not be the asymptotic variant first.
   - Instead, add a single exact Dubroff-Fox-Xu style theorem with shape:

     ```math
     N \ge \binom{n}{\lfloor n/2 \rfloor},
     ```

     where `n = A.card`.
   - Keep this theorem in a literature-facing module, likely
     `ErdosProblems/Problem1Literature.lean`, so provenance is explicit.
   - Then derive the current axioms `lb` and `lb_strong` as corollaries, rather than leaving them
     as independent black boxes.

4. **Derive the asymptotic `sqrt(2 / pi)` corollary honestly**
   - mathlib already has `Nat.choose`, factorial support, and Stirling machinery.
   - Add the required bridge lemmas from middle binomial coefficients to the asymptotic expression
     `(sqrt (2 / pi) - o(1)) * 2^n / sqrt n`.
   - If the full asymptotic derivation is too heavy at first, first prove a weaker explicit bound
     with fixed constants, then refine it to the asymptotic statement.

5. **Split the real-valued branch into honest layers**
   - The current theorem `Erdos1.erdos_1.variants.real` states the open exponential analogue for
     real sets. That should remain clearly marked as open.
   - Add a separate literature-backed theorem for the currently known real-valued lower bound at
     the `2^n / sqrt(n)` scale, sourced to the second Dubroff-Fox-Xu proof and Steinerberger's
     route.
   - This avoids conflating "known lower bound" with "open exponential conjecture".

6. **Formalize the best known upper construction**
   - Add a theorem surface for the Bohman construction, expressing the existence of
     `sum-distinct` sets of size `n` inside `{1, ..., ⌈C * 2^n⌉}` for some explicit
     `C < 1`.
   - Keep this in a separate literature namespace or imported-witness structure.
   - The point is not to reprove Bohman immediately, but to capture the best known upper record
     with explicit provenance.

7. **Build an honest gap statement**
   - After Steps 3 and 6, the repo should expose the real current state:
     one exact lower theorem at scale `2^n / sqrt(n)` and one upper construction at scale `2^n`.
   - Add a theorem or definition packaging this as the local "best known sandwich" rather than
     pretending the main conjecture is solved.

8. **Separate finite exact-value work from asymptotic literature imports**
   - `least_N_5` is a realistic next exact theorem candidate.
   - `least_N_9` and the OEIS value `a(10) = 309` should likely be handled by verified search
     certificates or small external computations, not by brute-force kernel search.
   - If this branch grows, move it into a dedicated exact-values module or certificate workflow.

## Non-feasible track today

Actually proving `Erdos1.erdos_1` from current mathematics is not a programming task. The open gap
is a factor of about `sqrt(n)` between:

```math
\left(\sqrt{2/\pi} - o(1)\right)\frac{2^n}{\sqrt{n}}
\qquad \text{and} \qquad
0.22002 \cdot 2^n.
```

Closing that gap requires new mathematics, not just Lean engineering.

## Plausible research directions suggested by the literature

1. **Strengthen the antichain / counting route**
   - Dubroff-Fox-Xu prove the sharp middle-binomial lower bound currently known.
   - A true solution would need a qualitatively stronger anti-concentration mechanism that removes
     the `sqrt(n)` loss.

2. **Exploit Steinerberger's continuous reformulation**
   - The integral inequality and equality characterization may provide a route to structural
     rigidity for near-extremal sets.
   - This looks like the most concrete literature-backed "new angle" rather than just an
     incremental improvement of older counting arguments.

3. **Classify near-extremizers**
   - If one can show that any near-optimal sum-distinct set must resemble a known construction,
     this could convert the current lower bound problem into a structural theorem.

4. **Connect upper constructions and obstruction theory**
   - Bohman shows that the upper side is genuinely exponential.
   - A real solution may need either:
     - a much stronger lower obstruction, or
     - a structural theorem explaining why Bohman-type constructions are essentially optimal up to
       constant factors.

## Definition of done for the next repo phase

- [x] Statement layer added in `ErdosProblems/Problem1.lean`.
- [x] Exact benchmark `Erdos1.erdos_1.variants.least_N_3`.
- [x] `Erdos1.erdos_1.variants.weaker` proved without axioms.
- [x] Exact Dubroff-Fox-Xu lower theorem added as the primary literature import.
- [x] `lb` and `lb_strong` reduced to the exact imported lower theorem plus local middle-binomial
      asymptotic machinery; the sharp central-binomial asymptotic is now proved.
- [x] Honest real-valued `2^n / sqrt(n)` theorem surface added.
- [x] Bohman upper-construction theorem surface added.
- [~] Exact-value strategy partly executed: `least_N_5` is now proved by finite verification;
      `least_N_9` and `a(10) = 309` remain open implementation targets.
- [ ] Repo surface made explicit about the remaining open `sqrt(n)` gap.

## Immediate next actions

1. Refactor `Problem1.lean` if we want the original public dotted names
   `Erdos1.erdos_1.variants.lb` and `Erdos1.erdos_1.variants.lb_strong` themselves to stop being
   axioms, rather than merely providing the non-axiomatic aliases
   `Erdos1.erdos_1.variants.proved.lb` and
   `Erdos1.erdos_1.variants.proved.lb_strong`.
2. Add a notes file auditing exact-value sources and certificate strategy for `a(9)` and
   `a(10) = 309`.
3. Decide whether to keep the real-valued lower results in `Problem1Literature.lean` or split them
   into a dedicated `Problem1Real.lean`.
4. Add README coverage for the new exact/literature surfaces if the documentation should track the
   latest code state more closely.

## External references anchoring this plan

- Problem status page, last edited January 23, 2026:
  <https://www.erdosproblems.com/1>
- Dubroff, Fox, Xu, "A note on distinct subset sums" (2021):
  <https://arxiv.org/abs/2101.02575>
- Steinerberger, "Some remarks on a problem of Erdős on distinct subset sums" (2023):
  <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v30i3p32>
- Bohman, "A sum packing problem" (1998):
  <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v5i1r27>
- OEIS A276661, last modified February 8, 2026:
  <https://oeis.org/A276661>
