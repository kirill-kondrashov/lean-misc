# Plan: Erdős #1 literature axioms -> base-axiom proofs (2026-03-08)

## Scope

This plan focuses only on the remaining literature axioms in
`ErdosProblems/Problem1Literature.lean`:

- `erdos_1_dubroff_fox_xu_lower_exact`
- `erdos_1_real_dubroff_fox_xu_lower_exact`
- `erdos_1_bohman_upper_construction`

The open problem axiom

- `Erdos1.erdos_1`

is explicitly out of scope here. The goal is not to solve Erdős Problem #1, but to replace the
literature axioms by theorems proved from base axioms inside Lean.

## Current dependency picture

At present:

1. The sharp middle-binomial asymptotic is already proved locally.
2. The remaining literature axioms are exactly:
   - the exact integer lower bound
     `N >= choose(n, floor(n/2))`,
   - the exact real spacing analogue,
   - the Bohman upper construction
     `N <= 0.22002 * 2^n` for infinitely many `n`.
3. Everything else in the Problem #1 stack now packages consequences of those three imports.

So the realistic axiom-burndown order is:

1. lower exact integer theorem,
2. lower exact real theorem,
3. upper Bohman construction.

## Literature anchor

The current problem-status page states:

- Dubroff-Fox-Xu (2021) prove the exact bound
  `N >= choose(n, floor(n/2))`.
- The second Dubroff-Fox-Xu proof also applies to the real spacing generalization.
- Bohman (1998) gives a construction with
  `N <= 0.22002 * 2^n`
  for all sufficiently large `n`.

This suggests one very concrete formalization strategy:

- use one common proof skeleton for both exact lower axioms,
- treat the Bohman upper theorem separately,
- and avoid mixing the upper-construction work with the lower-bound work.

## Chosen direction

### Main lower-bound direction

Use the second Dubroff-Fox-Xu proof as the primary exact-lower target, because it is the only route
currently cited in the local sources that should cover both:

- the integer exact lower theorem, and
- the real spacing exact lower theorem.

This is preferable to a forked strategy where the integer and real cases are formalized from
unrelated arguments.

### Main upper-bound direction

Split the current upper theorem into two layers:

1. a base-axiom constructive exponential upper theorem proved locally from an explicit family,
2. a later precision-upgrade theorem matching Bohman's `0.22002` constant.

This avoids blocking all upper-side progress on the full Bohman construction.

## Mathematical shape of the lower-bound target

Write

- `n = |A|`
- `k = floor(n / 2)`
- `Sigma_k(A) = { sum(S) : S subseteq A, |S| = k }`

Then:

1. `A` sum-distinct implies the map
   `S |-> sum(S)` on `k`-subsets is injective.
2. Hence
   `|Sigma_k(A)| = C(n,k)`.
3. The exact lower axiom is equivalent to proving
   `|Sigma_k(A)| <= N`.

So the real mathematical core is not the asymptotic step anymore. It is the exact statement

`|Sigma_floor(n/2)(A)| <= N`.

The formalization should therefore target this exact cardinality theorem directly, not an
asymptotic corollary first.

## Constructive proof plan by axiom

### Axiom 1: `erdos_1_dubroff_fox_xu_lower_exact`

Target theorem:

```text
forall N A, IsSumDistinctSet A N ->
  choose(A.card, A.card / 2) <= N
```

#### Phase L1: proof extraction from the paper

Before coding more lemmas, extract the second Dubroff-Fox-Xu proof into a Lean-sized dependency
graph:

- exact theorem statement
- central combinatorial or analytic lemma
- all uses of:
  - order on subset sums,
  - spacing/separation,
  - averaging/probability,
  - any convexity or comparison step

Deliverable:

- one note in `plan/` or inline comments describing the proof as 5-10 minimal lemmas

This phase is mandatory because the exact theorem is stronger than the current local counting
arguments, and guessing the lemma stack blindly is likely to waste time.

#### Phase L2: uniform-subset-sum API

Add a dedicated local API for fixed-cardinality subset sums:

- `uniformSubsetSumsNat (A : Finset ℕ) (k : ℕ) : Finset ℕ`
- theorem: sum-distinctness gives injectivity on `A.powersetCard k`
- theorem: `card (uniformSubsetSumsNat A k) = choose(A.card, k)`

This should isolate the exact lower theorem from the current broader `subsetSum` API, which mixes
all subset sizes together.

#### Phase L3: exact `|Sigma_k(A)| <= N` theorem

Formalize the paper's exact middle-layer bound as a theorem of the shape

```text
uniformSubsetSumsNat A (A.card / 2)).card <= N
```

Then conclude the literature theorem by rewriting the left-hand side as
`choose(A.card, A.card / 2)`.

### Axiom 2: `erdos_1_real_dubroff_fox_xu_lower_exact`

Target theorem:

```text
forall N A, IsSumDistinctRealSet A N ->
  choose(A.card, A.card / 2) <= N
```

#### Phase R1: reuse the same proof skeleton

The current literature summary says the second Dubroff-Fox-Xu proof applies to the real spacing
variant. So the formalization target should be a single abstract spacing lemma that is instantiated
twice:

- once for integer subset sums,
- once for real subset sums with distance at least `1`.

#### Phase R2: abstract spacing interface

Introduce a small interface expressing:

- ambient ordered additive type,
- a finite family of subset sums,
- pairwise distance at least `1`,
- all values contained in an interval of length `N`.

From this, prove a generic counting lemma:

`pairwise distance >= 1` inside an interval of length `N` implies `card <= N`.

If the second Dubroff-Fox-Xu proof can be organized around such a lemma, the integer and real exact
results should differ only in the proof that the relevant middle-layer sums satisfy the spacing
hypothesis.

### Axiom 3: `erdos_1_bohman_upper_construction`

Target theorem:

```text
forall^eventually n,
  exists N, HasSumDistinctSetCard N n /\ N <= 0.22002 * 2^n
```

#### Phase U1: immediate constructive surrogate

First prove locally, from base axioms only, the explicit binary construction:

- take
  `A_n = {1, 2, 4, ..., 2^(n-1)}`
- then `A_n` has distinct subset sums
- and `max(A_n) = 2^(n-1) = 0.5 * 2^n`

This does not remove the Bohman axiom, but it gives a theorem-level constructive upper surface
independent of any imported literature:

```text
forall n, exists N, HasSumDistinctSetCard N n /\ N <= 0.5 * 2^n
```

This should be added first, because it is low-risk and eliminates the need to use Bohman whenever
only an exponential upper bound is needed.

#### Phase U2: Bohman-specific witness architecture

Do not keep the Bohman theorem as one opaque axiom forever. Replace it by a witness bundle
architecture:

- explicit family data for sufficiently large `n`
- proof that the family has cardinality `n`
- proof that it is sum-distinct
- proof of the ambient upper bound

Then the only remaining opaque part, if any, is the explicit construction data itself, not the full
theorem statement.

#### Phase U3: full base-axiom Bohman proof

Long-term, formalize Bohman's actual construction and discharge the witness bundle entirely in Lean.

This is expected to be substantially harder than the binary surrogate and likely harder than the
exact lower theorem as well.

## Suggested module split

To keep the proof debt localized:

- `ErdosProblems/Problem1LowerExact.lean`
  - fixed-cardinality subset-sum API
  - integer exact lower theorem
- `ErdosProblems/Problem1LowerExactReal.lean`
  - abstract spacing lemmas
  - real exact lower theorem
- `ErdosProblems/Problem1UpperConstructive.lean`
  - explicit binary family with constant `1/2`
- `ErdosProblems/Problem1Bohman.lean`
  - Bohman witness bundle / final proof

`Problem1Literature.lean` should eventually become a packaging file, not the place where the
hardest proofs live.

## Checker policy target

The end state should be:

- no literature axioms left in `Problem1Literature.lean`
- all new proof files check under the existing base-axiom policy
- `make check` can include the new constructive/literature theorems without adding any new allowed
  axioms

The `native_decide` exact-value branch should remain separate from this policy target.

## Immediate next actions

1. Add this plan file.
2. Prove the binary constructive upper theorem with constant `1/2` in a new file.
3. Extract the second Dubroff-Fox-Xu proof into a lemma dependency list.
4. Build the `uniformSubsetSumsNat` API for fixed-cardinality subset sums.
5. Attempt the generic spacing lemma for the real proof path.

## Success criteria

This plan succeeds if, in order:

1. the binary upper theorem is proved from base axioms,
2. the exact integer lower axiom is replaced by a theorem,
3. the exact real lower axiom is replaced by a theorem,
4. the Bohman theorem is reduced to explicit witness data,
5. and finally the Bohman witness data is discharged too.

At that point the only remaining axiom in the Problem #1 stack should be the genuine open-problem
surface `Erdos1.erdos_1`.

## Sources

- Erdős Problem #1 status page, accessed March 8, 2026:
  <https://www.erdosproblems.com/1>
- Fox-Xu preprint (2020), for the sharp asymptotic probabilistic route:
  <https://doi.org/10.48550/arXiv.2006.12988>
- Bohman abstract page:
  <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v5i1r27>
