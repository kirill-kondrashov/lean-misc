# Stuck Plans

This note compresses the dead and superseded branches. The active route is now the additive
stability program, not the exact middle-binomial route by itself.

## Superseded Documentation Wrappers

- The following notes were useful staging wrappers but are no longer active:
  - `PLAN_stronger_than_middle_binomial_via_two_layer_gap.md`
  - `PLAN_improved_bound_theorem_first_program.md`
  - `NOTE_restricted_half_cube_stability_literature_bridge.md`
  - `PROGRESS_two_sheet_boundary_theorem_2026-03-22.md`
  - `PLAN_simple_lower_uniform_upper_pair_interface_boundary_lower_research.md`
  - `PLAN_two_layer_middle_boundary_inequality.md`
  - `STATEMENT_simple_lower_uniform_upper_pair_interface_boundary_lower.md`
- Their live content now sits in:
  - `PLAN_erdos1_additive_stability_program.md`
  - `PLAN_first_additive_improvement_beyond_middle_binomial.md`
  - `PLAN_restricted_half_cube_hamming_ball_stability.md`
  - `PLAN_subcritical_inward_descent_discrete_morse_route.md`
  - `PROOF_uniform_corner_weights_reduce_to_local_incidence_transport.md`
  - `NOTE_erdos1_position_against_current_literature.md`

## Exact Middle-Binomial Route Status

- The exact two-layer inequality
  \[
  |\partial^+F| \ge |C|
  \]
  remains mathematically meaningful and is still recorded in
  `PROOF_two_layer_middle_boundary_inequality.md`.
- It is no longer an active standalone plan because proving it recovers the known
  Dubroff-Fox-Xu middle-binomial lower bound, not a new state-of-art approximation.
- The exact route should be used only as infrastructure or as a base case for the additive gap
  theorem
  \[
  |\partial^+F| \ge |C| + m.
  \]

## Archived Branches

### 1. Section Route

- Unrestricted even adjacent-layer theorem:
  \[
  |\partial^+G| \ge |G_r|,
  \qquad
  G \subseteq \binom{[2m]}{r}\sqcup \binom{[2m]}{r+1}.
  \]
- Status: `falsified`.
- Counterexamples:
  \[
  G=\binom{[4]}{2}\sqcup \binom{[4]}{3}
  \quad\Rightarrow\quad
  |\partial^+G|=1<6=|G_2|,
  \]
  \[
  G=\binom{[6]}{3}\sqcup \binom{[6]}{4}
  \quad\Rightarrow\quad
  |\partial^+G|=6<20=|G_3|.
  \]
- Coupled repair attempt:
  \[
  |\partial^+(A\cup D)| + |\partial^+(B\cup E)| \ge |A| + |B|.
  \]
- Status: `falsified`.
- Consequence: sectioning survives only as an exact identity / heuristic, not as an active
  reduction theorem.

### 2. Compression-Monotonicity Route

- Conjectured functional:
  \[
  \Delta(U,V):=|T(V)\setminus U|-|\partial^\uparrow U|.
  \]
- Desired monotonicity:
  \[
  \Delta(U,V)\le \Delta(C_{ij}U,C_{ij}V).
  \]
- Status: `falsified`.
- Consequence: this route is dead.

### 3. Weaker Colex Reduction

- Proposed theorem:
  \[
  \Delta(U,V)\le \Delta(U^\ast,V^\ast)
  \]
  for equal-size colex pairs \((U^\ast,V^\ast)\).
- Status: `falsified`.
- Consequence: no direct reduction from arbitrary pairs to colex pairs via this defect functional.

### 4. Hall-Shadow Sufficient Condition

- Proposed sufficient condition:
  \[
  |\partial^\uparrow U| \ge |U\setminus T(V)|.
  \]
- Status: `falsified`.
- Consequence: the active boundary theorem cannot be reduced to a Hall-style argument of this form.

### 5. Flux / Calibration Heuristic

- Codimension-`1` local transport is false.
- Equal-split codimension-`2` weighting is false.
- Inverse-degree codimension-`2` weighting is false.
- Finite families of greedy local matching rules are false.
- The surviving information from that branch is only heuristic:
  codimension-`2` transport may still matter, but it is no longer an active commit gate.

### 6. Strict Compression Shortcut

- Proposed strengthening:
  every nonshifted two-layer pair admits a layer-preserving shift that strictly lowers
  \[
  |\partial^+F|.
  \]
- Status: `falsified`.
- Consequence: the compression route cannot be driven by a strictly descending potential alone.

### 7. Strict-Local-Minimum Plateau Route

- Proposed strengthening:
  every strict local minimum for the layer-preserving shift dynamics lies in a
  boundary-preserving shift component containing a shifted pair.
- Status: `falsified`.
- Consequence: any proof has to use genuinely interleaved nonincreasing paths or a more global
  monotone invariant.

### 8. Strong Inward Descent

- Proposed theorem:
  \[
  d(F)\ge 4
  \Longrightarrow
  \exists F' \text{ with } d(F')=d(F)-2 \text{ and } \Delta(F')\le \Delta(F).
  \]
- Status: `falsified`.
- Consequence:
  only the weaker subcritical descent theorem remains live, and the active replacement is now the
  four-step stack: shifted-template corner existence, incidence locality, structured-corner
  refinement, then uniform-corner incidence injection.
