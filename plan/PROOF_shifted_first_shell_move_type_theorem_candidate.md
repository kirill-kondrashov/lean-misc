# Proof Note: Shifted First-Shell Move-Type Theorem Candidate

This note records the current theorem candidate suggested by the exact shifted first-shell data on
the stronger-than-middle-binomial branch.

## Setup

Let

```math
n = 2m+1,
\qquad
P_m := \binom{[n]}{m},
\qquad
P_{m+1} := \binom{[n]}{m+1}.
```

For

```math
F = C \cup U,
\qquad
C \subseteq P_m,
\qquad
U \subseteq P_{m+1},
\qquad
|U| = |P_m \setminus C|,
```

write

```math
\Delta(F) := |\partial^+F| - |C|.
```

Let `\mathcal E` be the two shifted equality templates:

1. the full lower layer
   ```math
   F_{\mathrm{full}} = P_m;
   ```
2. the principal-star family
   ```math
   F_{\star}
   =
   \{A \in P_m : 0 \in A\}
   \;\cup\;
   \{B \in P_{m+1} : 0 \in B\}.
   ```

The active first-shell theorem candidate concerns shifted families at template distance `2`.

## Observed First-Shell Classification

Exact shifted computation now supports the following.

### Global shell structure

For shifted odd dimensions

```math
n = 7,9,11,13,15,17,19,21,
```

the distance-`2` shell around `\mathcal E` decomposes into:

```math
1 \text{ full-lower orbit } + 4 \text{ principal-star orbits}.
```

Moreover every orbit in that shell satisfies

```math
\Delta(F) = m.
```

### Local move-type decomposition

The sharper local decomposition computation is now exact through shifted

```math
n = 7,9,11,13,15,17,19,21.
```

It shows that the distance-`2` shell splits as follows.

1. Full-lower side:
   exactly one move type,
   ```math
   (\text{lower distance}, \text{upper distance}) = (1,1),
   ```
   with multiplicity `1`.

2. Principal-star side:
   exactly three move types,
   ```math
   (0,2),\qquad (1,1),\qquad (2,0),
   ```
   with multiplicities
   ```math
   1,\qquad 2,\qquad 1.
   ```

Every one of these move types still has

```math
\Delta(F) = m.
```

So the candidate theorem is no longer just a gap statement. It is a rigid shell-classification
statement.

There is also a cleaner structural split on the principal-star side:

- one pure upper move `(0,2)`;
- two mixed moves `(1,1)`;
- one pure lower move `(2,0)`.

So the principal-star first shell is not just a multiset of orbits. It breaks into

```math
\text{pure upper},\qquad \text{mixed},\qquad \text{mixed},\qquad \text{pure lower}.
```

This is a better proof target than the raw orbit count, because it suggests proving the first-shell
law by handling the two pure moves and the two mixed moves separately.

## Canonical Representative Shapes Suggested By The Data

The exact witnesses in low dimensions suggest the following formulas.

### Full-lower shell

The unique full-lower distance-`2` orbit appears to be

```math
C = P_m \setminus \{\{m+1,m+2,\dots,2m\}\},
\qquad
U = \{\{0,1,\dots,m\}\}.
```

That is: remove the top lex/colex lower vertex and add the bottom upper vertex.

### Principal-star `(0,2)` shell

The unique principal-star orbit with lower/upper distances `(0,2)` appears to be

```math
C = \{A \in P_m : 0 \in A\},
```
```math
U =
\bigl(\{B \in P_{m+1} : 0 \in B\} \setminus \{\{0,m+1,\dots,2m\}\}\bigr)
\cup
\{\{1,2,\dots,m+1\}\}.
```

So the lower layer stays at the star template, while the upper layer swaps its top star vertex for
the bottom nonzero vertex.

### Principal-star `(2,0)` shell

The unique principal-star orbit with lower/upper distances `(2,0)` appears to be obtained by the
dual lower-layer move:

```math
C =
\bigl(\{A \in P_m : 0 \in A\} \setminus \{\{0,m+2,\dots,2m\}\}\bigr)
\cup
\{\{1,2,\dots,m\}\},
\qquad
U = \{B \in P_{m+1} : 0 \in B\}.
```

So the upper layer stays at the star template, while the lower layer swaps one top star vertex for
the bottom nonzero vertex.

### Principal-star `(1,1)` shell

There are exactly two shifted orbits of type `(1,1)`.

The new compact delta signatures isolate the two general shapes.

#### Lower-add / upper-remove class

```math
C = \{A \in P_m : 0 \in A\} \cup \{\{1,2,\dots,m\}\},
```
```math
U = \{B \in P_{m+1} : 0 \in B\} \setminus \{\{0,m+1,\dots,2m\}\}.
```

So one first-shell orbit is obtained by adding the bottom nonzero lower vertex while removing the
top star upper vertex.

This is the first mixed principal-star class.

#### Lower-remove / upper-add class

```math
C = \{A \in P_m : 0 \in A\} \setminus \{\{0,m+2,\dots,2m\}\},
```
```math
U = \{B \in P_{m+1} : 0 \in B\} \cup \{\{1,2,\dots,m+1\}\}.
```

So the other first-shell orbit is obtained by removing the top star lower vertex while adding the
bottom nonzero upper vertex.

This is the second mixed principal-star class.

## Direct Boundary Calculation For The Five Shell Classes

This section proves something narrower than the full first-shell theorem:
it shows that every one of the five symbolic shell classes above satisfies

```math
\Delta(F)=m.
```

Write

```math
C_\star := \{A \in P_m : 0 \in A\},
\qquad
U_\star := \{B \in P_{m+1} : 0 \in B\}.
```

Also write

```math
L_0 := \{1,2,\dots,m\},
\qquad
U_0 := \{1,2,\dots,m+1\},
```
```math
L_{\mathrm{top}} := \{0,m+2,\dots,2m\},
\qquad
U_{\mathrm{top}} := \{0,m+1,\dots,2m\}.
```

For a two-layer family \(F=C \cup U\), we have the rank-split identity

```math
\partial^+F = (\partial^\uparrow C \setminus U) \sqcup \partial^\uparrow U,
```

with the first part in rank \(m+1\) and the second part in rank \(m+2\).

### Full-lower shell

Take

```math
C = P_m \setminus \{\{m+1,\dots,2m\}\},
\qquad
U = \{\{0,\dots,m\}\}.
```

Every set in \(P_{m+1}\) other than \(\{0,\dots,m\}\) still contains some \(m\)-subset in \(C\),
so

```math
|\partial^\uparrow C \setminus U| = |P_{m+1}| - 1.
```

Also \(U\) has exactly \(m\) supersets of size \(m+2\), so

```math
|\partial^\uparrow U| = m.
```

Since \(|C| = |P_m|-1 = |P_{m+1}|-1\), we get

```math
\Delta(F)
= (|P_{m+1}|-1+m) - (|P_m|-1)
= m.
```

### Principal-star pure upper move `(0,2)`

Take

```math
C = C_\star,
\qquad
U = (U_\star \setminus \{U_{\mathrm{top}}\}) \cup \{U_0\}.
```

Because \(\partial^\uparrow C_\star = U_\star\), the removed star upper vertex becomes the unique
rank-\(m+1\) boundary point:

```math
|\partial^\uparrow C \setminus U| = 1.
```

The star part of the rank-\(m+2\) boundary is unchanged, because deleting one star upper vertex
does not destroy any rank-\(m+2\) set containing \(0\). The new upper vertex \(U_0\) has
\(m\) supersets of size \(m+2\), exactly one of which contains \(0\) and is already in the star
boundary. So it contributes \(m-1\) new rank-\(m+2\) boundary points. Hence

```math
\Delta(F) = 1 + (m-1) = m.
```

### Principal-star pure lower move `(2,0)`

Take

```math
C = (C_\star \setminus \{L_{\mathrm{top}}\}) \cup \{L_0\},
\qquad
U = U_\star.
```

The new lower vertex \(L_0\) has exactly the \(m\) non-star supersets
\(L_0 \cup \{j\}\) with \(j \in \{m+1,\dots,2m\}\), and none of them lies in \(U_\star\). Thus

```math
|\partial^\uparrow C \setminus U| = m.
```

The rank-\(m+2\) boundary contributed by \(U_\star\) is unchanged, so again

```math
\Delta(F)=m.
```

### Principal-star mixed lower-add / upper-remove

Take

```math
C = C_\star \cup \{L_0\},
\qquad
U = U_\star \setminus \{U_{\mathrm{top}}\}.
```

The removed star upper vertex contributes one rank-\(m+1\) boundary point. The added lower vertex
\(L_0\) contributes the \(m\) non-star rank-\(m+1\) boundary points \(L_0 \cup \{j\}\) with
\(j \in \{m+1,\dots,2m\}\). So

```math
|\partial^\uparrow C \setminus U| = m+1.
```

The rank-\(m+2\) boundary remains the same as for the star template. Since \(|C|=|C_\star|+1\),
we get

```math
\Delta(F) = (|C_\star| + m + 1) - (|C_\star| + 1) = m.
```

### Principal-star mixed lower-remove / upper-add

Take

```math
C = C_\star \setminus \{L_{\mathrm{top}}\},
\qquad
U = U_\star \cup \{U_0\}.
```

There is no new rank-\(m+1\) boundary because \(\partial^\uparrow C \subseteq U_\star \subseteq U\).
The new upper vertex \(U_0\) contributes \(m-1\) new rank-\(m+2\) boundary points exactly as in
the pure-upper case. Since \(|C| = |C_\star|-1\), we obtain

```math
\Delta(F) = (|C_\star| + m - 1) - (|C_\star| - 1) = m.
```

So all five symbolic first-shell classes satisfy the same exact gap law

```math
\Delta(F)=m.
```

## Shifted Classification Of The Distance-`2` Shell Around The Two Model Templates

This section proves the classification statement that was previously only inferred from exact
computation.

We use the standard shifted order on \(k\)-subsets:
for

```math
A = \{a_1 < \cdots < a_k\},
\qquad
B = \{b_1 < \cdots < b_k\},
```

write

```math
A \preceq B
\qquad\Longleftrightarrow\qquad
a_i \le b_i \ \text{ for every } i.
```

A shifted family in a fixed rank is an initial segment of this order. Equivalently, its complement
inside that rank is an upper ideal.

### Extremal vertices in the relevant shifted orders

In rank \(m\):

- the unique maximal element of \(P_m\) is
  ```math
  \{m+1,m+2,\dots,2m\};
  ```
- the unique minimal non-star element of \(P_m \setminus C_\star\) is
  ```math
  L_0 = \{1,2,\dots,m\};
  ```
- the unique maximal star element of \(C_\star\) is
  ```math
  L_{\mathrm{top}} = \{0,m+2,\dots,2m\}.
  ```

In rank \(m+1\):

- the unique minimal element of \(P_{m+1}\) is
  ```math
  \{0,1,\dots,m\};
  ```
- the unique minimal non-star element of \(P_{m+1} \setminus U_\star\) is
  ```math
  U_0 = \{1,2,\dots,m+1\};
  ```
- the unique maximal star element of \(U_\star\) is
  ```math
  U_{\mathrm{top}} = \{0,m+1,\dots,2m\}.
  ```

These are immediate from the coordinatewise order \(\preceq\).

### Full-lower template

Assume \(F=C \cup U\) is shifted and

```math
|F \triangle F_{\mathrm{full}}| = 2.
```

Since \(F_{\mathrm{full}} = P_m\) has no upper part and \(F\) has the same total size as
\(P_m\), there must be exactly one deleted lower vertex and one added upper vertex:

```math
C = P_m \setminus \{L\},
\qquad
U = \{B\}.
```

Because \(C\) is shifted, its complement inside \(P_m\) is an upper ideal of size \(1\). Hence
\(L\) is the unique maximal element of \(P_m\), namely

```math
L = \{m+1,m+2,\dots,2m\}.
```

Because \(U\) is a shifted rank-\((m+1)\) family of size \(1\), it must be the unique minimal
element of \(P_{m+1}\), namely

```math
B = \{0,1,\dots,m\}.
```

So every shifted family at distance `2` from \(F_{\mathrm{full}}\) is exactly the unique
full-lower shell class recorded above.

### Principal-star template

Assume now that \(F=C \cup U\) is shifted and

```math
|F \triangle F_\star| = 2.
```

Since \(F\) and \(F_\star\) have the same total size, the symmetric difference consists of one
deleted template vertex and one added non-template vertex. There are therefore only four cases.

#### Case `(0,2)`: upper delete / upper add

Here

```math
C = C_\star,
\qquad
U = (U_\star \setminus \{R\}) \cup \{A\},
```

with \(R \in U_\star\) and \(A \in P_{m+1} \setminus U_\star\).

Because \(U\) is shifted and contains exactly one non-star upper vertex, that vertex must be the
unique minimal non-star upper element:

```math
A = U_0.
```

Because \(U \cap U_\star\) is a shifted subfamily of \(U_\star\) of codimension \(1\), the
deleted star upper vertex must be the unique maximal element of \(U_\star\):

```math
R = U_{\mathrm{top}}.
```

So this is exactly the pure-upper principal-star class.

#### Case `(2,0)`: lower delete / lower add

Here

```math
C = (C_\star \setminus \{R\}) \cup \{A\},
\qquad
U = U_\star,
```

with \(R \in C_\star\) and \(A \in P_m \setminus C_\star\).

Because \(C\) is shifted and contains exactly one non-star lower vertex, that vertex must be the
unique minimal non-star lower element:

```math
A = L_0.
```

Because \(C \cap C_\star\) is a shifted subfamily of \(C_\star\) of codimension \(1\), the
deleted star lower vertex must be the unique maximal star lower element:

```math
R = L_{\mathrm{top}}.
```

So this is exactly the pure-lower principal-star class.

#### Case `(1,1)`: lower add / upper remove

Here

```math
C = C_\star \cup \{A\},
\qquad
U = U_\star \setminus \{R\},
```

with \(A \in P_m \setminus C_\star\) and \(R \in U_\star\).

The same shiftedness argument forces

```math
A = L_0,
\qquad
R = U_{\mathrm{top}}.
```

So this is exactly the mixed lower-add / upper-remove class.

#### Case `(1,1)`: lower remove / upper add

Here

```math
C = C_\star \setminus \{R\},
\qquad
U = U_\star \cup \{A\},
```

with \(R \in C_\star\) and \(A \in P_{m+1} \setminus U_\star\).

Again shiftedness forces

```math
R = L_{\mathrm{top}},
\qquad
A = U_0.
```

So this is exactly the mixed lower-remove / upper-add class.

Putting the four cases together, every shifted family at distance `2` from \(F_\star\) is one of
the four principal-star classes listed above.

### Classification theorem for the model-template first shell

We have proved:

```math
\text{If } F \text{ is shifted and }
\bigl(|F \triangle F_{\mathrm{full}}| = 2 \text{ or } |F \triangle F_\star| = 2\bigr),
```
```math
\text{then } F \text{ is exactly one of the five symbolic shell classes above.}
```

Combining this classification with the direct boundary counts from the previous section gives the
model-template first-shell theorem

```math
\text{If } F \text{ is shifted and }
\bigl(|F \triangle F_{\mathrm{full}}| = 2 \text{ or } |F \triangle F_\star| = 2\bigr),
\quad\text{then}\quad
\Delta(F) = m.
```

So the first-shell problem is now reduced further:
the remaining gap is no longer the local classification around the two model templates, but the
global identification of the shifted equality set with those two templates and then the lift from
the distance-`2` shell to full shifted stability.

## Remaining Global Conjectural Theorem

What remains conjectural is the global version stated using the actual shifted equality set
\(\mathcal E\):

```math
\operatorname{dist}(F,\mathcal E)=2
\quad\Longrightarrow\quad
\Delta(F)=m.
```

The new content of this note proves the corresponding statement around the two model templates
\(F_{\mathrm{full}}\) and \(F_\star\). So the gap between this note and the full shifted
first-shell theorem is now only:

- prove that the shifted equality set \(\mathcal E\) is exactly
  \(\{F_{\mathrm{full}},F_\star\}\).

That would make the model-template first-shell theorem proved above identical to the actual
distance-`2` shell theorem needed on the stronger branch.

This remains the first real theorem on the way to the additive improvement

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor.
```

## Current Status

- The scalar first-shell law `\Delta(F)=m` is exact in shifted data through `n = 25`.
- The sharper move-type decomposition is exact through `n = 21`.
- The compact delta-signature output now isolates all five distance-`2` shifted shell orbits
  symbolically through `n = 21`:
  `1` full-lower orbit plus `4` principal-star orbits.
- Equivalently, the principal-star first shell now has an explicit four-class decomposition into
  one pure upper move, two mixed moves, and one pure lower move.
- The shifted `n = 23` decomposition probe now returns as well, with aggregate profile
  `entry_count = 6` and `pair_count = 7`, consistent with the same
  `2` equality entries plus `4` distance-`2` move-type entries.
- What is still missing computationally is a clean theorem-facing extraction of the exact `n = 23`
  move rows from the probe; even after the compact delta-signature refactor, `n = 23` is still
  not a short or medium run for the full row-level decomposition. So the fully tabulated move-type
  witness table in this note remains recorded only through `n = 21`.

So this note should now be read as:

- a proof of the shifted distance-`2` shell theorem around the two model templates
  \(F_{\mathrm{full}}\) and \(F_\star\);
- together with exact computational evidence that these are the right templates and that the same
  shell picture persists through much larger odd dimensions.
