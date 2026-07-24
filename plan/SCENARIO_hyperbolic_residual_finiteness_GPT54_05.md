# Scenario: Hyperbolic residual finiteness, GPT54_05

We keep the concrete triple from the previous scenario:

```text
G = 𝒢_{HB_2^{(2)}}(7),    H = <a,b>,    g = c.
```

The only question here is whether the explicit Caprace–Conder–Kaluba–Witzel finite-quotient family already separates `c` from `<a,b>`.

## 1. Explicit quotient map

CCKW, Section 7.3, first construct epimorphisms from every hyperbolic KMS group over `𝐅_p` onto `𝒢_{Ã_2}(p)`, “sending each generator of the source KMS group to a generator of the target KMS group” (Section `sec:KMS-epim`, Figure `fig:Epimor-KMS`). In particular there is a surjection

```text
π : 𝒢_{HB_2^{(2)}}(7) → 𝒢_{Ã_2}(7)
```

with

```text
π(a)=a,   π(b)=b,   π(c)=c.
```

CCKW then give an explicit representation of `𝒢_{Ã_2}(p)` (Proposition `prop:Morphism-A2t`, Section `sec:KMS-A2t`):

```text
a ↦ A = [[1,1,0],[0,1,0],[0,0,1]],
b ↦ B = [[1,0,0],[0,1,1],[0,0,1]],
c ↦ C(T) = [[1,0,0],[0,1,0],[T,0,1]]
```

inside `SL_3(𝐅_p[T])`.

For every `e ≥ 3`, Corollary `cor:SL(3,q)-quotients` composes this with a quotient map `𝐅_p[T] ↠ 𝐅_q`, `q=p^e`, and proves the resulting map onto `SL_3(𝐅_q)` is surjective.

Take the concrete case `p=7`, `e=3`, `q=7^3`. Choose any surjection

```text
ψ : 𝐅_7[T] ↠ 𝐅_{7^3}
```

(for example by quotienting by any irreducible cubic over `𝐅_7`) and let `t = ψ(T) ∈ 𝐅_{7^3}`. Then the required finite quotient map is

```text
ρ = ψ_* ◦ ρ_{Ã_2} ◦ π : 𝒢_{HB_2^{(2)}}(7) → SL_3(𝐅_{7^3}),
```

with exact images

```text
ρ(a) = A = [[1,1,0],[0,1,0],[0,0,1]],
ρ(b) = B = [[1,0,0],[0,1,1],[0,0,1]],
ρ(c) = C = [[1,0,0],[0,1,0],[t,0,1]].
```

The source locations are exactly:

- generator-preserving KMS epimorphisms: Section `sec:KMS-epim`, Figure `fig:Epimor-KMS`;
- explicit matrices: Proposition `prop:Morphism-A2t`;
- surjectivity onto `SL_3(𝐅_{7^3})`: Corollary `cor:SL(3,q)-quotients`.

## 2. Direct relator check

The presentation of `G = 𝒢_{HB_2^{(2)}}(7)` is

```text
<a,b,c |
 a^7, b^7, c^7,
 [a,b,a], [a,b,b],
 [c,b,c], [c,b,b,c], [c,b,b,b],
 [c,a,c], [c,a,a,c], [c,a,a,a] >.
```

A direct matrix calculation verifies these relators.

First, since `A = I + E_{12}`, `B = I + E_{23}`, `C = I + tE_{31}` with `E_{ij}^2 = 0`, over characteristic `7` one has

```text
A^7 = B^7 = C^7 = I.
```

Next,

```text
[A,B] = I + E_{13},
```

and `E_{13}` commutes with both `E_{12}` and `E_{23}`, hence

```text
[A,B,A] = [A,B,B] = I.
```

Similarly,

```text
[C,B] = I + tE_{21},
[C,A] = I - tE_{32},
```

and now `E_{21}` commutes with `E_{31}` and satisfies

```text
[E_{21},E_{23}] = E_{21}E_{23} - E_{23}E_{21} = 0,
```

so the iterated commutators required in the `b`-branch vanish:

```text
[C,B,C] = [C,B,B,C] = [C,B,B,B] = I.
```

Likewise `E_{32}` commutes with `E_{31}` and satisfies

```text
[E_{32},E_{12}] = 0,
```

so the iterated commutators in the `a`-branch vanish:

```text
[C,A,C] = [C,A,A,C] = [C,A,A,A] = I.
```

Thus the defining relators of `𝒢_{HB_2^{(2)}}(7)` hold for `(A,B,C)`.

As for the image: by Corollary `cor:SL(3,q)-quotients`, the composite map to `SL_3(𝐅_{7^3})` is surjective. So this is not merely a homomorphism into a finite matrix group; it is the claimed finite quotient.

## 3. Does `ρ(c)` lie in `<ρ(a),ρ(b)>`?

No.

Indeed, both `A` and `B` are upper-unitriangular matrices. Therefore every element of the subgroup

```text
<ρ(a),ρ(b)> = <A,B>
```

is upper unitriangular, because the upper-unitriangular subgroup `U_3(𝐅_{7^3})` is closed under multiplication and inversion.

Concretely, every element of `<A,B>` has the form

```text
[[1,x,z],[0,1,y],[0,0,1]]
```

with zero `(3,1)`-entry.

But

```text
ρ(c) = C = [[1,0,0],[0,1,0],[t,0,1]]
```

has `(3,1)`-entry equal to `t`.

Because `ψ : 𝐅_7[T] ↠ 𝐅_{7^3}` is surjective, `t = ψ(T)` is not zero: if `t=0`, then `ψ` would factor through `𝐅_7[T]/(T) ≅ 𝐅_7`, impossible since the target has size `7^3`.

Hence `ρ(c)` is lower-unitriangular and is not upper unitriangular, so

```text
ρ(c) ∉ <ρ(a),ρ(b)>.
```

This is a fully structural separation argument; no computer algebra is needed.

## 4. Consequence for the triple `(G,<a,b>,c)`

Since `ρ` is a finite quotient of `G` and

```text
ρ(c) ∉ ρ(<a,b>) = <ρ(a),ρ(b)>,
```

the concrete triple chosen in the previous scenario is separated by a finite quotient.

Therefore it cannot serve as a profinite-nonseparability witness.

## 5. What exactly has been falsified?

This does **not** settle the global conjecture and does **not** prove anything universal about all finite quotients of all KMS groups. It only decisively classifies the previously proposed explicit triple:

```text
G = 𝒢_{HB_2^{(2)}}(7),   H=<a,b>,   g=c.
```

For this triple, the CCKW quotient family already gives a finite quotient separating `g` from `H`.

The KMS triple is falsified by the quotient: composing the generator-preserving epimorphism `𝒢_{HB_2^{(2)}}(7) ↠ 𝒢_{Ã_2}(7)` with CCKW’s explicit matrix representation and any quotient `𝐅_7[T] ↠ 𝐅_{7^3}` yields a surjection `ρ : G → SL_3(𝐅_{7^3})` with `ρ(a),ρ(b)` upper unitriangular and `ρ(c) = I + tE_{31}` (`t ≠ 0`), so `ρ(c) ∉ <ρ(a),ρ(b)> = ρ(<a,b>)`.
