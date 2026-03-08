# Note: Stronger Upper Theorem Needed for Full `k = 3`

Date: 2026-03-08

## Context

The original `k = 3` extremal function is

```math
r_3(N)=\max\Bigl\{|A|:\ A\subseteq\{1,\dots,N\},\ 
A\text{ contains no non-trivial 3-term arithmetic progression}\Bigr\}.
```

Here "non-trivial 3-term arithmetic progression" means a triple

```math
a,\ a+d,\ a+2d
```

with

```math
d\neq 0.
```

Equivalently:

```math
x,y,z\in A,\ x+z=2y \Longrightarrow x=y=z.
```

The original mathematical target for the `k = 3` branch is:

```math
\exists f:\mathbb{N}\to\mathbb{R}
\quad\text{such that}\quad
r_3(N)=\Theta(f(N))
\qquad (N\to\infty).
```

The repository now proves the strongest honest base-axiom `k = 3` source-backed split statement:

```math
L_3(N)=O(r_3(N)), \qquad r_3(N)=O(U_3(N)), \qquad L_3(N)=O(U_3(N)).
```

with

```math
L_3(N)\asymp N\exp\!\bigl(-c_\ell \sqrt{\log N}\bigr)
```

and current source-backed upper exponent

```math
\beta = \frac{1}{12}, \qquad
U_3(N)\asymp N\exp\!\bigl(-c_u(\log N)^\beta\bigr).
```

This does **not** yet yield a matched asymptotic profile

```math
r_3(N)=\Theta(f(N)).
```

## Exact Missing Sentences

### A. Exact sentence needed by the current formal matched-profile route

The current matched-profile route in the repository is built around one common superpolylog profile

```math
g_{\beta,c,C}(N):=
C\,N\exp\!\bigl(-c(\log(N+2))^\beta\bigr).
```

Its exact witness condition is:

```math
\exists \beta>0,\ \exists c>0,\ \exists C>0
\text{ such that }
r_3(N)=O(g_{\beta,c,C}(N))
\quad\text{and}\quad
g_{\beta,c,C}(N)=O(r_3(N)).
```

Expanded fully, this means:

```math
\exists \beta>0,\ \exists c>0,\ \exists C>0,\ 
\exists K_1>0,\ \exists K_2>0,\ \exists N_1,\ \exists N_2
```

such that

```math
\forall N\ge N_1,\quad
r_3(N)\le K_1\,C\,N\exp\!\bigl(-c(\log(N+2))^\beta\bigr),
```

and

```math
\forall N\ge N_2,\quad
C\,N\exp\!\bigl(-c(\log(N+2))^\beta\bigr)\le K_2\,r_3(N).
```

This is the exact kind of sentence needed to instantiate the current formal object
`K3ProfileWitness`.

### B. Exact comparison sentence missing from the current split-to-matched route

The repository already has a split sandwich of the form

```math
L_3(N)=O(r_3(N)),\qquad r_3(N)=O(U_3(N)),
```

with

```math
L_3(N)=C_\ell N\exp\!\bigl(-c_\ell\sqrt{\log(N+2)}\bigr),
```

and

```math
U_3(N)=C_u N\exp\!\bigl(-c_u(\log(N+2))^\beta\bigr).
```

So the exact missing comparison sentence on that route is

```math
U_3(N)=O(L_3(N)).
```

Expanded fully, this means:

```math
\exists K>0,\ \exists N_0,\ \forall N\ge N_0,
```

```math
C_u N\exp\!\bigl(-c_u(\log(N+2))^\beta\bigr)
\le
K\,C_\ell N\exp\!\bigl(-c_\ell\sqrt{\log(N+2)}\bigr).
```

If this comparison held, then together with the already-proved

```math
L_3(N)=O(r_3(N))
\quad\text{and}\quad
r_3(N)=O(U_3(N)),
```

the branch would collapse to one matched asymptotic profile.

### C. Stronger upper theorem that would solve the branch mathematically

A mathematically natural theorem strong enough to close the `k = 3` branch is:

```math
\exists c>0,\ \exists C>0,\ \exists N_0\in\mathbb{N}
\text{ such that }
\forall N\ge N_0,\quad
r_3(N)\le C\,N\exp\!\bigl(-c\sqrt{\log(N+2)}\bigr).
```

Equivalently,

```math
r_3(N)=O\!\left(N\exp(-c\sqrt{\log(N+2)})\right).
```

This is not the same as the current `K3ProfileWitness` interface, but it is the clean
mathematical strengthening one would most naturally want.

## Connection Back to the Original Problem

The currently proved lower theorem is a Behrend-type lower bound:

```math
N\exp\!\bigl(-c'\sqrt{\log(N+2)}\bigr)=O(r_3(N)).
```

So if one could prove the stronger upper theorem from Section `C`, then the branch would have
matching upper and lower scales of square-root-log type. That would be the mathematically natural
route to a full asymptotic-formula theorem for `r_3(N)`.

## Sufficient Comparison Forms

Any one of the following would be sufficient for the current formal route:

1. A direct Behrend-scale upper theorem:

   ```math
   r_3(N)=O\!\left(N\exp(-c\sqrt{\log(N+2)})\right).
   ```

2. A superpolylog upper theorem with exponent strictly larger than one half:

   ```math
   r_3(N)=O\!\left(N\exp(-c(\log(N+2))^\beta)\right),
   \qquad \beta>\frac12.
   ```

3. A borderline square-root theorem with explicit constant comparison:

   ```math
   r_3(N)=O\!\left(N\exp(-c_u\sqrt{\log(N+2)})\right)
   ```

   with `c_u` strong enough to dominate the Behrend lower-side constant.

## Current Obstruction

The current source-backed import fixes

```math
\beta = \frac{1}{12},
```

so option `2` is not supplied by the existing literature layer in this repository.

Therefore the full `k = 3` asymptotic-formula theorem remains blocked, while the
source-backed split theorem is complete.

## Internet Literature Check (2026-03-08)

Search outcome:

- I did **not** find a publication proving the Behrend-scale upper theorem

  ```math
  r_3(N)=O\!\left(N\exp(-c\sqrt{\log(N+2)})\right).
  ```

- I also did **not** find a publication stating that theorem as an established result.

What I did find are weaker published/preprint upper bounds:

1. Bloom--Sisask (2020):

   ```math
   r_3(N)\ll \frac{N}{(\log N)^{1+c}}
   ```

   for some `c>0`.

2. Kelley--Meka (2023/2024 arXiv version):

   ```math
   r_3(N)\le N\exp\!\bigl(-c(\log N)^\beta\bigr)
   ```

   for some `\beta>0`; the currently imported source-backed exponent in this repository is

   ```math
   \beta=\frac{1}{12}.
   ```

3. Bloom--Sisask improvement to the Kelley--Meka-type regime:

   ```math
   r_3(N)\le N\exp\!\bigl(-c(\log N)^{1/9}\bigr).
   ```

Conclusion:

```text
the Behrend-scale upper theorem remains a natural strengthening target,
not a theorem currently supported by the sources audited for this repository.
```

Primary sources checked:

- Bloom--Sisask, "Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions":
  https://arxiv.org/abs/2007.03528
- Kelley--Meka, "Strong bounds for 3-progressions":
  https://arxiv.org/abs/2302.05537
- Bloom--Sisask, "An improvement to the Kelley--Meka bounds on three-term arithmetic progressions":
  https://arxiv.org/abs/2309.02353
