# A Lean proof of an improved bound for Green's Problem 22

This repository formalizes a solution to the target `Green22.green_22` of Ben Green's Problem 22
(monochromatic sums and products), as registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/22.lean).
Let `N₀(r)` be the least `N` such that every `r`-colouring of `{1, ..., N}` contains integers
`x, y ≥ 3` for which `x + y` and `xy` lie in `{1, ..., N}` and have the same colour. The theorem is

```text
N₀(r) ≤ ⌈exp(exp(r^43))⌉   for all sufficiently large r,
```

and `⌈exp(exp(r^43))⌉ = o(exp(exp(r^50)))`, where `exp(exp(r^50))` is the bound of Green and
Sawhney. The proof is complete: it includes the inverse theorem of Green and Sawhney
(their Proposition 5.1) and every analytic input it needs, so nothing is assumed beyond mathlib.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-22-exponent-43%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen22Exponent43Lean4Web.lean)
(Lean4Web project "Latest Mathlib" with Lean v4.35.0-rc3; the file is about 26,000 lines long, so
elaboration takes several minutes)

This does **not** determine the true order of growth of `N₀(r)`.

## Formal Conjectures target

The file in `lean/` imports the Formal Conjectures statement and proves it with the answer
`r ↦ ⌈exp(exp(r^43))⌉`. The definitions `HasMonochromaticSumProduct`, `N₀` and
`GreenSawhneyBound` are the ones imported from Formal Conjectures, and the statement is the
Formal Conjectures one with only the answer hole filled:

```lean
theorem Green22.green_22_solved :
    let ans := (answer(fun r => ⌈Real.exp (Real.exp (r ^ 43))⌉₊) : ℕ → ℝ)
    ∀ᶠ r in atTop, N₀ r ≤ ans r ∧
    ans =o[atTop] GreenSawhneyBound
```

Thus the theorem `Green22.green_22` can be changed from `research open` to `research solved` by
replacing `answer(sorry)` with `answer(fun r => ⌈Real.exp (Real.exp (r ^ 43))⌉₊)` and using this
proof. The file in `lean4web/` copies the three definitions and the `answer( )` syntax of Formal
Conjectures and proves the same statement under the name `Green22.green_22`.

**Remark on the target.** Right after their Theorem 1.1, Green and Sawhney remark that minor
tweaks to their numerics would replace `50` by a slightly smaller constant, and that a constant
below `10`, say, would appear to require new ideas. So the qualitative little-o statement was
anticipated there. What is new here is the explicit exponent `43`, obtained by summing over colours
instead of fixing one (section 2 below), together with a complete kernel-checked proof.

## Mathematical explanation (AI generated)

GS denotes B. Green and M. Sawhney, *Bounds for monochromatic solutions to $`\{x+y,xy\}`$*,
arXiv:2511.09365v2. All logarithms are natural, $`\mathbb E^{\log}`$ denotes logarithmic
averages (weights $`1/n`$), and

```math
\Pi_{q,H}f(n)=\mathbb E_{h,h'\le H}\,f(n+q(h-h')),\qquad
\|f\|^2_{U^1_{\log}[N;q,H]}=\mathbb E^{\log}_{n\le N}\bigl|\mathbb E_{h\le H}f(n+qh)\bigr|^2 .
```

### 1. The strategy and the parameters

The argument follows GS, but it keeps all colours and all initial indices together until the very
end. Three devices remove the factors of $`r`$ that GS lose by pigeonholing a colour:

- positivity is proved for the sum over colours;
- the energy increment is summed over a subpartition of unity;
- random signs let the scalar inverse theorem control a sum over all colours.

Every parameter is an integer power of $`r`$:

- $`K=t=r^7`$, $`d=r^4`$, $`\delta=1/d`$;
- $`V=(d^C)!`$, where $`C`$ is the constant of GS Proposition 5.1;
- $`b_j=V^{4^j}`$, $`L=r^{28}`$;
- $`H_{i,j}=\lfloor\exp\exp(L(4Ki+j))\rfloor`$;
- $`M=\lceil\exp\exp(r^{43})\rceil`$.

$`\mathscr P_{i,h}`$ is the set of primes in $`[H_{i,2h-1},H_{i,2h})`$; by Mertens' theorem its
logarithmic mass is $`\asymp L`$. The scales satisfy $`\log\log H_{t,2K}\approx 4KtL=4r^{42}`$,
far below $`\log\log M\approx r^{43}`$. Consecutive scales are separated by arbitrarily large
fixed powers.

### 2. The colour-summed argument

Let $`A_1,\dots,A_r`$ be the colour classes of a colouring of $`[1,M]`$, and put
$`f_{a,c}(n)=1_{A_c}(b_an)`$. For each $`a`$ the functions $`(f_{a,c})_c`$ form a subpartition of
unity.

**Positivity.** Fix a row $`i`$ and choose primes $`p_h\in\mathscr P_{i,h}`$. Put
$`T_{a,j}=p_{a+1}\cdots p_j`$. For almost all $`n`$, Cauchy–Schwarz over colours gives
$`\sum_c(\sum_j 1_{A_c}(b_jT_{0,j}n))^2\ge K^2/r`$. Discard the pairs $`(a,j)`$ with
$`|j-a|\le1`$ and remove the common prefix $`p_1\cdots p_a`$ by prime dilation (GS Lemma A.5).
This gives

```math
S_i=\sum_{a<j-1}\sum_c\mathbb E^{\log}_{n,p}\,f_{a,c}(n)\,1_{A_c}(b_jT_{a,j}n)\ \gg\ K^2/r .
```

The colour sum stays 1-bounded during the dilation, so no factor $`r`$ is lost. This holds for
every row $`i`$; no colour and no index $`a`$ is selected.

**Projections.** Put $`q_{a,j}=(b_j/b_a^2)V`$. GS (6.4) with $`\eta\asymp r^{-2}`$ gives, for each
pair and colour, $`\langle\Pi f,g\rangle\ge\frac\eta8\langle f,g\rangle-\frac{\eta^2}8`$ for the
small projection $`\Pi=\Pi_{q_{a,j-1},H_{i+1,0}}`$. Then GS Lemma 6.2 shifts the argument by
$`s_{a,j}=(b_j/b_a^2)T_{a,j}`$, which is a multiple of $`q_{a,j-1}`$. Summing over colours, pairs
and the $`t`$ rows gives a total $`\mathcal S\gg K^3/r^3`$.

**Energy.** Put $`X_{i,j,c}=\|\Pi_{q_{a,j},H_{i,0}}f_{a,c}\|^2`$. By GS Lemma 6.4 (approximate
Pythagoras), the squared distance between the large and the small projection is at most
$`X_{i,j,c}-X_{i+1,j-1,c}`$ up to negligible errors. Summing over the grid $`(i,j)`$ telescopes along
diagonals, and $`\sum_cX_{i,j,c}\le1`$ because the projections of a subpartition are a
subpartition. So the total energy is $`O(K(t+K))`$, not $`O(rK(t+K))`$. Cauchy–Schwarz then shows
that replacing small by large projections costs $`O(K^{5/2})=o(\mathcal S)`$.

**Random signs.** For fixed $`(i,a,j)`$, write the remaining error as a sum over colours. With
independent signs $`\sigma_c`$, put $`u_\sigma=\sum_c\sigma_cf_{a,c}`$ and
$`v_\sigma=\sum_c\sigma_c1_{A_c}(b_a^2\,\cdot)`$. Both are 1-bounded, and averaging over
$`\sigma`$ recovers the colour sum exactly. If the error exceeded $`2\delta`$, some choice of signs
would give a correlation $`\ge\delta`$ of the scalar form

```math
\mathbb E^{\log}_{n,p,p'}\,F(n+\lambda pp')\,G(\lambda npp').
```

GS Proposition 5.1 would then force $`\|u_\sigma-\Pi u_\sigma\|_{U^1_{\log}[M;\lambda V,H_{i,0}^2]}\gg\delta^{O(1)}`$,
while GS Lemma 6.3 bounds this norm by $`H_{i,0}^{-1}`$. Hence every error is at most $`2\delta`$,
with no factor $`r`$. The total of these errors is at most $`K^3\delta=o(K^3/r^3)`$.

**Extraction.** What remains is a positive sum of nonnegative terms
$`f_{a,c}(n+\lambda T)\,1_{A_c}(b_jTn)`$. A nonzero term gives $`x=b_an`$ and
$`y=(b_j/b_a)T`$ with $`x+y=b_a(n+\lambda T)`$ and $`xy=b_jTn`$ in the same colour class.

### 3. GS Proposition 5.1 by an elementary route

GS prove their inverse theorem with a majorant for the primes (their Lemma 4.1) and with
diophantine properties of almost-prime sets (their Lemma 3.2). The latter uses the
Siegel–Walfisz theorem and logarithm-free exponential sums over primes (their Appendix B). Here
these inputs are replaced by statements that need only elementary number theory.

**Fejér-positive diophantine sets.** Let
$`\Phi_T(\alpha)=|T^{-1}\sum_{t\le T}e(\alpha t)|^2`$. A finite set $`S\subset\mathbb Z`$ is
*FPD* with parameters $`(T,D,\eta,Q_0,W)`$ if every $`\theta`$ with
$`\mathbb E_{s\in S}\Phi_T(\theta s)\ge\eta`$ satisfies $`\|q\theta\|\le W/(TD)`$ for some
$`1\le q\le Q_0`$. This is exactly what the proofs of GS Lemmas 2.4–2.6 use.

- **Lemma L (products of primes).** Suppose few pairs of $`S\subset[Y,2Y]`$ share a factor. Then
  $`S`$ is FPD with $`Q_0=1`$. Two coprime $`s,s'`$ with $`\theta s`$ and $`\theta s'`$ both near
  integers force $`\theta`$ near an integer, by Bézout's identity. The almost primes
  $`p_1\cdots p_k`$ with $`p_\ell`$ in disjoint intervals are almost always coprime.
- **Lemma Q (squares).** For $`\{x^2-c\}`$, look at a good triple $`x,y,z`$: the numbers
  $`x^2-y^2`$ and $`x^2-z^2`$ have a small gcd, which bounds the denominator $`q`$. Good triples
  exist by a counting argument. It uses the divisor bound $`\#\{x \bmod d: x^2\equiv b\}\le2\tau(d)`$,
  a Rankin-type tail bound, and Brun–Titchmarsh in progressions.
- **Lemmas 2.4 and 2.6 in FPD form** are proved by discrete Fourier analysis on
  $`\mathbb Z/P\mathbb Z`$ (Parseval) instead of integrals. This is shorter than GS and gives
  $`\delta^2/(100Q_0)`$ in the conclusion.
- **GS Lemma 4.1 (the majorant).** Take Selberg's majorant
  $`\tilde\Lambda=G\cdot\beta`$, with $`\beta(n)=(\sum_{d\mid n,\,d\le R}\lambda_d)^2`$. Expand it
  in Ramanujan sums: $`\beta=\sum_{q\le R^2}C_q\,c_q`$. The coefficients are explicit:
  $`C_1=1/G`$ and $`|C_q|\le3^{\omega(q)}/(G\varphi(q))`$. This gives GS (4.1)–(4.6) and (4.17).
  Summing the same expansion over an arithmetic progression gives Brun–Titchmarsh in
  progressions:
  ```math
  \#\{u\le p<u+y:\ p\equiv b\ (d)\}\le 40\cdot4^{\omega(d)}\,\frac{y}{d\log y}\qquad(d^{10}\le y).
  ```
- **Mertens' theorems** are proved with explicit constants.
  - The first theorem comes from Legendre's formula for $`\log n!`$, Chebyshev's bound
    $`\prod_{p\le n}p\le4^n`$, and $`n\log n-n\le\log n!\le n\log n`$.
  - The second theorem, $`\log\log n-4.5\le\sum_{p\le n}1/p\le\log\log n+3.4`$, then follows by
    partial summation.
  - This replaces the use of PrimeNumberTheoremAnd in the development.

The body of GS §5 is split into 22 independently proved steps. Each step is a Lean theorem;
`prop51_of_leaves` assembles them into Proposition 5.1.

- **The branch (5.9).** Cauchy–Schwarz reduces it to the box average of GS (2.12). Lemma 2.6 in
  FPD form with Lemma L gives step lengths $`q_1=q_2=1`$. The Fourier kernel is then nonnegative,
  so $`2H^2\cdot\text{box}\le\max_\theta|\hat\psi(\theta)|^2`$ follows without the
  $`L^{4/3}`$ estimate of GS. This contradicts (4.4)–(4.6).
- **The branch (5.10).** Periodicity of $`\Lambda_{\mathrm{per}}`$, Cauchy–Schwarz, and near-coprimality
  of almost primes (GS Lemma 5.2) lead to GS (5.26). The boxes are then restricted so that the last
  factor is rich in primes. Lemma R gives the hypotheses of Lemma Q, Lemma Q gives FPD for the
  squares, and Lemma 2.4 in FPD form and GS Lemma A.6 finish.

Formalization found three places that needed care:

- GS Lemma 6.4 needs $`q'\ge1`$.
- Proposition 5.1 is used with the extra hypothesis $`P_2\ge4P_1`$. This is a weaker statement,
  and it lets GS (5.4) use Chebyshev's bounds instead of the prime number theorem.
- The passage (5.12)→(5.13) drops logarithmic weights from a signed average. Here it keeps a
  weight $`\rho\in[1/4,1]`$ instead.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `2424bb48...` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `5e0c4e52...`) |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`. The proof file concatenates the modules of the development, one section per
module. The section headers `/- ## Section: ... -/` mark the parts listed above.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked. The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem. Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is proved here:

```text
N₀(r) ≤ ⌈exp(exp(r^43))⌉ for all sufficiently large r;
hence N₀(r) = o(exp(exp(r^50))).
```

What remains open:

```text
The true order of growth of N₀(r) (Green's question "find reasonable bounds").
```

Green and Sawhney also give an explicit colouring showing that `N₀(r)` grows at least
exponentially in `r`, so the truth lies between exponential and doubly exponential.

## Sources

- B. Green, *100 open problems*, Problem 22,
  [open-problems.pdf](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
- [Formal Conjectures: `GreensOpenProblems/22.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/22.lean)
- B. Green and M. Sawhney, *Bounds for monochromatic solutions to {x + y, xy}*,
  [arXiv:2511.09365](https://arxiv.org/abs/2511.09365)
- J. Moreira, *Monochromatic sums and products in ℕ*, Ann. of Math. 185 (2017)
- F. K. Richter, *Sums and products in sets of positive density*,
  [arXiv:2507.00515](https://arxiv.org/abs/2507.00515)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from OpenAI Codex, and Claude Code using Claude Opus 5.5.

## Appendix: relation to previous work (AI generated)

### What was known

- **Existence.** Moreira (2017) proved that $`N_0(r)`$ exists; in fact $`x`$ can also be taken of
  the same colour. His main proof uses topological dynamics and gives no bound. Green's comments
  on the problem note that the elementary proof in §5 of that paper gives a bound in principle,
  but an extremely weak one.
- **The Green–Sawhney bound.** Green and Sawhney (2025), building on ideas of Richter, proved
  $`N_0(r)\le\exp\exp(r^{50})`$ for $`r\ge r_0`$. In the 2025 update of his problem list, Green
  writes that this "arguably addresses the original formulation of the problem".
- **What Green and Sawhney say about improving it.** Right after their Theorem 1.1, they remark
  that minor tweaks to the numerics of their argument would replace $`50`$ by a slightly smaller
  constant. They also say that a small constant, below $`10`$ say, would seem to need new ideas.
  In their §8 they explain why going below a double exponential looks hard with their methods:
  - the highly divisible set $`B_0`$ already has elements of doubly exponential size in $`r`$;
  - Proposition 5.1 needs a hierarchy of prime scales whose reciprocal sums are $`\gg1`$.
- **Lower bound.** Green and Sawhney also give a colouring of $`[\tfrac12(3^r+7)]`$ without the
  pattern. So $`N_0(r)`$ grows at least exponentially, and their bound is at most one logarithm
  from the truth.
- **Formal Conjectures.** `Green22.green_22` asks for an explicit answer that bounds $`N_0(r)`$
  for large $`r`$ and is $`o(\exp\exp(r^{50}))`$, that is, an improvement on the Green–Sawhney bound.
  By the remark above, the qualitative statement was expected from their method. The target is
  still `research open` in Formal Conjectures.

### What this repository adds

1. **An explicit exponent, from structural changes rather than numerics.**
   - Green and Sawhney fix one colour class at the very start of the proof, by pigeonhole, so its
     density is only $`\gg1/r`$.
   - Later, for each row of scales, they pigeonhole the initial index $`j'`$ and pass to a
     $`1/K`$-fraction of the rows (their §7, with $`K=r^8`$).
   - The argument here keeps all colours and all initial indices (section 2 above). Positivity is
     proved for the sum over colours. The energy increment is summed over a subpartition, which
     costs no factor $`r`$. Random signs let the scalar Proposition 5.1 control the whole colour
     sum.
   - With these factors gone, the parameters can be taken as $`K=r^7`$, $`\delta=r^{-4}`$ and
     $`L=r^{28}`$, which gives $`N_0(r)\le\lceil\exp\exp(r^{43})\rceil`$.
   - The exponent $`43`$ is not optimised. The formalization uses integer powers of $`r`$, and it
     uses Proposition 5.1 with the width condition $`k\delta^{-5}`$ instead of GS's
     $`k\delta^{-4.1}`$. A pen-and-paper version with fractional powers of $`r`$ and GS's width
     condition suggests the exponent $`31`$. That refinement is **not** formalized here.
2. **The inverse theorem without Siegel–Walfisz.**
   - GS prove Proposition 5.1 with diophantine properties of almost primes (their Lemma 3.2).
     Their Appendix B supplies these with logarithm-free exponential sums over primes and the
     Siegel–Walfisz theorem. They mention that possible Siegel zeros are one reason why computing
     $`r_0`$ would be painful.
   - Here Proposition 5.1 is proved by the elementary route of section 3:
     - Fejér-positive diophantine sets (Lemma L for products of primes, Lemma Q for their squares);
     - GS Lemma 4.1 from a Selberg majorant expanded in Ramanujan sums;
     - Brun–Titchmarsh in progressions from the same expansion;
     - Chebyshev's bounds and an elementary proof of Mertens' theorems.
   - No $`L`$-functions, no prime number theorem and no exponential sums over primes are used.
3. **A complete formal verification.**
   - Everything is checked by the Lean kernel with only the standard axioms: the colour-summed
     argument, GS Proposition 5.1, every lemma it uses, and the analytic inputs. The lemmas are
     GS Lemmas 4.1, 5.2, 6.2–6.5 and A.1–A.6, together with FPD forms of GS Lemmas 2.4–2.6.
   - Formalization also located three places in GS that need care; they are listed at the end of
     section 3.

| | Green–Sawhney (2025) | This repository |
|---|---|---|
| Bound | $`\exp\exp(r^{50})`$ (a slightly smaller exponent by tuning, per their remark) | $`\lceil\exp\exp(r^{43})\rceil`$ |
| Colours | one colour class fixed by pigeonhole | all colours kept; random signs |
| Initial index | pigeonholed, losing a factor $`K`$ | all kept |
| Inverse theorem | Siegel–Walfisz, exponential sums over primes, prime number theorem | FPD sets, Selberg majorant, Brun–Titchmarsh, Chebyshev, Mertens |
| Verification | paper proof | Lean 4, `[propext, Classical.choice, Quot.sound]` |

Neither approach goes below a double exponential. The gap to the exponential lower bound remains
open.
