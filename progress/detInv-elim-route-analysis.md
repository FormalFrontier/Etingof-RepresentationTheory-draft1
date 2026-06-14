# `detInv_elim_of_polynomial` — route analysis and decomposition (issue #4683)

This note records why `detInv_elim_of_polynomial`
(`Chapter5/PolynomialRepEmbedding.lean`) is the genuine deep core of
Theorem 5.23.2(i)'s polynomial case, why the elementary routes fail, and the
concrete decomposition into sub-issues that replaces it.

## The statement

Given an algebraic representation `M` of `GL_N(k)` (matrix coefficients in
`k[Xᵢⱼ, D]`, `D = det⁻¹`) whose `ℕ`-indexed weight spaces span `M` (`h_span`),
produce a basis `b` and **bare-entry** polynomials `Q a c ∈ k[Xᵢⱼ]` (no `D`)
with `b.repr (M.ρ g (b c)) a = eval (gᵢⱼ) (Q a c)` for all `g ∈ GL_N`.

Equivalently: clearing denominators `f_{ac} = Q_{ac}/det^r` for a common `r`,
show `det^r ∣ Q_{ac}` (in the UFD `k[Xᵢⱼ]`), i.e. the minimal `r` is `0`.

## Why the elementary routes are insufficient (verified)

Pick a **weight basis** (available: `glWeightSpace_iSupIndep` +
`DirectSum.IsInternal` under `h_span`, see `FormalCharacterIso.lean:236,274`).
For `b_c` of weight `μ_c ∈ ℕ^N` and `b_a` of weight `μ_a ∈ ℕ^N`, the
two-sided torus eigen-relation
`M.ρ (diag t) b_e = (∏ᵢ tᵢ^{(μ_e)ᵢ}) b_e` gives, for the cleared numerator,

```
Q_{ac}(diag(t) · g · diag(s)) = (∏ᵢ tᵢ^{(μ_a)ᵢ + r})(∏ⱼ sⱼ^{(μ_c)ⱼ + r}) Q_{ac}(g).
```

So `Q_{ac}` is **multi-homogeneous**: every monomial `X^A` in it has
row-sums `∑ⱼ A_{ij} = (μ_a)ᵢ + r` and column-sums `∑ᵢ A_{ij} = (μ_c)ⱼ + r`.

**Multi-homogeneity does NOT imply `det^r ∣ Q`.** Counterexample (`N=2, r=1`):
`α·g₁₁g₂₂ + β·g₁₂g₂₁` is row/column multi-homogeneous of degree `1`, yet
`det = g₁₁g₂₂ − g₁₂g₂₁` divides it only when `α = −β`. Crucially this
counterexample has **both** torus weights `≥ 0`, so neither one-sided nor
two-sided torus-weight nonnegativity is enough. The constraint forcing
divisibility must come from the **full `GL` action**, not just the torus.

(This is the `matrixCoeff_isHomogeneous` story carried one step further; that
lemma — already proven — extracts the *aggregate/central* homogeneity from
`h_scalar`. det⁻¹ elimination needs the *individual* weight nonnegativity, and
even that, as just shown, is not enough at the torus level.)

## The genuine content (the kernel lemma)

The matrix coefficients of `M` span a finite-dimensional subspace
`W = span{f_{ac}} ⊆ O(GL_N) = k[Xᵢⱼ, det⁻¹]` that is **stable under right
translation** by `GL_N` (`f_{ac}(g·h)` re-expands in the `f`'s, since
`M.ρ(gh) = M.ρ(g)M.ρ(h)`), and `W ≅ M` as a right `GL_N`-rep. Its torus weights
are exactly `{μ_c} ⊆ ℕ^N`. The theorem reduces to:

> **(K) Kernel lemma.** A finite-dimensional right-`GL_N`-subrepresentation
> `W ⊆ k[Xᵢⱼ, det⁻¹]` all of whose torus weights lie in `ℕ^N` is contained in
> `k[Xᵢⱼ]`.

(K) is essentially the polynomial-weight half of the Peter–Weyl decomposition
for `GL_N` (Theorem 5.23.2(ii)): as a `GL×GL`-rep,
`k[Xᵢⱼ, det⁻¹] = ⊕_{λ dominant ∈ ℤ^N} V_λ* ⊠ V_λ`, and the polynomial subring
`k[Xᵢⱼ]` is exactly the sum over `λ ∈ ℕ^N` (dominant, nonnegative). A subrep
with weights `≥ 0` involves only nonnegative `λ`, hence lands in `k[Xᵢⱼ]`. The
`Sym²(V) ⊗ det⁻¹` example (ℤ-weights `(1,−1),(0,0),(−1,1)`) is excluded
precisely because it has a negative weight, so its `ℕ`-indexed weight spaces do
not span — i.e. `h_span` fails.

The repo already has substantial coordinate-ring infrastructure to build on:
`Theorem5_23_2.lean` (`GLCoordinateRing`, `DominantWeight`, `AlgIrrepGL`,
`glCoordinateRing_rank`, `Theorem5_23_2_ii` — the Peter–Weyl rank statement),
`PolynomialTensorBridge.lean`, `PolynomialGLDecomposition.lean`.

## Decomposition

- **Sub-issue (K): the kernel lemma.** Prove (K) — a nonneg-weight finite-dim
  right-`GL_N`-subrep of `k[Xᵢⱼ, det⁻¹]` lies in `k[Xᵢⱼ]`. This is the real
  mathematics; expect it to lean on the `Theorem5_23_2.lean` coordinate-ring /
  Peter–Weyl machinery and may itself decompose (e.g. an `r`-minimal /
  det-divisibility argument, or a direct weight-grading of the localization
  `k[Xᵢⱼ][det⁻¹]`).

- **Sub-issue (A): assembly.** Given (K): build the matrix-coefficient subrep
  `W` from `M`, use `h_span` (+ `glWeightSpace_iSupIndep` /
  `DirectSum.IsInternal`) to certify all weights `≥ 0`, apply (K) to land each
  `f_{ac}` in `k[Xᵢⱼ]`, and read off the basis `b` and bare polynomials `Q a c`
  to close `detInv_elim_of_polynomial`. Depends on (K).

## What is NOT a valid shortcut

- Re-deriving multi-homogeneity of the cleared numerator and stopping there —
  proven insufficient above.
- One-sided OR two-sided torus-weight nonnegativity alone — the `N=2`
  counterexample defeats both.
- A monoid-extension `M_N(k) → End(M)` defined via the cleared coefficients —
  circular (defining it needs `det^r ∣ Q`, which is the goal).
