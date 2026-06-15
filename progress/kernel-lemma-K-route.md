# Kernel lemma (K) — det⁻¹-elimination: reduction, insufficiency proof, decomposition (issue #4694)

This refines `progress/detInv-elim-route-analysis.md`. It records a concrete
det-power **filtration reduction** of the kernel lemma (K) to a single
representation-theoretic core (K′), an explicit proof that the torus-only route
gives only column-sum bounds (not divisibility), and the exact missing
infrastructure. It justifies the worker-led decomposition of #4694.

## The kernel lemma (K)

> A finite-dimensional **right-`GL_N`-stable** subspace `W ⊆ O = k[Xᵢⱼ, det⁻¹]`
> all of whose **right-torus weights lie in `ℕ^N`** is contained in the
> polynomial subring `A = k[Xᵢⱼ]`.

Right translation `(R_h f)(g) = f(g h)`. On generators `X_{ij}(g) = g_{ij}`:
`R_h X_{ij} = ∑_l h_{lj} X_{il}` (acts on the **column** index `j`, preserves
the row index `i`). `R_h det = det(h)·det`, `R_h det⁻¹ = det(h)⁻¹·det⁻¹`.
Right-torus weight of `X_{ij}` is `e_j`; of a monomial `X^E` it is the vector of
**column sums** `col_j(E) = ∑_i E_{ij}`; of `det` it is `(1,…,1)`; of `det⁻¹` it
is `(-1,…,-1)`.

## What the assembly #4695 needs (interface)

`detInv_elim_of_polynomial` consumes (K) in the **functions-on-`GL`** form:
each matrix coefficient `f_{ac}(g) = b.repr (M.ρ g (b c)) a`, a priori
`= evalAtGL g (P a c)` with `P a c ∈ k[Xᵢⱼ, D]`, is `eval`-equal **on all of
`GL`** to a bare-entry polynomial `Q a c ∈ k[Xᵢⱼ]` (no `D = det⁻¹`). The faithful
model: `evalAtGL` factors through `A[det⁻¹] ≅ k[GLCoordVars]/(D·det − 1)`, and
`A[det⁻¹] ↪ (GL → k)` is injective because `GL_N` is Zariski-dense in `M_N`
(`eq_of_eval_eq_on_gl`, `PolynomialRepEmbedding.lean:603`, already proven).

## Det-power filtration reduction (K) ⟸ (K′)

`O = A[det⁻¹]`. `A` is a UFD; `det` is irreducible (PREREQUISITE, see below).
Every `f ∈ O` has a unique normal form `f = Q / det^r`, `Q ∈ A`, `det ∤ Q`
(`r = 0 ⟺ f ∈ A`). Define the GL-stable filtration `A_r := det^{-r}·A`:
`A = A_0 ⊆ A_1 ⊆ ⋯`, `O = ⋃_r A_r`, each `A_r` right-GL-stable
(`R_h(Q/det^r) = (R_h Q)/(det(h)^r det^r)`, `R_h Q ∈ A`).

Quotient as right-GL-modules, **twisting by the determinant character**
`χ : R_h ↦ det(h)`:

> `A_r / A_{r-1} ≅ (A/det) ⊗ χ^{-r}`  via  `Q/det^r ↦ Q mod det`.

(`R_h` acts on the RHS by `Q̄ ↦ det(h)^{-r}·(R_h Q mod det)`.) The right-torus
weights of `A/det` are column sums `∈ ℕ^N`; twisting by `χ^{-r}` subtracts
`(r,…,r)`. **Torus-equivariant quotient ⇒ any weight of the image is a weight of
`W`.**

Now suppose `W ⊆ O` is finite-dimensional, right-GL-stable, all weights `∈ ℕ^N`,
and `W ⊄ A`. Pick `r ≥ 1` minimal with `W ⊆ A_r` (exists: `W` fin-dim). Then
the image `W̄ ⊆ A_r/A_{r-1}` is a **nonzero** right-GL-submodule of
`(A/det) ⊗ χ^{-r}`, all of whose weights are `≥ 0` (they are weights of `W`).
The reduction is finished by:

> **(K′)** For `r ≥ 1`, `(A/det) ⊗ χ^{-r}` has **no nonzero right-`GL_N`-submodule
> all of whose weights lie in `ℕ^N`**.

`(K′)` contradicts `W̄ ≠ 0`; hence `W ⊆ A`. ∎ (reduction)

## Why the torus alone is insufficient (explicit, confirms the route doc)

Right-multiplying by the full diagonal torus `diag(z₁,…,z_N)` and using
weights `≥ 0`, one derives for the cleared numerator `Q` (with `f = Q/det^r`):

```
Q(g₀·diag(z)) = det(g₀)^r · ∑_{ν ≥ 0} (∏_j z_j^{r+ν_j}) f_ν(g₀),
```

so `Q(g₀·diag(z))` is divisible by `∏_j z_j^r` for every `g₀ ∈ GL`. Splitting `Q`
by column-multidegree `Q = ∑_c Q_c` gives `Q_c = 0` whenever some `c_j < r`,
i.e. **every monomial of `Q` has all column sums `≥ r`**. This is necessary but
**NOT** `det^r ∣ Q`: for `N=2, r=1`, `α·X₁₁X₂₂ + β·X₁₂X₂₁` has all column sums
`= 1` yet is `det`-divisible only when `α = -β`. The missing constraint is the
**full (non-diagonal) right-`GL` action** — exactly the content of (K′).

## (K′) is the genuine representation-theoretic core

By complete reducibility (`Theorem5_23_2_i`) `W̄` contains an irreducible
right-GL-subrep `L`. "All weights of `L` are `≥ 0`" is equivalent (lowest-weight
theory: the lowest weight of an irrep of highest weight `ν` is `w₀ν =
(ν_N,…,ν_1)`) to **`ν ∈ ℕ^N`**, i.e. `L` is a *polynomial* irrep. So (K′) ⟺

> Every irreducible constituent of `(A/det) ⊗ χ^{-r}` (`r ≥ 1`) has highest
> weight with a **negative** coordinate; equivalently every constituent of
> `A/det = k[Xᵢⱼ]/(det)` has highest weight `ν` with **last coordinate
> `ν_N = 0`** (so that `ν_N − r = −r < 0` after the `χ^{-r}` twist).

The fact "constituents of `k[Xᵢⱼ]/(det)` have `ν_N = 0`" is the **GL×GL-equivariant
Cauchy decomposition** of `O(M_N) = k[Xᵢⱼ] = ⊕_{ν ∈ ℕ^N dom} V_ν^* ⊠ V_ν`
together with `det·A ≅ A ⊗ χ` (multiplication by `det` shifts highest weights by
`(1,…,1)`), so `A/det` keeps exactly the `ν` with `ν_N = 0`.

## Missing infrastructure (the reason for decomposition)

The repo does **not** have, and Mathlib does **not** have:

1. **`det` irreducibility / prime** in `MvPolynomial (Fin N × Fin N) k`, and the
   det-power normal form on the localization `A[det⁻¹]` (`IsLocalization.Away det`
   exists in Mathlib; the normal form does not). — ELEMENTARY, self-contained.
2. The **GL×GL-equivariant** Cauchy/Peter–Weyl decomposition of `O(M_N)` /
   `O(GL_N)`. `Theorem5_23_2_ii` is only a **rank** isomorphism
   (`nonempty_linearEquiv_of_rank_eq`), carrying **no** weight/equivariance data.
3. **Highest/lowest-weight theory** for `GL_N` irreps (weights of `L_ν`,
   `ν ∈ ℕ^N ⟺ all weights ≥ 0`). The classification entry point
   `iso_of_formalCharacter_eq_schurPoly` (`FormalCharacterIso.lean:388`) is itself
   an open `sorry` (#4699).

Pieces (2)–(3) are a multi-issue, research-level effort — they are essentially
"make Peter–Weyl equivariant" plus GL_N highest-weight theory. This is why
#4694 cannot be closed in a single session and is decomposed.

## Decomposition

- **#K-det (prerequisite, not blocked):** `det` is irreducible/prime in
  `MvPolynomial (Fin N × Fin N) k`; the det-power normal form `f = Q/det^r`
  (min `r`) for `A[det⁻¹]`, and that `evalAtGL` factors faithfully through
  `A[det⁻¹]` (`eq_of_eval_eq_on_gl`). Self-contained, session-sized.

- **#K-cauchy ((K′), the deep core; depends-on #K-det and the equivariant
  Cauchy/highest-weight gap, cf. #4699):** prove (K′) — for `r ≥ 1`,
  `(A/det) ⊗ χ^{-r}` has no nonzero nonneg-weight right-GL-submodule;
  equivalently constituents of `k[Xᵢⱼ]/(det)` have `ν_N = 0`. The genuine
  mathematics; expect further decomposition into the equivariant Cauchy
  decomposition + the `det·A ≅ A⊗χ` highest-weight shift.

- **#4694 (narrowed to the assembly):** assemble (K) from #K-det (filtration
  normal form) + #K-cauchy ((K′)) via the det-power filtration argument above,
  then deliver the functions-on-`GL` interface #4695 consumes.

## What is NOT a valid shortcut (carried over + sharpened)

- Stopping at "all column sums `≥ r`" — proven insufficient above (the explicit
  `α X₁₁X₂₂ + β X₁₂X₂₁` computation).
- Using `Theorem5_23_2_ii` directly — it is a rank iso, with no weight data.
- One-/two-sided torus-weight nonnegativity — defeated by the same `N=2` example.
</content>
</invoke>
