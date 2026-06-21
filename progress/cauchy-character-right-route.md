# Route: `polyRightDegreeFDRep_formalCharacter` (right-`GL_N` Cauchy character identity, #4944)

This records a concrete two-piece decomposition of the single research `sorry` in
`Chapter5/CauchyCharacterRight.lean:145`, grounded in the existing (sorry-free)
infrastructure, plus what was landed toward it.

## The target

```
theorem polyRightDegreeFDRep_formalCharacter
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    formalCharacter k N (polyRightDegreeFDRep k N d)
      = ∑ ν : BoundedPartition N d,
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts)) •
            schurPoly N ν.parts
```

`A_d = homogeneousSubmodule (Fin N × Fin N) k d` as a right-`GL_N` rep. The
identity is the Cauchy identity `∑_ν s_ν(x) s_ν(y) = ∏_{i,j}(1 - x_i y_j)^{-1}`
specialised at `y = (1,…,1)` (so RHS multiplicity `= s_ν(1^N)`) and truncated to
total degree `d`.

## The clean meeting point: coefficient `∏_j C(μ_j + N − 1, N − 1)`

Prove by `MvPolynomial.ext` (coefficient-wise). For every `μ : Fin N →₀ ℕ`:

- **LHS coefficient** (`formalCharacter_coeff`): `coeff μ (formalCharacter …) =
  finrank (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)`. The weight space is
  spanned by the monomials of `A_d` whose **column-degree vector** is `μ`
  (`μ_j = ∑_i s(i,j)`), so its dimension is the number of such monomials,
  `∏_j C(μ_j + N − 1, N − 1)` when `∑_j μ_j = d` (else `0`: a degree-`d` monomial
  has column degrees summing to `d`).
- **RHS coefficient**: `coeff μ (∑_ν s_ν(1^N) • s_ν) = ∑_ν s_ν(1^N) · coeff μ (s_ν)`.
  The Cauchy identity at `y = 1^N` says this equals the same
  `∏_j C(μ_j + N − 1, N − 1)` (the `μ`-coefficient of `∏_j (1 − x_j)^{-N}`).

So the two sides meet at the single combinatorial number
`∏_j C(μ_j + N − 1, N − 1)` — making the two sub-issues genuinely independent.

## Sub-issue A — weight-space side (elementary, no Schur-Weyl)

> For every `μ`, `finrank (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
> = if ∑_j μ_j = d then ∏_j C(μ_j + N − 1, N − 1) else 0`.

Route:
- `diagUnit k N i t` (`Theorem5_22_1.lean`) is the diagonal matrix
  `diagonal (Function.update 1 i t)`. The right action on a monomial is now
  **landed** (this session): `rTransAlgHom_diagonal_monomial`
  (`PolynomialGLRightAction.lean`) — a diagonal matrix `diag(v)` scales
  `monomial s c` by `∏_{(i,j)} v_j^{s(i,j)}`, i.e. every monomial is a right-torus
  eigenvector with weight the column degrees. Specialising `v = update 1 i t`
  gives eigenvalue `t^{col_i(s)}` where `col_i(s) = ∑_l s(l,i)`.
- Hence the monomial `X^s ∈ A_d` lies in `glWeightSpace … μ` iff `col_j(s) = μ_j`
  for all `j`. The monomials of `A_d` form a basis adapted to the weight grading
  (distinct column-degree vectors ⟹ distinct weight spaces, and the monomials
  span `A_d`), so `glWeightSpace … μ` is the span of `{X^s : col(s) = μ}` and its
  dimension is `#{s : (Fin N × Fin N) →₀ ℕ | col_j(s) = μ_j ∀ j}`.
- Count: choosing column `j` independently, `#{(s(0,j),…,s(N−1,j)) : ∑_i = μ_j} =
  C(μ_j + N − 1, N − 1)` (stars and bars, `Nat.choose`), so the product is
  `∏_j C(μ_j + N − 1, N − 1)`.

Missing Lean: the basis-of-weight-space lemma (weight space = monomial span) and
the stars-and-bars count. `Mathlib`: `Sym`/`Finset.Nat.antidiagonalTuple`,
`MvPolynomial.basisMonomials`. This is self-contained, ~elementary, but nontrivial
(eigenspace = monomial span needs a diagonalisation/independence argument).

Useful cross-check: `fullCauchyProd_coeff_eq_card_gen`
(`PowerSumCauchyBilinearGen.lean`) gives `[x^α y^β] ∏_{i,j}(1−x_iy_j)^{-1} =
#{NN matrices, row sums α, col sums β}`; summing over row margins `α`
(set `x_i = 1`) recovers `∏_j C(μ_j+N−1,N−1) = #{NN matrices with col sums μ}`.

## Sub-issue B — Cauchy identity in the Schur basis (the symmetric-function core)

> For every `μ` with `∑_j μ_j = d`,
> `∑_{ν : BoundedPartition N d} (eval 1 (schurPoly N ν.parts)) · (schurPoly N ν.parts).coeff μ
> = ∏_j C(μ_j + N − 1, N − 1)`.

Equivalently the polynomial identity
`∑_ν s_ν(1^N) • s_ν = degree-d part of ∏_j (1 − x_j)^{-N}`.

Route — assemble the **Schur-form** Cauchy identity from what exists:
- Power-sum Cauchy, coefficient level (**have**, sorry-free):
  `powerSum_bilinear_coeff_gen` and `fullCauchyProd_coeff_eq_card_gen`
  (`PowerSumCauchyBilinear.lean`, `PowerSumCauchyBilinearGen.lean`).
- Frobenius change of basis `p_μ = ∑_λ χ_λ(μ) s_λ` (**have**, sorry-free):
  `Proposition5_21_1_univ` / `psumPart` decomposition used by
  `sum_X_pow_eq_sum_charValue_smul_schurPoly` (`SchurWeylPolynomialIdentity.lean`),
  with `charValue` (`Proposition5_21_1.lean`).
- `S_n` character column-orthogonality `∑_μ z_μ^{-1} χ_λ(μ) χ_ρ(μ) = δ_{λρ}` to
  pass from the power-sum Cauchy to `∑_λ s_λ(x) s_λ(y)`. **Check whether this is
  already in the repo** (the character-table machinery around `charValue`); if
  not it is the main missing piece and may warrant its own sub-issue.
- Specialise `y = (1,…,1)`: `s_ν(1^N) = eval (fun _ => 1) (schurPoly N ν.parts)`
  (closed form available via `Proposition5_21_2_dimension`, the hook-length
  formula, though only the symbol `eval 1` is needed), and
  `∏_{i,j}(1−x_iy_j)^{-1}|_{y=1^N} = ∏_j (1−x_j)^{-N}`, whose degree-`d`
  `x^μ`-coefficient is `∏_j C(μ_j+N−1,N−1)` — meeting sub-issue A.

This is research-level symmetric-function theory; it is the genuine core and is
likely a multi-issue effort (the Schur-form Cauchy identity is itself a
landmark). It overlaps the highest-weight classification interface
`iso_of_formalCharacter_eq_schurPoly` (#4699/#4882) only at `schurPoly`/`charValue`
plumbing, not in substance.

## Assembly

`polyRightDegreeFDRep_formalCharacter` follows by `MvPolynomial.ext` from A and B:
`coeff μ LHS = ∏_j C(μ_j+N−1,N−1) = coeff μ RHS` (both `0` off degree `d`). This
final glue is a few lines once A and B exist; fold it into whichever sub-issue
lands second, or into the #4944 residual.

## Landed this session (toward A)

`PolynomialGLRightAction.lean` (sorry-free):
- `rTransAlgHom_diagonal_X (v) (p)`: `R_{diag v} X_p = v_{p.2} • X_p`.
- `rTransAlgHom_diagonal_monomial (v) (s) (c)`:
  `R_{diag v} (monomial s c) = (∏_{(i,j)} v_j^{s(i,j)}) • monomial s c` — every
  monomial is a right-torus eigenvector; its weight is the column-degree vector.

These are exactly the eigenbasis facts sub-issue A's weight-space dimension count
is built on.
