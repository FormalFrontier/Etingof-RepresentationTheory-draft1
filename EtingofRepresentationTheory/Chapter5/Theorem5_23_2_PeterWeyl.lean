import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.LocalizationGLBiAction
import EtingofRepresentationTheory.Chapter5.PeterWeylMatrixCoeff

/-!
# Theorem 5.23.2(ii): the genuine `GL_n × GL_n`-equivariant Peter-Weyl decomposition

`Theorem5_23_2.lean` states part (ii) only as a *bare `k`-linear* rank-matching
isomorphism `R ≃ₗ[k] ⊕_λ L*_λ ⊗ L_λ` — true for any two countably-infinite-dim
free modules, carrying no representation-theoretic content. This file states the
genuine theorem: a **`GL_n × GL_n`-equivariant** isomorphism

  `R ≅ ⊕_λ L*_λ ⊗ L_λ`   as representations of `GL_n × GL_n`,

where `R = k[gᵢⱼ][1/det] = Localization.Away (detPoly k n)` is the coordinate ring
with its left/right translation bi-action (`localBiRep`, `LocalizationGLBiAction.lean`),
`L_λ = AlgIrrepGL` carries the det-twisted Schur-module action (`algIrrepGLRepρ`,
`AlgIrrepGLRep.lean`), `L*_λ = AlgIrrepGLDual` its contragredient
(`algIrrepGLRepDualρ`), and the action on the summand `L*_λ ⊗ L_λ` is the left
factor on `L*_λ` (via the first `GL_n`) and the right factor on `L_λ` (via the
second `GL_n`).

The right-hand-side representation `peterWeylRHS` is assembled with
`Representation.tprod` and `Representation.directSum`. The candidate isomorphism
`peterWeylMap : peterWeylRHS → R` is assembled here from the per-summand
matrix-coefficient maps `peterWeylSummandMap` (`PeterWeylMatrixCoeff.lean`) via
`DirectSum.toModule`, and its `GL_n × GL_n`-equivariance (`peterWeylMap_equivariant`)
is assembled from the per-summand equivariance. This reduces the capstone
`Theorem5_23_2_ii_equivariant` to a single bijectivity statement
`peterWeylMap_bijective` (the Cauchy decomposition,
`PolynomialGLDecomposition.lean` / `CauchyDetQuotient*`), which is the sole remaining
`sorry` and is being assembled separately.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

open Etingof.LocalizationGLAction Etingof.DetLocalization

variable {k : Type*}

/-- **The right-hand side of Peter-Weyl as a `GL_n × GL_n`-representation.**
`⊕_λ L*_λ ⊗ L_λ`, where the first `GL_n` acts on the `L*_λ` factor (via
`MonoidHom.fst`) and the second `GL_n` acts on the `L_λ` factor (via
`MonoidHom.snd`). Built from `Representation.tprod` over each summand and
`Representation.directSum` over all dominant weights. -/
noncomputable def peterWeylRHS (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k
      (Matrix.GeneralLinearGroup (Fin n) k × Matrix.GeneralLinearGroup (Fin n) k)
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :=
  Representation.directSum fun lam =>
    Representation.tprod
      ((algIrrepGLRepDualρ n lam k).comp (MonoidHom.fst _ _))
      ((algIrrepGLRepρ n lam k).comp (MonoidHom.snd _ _))

@[simp] theorem peterWeylRHS_apply (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :
    peterWeylRHS n k (g, h) x =
      DirectSum.lmap (fun lam =>
        TensorProduct.map (algIrrepGLRepDualρ n lam k g) (algIrrepGLRepρ n lam k h)) x :=
  rfl

/-- A `GL_n × GL_n`-equivariant `k`-linear isomorphism between two representations:
a linear equivalence intertwining the two actions. (The full content of the
Peter-Weyl statement lives in the equivariance condition; without it the bare
linear equivalence is vacuous, as the rank iso in `Theorem5_23_2.lean` shows.) -/
def IsEquivariantEquiv {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    (ρ₁ : Representation k G W₁) (ρ₂ : Representation k G W₂)
    (e : W₁ ≃ₗ[k] W₂) : Prop :=
  ∀ (g : G) (x : W₁), e (ρ₁ g x) = ρ₂ g (e x)

/-- The inverse of an equivariant equivalence is equivariant for the reversed
pair. The matrix-coefficient map of Peter-Weyl is naturally built in the
`peterWeylRHS → R` direction (`u ⊗ v ↦` matrix coefficient); this lemma transports
its equivariance to the `R ≃ peterWeylRHS` direction demanded by
`Theorem5_23_2_ii_equivariant`. -/
theorem IsEquivariantEquiv.symm {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {ρ₁ : Representation k G W₁} {ρ₂ : Representation k G W₂}
    {e : W₁ ≃ₗ[k] W₂} (he : IsEquivariantEquiv ρ₁ ρ₂ e) :
    IsEquivariantEquiv ρ₂ ρ₁ e.symm := by
  intro g y
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm y), e.apply_symm_apply]

/-- Decidable equality on dominant weights (the underlying type is a subtype of the
finite-support function type `Fin n → ℤ`). Needed for the `DirectSum.of`/`toModule`
API on `⊕_λ`, which `Representation.directSum` (using only `DirectSum.lmap`) sidesteps. -/
instance instDecidableEqDominantWeight (n : ℕ) : DecidableEq (DominantWeight n) :=
  inferInstanceAs (DecidableEq {lam : Fin n → ℤ // Antitone lam})

/-- **The assembled direct-sum matrix-coefficient map** `⊕_λ L*_λ ⊗ L_λ →ₗ[k] R`.
Built from the per-summand maps `peterWeylSummandMap` (`PeterWeylMatrixCoeff.lean`)
via `DirectSum.toModule`. This is the candidate Peter-Weyl isomorphism, in the
`peterWeylRHS → R` direction (matrix coefficients `u ⊗ v ↦ (g ↦ ⟨u, ρ(g) v⟩)`). -/
noncomputable def peterWeylMap (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) →ₗ[k]
      Localization.Away (detPoly k n) :=
  DirectSum.toModule k (DominantWeight n) _ (fun lam => peterWeylSummandMap n lam k)

@[simp] theorem peterWeylMap_of (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) (y : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k) :
    peterWeylMap n k (DirectSum.of _ lam y) = peterWeylSummandMap n lam k y := by
  unfold peterWeylMap
  erw [DirectSum.toModule_lof]

/-- The per-summand equivariance, extended from pure tensors to all of `L*_λ ⊗ L_λ`
by linearity: the per-summand map intertwines the summand action
`ρ*(g) ⊗ ρ(h)` (as `TensorProduct.map`) with the bi-action `localBiRep`. -/
theorem peterWeylSummandMap_map_equivariant (n : ℕ) (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (y : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k) :
    peterWeylSummandMap n lam k
        (TensorProduct.map (algIrrepGLRepDualρ n lam k g) (algIrrepGLRepρ n lam k h) y)
      = localBiRep k n (g, h) (peterWeylSummandMap n lam k y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul]
      exact peterWeylSummandMap_equivariant n lam k g h u v
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **`GL_n × GL_n`-equivariance of the assembled map.** `peterWeylMap` intertwines
the right-hand-side representation `peterWeylRHS` with the left/right-translation
bi-action `localBiRep`. Assembled summand-by-summand from
`peterWeylSummandMap_equivariant`, since `peterWeylRHS` acts as `DirectSum.lmap` of
the per-summand `TensorProduct.map` actions. -/
theorem peterWeylMap_equivariant (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :
    peterWeylMap n k (peterWeylRHS n k (g, h) x)
      = localBiRep k n (g, h) (peterWeylMap n k x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of lam y =>
      rw [peterWeylRHS_apply, DirectSum.lmap_of, peterWeylMap_of, peterWeylMap_of]
      exact peterWeylSummandMap_map_equivariant n k lam g h y
  | add x₁ x₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- **Reduction of the Peter-Weyl capstone to a single bijectivity statement.**
Given that the assembled matrix-coefficient map `peterWeylMap` is bijective,
`LinearEquiv.ofBijective` upgrades it to a `k`-linear equivalence `peterWeylRHS ≃ R`;
its inverse `R ≃ peterWeylRHS` is the equivalence demanded by
`Theorem5_23_2_ii_equivariant`, and `peterWeylMap_equivariant` (transported across
`IsEquivariantEquiv.symm`) supplies the intertwining. Thus the only remaining
representation-theoretic input is the Cauchy bijectivity of `peterWeylMap`. -/
theorem nonempty_equivariantEquiv_of_bijective
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (hbij : Function.Bijective (peterWeylMap n k)) :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam =>
          (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e } := by
  let e := LinearEquiv.ofBijective (peterWeylMap n k) hbij
  have he : IsEquivariantEquiv (peterWeylRHS n k) (localBiRep k n) e := by
    intro gh x
    obtain ⟨g, h⟩ := gh
    change peterWeylMap n k (peterWeylRHS n k (g, h) x)
      = localBiRep k n (g, h) (peterWeylMap n k x)
    exact peterWeylMap_equivariant n k g h x
  exact ⟨e.symm, he.symm⟩

/-- **Bijectivity of the assembled matrix-coefficient map** (the Cauchy decomposition).
This is the sole remaining representation-theoretic input to the Peter-Weyl capstone:
the matrix coefficients of the pairwise-distinct irreducibles `L_λ` are linearly
independent and span `R = k[gᵢⱼ][1/det]`. Its proof is the Cauchy decomposition
machinery (`PolynomialGLDecomposition.lean`, `CauchyDetQuotient*`) and is assembled
separately. -/
theorem peterWeylMap_bijective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Bijective (peterWeylMap n k) := by
  sorry

/-- **Theorem 5.23.2(ii) — Peter-Weyl for `GL_n(k)`.** The coordinate ring
`R = k[gᵢⱼ][1/det]`, as a representation of `GL_n × GL_n` under the left/right
translation bi-action `(g, h) · φ = L_g R_h φ` (`localBiRep`), is
**`GL_n × GL_n`-equivariantly isomorphic** to `⊕_λ L*_λ ⊗ L_λ` (`peterWeylRHS`),
the sum over all dominant integer weights `λ = (λ₁ ≥ ⋯ ≥ λ_n)`.

Unlike the bare rank iso `Theorem5_23_2_ii` in `Theorem5_23_2.lean`, this carries
genuine representation-theoretic content: the isomorphism intertwines the two
`GL_n × GL_n`-actions (`IsEquivariantEquiv`).

**Proof (Etingof §5.23(ii)).** By part (i) every algebraic representation is
completely reducible into the `L_λ`, which are pairwise non-isomorphic. The matrix
coefficient map `L*_λ ⊗ L_λ → R`, `u ⊗ v ↦ (g ↦ ⟨u, g⁻¹ v⟩)`, is `GL × GL`-equivariant
(left `GL` on `L*_λ`, right `GL` on `L_λ`); summing over `λ` and using that the
matrix coefficients of the pairwise-distinct irreducibles `L_λ` are linearly
independent and span `R` (the Cauchy decomposition,
`PolynomialGLDecomposition.lean` / `CauchyDetQuotient*`) gives the isomorphism.
The detailed assembly is out of scope for this file. -/
theorem Theorem5_23_2_ii_equivariant
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam =>
          (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e } :=
  -- The equivariant *structure* is assembled here: `peterWeylMap` together with
  -- `peterWeylMap_equivariant` reduce the capstone to `peterWeylMap_bijective`
  -- (the Cauchy decomposition), the sole remaining sorry.
  nonempty_equivariantEquiv_of_bijective n k (peterWeylMap_bijective n k)

end Etingof
