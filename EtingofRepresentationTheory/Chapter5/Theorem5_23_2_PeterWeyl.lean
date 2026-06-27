import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.LocalizationGLBiAction

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
`Representation.tprod` and `Representation.directSum`. The equivariant
isomorphism `Theorem5_23_2_ii_equivariant` is the content of Etingof §5.23(ii); its
proof from part (i) and the Cauchy decomposition machinery
(`PolynomialGLDecomposition.lean`, `CauchyDetQuotient*`) is out of scope here and
is left as `sorry` with the book outline recorded in the proof.
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
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam =>
          (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e } := by
  -- The book's proof (matrix coefficients + Cauchy decomposition); see the
  -- docstring. The supporting decomposition machinery
  -- (`PolynomialGLDecomposition`, `CauchyDetQuotient*`) is the substantial input
  -- and is being assembled separately.
  sorry

end Etingof
