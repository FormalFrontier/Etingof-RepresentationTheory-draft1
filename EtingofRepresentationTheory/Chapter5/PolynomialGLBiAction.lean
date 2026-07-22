import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialGLRightAction

/-!
# The left-translation `GL_N`-action and the `GL_N × GL_N` bi-action on `k[Xᵢⱼ]`

This file complements `PolynomialGLRightAction.lean`. There the **right
translation** `(R_h f)(g) = f(g h)` was realised as the algebra endomorphism
`rTransAlgHom M : X_{ij} ↦ ∑_l M_{lj} X_{il}` (mixing the **column** index `j`),
packaged into `polyRightRep`. Here we add the commuting **left translation**
`(L_h f)(g) = f(hᵀ g)`, which on generators acts by

`L_h X_{ij} = ∑_l h_{li} X_{lj}`

— it mixes the **row** index `i` and fixes the column index `j`. We package it as
`lTransAlgHom M`, show it is multiplicative in `M` (`lTransAlgHom_one`,
`lTransAlgHom_mul`), and restrict to `GL_N` to obtain a genuine
`Representation k GL_N A` (`polyLeftRep`).

## The bi-action

The central fact is that the two actions **commute**
(`lTransAlgHom_comp_rTransAlgHom`, `polyLeftRep_commute_polyRightRep`): left
multiplication mixes rows, right multiplication mixes columns, and the two
operations are independent. This realises `A = k[Xᵢⱼ]` as a genuine
`GL_N × GL_N`-representation — the structure underlying the Cauchy decomposition
`k[Xᵢⱼ] = ⊕_{ν ∈ ℕ^N dom} V_ν^* ⊠ V_ν` (left factor `V_ν^*`, right factor `V_ν`).

## The determinant is a bi-semi-invariant

As for the right action, the generic determinant transforms by the determinant
character on the left too: `L_M det(X) = det(M)·det(X)` (`lTransAlgHom_det`), so
the principal ideal `(det)` is also left-`GL_N`-stable
(`lTransAlgHom_mem_detIdeal`). Combined with the right-stability from
`PolynomialGLRightAction.lean`, the quotient `A/det = k[Xᵢⱼ]/(det)` inherits the
full `GL_N × GL_N` bi-action — the bi-representation whose constituents the kernel
lemma (K′) and the Cauchy decomposition (#4904, #4896) analyse.
-/

namespace Etingof.PolynomialGLAction

open MvPolynomial

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The left-translation endomorphism of `A = k[Xᵢⱼ]` attached to a matrix `M`:
the algebra hom sending the coordinate `X_{ij}` to `∑_l M_{li} X_{lj}`. For
`M = h ∈ GL_N` this is the left translation `(L_h f)(g) = f(hᵀ g)` (it mixes the
row index `i`, fixes the column index `j`). -/
noncomputable def lTransAlgHom (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval (fun ij : Fin N × Fin N => ∑ l : Fin N, M l ij.1 • MvPolynomial.X (l, ij.2))

@[simp] theorem lTransAlgHom_X (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    lTransAlgHom M (MvPolynomial.X (i, j)) = ∑ l, M l i • MvPolynomial.X (l, j) := by
  simp [lTransAlgHom]

/-- The identity matrix acts trivially: `L_1 = id`. -/
theorem lTransAlgHom_one :
    lTransAlgHom (1 : Matrix (Fin N) (Fin N) k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [lTransAlgHom_X]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, AlgHom.id_apply]
  rw [Finset.sum_ite_eq' Finset.univ i (fun l => MvPolynomial.X (l, j))]
  simp

/-- Multiplicativity in the matrix argument: `L_{M₁ M₂} = L_{M₁} ∘ L_{M₂}`.
This is the homomorphism property making the left translation a representation. -/
theorem lTransAlgHom_mul (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    lTransAlgHom (M₁ * M₂) = (lTransAlgHom M₁).comp (lTransAlgHom M₂) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, lTransAlgHom_X, lTransAlgHom_X, map_sum]
  simp_rw [map_smul, lTransAlgHom_X, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]

/-- The **left-translation representation** of `GL_N(k)` on `A = k[Xᵢⱼ]`:
`g ↦ (L_g : f ↦ f(gᵀ ·))`. The left translation `(L_h f)(g) = f(hᵀ g)` acts on
generators by `L_h X_{ij} = ∑_l h_{li} X_{lj}`. -/
noncomputable def polyLeftRep (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k) where
  toFun g := (lTransAlgHom (g : Matrix (Fin N) (Fin N) k)).toLinearMap
  map_one' := by
    change (lTransAlgHom ((1 : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_one, lTransAlgHom_one]
    rfl
  map_mul' g₁ g₂ := by
    change (lTransAlgHom ((g₁ * g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_mul, lTransAlgHom_mul]
    rfl

@[simp] theorem polyLeftRep_apply_X (g : Matrix.GeneralLinearGroup (Fin N) k)
    (i j : Fin N) :
    polyLeftRep k N g (MvPolynomial.X (i, j))
      = ∑ l, (g : Matrix (Fin N) (Fin N) k) l i • MvPolynomial.X (l, j) :=
  lTransAlgHom_X _ i j

/-- The left-translation representation acts as the algebra endomorphism
`lTransAlgHom`: `polyLeftRep g f = lTransAlgHom (↑g) f`. -/
theorem polyLeftRep_apply (g : Matrix.GeneralLinearGroup (Fin N) k)
    (f : MvPolynomial (Fin N × Fin N) k) :
    polyLeftRep k N g f = lTransAlgHom (↑g) f :=
  rfl

/-- **Left and right translations commute** as algebra endomorphisms of
`A = k[Xᵢⱼ]`: the left action mixes the row index, the right action mixes the
column index, and the two operations are independent. This is what makes
`A = k[Xᵢⱼ]` a genuine `GL_N × GL_N`-representation. -/
theorem lTransAlgHom_comp_rTransAlgHom (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    (lTransAlgHom M₁).comp (rTransAlgHom M₂)
      = (rTransAlgHom M₂).comp (lTransAlgHom M₁) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rTransAlgHom_X, lTransAlgHom_X,
    map_sum, map_sum]
  simp_rw [map_smul, lTransAlgHom_X, rTransAlgHom_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

/-- The left and right `GL_N`-actions on `A = k[Xᵢⱼ]` commute, exhibiting the
genuine `GL_N × GL_N` bi-action: for `g, h ∈ GL_N`, `L_g` and `R_h` commute as
linear endomorphisms. -/
theorem polyLeftRep_commute_polyRightRep (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    Commute (polyLeftRep k N g) (polyRightRep k N h) := by
  have key : polyLeftRep k N g * polyRightRep k N h
      = polyRightRep k N h * polyLeftRep k N g := by
    apply LinearMap.ext
    intro f
    rw [Module.End.mul_apply, Module.End.mul_apply, polyLeftRep_apply,
      polyRightRep_apply, polyRightRep_apply, polyLeftRep_apply]
    have h2 := AlgHom.congr_fun (lTransAlgHom_comp_rTransAlgHom (↑g) (↑h)) f
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h2
    exact h2
  exact key

/-- The generic matrix transforms under the left substitution by left
multiplication by the transpose: applying `lTransAlgHom M` to the generic matrix
of variables is left multiplication by the constant matrix `Mᵀ`. -/
theorem mapMatrix_mvPolynomialX_left (M : Matrix (Fin N) (Fin N) k) :
    (lTransAlgHom M).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) k)
      = (Matrix.transpose M).map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)
        * Matrix.mvPolynomialX (Fin N) (Fin N) k := by
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX,
    Matrix.of_apply, lTransAlgHom_X, Matrix.mul_apply, MvPolynomial.smul_eq_C_mul,
    Matrix.transpose_apply]

/-- **Determinant semi-invariance (left action).** The generic determinant
`det(Xᵢⱼ)` transforms under left translation by the determinant character:
`L_M det(X) = det(M) · det(X)`. For `M = h ∈ GL_N` this is `L_h det = det(h)·det`,
so `det` spans a copy of the determinant character `χ` for the left action too. -/
theorem lTransAlgHom_det (M : Matrix (Fin N) (Fin N) k) :
    lTransAlgHom M (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k))
      = MvPolynomial.C M.det * Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) := by
  have hmap : ((Matrix.transpose M).map
        (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).det
      = MvPolynomial.C M.det := by
    rw [← Matrix.det_transpose M]
    exact (RingHom.map_det _ _).symm
  rw [AlgHom.map_det, mapMatrix_mvPolynomialX_left, Matrix.det_mul, hmap]

/-- **The determinant ideal `(det)` is left-`GL_N`-stable.** A multiple of the
generic determinant maps under left translation to a multiple of it (the
semi-invariance `lTransAlgHom_det` keeps the factor `det`). Together with
right-stability (`rTransAlgHom_mem_detIdeal`), the quotient `A/det` inherits the
full `GL_N × GL_N` bi-action. -/
theorem lTransAlgHom_mem_detIdeal (M : Matrix (Fin N) (Fin N) k)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}) :
    lTransAlgHom M f ∈
      Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)} := by
  rw [Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, lTransAlgHom_det]
  exact ⟨MvPolynomial.C M.det * lTransAlgHom M q, by ring⟩

end Etingof.PolynomialGLAction
