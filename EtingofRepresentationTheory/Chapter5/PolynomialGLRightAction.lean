import Mathlib
import EtingofRepresentationTheory.Chapter5.DetLocalization

/-!
# The right-translation `GL_N`-action on the coordinate ring `k[Xᵢⱼ]`

This file constructs the **right-translation representation** of `GL_N(k)` on the
polynomial coordinate ring `A = k[Xᵢⱼ] = MvPolynomial (Fin N × Fin N) k`, the
representation-theoretic object the det⁻¹-elimination kernel lemma (K′) (issue
#4713, route doc `progress/kernel-lemma-K-route.md`) is stated over.

On the coordinate functions `X_{ij}(g) = g_{ij}` the right translation
`(R_h f)(g) = f(g · h)` acts by
`R_h X_{ij} = ∑_l h_{lj} X_{il}` — it mixes the **column** index `j` (right
multiplication acts on columns) and fixes the **row** index `i`. We package this
as an algebra endomorphism `rTransAlgHom M` for an arbitrary matrix `M`, show it
is multiplicative in `M` (`rTransAlgHom_one`, `rTransAlgHom_mul`), and restrict to
`GL_N` to obtain a genuine `Representation k GL_N A` (`polyRightRep`).

## The determinant is a semi-invariant

The generic determinant `det(Xᵢⱼ)` transforms by the determinant character:
`R_h det(X) = det(h) · det(X)` (`rTransAlgHom_det`). Consequently the principal
ideal `(det)` is `GL_N`-stable (`rTransAlgHom_mem_detIdeal`), so the quotient
`A/det` inherits a right-`GL_N`-action — this is exactly the rep `A/det` that (K′)
analyses (twisted by the determinant character `χ^{-r}`).

These are the structural prerequisites for the genuine representation-theoretic
core (K′): every irreducible constituent of `k[Xᵢⱼ]/(det)` has last
highest-weight coordinate `ν_N = 0`, proved via the `GL×GL`-equivariant Cauchy
decomposition. That core is tracked in the follow-up sub-issue; this file
supplies the action it is phrased over.
-/

namespace Etingof.PolynomialGLAction

open MvPolynomial

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The right-translation endomorphism of `A = k[Xᵢⱼ]` attached to a matrix `M`:
the algebra hom sending the coordinate `X_{ij}` to `∑_l M_{lj} X_{il}`. For
`M = h ∈ GL_N` this is the right translation `(R_h f)(g) = f(g · h)` (right
multiplication acts on the column index, fixes the row index). -/
noncomputable def rTransAlgHom (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval (fun ij : Fin N × Fin N => ∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l))

@[simp] theorem rTransAlgHom_X (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    rTransAlgHom M (MvPolynomial.X (i, j)) = ∑ l, M l j • MvPolynomial.X (i, l) := by
  simp [rTransAlgHom]

/-- The identity matrix acts trivially: `R_1 = id`. -/
theorem rTransAlgHom_one :
    rTransAlgHom (1 : Matrix (Fin N) (Fin N) k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [rTransAlgHom_X]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, AlgHom.id_apply]
  rw [Finset.sum_ite_eq' Finset.univ j (fun l => MvPolynomial.X (i, l))]
  simp

/-- Multiplicativity in the matrix argument: `R_{M₁ M₂} = R_{M₁} ∘ R_{M₂}`.
This is the homomorphism property making the right translation a representation. -/
theorem rTransAlgHom_mul (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    rTransAlgHom (M₁ * M₂) = (rTransAlgHom M₁).comp (rTransAlgHom M₂) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, rTransAlgHom_X, rTransAlgHom_X, map_sum]
  simp_rw [map_smul, rTransAlgHom_X, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]

/-- The **right-translation representation** of `GL_N(k)` on `A = k[Xᵢⱼ]`:
`g ↦ (R_g : f ↦ f(· g))`. The right translation `(R_h f)(g) = f(g h)` acts on
generators by `R_h X_{ij} = ∑_l h_{lj} X_{il}`. -/
noncomputable def polyRightRep (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k) where
  toFun g := (rTransAlgHom (g : Matrix (Fin N) (Fin N) k)).toLinearMap
  map_one' := by
    change (rTransAlgHom ((1 : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_one, rTransAlgHom_one]
    rfl
  map_mul' g₁ g₂ := by
    change (rTransAlgHom ((g₁ * g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_mul, rTransAlgHom_mul]
    rfl

@[simp] theorem polyRightRep_apply_X (g : Matrix.GeneralLinearGroup (Fin N) k)
    (i j : Fin N) :
    polyRightRep k N g (MvPolynomial.X (i, j))
      = ∑ l, (g : Matrix (Fin N) (Fin N) k) l j • MvPolynomial.X (i, l) :=
  rTransAlgHom_X _ i j

/-- The right-translation representation acts as the algebra endomorphism
`rTransAlgHom`: `polyRightRep g f = rTransAlgHom (↑g) f`. -/
theorem polyRightRep_apply (g : Matrix.GeneralLinearGroup (Fin N) k)
    (f : MvPolynomial (Fin N × Fin N) k) :
    polyRightRep k N g f = rTransAlgHom (↑g) f :=
  rfl

/-- The generic determinant matrix `(rTransAlgHom M).mapMatrix mvPolynomialX`
equals `mvPolynomialX * M.map C`: applying the column-mixing substitution to the
generic matrix of variables is right multiplication by the constant matrix `M`. -/
theorem mapMatrix_mvPolynomialX (M : Matrix (Fin N) (Fin N) k) :
    (rTransAlgHom M).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) k)
      = Matrix.mvPolynomialX (Fin N) (Fin N) k
        * M.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k) := by
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX,
    Matrix.of_apply, rTransAlgHom_X, Matrix.mul_apply, MvPolynomial.smul_eq_C_mul]
  simp only [mul_comm]

/-- **Determinant semi-invariance.** The generic determinant `det(Xᵢⱼ)`
transforms under right translation by the determinant character:
`R_M det(X) = det(M) · det(X)`. For `M = h ∈ GL_N` this is `R_h det = det(h)·det`,
the statement that `det` spans a copy of the determinant character `χ`. -/
theorem rTransAlgHom_det (M : Matrix (Fin N) (Fin N) k) :
    rTransAlgHom M (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k))
      = MvPolynomial.C M.det * Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) := by
  have hmap : (M.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).det
      = MvPolynomial.C M.det := (RingHom.map_det _ _).symm
  rw [AlgHom.map_det, mapMatrix_mvPolynomialX, Matrix.det_mul, hmap, mul_comm]

/-- **The determinant ideal `(det)` is right-`GL_N`-stable.** A multiple of the
generic determinant maps under right translation to a multiple of it (the
semi-invariance `rTransAlgHom_det` keeps the factor `det`). Consequently the
quotient ring `A/det = k[Xᵢⱼ]/(det)` inherits the right-`GL_N`-action: it is the
representation (twisted by `χ^{-r}`) that the kernel lemma (K′) analyses. -/
theorem rTransAlgHom_mem_detIdeal (M : Matrix (Fin N) (Fin N) k)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}) :
    rTransAlgHom M f ∈
      Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)} := by
  rw [Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, rTransAlgHom_det]
  exact ⟨MvPolynomial.C M.det * rTransAlgHom M q, by ring⟩

end Etingof.PolynomialGLAction
