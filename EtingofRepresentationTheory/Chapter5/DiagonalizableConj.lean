import Mathlib
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace

/-!
# A matrix with `N` distinct eigenvalues is conjugate to a diagonal torus element

This file proves the pure-linear-algebra conjugacy fact needed by the geometric
density core of the character-independence seam (issue #4925, sub-piece (ii)):

> A complex `N × N` invertible matrix whose characteristic polynomial has `N`
> distinct roots is conjugate (in `GL_N(ℂ)`) to a `diagTorus` element.

The strategy is the classical eigenbasis construction:

* the `N` distinct roots of `charpoly` are eigenvalues (`Matrix.spectrum_toLin'`
  + `Module.End.hasEigenvalue_iff_mem_spectrum`), and none of them is `0` because
  `g` is a unit (`spectrum.zero_mem_iff`);
* choosing one eigenvector per eigenvalue gives `N` linearly independent vectors
  (`Module.End.eigenvectors_linearIndependent'`), hence an eigenbasis
  (`basisOfLinearIndependentOfCardEqFinrank`);
* the change-of-basis matrix `V = (Pi.basisFun).toMatrix eigenbasis` is invertible
  (`Basis.invertibleToMatrix`) and satisfies `A * V = V * D` columnwise (each
  column is an eigenvector), so `A = V * D * V⁻¹` with `D` the diagonal of
  eigenvalues, which is exactly `diagTorus`.

## Main result

* `gl_conj_diagTorus_of_distinct_eigenvalues`
-/

open Matrix Module Polynomial

namespace Etingof

noncomputable section

/-- A `GL_N(ℂ)` matrix whose characteristic polynomial has `N` distinct roots is
conjugate to a diagonal torus element: there is a tuple of nonzero eigenvalues
`t : Fin N → ℂˣ` and a base change `h ∈ GL_N(ℂ)` with `g = h * diag(t) * h⁻¹`. -/
theorem gl_conj_diagTorus_of_distinct_eigenvalues
    (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) ℂ)
    (hdist : (g : Matrix (Fin N) (Fin N) ℂ).charpoly.roots.toFinset.card = N) :
    ∃ (t : Fin N → ℂˣ) (h : Matrix.GeneralLinearGroup (Fin N) ℂ),
      g = h * diagTorus ℂ N t * h⁻¹ := by
  -- `N = 0` is degenerate: `GL_0(ℂ)` is a subsingleton.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact ⟨fun i => i.elim0, 1, Subsingleton.elim _ _⟩
  have : NeZero N := ⟨hNpos.ne'⟩
  set A : Matrix (Fin N) (Fin N) ℂ := (g : Matrix (Fin N) (Fin N) ℂ) with hA_def
  -- `A` is a unit, hence `0` is not in its spectrum.
  have hAunit : IsUnit A := ⟨g, rfl⟩
  -- Enumerate the `N` distinct roots of the characteristic polynomial.
  set s : Finset ℂ := A.charpoly.roots.toFinset with hs_def
  have hcard_s : Fintype.card s = N := by rw [Fintype.card_coe]; exact hdist
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard_s).symm
  let t : Fin N → ℂ := fun i => (e i : ℂ)
  have ht_inj : Function.Injective t :=
    fun i j h => e.injective (Subtype.ext h)
  -- Each `t i` is a root of `charpoly`, hence in the spectrum of `A`.
  have ht_mem : ∀ i, t i ∈ spectrum ℂ A := by
    intro i
    have hroot : A.charpoly.IsRoot (t i) := by
      have hmem : t i ∈ A.charpoly.roots.toFinset := (e i).2
      rw [Multiset.mem_toFinset, mem_roots'] at hmem
      exact hmem.2
    exact (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hroot
  -- The associated endomorphism and its eigenvalues.
  let f : Module.End ℂ (Fin N → ℂ) := Matrix.toLin' A
  have hf_eig : ∀ i, f.HasEigenvalue (t i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact ht_mem i
  -- Eigenvalues of a unit are nonzero.
  have ht_ne : ∀ i, t i ≠ 0 := by
    intro i hzero
    have : (0 : ℂ) ∈ spectrum ℂ A := hzero ▸ ht_mem i
    exact ((spectrum.zero_mem_iff ℂ).mp this) hAunit
  -- Choose one eigenvector per eigenvalue.
  let v : Fin N → (Fin N → ℂ) := fun i => (hf_eig i).exists_hasEigenvector.choose
  have hvspec : ∀ i, f.HasEigenvector (t i) (v i) := fun i =>
    (hf_eig i).exists_hasEigenvector.choose_spec
  -- The eigenvectors are linearly independent (distinct eigenvalues), hence a basis.
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' f t ht_inj v hvspec
  have hcard_eq : Fintype.card (Fin N) = Module.finrank ℂ (Fin N → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card]
  let b : Basis (Fin N) ℂ (Fin N → ℂ) := basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  -- The change-of-basis matrix: eigenvectors as columns.
  let V : Matrix (Fin N) (Fin N) ℂ := (Pi.basisFun ℂ (Fin N)).toMatrix ⇑b
  have hVentry : ∀ i j, V i j = v j i := by
    intro i j
    change (Pi.basisFun ℂ (Fin N)).toMatrix ⇑b i j = v j i
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, hb]
  haveI hVinv : Invertible V := Basis.invertibleToMatrix (Pi.basisFun ℂ (Fin N)) b
  -- The eigenvector equation in matrix form.
  have hcol : ∀ j, A *ᵥ (v j) = (t j) • v j := by
    intro j
    have h2 := (hvspec j).apply_eq_smul
    change A *ᵥ (v j) = (t j) • v j at h2
    exact h2
  -- `A * V = V * D`, columnwise from the eigenvector equation.
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => t i) with hD_def
  have hAV : A * V = V * D := by
    ext i j
    have lhs : (A * V) i j = (A *ᵥ (v j)) i := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hVentry]
    rw [lhs, hcol j, hD_def, Matrix.mul_diagonal]
    simp only [hVentry, Pi.smul_apply, smul_eq_mul]
    ring
  -- Hence `A = V * D * V⁻¹`.
  have hVVinv : V * V⁻¹ = 1 := Matrix.mul_inv_of_invertible V
  have hA_conj : A = V * D * V⁻¹ := by
    rw [← hAV, Matrix.mul_assoc, hVVinv, Matrix.mul_one]
  -- Package the eigenvalues as units and the base change as a `GL` element.
  let t' : Fin N → ℂˣ := fun i => Units.mk0 (t i) (ht_ne i)
  have ht'_val : ∀ i, (t' i : ℂ) = t i := fun _ => rfl
  let h : Matrix.GeneralLinearGroup (Fin N) ℂ := unitOfInvertible V
  refine ⟨t', h, ?_⟩
  -- Reduce the `GL` equation to the underlying matrix equation.
  refine Units.ext ?_
  have hh_val : (h : Matrix (Fin N) (Fin N) ℂ) = V := rfl
  have hdiag_val : (diagTorus ℂ N t' : Matrix (Fin N) (Fin N) ℂ) = D := by
    rw [hD_def]
    exact congrArg Matrix.diagonal (funext ht'_val)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv, hh_val, hdiag_val, ← hA_conj, hA_def]

end

end Etingof
