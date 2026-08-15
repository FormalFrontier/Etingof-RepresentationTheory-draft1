/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.UnitTupleActions

open Matrix Module Polynomial

namespace RepresentationTheory.LinearAlgebra.GeneralLinearGroup.Auxiliary

noncomputable section

variable {k : Type*} [Field k] [DecidableEq k]

/-- If the set of roots of the characteristic polynomial has cardinality equal to the matrix
size, the element is conjugate to an element from the auxiliary family. -/
theorem exists_eq_conjugate_auxiliary_of_card_roots_eq
    (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (hdist : (g : Matrix (Fin N) (Fin N) k).charpoly.roots.toFinset.card = N) :
    ∃ (t : Fin N → kˣ) (h : Matrix.GeneralLinearGroup (Fin N) k),
      g = h * RepresentationTheory.UnitTupleActions.unitTupleElement k N t * h⁻¹ := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact ⟨fun i => i.elim0, 1, Subsingleton.elim _ _⟩
  have : NeZero N := ⟨hNpos.ne'⟩
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) with hA_def
  have hAunit : IsUnit A := ⟨g, rfl⟩
  set s : Finset k := A.charpoly.roots.toFinset with hs_def
  have hcard_s : Fintype.card s = N := by rw [Fintype.card_coe]; exact hdist
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard_s).symm
  let t : Fin N → k := fun i => (e i : k)
  have ht_inj : Function.Injective t :=
    fun i j h => e.injective (Subtype.ext h)
  have ht_mem : ∀ i, t i ∈ spectrum k A := by
    intro i
    have hroot : A.charpoly.IsRoot (t i) := by
      have hmem : t i ∈ A.charpoly.roots.toFinset := (e i).2
      rw [Multiset.mem_toFinset, mem_roots'] at hmem
      exact hmem.2
    exact (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hroot
  let f : Module.End k (Fin N → k) := Matrix.toLin' A
  have hf_eig : ∀ i, f.HasEigenvalue (t i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact ht_mem i
  have ht_ne : ∀ i, t i ≠ 0 := by
    intro i hzero
    have : (0 : k) ∈ spectrum k A := hzero ▸ ht_mem i
    exact ((spectrum.zero_mem_iff k).mp this) hAunit
  let v : Fin N → (Fin N → k) := fun i => (hf_eig i).exists_hasEigenvector.choose
  have hvspec : ∀ i, f.HasEigenvector (t i) (v i) := fun i =>
    (hf_eig i).exists_hasEigenvector.choose_spec
  have hli : LinearIndependent k v :=
    Module.End.eigenvectors_linearIndependent' f t ht_inj v hvspec
  have hcard_eq : Fintype.card (Fin N) = Module.finrank k (Fin N → k) := by
    rw [Module.finrank_fintype_fun_eq_card]
  let b : Basis (Fin N) k (Fin N → k) := basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  let V : Matrix (Fin N) (Fin N) k := (Pi.basisFun k (Fin N)).toMatrix ⇑b
  have hVentry : ∀ i j, V i j = v j i := by
    intro i j
    change (Pi.basisFun k (Fin N)).toMatrix ⇑b i j = v j i
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, hb]
  haveI hVinv : Invertible V := Basis.invertibleToMatrix (Pi.basisFun k (Fin N)) b
  have hcol : ∀ j, A *ᵥ (v j) = (t j) • v j := by
    intro j
    have h2 := (hvspec j).apply_eq_smul
    change A *ᵥ (v j) = (t j) • v j at h2
    exact h2
  set D : Matrix (Fin N) (Fin N) k := Matrix.diagonal (fun i => t i) with hD_def
  have hAV : A * V = V * D := by
    ext i j
    have lhs : (A * V) i j = (A *ᵥ (v j)) i := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hVentry]
    rw [lhs, hcol j, hD_def, Matrix.mul_diagonal]
    simp only [hVentry, Pi.smul_apply, smul_eq_mul]
    ring
  have hVVinv : V * V⁻¹ = 1 := Matrix.mul_inv_of_invertible V
  have hA_conj : A = V * D * V⁻¹ := by
    rw [← hAV, Matrix.mul_assoc, hVVinv, Matrix.mul_one]
  let t' : Fin N → kˣ := fun i => Units.mk0 (t i) (ht_ne i)
  have ht'_val : ∀ i, (t' i : k) = t i := fun _ => rfl
  let h : Matrix.GeneralLinearGroup (Fin N) k := unitOfInvertible V
  refine ⟨t', h, ?_⟩
  refine Units.ext ?_
  have hh_val : (h : Matrix (Fin N) (Fin N) k) = V := rfl
  have hdiag_val :
      (RepresentationTheory.UnitTupleActions.unitTupleElement k N t' :
        Matrix (Fin N) (Fin N) k) = D := by
    rw [hD_def]
    exact congrArg Matrix.diagonal (funext ht'_val)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv, hh_val, hdiag_val, ← hA_conj, hA_def]

end

end RepresentationTheory.LinearAlgebra.GeneralLinearGroup.Auxiliary
