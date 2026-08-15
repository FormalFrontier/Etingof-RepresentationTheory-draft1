/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

open scoped TensorProduct
open Matrix

noncomputable section

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

/-- Evaluation at a general linear matrix preserves multiplication. -/
theorem evaluate_mul {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p q : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (p * q) = RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g p * RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g q := by
  simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_mul]

/-- Evaluation at a general linear matrix commutes with a finite sum of polynomials. -/
theorem evaluate_sum {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (s : Finset ι) (f : ι → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (∑ i ∈ s, f i) = ∑ i ∈ s, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (f i) := by
  simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_sum]

/-- Evaluation at a general linear matrix commutes with a finite product of polynomials. -/
theorem evaluate_prod {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (s : Finset ι) (f : ι → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (∏ i ∈ s, f i) = ∏ i ∈ s, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (f i) := by
  simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_prod]

/-- Evaluating a constant polynomial at a general linear matrix returns that constant. -/
theorem evaluate_C {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.C r) = r := by
  simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, MvPolynomial.eval_C]

/-- Evaluating the variable indexed by a pair of finite indices returns the corresponding matrix entry. -/
theorem evaluate_X_entry {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (i j : Fin N) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.X (Sum.inl (i, j))) = g.val i j := by
  change MvPolynomial.eval _ (MvPolynomial.X (Sum.inl (i, j))) = _
  rw [MvPolynomial.eval_X]
  rfl

/-- Defines a multivariate polynomial over a field with the displayed index type. -/

def auxiliaryPolynomial (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k :=
  (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).det

/-- Evaluating the auxiliary polynomial at a general linear matrix returns its determinant. -/
@[simp]
theorem evaluate_auxiliaryPolynomial {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (auxiliaryPolynomial k N) = (Matrix.GeneralLinearGroup.det g : k) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  unfold RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation auxiliaryPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply]

end RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

/-- Shows that the displayed property is preserved after scaling each linear map by the determinant of its matrix argument. -/

theorem auxiliary_det_smul {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      (fun g => (Matrix.GeneralLinearGroup.det g : k) • ρ g) := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b, fun a c => RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.auxiliaryPolynomial k N * P a c, fun g a c => ?_⟩
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c,
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_auxiliaryPolynomial]

/-- Shows that the displayed property holds for the restrictions to a submodule preserved by every matrix-indexed linear map. -/

theorem auxiliary_restrict {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ)
    (W : Submodule k Y) [Module.Finite k W]
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (fun g => (ρ g).restrict (hW g)) := by
  classical
  obtain ⟨M, B, P, hP⟩ := h

  let b' : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W

  obtain ⟨W', hWW'⟩ := W.exists_isCompl
  let π : Y →ₗ[k] W := W.projectionOnto W' hWW'
  have hπincl : ∀ w : W, π (W.subtype w) = w := fun w =>
    W.projectionOnto_apply_left hWW' w
  refine ⟨Module.finrank k W, b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (W.subtype (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (π (B e)) a), fun g a c => ?_⟩

  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp π)
  have hφ_apply : ∀ y, φ y = b'.repr (π y) a := fun _ => rfl
  have hcoe : (W.subtype) ((ρ g).restrict (hW g) (b' c)) = ρ g (W.subtype (b' c)) :=
    LinearMap.coe_restrict_apply (hW g) (b' c)

  have hlhs : b'.repr ((ρ g).restrict (hW g) (b' c)) a
      = ∑ d, ∑ e, B.repr (W.subtype (b' c)) d
          * (RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P e d) * b'.repr (π (B e)) a) := by
    have h1 : (ρ g).restrict (hW g) (b' c) = π (ρ g (W.subtype (b' c))) := by
      rw [← hcoe, hπincl]
    rw [show b'.repr ((ρ g).restrict (hW g) (b' c)) a = φ (ρ g (W.subtype (b' c))) from by
      rw [hφ_apply, h1]]

    rw [show ρ g (W.subtype (b' c))
        = ∑ d, B.repr (W.subtype (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show W.subtype (b' c) = ∑ d, B.repr (W.subtype (b' c)) d • B d from
        (B.sum_repr (W.subtype (b' c))).symm]
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [map_smul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, smul_eq_mul]

    have hd : φ (ρ g (B d))
        = ∑ e, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P e d) * b'.repr (π (B e)) a := by
      conv_lhs => rw [show ρ g (B d) = ∑ e, B.repr (ρ g (B d)) e • B e from
        (B.sum_repr (ρ g (B d))).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, hP g e d, hφ_apply]
    rw [hd, Finset.mul_sum]
  rw [hlhs, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_C, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_C]
  ring

end RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

namespace RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

/-- Defines a basis indexed by functions from `Fin n` to `Fin N` for the displayed module. -/

def auxiliaryBasis (k : Type*) [Field k] (N n : ℕ) :
    Module.Basis (Fin n → Fin N) k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
  Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun k (Fin N))

/-- Computes a coordinate of the displayed action in the given basis as a finite product of matrix entries. -/

theorem action_basis_repr_apply {k : Type*} [Field k] {N n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (f h : Fin n → Fin N) :
    (auxiliaryBasis k N n).repr (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g (auxiliaryBasis k N n f)) h
      = ∏ m, (g.val) (h m) (f m) := by
  change (auxiliaryBasis k N n).repr
      (PiTensorProduct.map (fun _ => Matrix.mulVecLin (R := k) g.val)
        (auxiliaryBasis k N n f)) h = _
  simp only [auxiliaryBasis, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Pi.basisFun_repr, Matrix.mulVecLin_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  rfl

/-- Establishes the first displayed predicate for the given matrix-indexed linear representation. -/

theorem auxiliaryRepresentation_property (k : Type*) [Field k] (N n : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n) := by
  classical
  set ι := Fin n → Fin N
  set eqv : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with heqv
  refine ⟨Fintype.card ι, (auxiliaryBasis k N n).reindex eqv.symm,
    fun a c => ∏ m, MvPolynomial.X (Sum.inl (eqv a m, eqv c m)),
    fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  simp only [Equiv.symm_symm]
  rw [action_basis_repr_apply, evaluate_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [evaluate_X_entry]

/-- Establishes the second displayed predicate for the given representation. -/

theorem auxiliaryRepresentation_property_two (k : Type*) [Field k] (N n : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty N (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n) :=
  (auxiliaryRepresentation_property k N n).impliesRepresentationProperty

end RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

/-- Transfers the displayed property along a linear equivalence intertwining two matrix-indexed families of linear maps. -/

theorem auxiliary_of_linearEquiv {k : Type*} [Field k] {N : ℕ}
    {Y Z : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Z] [Module k Z] [Module.Finite k Z]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {σ : Matrix.GeneralLinearGroup (Fin N) k → Z →ₗ[k] Z}
    (e : Y ≃ₗ[k] Z)
    (hcomm : ∀ g y, e (ρ g y) = σ g (e y))
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N σ := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b.map e, P, fun g a c => ?_⟩

  have hbe : ∀ w, (b.map e).repr (e w) = b.repr w := by
    intro w
    rw [show (b.map e).repr = e.symm.trans b.repr from rfl, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  rw [Module.Basis.map_apply, ← hcomm g (b c), hbe (ρ g (b c))]
  exact hP g a c

end RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

namespace RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

/-- Defines a scalar-valued function of a general linear matrix and an element of the displayed index type. -/

noncomputable def auxiliaryEvaluationValue {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) : RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N → k :=
  Sum.elim (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
           (fun _ => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)

/-- Identifies the displayed evaluation map with multivariate-polynomial evaluation at the associated variable assignment. -/
theorem evaluate_eq_eval {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g p = MvPolynomial.eval (auxiliaryEvaluationValue g) p := rfl

/-- Evaluating the variable indexed by a unit returns the inverse determinant of the matrix. -/

theorem evaluate_X_unit {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (u : Unit) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.X (Sum.inr u))
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by
  change MvPolynomial.eval _ (MvPolynomial.X (Sum.inr u)) = _
  rw [MvPolynomial.eval_X]
  rfl

/-- Evaluation commutes with taking the specified entry of an adjugate matrix built from polynomial variables. -/

theorem evaluate_adjugate {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a b : Fin N) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
        ((Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).adjugate a b)
      = (g : Matrix (Fin N) (Fin N) k).adjugate a b := by
  have hmap : (MvPolynomial.eval (auxiliaryEvaluationValue g)).mapMatrix
        (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j)))
      = (g : Matrix (Fin N) (Fin N) k) := by
    ext a' b'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact evaluate_X_entry g a' b'
  rw [evaluate_eq_eval]
  calc MvPolynomial.eval (auxiliaryEvaluationValue g)
          ((Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).adjugate a b)
      = ((MvPolynomial.eval (auxiliaryEvaluationValue g)).mapMatrix
          ((Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).adjugate)) a b :=
        rfl
    _ = (Matrix.adjugate ((MvPolynomial.eval (auxiliaryEvaluationValue g)).mapMatrix
          (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))))) a b := by
        rw [RingHom.map_adjugate]
    _ = (g : Matrix (Fin N) (Fin N) k).adjugate a b := by rw [hmap]

/-- Defines a map from the displayed index type to multivariate polynomials. -/

noncomputable def auxiliarySubstitution (k : Type*) [Field k] (N : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k :=
  Sum.elim
    (fun ij : Fin N × Fin N => MvPolynomial.X (Sum.inr ()) *
      (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).adjugate ij.1 ij.2)
    (fun _ => auxiliaryPolynomial k N)

/-- Evaluating a polynomial after the displayed variable substitution agrees with evaluating the original polynomial at the inverse matrix. -/

theorem evaluate_bind {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.bind₁ (auxiliarySubstitution k N) p) = RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g⁻¹ p := by
  have hvar : (fun i => RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (auxiliarySubstitution k N i)) = auxiliaryEvaluationValue g⁻¹ := by
    funext i
    cases i with
    | inl ij =>
        obtain ⟨a, b⟩ := ij
        change RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
            (MvPolynomial.X (Sum.inr ()) *
              (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).adjugate a b)
          = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k) a b
        rw [evaluate_mul, evaluate_X_unit, evaluate_adjugate,
          Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
          Ring.inverse_eq_inv]
    | inr u =>
        change RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (auxiliaryPolynomial k N)
          = (((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k).det)⁻¹
        rw [evaluate_auxiliaryPolynomial, Matrix.GeneralLinearGroup.val_det_apply,
          Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]
  rw [evaluate_eq_eval, evaluate_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁,
    MvPolynomial.aeval_eq_eval]
  rw [show (fun i => MvPolynomial.aeval (auxiliaryEvaluationValue g) (auxiliarySubstitution k N i)) = auxiliaryEvaluationValue g⁻¹ from hvar]

end RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

/-- Transfers the displayed property from a representation to its dual representation. -/

theorem auxiliary_dual {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) Y)
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (Representation.dual ρ) := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b.dualBasis, fun a c => MvPolynomial.bind₁ (RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.auxiliarySubstitution k N) (P c a), fun g a c => ?_⟩
  rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_bind, Representation.dual_apply, Module.Dual.transpose_apply,
    Module.Basis.dualBasis_repr, LinearMap.comp_apply, Module.Basis.dualBasis_apply]
  exact hP g⁻¹ c a

end RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

namespace RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

/-- Establishes the first displayed predicate for the representation obtained from the given field-dependent data. -/

theorem auxiliaryFDRep_property {k : Type*} [Field k] [IsAlgClosed k] (N : ℕ)
    (lam : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam).ρ := by
  unfold RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation
  rw [FDRep.of_ρ']
  exact (auxiliaryRepresentation_property k N (∑ i, lam i)).auxiliary_restrict
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam)
    (fun g v hv => RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule_invariant k N lam g v hv)

/-- Establishes the second displayed predicate for the representation obtained from the given field-dependent data. -/

theorem auxiliaryFDRep_property_two {k : Type*} [Field k] [IsAlgClosed k]
    (N : ℕ) (lam : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty N (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam).ρ :=
  (auxiliaryFDRep_property N lam).impliesRepresentationProperty

end RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
