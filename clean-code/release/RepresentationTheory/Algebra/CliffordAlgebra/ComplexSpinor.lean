/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import RepresentationTheory.Alignment.Attribute

/-! # Complex Spinor -/

namespace RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor

open LinearMap

/-- An auxiliary complex vector space indexed by a natural number. -/
abbrev spinorSpace (n : ℕ) := ExteriorAlgebra ℂ (Fin n → ℂ)

/-- An auxiliary complex vector space indexed by a natural number. -/
abbrev quadraticSpace (n : ℕ) :=
  Module.Dual ℂ (Fin n → ℂ) × (Fin n → ℂ)

/-- A quadratic form on the displayed complex vector space. -/
noncomputable def quadraticForm (n : ℕ) : QuadraticForm ℂ (quadraticSpace n) :=
  QuadraticForm.dualProd ℂ (Fin n → ℂ)

/-- A linear map from a finite complex function space to endomorphisms of the displayed spinor space. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def vectorAction (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (spinorSpace n) :=
  (Algebra.lmul ℂ (spinorSpace n)).toLinearMap.comp (ExteriorAlgebra.ι ℂ)

/-- A linear map from the dual of a finite complex function space to endomorphisms of the displayed spinor space. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def dualAction (n : ℕ) :
    Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (spinorSpace n) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Fin n → ℂ)))

/-- The square of the displayed vector action is zero. -/
@[simp]
theorem vectorAction_sq (n : ℕ) (u : Fin n → ℂ) :
    vectorAction n u * vectorAction n u = 0 := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ u * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The square of the displayed dual action is zero. -/
@[simp]
theorem dualAction_sq (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) :
    dualAction n f * dualAction n f = 0 := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.contractLeft f
    (CliffordAlgebra.contractLeft f x) = 0
  exact CliffordAlgebra.contractLeft_contractLeft f x

/-- The sum of the displayed dual and vector actions is scalar multiplication by their evaluation. -/
theorem dualAction_add_vectorAction (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (u : Fin n → ℂ) (x : spinorSpace n) :
    dualAction n f (vectorAction n u x) + vectorAction n u (dualAction n f x) = f u • x := by
  change CliffordAlgebra.contractLeft f (ExteriorAlgebra.ι ℂ u * x)
    + ExteriorAlgebra.ι ℂ u * CliffordAlgebra.contractLeft f x = f u • x
  rw [CliffordAlgebra.contractLeft_ι_mul]
  module

/-- The sum of the displayed dual and vector action products is scalar multiplication of one. -/
theorem dualAction_add_vectorAction_eq_smul_one (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (u : Fin n → ℂ) :
    dualAction n f * vectorAction n u + vectorAction n u * dualAction n f =
      f u • (1 : Module.End ℂ (spinorSpace n)) := by
  apply LinearMap.ext
  intro x
  exact dualAction_add_vectorAction n f u x

/-- A linear map from the displayed quadratic space to endomorphisms of the spinor space. -/
noncomputable def quadraticSpaceAction (n : ℕ) :
    quadraticSpace n →ₗ[ℂ] Module.End ℂ (spinorSpace n) :=
  LinearMap.coprod (dualAction n) (vectorAction n)

/-- The square of the displayed action is the stated scalar multiple of one. -/
theorem quadraticSpaceAction_sq (n : ℕ) (x : quadraticSpace n) :
    quadraticSpaceAction n x * quadraticSpaceAction n x =
      quadraticForm n x • (1 : Module.End ℂ (spinorSpace n)) := by
  apply LinearMap.ext
  intro y
  rcases x with ⟨f, u⟩
  change ((dualAction n f + vectorAction n u) *
      (dualAction n f + vectorAction n u)) y = f u • y
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  have hc := LinearMap.congr_fun (vectorAction_sq n u) y
  have ha := LinearMap.congr_fun (dualAction_sq n f) y
  change vectorAction n u (vectorAction n u y) = 0 at hc
  change dualAction n f (dualAction n f y) = 0 at ha
  rw [map_add, map_add, ha, hc, zero_add, add_zero, dualAction_add_vectorAction]

/-- An algebra homomorphism from the displayed Clifford algebra to endomorphisms of the spinor space. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def cliffordRepresentation (n : ℕ) :
    CliffordAlgebra (quadraticForm n) →ₐ[ℂ] Module.End ℂ (spinorSpace n) :=
  CliffordAlgebra.lift _ ⟨quadraticSpaceAction n, quadraticSpaceAction_sq n⟩

/-- The Clifford representation sends the displayed dual generator to the dual action. -/
@[simp]
theorem cliffordRepresentation_dual (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) :
    cliffordRepresentation n
        (CliffordAlgebra.ι (quadraticForm n) (f, 0)) =
      dualAction n f := by
  rw [cliffordRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [quadraticSpaceAction]

/-- The Clifford representation sends the displayed vector generator to the vector action. -/
@[simp]
theorem cliffordRepresentation_vector (n : ℕ) (u : Fin n → ℂ) :
    cliffordRepresentation n
        (CliffordAlgebra.ι (quadraticForm n) (0, u)) =
      vectorAction n u := by
  rw [cliffordRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [quadraticSpaceAction]

/-- The dimension of the displayed spinor space is two to the indicated power. -/
@[simp]
theorem finrank_spinorSpace (n : ℕ) :
    Module.finrank ℂ (spinorSpace n) = 2 ^ n := by
  rw [Module.finrank_eq_card_basis
    (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n))),
    Fintype.card_finset, Fintype.card_fin]

/-- An endomorphism of the displayed spinor space. -/
noncomputable def gradingInvolution (n : ℕ) : Module.End ℂ (spinorSpace n) :=
  CliffordAlgebra.involute.toLinearMap

/-- The square of the displayed endomorphism is one. -/
@[simp]
theorem gradingInvolution_sq (n : ℕ) :
    gradingInvolution n * gradingInvolution n = 1 := by
  apply LinearMap.ext
  intro x
  exact CliffordAlgebra.involute_involute x

/-- The displayed dual action anticommutes with Clifford involution. -/
theorem dualAction_involute (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (x : spinorSpace n) :
    dualAction n f (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (dualAction n f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [dualAction]
  | add x y hx hy =>
      simp only [map_add, hx, hy, neg_add]
  | ι_mul x u hx =>
      change CliffordAlgebra.contractLeft f (CliffordAlgebra.involute x) =
        -CliffordAlgebra.involute (CliffordAlgebra.contractLeft f x) at hx
      rw [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg]
      change -(CliffordAlgebra.contractLeft f
        (ExteriorAlgebra.ι ℂ u * CliffordAlgebra.involute x)) =
        -CliffordAlgebra.involute
          (CliffordAlgebra.contractLeft f (ExteriorAlgebra.ι ℂ u * x))
      rw [CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
        CliffordAlgebra.involute_ι, hx]
      noncomm_ring

/-- The displayed endomorphism anticommutes with the vector action. -/
theorem gradingInvolution_mul_vectorAction (n : ℕ) (u : Fin n → ℂ) :
    gradingInvolution n * vectorAction n u = -(vectorAction n u * gradingInvolution n) := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.involute (ExteriorAlgebra.ι ℂ u * x) =
    -(ExteriorAlgebra.ι ℂ u * CliffordAlgebra.involute x)
  rw [map_mul, CliffordAlgebra.involute_ι, neg_mul]

/-- The displayed endomorphism anticommutes with the dual action. -/
theorem gradingInvolution_mul_dualAction (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) :
    gradingInvolution n * dualAction n f = -(dualAction n f * gradingInvolution n) := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.involute (dualAction n f x) =
    -dualAction n f (CliffordAlgebra.involute x)
  rw [dualAction_involute]
  simp

/-- The displayed endomorphism anticommutes with the quadratic-space action. -/
theorem gradingInvolution_mul_quadraticSpaceAction (n : ℕ) (x : quadraticSpace n) :
    gradingInvolution n * quadraticSpaceAction n x =
      -(quadraticSpaceAction n x * gradingInvolution n) := by
  rcases x with ⟨f, u⟩
  change gradingInvolution n * (dualAction n f + vectorAction n u) =
    -((dualAction n f + vectorAction n u) * gradingInvolution n)
  rw [mul_add, add_mul, gradingInvolution_mul_dualAction,
    gradingInvolution_mul_vectorAction, neg_add]

/-- The symmetric bilinear form associated to the hyperbolic quadratic form. -/
private noncomputable def hyperbolicB (n : ℕ) :
    LinearMap.BilinForm ℂ (quadraticSpace n) :=
  QuadraticMap.associated (R := ℂ) (quadraticForm n)

/-- The standard hyperbolic bilinear form is nondegenerate. -/
private theorem hyperbolicB_nondegenerate (n : ℕ) :
    (hyperbolicB n).Nondegenerate := by
  have hB : QuadraticMap.associated (R := ℂ) (quadraticForm n) =
      (2 : ℂ)⁻¹ • LinearMap.dualProd ℂ (Fin n → ℂ) := by
    apply LinearMap.ext₂
    intro x y
    rcases x with ⟨f, u⟩
    rcases y with ⟨g, v⟩
    simp [quadraticForm, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd]
    ring
  change (QuadraticMap.associated (R := ℂ) (quadraticForm n)).Nondegenerate
  rw [(QuadraticForm.associated_isSymm ℂ
    (quadraticForm n)).isRefl.nondegenerate_iff_separatingLeft]
  intro x hx
  apply (LinearMap.separatingLeft_dualProd
    (R := ℂ) (M := Fin n → ℂ)).2 (Module.eval_apply_injective ℂ)
  intro y
  have hxy := hx y
  rw [hB] at hxy
  simp only [LinearMap.smul_apply, smul_eq_mul] at hxy
  exact (mul_eq_zero.mp hxy).resolve_left (inv_ne_zero two_ne_zero)

/-- The Clifford algebra of the displayed quadratic form is a simple ring. -/
theorem clifford_isSimpleRing (n : ℕ) :
    IsSimpleRing (CliffordAlgebra (quadraticForm n)) := by
  have hdim : Module.finrank ℂ (quadraticSpace n) = 2 * n := by
    simp [quadraticSpace, Module.finrank_prod]
    omega
  obtain ⟨S, instAdd, instModule, hS, ⟨e⟩⟩ :=
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.exists_algEquiv_end_of_finrank_even (V := quadraticSpace n) (hyperbolicB n)
      (QuadraticMap.associated_isSymm ℂ (quadraticForm n))
      (hyperbolicB_nondegenerate n) n hdim
  letI : AddCommGroup S := instAdd
  letI : Module ℂ S := instModule
  have hpos : 0 < Module.finrank ℂ S := by rw [hS]; positivity
  letI : Module.Finite ℂ S := Module.finite_of_finrank_pos hpos
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hpos
  letI : Nonempty (Fin (Module.finrank ℂ S)) := ⟨⟨0, hpos⟩⟩
  have hEnd : IsSimpleRing (Module.End ℂ S) :=
    IsSimpleRing.of_ringEquiv
      (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ S)).symm.toRingEquiv
      (inferInstance : IsSimpleRing
        (Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ))
  have hCliff : IsSimpleRing (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra (hyperbolicB n)) :=
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hEnd
  have hq : _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm (hyperbolicB n) = quadraticForm n := by
    exact QuadraticMap.toQuadraticMap_associated ℂ (quadraticForm n)
  rw [← hq]
  exact hCliff

/-- The source and target of the explicit spinor representation have equal dimension. -/
private theorem finrank_hyperbolicClifford_eq_end (n : ℕ) :
    Module.finrank ℂ (CliffordAlgebra (quadraticForm n)) =
      Module.finrank ℂ (Module.End ℂ (spinorSpace n)) := by
  have hq : _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm (hyperbolicB n) = quadraticForm n := by
    exact QuadraticMap.toQuadraticMap_associated ℂ (quadraticForm n)
  have hdim : Module.finrank ℂ (quadraticSpace n) = 2 * n := by
    simp [quadraticSpace, Module.finrank_prod]
    omega
  have hsource :
      Module.finrank ℂ (CliffordAlgebra (quadraticForm n)) = 2 ^ (2 * n) := by
    rw [← hq]
    simpa [hdim] using
      _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.finrank_eq_two_pow (hyperbolicB n)
        (Module.finBasis ℂ (quadraticSpace n))
  letI : Module.Finite ℂ (spinorSpace n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  rw [hsource, Module.finrank_linearMap, finrank_spinorSpace,
    mul_comm 2 n, pow_mul]
  simp [pow_two]

/-- The displayed Clifford algebra representation is bijective. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem cliffordRepresentation_bijective (n : ℕ) :
    Function.Bijective (cliffordRepresentation n) := by
  letI : IsSimpleRing (CliffordAlgebra (quadraticForm n)) :=
    clifford_isSimpleRing n
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  have hinj : Function.Injective (cliffordRepresentation n) :=
    RingHom.injective (cliffordRepresentation n).toRingHom
  refine ⟨hinj, ?_⟩
  letI : Module.Finite ℂ (CliffordAlgebra (quadraticForm n)) := by
    haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
    haveI : Module.Finite ℂ (ExteriorAlgebra ℂ (quadraticSpace n)) :=
      Module.Finite.of_basis
        (Module.Basis.ExteriorAlgebra
          (Module.finBasis ℂ (quadraticSpace n)))
    exact Module.Finite.equiv
      (CliffordAlgebra.equivExterior (quadraticForm n)).symm
  letI : Module.Finite ℂ (spinorSpace n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (cliffordRepresentation n).toLinearMap)
    (finrank_hyperbolicClifford_eq_end n)).mp hinj

/-- The displayed spinor space is a simple module over its Clifford algebra. -/
@[source_ref "Chapter3/Problem3.9.5" (role := primary)]
theorem spinorSpace_isSimpleModule (n : ℕ) :
    @IsSimpleModule (CliffordAlgebra (quadraticForm n)) _ (spinorSpace n) _
      (Module.compHom (spinorSpace n) (cliffordRepresentation n).toRingHom) := by
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  letI : Module (CliffordAlgebra (quadraticForm n)) (spinorSpace n) :=
    Module.compHom (spinorSpace n) (cliffordRepresentation n).toRingHom
  letI : RingHomSurjective (cliffordRepresentation n).toRingHom :=
    ⟨(cliffordRepresentation_bijective n).2⟩
  let e : spinorSpace n →ₛₗ[(cliffordRepresentation n).toRingHom] spinorSpace n :=
    { AddMonoidHom.id (spinorSpace n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

end RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor
