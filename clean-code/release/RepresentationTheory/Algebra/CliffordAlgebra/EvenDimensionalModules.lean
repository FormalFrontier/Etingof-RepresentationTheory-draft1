/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import RepresentationTheory.Alignment.Attribute

/-! # Even-Dimensional Modules -/

namespace RepresentationTheory.Algebra.CliffordAlgebra.EvenDimensionalModules

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The bilinear form associated to the standard even-dimensional quadratic form separates points in its left argument. -/
theorem standardEvenQuadraticForm_associated_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)).SeparatingLeft := by
  intro x hx
  rcases x with ⟨f, u⟩
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    have h := hx (0, v)
    simpa [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd] using h
  · apply funext
    intro i
    let g : Module.Dual ℂ (Fin n → ℂ) :=
      LinearMap.proj i
    have h := hx (g, 0)
    simpa [g, _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd] using h

/-- An isometric equivalence from the quadratic form associated to the given bilinear form to the standard even-dimensional quadratic form. -/
noncomputable def standardEvenQuadraticFormIsometryEquiv
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B).IsometryEquiv (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) := by
  let e₀ : V ≃ₗ[ℂ] _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpace n :=
    LinearEquiv.ofFinrankEq V (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpace n) (by
      rw [hdim]
      simp [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpace, Module.finrank_prod]
      omega)
  let Q₀ : QuadraticForm ℂ V :=
    (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n).comp e₀.toLinearMap
  have hB : (QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B)).SeparatingLeft := by
    rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    exact hnd.1
  have hQ₀ : (QuadraticMap.associated (R := ℂ) Q₀).SeparatingLeft := by
    intro x hx
    apply e₀.injective
    rw [map_zero]
    apply standardEvenQuadraticForm_associated_separatingLeft n
    intro y
    obtain ⟨z, rfl⟩ := e₀.surjective y
    have := hx z
    simpa [Q₀, QuadraticMap.associated_comp] using this
  let e₁ : (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B).IsometryEquiv Q₀ :=
    Classical.choice
      (QuadraticForm.equivalent_of_isAlgClosed (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B) Q₀ hB hQ₀)
  exact e₁.trans
    (QuadraticMap.isometryEquivOfCompLinearEquiv
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) e₀).symm

/-- The coordinate vector at an index of a finite complex function space. -/
def coordinateVector (n : ℕ) (i : Fin n) : Fin n → ℂ :=
  fun j => if i = j then 1 else 0

/-- The coordinate covector at an index of a finite complex function space. -/
def coordinateCovector (n : ℕ) (i : Fin n) :
    Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.proj i

/-- The first indexed family of vectors for a nondegenerate symmetric complex bilinear form of dimension twice its index size. -/
noncomputable def firstIsotropicFamily
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) : V :=
  (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim).symm
    (0, coordinateVector n i)

/-- The second indexed family of vectors for a nondegenerate symmetric complex bilinear form of dimension twice its index size. -/
noncomputable def secondIsotropicFamily
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) : V :=
  (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim).symm
    (coordinateCovector n i, 0)

/-- The isometry identifies the given bilinear form with the form associated to the standard even-dimensional quadratic form. -/
theorem standardEvenQuadraticFormIsometryEquiv_associated
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (x y : V) :
    B x y =
      QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)
        (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim x)
        (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim y) := by
  let e := standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim
  change B x y =
    QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) (e x) (e y)
  calc
    B x y =
        QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B) x y := by
      rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    _ = QuadraticMap.associated (R := ℂ) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) (e x) (e y) := by
      have hxy :
          _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n (e x + e y) = _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B (x + y) := by
        calc
          _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n (e x + e y) =
              _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n (e (x + y)) :=
            congrArg (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) (e.toLinearEquiv.map_add x y).symm
          _ = _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B (x + y) := e.map_app (x + y)
      simp only [QuadraticMap.associated_apply]
      rw [hxy, e.map_app, e.map_app]

/-- The bilinear form vanishes on every pair of vectors in the first indexed family. -/
@[simp]
theorem firstIsotropicFamily_pair_self
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (firstIsotropicFamily B hsymm hnd n hdim i)
      (firstIsotropicFamily B hsymm hnd n hdim j) = 0 := by
  rw [standardEvenQuadraticFormIsometryEquiv_associated B hsymm hnd n hdim]
  simp only [firstIsotropicFamily, QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm, QuadraticMap.associated_apply,
    QuadraticForm.dualProd]

/-- The bilinear form vanishes on every pair of vectors in the second indexed family. -/
@[simp]
theorem secondIsotropicFamily_pair_self
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (secondIsotropicFamily B hsymm hnd n hdim i)
      (secondIsotropicFamily B hsymm hnd n hdim j) = 0 := by
  rw [standardEvenQuadraticFormIsometryEquiv_associated B hsymm hnd n hdim]
  simp only [secondIsotropicFamily, QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm, QuadraticMap.associated_apply,
    QuadraticForm.dualProd]

/-- Pairing the first and second indexed families gives one half on matching indices and zero otherwise. -/
@[simp]
theorem firstIsotropicFamily_pair_secondIsotropicFamily
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (firstIsotropicFamily B hsymm hnd n hdim i)
      (secondIsotropicFamily B hsymm hnd n hdim j) =
        if i = j then (2 : ℂ)⁻¹ else 0 := by
  rw [standardEvenQuadraticFormIsometryEquiv_associated B hsymm hnd n hdim]
  simp only [firstIsotropicFamily, secondIsotropicFamily,
    QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [coordinateVector, coordinateCovector,
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm, QuadraticMap.associated_apply, QuadraticForm.dualProd]

/-- The standard representation of the Clifford algebra of an even-dimensional nondegenerate symmetric complex bilinear form. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def standardCliffordRepresentation
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B →ₐ[ℂ] Module.End ℂ (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) :=
  (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.cliffordRepresentation n).comp
    (CliffordAlgebra.equivOfIsometry
      (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim)).toAlgHom

/-- The standard representation sends a Clifford generator to the prescribed action of its image under the quadratic-form isometry. -/
@[simp]
theorem standardCliffordRepresentation_iota
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (x : V) :
    standardCliffordRepresentation B hsymm hnd n hdim
        (CliffordAlgebra.ι (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B) x) =
      _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpaceAction n (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim x) := by
  simp [standardCliffordRepresentation, _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.cliffordRepresentation]

/-- The standard representation sends a generator from the first isotropic family to the prescribed operator on the corresponding coordinate vector. -/
@[simp]
theorem standardCliffordRepresentation_firstIsotropicFamily
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) :
    standardCliffordRepresentation B hsymm hnd n hdim
        (CliffordAlgebra.ι (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B)
          (firstIsotropicFamily B hsymm hnd n hdim i)) =
      _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.vectorAction n (coordinateVector n i) := by
  rw [standardCliffordRepresentation_iota]
  simp [firstIsotropicFamily, _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpaceAction]

/-- The standard representation sends a generator from the second isotropic family to the prescribed operator on the corresponding coordinate covector. -/
@[simp]
theorem standardCliffordRepresentation_secondIsotropicFamily
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) :
    standardCliffordRepresentation B hsymm hnd n hdim
        (CliffordAlgebra.ι (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B)
          (secondIsotropicFamily B hsymm hnd n hdim i)) =
      _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.dualAction n (coordinateCovector n i) := by
  rw [standardCliffordRepresentation_iota]
  simp [secondIsotropicFamily, _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticSpaceAction]

/-- The standard Clifford representation is bijective. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem standardCliffordRepresentation_bijective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Function.Bijective (standardCliffordRepresentation B hsymm hnd n hdim) :=
  (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.cliffordRepresentation_bijective n).comp
    (CliffordAlgebra.equivOfIsometry
      (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim)).bijective

/-- An algebra equivalence from the Clifford algebra of an even-dimensional nondegenerate symmetric form to an endomorphism algebra. -/
noncomputable def cliffordAlgEquivEnd
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B ≃ₐ[ℂ] Module.End ℂ (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) :=
  AlgEquiv.ofBijective (standardCliffordRepresentation B hsymm hnd n hdim)
    (standardCliffordRepresentation_bijective B hsymm hnd n hdim)

/-- The standard carrier is a simple module for the even-dimensional Clifford algebra. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem standardCarrier_isSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    @IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) _ (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) _
      (Module.compHom (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n)
        (standardCliffordRepresentation B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.finrank_spinorSpace]; positivity)
  letI : Module (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) :=
    Module.compHom (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n)
      (standardCliffordRepresentation B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (standardCliffordRepresentation B hsymm hnd n hdim).toRingHom :=
    ⟨(standardCliffordRepresentation_bijective B hsymm hnd n hdim).2⟩
  let e : _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n →ₛₗ[
      (standardCliffordRepresentation B hsymm hnd n hdim).toRingHom] _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n :=
    { AddMonoidHom.id (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- A distinguished module carrier associated with a nondegenerate symmetric complex bilinear form of even dimension. -/
def EvenCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n) :=
  ULift (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n)

/-- The additive commutative group structure on the distinguished even-dimensional Clifford-module carrier. -/
instance evenCliffordModuleAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    AddCommGroup (EvenCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (ULift (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n)))

/-- The complex module structure on the distinguished even-dimensional Clifford-module carrier. -/
instance evenCliffordModuleComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Module ℂ (EvenCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (ULift (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n)))

/-- A complex-linear equivalence from the standard carrier to the distinguished even-dimensional Clifford-module carrier. -/
noncomputable def standardCarrierLinearEquivEvenCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n ≃ₗ[ℂ] EvenCliffordModule B hsymm hnd n hdim :=
  ULift.moduleEquiv.symm

/-- The Clifford algebra action by complex-linear endomorphisms on the distinguished even-dimensional carrier. -/
noncomputable def evenCliffordModuleAction
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B →ₐ[ℂ]
      Module.End ℂ (EvenCliffordModule B hsymm hnd n hdim) :=
  (standardCarrierLinearEquivEvenCliffordModule B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (standardCliffordRepresentation B hsymm hnd n hdim)

/-- The module structure over the Clifford algebra on the distinguished even-dimensional carrier. -/
noncomputable instance evenCliffordModuleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Module (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) (EvenCliffordModule B hsymm hnd n hdim) :=
  Module.compHom _ (evenCliffordModuleAction B hsymm hnd n hdim).toRingHom

/-- The distinguished even-dimensional Clifford module is simple. -/
theorem evenCliffordModule_isSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) (EvenCliffordModule B hsymm hnd n hdim) := by
  letI : Nontrivial (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.finrank_spinorSpace]; positivity)
  letI : Nontrivial (EvenCliffordModule B hsymm hnd n hdim) :=
    (standardCarrierLinearEquivEvenCliffordModule B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (evenCliffordModuleAction B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact
      (standardCarrierLinearEquivEvenCliffordModule B hsymm hnd n hdim).conjAlgEquiv ℂ
        |>.surjective.comp
          (standardCliffordRepresentation_bijective B hsymm hnd n hdim).2
  let e : EvenCliffordModule B hsymm hnd n hdim →ₛₗ[
      (evenCliffordModuleAction B hsymm hnd n hdim).toRingHom]
      EvenCliffordModule B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- Every simple module over the even-dimensional Clifford algebra is linearly equivalent to the distinguished module carrier. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem simpleModule_linearEquiv_evenCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n)
    (W : Type*) [AddCommGroup W] [Module (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) W]
    [IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) W] :
    Nonempty
      (W ≃ₗ[_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B] EvenCliffordModule B hsymm hnd n hdim) := by
  letI : IsSimpleRing (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) :=
    IsSimpleRing.of_ringEquiv
      (CliffordAlgebra.equivOfIsometry
        (standardEvenQuadraticFormIsometryEquiv B hsymm hnd n hdim)).symm.toRingEquiv
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.clifford_isSimpleRing n)
  letI : IsArtinianRing (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) :=
    IsArtinianRing.of_finite ℂ (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B)
  letI : IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B)
      (EvenCliffordModule B hsymm hnd n hdim) :=
    evenCliffordModule_isSimpleModule B hsymm hnd n hdim
  obtain ⟨I, ⟨eW⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) W
  obtain ⟨J, ⟨eS⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) (EvenCliffordModule B hsymm hnd n hdim)
  letI : IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) I :=
    eW.isSimpleModule_iff.mp inferInstance
  letI : IsSimpleModule (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) J :=
    eS.isSimpleModule_iff.mp inferInstance
  let eJI : J ≃ₗ[_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B] I :=
    ((IsSimpleRing.isIsotypic (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B) (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.BilinearCliffordAlgebra B)) I J).some
  exact ⟨eW.trans (eJI.symm.trans eS.symm)⟩

end RepresentationTheory.Algebra.CliffordAlgebra.EvenDimensionalModules
