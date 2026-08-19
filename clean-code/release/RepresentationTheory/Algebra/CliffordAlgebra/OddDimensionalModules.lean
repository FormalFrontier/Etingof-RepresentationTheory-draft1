/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.CliffordAlgebra.EvenDimensionalModules
import RepresentationTheory.Algebra.Matrix.ProductSemisimplicity
import RepresentationTheory.Alignment.Attribute

/-! # Odd-Dimensional Modules -/

namespace RepresentationTheory.Algebra.CliffordAlgebra.OddDimensionalModules

open LinearMap
open RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor
open RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification
open RepresentationTheory.Algebra.CliffordAlgebra.EvenDimensionalModules
open RepresentationTheory.Algebra.Matrix.ProductSemisimplicity

/-- A family of auxiliary types indexed by natural numbers. -/
abbrev AuxiliarySpace (n : ℕ) := quadraticSpace n × ℂ

/-- The complex quadratic form on the auxiliary space. -/
noncomputable def oddQuadraticForm (n : ℕ) :
    QuadraticForm ℂ (AuxiliarySpace n) :=
  (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n).prod
    (QuadraticMap.sq : QuadraticForm ℂ ℂ)

/-- The complex-linear map sending a scalar to an endomorphism of the standard carrier. -/
noncomputable def scalarEndomorphismMap (n : ℕ) :
    ℂ →ₗ[ℂ] Module.End ℂ (spinorSpace n) where
  toFun z := z • gradingInvolution n
  map_add' x y := add_smul x y _
  map_smul' x y := by
    simp only [RingHom.id_apply]
    exact (smul_smul x y (gradingInvolution n)).symm

/-- A scalar-parameterized linear action of the auxiliary space by endomorphisms. -/
noncomputable def signedGeneratorAction (n : ℕ) (σ : ℂ) :
    AuxiliarySpace n →ₗ[ℂ] Module.End ℂ (spinorSpace n) :=
  LinearMap.coprod (quadraticSpaceAction n) (σ • scalarEndomorphismMap n)

/-- When the scalar parameter squares to one, each signed generator action squares to the
quadratic value times the identity. -/
theorem signedGeneratorAction_sq (n : ℕ) (σ : ℂ) (hσ : σ * σ = 1)
    (x : AuxiliarySpace n) :
    signedGeneratorAction n σ x * signedGeneratorAction n σ x =
      oddQuadraticForm n x • (1 : Module.End ℂ (spinorSpace n)) := by
  rcases x with ⟨v, z⟩
  simp only [signedGeneratorAction, oddQuadraticForm, LinearMap.coprod_apply,
    LinearMap.smul_apply, scalarEndomorphismMap, QuadraticMap.prod_apply,
    QuadraticMap.sq_apply]
  change (quadraticSpaceAction n v + σ • (z • gradingInvolution n)) *
      (quadraticSpaceAction n v + σ • (z • gradingInvolution n)) =
    (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n v + z * z) •
      (1 : Module.End ℂ (spinorSpace n))
  rw [smul_smul]
  have hcross :
      quadraticSpaceAction n v * ((σ * z) • gradingInvolution n) +
        ((σ * z) • gradingInvolution n) * quadraticSpaceAction n v = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add,
      gradingInvolution_mul_quadraticSpaceAction]
    simp
  have hlast :
      ((σ * z) • gradingInvolution n) * ((σ * z) • gradingInvolution n) =
        ((σ * z) * (σ * z)) •
          (1 : Module.End ℂ (spinorSpace n)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, gradingInvolution_sq]
  calc
    (quadraticSpaceAction n v + (σ * z) • gradingInvolution n) *
        (quadraticSpaceAction n v + (σ * z) • gradingInvolution n) =
      quadraticSpaceAction n v * quadraticSpaceAction n v +
        (quadraticSpaceAction n v * ((σ * z) • gradingInvolution n) +
          ((σ * z) • gradingInvolution n) * quadraticSpaceAction n v) +
        ((σ * z) • gradingInvolution n) * ((σ * z) • gradingInvolution n) := by
      rw [add_mul, mul_add, mul_add]
      ac_rfl
    _ = _root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n v •
        (1 : Module.End ℂ (spinorSpace n)) +
        ((σ * z) * (σ * z)) • (1 : Module.End ℂ (spinorSpace n)) := by
      rw [quadraticSpaceAction_sq, hcross, hlast, add_zero]
    _ = (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n v +
          z * z) •
        (1 : Module.End ℂ (spinorSpace n)) := by
      rw [← add_smul]
      congr 1
      rw [mul_mul_mul_comm, hσ, one_mul]

/-- The Clifford algebra representation whose distinguished extra generator acts by the positive
auxiliary endomorphism. -/
noncomputable def positiveSpinRepresentation (n : ℕ) :
    CliffordAlgebra (oddQuadraticForm n) →ₐ[ℂ] Module.End ℂ (spinorSpace n) :=
  CliffordAlgebra.lift _
    ⟨signedGeneratorAction n 1, signedGeneratorAction_sq n 1 (by simp)⟩

/-- The Clifford algebra representation whose distinguished extra generator acts by the negative
auxiliary endomorphism. -/
noncomputable def negativeSpinRepresentation (n : ℕ) :
    CliffordAlgebra (oddQuadraticForm n) →ₐ[ℂ] Module.End ℂ (spinorSpace n) :=
  CliffordAlgebra.lift _
    ⟨signedGeneratorAction n (-1), signedGeneratorAction_sq n (-1) (by simp)⟩

/-- The positive representation agrees with the prescribed action on generators in the first
coordinate. -/
@[simp]
theorem positiveSpinRepresentation_firstGenerator
    (n : ℕ) (x : quadraticSpace n) :
    positiveSpinRepresentation n
        (CliffordAlgebra.ι (oddQuadraticForm n) (x, 0)) =
      quadraticSpaceAction n x := by
  rw [positiveSpinRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [signedGeneratorAction]

/-- The negative representation agrees with the prescribed action on generators in the first
coordinate. -/
@[simp]
theorem negativeSpinRepresentation_firstGenerator
    (n : ℕ) (x : quadraticSpace n) :
    negativeSpinRepresentation n
        (CliffordAlgebra.ι (oddQuadraticForm n) (x, 0)) =
      quadraticSpaceAction n x := by
  rw [negativeSpinRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [signedGeneratorAction]

/-- The positive representation sends the generator in the second coordinate to the auxiliary
endomorphism. -/
@[simp]
theorem positiveSpinRepresentation_extraGenerator (n : ℕ) :
    positiveSpinRepresentation n
        (CliffordAlgebra.ι (oddQuadraticForm n) (0, 1)) =
      gradingInvolution n := by
  rw [positiveSpinRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [signedGeneratorAction, scalarEndomorphismMap]

/-- The negative representation sends the generator in the second coordinate to the negative
auxiliary endomorphism. -/
@[simp]
theorem negativeSpinRepresentation_extraGenerator (n : ℕ) :
    negativeSpinRepresentation n
        (CliffordAlgebra.ι (oddQuadraticForm n) (0, 1)) =
      -gradingInvolution n := by
  rw [negativeSpinRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [signedGeneratorAction, scalarEndomorphismMap]

/-- The algebra homomorphism between the Clifford algebras induced by adjoining a zero second
coordinate. -/
noncomputable def cliffordAlgHomToOddForm (n : ℕ) :
    CliffordAlgebra
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) →ₐ[ℂ]
      CliffordAlgebra (oddQuadraticForm n) :=
  CliffordAlgebra.map
    (QuadraticMap.Isometry.inl
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)
      (QuadraticMap.sq : QuadraticForm ℂ ℂ))

/-- The Clifford algebra homomorphism sends a generator to the generator with zero second
coordinate. -/
@[simp]
theorem cliffordAlgHomToOddForm_iota (n : ℕ) (x : quadraticSpace n) :
    cliffordAlgHomToOddForm n
        (CliffordAlgebra.ι
          (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) x) =
      CliffordAlgebra.ι (oddQuadraticForm n) (x, 0) := by
  rw [cliffordAlgHomToOddForm, CliffordAlgebra.map_apply_ι]
  rfl

/-- Composing the positive representation with the auxiliary Clifford algebra homomorphism gives
the prescribed representation. -/
theorem positiveSpinRepresentation_comp_cliffordAlgHomToOddForm (n : ℕ) :
    (positiveSpinRepresentation n).comp (cliffordAlgHomToOddForm n) =
      cliffordRepresentation n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change ((positiveSpinRepresentation n).comp (cliffordAlgHomToOddForm n))
      (CliffordAlgebra.ι
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) x) =
    cliffordRepresentation n
      (CliffordAlgebra.ι
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) x)
  rw [AlgHom.comp_apply, cliffordAlgHomToOddForm_iota,
    positiveSpinRepresentation_firstGenerator,
    cliffordRepresentation, CliffordAlgebra.lift_ι_apply]

/-- Composing the negative representation with the auxiliary Clifford algebra homomorphism gives
the prescribed representation. -/
theorem negativeSpinRepresentation_comp_cliffordAlgHomToOddForm (n : ℕ) :
    (negativeSpinRepresentation n).comp (cliffordAlgHomToOddForm n) =
      cliffordRepresentation n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change ((negativeSpinRepresentation n).comp (cliffordAlgHomToOddForm n))
      (CliffordAlgebra.ι
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) x) =
    cliffordRepresentation n
      (CliffordAlgebra.ι
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n) x)
  rw [AlgHom.comp_apply, cliffordAlgHomToOddForm_iota,
    negativeSpinRepresentation_firstGenerator,
    cliffordRepresentation, CliffordAlgebra.lift_ι_apply]

/-- The positive Clifford algebra representation is surjective. -/
theorem positiveSpinRepresentation_surjective (n : ℕ) :
    Function.Surjective (positiveSpinRepresentation n) := by
  intro f
  obtain ⟨c, rfl⟩ := (cliffordRepresentation_bijective n).2 f
  exact ⟨cliffordAlgHomToOddForm n c,
    AlgHom.congr_fun (positiveSpinRepresentation_comp_cliffordAlgHomToOddForm n) c⟩

/-- The negative Clifford algebra representation is surjective. -/
theorem negativeSpinRepresentation_surjective (n : ℕ) :
    Function.Surjective (negativeSpinRepresentation n) := by
  intro f
  obtain ⟨c, rfl⟩ := (cliffordRepresentation_bijective n).2 f
  exact ⟨cliffordAlgHomToOddForm n c,
    AlgHom.congr_fun (negativeSpinRepresentation_comp_cliffordAlgHomToOddForm n) c⟩

/-- The bilinear form associated to the auxiliary quadratic form separates points in its left
argument. -/
theorem oddQuadraticForm_associated_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (R := ℂ) (oddQuadraticForm n)).SeparatingLeft := by
  intro x hx
  rcases x with ⟨v, z⟩
  apply Prod.ext
  · apply standardEvenQuadraticForm_associated_separatingLeft n
    intro y
    have h := hx (y, 0)
    simpa [oddQuadraticForm, QuadraticMap.associated_apply] using h
  · have h := hx (0, 1)
    simpa [oddQuadraticForm, QuadraticMap.associated_apply] using h

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- An isometric equivalence from the quadratic form associated to the given bilinear form to the
auxiliary odd-dimensional quadratic form. -/
noncomputable def oddQuadraticFormIsometryEquiv
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
      B).IsometryEquiv
      (oddQuadraticForm n) := by
  let e₀ : V ≃ₗ[ℂ] AuxiliarySpace n :=
    LinearEquiv.ofFinrankEq V (AuxiliarySpace n) (by
      rw [hdim]
      simp [AuxiliarySpace, quadraticSpace, Module.finrank_prod]
      omega)
  let Q₀ : QuadraticForm ℂ V :=
    (oddQuadraticForm n).comp e₀.toLinearMap
  have hB :
      (QuadraticMap.associated (R := ℂ)
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
          B)).SeparatingLeft := by
    rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    exact hnd.1
  have hQ₀ : (QuadraticMap.associated (R := ℂ) Q₀).SeparatingLeft := by
    intro x hx
    apply e₀.injective
    rw [map_zero]
    apply oddQuadraticForm_associated_separatingLeft n
    intro y
    obtain ⟨z, rfl⟩ := e₀.surjective y
    have := hx z
    simpa [Q₀, QuadraticMap.associated_comp] using this
  let e₁ :
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
        B).IsometryEquiv
        Q₀ :=
    Classical.choice
      (QuadraticForm.equivalent_of_isAlgClosed
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B)
        Q₀ hB hQ₀)
  exact e₁.trans
    (QuadraticMap.isometryEquivOfCompLinearEquiv
      (oddQuadraticForm n) e₀).symm

/-- The positive spin representation of the Clifford algebra of a nondegenerate symmetric bilinear
form of odd dimension. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def positiveSpinRepresentationOfBilin
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    BilinearCliffordAlgebra B →ₐ[ℂ] Module.End ℂ (spinorSpace n) :=
  (positiveSpinRepresentation n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).toAlgHom

/-- The negative spin representation of the Clifford algebra of a nondegenerate symmetric bilinear
form of odd dimension. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def negativeSpinRepresentationOfBilin
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    BilinearCliffordAlgebra B →ₐ[ℂ] Module.End ℂ (spinorSpace n) :=
  (negativeSpinRepresentation n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).toAlgHom

/-- The positive representation of a Clifford generator is the signed generator action after the
quadratic-form isometry. -/
@[simp]
theorem positiveSpinRepresentationOfBilin_iota
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) (x : V) :
    positiveSpinRepresentationOfBilin B hsymm hnd n hdim
        (CliffordAlgebra.ι
          (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
            B)
          x) =
      signedGeneratorAction n 1
        (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim x) := by
  simp [positiveSpinRepresentationOfBilin, positiveSpinRepresentation]

/-- An auxiliary fact about the negative representation and the odd-dimensional quadratic-form
equivalence. -/
@[simp]
theorem auxiliary_fact1
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) (x : V) :
    negativeSpinRepresentationOfBilin B hsymm hnd n hdim
        (CliffordAlgebra.ι
          (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
            B)
          x) =
      signedGeneratorAction n (-1)
        (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim x) := by
  simp [negativeSpinRepresentationOfBilin, negativeSpinRepresentation]

/-- A distinguished vector for a nondegenerate symmetric complex bilinear form of odd dimension. -/
noncomputable def distinguishedVector
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) : V :=
  (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim).symm (0, 1)

/-- The positive representation sends the Clifford generator of the distinguished vector to the
auxiliary endomorphism. -/
@[simp]
theorem positiveSpinRepresentationOfBilin_distinguishedVector
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    positiveSpinRepresentationOfBilin B hsymm hnd n hdim
        (CliffordAlgebra.ι
          (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
            B)
          (distinguishedVector B hsymm hnd n hdim)) =
      gradingInvolution n := by
  rw [positiveSpinRepresentationOfBilin_iota]
  simp [distinguishedVector, signedGeneratorAction, scalarEndomorphismMap]

/-- The negative representation sends the Clifford generator of the distinguished vector to the
negative auxiliary endomorphism. -/
@[simp]
theorem negativeSpinRepresentationOfBilin_distinguishedVector
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    negativeSpinRepresentationOfBilin B hsymm hnd n hdim
        (CliffordAlgebra.ι
          (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
            B)
          (distinguishedVector B hsymm hnd n hdim)) =
      -gradingInvolution n := by
  rw [auxiliary_fact1]
  simp [distinguishedVector, signedGeneratorAction, scalarEndomorphismMap]

/-- The positive spin representation of the Clifford algebra of the bilinear form is surjective. -/
theorem positiveSpinRepresentationOfBilin_surjective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Function.Surjective (positiveSpinRepresentationOfBilin B hsymm hnd n hdim) :=
  (positiveSpinRepresentation_surjective n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).surjective

/-- The negative spin representation of the Clifford algebra of the bilinear form is surjective. -/
theorem negativeSpinRepresentationOfBilin_surjective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Function.Surjective (negativeSpinRepresentationOfBilin B hsymm hnd n hdim) :=
  (negativeSpinRepresentation_surjective n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).surjective

/-- The standard carrier is a simple module for the Clifford algebra through the positive
representation. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem isSimpleModule_positiveSpinRepresentationOfBilin
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    @IsSimpleModule (BilinearCliffordAlgebra B) _ (spinorSpace n) _
      (Module.compHom (spinorSpace n)
        (positiveSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  letI : Module (BilinearCliffordAlgebra B) (spinorSpace n) :=
    Module.compHom (spinorSpace n)
      (positiveSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (positiveSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom :=
    ⟨positiveSpinRepresentationOfBilin_surjective B hsymm hnd n hdim⟩
  let e : spinorSpace n →ₛₗ[
      (positiveSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom] spinorSpace n :=
    { AddMonoidHom.id (spinorSpace n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The standard carrier is a simple module for the Clifford algebra through the negative
representation. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem isSimpleModule_negativeSpinRepresentationOfBilin
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    @IsSimpleModule (BilinearCliffordAlgebra B) _ (spinorSpace n) _
      (Module.compHom (spinorSpace n)
        (negativeSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  letI : Module (BilinearCliffordAlgebra B) (spinorSpace n) :=
    Module.compHom (spinorSpace n)
      (negativeSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (negativeSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom :=
    ⟨negativeSpinRepresentationOfBilin_surjective B hsymm hnd n hdim⟩
  let e : spinorSpace n →ₛₗ[
      (negativeSpinRepresentationOfBilin B hsymm hnd n hdim).toRingHom] spinorSpace n :=
    { AddMonoidHom.id (spinorSpace n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The second module carrier associated with a nondegenerate symmetric complex bilinear form of
odd dimension. -/
def SecondOddCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n + 1) :=
  spinorSpace n

/-- The first module carrier associated with a nondegenerate symmetric complex bilinear form of odd
dimension. -/
def FirstOddCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n + 1) :=
  spinorSpace n

/-- The additive commutative group structure on the second odd-dimensional module carrier. -/
instance secondOddCliffordModuleAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    AddCommGroup (SecondOddCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (spinorSpace n))

/-- The complex module structure on the second odd-dimensional module carrier. -/
instance secondOddCliffordModuleComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module ℂ (SecondOddCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (spinorSpace n))

/-- The additive commutative group structure on the first odd-dimensional module carrier. -/
instance firstOddCliffordModuleAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    AddCommGroup (FirstOddCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (spinorSpace n))

/-- The complex module structure on the first odd-dimensional module carrier. -/
instance firstOddCliffordModuleComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module ℂ (FirstOddCliffordModule B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (spinorSpace n))

/-- A complex-linear equivalence from the standard carrier to the second odd-dimensional module
carrier. -/
noncomputable def secondOddCliffordModuleLinearEquiv
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    spinorSpace n ≃ₗ[ℂ] SecondOddCliffordModule B hsymm hnd n hdim :=
  LinearEquiv.refl ℂ (spinorSpace n)

/-- A complex-linear equivalence from the standard carrier to the first odd-dimensional module
carrier. -/
noncomputable def firstOddCliffordModuleLinearEquiv
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    spinorSpace n ≃ₗ[ℂ] FirstOddCliffordModule B hsymm hnd n hdim :=
  LinearEquiv.refl ℂ (spinorSpace n)

/-- The Clifford algebra action on the second odd-dimensional module carrier. -/
noncomputable def secondOddCliffordModuleAction
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    BilinearCliffordAlgebra B →ₐ[ℂ]
      Module.End ℂ (SecondOddCliffordModule B hsymm hnd n hdim) :=
  (secondOddCliffordModuleLinearEquiv B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (positiveSpinRepresentationOfBilin B hsymm hnd n hdim)

/-- The Clifford algebra action on the first odd-dimensional module carrier. -/
noncomputable def firstOddCliffordModuleAction
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    BilinearCliffordAlgebra B →ₐ[ℂ]
      Module.End ℂ (FirstOddCliffordModule B hsymm hnd n hdim) :=
  (firstOddCliffordModuleLinearEquiv B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (negativeSpinRepresentationOfBilin B hsymm hnd n hdim)

/-- The module structure over the Clifford algebra on the second odd-dimensional carrier. -/
noncomputable instance secondOddCliffordModuleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module (BilinearCliffordAlgebra B) (SecondOddCliffordModule B hsymm hnd n hdim) :=
  Module.compHom _ (secondOddCliffordModuleAction B hsymm hnd n hdim).toRingHom

/-- The module structure over the Clifford algebra on the first odd-dimensional carrier. -/
noncomputable instance firstOddCliffordModuleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module (BilinearCliffordAlgebra B) (FirstOddCliffordModule B hsymm hnd n hdim) :=
  Module.compHom _ (firstOddCliffordModuleAction B hsymm hnd n hdim).toRingHom

/-- The second odd-dimensional Clifford module is simple. -/
theorem secondOddCliffordModuleIsSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsSimpleModule (BilinearCliffordAlgebra B)
      (SecondOddCliffordModule B hsymm hnd n hdim) := by
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  letI : Nontrivial (SecondOddCliffordModule B hsymm hnd n hdim) :=
    (secondOddCliffordModuleLinearEquiv B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (secondOddCliffordModuleAction B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact (secondOddCliffordModuleLinearEquiv B hsymm hnd n hdim).conjAlgEquiv ℂ
      |>.surjective.comp
      (positiveSpinRepresentationOfBilin_surjective B hsymm hnd n hdim)
  let e : SecondOddCliffordModule B hsymm hnd n hdim →ₛₗ[
      (secondOddCliffordModuleAction B hsymm hnd n hdim).toRingHom]
      SecondOddCliffordModule B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The first odd-dimensional Clifford module is simple. -/
theorem firstOddCliffordModuleIsSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsSimpleModule (BilinearCliffordAlgebra B)
      (FirstOddCliffordModule B hsymm hnd n hdim) := by
  letI : Nontrivial (spinorSpace n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinorSpace]; positivity)
  letI : Nontrivial (FirstOddCliffordModule B hsymm hnd n hdim) :=
    (firstOddCliffordModuleLinearEquiv B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (firstOddCliffordModuleAction B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact (firstOddCliffordModuleLinearEquiv B hsymm hnd n hdim).conjAlgEquiv ℂ
      |>.surjective.comp
      (negativeSpinRepresentationOfBilin_surjective B hsymm hnd n hdim)
  let e : FirstOddCliffordModule B hsymm hnd n hdim →ₛₗ[
      (firstOddCliffordModuleAction B hsymm hnd n hdim).toRingHom]
      FirstOddCliffordModule B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- A map from the auxiliary Clifford algebra to that of a nondegenerate symmetric form of odd
dimension. -/
noncomputable def cliffordMapFromAuxiliaryForm
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)) :
    BilinearCliffordAlgebra B :=
  (CliffordAlgebra.equivOfIsometry
    (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).symm
      (cliffordAlgHomToOddForm n c)

/-- The positive representation agrees with the prescribed representation on the image of the
auxiliary Clifford algebra. -/
@[simp]
theorem positiveSpinRepresentationOfBilin_cliffordMap
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)) :
    positiveSpinRepresentationOfBilin B hsymm hnd n hdim
        (cliffordMapFromAuxiliaryForm B hsymm hnd n hdim c) =
      cliffordRepresentation n c := by
  change positiveSpinRepresentation n
      ((CliffordAlgebra.equivOfIsometry
        (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim))
          ((CliffordAlgebra.equivOfIsometry
            (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).symm
              (cliffordAlgHomToOddForm n c))) =
    cliffordRepresentation n c
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun
    (positiveSpinRepresentation_comp_cliffordAlgHomToOddForm n) c

/-- The negative representation agrees with the prescribed representation on the image of the
auxiliary Clifford algebra. -/
@[simp]
theorem negativeSpinRepresentationOfBilin_cliffordMap
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexSpinor.quadraticForm n)) :
    negativeSpinRepresentationOfBilin B hsymm hnd n hdim
        (cliffordMapFromAuxiliaryForm B hsymm hnd n hdim c) =
      cliffordRepresentation n c := by
  change negativeSpinRepresentation n
      ((CliffordAlgebra.equivOfIsometry
        (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim))
          ((CliffordAlgebra.equivOfIsometry
            (oddQuadraticFormIsometryEquiv B hsymm hnd n hdim)).symm
              (cliffordAlgHomToOddForm n c))) =
    cliffordRepresentation n c
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun
    (negativeSpinRepresentation_comp_cliffordAlgHomToOddForm n) c

/-- There is no Clifford-module linear equivalence from the second odd-dimensional carrier to the
first. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem isEmpty_linearEquiv_secondOddCliffordModule_firstOddCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsEmpty
      (SecondOddCliffordModule B hsymm hnd n hdim ≃ₗ[BilinearCliffordAlgebra B]
        FirstOddCliffordModule B hsymm hnd n hdim) := by
  constructor
  intro e
  obtain ⟨c, hc⟩ :=
    (cliffordRepresentation_bijective n).2 (gradingInvolution n)
  let a := cliffordMapFromAuxiliaryForm B hsymm hnd n hdim c
  let z :=
    CliffordAlgebra.ι
      (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm B)
      (distinguishedVector B hsymm hnd n hdim)
  have hcomm (x : SecondOddCliffordModule B hsymm hnd n hdim) :
      e (gradingInvolution n x) = gradingInvolution n (e x) := by
    have h := e.map_smul a x
    change e ((positiveSpinRepresentationOfBilin B hsymm hnd n hdim a) x) =
      (negativeSpinRepresentationOfBilin B hsymm hnd n hdim a) (e x) at h
    rw [positiveSpinRepresentationOfBilin_cliffordMap,
      negativeSpinRepresentationOfBilin_cliffordMap, hc] at h
    exact h
  have hanti (x : SecondOddCliffordModule B hsymm hnd n hdim) :
      e (gradingInvolution n x) = -gradingInvolution n (e x) := by
    have h := e.map_smul z x
    change e ((positiveSpinRepresentationOfBilin B hsymm hnd n hdim z) x) =
      (negativeSpinRepresentationOfBilin B hsymm hnd n hdim z) (e x) at h
    rw [positiveSpinRepresentationOfBilin_distinguishedVector,
      negativeSpinRepresentationOfBilin_distinguishedVector] at h
    exact h
  have hzero (x : SecondOddCliffordModule B hsymm hnd n hdim) :
      gradingInvolution n (e x) = 0 := by
    have h := (hcomm x).symm.trans (hanti x)
    have htwo : (2 : ℂ) • gradingInvolution n (e x) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  let y : FirstOddCliffordModule B hsymm hnd n hdim :=
    firstOddCliffordModuleLinearEquiv B hsymm hnd n hdim (1 : spinorSpace n)
  have hy : y ≠ 0 := by
    change (1 : spinorSpace n) ≠ 0
    exact one_ne_zero
  have hp : gradingInvolution n y = y := by
    change CliffordAlgebra.involute (1 : spinorSpace n) = 1
    exact map_one _
  have hz := hzero (e.symm y)
  rw [e.apply_symm_apply, hp] at hz
  exact hy hz

/-- Every finite-dimensional simple module for the odd-dimensional Clifford algebra is linearly
equivalent to the first or second distinguished module. -/
theorem finiteDimensional_simpleModule_equiv_first_or_second
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [Module (BilinearCliffordAlgebra B) W]
    [IsScalarTower ℂ (BilinearCliffordAlgebra B) W] [FiniteDimensional ℂ W]
    [IsSimpleModule (BilinearCliffordAlgebra B) W] :
    Nonempty
        (W ≃ₗ[BilinearCliffordAlgebra B] SecondOddCliffordModule B hsymm hnd n hdim) ∨
      Nonempty
        (W ≃ₗ[BilinearCliffordAlgebra B] FirstOddCliffordModule B hsymm hnd n hdim) := by
  classical
  obtain ⟨d, hd, ⟨eA⟩⟩ :=
    exists_algEquiv_pi_matrix_of_finrank_odd B hsymm hnd n hdim
  let P := MatrixProduct ℂ d
  letI : ∀ i, NeZero (d i) := fun i => ⟨Nat.ne_of_gt (hd i)⟩
  letI : Module P W :=
    Module.compHom W eA.symm.toRingHom
  letI : IsScalarTower ℂ P W := by
    constructor
    intro c a w
    change eA.symm (c • a) • w = c • (eA.symm a • w)
    rw [map_smul, smul_assoc]
  letI : RingHomSurjective eA.symm.toRingHom :=
    ⟨eA.symm.surjective⟩
  let lW : W →ₛₗ[eA.symm.toRingHom] W :=
    { AddMonoidHom.id W with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P W :=
    (lW.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      inferInstance
  let Splus := SecondOddCliffordModule B hsymm hnd n hdim
  let Sminus := FirstOddCliffordModule B hsymm hnd n hdim
  letI : Module.Finite ℂ (spinorSpace n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  letI : IsScalarTower ℂ (BilinearCliffordAlgebra B) Splus := by
    constructor
    intro c a s
    change
      (secondOddCliffordModuleAction B hsymm hnd n hdim (c • a)) s =
        c • (secondOddCliffordModuleAction B hsymm hnd n hdim a) s
    rw [map_smul]
    rfl
  letI : FiniteDimensional ℂ Splus :=
    Module.Finite.equiv
      (secondOddCliffordModuleLinearEquiv B hsymm hnd n hdim)
  letI : Module P Splus :=
    Module.compHom Splus eA.symm.toRingHom
  letI : IsScalarTower ℂ P Splus := by
    constructor
    intro c a s
    change eA.symm (c • a) • s = c • (eA.symm a • s)
    rw [map_smul, smul_assoc]
  let lPlus : Splus →ₛₗ[eA.symm.toRingHom] Splus :=
    { AddMonoidHom.id Splus with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P Splus :=
    (lPlus.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      (secondOddCliffordModuleIsSimpleModule B hsymm hnd n hdim)
  letI : IsScalarTower ℂ (BilinearCliffordAlgebra B) Sminus := by
    constructor
    intro c a s
    change
      (firstOddCliffordModuleAction B hsymm hnd n hdim (c • a)) s =
        c • (firstOddCliffordModuleAction B hsymm hnd n hdim a) s
    rw [map_smul]
    rfl
  letI : FiniteDimensional ℂ Sminus :=
    Module.Finite.equiv
      (firstOddCliffordModuleLinearEquiv B hsymm hnd n hdim)
  letI : Module P Sminus :=
    Module.compHom Sminus eA.symm.toRingHom
  letI : IsScalarTower ℂ P Sminus := by
    constructor
    intro c a s
    change eA.symm (c • a) • s = c • (eA.symm a • s)
    rw [map_smul, smul_assoc]
  let lMinus : Sminus →ₛₗ[eA.symm.toRingHom] Sminus :=
    { AddMonoidHom.id Sminus with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P Sminus :=
    (lMinus.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      (firstOddCliffordModuleIsSimpleModule B hsymm hnd n hdim)
  obtain ⟨iW, ⟨eW⟩⟩ :=
    simpleModule_linearEquiv_standardModule (k := ℂ) (d := d) W
  obtain ⟨iP, ⟨eP⟩⟩ :=
    simpleModule_linearEquiv_standardModule (k := ℂ) (d := d) Splus
  obtain ⟨iM, ⟨eM⟩⟩ :=
    simpleModule_linearEquiv_standardModule (k := ℂ) (d := d) Sminus
  have hPM : iP ≠ iM := by
    intro h
    subst h
    let f := eP.trans eM.symm
    let fA : Splus ≃ₗ[BilinearCliffordAlgebra B] Sminus :=
      { f.toAddEquiv with
        map_smul' := fun a s => by
          have hmap := f.map_smul (eA a) s
          change f (eA.symm (eA a) • s) =
            eA.symm (eA a) • f s at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }
    exact
      (isEmpty_linearEquiv_secondOddCliffordModule_firstOddCliffordModule
        B hsymm hnd n hdim).false fA
  have hW : iW = iP ∨ iW = iM := by
    fin_cases iW <;> fin_cases iP <;> fin_cases iM <;> simp_all
  rcases hW with hW | hW
  · subst hW
    left
    let f := eW.trans eP.symm
    exact ⟨
      { f.toAddEquiv with
        map_smul' := fun a w => by
          have hmap := f.map_smul (eA a) w
          change f (eA.symm (eA a) • w) =
            eA.symm (eA a) • f w at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }⟩
  · subst hW
    right
    let f := eW.trans eM.symm
    exact ⟨
      { f.toAddEquiv with
        map_smul' := fun a w => by
          have hmap := f.map_smul (eA a) w
          change f (eA.symm (eA a) • w) =
            eA.symm (eA a) • f w at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }⟩

/-- Every simple module for the odd-dimensional Clifford algebra is linearly equivalent to the
first or second distinguished module. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem simpleModule_equiv_first_or_second
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (W : Type*) [AddCommGroup W] [Module (BilinearCliffordAlgebra B) W]
    [IsSimpleModule (BilinearCliffordAlgebra B) W] :
    Nonempty
        (W ≃ₗ[BilinearCliffordAlgebra B] SecondOddCliffordModule B hsymm hnd n hdim) ∨
      Nonempty
        (W ≃ₗ[BilinearCliffordAlgebra B] FirstOddCliffordModule B hsymm hnd n hdim) := by
  letI : Module ℂ W :=
    Module.compHom W (algebraMap ℂ (BilinearCliffordAlgebra B))
  letI : IsScalarTower ℂ (BilinearCliffordAlgebra B) W := by
    constructor
    intro c a w
    change (algebraMap ℂ (BilinearCliffordAlgebra B) c * a) • w =
      (algebraMap ℂ (BilinearCliffordAlgebra B) c) • (a • w)
    rw [mul_smul]
  letI : Module.Finite (BilinearCliffordAlgebra B) W := by
    haveI := IsSimpleModule.nontrivial (BilinearCliffordAlgebra B) W
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hmem : w ∈ Submodule.span (BilinearCliffordAlgebra B) {w} :=
      Submodule.mem_span_singleton_self w
    have hspan : Submodule.span (BilinearCliffordAlgebra B) {w} = ⊤ := by
      rcases eq_bot_or_eq_top (Submodule.span (BilinearCliffordAlgebra B) {w}) with h | h
      · rw [h, Submodule.mem_bot] at hmem
        exact absurd hmem hw
      · exact h
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_singleton w)
  letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  letI : Module.Finite ℂ (ExteriorAlgebra ℂ V) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Module.finBasis ℂ V))
  letI : Module.Finite ℂ (BilinearCliffordAlgebra B) :=
    Module.Finite.equiv
      (CliffordAlgebra.equivExterior
        (_root_.RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification.quadraticForm
          B)).symm
  letI : FiniteDimensional ℂ W :=
    Module.Finite.trans (BilinearCliffordAlgebra B) W
  exact
    finiteDimensional_simpleModule_equiv_first_or_second
      B hsymm hnd n hdim W

end RepresentationTheory.Algebra.CliffordAlgebra.OddDimensionalModules
