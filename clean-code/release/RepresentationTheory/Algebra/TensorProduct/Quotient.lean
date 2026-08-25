/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.LinearAlgebra.TensorProduct.Basic
import RepresentationTheory.Alignment.Attribute

/-! # A quotient construction for tensor products -/

namespace RepresentationTheory.Algebra.TensorProduct.Quotient

open scoped TensorProduct

variable (k V W : Type*) [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A set of elements of the free abelian group on pairs of module elements. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
def tensorProductRelations : Set (FreeAbelianGroup (V × W)) :=
  {x | (∃ v₁ v₂ w, x = FreeAbelianGroup.of (v₁ + v₂, w) - FreeAbelianGroup.of (v₁, w)
          - FreeAbelianGroup.of (v₂, w)) ∨
       (∃ v w₁ w₂, x = FreeAbelianGroup.of (v, w₁ + w₂) - FreeAbelianGroup.of (v, w₁)
          - FreeAbelianGroup.of (v, w₂)) ∨
       (∃ (a : k) (v : V) (w : W), x = FreeAbelianGroup.of (a • v, w)
          - FreeAbelianGroup.of (v, a • w))}

/-- An additive subgroup of the free abelian group on pairs of module elements. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
def tensorProductRelationSubgroup : AddSubgroup (FreeAbelianGroup (V × W)) :=
  AddSubgroup.closure (tensorProductRelations k V W)

/-- A type associated with a pair of modules. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
abbrev tensorProductQuotient :=
  FreeAbelianGroup (V × W) ⧸ tensorProductRelationSubgroup k V W

/-- Additive homomorphism from the defining quotient to the tensor product. -/
noncomputable def quotientToTensorProduct :
    (tensorProductQuotient k V W) →+ (_root_.TensorProduct k V W) :=
  QuotientAddGroup.lift (tensorProductRelationSubgroup k V W)
    (FreeAbelianGroup.lift (fun p : V × W => p.1 ⊗ₜ[k] p.2))
    (by
      rw [tensorProductRelationSubgroup, AddSubgroup.closure_le]
      rintro y (⟨v₁, v₂, w, rfl⟩ | ⟨v, w₁, w₂, rfl⟩ | ⟨a, v, w, rfl⟩)
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
        rw [TensorProduct.add_tmul]; abel
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
        rw [TensorProduct.tmul_add]; abel
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
        rw [TensorProduct.smul_tmul]; abel)

/-- The quotient-to-tensor-product homomorphism on a free abelian group class is the lifted pure-tensor map. -/
@[simp]
theorem quotientToTensorProduct_mk (x : FreeAbelianGroup (V × W)) :
    quotientToTensorProduct k V W (x : tensorProductQuotient k V W) =
      FreeAbelianGroup.lift (fun p : V × W => p.1 ⊗ₜ[k] p.2) x :=
  rfl

/-- A curried additive map sending a pair of module elements to an element of the associated type. -/
noncomputable def pairToQuotient : V →+ W →+ tensorProductQuotient k V W :=
  AddMonoidHom.mk'
    (fun v => AddMonoidHom.mk'
      (fun w => QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
        (FreeAbelianGroup.of (v, w)))
      (fun w₁ w₂ => by
        have h : QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
            (FreeAbelianGroup.of (v, w₁ + w₂) - FreeAbelianGroup.of (v, w₁)
              - FreeAbelianGroup.of (v, w₂)) = 0 := by
          rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
          exact AddSubgroup.subset_closure (Or.inr (Or.inl ⟨v, w₁, w₂, rfl⟩))
        rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
        simpa using h))
    (fun v₁ v₂ => by
      ext w
      have h : QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
          (FreeAbelianGroup.of (v₁ + v₂, w) - FreeAbelianGroup.of (v₁, w)
            - FreeAbelianGroup.of (v₂, w)) = 0 := by
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        exact AddSubgroup.subset_closure (Or.inl ⟨v₁, v₂, w, rfl⟩)
      rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
      simpa using h)

/-- The pair-to-quotient map evaluates to the class of the corresponding free generator. -/
@[simp]
theorem pairToQuotient_apply (v : V) (w : W) :
    pairToQuotient k V W v w =
      QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W) (FreeAbelianGroup.of (v, w)) :=
  rfl

/-- Additive homomorphism from the tensor product to its defining quotient. -/
noncomputable def tensorProductToQuotient :
    (_root_.TensorProduct k V W) →+ (tensorProductQuotient k V W) :=
  TensorProduct.liftAddHom (pairToQuotient k V W)
    (fun a v w => by
      have h : QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
          (FreeAbelianGroup.of (a • v, w) - FreeAbelianGroup.of (v, a • w)) = 0 := by
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        exact AddSubgroup.subset_closure (Or.inr (Or.inr ⟨a, v, w, rfl⟩))
      rw [map_sub, sub_eq_zero] at h
      simpa using h)

/-- The tensor-product-to-quotient homomorphism sends a pure tensor to its generating class. -/
@[simp]
theorem tensorProductToQuotient_tmul (v : V) (w : W) :
    tensorProductToQuotient k V W (v ⊗ₜ[k] w) =
      QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
        (FreeAbelianGroup.of (v, w)) := by
  rw [tensorProductToQuotient, TensorProduct.liftAddHom_tmul, pairToQuotient_apply]

/-- The quotient and tensor-product maps compose to the identity on the tensor product. -/
theorem quotientToTensorProduct_comp_tensorProductToQuotient
    (t : _root_.TensorProduct k V W) :
    quotientToTensorProduct k V W (tensorProductToQuotient k V W t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The two quotient and tensor-product maps compose to the identity on the quotient. -/
theorem tensorProductToQuotient_comp_quotientToTensorProduct
    (q : tensorProductQuotient k V W) :
    tensorProductToQuotient k V W (quotientToTensorProduct k V W q) = q := by
  induction q using QuotientAddGroup.induction_on with
  | H z =>
    rw [← QuotientAddGroup.mk'_apply]
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp
    | of p => obtain ⟨v, w⟩ := p; simp
    | neg p ih => simp only [map_neg]; rw [ih]
    | add x y hx hy => simp only [map_add]; rw [hx, hy]

/-- Additive equivalence from the defining quotient to the tensor product. -/
noncomputable def quotientToTensorProductAddEquiv :
    (tensorProductQuotient k V W) ≃+ (_root_.TensorProduct k V W) where
  toFun := quotientToTensorProduct k V W
  invFun := tensorProductToQuotient k V W
  left_inv := tensorProductToQuotient_comp_quotientToTensorProduct k V W
  right_inv := quotientToTensorProduct_comp_tensorProductToQuotient k V W
  map_add' := (quotientToTensorProduct k V W).map_add

/-- Scalar action on the quotient used to construct the tensor product. -/
noncomputable instance quotientSMul : SMul k (tensorProductQuotient k V W) where
  smul a q := (quotientToTensorProductAddEquiv k V W).symm
    (a • quotientToTensorProductAddEquiv k V W q)

/-- The quotient-to-tensor-product additive equivalence commutes with scalar multiplication. -/
@[simp]
theorem quotientToTensorProduct_smul (a : k) (q : tensorProductQuotient k V W) :
    quotientToTensorProductAddEquiv k V W (a • q) =
      a • quotientToTensorProductAddEquiv k V W q :=
  (quotientToTensorProductAddEquiv k V W).apply_symm_apply _

/-- Module structure on the quotient used to construct the tensor product. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
noncomputable instance quotientModule : Module k (tensorProductQuotient k V W) :=
  Function.Injective.module k (quotientToTensorProductAddEquiv k V W).toAddMonoidHom
    (quotientToTensorProductAddEquiv k V W).injective
    (quotientToTensorProduct_smul k V W)

/-- Linear equivalence from the defining quotient to the tensor product. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
noncomputable def quotientToTensorProductLinearEquiv :
    (tensorProductQuotient k V W) ≃ₗ[k] (_root_.TensorProduct k V W) where
  toAddEquiv := quotientToTensorProductAddEquiv k V W
  map_smul' := quotientToTensorProduct_smul k V W

/-- The quotient-to-tensor-product linear equivalence sends a generating pair to its pure tensor. -/
@[source_ref "Chapter2/Exercise2.11.2" (role := supporting)]
theorem quotientToTensorProductLinearEquiv_mk_pair (v : V) (w : W) :
    quotientToTensorProductLinearEquiv k V W
        (QuotientAddGroup.mk' (tensorProductRelationSubgroup k V W)
          (FreeAbelianGroup.of (v, w))) =
      v ⊗ₜ[k] w := by
  rfl

/-- An additive equivalence between the defining quotient and tensor product exists. -/
theorem quotientToTensorProductAddEquiv_nonempty :
    Nonempty ((tensorProductQuotient k V W) ≃+ (_root_.TensorProduct k V W)) :=
  ⟨(quotientToTensorProductLinearEquiv k V W).toAddEquiv⟩

end RepresentationTheory.Algebra.TensorProduct.Quotient

attribute [nolint defsWithUnderscore]
  RepresentationTheory.Algebra.TensorProduct.Quotient.tensorProductRelations
  RepresentationTheory.Algebra.TensorProduct.Quotient.tensorProductRelationSubgroup
  RepresentationTheory.Algebra.TensorProduct.Quotient.tensorProductQuotient
  RepresentationTheory.Algebra.TensorProduct.Quotient.quotientToTensorProduct
  RepresentationTheory.Algebra.TensorProduct.Quotient.pairToQuotient
  RepresentationTheory.Algebra.TensorProduct.Quotient.tensorProductToQuotient
  RepresentationTheory.Algebra.TensorProduct.Quotient.quotientToTensorProductAddEquiv
  RepresentationTheory.Algebra.TensorProduct.Quotient.quotientSMul
  RepresentationTheory.Algebra.TensorProduct.Quotient.quotientModule
  RepresentationTheory.Algebra.TensorProduct.Quotient.quotientToTensorProductLinearEquiv
