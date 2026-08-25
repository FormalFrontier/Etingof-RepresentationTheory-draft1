/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import RepresentationTheory.LieModule.HomTensorAdjunction
import RepresentationTheory.Alignment.Attribute

/-!
# Representation adjunctions

This module packages adjunctions for representations, algebras, groups, and Lie algebras.
-/

open CategoryTheory MonoidalCategory

universe u v

-- v4.31: `LieRing.ofAssociativeRing` is no longer a global instance (only file-local in Mathlib);
-- re-enable it locally so the Lie structure on `End`/`Module.End` is found.
attribute [local instance] LieRing.ofAssociativeRing

/-- Tensoring by the right dual of a finite-dimensional group representation is left adjoint to tensoring by the representation. -/
@[source_ref "Chapter7/Example7.6.3" (role := supporting)]
noncomputable def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.rightDualTensorLeftAdjunction
    (k : Type u) (G : Type v) [Field k] [Group G] (V : FDRep k G) :
    tensorLeft (Vᘁ) ⊣ tensorLeft V :=
  tensorLeftAdjunction V Vᘁ

/-- Tensoring by a finite-dimensional group representation is left adjoint to tensoring by its right dual. -/
@[source_ref "Chapter7/Example7.6.3" (role := supporting)]
noncomputable def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.tensorLeftRightDualAdjunction
    (k : Type u) (G : Type v) [Field k] [Group G] (V : FDRep k G) :
    tensorLeft V ⊣ tensorLeft (Vᘁ) :=
  haveI : ExactPairing (Vᘁ) V := BraidedCategory.exactPairing_swap V Vᘁ
  tensorLeftAdjunction (Vᘁ) V

namespace RepresentationTheory.CategoryTheory.RepresentationAdjunctions

/-- The category-shaped collection of finite-dimensional representations of a Lie algebra. -/
structure FiniteDimensionalLieRep (k : Type u) [Field k] (L : Type u) [LieRing L] [LieAlgebra k L] where

  /-- The underlying vector space of a finite-dimensional Lie representation. -/
  carrier : Type u
  /-- The additive commutative group carried by a finite-dimensional Lie representation. -/
  [addCommGroup : AddCommGroup carrier]
  /-- The scalar module structure on a representation carrier. -/
  [moduleStructure : Module k carrier]
  /-- The induced Lie ring module structure on a representation carrier. -/
  [lieRingModule : LieRingModule L carrier]
  /-- The natural Lie module structure on a representation carrier. -/
  [lieModule : LieModule k L carrier]
  /-- The carrier of every object is finite-dimensional over the coefficient field. -/
  [finiteDimensional : FiniteDimensional k carrier]

namespace FiniteDimensionalLieRep

variable (k : Type u) [Field k] (L : Type u) [LieRing L] [LieAlgebra k L]

attribute [instance] addCommGroup moduleStructure lieRingModule lieModule finiteDimensional

/-- Coercion from a representation object to its underlying type. -/
instance coeSort : CoeSort (FiniteDimensionalLieRep k L) (Type u) := ⟨carrier⟩

/-- Builds a finite-dimensional representation from a finite-dimensional Lie module. -/
abbrev of (V : Type u) [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V] : FiniteDimensionalLieRep k L := ⟨V⟩

/-- Morphisms between finite-dimensional Lie representations. -/
structure Hom (V W : FiniteDimensionalLieRep k L) where

  /-- Interprets a representation morphism as an equivariant linear map. -/
  toLieModuleHom : V →ₗ⁅k,L⁆ W

/-- The category structure on finite-dimensional Lie representations. -/
instance category : Category (FiniteDimensionalLieRep k L) where
  Hom := Hom k L
  id _ := ⟨LieModuleHom.id⟩
  comp f g := ⟨g.toLieModuleHom.comp f.toLieModuleHom⟩

/-- Builds a representation morphism from an equivariant linear map. -/
abbrev ofHom {V W : Type u} [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [LieRingModule L W] [LieModule k L W] [FiniteDimensional k W]
    (f : V →ₗ⁅k,L⁆ W) : of k L V ⟶ of k L W := ⟨f⟩

/-- Representation morphisms are determined by their underlying equivariant linear maps. -/
theorem hom_ext {V W : FiniteDimensionalLieRep k L} {f g : V ⟶ W} (h : f.toLieModuleHom = g.toLieModuleHom) : f = g := by
  match f, g with
  | ⟨f⟩, ⟨g⟩ =>
    cases h
    rfl

/-- The identity representation morphism has the identity equivariant linear map. -/
@[simp] theorem id_toLieModuleHom (V : FiniteDimensionalLieRep k L) : (𝟙 V : V ⟶ V).toLieModuleHom = LieModuleHom.id := rfl

/-- Composition of representation morphisms agrees with composition of their equivariant linear maps. -/
@[simp] theorem hom_comp {U V W : FiniteDimensionalLieRep k L} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).toLieModuleHom = g.toLieModuleHom.comp f.toLieModuleHom := rfl

end FiniteDimensionalLieRep

variable {k : Type u} [Field k] {L : Type u} [LieRing L] [LieAlgebra k L]

/-- The equivariant symmetry equivalence for tensor products of representations. -/
noncomputable def tensorComm (V W : FiniteDimensionalLieRep k L) :
    TensorProduct k V W ≃ₗ⁅k,L⁆ TensorProduct k W V :=
  { TensorProduct.comm k V W with
    map_lie' := by
      intro x t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v w => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
      | add a b ha hb =>
        calc
          (TensorProduct.comm k V W) ⁅x, a + b⁆ =
              (TensorProduct.comm k V W) (⁅x, a⁆ + ⁅x, b⁆) := by rw [lie_add]
          _ = (TensorProduct.comm k V W) ⁅x, a⁆ +
              (TensorProduct.comm k V W) ⁅x, b⁆ := map_add _ _ _
          _ = ⁅x, (TensorProduct.comm k V W) a⁆ +
              ⁅x, (TensorProduct.comm k V W) b⁆ :=
            congrArg₂ (fun p q ↦ p + q) ha hb
          _ = ⁅x, (TensorProduct.comm k V W) a + (TensorProduct.comm k V W) b⁆ := by
            rw [lie_add]
          _ = ⁅x, (TensorProduct.comm k V W) (a + b)⁆ := by rw [map_add] }

/-- The tensor symmetry sends a pure tensor to the reversed order. -/
@[simp]
theorem tensorComm_tmul (V W : FiniteDimensionalLieRep k L) (v : V) (w : W) :
    tensorComm V W (v ⊗ₜ[k] w) = w ⊗ₜ[k] v := rfl

/-- The inverse tensor symmetry sends a reversed pure tensor to the original order. -/
@[simp]
theorem tensorComm_symm_tmul (V W : FiniteDimensionalLieRep k L) (w : W) (v : V) :
    (tensorComm V W).symm (w ⊗ₜ[k] v) = v ⊗ₜ[k] w := rfl

/-- The tensor product map of equivariant linear maps acts componentwise on pure tensors. -/
@[simp]
theorem lieModuleTensorMap_tmul {A B C D : Type u}
    [AddCommGroup A] [Module k A] [LieRingModule L A] [LieModule k L A]
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    [AddCommGroup D] [Module k D] [LieRingModule L D] [LieModule k L D]
    (f : LieModuleHom k L A C) (g : LieModuleHom k L B D) (a : A) (b : B) :
    TensorProduct.LieModule.map f g (a ⊗ₜ[k] b) = f a ⊗ₜ[k] g b := rfl

/-- A finite-dimensional Lie representation is equivariantly equivalent to its double dual. -/
noncomputable def doubleDualEquiv (V : FiniteDimensionalLieRep k L) :
    V ≃ₗ⁅k,L⁆ Module.Dual k (Module.Dual k V) :=
  { Module.evalEquiv k V with
    map_lie' := by
      intro x v
      ext f
      simp }

/-- The endofunctor given by tensoring a representation on the left. -/
def tensorLeft (V : FiniteDimensionalLieRep k L) : FiniteDimensionalLieRep k L ⥤ FiniteDimensionalLieRep k L where
  obj W := FiniteDimensionalLieRep.of k L (TensorProduct k V W)
  map f := FiniteDimensionalLieRep.ofHom k L (TensorProduct.LieModule.map LieModuleHom.id f.toLieModuleHom)
  map_id W := by
    apply FiniteDimensionalLieRep.hom_ext
    apply LieModuleHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
  map_comp f g := by
    apply FiniteDimensionalLieRep.hom_ext
    apply LieModuleHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb

/-- The dual finite-dimensional Lie representation. -/
noncomputable def dual (V : FiniteDimensionalLieRep k L) : FiniteDimensionalLieRep k L :=
  FiniteDimensionalLieRep.of k L (Module.Dual k V)

/-- An equivariant equivalence between source modules induces a linear equivalence between the corresponding equivariant hom spaces. -/
def lieModuleHom_precompEquiv {A B C : Type u}
    [AddCommGroup A] [Module k A] [LieRingModule L A] [LieModule k L A]
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    (e : A ≃ₗ⁅k,L⁆ B) : (A →ₗ⁅k,L⁆ C) ≃ₗ[k] (B →ₗ⁅k,L⁆ C) where
  toFun f := f.comp (e.symm : B →ₗ⁅k,L⁆ A)
  invFun g := g.comp (e : A →ₗ⁅k,L⁆ B)
  map_add' f g := by ext; simp [LieModuleHom.comp_apply]
  map_smul' c f := by ext; simp [LieModuleHom.comp_apply]
  left_inv f := by ext; simp [LieModuleHom.comp_apply]
  right_inv g := by ext; simp [LieModuleHom.comp_apply]

/-- Currying gives a linear equivalence from equivariant maps out of a tensor product to equivariant maps into a dual tensor product. -/
noncomputable def tensorHomCurrying (V W U : FiniteDimensionalLieRep k L) :
    (TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (W →ₗ⁅k,L⁆ TensorProduct k (Module.Dual k V) U) :=
  (lieModuleHom_precompEquiv (tensorComm V W)).trans
    ((TensorProduct.LieModule.liftLie k L W V U).symm.trans
      ((RepresentationTheory.LieModule.HomTensorAdjunction.lieModuleHomCongr
          (RepresentationTheory.LieModule.HomTensorAdjunction.linearMapLieModuleEquivTensorDual (k := k) (L := L) (W := V) (U := U))).trans
        (RepresentationTheory.LieModule.HomTensorAdjunction.lieModuleHomCongr (tensorComm (FiniteDimensionalLieRep.of k L U) (dual V)))))

/-- The tensor-duality adjunction equivalence on representation morphisms. -/
noncomputable def tensorLeftHomEquiv (V W U : FiniteDimensionalLieRep k L) :
    ((tensorLeft V).obj W ⟶ U) ≃
      (W ⟶ (tensorLeft (dual V)).obj U) where
  toFun f := FiniteDimensionalLieRep.ofHom k L (tensorHomCurrying V W U f.toLieModuleHom)
  invFun g := FiniteDimensionalLieRep.ofHom k L ((tensorHomCurrying V W U).symm g.toLieModuleHom)
  left_inv f := by
    apply FiniteDimensionalLieRep.hom_ext
    exact (tensorHomCurrying V W U).symm_apply_apply f.toLieModuleHom
  right_inv g := by
    apply FiniteDimensionalLieRep.hom_ext
    exact (tensorHomCurrying V W U).apply_symm_apply g.toLieModuleHom

/-- The inverse currying map is evaluated on a pure tensor by dual-tensor evaluation. -/
theorem tensorHomCurrying_symm_apply (V W U : FiniteDimensionalLieRep k L)
    (g : LieModuleHom k L W (TensorProduct k (Module.Dual k V) U))
    (v : V) (w : W) :
    (tensorHomCurrying V W U).symm g (v ⊗ₜ[k] w) =
      dualTensorHom k V U (g w) v := by
  simp only [tensorHomCurrying, lieModuleHom_precompEquiv,
    RepresentationTheory.LieModule.HomTensorAdjunction.lieModuleHomCongr, RepresentationTheory.LieModule.HomTensorAdjunction.linearMapLieModuleEquivTensorDual,
    dualTensorHomEquiv, LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm,
    TensorProduct.comm_symm, LieModuleEquiv.symm_symm, LinearEquiv.symm_mk,
    LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.coe_mk, LieModuleHom.comp_apply,
    LieModuleEquiv.coe_coe, tensorComm_tmul,
    TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LinearEquiv.coe_coe, dualTensorHomEquivOfBasis_apply]
  congr 2
  exact (tensorComm (FiniteDimensionalLieRep.of k L U) (dual V)).apply_symm_apply (g w)

/-- Evaluating the curried tensor morphism gives the original morphism on a pure tensor. -/
theorem tensorHomCurrying_apply (V W U : FiniteDimensionalLieRep k L)
    (f : LieModuleHom k L (TensorProduct k V W) U) (w : W) (v : V) :
    dualTensorHom k V U ((tensorHomCurrying V W U f) w) v =
      f (v ⊗ₜ[k] w) := by
  rw [← tensorHomCurrying_symm_apply V W U
      (tensorHomCurrying V W U f) v w,
    LinearEquiv.symm_apply_apply]

/-- Evaluation through a dual tensor homomorphism commutes with a linear map of targets. -/
theorem dualTensorHom_map {A B : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (V : FiniteDimensionalLieRep k L)
    (g : A →ₗ[k] B) (t : TensorProduct k (Module.Dual k V) A) (v : V) :
    dualTensorHom k V B (TensorProduct.map LinearMap.id g t) v =
      g (dualTensorHom k V A t v) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul f a => simp [dualTensorHom_apply]

/-- An equivariant isomorphism induces an isomorphism between the corresponding tensor-left functors. -/
noncomputable def tensorLeftCongr {V V' : FiniteDimensionalLieRep k L}
    (e : LieModuleEquiv k L V V') : tensorLeft V ≅ tensorLeft V' :=
  NatIso.ofComponents
    (fun W =>
      { hom := FiniteDimensionalLieRep.ofHom k L (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id)
        inv := FiniteDimensionalLieRep.ofHom k L
          (TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id)
        hom_inv_id := by
          apply FiniteDimensionalLieRep.hom_ext
          apply LieModuleHom.ext
          intro t
          change TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id
              (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id t) = t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
          | tmul v w => simp
        inv_hom_id := by
          apply FiniteDimensionalLieRep.hom_ext
          apply LieModuleHom.ext
          intro t
          change TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id
              (TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id t) = t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
          | tmul v w => simp })
    (fun f => by
      apply FiniteDimensionalLieRep.hom_ext
      apply LieModuleHom.ext
      intro t
      change TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id
          (TensorProduct.LieModule.map LieModuleHom.id f.toLieModuleHom t) =
        TensorProduct.LieModule.map LieModuleHom.id f.toLieModuleHom
          (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id t)
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
      | tmul v w => simp)

/-- Tensoring with a representation is left adjoint to tensoring with its dual. -/
@[source_ref "Chapter7/Example7.6.3" (role := supporting)]
noncomputable def tensorDualAdjunction (V : FiniteDimensionalLieRep k L) :
    tensorLeft V ⊣ tensorLeft (dual V) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorLeftHomEquiv V
    homEquiv_naturality_left_symm := by
      intro W' W U f g
      apply FiniteDimensionalLieRep.hom_ext
      apply LieModuleHom.ext
      intro t
      change ((tensorHomCurrying V W' U).symm (g.toLieModuleHom.comp f.toLieModuleHom)) t =
        ((tensorHomCurrying V W U).symm g.toLieModuleHom)
          (TensorProduct.LieModule.map LieModuleHom.id f.toLieModuleHom t)
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
      | tmul v w =>
        simp [tensorHomCurrying_symm_apply]
        rfl
    homEquiv_naturality_right := by
      intro W U U' f g
      apply FiniteDimensionalLieRep.hom_ext
      apply LieModuleHom.ext
      intro w
      change tensorHomCurrying V W U' (g.toLieModuleHom.comp f.toLieModuleHom) w =
        TensorProduct.LieModule.map LieModuleHom.id g.toLieModuleHom
          (tensorHomCurrying V W U f.toLieModuleHom w)
      apply (dualTensorHomEquiv k V U').injective
      apply LinearMap.ext
      intro v
      simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply]
      rw [tensorHomCurrying_apply]
      change g.toLieModuleHom (f.toLieModuleHom (v ⊗ₜ[k] w)) =
        dualTensorHom k V U'
          (TensorProduct.map LinearMap.id g.toLieModuleHom.toLinearMap
            (tensorHomCurrying V W U f.toLieModuleHom w)) v
      rw [dualTensorHom_map, tensorHomCurrying_apply]
      rfl
  }

/-- Tensoring with a dual representation is left adjoint to tensoring with the representation. -/
@[source_ref "Chapter7/Example7.6.3" (role := supporting)]
noncomputable def dualTensorAdjunction (V : FiniteDimensionalLieRep k L) :
    tensorLeft (dual V) ⊣ tensorLeft V :=
  (tensorDualAdjunction (dual V)).ofNatIsoRight
    (tensorLeftCongr (doubleDualEquiv V).symm)

end RepresentationTheory.CategoryTheory.RepresentationAdjunctions

/-- Induction along a group homomorphism is left adjoint to restriction. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
noncomputable def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.inductionRestrictionAdjunction
    (k : Type u) {G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) :
    Rep.indFunctor k φ ⊣ Rep.resFunctor φ :=
  Rep.indResAdjunction k φ

/-- Restriction to a finite-index subgroup is left adjoint to induction. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
noncomputable def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.restrictionInductionAdjunction
    (k : Type u) {G : Type v} [CommRing k] [Group G] (S : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex] :
    Rep.resFunctor S.subtype ⊣ Rep.indFunctor k S.subtype :=
  Rep.resIndAdjunction k S

/-- Algebra maps from an enveloping algebra correspond to Lie algebra homomorphisms. -/
def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.universalEnvelopingAlgebraAlgHomEquiv
    (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (A : Type*) [Ring A] [Algebra R A] :
    (L →ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) :=
  UniversalEnvelopingAlgebra.lift R

/-- Algebra maps from a monoid algebra correspond to group homomorphisms into units. -/
noncomputable def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.monoidAlgebraAlgHomEquiv
    (k : Type*) [CommRing k] (G : Type*) [Group G] (A : Type*) [Ring A] [Algebra k A] :
    (G →* Aˣ) ≃ (MonoidAlgebra k G →ₐ[k] A) :=
  let unitsEquiv : (G →* Aˣ) ≃ (G →* A) :=
    { toFun := fun f => (Units.coeHom A).comp f
      invFun := fun f => f.toHomUnits
      left_inv := fun f => by ext g; simp
      right_inv := fun f => by ext g; simp }
  unitsEquiv.trans (MonoidAlgebra.lift k A G)

/-- Algebra maps from a tensor algebra correspond to linear maps from its generators. -/
def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.tensorAlgebraAlgHomEquiv
    (k : Type*) [CommRing k] (V : Type*) [AddCommMonoid V] [Module k V]
    (A : Type*) [Semiring A] [Algebra k A] :
    (V →ₗ[k] A) ≃ (TensorAlgebra k V →ₐ[k] A) :=
  TensorAlgebra.lift k

/-- Algebra maps from a symmetric algebra correspond to linear maps from its generators. -/
def RepresentationTheory.CategoryTheory.RepresentationAdjunctions.symmetricAlgebraAlgHomEquiv
    (k : Type*) [CommRing k] (V : Type*) [AddCommMonoid V] [Module k V]
    (A : Type*) [CommSemiring A] [Algebra k A] :
    (V →ₗ[k] A) ≃ (SymmetricAlgebra k V →ₐ[k] A) :=
  SymmetricAlgebra.lift

namespace RepresentationTheory.CategoryTheory.RepresentationAdjunctions

/-- The category-shaped collection of Lie algebras over a commutative ring. -/
structure LieAlgebraCategory (R : Type u) [CommRing R] where

  /-- The underlying type of an object in the Lie algebra category. -/
  carrier : Type u
  /-- The underlying Lie ring structure carried by a category object. -/
  [lieRing : LieRing carrier]
  /-- The Lie algebra structure carried by an object of the category. -/
  [lieAlgebra : LieAlgebra R carrier]

namespace LieAlgebraCategory

variable (R : Type u) [CommRing R]

attribute [instance] lieRing lieAlgebra

/-- Coercion from a Lie algebra category object to its underlying type. -/
instance coeSort : CoeSort (LieAlgebraCategory R) (Type u) := ⟨carrier⟩

/-- Builds a Lie algebra category object from a Lie algebra. -/
abbrev of (L : Type u) [LieRing L] [LieAlgebra R L] : LieAlgebraCategory R := ⟨L⟩

/-- Morphisms between Lie algebras over a fixed commutative ring. -/
structure Hom (L M : LieAlgebraCategory R) where

  /-- Interprets a category morphism as a homomorphism of Lie algebras. -/
  toLieHom : L →ₗ⁅R⁆ M

/-- The category structure on Lie algebras over the base ring. -/
instance category : Category (LieAlgebraCategory R) where
  Hom := Hom R
  id L := ⟨LieHom.id⟩
  comp f g := ⟨g.toLieHom.comp f.toLieHom⟩

/-- The identity category morphism is represented by the identity Lie homomorphism. -/
@[simp] theorem id_toLieHom (L : LieAlgebraCategory R) : (𝟙 L : L ⟶ L).toLieHom = LieHom.id := rfl

/-- Composition in the Lie algebra category agrees with composition of Lie homomorphisms. -/
@[simp] theorem hom_comp {L M N : LieAlgebraCategory R} (f : L ⟶ M) (g : M ⟶ N) :
    (f ≫ g).toLieHom = g.toLieHom.comp f.toLieHom := rfl

/-- Builds a category morphism from a homomorphism of Lie algebras. -/
abbrev ofHom {L M : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) : of R L ⟶ of R M := ⟨f⟩

/-- Lie algebra category morphisms are determined by their Lie homomorphisms. -/
theorem hom_ext {L M : LieAlgebraCategory R} {f g : L ⟶ M} (h : f.toLieHom = g.toLieHom) : f = g := by
  match f, g with
  | ⟨f⟩, ⟨g⟩ =>
    cases h
    rfl

end LieAlgebraCategory

/-- Sends an associative algebra to its underlying Lie algebra. -/
def algToLieAlgebra (R : Type u) [CommRing R] : AlgCat.{u} R ⥤ LieAlgebraCategory R where
  obj A := LieAlgebraCategory.of R A
  map f := LieAlgebraCategory.ofHom R f.hom.toLieHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor sending a Lie algebra to its universal enveloping algebra. -/
def universalEnvelopingAlgebraFunctor (R : Type u) [CommRing R] : LieAlgebraCategory R ⥤ AlgCat.{u} R where
  obj L := AlgCat.of R (UniversalEnvelopingAlgebra R L)
  map f := AlgCat.ofHom <| UniversalEnvelopingAlgebra.lift R <|
    (UniversalEnvelopingAlgebra.ι R).comp f.toLieHom
  map_id L := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp

/-- The universal-enveloping-algebra adjunction equivalence on morphism spaces. -/
def universalEnvelopingAlgebraHomEquiv (R : Type u) [CommRing R]
    (L : LieAlgebraCategory R) (A : AlgCat.{u} R) :
    ((universalEnvelopingAlgebraFunctor R).obj L ⟶ A) ≃ (L ⟶ (algToLieAlgebra R).obj A) where
  toFun f := LieAlgebraCategory.ofHom R ((UniversalEnvelopingAlgebra.lift (A := A) R).symm f.hom)
  invFun g := AlgCat.ofHom ((UniversalEnvelopingAlgebra.lift (A := A) R) g.toLieHom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (UniversalEnvelopingAlgebra.lift (A := A) R).apply_symm_apply f.hom
  right_inv g := by
    apply LieAlgebraCategory.hom_ext
    exact (UniversalEnvelopingAlgebra.lift (A := A) R).symm_apply_apply g.toLieHom

/-- The universal enveloping algebra functor is left adjoint to the underlying Lie algebra functor. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
def universalEnvelopingAlgebraAdjunction (R : Type u) [CommRing R] :
    universalEnvelopingAlgebraFunctor R ⊣ algToLieAlgebra R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := universalEnvelopingAlgebraHomEquiv R
    homEquiv_naturality_left_symm := by
      intro L' L A f g
      apply AlgCat.hom_ext
      change UniversalEnvelopingAlgebra.lift (A := A) R (f ≫ g).toLieHom =
        (UniversalEnvelopingAlgebra.lift (A := A) R g.toLieHom).comp
          (UniversalEnvelopingAlgebra.lift R
            ((UniversalEnvelopingAlgebra.ι R).comp f.toLieHom))
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      simp
      rfl
    homEquiv_naturality_right := by
      intro L A A' f g
      apply LieAlgebraCategory.hom_ext
      change (g.hom.comp f.hom).toLieHom.comp (UniversalEnvelopingAlgebra.ι R) =
        g.hom.toLieHom.comp (f.hom.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))
      rfl
  }

/-- The underlying algebra homomorphism of the inverse adjunction equivalence is induced by the given Lie algebra homomorphism. -/
@[simp] theorem universalEnvelopingAlgebraHomEquiv_symm_hom
    (R : Type u) [CommRing R] (L A : Type u) [LieRing L] [LieAlgebra R L]
    [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A) :
    ((universalEnvelopingAlgebraHomEquiv R (LieAlgebraCategory.of R L) (AlgCat.of R A)).symm
      (LieAlgebraCategory.ofHom R f)).hom = universalEnvelopingAlgebraAlgHomEquiv R L A f := rfl

/-- The functor sending a group to its monoid algebra. -/
noncomputable def monoidAlgebraFunctor (k : Type u) [CommRing k] :
    GrpCat.{u} ⥤ AlgCat.{u} k where
  obj G := AlgCat.of k (MonoidAlgebra k G)
  map f := AlgCat.ofHom (MonoidAlgebra.mapDomainAlgHom k k f.hom)
  map_id G := by
    apply AlgCat.hom_ext
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    simp

/-- The functor sending an algebra to the group of its units. -/
def unitsFunctor (k : Type u) [CommRing k] : AlgCat.{u} k ⥤ GrpCat.{u} where
  obj A := GrpCat.of Aˣ
  map f := GrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id A := by
    apply GrpCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    ext x
    rfl

/-- The adjunction equivalence between group maps to units and algebra maps from a monoid algebra. -/
noncomputable def monoidAlgebraHomEquiv (k : Type u) [CommRing k]
    (G : GrpCat.{u}) (A : AlgCat.{u} k) :
    ((monoidAlgebraFunctor k).obj G ⟶ A) ≃ (G ⟶ (unitsFunctor k).obj A) where
  toFun f := GrpCat.ofHom ((monoidAlgebraAlgHomEquiv k G A).symm f.hom)
  invFun g := AlgCat.ofHom (monoidAlgebraAlgHomEquiv k G A g.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (monoidAlgebraAlgHomEquiv k G A).apply_symm_apply f.hom
  right_inv g := by
    apply GrpCat.hom_ext
    exact (monoidAlgebraAlgHomEquiv k G A).symm_apply_apply g.hom

/-- The monoid algebra functor is left adjoint to the units functor. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
noncomputable def monoidAlgebraAdjunction (k : Type u) [CommRing k] :
    monoidAlgebraFunctor k ⊣ unitsFunctor k :=
  Adjunction.mkOfHomEquiv {
    homEquiv := monoidAlgebraHomEquiv k
    homEquiv_naturality_left_symm := by
      intro G' G A f g
      apply AlgCat.hom_ext
      change MonoidAlgebra.lift k A G'
          ((Units.coeHom A).comp (g.hom.comp f.hom)) =
        (MonoidAlgebra.lift k A G ((Units.coeHom A).comp g.hom)).comp
          (MonoidAlgebra.mapDomainAlgHom k k f.hom)
      apply MonoidAlgebra.algHom_ext
      · intro x
        simp
        rfl
      · ext
    homEquiv_naturality_right := by
      intro G A A' f g
      apply GrpCat.hom_ext
      ext x
      apply Units.ext
      rfl
  }

/-- The underlying algebra homomorphism of the inverse adjunction equivalence is the map induced by the given homomorphism into units. -/
@[simp] theorem monoidAlgebraHomEquiv_symm_hom
    (k : Type u) [CommRing k] (G A : Type u) [Group G] [Ring A] [Algebra k A]
    (f : G →* Aˣ) :
    ((monoidAlgebraHomEquiv k (GrpCat.of G) (AlgCat.of k A)).symm
      (GrpCat.ofHom f)).hom = monoidAlgebraAlgHomEquiv k G A f := rfl

/-- The functor sending a module to its tensor algebra. -/
def tensorAlgebraFunctor (k : Type u) [CommRing k] : ModuleCat.{u} k ⥤ AlgCat.{u} k where
  obj V := AlgCat.of k (TensorAlgebra k V)
  map f := AlgCat.ofHom <| TensorAlgebra.lift k <| (TensorAlgebra.ι k).comp f.hom
  map_id V := by
    apply AlgCat.hom_ext
    apply TensorAlgebra.hom_ext
    ext x
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    apply TensorAlgebra.hom_ext
    ext x
    simp

/-- The tensor-algebra adjunction equivalence on morphism spaces. -/
def tensorAlgebraHomEquiv (k : Type u) [CommRing k]
    (V : ModuleCat.{u} k) (A : AlgCat.{u} k) :
    ((tensorAlgebraFunctor k).obj V ⟶ A) ≃
      (V ⟶ (forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)).obj A) where
  toFun f := ModuleCat.ofHom ((TensorAlgebra.lift k).symm f.hom)
  invFun g := AlgCat.ofHom (TensorAlgebra.lift (A := A) k g.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (TensorAlgebra.lift k).apply_symm_apply f.hom
  right_inv g := by
    apply ModuleCat.hom_ext
    exact (TensorAlgebra.lift (A := A) k).symm_apply_apply g.hom

/-- The tensor algebra functor is left adjoint to the forgetful functor to modules. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
def tensorAlgebraAdjunction (k : Type u) [CommRing k] :
    tensorAlgebraFunctor k ⊣ forget₂ (AlgCat.{u} k) (ModuleCat.{u} k) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorAlgebraHomEquiv k
    homEquiv_naturality_left_symm := by
      intro V' V A f g
      apply AlgCat.hom_ext
      change TensorAlgebra.lift (A := A) k (g.hom.comp f.hom) =
        (TensorAlgebra.lift (A := A) k g.hom).comp
          (TensorAlgebra.lift k ((TensorAlgebra.ι k).comp f.hom))
      apply TensorAlgebra.hom_ext
      ext x
      simp
    homEquiv_naturality_right := by
      intro V A A' f g
      apply ModuleCat.hom_ext
      change (g.hom.comp f.hom).toLinearMap.comp (TensorAlgebra.ι k) =
        g.hom.toLinearMap.comp (f.hom.toLinearMap.comp (TensorAlgebra.ι k))
      rfl
  }

/-- The underlying algebra homomorphism of the inverse adjunction equivalence is induced by the given linear map. -/
@[simp] theorem tensorAlgebraHomEquiv_symm_hom
    (k : Type u) [CommRing k] (V A : Type u) [AddCommGroup V] [Module k V]
    [Ring A] [Algebra k A] (f : V →ₗ[k] A) :
    ((tensorAlgebraHomEquiv k (ModuleCat.of k V) (AlgCat.of k A)).symm
      (ModuleCat.ofHom f)).hom = tensorAlgebraAlgHomEquiv k V A f := rfl

/-- The forgetful functor from commutative algebras to modules. -/
def commAlgForgetToModule (k : Type u) [CommRing k] :
    CommAlgCat.{u} k ⥤ ModuleCat.{u} k :=
  forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙
    forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)

/-- The functor sending a module to its symmetric algebra. -/
def symmetricAlgebraFunctor (k : Type u) [CommRing k] :
    ModuleCat.{u} k ⥤ CommAlgCat.{u} k where
  obj V := CommAlgCat.of k (SymmetricAlgebra k V)
  map f := CommAlgCat.ofHom <| SymmetricAlgebra.lift <|
    (SymmetricAlgebra.ι k _).comp f.hom
  map_id V := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    simp
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    simp

/-- The symmetric-algebra adjunction equivalence on morphism spaces. -/
def symmetricAlgebraHomEquiv (k : Type u) [CommRing k]
    (V : ModuleCat.{u} k) (A : CommAlgCat.{u} k) :
    ((symmetricAlgebraFunctor k).obj V ⟶ A) ≃
      (V ⟶ (commAlgForgetToModule k).obj A) where
  toFun f := ModuleCat.ofHom (f.hom.toLinearMap.comp (SymmetricAlgebra.ι k V))
  invFun g := CommAlgCat.ofHom (SymmetricAlgebra.lift (A := A) g.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    simp
    rfl
  right_inv g := by
    apply ModuleCat.hom_ext
    ext x
    change SymmetricAlgebra.lift (A := A) g.hom (SymmetricAlgebra.ι k V x) = g.hom x
    simp
    rfl

/-- The symmetric algebra functor is left adjoint to the forgetful functor to modules. -/
@[source_ref "Chapter7/Example7.6.3" (role := primary)]
def symmetricAlgebraAdjunction (k : Type u) [CommRing k] :
    symmetricAlgebraFunctor k ⊣ commAlgForgetToModule k :=
  Adjunction.mkOfHomEquiv {
    homEquiv := symmetricAlgebraHomEquiv k
    homEquiv_naturality_left_symm := by
      intro V' V A f g
      apply CommAlgCat.hom_ext
      change SymmetricAlgebra.lift (A := A) (g.hom.comp f.hom) =
        (SymmetricAlgebra.lift (A := A) g.hom).comp
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp f.hom))
      apply SymmetricAlgebra.algHom_ext
      ext x
      simp
      rfl
    homEquiv_naturality_right := by
      intro V A A' f g
      apply ModuleCat.hom_ext
      rfl
  }

/-- The underlying algebra homomorphism of the inverse adjunction equivalence is induced by the given linear map. -/
@[simp] theorem symmetricAlgebraHomEquiv_symm_hom
    (k : Type u) [CommRing k] (V A : Type u) [AddCommGroup V] [Module k V]
    [CommRing A] [Algebra k A] (f : V →ₗ[k] A) :
    ((symmetricAlgebraHomEquiv k (ModuleCat.of k V) (CommAlgCat.of k A)).symm
      (ModuleCat.ofHom f)).hom = symmetricAlgebraAlgHomEquiv k V A f := rfl

end RepresentationTheory.CategoryTheory.RepresentationAdjunctions
