/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.FunctionRingHom
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

set_option backward.isDefEq.respectTransparency false

/-!
# A tensor induction functor for path algebras

This module constructs a tensor functor from modules over the function ring to modules over the
path algebra, proves its adjunction with scalar restriction along
`RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.functionRingHom`, and shows that its
objects are projective.
-/

universe u

open CategoryTheory TensorProduct

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-- Images of functions under the displayed map commute. -/
theorem scalarImages_commute (s t : Q → k) :
    Commute (functionRingHom k Q s) (functionRingHom k Q t) := by
  change functionRingHom k Q s * functionRingHom k Q t
      = functionRingHom k Q t * functionRingHom k Q s
  rw [← map_mul, ← map_mul, mul_comm]

/-- The ring homomorphism from the function ring into the opposite target algebra. -/
noncomputable def toOppositeRingHom : (Q → k) →+* (AuxiliaryPathType k Q)ᵐᵒᵖ :=
  (functionRingHom k Q).toOpposite scalarImages_commute

/-- The module structure of the target algebra over the function ring. -/
noncomputable instance moduleStructure : Module (Q → k) (AuxiliaryPathType k Q) :=
  Module.compHom (AuxiliaryPathType k Q) (toOppositeRingHom (k := k) (Q := Q))

/-- Function scalar multiplication on the algebra equals right multiplication by the corresponding
image. -/
theorem smul_eq_mul_image (s : Q → k) (a : AuxiliaryPathType k Q) :
    s • a = a * functionRingHom k Q s := rfl

/-- Scalar multiplication by functions commutes with multiplication in the target algebra. -/
instance smulCommClass : SMulCommClass (Q → k) (AuxiliaryPathType k Q) (AuxiliaryPathType k Q) where
  smul_comm s a b := by
    simp only [smul_eq_mul_image, smul_eq_mul, mul_assoc]

variable (k Q)

/-- Forms the target-algebra module associated with a module over the function ring. -/
noncomputable def obj (M : ModuleCat.{u + 1} (Q → k)) :
    ModuleCat.{u + 1} (AuxiliaryPathType k Q) :=
  ModuleCat.of (AuxiliaryPathType k Q) (TensorProduct (Q → k) (AuxiliaryPathType k Q) (M : Type (u + 1)))

variable {k Q}

/-- Maps a module morphism through the tensor construction. -/
noncomputable def map {M M' : ModuleCat.{u + 1} (Q → k)} (l : M ⟶ M') :
    obj k Q M ⟶ obj k Q M' :=
  ModuleCat.ofHom
    { __ := TensorProduct.map (LinearMap.id (R := Q → k) (M := AuxiliaryPathType k Q)) l.hom
      map_smul' := fun a x => by
        change TensorProduct.map (LinearMap.id (R := Q → k) (M := AuxiliaryPathType k Q)) l.hom (a • x)
          = a • TensorProduct.map (LinearMap.id (R := Q → k) (M := AuxiliaryPathType k Q)) l.hom x
        induction x with
        | zero => simp
        | tmul b m =>
            simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

/-- The induced map sends a pure tensor by applying the original morphism to its second factor. -/
@[simp]
theorem map_tmul {M M' : ModuleCat.{u + 1} (Q → k)} (l : M ⟶ M') (a : AuxiliaryPathType k Q)
    (m : M) : (map l).hom (a ⊗ₜ[Q → k] m) = a ⊗ₜ[Q → k] l.hom m := rfl

/-- The functor from modules over the function ring to modules over the target algebra. -/
noncomputable def functor :
    ModuleCat.{u + 1} (Q → k) ⥤ ModuleCat.{u + 1} (AuxiliaryPathType k Q) where
  obj := obj k Q
  map := map
  map_id M := by
    ext x
    refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
    · simp
    · simp [map_tmul]
    · simp only [map_add, hx, hy]
  map_comp {M M' M''} l l' := by
    ext x
    refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
    · simp
    · simp [map_tmul]
    · simp only [map_add, hx, hy]

/-! ## The tensor–restriction adjunction -/

section Adjunction

variable {M M' : ModuleCat.{u + 1} (Q → k)} {N N' : ModuleCat.{u + 1} (AuxiliaryPathType k Q)}

open ModuleCat (restrictScalars)

/-- A morphism after scalar restriction preserves the transported function action. -/
theorem hom_apply_smul (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N)
    (s : Q → k) (m : M) :
    (h.hom (s • m) : N) = functionRingHom k Q s • (h.hom m : N) :=
  h.hom.map_smul s m

/-- Constructs a morphism from the tensor construction using its value on unit tensors. -/
noncomputable def homOfTensorHom (g : functor.obj M ⟶ N) :
    M ⟶ (restrictScalars (functionRingHom k Q)).obj N :=
  ModuleCat.ofHom (X := M) (Y := (restrictScalars (functionRingHom k Q)).obj N)
    { toFun := fun m => g.hom (1 ⊗ₜ[Q → k] m)
      map_add' := fun m m' => by rw [tmul_add, map_add]
      map_smul' := fun s m => by
        have key : (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k] (s • (m : M))
            = functionRingHom k Q s • ((1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k] (m : M)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
            smul_eq_mul_image, one_mul]
        change (g.hom (1 ⊗ₜ[Q → k] (s • m)) : N)
          = functionRingHom k Q s • (g.hom (1 ⊗ₜ[Q → k] m) : N)
        rw [key, map_smul] }

/-- Packages a scalar-restricted morphism as an additive map from algebra elements to maps of
carriers. -/
noncomputable def actionMap (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N) :
    AuxiliaryPathType k Q →+ (M →+ N) where
  toFun a :=
    { toFun := fun m => a • (h.hom m : N)
      map_zero' := by simp
      map_add' := fun m m' => by rw [map_add, smul_add] }
  map_zero' := by ext m; simp
  map_add' a a' := by
    ext m; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul, AddMonoidHom.add_apply]

/-- The packaged map sends an algebra element and a module element to the scalar action on the
morphism value. -/
theorem actionMap_apply (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N)
    (a : AuxiliaryPathType k Q) (m : M) : actionMap h a m = a • (h.hom m : N) := rfl

/-- The packaged action map is balanced with respect to function scalars. -/
theorem actionMap_smul (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N)
    (s : Q → k) (a : AuxiliaryPathType k Q) (m : M) :
    actionMap h (s • a) m = actionMap h a (s • m) := by
  rw [actionMap_apply, actionMap_apply, hom_apply_smul, smul_eq_mul_image,
    SemigroupAction.mul_smul]

/-- Constructs a tensor-construction morphism from a morphism after scalar restriction. -/
noncomputable def tensorHomOfHom (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N) :
    functor.obj M ⟶ N :=
  ModuleCat.ofHom
    { toFun := TensorProduct.liftAddHom (actionMap h) (actionMap_smul h)
      map_add' := map_add _
      map_smul' := fun a x => by
        change TensorProduct.liftAddHom (actionMap h) (actionMap_smul h) (a • x)
          = a • TensorProduct.liftAddHom (actionMap h) (actionMap_smul h) x
        induction x with
        | zero => simp
        | tmul b m =>
            rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul,
              TensorProduct.liftAddHom_tmul, actionMap_apply, actionMap_apply, smul_eq_mul,
              SemigroupAction.mul_smul]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

/-- Describes the constructed morphism on pure tensors. -/
@[simp]
theorem tensorHomOfHom_tmul (h : M ⟶ (restrictScalars (functionRingHom k Q)).obj N)
    (a : AuxiliaryPathType k Q) (m : M) :
    (tensorHomOfHom h).hom (a ⊗ₜ[Q → k] m) = a • (h.hom m : N) := rfl

/-- Evaluates the constructed morphism at an element of the source module. -/
@[simp]
theorem homOfTensorHom_apply (g : functor.obj M ⟶ N) (m : M) :
    (homOfTensorHom g).hom m = g.hom (1 ⊗ₜ[Q → k] m) := rfl

/-- The adjunction between the displayed functor and scalar restriction. -/
noncomputable def adjunction :
    functor (k := k) (Q := Q) ⊣ restrictScalars (functionRingHom k Q) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := homOfTensorHom
          invFun := tensorHomOfHom
          left_inv := fun g => by
            apply ModuleCat.hom_ext
            ext x
            refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
            · simp
            · rw [tensorHomOfHom_tmul, homOfTensorHom_apply, ← g.hom.map_smul,
                TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            · rw [map_add, map_add, hx, hy]
          right_inv := fun h => by
            apply ModuleCat.hom_ext
            ext m
            rw [homOfTensorHom_apply, tensorHomOfHom_tmul, one_smul] }
      homEquiv_naturality_left_symm := fun {M' M N} f g => by
        apply ModuleCat.hom_ext
        ext x
        refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
        · simp
        · rfl
        · rw [map_add, map_add, hx, hy]
      homEquiv_naturality_right := fun {M N N'} f g => by
        apply ModuleCat.hom_ext
        ext m
        rfl }

/-- Objects produced by the functor are projective. -/
theorem projective_obj (M : ModuleCat.{u + 1} (Q → k)) :
    CategoryTheory.Projective (functor.obj M) := by
  have hSproj : CategoryTheory.Projective M := by
    have : Module.Projective (Q → k) M := Module.projective_of_isSemisimpleRing (Q → k) M
    exact M.projective_of_categoryTheory_projective
  haveI : (restrictScalars (functionRingHom k Q)).PreservesEpimorphisms := by
    constructor
    intro X Y φ hφ
    rw [ModuleCat.epi_iff_surjective] at hφ ⊢
    exact hφ
  haveI : (functor (k := k) (Q := Q)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (adjunction (k := k) (Q := Q))
  exact Functor.projective_obj_of_projective _ hSproj

end Adjunction

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
