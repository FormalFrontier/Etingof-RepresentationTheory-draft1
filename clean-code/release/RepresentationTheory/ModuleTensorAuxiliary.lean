/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.EdgeModule
import RepresentationTheory.TensorAdjunction

set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary module tensor constructions

This module constructs auxiliary tensor-product module objects and morphisms associated with a
module over a quiver path algebra, and packages them into a short complex.
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-! ## Auxiliary weighted-action arithmetic -/

omit [DecidableEq Q] [Fintype Q] in
/-- The auxiliary weighted action preserves addition in its finitely supported argument. -/
theorem auxiliaryAction_add_argument (wt : Edge Q → Q) (s : Q → k) (v w : Edge Q →₀ k) :
    weightedScale k Q wt s (v + w) = weightedScale k Q wt s v + weightedScale k Q wt s w := by
  ext i; simp only [weightedScale_apply, Finsupp.add_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
/-- The auxiliary weighted action sends a sum of functions to the sum of their actions. -/
theorem auxiliaryAction_add_scalar (wt : Edge Q → Q) (s t : Q → k) (v : Edge Q →₀ k) :
    weightedScale k Q wt (s + t) v =
      weightedScale k Q wt s v + weightedScale k Q wt t v := by
  ext i; simp only [weightedScale_apply, Finsupp.add_apply, Pi.add_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
/-- The auxiliary weighted action of the zero function is zero. -/
theorem auxiliaryAction_zero_scalar (wt : Edge Q → Q) (v : Edge Q →₀ k) :
    weightedScale k Q wt 0 v = 0 := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
/-- The auxiliary weighted action of the constant one function fixes every finitely supported value. -/
theorem auxiliaryAction_one_scalar (wt : Edge Q → Q) (v : Edge Q →₀ k) :
    weightedScale k Q wt 1 v = v := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
/-- The action of a product of functions is the successive auxiliary action of the two functions. -/
theorem auxiliaryAction_mul_scalar (wt : Edge Q → Q) (s t : Q → k) (v : Edge Q →₀ k) :
    weightedScale k Q wt (s * t) v =
      weightedScale k Q wt s (weightedScale k Q wt t v) := by
  ext i; simp only [weightedScale_apply, Pi.mul_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
/-- The auxiliary weighted action sends the zero finitely supported value to zero. -/
theorem auxiliaryAction_zero_argument (wt : Edge Q → Q) (s : Q → k) :
    weightedScale k Q wt s (0 : Edge Q →₀ k) = 0 := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
/-- On a singleton, the auxiliary weighted action multiplies its coefficient by the function value at the assigned vertex. -/
theorem auxiliaryAction_single (wt : Edge Q → Q) (s : Q → k) (x : Edge Q) (c : k) :
    weightedScale k Q wt s (Finsupp.single x c) = Finsupp.single x (s (wt x) * c) := by
  classical
  ext i
  rw [weightedScale_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-! ## Weighted scaling under the edge linear map -/

/-- Under the displayed map, the first auxiliary weighted action agrees with left multiplication by the image of the function. -/
theorem auxiliary_left_weight_eq_mul (s : Q → k) (v : Edge Q →₀ k) :
    edgeLinearMap (weightedScale k Q Edge.source s v) =
      functionRingHom k Q s * edgeLinearMap v := by
  induction v using Finsupp.induction_linear with
  | zero => simp [auxiliaryAction_zero_argument]
  | add v w hv hw => rw [auxiliaryAction_add_argument, map_add, map_add, mul_add, hv, hw]
  | single x c =>
      rw [auxiliaryAction_single, edgeLinearMap_single, edgeLinearMap_single, mul_smul_comm,
        vertexFunction_mul, smul_smul, mul_comm c]

/-- Under the displayed map, the second auxiliary weighted action agrees with right multiplication by the image of the function. -/
theorem auxiliary_right_weight_eq_mul (s : Q → k) (v : Edge Q →₀ k) :
    edgeLinearMap (weightedScale k Q Edge.target s v) =
      edgeLinearMap v * functionRingHom k Q s := by
  induction v using Finsupp.induction_linear with
  | zero => simp [auxiliaryAction_zero_argument]
  | add v w hv hw => rw [auxiliaryAction_add_argument, map_add, map_add, add_mul, hv, hw]
  | single x c =>
      rw [auxiliaryAction_single, edgeLinearMap_single, edgeLinearMap_single, smul_mul_assoc,
        mul_vertexFunction, smul_smul, mul_comm c]

/-! ## An auxiliary type with the target action -/

variable (k Q) in
/-- An auxiliary type associated to a field and a quiver. -/
def FieldQuiverAuxiliary : Type (u + 1) := Edge Q →₀ k

/-- The additive commutative group structure on the auxiliary type. -/
noncomputable instance instAddCommGroupFieldQuiverAuxiliary :
    AddCommGroup (FieldQuiverAuxiliary k Q) :=
  inferInstanceAs (AddCommGroup (Edge Q →₀ k))

/-- The ground-field module structure on the auxiliary type. -/
noncomputable instance instModuleFieldQuiverAuxiliary : Module k (FieldQuiverAuxiliary k Q) :=
  inferInstanceAs (Module k (Edge Q →₀ k))

/-- The module structure on the auxiliary type over the ring of vertex-indexed functions. -/
noncomputable instance instModuleFunctionsFieldQuiverAuxiliary :
    Module (Q → k) (FieldQuiverAuxiliary k Q) :=
  edgeFinsuppModule' k Q

/-- The linear endomorphism of the auxiliary type determined by a vertex-indexed function. -/
noncomputable def functionAction (s : Q → k) :
    FieldQuiverAuxiliary k Q →ₗ[Q → k] FieldQuiverAuxiliary k Q where
  toFun v := weightedScale k Q Edge.source s v
  map_add' v w := auxiliaryAction_add_argument _ _ _ _
  map_smul' t v := by
    change weightedScale k Q Edge.source s (weightedScale k Q Edge.target t v) =
      weightedScale k Q Edge.target t (weightedScale k Q Edge.source s v)
    exact source_target_scale_commute s t v

omit [DecidableEq Q] [Fintype Q] in
/-- Applying the function endomorphism agrees with the displayed auxiliary weighted action. -/
@[simp] theorem functionAction_apply (s : Q → k) (v : FieldQuiverAuxiliary k Q) :
    functionAction s v = weightedScale k Q Edge.source s v := rfl

omit [DecidableEq Q] [Fintype Q] in
/-- The endomorphism associated to the constant one function is the identity. -/
theorem functionAction_one : functionAction (1 : Q → k) = LinearMap.id := by
  ext v; simp [functionAction_apply, auxiliaryAction_one_scalar]

omit [DecidableEq Q] [Fintype Q] in
/-- The endomorphism associated to a product of functions is the composite of their endomorphisms. -/
theorem functionAction_mul (s t : Q → k) :
    functionAction (s * t) = functionAction s ∘ₗ functionAction t := by
  ext v; simp [functionAction_apply, auxiliaryAction_mul_scalar]

omit [DecidableEq Q] [Fintype Q] in
/-- The endomorphism associated to a sum of functions is the sum of their endomorphisms. -/
theorem functionAction_add (s t : Q → k) : functionAction (s + t) = functionAction s + functionAction t := by
  ext v; simp [functionAction_apply, auxiliaryAction_add_scalar]

omit [DecidableEq Q] [Fintype Q] in
/-- The endomorphism associated to the zero function is zero. -/
theorem functionAction_zero : functionAction (0 : Q → k) = 0 := by
  ext v; simp [functionAction_apply, auxiliaryAction_zero_scalar]

/-! ## A module-associated auxiliary tensor type -/

variable (M : ModuleCat.{u + 1} (AuxiliaryPathType k Q))

/-- A second module object over the function ring associated to an object of the original module category. -/
noncomputable abbrev secondaryFunctionModuleObject : ModuleCat.{u + 1} (Q → k) :=
  (restrictScalars (functionRingHom k Q)).obj M

/-- An auxiliary type associated to an object of the displayed module category. -/
def ModuleAuxiliary : Type (u + 1) :=
  TensorProduct (Q → k) (FieldQuiverAuxiliary k Q) (secondaryFunctionModuleObject M)

/-- The additive commutative group structure on the module-associated auxiliary type. -/
noncomputable instance instAddCommGroupModuleAuxiliary : AddCommGroup (ModuleAuxiliary M) :=
  inferInstanceAs
    (AddCommGroup
      (TensorProduct (Q → k) (FieldQuiverAuxiliary k Q) (secondaryFunctionModuleObject M)))

/-- The scalar action of vertex-indexed functions on the module-associated auxiliary type. -/
noncomputable instance instSMulFunctionsModuleAuxiliary : SMul (Q → k) (ModuleAuxiliary M) where
  smul s x := TensorProduct.map (functionAction s) LinearMap.id x

/-- The function action on the module-associated auxiliary type is the tensor-product map induced by the function endomorphism and the identity. -/
theorem moduleAuxiliary_smul_eq_tensorMap (s : Q → k) (x : ModuleAuxiliary M) :
    s • x = TensorProduct.map (functionAction s) LinearMap.id x := rfl

/-- The displayed tensor-product map applies the function endomorphism to the first factor of a pure tensor. -/
theorem tensorMap_functionAction_tmul (s : Q → k) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    TensorProduct.map (functionAction s) LinearMap.id
        (v ⊗ₜ[Q → k] m : ModuleAuxiliary M) =
      functionAction s v ⊗ₜ[Q → k] m := by
  rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

/-- The function-ring module structure on the module-associated auxiliary type. -/
noncomputable instance instModuleFunctionsModuleAuxiliary :
    Module (Q → k) (ModuleAuxiliary M) where
  one_smul x := by
    rw [moduleAuxiliary_smul_eq_tensorMap, functionAction_one, TensorProduct.map_id,
      LinearMap.id_coe, id_eq]
  mul_smul s t x := by
    change TensorProduct.map (functionAction (s * t)) LinearMap.id x =
      TensorProduct.map (functionAction s) LinearMap.id
        (TensorProduct.map (functionAction t) LinearMap.id x)
    rw [functionAction_mul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp]
  smul_zero s := by rw [moduleAuxiliary_smul_eq_tensorMap, map_zero]
  smul_add s x y := by
    rw [moduleAuxiliary_smul_eq_tensorMap, moduleAuxiliary_smul_eq_tensorMap,
      moduleAuxiliary_smul_eq_tensorMap, map_add]
  add_smul s t x := by
    rw [moduleAuxiliary_smul_eq_tensorMap, moduleAuxiliary_smul_eq_tensorMap,
      moduleAuxiliary_smul_eq_tensorMap, functionAction_add, TensorProduct.map_add_left,
      LinearMap.add_apply]
  zero_smul x := by
    rw [moduleAuxiliary_smul_eq_tensorMap, functionAction_zero, TensorProduct.map_zero_left,
      LinearMap.zero_apply]

/-- A module object over the function ring associated to an object of the original module category. -/
noncomputable def functionModuleObject : ModuleCat.{u + 1} (Q → k) :=
  ModuleCat.of (Q → k) (ModuleAuxiliary M)

/-! ## An auxiliary morphism to the original object -/

/-- An auxiliary module-category object associated to a given module-category object. -/
noncomputable abbrev auxiliaryModuleObject : ModuleCat.{u + 1} (AuxiliaryPathType k Q) :=
  functor.obj (secondaryFunctionModuleObject M)

/-- A second auxiliary module-category object associated to a given module-category object. -/
noncomputable abbrev secondaryAuxiliaryModuleObject :
    ModuleCat.{u + 1} (AuxiliaryPathType k Q) :=
  functor.obj (functionModuleObject M)

/-- A morphism from the auxiliary associated module object to the original object. -/
noncomputable def auxiliaryModuleToObject : auxiliaryModuleObject M ⟶ M :=
  tensorHomOfHom (𝟙 (secondaryFunctionModuleObject M))

/-- The auxiliary morphism to the original object is the component of the displayed adjunction counit. -/
theorem auxiliaryModuleToObject_eq_counitApp :
    auxiliaryModuleToObject M = adjunction.counit.app M := by
  rw [auxiliaryModuleToObject, ← Adjunction.homEquiv_symm_id]
  simp only [adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The auxiliary morphism sends a pure tensor to the scalar action of its first factor on the second. -/
theorem auxiliaryModuleToObject_tmul (a : AuxiliaryPathType k Q)
    (m : secondaryFunctionModuleObject M) :
    (auxiliaryModuleToObject M).hom (a ⊗ₜ[Q → k] m) = a • (m : M) := by
  rw [auxiliaryModuleToObject, tensorHomOfHom_tmul]
  rfl

/-! ## An auxiliary comparison morphism -/

/-- A curried additive map from the auxiliary type and the secondary function-module object to the restricted associated module. -/
noncomputable def auxiliaryBiadditiveMap :
    FieldQuiverAuxiliary k Q →+ secondaryFunctionModuleObject M →+
      (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) where
  toFun v :=
    { toFun := fun m => edgeLinearMap v ⊗ₜ[Q → k] m -
        (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
          (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M)
      map_zero' := by simp
      map_add' := fun m m' => by
        simp only [TensorProduct.tmul_add, smul_add]
        abel }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul,
      TensorProduct.add_tmul, TensorProduct.tmul_add, AddMonoidHom.add_apply]
    abel

/-- The auxiliary biadditive map is the difference of the tensor with the displayed image and the corresponding action tensor. -/
theorem auxiliaryBiadditiveMap_apply (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    auxiliaryBiadditiveMap M v m = edgeLinearMap v ⊗ₜ[Q → k] m -
      (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
        (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := rfl

/-- Moving a function scalar between the two arguments of the auxiliary biadditive map does not change its value. -/
theorem auxiliaryBiadditiveMap_smul (s : Q → k) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    auxiliaryBiadditiveMap M (s • v) m = auxiliaryBiadditiveMap M v (s • m) := by
  rw [auxiliaryBiadditiveMap_apply, auxiliaryBiadditiveMap_apply]
  have hv : edgeLinearMap (s • v : FieldQuiverAuxiliary k Q) =
      edgeLinearMap v * functionRingHom k Q s := auxiliary_right_weight_eq_mul s v
  rw [hv]
  have e1 : (edgeLinearMap v * functionRingHom k Q s) ⊗ₜ[Q → k] m =
      edgeLinearMap v ⊗ₜ[Q → k]
        ((s : Q → k) • m : secondaryFunctionModuleObject M) := by
    rw [← smul_eq_mul_image, TensorProduct.smul_tmul]
  have e2 : (edgeLinearMap v * functionRingHom k Q s) • (m : M) =
      edgeLinearMap v • ((s : Q → k) • m : secondaryFunctionModuleObject M) := by
    exact _root_.SemigroupAction.mul_smul
      (edgeLinearMap (show Edge Q →₀ k from v))
      (functionRingHom k Q s) (m : M)
  rw [e1, e2]

/-- An additive homomorphism from the module-associated auxiliary type to the restricted associated module. -/
noncomputable def auxiliaryComparisonAddHom :
    ModuleAuxiliary M →+
      (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  TensorProduct.liftAddHom (auxiliaryBiadditiveMap M) (auxiliaryBiadditiveMap_smul M)

/-- On a pure tensor, the auxiliary additive homomorphism is the difference of the tensor with the displayed image and the corresponding action tensor. -/
@[simp] theorem auxiliaryComparisonAddHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    auxiliaryComparisonAddHom M (v ⊗ₜ[Q → k] m) =
      edgeLinearMap v ⊗ₜ[Q → k] m -
        (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
          (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) :=
  rfl

/-- Tensoring one with the action of the displayed image of a function equals tensoring that image with the same element. -/
theorem one_tmul_smul_eq_tmul (s : Q → k) (y : secondaryFunctionModuleObject M) :
    (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
        ((functionRingHom k Q s • (y : M)) : secondaryFunctionModuleObject M) =
      functionRingHom k Q s ⊗ₜ[Q → k] y := by
  conv_rhs => rw [show functionRingHom k Q s =
    (s : Q → k) • (1 : AuxiliaryPathType k Q) by
      rw [smul_eq_mul_image, one_mul]]
  rw [TensorProduct.smul_tmul]
  rfl

/-- An auxiliary morphism from the function-ring module object to a scalar restriction of the associated module object. -/
noncomputable def auxiliaryComparisonHom :
    functionModuleObject M ⟶
      (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  ModuleCat.ofHom (X := functionModuleObject M)
    (Y := (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M))
    { toFun := fun x => auxiliaryComparisonAddHom M x
      map_add' := fun x y => (auxiliaryComparisonAddHom M).map_add x y
      map_smul' := fun s x => by
        change (auxiliaryComparisonAddHom M (s • x) : auxiliaryModuleObject M) =
          functionRingHom k Q s •
            (auxiliaryComparisonAddHom M x : auxiliaryModuleObject M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul,
              auxiliaryComparisonAddHom_tmul, auxiliaryComparisonAddHom_tmul]
            simp only [functionAction_apply, auxiliary_left_weight_eq_mul]
            rw [smul_sub]
            refine congr_arg₂ (· - ·) ?_ ?_
            · rw [TensorProduct.smul_tmul', smul_eq_mul]
            · rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← one_tmul_smul_eq_tmul]
              congr 1
              exact _root_.SemigroupAction.mul_smul (functionRingHom k Q s)
                (edgeLinearMap (show Edge Q →₀ k from v)) (m : M)
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

/-- The auxiliary comparison morphism sends a pure tensor to the difference of the tensor with the displayed image and the corresponding action tensor. -/
@[simp] theorem auxiliaryComparisonHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    (auxiliaryComparisonHom M).hom (v ⊗ₜ[Q → k] m) =
      edgeLinearMap v ⊗ₜ[Q → k] m -
        (1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
          (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  change auxiliaryComparisonAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [auxiliaryComparisonAddHom_tmul]

/-- An auxiliary morphism from the secondary associated module object to the first. -/
noncomputable def auxiliaryDifferential :
    secondaryAuxiliaryModuleObject M ⟶ auxiliaryModuleObject M :=
  tensorHomOfHom (auxiliaryComparisonHom M)

/-- The auxiliary differential on a nested pure tensor is the difference of the displayed multiplication and action tensors. -/
@[simp] theorem auxiliaryDifferential_tmul (a : AuxiliaryPathType k Q)
    (v : FieldQuiverAuxiliary k Q) (m : secondaryFunctionModuleObject M) :
    (auxiliaryDifferential M).hom
        (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : functionModuleObject M)) =
      (a * edgeLinearMap v) ⊗ₜ[Q → k] m -
        a ⊗ₜ[Q → k]
          (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  rw [auxiliaryDifferential, tensorHomOfHom_tmul, auxiliaryComparisonHom_tmul, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-! ## An auxiliary short complex -/

/-- Composing the auxiliary differential with the morphism to the original object gives zero. -/
theorem auxiliaryDifferential_comp_toObject :
    auxiliaryDifferential M ≫ auxiliaryModuleToObject M = 0 := by
  apply ModuleCat.hom_ext
  ext x
  refine TensorProduct.induction_on x (by simp) (fun a y => ?_)
    (fun p q hp hq => by rw [map_add, map_add, hp, hq])
  change (auxiliaryModuleToObject M).hom
    ((auxiliaryDifferential M).hom (a ⊗ₜ[Q → k] y)) = 0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v m =>
      rw [auxiliaryDifferential_tmul, map_sub, auxiliaryModuleToObject_tmul,
        auxiliaryModuleToObject_tmul]
      apply sub_eq_zero.mpr
      exact _root_.SemigroupAction.mul_smul a
        (edgeLinearMap (show Edge Q →₀ k from v)) (m : M)
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, add_zero]

/-- The auxiliary morphism from the associated module object is an epimorphism. -/
theorem auxiliaryModuleToObject_epi : Epi (auxiliaryModuleToObject M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨(1 : AuxiliaryPathType k Q) ⊗ₜ[Q → k]
    (m : secondaryFunctionModuleObject M), ?_⟩
  rw [auxiliaryModuleToObject_tmul, one_smul]

/-- An auxiliary short complex associated to a module-category object. -/
noncomputable def auxiliaryShortComplex :
    ShortComplex (ModuleCat.{u + 1} (AuxiliaryPathType k Q)) :=
  ShortComplex.mk (auxiliaryDifferential M) (auxiliaryModuleToObject M)
    (auxiliaryDifferential_comp_toObject M)

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
