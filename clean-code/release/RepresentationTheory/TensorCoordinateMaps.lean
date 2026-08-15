/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Path
import RepresentationTheory.Grading

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- Computes a component of the product of two specified generators, with support at the successor of the first generator's index. -/
theorem component_mul_generators (m : ℕ) (x : Quiver.BundledPath Q) (y : Edge Q) :
    degreeProjection k Q m ((ofPath x : PathAlgebra k Q) * ofEdge y)
      = if pathDegree x + 1 = m then (ofPath x : PathAlgebra k Q) * ofEdge y else 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, e⟩ := y
  rw [ofEdge, Edge.toPath, pathElement_mul_pathElement]
  by_cases hbc : b = c
  · subst hbc
    rw [mulPath_of_composable, degreeProjection_single, pathDegree_eq_length, Quiver.Path.length_comp,
      Quiver.Path.length_toPath, pathDegree_eq_length]
  · rw [mulPath_of_not_composable _ _ hbc, map_zero, ite_self]

/-- A successor component of a product with an embedded finitely supported element equals the preceding component times that element. -/
theorem component_succ_mul (n : ℕ) (a : PathAlgebra k Q) (v : Edge Q →₀ k) :
    degreeProjection k Q (n + 1) (a * edgeLinearMap v) = degreeProjection k Q n a * edgeLinearMap v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, mul_add, map_add, hv, hw, mul_add]
  | single y d =>
    rw [edgeLinearMap_single]
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, map_add, add_mul, hf, hg]
    | single x c =>
      have hsx : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
        rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsx, smul_mul, RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_smul,
        map_smul, map_smul,
        component_mul_generators]
      simp only [add_left_inj]
      rw [map_smul, show (degreeProjection k Q n) (ofPath x)
          = if pathDegree x = n then (ofPath x : PathAlgebra k Q) else 0 from by
            rw [ofPath, degreeProjection_single]]
      split_ifs with h
      · rw [smul_mul, RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_smul]
      · simp

/-- The zeroth component of a product with an embedded finitely supported element vanishes. -/
theorem component_zero_mul (a : PathAlgebra k Q) (v : Edge Q →₀ k) :
    degreeProjection k Q 0 (a * edgeLinearMap v) = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, mul_add, map_add, hv, hw, add_zero]
  | single y d =>
    rw [edgeLinearMap_single]
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, hf, hg, add_zero]
    | single x c =>
      have hsx : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
        rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsx, smul_mul, RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_smul,
        map_smul, map_smul, component_mul_generators,
        if_neg (Nat.succ_ne_zero _), smul_zero, smul_zero]

section Induced

variable [Fintype Q]

variable (N : ModuleCat.{u + 1} (Q → k))

/-- The linear map from a tensor product to finitely supported tensor-valued sequences. -/
noncomputable def tensorToFinsupp :
    TensorProduct (Q → k) (PathAlgebra k Q) N →ₗ[Q → k]
      (ℕ →₀ TensorProduct (Q → k) (PathAlgebra k Q) N) :=
  (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) N ℕ).toLinearMap.comp
    (TensorProduct.map (degreeData k Q) LinearMap.id)

/-- Evaluating the image of a pure tensor at an index applies the corresponding component map to
its first factor. -/
@[simp] theorem tensorToFinsupp_tmul_apply (a : PathAlgebra k Q) (m : N) (n : ℕ) :
    tensorToFinsupp N (a ⊗ₜ[Q → k] m) n = (degreeProjection k Q n a) ⊗ₜ[Q → k] m := by
  simp only [tensorToFinsupp, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, degreeData_eq_comparisonMap, TensorProduct.finsuppLeft_apply_tmul_apply,
    degreeProjection_apply]

/-- The tensor-to-finitely-supported-sequence map is injective. -/
theorem tensorToFinsupp_injective : Function.Injective (tensorToFinsupp N) := by
  have hleft : ∀ x : TensorProduct (Q → k) (PathAlgebra k Q) N,
      (TensorProduct.map (ofDegreeData k Q) (LinearMap.id (R := Q → k) (M := N)))
        (TensorProduct.map (degreeData k Q) LinearMap.id x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ofDegreeData_comp_degreeData,
      LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  intro x y hxy
  refine Function.LeftInverse.injective hleft ?_
  exact (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) N ℕ).injective hxy

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- Computes a successor difference coordinate on a nested pure tensor as a difference of two pure tensors. -/
theorem difference_tmul_succ_apply (a : PathAlgebra k Q) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) (n : ℕ) :
    componentData M ((auxiliaryDifferential M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : functionModuleObject M))) (n + 1)
      = (degreeProjection k Q n a * edgeLinearMap v) ⊗ₜ[Q → k] (m : M)
        - (degreeProjection k Q (n + 1) a) ⊗ₜ[Q → k]
            (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  rw [auxiliaryDifferential_tmul, map_sub, Finsupp.sub_apply, componentData_tmul_apply, componentData_tmul_apply,
    component_succ_mul]

/-- Computes the zeroth difference coordinate on a nested pure tensor as a negated pure tensor. -/
theorem difference_tmul_zero_apply (a : PathAlgebra k Q) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    componentData M ((auxiliaryDifferential M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : functionModuleObject M))) 0
      = - (degreeProjection k Q 0 a) ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  rw [auxiliaryDifferential_tmul, map_sub, Finsupp.sub_apply, componentData_tmul_apply, componentData_tmul_apply,
    component_zero_mul, TensorProduct.zero_tmul, zero_sub]

/-- The curried additive map sending two inputs to their pure tensor after embedding the first. -/
noncomputable def firstFactorEmbeddingBilinear :
    FieldQuiverAuxiliary k Q →+ secondaryFunctionModuleObject M →+ (restrictScalars (functionRingHom k Q)).obj
      (auxiliaryModuleObject M) where
  toFun v :=
    { toFun := fun m => edgeLinearMap v ⊗ₜ[Q → k] m
      map_zero' := by simp
      map_add' := fun m m' => by rw [TensorProduct.tmul_add] }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.add_tmul,
      AddMonoidHom.add_apply]

/-- The curried embedding map evaluates to the pure tensor with embedded first input. -/
theorem firstFactorEmbeddingBilinear_apply (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    firstFactorEmbeddingBilinear M v m = edgeLinearMap v ⊗ₜ[Q → k] m := rfl

/-- Scaling the first input of the curried embedding map agrees with scaling its second input. -/
theorem firstFactorEmbeddingBilinear_smul (s : Q → k) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    firstFactorEmbeddingBilinear M (s • v) m = firstFactorEmbeddingBilinear M v (s • m) := by
  rw [firstFactorEmbeddingBilinear_apply, firstFactorEmbeddingBilinear_apply]
  have hv : edgeLinearMap (s • v : FieldQuiverAuxiliary k Q)
      = edgeLinearMap v * functionRingHom k Q s := auxiliary_right_weight_eq_mul s v
  rw [hv, ← smul_eq_mul_image, TensorProduct.smul_tmul]

/-- The additive map into the restricted-scalar target that embeds the first tensor factor. -/
noncomputable def firstFactorEmbeddingAddHom :
    ModuleAuxiliary M →+ (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  TensorProduct.liftAddHom (firstFactorEmbeddingBilinear M) (firstFactorEmbeddingBilinear_smul M)

/-- The restricted additive multiplication map sends a pure tensor to the tensor with its first
factor embedded. -/
@[simp] theorem firstFactorEmbeddingAddHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    firstFactorEmbeddingAddHom M (v ⊗ₜ[Q → k] m) = edgeLinearMap v ⊗ₜ[Q → k] m := rfl

/-- A quiver morphism into the restricted-scalar target that embeds the first tensor factor. -/
noncomputable def firstFactorEmbeddingHom :
    functionModuleObject M ⟶ (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  ModuleCat.ofHom (X := functionModuleObject M)
    (Y := (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M))
    { toFun := fun x => firstFactorEmbeddingAddHom M x
      map_add' := fun x y => (firstFactorEmbeddingAddHom M).map_add x y
      map_smul' := fun s x => by
        change (firstFactorEmbeddingAddHom M (s • x) : auxiliaryModuleObject M)
          = functionRingHom k Q s • (firstFactorEmbeddingAddHom M x : auxiliaryModuleObject M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, firstFactorEmbeddingAddHom_tmul, firstFactorEmbeddingAddHom_tmul]
            simp only [functionAction_apply, auxiliary_left_weight_eq_mul]
            rw [TensorProduct.smul_tmul', smul_eq_mul]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

/-- The restricted embedding morphism sends a pure tensor to the tensor with embedded first
factor. -/
@[simp] theorem firstFactorEmbeddingHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    (firstFactorEmbeddingHom M).hom (v ⊗ₜ[Q → k] m) = edgeLinearMap v ⊗ₜ[Q → k] m := by
  change firstFactorEmbeddingAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [firstFactorEmbeddingAddHom_tmul]

/-- The curried additive map sending two inputs to one tensored with the action on the second input. -/
noncomputable def actionRestrictedBilinear :
    FieldQuiverAuxiliary k Q →+ secondaryFunctionModuleObject M →+ (restrictScalars (functionRingHom k Q)).obj
      (auxiliaryModuleObject M) where
  toFun v :=
    { toFun := fun m =>
        (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M)
      map_zero' := by simp
      map_add' := fun m m' => by simp only [smul_add, TensorProduct.tmul_add] }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul, TensorProduct.tmul_add,
      AddMonoidHom.add_apply]

/-- The curried action map evaluates to one tensored with the acted-on second input. -/
theorem actionRestrictedBilinear_apply (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    actionRestrictedBilinear M v m
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := rfl

/-- Scaling the first input of the curried action map agrees with scaling its second input. -/
theorem actionRestrictedBilinear_smul (s : Q → k) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    actionRestrictedBilinear M (s • v) m = actionRestrictedBilinear M v (s • m) := by
  rw [actionRestrictedBilinear_apply, actionRestrictedBilinear_apply]
  have hv : edgeLinearMap (s • v : FieldQuiverAuxiliary k Q)
      = edgeLinearMap v * functionRingHom k Q s := auxiliary_right_weight_eq_mul s v
  have e2 : (edgeLinearMap v * functionRingHom k Q s) • (m : M)
      = edgeLinearMap v • ((s : Q → k) • m : secondaryFunctionModuleObject M) := by
    rw [_root_.SemigroupAction.mul_smul]; rfl
  rw [hv, e2]

/-- The additive map into the restricted-scalar target associated with action on the module factor. -/
noncomputable def actionRestrictedAddHom :
    ModuleAuxiliary M →+ (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  TensorProduct.liftAddHom (actionRestrictedBilinear M) (actionRestrictedBilinear_smul M)

/-- The restricted additive action map sends a pure tensor to one tensored with the acted-on module
element. -/
@[simp] theorem actionRestrictedAddHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    actionRestrictedAddHom M (v ⊗ₜ[Q → k] m)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := rfl

/-- A quiver morphism into the restricted-scalar target using the first input's action on the module factor. -/
noncomputable def actionRestrictedHom :
    functionModuleObject M ⟶ (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M) :=
  ModuleCat.ofHom (X := functionModuleObject M)
    (Y := (restrictScalars (functionRingHom k Q)).obj (auxiliaryModuleObject M))
    { toFun := fun x => actionRestrictedAddHom M x
      map_add' := fun x y => (actionRestrictedAddHom M).map_add x y
      map_smul' := fun s x => by
        change (actionRestrictedAddHom M (s • x) : auxiliaryModuleObject M)
          = functionRingHom k Q s • (actionRestrictedAddHom M x : auxiliaryModuleObject M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, actionRestrictedAddHom_tmul, actionRestrictedAddHom_tmul]
            simp only [functionAction_apply, auxiliary_left_weight_eq_mul]
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← one_tmul_smul_eq_tmul]
            congr 1
            exact _root_.SemigroupAction.mul_smul _ _ _
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

/-- The restricted action morphism sends a pure tensor to one tensored with the acted-on module
factor. -/
@[simp] theorem actionRestrictedHom_tmul (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    (actionRestrictedHom M).hom (v ⊗ₜ[Q → k] m)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  change actionRestrictedAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [actionRestrictedAddHom_tmul]

/-- The quiver morphism from the tensor construction to its target induced by multiplication of tensor factors. -/
noncomputable def multiplicationHom : secondaryAuxiliaryModuleObject M ⟶ auxiliaryModuleObject M :=
  tensorHomOfHom (firstFactorEmbeddingHom M)

/-- The multiplication morphism sends a nested pure tensor to the pure tensor obtained by
multiplying its first two factors. -/
@[simp] theorem multiplicationHom_tmul (a : PathAlgebra k Q) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    (multiplicationHom M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : functionModuleObject M))
      = (a * edgeLinearMap v) ⊗ₜ[Q → k] (m : M) := by
  rw [multiplicationHom, tensorHomOfHom_tmul, firstFactorEmbeddingHom_tmul, TensorProduct.smul_tmul', smul_eq_mul]

/-- The quiver morphism from the tensor construction to its target induced by the scalar action on the module factor. -/
noncomputable def actionHom : secondaryAuxiliaryModuleObject M ⟶ auxiliaryModuleObject M :=
  tensorHomOfHom (actionRestrictedHom M)

/-- The action morphism sends a nested pure tensor to the pure tensor obtained by acting on its
module factor. -/
@[simp] theorem actionHom_tmul (a : PathAlgebra k Q) (v : FieldQuiverAuxiliary k Q)
    (m : secondaryFunctionModuleObject M) :
    (actionHom M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : functionModuleObject M))
      = a ⊗ₜ[Q → k] (edgeLinearMap v • (m : M) : secondaryFunctionModuleObject M) := by
  rw [actionHom, tensorHomOfHom_tmul, actionRestrictedHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The difference morphism is pointwise the multiplication morphism minus the action morphism. -/
theorem difference_apply (x : secondaryAuxiliaryModuleObject M) :
    (auxiliaryDifferential M).hom x = (multiplicationHom M).hom x - (actionHom M).hom x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m => rw [auxiliaryDifferential_tmul, multiplicationHom_tmul, actionHom_tmul]
      | add y z hy hz =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz]; abel
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

/-- The successor coordinate of the difference morphism is the multiplication image at an index minus the action image at its successor. -/
theorem difference_succ_apply (s : secondaryAuxiliaryModuleObject M) (n : ℕ) :
    componentData M ((auxiliaryDifferential M).hom s) (n + 1)
      = (multiplicationHom M).hom (tensorToFinsupp (functionModuleObject M) s n)
        - (actionHom M).hom (tensorToFinsupp (functionModuleObject M) s (n + 1)) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m =>
          rw [difference_tmul_succ_apply, tensorToFinsupp_tmul_apply, tensorToFinsupp_tmul_apply,
            multiplicationHom_tmul, actionHom_tmul]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hy, hz]; abel
  | add s t hs ht =>
      simp only [map_add, Finsupp.add_apply, hs, ht]; abel

/-- The zeroth coordinate of the difference morphism is the negation of the zeroth action image. -/
theorem difference_zero_apply (s : secondaryAuxiliaryModuleObject M) :
    componentData M ((auxiliaryDifferential M).hom s) 0
      = - (actionHom M).hom (tensorToFinsupp (functionModuleObject M) s 0) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m =>
          rw [difference_tmul_zero_apply, tensorToFinsupp_tmul_apply, actionHom_tmul]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hy, hz]; abel
  | add s t hs ht =>
      simp only [map_add, Finsupp.add_apply, hs, ht]; abel

/-- Constructs a sequence supported at one index whose image is the tensor of a single vertex coefficient with a module element. -/
theorem exists_supported_preimage_single (x : Quiver.BundledPath Q) (c : k) {n : ℕ}
    (hx : pathDegree x = n + 1) (m : secondaryFunctionModuleObject M) :
    ∃ η : secondaryAuxiliaryModuleObject M,
      tensorToFinsupp (functionModuleObject M) η n = η ∧
      (∀ j, j ≠ n → tensorToFinsupp (functionModuleObject M) η j = 0) ∧
      (multiplicationHom M).hom η
        = ((Finsupp.single x c : PathAlgebra k Q) ⊗ₜ[Q → k] (m : M) : componentType M) := by
  obtain ⟨a, cc, q⟩ := x
  rw [pathDegree_eq_length] at hx
  obtain ⟨b, p, e, hcomp, hlen⟩ := exists_factorization_of_length_succ (k := k) q hx
  have hlp : degreeProjection k Q n (ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q))
      = ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) := by
    rw [ofPath, degreeProjection_single, pathDegree_eq_length, hlen, if_pos rfl]
  have hlp0 : ∀ j, j ≠ n →
      degreeProjection k Q j (ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q)) = 0 := by
    intro j hj
    rw [ofPath, degreeProjection_single, pathDegree_eq_length, hlen, if_neg (fun h => hj h.symm)]
  refine ⟨(c • ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q)) ⊗ₜ[Q → k]
      ((Finsupp.single (⟨b, cc, e⟩ : Edge Q) 1 : FieldQuiverAuxiliary k Q)
        ⊗ₜ[Q → k] m : functionModuleObject M), ?_, ?_, ?_⟩
  · rw [tensorToFinsupp_tmul_apply, map_smul, hlp]
  · intro j hj
    rw [tensorToFinsupp_tmul_apply, map_smul, hlp0 j hj, smul_zero, TensorProduct.zero_tmul]
  · have hmul : (c • ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q))
        * edgeLinearMap (Finsupp.single (⟨b, cc, e⟩ : Edge Q) 1 : FieldQuiverAuxiliary k Q)
        = (Finsupp.single (⟨a, cc, q⟩ : Quiver.BundledPath Q) c : PathAlgebra k Q) := by
      rw [edgeLinearMap_single, one_smul, smul_mul_assoc, ← hcomp, ofPath, Finsupp.smul_single,
        smul_eq_mul, mul_one]
    rw [multiplicationHom_tmul, hmul]

/-- Constructs a sequence supported at a chosen index whose image is the next coordinate of the given element. -/
theorem exists_supported_preimage_succ (y : auxiliaryModuleObject M) (n : ℕ) :
    ∃ η : secondaryAuxiliaryModuleObject M,
      tensorToFinsupp (functionModuleObject M) η n = η ∧
      (∀ j, j ≠ n → tensorToFinsupp (functionModuleObject M) η j = 0) ∧
      (multiplicationHom M).hom η = componentData M y (n + 1) := by
  let G : componentType M → Prop := fun z =>
    ∃ η : secondaryAuxiliaryModuleObject M,
      tensorToFinsupp (functionModuleObject M) η n = η ∧
      (∀ j, j ≠ n → tensorToFinsupp (functionModuleObject M) η j = 0) ∧
      (multiplicationHom M).hom η = z
  have hzero : G 0 := ⟨0, by simp, by simp, by simp⟩
  have hadd : ∀ z₁ z₂ : componentType M, G z₁ → G z₂ → G (z₁ + z₂) := by
    rintro z₁ z₂ ⟨η₁, h1n, h1j, h1⟩ ⟨η₂, h2n, h2j, h2⟩
    refine ⟨η₁ + η₂, ?_, ?_, ?_⟩
    · rw [map_add, Finsupp.add_apply, h1n, h2n]
    · intro j hj; rw [map_add, Finsupp.add_apply, h1j j hj, h2j j hj, add_zero]
    · rw [map_add, h1, h2]
  suffices H : ∀ (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M),
      G (degreeProjection k Q (n + 1) a ⊗ₜ[Q → k] (m : M)) by
    induction y using TensorProduct.induction_on with
    | zero =>
        have h0 : componentData M (0 : auxiliaryModuleObject M) (n + 1) = 0 := by simp
        rw [h0]; exact hzero
    | tmul a m => rw [componentData_tmul_apply]; exact H a m
    | add y₁ y₂ hy₁ hy₂ =>
        have hsum : componentData M (y₁ + y₂) (n + 1)
            = componentData M y₁ (n + 1) + componentData M y₂ (n + 1) := by
          rw [LinearMap.map_add, Finsupp.add_apply]
        rw [hsum]; exact hadd _ _ hy₁ hy₂
  intro a m
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero, TensorProduct.zero_tmul]; exact hzero
  | add f g hf hg => rw [map_add, TensorProduct.add_tmul]; exact hadd _ _ hf hg
  | single x c =>
      rw [degreeProjection_single]
      split_ifs with hx
      · exact exists_supported_preimage_single M x c hx m
      · rw [TensorProduct.zero_tmul]; exact hzero

end Induced

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
