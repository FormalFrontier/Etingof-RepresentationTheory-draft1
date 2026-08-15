/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.PathDegreeDecomposition
import RepresentationTheory.ModuleTensorAuxiliary
import Mathlib.LinearAlgebra.DirectSum.Finsupp

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-- Right multiplication by the element indexed by the length-zero path at i returns the indexed element when its displayed vertex is i, and zero otherwise. -/
theorem indexedElement_mul_nilPath (i : Q) (x : Quiver.BundledPath Q) :
    (ofPath x : PathAlgebra k Q) * ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)
      = if x.2.1 = i then ofPath x else 0 := by
  obtain ⟨a, b, p⟩ := x
  rw [pathElement_mul_pathElement, mulPath_pathVertex]
  split_ifs with h
  · rfl
  · rfl

/-- Multiplying the element indexed by x by the image of s scales it by s at the displayed vertex of x. -/
theorem indexedElement_mul_vertexFunction (x : Quiver.BundledPath Q) (s : Q → k) :
    (ofPath x : PathAlgebra k Q) * functionRingHom k Q s = s x.2.1 • ofPath x := by
  have hsingle : ∀ i : Q, (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (s i)
        : PathAlgebra k Q) = s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [functionRingHom_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.mul_sum]
  have hterm : ∀ i : Q,
      (ofPath x : PathAlgebra k Q) * (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q))
        = if x.2.1 = i then s i • ofPath (k := k) x else 0 := by
    intro i
    rw [RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_smul,
      indexedElement_mul_nilPath]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq Finset.univ x.2.1,
    if_pos (Finset.mem_univ _)]

/-- Multiplying a singleton-supported element by a vertex scalar function scales its coefficient at the displayed vertex. -/
theorem single_mul_vertexFunction (x : Quiver.BundledPath Q) (c : k) (s : Q → k) :
    (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
        (Finsupp.single x c) (functionRingHom k Q s))
      = s x.2.1 • (Finsupp.single x c : PathAlgebra k Q) := by
  rw [show (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x from by
      rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one],
    smul_mul, indexedElement_mul_vertexFunction, smul_comm]

/-- Each natural-number component commutes with multiplication by a vertex-indexed scalar function. -/
theorem degreeComponent_mul_vertexFunction (n : ℕ) (a : PathAlgebra k Q) (s : Q → k) :
    degreeProjection k Q n ((a * functionRingHom k Q s : PathAlgebra k Q))
      = degreeProjection k Q n a * functionRingHom k Q s := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, map_add, map_add, add_mul, hf, hg]
  | single x c =>
    rw [single_mul_vertexFunction, map_smul, degreeProjection_single]
    split_ifs with h
    · exact (single_mul_vertexFunction x c s).symm
    · rw [smul_zero, zero_mul]

/-- The degree-data map turns multiplication by a vertex-indexed scalar function into scalar multiplication. -/
theorem degreeData_mul_vertexFunction (a : PathAlgebra k Q) (s : Q → k) :
    pathDegreeDecomposition k Q ((a * functionRingHom k Q s : PathAlgebra k Q))
      = s • pathDegreeDecomposition k Q a := by
  ext n
  rw [Finsupp.smul_apply, ← degreeProjection_apply, ← degreeProjection_apply, smul_eq_mul_image,
    degreeComponent_mul_vertexFunction]

variable (k Q) in
/-- Maps an algebra element to finitely supported natural-number degree data. -/
noncomputable def degreeData : PathAlgebra k Q →ₗ[Q → k] (ℕ →₀ PathAlgebra k Q) where
  toFun := pathDegreeDecomposition k Q
  map_add' := map_add _
  map_smul' s a := by
    change pathDegreeDecomposition k Q (s • a) = s • pathDegreeDecomposition k Q a
    rw [smul_eq_mul_image, degreeData_mul_vertexFunction]

/-- The degree-data map agrees pointwise with the comparison map. -/
@[simp] theorem degreeData_eq_comparisonMap (a : PathAlgebra k Q) :
    degreeData k Q a = pathDegreeDecomposition k Q a := rfl

variable (k Q) in
/-- Builds an algebra element from finitely supported natural-number degree data. -/
noncomputable def ofDegreeData : (ℕ →₀ PathAlgebra k Q) →ₗ[Q → k] PathAlgebra k Q where
  toFun := sumDegreeComponents k Q
  map_add' := map_add _
  map_smul' s F := by
    change sumDegreeComponents k Q (s • F) = s • sumDegreeComponents k Q F
    induction F using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, smul_add]
    | single n a => rw [Finsupp.smul_single, sumDegreeComponents_single, sumDegreeComponents_single]

/-- The reconstruction map agrees pointwise with the comparison map. -/
@[simp] theorem ofDegreeData_eq_comparisonMap (F : ℕ →₀ PathAlgebra k Q) :
    ofDegreeData k Q F = sumDegreeComponents k Q F := rfl

/-- Reconstructing after taking degree data is the identity. -/
theorem ofDegreeData_comp_degreeData :
    (ofDegreeData k Q).comp (degreeData k Q) = LinearMap.id := by
  ext a
  simp only [LinearMap.comp_apply, degreeData_eq_comparisonMap, ofDegreeData_eq_comparisonMap,
    sumDegreeComponents_decomposition, LinearMap.id_coe, id_eq]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- The component type attached to a module. -/
abbrev componentType : Type (u + 1) :=
  TensorProduct (Q → k) (PathAlgebra k Q) (secondaryFunctionModuleObject M)

/-- Maps an element to finitely supported natural-number component data. -/
noncomputable def componentData :
    componentType M →ₗ[Q → k] (ℕ →₀ componentType M) :=
  (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) (secondaryFunctionModuleObject M) ℕ).toLinearMap.comp
    (TensorProduct.map (degreeData k Q) LinearMap.id)

/-- The nth component of a pure tensor is the tensor of the nth image of its first factor with its second factor. -/
@[simp] theorem componentData_tmul_apply (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) (n : ℕ) :
    componentData M (a ⊗ₜ[Q → k] m) n
      = (degreeProjection k Q n a) ⊗ₜ[Q → k] (m : M) := by
  simp only [componentData, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, degreeData_eq_comparisonMap, TensorProduct.finsuppLeft_apply_tmul_apply,
    degreeProjection_apply]

/-- The component-data map is injective. -/
theorem componentData_injective : Function.Injective (componentData M) := by
  have hleft : ∀ x : componentType M,
      (TensorProduct.map (ofDegreeData k Q) (LinearMap.id (R := Q → k) (M := secondaryFunctionModuleObject M)))
        (TensorProduct.map (degreeData k Q) LinearMap.id x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ofDegreeData_comp_degreeData,
      LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  intro x y hxy
  refine Function.LeftInverse.injective hleft ?_
  exact (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) (secondaryFunctionModuleObject M) ℕ).injective
    hxy

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
