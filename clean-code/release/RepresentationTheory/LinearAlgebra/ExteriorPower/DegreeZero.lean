/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Degree zero and basis independence for a symmetric-algebra complex

This module defines
`RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero`, its scalar actions, and
the augmentation map
`RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero`. It also supplies
the exterior-power basis and proves that the basis-indexed differential and resulting complex from
`RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex` are basis-independent. The
generator formula uses
`RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction_unrenderedAux`.
-/

universe u v w w'

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-! ### The degree-zero module -/

/-- The degree-zero exterior-power module over a commutative ring. -/
def degreeZero (k : Type u) [CommRing k] (V : Type v) [AddCommGroup V] [Module k V] :
    Type max u v := ULift.{v} k

namespace degreeZero

/-- The additive commutative group structure on the degree-zero module. -/
instance addCommGroup : AddCommGroup (degreeZero k V) :=
  inferInstanceAs (AddCommGroup (ULift.{v} k))

/-- The base-ring module structure on the degree-zero module. -/
instance instModule : Module k (degreeZero k V) := inferInstanceAs (Module k (ULift.{v} k))

/-- The symmetric-algebra module structure on the degree-zero module. -/
noncomputable instance symmetricAlgebraModule : Module (SymmetricAlgebra k V) (degreeZero k V) :=
  Module.compHom (degreeZero k V)
    (SymmetricAlgebra.algebraMapInv (R := k) (M := V)).toRingHom

variable (k V) in
/-- A linear equivalence from the degree-zero module to the base ring. -/
def equivBaseRing : degreeZero k V ≃ₗ[k] k := ULift.moduleEquiv

/-- The base-ring equivalence sends scalar multiplication to multiplication after applying the
inverse algebra map. -/
@[simp]
theorem equivBaseRing_smul (s : SymmetricAlgebra k V) (x : degreeZero k V) :
    equivBaseRing k V (s • x) = SymmetricAlgebra.algebraMapInv s * equivBaseRing k V x :=
  rfl

end degreeZero

/-! ### The tensor map to degree zero -/

variable (k V) in
/-- A symmetric-algebra-linear map to the degree-zero module. -/
noncomputable def symmetricAlgebraToDegreeZero :
    SymmetricAlgebra k V →ₗ[SymmetricAlgebra k V] degreeZero k V where
  toFun s := (degreeZero.equivBaseRing k V).symm (SymmetricAlgebra.algebraMapInv s)
  map_add' s t := by simp
  map_smul' s t := by
    apply (degreeZero.equivBaseRing k V).injective
    simp [smul_eq_mul]

/-- Applying the base-ring equivalence to the symmetric-algebra map gives the inverse algebra
map. -/
@[simp]
theorem equivBaseRing_symmetricAlgebraToDegreeZero (s : SymmetricAlgebra k V) :
    degreeZero.equivBaseRing k V (symmetricAlgebraToDegreeZero k V s) =
      SymmetricAlgebra.algebraMapInv s :=
  (degreeZero.equivBaseRing k V).apply_symm_apply _

variable (k V) in
/-- A symmetric-algebra-linear map from the tensor product with the degree-zero exterior power. -/
noncomputable def tensorToDegreeZero :
    RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V 0
      →ₗ[SymmetricAlgebra k V] degreeZero k V :=
  (symmetricAlgebraToDegreeZero k V).comp
    ((TensorProduct.AlgebraTensorModule.rid k (SymmetricAlgebra k V)
        (SymmetricAlgebra k V)).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := SymmetricAlgebra k V))
        (exteriorPower.zeroEquiv k V).toLinearMap))

/-- The base-ring equivalence evaluates the tensor map on a pure tensor as scalar multiplication by
the inverse algebra image. -/
@[simp]
theorem equivBaseRing_tensorToDegreeZero_tmul (s : SymmetricAlgebra k V) (w : ⋀[k]^0 V) :
    degreeZero.equivBaseRing k V (tensorToDegreeZero k V (s ⊗ₜ[k] w)) =
      exteriorPower.zeroEquiv k V w • SymmetricAlgebra.algebraMapInv s := by
  simp [tensorToDegreeZero, map_smul]

/-- The tensor map to the degree-zero module is surjective. -/
theorem tensorToDegreeZero_surjective : Function.Surjective (tensorToDegreeZero k V) := by
  intro y
  refine ⟨(algebraMap k (SymmetricAlgebra k V) (degreeZero.equivBaseRing k V y)) ⊗ₜ[k]
    (exteriorPower.zeroEquiv k V).symm 1, ?_⟩
  apply (degreeZero.equivBaseRing k V).injective
  simp

/-- Composing the tensor map with the degree-zero basis-indexed map is zero. -/
theorem tensorToDegreeZero_comp_basisMap_zero
    {κ : Type w} [Fintype κ] (b : Module.Basis κ k V) :
    (tensorToDegreeZero k V).comp
      (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
        b 0) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
      apply (degreeZero.equivBaseRing k V).injective
      rw [RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential_tmul]
      simp [SymmetricAlgebra.algebraMapInv_ι]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-! ### Freeness of the terms -/

variable (k V) in
/-- A basis for an exterior-power module indexed by subsets of a fixed cardinality. -/
noncomputable def exteriorPowerBasis
    {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (i : ℕ) :
    Module.Basis (Set.powersetCard I i) (SymmetricAlgebra k V)
      (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
        k V i) :=
  (b.exteriorPower i).baseChange (SymmetricAlgebra k V)

/-- Each vector of the exterior-power basis is the pure tensor of one with the corresponding
exterior-power basis vector. -/
@[simp]
theorem exteriorPowerBasis_apply
    {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (i : ℕ)
    (s : Set.powersetCard I i) :
    exteriorPowerBasis k V b i s = 1 ⊗ₜ[k] (b.exteriorPower i) s :=
  Module.Basis.baseChange_apply _ _ _

/-- Each exterior-power module is free when the original module is free. -/
instance exteriorPower_moduleFree [Module.Free k V] (i : ℕ) :
    Module.Free (SymmetricAlgebra k V)
      (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
        k V i) := by
  obtain ⟨⟨I, c⟩⟩ := Module.Free.exists_basis (R := k) (M := ⋀[k]^i V)
  exact Module.Free.of_basis (c.baseChange (SymmetricAlgebra k V))

/-- Each exterior-power module is projective when the original module is free. -/
instance exteriorPower_moduleProjective [Module.Free k V] (i : ℕ) :
    Module.Projective (SymmetricAlgebra k V)
      (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
        k V i) :=
  Module.Projective.of_free

/-! ### Basis independence -/

/-- Two linear maps from an exterior-power module are equal when they agree on all displayed
exterior-power generators. -/
theorem linearMap_ext_on_exteriorPowerGenerators
    {N : Type*} [AddCommGroup N] [Module (SymmetricAlgebra k V) N] {n : ℕ}
    {f g : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
      k V n →ₗ[SymmetricAlgebra k V] N}
    (h : ∀ v : Fin n → V,
      f (1 ⊗ₜ[k] exteriorPower.ιMulti k n v) = g (1 ⊗ₜ[k] exteriorPower.ιMulti k n v)) :
    f = g := by
  have key : ∀ w : ⋀[k]^n V, f (1 ⊗ₜ[k] w) = g (1 ⊗ₜ[k] w) := by
    intro w
    have hw : w ∈ (⊤ : Submodule k (⋀[k]^n V)) := trivial
    rw [← exteriorPower.ιMulti_span k n] at hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact h v
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | smul c x _ hx =>
        have hc : (1 : SymmetricAlgebra k V) ⊗ₜ[k] (c • x)
            = (algebraMap k (SymmetricAlgebra k V) c) •
              ((1 : SymmetricAlgebra k V) ⊗ₜ[k] x) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
          simp [Algebra.algebraMap_eq_smul_one]
        rw [hc, map_smul, map_smul, hx]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
      have hs : s ⊗ₜ[k] w = s • ((1 : SymmetricAlgebra k V) ⊗ₜ[k] w) := by
        rw [TensorProduct.smul_tmul']; simp
      rw [hs, map_smul, map_smul, key]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {κ : Type w} [Fintype κ]

/-- A theorem whose formal type could not be rendered in the packet. -/
theorem basisIndexedMap_unrendered
    (b : Module.Basis κ k V) (i : ℕ) (v : Fin (i + 1) → V) :
    RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
        b i
        (1 ⊗ₜ[k] exteriorPower.ιMulti k (i + 1) v) =
      ∑ j : Fin (i + 1), ((-1 : k) ^ ((j : ℕ) + 1)) •
        (SymmetricAlgebra.ι k V (v j) ⊗ₜ[k] exteriorPower.ιMulti k i (v ∘ j.succAbove)) := by
  rw [RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential_tmul]
  simp only [mul_one,
    RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction_unrenderedAux,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The basis is eliminated here: `v j` is reassembled from its coordinates,
  -- `∑ₐ b.coord a (v j) • b a = v j`.
  have hb : ∑ a : κ, (b.coord a) (v j) • SymmetricAlgebra.ι k V (b a)
      = SymmetricAlgebra.ι k V (v j) := by
    simp only [← map_smul, ← map_sum]
    congr 1
    simp [b.sum_repr (v j)]
  simp only [mul_smul, ← Finset.smul_sum]
  congr 1
  rw [← hb, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun a _ => (TensorProduct.smul_tmul' _ _ _).symm

/-- The basis-indexed maps associated to two finite bases agree at every natural-number index. -/
theorem basisIndexedMap_eq
    {κ' : Type w'} [Fintype κ'] (b : Module.Basis κ k V)
    (b' : Module.Basis κ' k V) (i : ℕ) :
    RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
        b i =
      RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
        b' i :=
  linearMap_ext_on_exteriorPowerGenerators fun v => by
    rw [basisIndexedMap_unrendered, basisIndexedMap_unrendered]

/-- The displayed map has equal values for any two finite bases. -/
theorem basisIndependentMap_eq
    {κ' : Type w'} [Fintype κ'] (b : Module.Basis κ k V) (b' : Module.Basis κ' k V) :
    RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b =
      RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b' := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp only [RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_d,
    basisIndexedMap_eq b b' j]
  simp

end RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero
