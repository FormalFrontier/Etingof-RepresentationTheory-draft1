/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.GroupTheory.ConjugacyClassBounds
import RepresentationTheory.AuxiliaryDecompositionData
import RepresentationTheory.CategoryTheory.FullFunctorConsequences
import RepresentationTheory.RingTheory.AuxiliaryTypeInvariants

open CategoryTheory
open scoped TensorProduct

set_option linter.unusedFintypeInType false

namespace RepresentationTheory.GroupTheory.ConjugacyClassCardinalityBounds

universe u v

section IsAlgClosedBound

open RepresentationTheory.ConjugacyClassTrace RepresentationTheory.AuxiliaryDecompositionData

private lemma traceForm_Std_eq_trace {K : Type u} {G : Type v}
    [Field K] [IsAlgClosed K] [Group G] [Fintype G]
    (D : RepresentationTheory.AuxiliaryDecompositionData.AuxiliaryDecompositionData K G)
    (i : Fin D.count) (x : MonoidAlgebra K G) :
    RepresentationTheory.ConjugacyClassTrace.moduleTrace K (D.indexedType i) x =
      (D.matrixRepresentation i x).trace := by
  let e : D.indexedType i ≃ₗ[K] (Fin (D.dimension i) → K) :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hconj : e.conj
      (RepresentationTheory.ConjugacyClassTrace.monoidAlgebraActionHom K (D.indexedType i) x) =
      (D.matrixRepresentation i x).toLin' := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply]
    rfl
  rw [RepresentationTheory.ConjugacyClassTrace.moduleTrace_eq_trace_action,
    ← LinearMap.trace_conj'
      (RepresentationTheory.ConjugacyClassTrace.monoidAlgebraActionHom K (D.indexedType i) x) e,
    hconj]
  exact Matrix.trace_toLin'_eq (D.matrixRepresentation i x)

/-- The maps associated to an auxiliary family are linearly independent. -/
theorem auxiliaryFamily_linearIndependent {K : Type u} {G : Type v}
    [Field K] [IsAlgClosed K] [Group G] [Fintype G]
    (D : RepresentationTheory.AuxiliaryDecompositionData.AuxiliaryDecompositionData K G) :
    LinearIndependent K (fun i =>
      (RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace K (D.indexedType i) :
        RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient K G →ₗ[K] K)) := by
  classical
  refine Fintype.linearIndependent_iff.mpr (fun c hc j => ?_)
  haveI := D.dimension_neZero j
  obtain ⟨xj, hxj⟩ := D.matrixProductRepresentation_surjective
    (Pi.single j (Matrix.single (0 : Fin (D.dimension j)) 0 (1 : K)))
  have hval : ∀ i, RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace K
      (D.indexedType i)
      (Submodule.mkQ
        (RepresentationTheory.ConjugacyClassTrace.auxiliaryRelationSubmodule K G) xj) =
      if i = j then 1 else 0 := by
    intro i
    rw [RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace_mkQ,
      traceForm_Std_eq_trace D i xj]
    have hb : D.matrixRepresentation i xj =
        (Pi.single j (Matrix.single (0 : Fin (D.dimension j)) 0 (1 : K)) :
          ∀ i, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) i := by
      simp only [
        RepresentationTheory.AuxiliaryDecompositionData.AuxiliaryDecompositionData.matrixRepresentation,
        AlgHom.comp_apply, hxj, Pi.evalAlgHom_apply]
    rw [hb]
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same, Matrix.trace_single_eq_same, if_pos rfl]
    · rw [Pi.single_eq_of_ne hij, Matrix.trace_zero, if_neg hij]
  have happ := LinearMap.congr_fun hc
    (Submodule.mkQ
      (RepresentationTheory.ConjugacyClassTrace.auxiliaryRelationSubmodule K G) xj)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, hval, smul_eq_mul, mul_ite, mul_one,
    mul_zero, LinearMap.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] using happ

/-- Over an algebraically closed field, the cardinality of an auxiliary type is bounded by the conjugacy classes. -/
theorem auxiliaryCard_le_card_conjClasses_algClosed
    (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter K G) ≤
      Nat.card (ConjClasses G) := by
  classical
  obtain ⟨D, hD⟩ :=
    RepresentationTheory.AuxiliaryDecompositionData.exists_auxiliaryDecompositionData_card_eq_count
      K G
  rw [RepresentationTheory.SimpleRepresentationModules.natCard_auxiliaryTypes_eq K G, hD]
  have hcard :=
    RepresentationTheory.GroupTheory.ConjugacyClassBounds.fintypeCard_le_card_conjClasses_of_linearIndependent_family
      (S := fun i => D.indexedType i) (auxiliaryFamily_linearIndependent D)
  simpa using hcard

end IsAlgClosedBound

/-- An algebra extension gives a cardinality bound between the associated auxiliary types. -/
theorem auxiliaryCard_le_auxiliaryCard_of_algebra
    (k K G : Type u) [Field k] [Field K] [Algebra k K] [Group G] [Fintype G] :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G) ≤
      Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter K G) := by
  classical
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  haveI : Module.Finite K (MonoidAlgebra K G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G K)
  set J : Ideal (MonoidAlgebra k G) := Ring.jacobson (MonoidAlgebra k G) with hJ
  haveI : IsArtinianRing (MonoidAlgebra k G) := IsArtinianRing.of_finite k (MonoidAlgebra k G)
  haveI : IsSemiprimaryRing (MonoidAlgebra k G) := inferInstance
  haveI : IsSemisimpleRing (MonoidAlgebra k G ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite k (MonoidAlgebra k G ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k J).toLinearMap
      Ideal.Quotient.mk_surjective
  set ψ : MonoidAlgebra k G →ₐ[k] K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ k J) with hψ
  set mh : G →* K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    ψ.toRingHom.toMonoidHom.comp (MonoidAlgebra.of k G) with hmh
  set φ : MonoidAlgebra K G →ₐ[K] K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    MonoidAlgebra.lift K (K ⊗[k] (MonoidAlgebra k G ⧸ J)) G mh with hφ
  set ι : MonoidAlgebra k G →ₐ[k] MonoidAlgebra K G :=
    MonoidAlgebra.lift k (MonoidAlgebra K G) G (MonoidAlgebra.of K G) with hι
  have hcomp : (φ.restrictScalars k).comp ι = ψ := by
    refine MonoidAlgebra.algHom_ext (M := G) (fun g => ?_) ?_
    · have hιg : ι (MonoidAlgebra.single g (1 : k)) =
          MonoidAlgebra.single g (1 : K) := by
        rw [hι, MonoidAlgebra.lift_single, one_smul, MonoidAlgebra.of_apply]
      have hφg : φ (MonoidAlgebra.single g (1 : K)) =
          ψ (MonoidAlgebra.single g (1 : k)) := by
        rw [hφ, MonoidAlgebra.lift_single, one_smul, hmh, MonoidHom.coe_comp,
          Function.comp_apply, MonoidAlgebra.of_apply]
        rfl
      rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hιg, hφg]
    · ext
  have hone : ∀ x : MonoidAlgebra k G ⧸ J, (1 : K) ⊗ₜ[k] x ∈ φ.range := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨ι p, ?_⟩
    change φ (ι p) = (1 : K) ⊗ₜ[k] Ideal.Quotient.mk J p
    have := AlgHom.congr_fun hcomp p
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this, hψ, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Ideal.Quotient.mkₐ_eq_mk]
  have hsurj : Function.Surjective
      (φ : MonoidAlgebra K G → K ⊗[k] (MonoidAlgebra k G ⧸ J)) := by
    rw [← AlgHom.range_eq_top, eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a x =>
        have hax : a ⊗ₜ[k] x = a • ((1 : K) ⊗ₜ[k] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hax]
        exact Subalgebra.smul_mem φ.range (hone x) a
    | add x y hx hy => exact add_mem hx hy
  rw [RepresentationTheory.SimpleRepresentationModules.natCard_auxiliaryTypes_eq k G,
    RepresentationTheory.SimpleRepresentationModules.natCard_auxiliaryTypes_eq K G]
  calc Nat.card
        (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u}
          (MonoidAlgebra k G)) =
      Nat.card
        (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u}
          (MonoidAlgebra k G ⧸ J)) :=
        (RepresentationTheory.SimpleRepresentationModules.natCard_auxiliaryRingType_jacobsonQuotient
          k).symm
    _ ≤ Nat.card
        (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u}
          (K ⊗[k] (MonoidAlgebra k G ⧸ J))) :=
        RepresentationTheory.RingTheory.AuxiliaryTypeInvariants.auxiliaryCard_le_tensorProduct_auxiliaryCard
          k K
    _ ≤ Nat.card
        (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u}
          (MonoidAlgebra K G)) :=
        RepresentationTheory.CategoryTheory.FullFunctorConsequences.natCard_auxiliaryType_le_of_surjective_ringHom
          K φ.toRingHom hsurj

/-- The cardinality of an auxiliary type is bounded by the number of conjugacy classes. -/
theorem auxiliaryCard_le_card_conjClasses
    (k G : Type u) [Field k] [Group G] [Fintype G] :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G) ≤
      Nat.card (ConjClasses G) :=
  (auxiliaryCard_le_auxiliaryCard_of_algebra k (AlgebraicClosure k) G).trans
    (auxiliaryCard_le_card_conjClasses_algClosed (AlgebraicClosure k) G)

end RepresentationTheory.GroupTheory.ConjugacyClassCardinalityBounds
