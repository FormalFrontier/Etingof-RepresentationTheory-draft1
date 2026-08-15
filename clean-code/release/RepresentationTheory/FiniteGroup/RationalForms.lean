/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroup.CharacterArithmetic
import RepresentationTheory.Group.CharacterOperations
import RepresentationTheory.Representation.FiniteProducts
import RepresentationTheory.FDRep.CharacterDecomposition
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.FDRep.Character
import RepresentationTheory.Alignment.Attribute

/-! # Rational forms of finite-group representations -/

namespace RepresentationTheory.FiniteGroup.RationalForms

open Finset CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G]

/-! ## Part (a): finite Galois envelopes for algebraic matrix realizations -/

/-- Scalar extension of a monoid algebra along a field algebra is algebra-equivalent to the monoid algebra over the extended field. -/
noncomputable def tensorProductMonoidAlgebraAlgEquiv
    (A C G : Type) [Field A] [Field C] [Algebra A C] [Group G] :
    C ⊗[A] MonoidAlgebra A G ≃ₐ[C] MonoidAlgebra C G := by
  let f : C ⊗[A] MonoidAlgebra A G →ₐ[C] MonoidAlgebra C G :=
    Algebra.TensorProduct.lift (Algebra.ofId C (MonoidAlgebra C G))
      (MonoidAlgebra.mapAlgHom G (Algebra.ofId A C)) (fun c x => by
        change Commute (algebraMap C (MonoidAlgebra C G) c) _
        exact Algebra.commutes _ _)
  let groupMap : G →* C ⊗[A] MonoidAlgebra A G :=
    (Algebra.TensorProduct.includeRight.toMonoidHom).comp (MonoidAlgebra.of A G)
  let g : MonoidAlgebra C G →ₐ[C] C ⊗[A] MonoidAlgebra A G :=
    (MonoidAlgebra.lift C _ G) groupMap
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext x m
    simp [f, g, groupMap]
  · apply AlgHom.toLinearMap_injective
    ext c
    have hmap : (MonoidAlgebra.mapAlgHom G (Algebra.ofId A C))
        (MonoidAlgebra.single c 1) = MonoidAlgebra.single c 1 := by
      rw [MonoidAlgebra.mapAlgHom_single]
      simp
    simp [f, g, groupMap, hmap]

/-- A property asserting field-relative structure for a finite-dimensional complex representation. -/
def FDRep.IsDefinedOver (K : IntermediateField ℚ ℂ) (V : FDRep ℂ G) : Prop :=
  ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
    ∀ g i j, LinearMap.toMatrix b b (V.ρ g) i j ∈ K

/-- A property of a finite-dimensional complex representation of a group. -/
def FDRep.IsAlgebraic (V : FDRep ℂ G) : Prop :=
  ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
    ∀ g i j, _root_.IsAlgebraic ℚ (LinearMap.toMatrix b b (V.ρ g) i j)

/-- A predicate on a basis of the underlying complex module of a finite-dimensional representation. -/
def FDRep.BasisIsAlgebraic {I : Type} [Fintype I] [DecidableEq I] (V : FDRep ℂ G)
    (b : Module.Basis I ℂ V) : Prop :=
  ∀ g i j, _root_.IsAlgebraic ℚ (LinearMap.toMatrix b b (V.ρ g) i j)

/-- The basis predicate is preserved when the basis is reindexed along an equivalence. -/
theorem FDRep.BasisIsAlgebraic.reindex {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {V : FDRep ℂ G} {b : Module.Basis I ℂ V} (h : FDRep.BasisIsAlgebraic V b)
    (e : I ≃ J) : FDRep.BasisIsAlgebraic V (b.reindex e) := by
  classical
  intro g i j
  simpa [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply] using h g (e.symm i) (e.symm j)

/-- A representation is algebraic when it has a basis satisfying the corresponding basis predicate. -/
theorem FDRep.isAlgebraic_of_basis {I : Type} [Fintype I] [DecidableEq I]
    {V : FDRep ℂ G}
    (b : Module.Basis I ℂ V) (h : FDRep.BasisIsAlgebraic V b) :
    FDRep.IsAlgebraic V := by
  let e : I ≃ Fin (Module.finrank ℂ V) :=
    (Fintype.equivFin I).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  refine ⟨b.reindex e, ?_⟩
  exact h.reindex e

/-- This representation property passes across an isomorphism. -/
theorem FDRep.IsAlgebraic.ofIso {V W : FDRep ℂ G} (e : V ≅ W)
    (hV : FDRep.IsAlgebraic V) : FDRep.IsAlgebraic W := by
  obtain ⟨b, hb⟩ := hV
  let φ : V ≃ₗ[ℂ] W := FDRep.isoToLinearEquiv e
  let bW : Module.Basis (Fin (Module.finrank ℂ V)) ℂ W := b.map φ
  have hbW : FDRep.BasisIsAlgebraic W bW := by
    intro g i j
    have hinter : W.ρ g (φ (b j)) = φ (V.ρ g (b j)) := by
      rw [FDRep.Iso.conj_ρ e g, LinearEquiv.conj_apply]
      simp [φ]
    simpa [bW, φ, LinearMap.toMatrix_apply, Module.Basis.map_apply, hinter,
      Module.Basis.map] using hb g i j
  exact FDRep.isAlgebraic_of_basis bW hbW

/-- The representation produced by the indicated finite-family construction is algebraic when every member of the family is algebraic. -/
theorem FDRep.isAlgebraic_auxiliaryFamilyConstruction {I : Type} [Fintype I] (V : I → FDRep ℂ G)
    (hV : ∀ i, FDRep.IsAlgebraic (V i)) :
    FDRep.IsAlgebraic (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) := by
  classical
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : FDRep.BasisIsAlgebraic (V i) (b i) := by
    simpa [FDRep.BasisIsAlgebraic, b] using (hV i).choose_spec
  let coord : (RepresentationTheory.Representation.FiniteProducts.finiteProduct V : Type) ≃ₗ[ℂ]
      ((p : Σ i, Fin (Module.finrank ℂ (V i))) → ℂ) := {
    toFun := fun x p => (b p.1).repr (x p.1) p.2
    invFun := fun c i => (b i).equivFun.symm (fun j => c ⟨i, j⟩)
    left_inv := fun x => by
      funext i
      exact (b i).equivFun.symm_apply_apply (x i)
    right_inv := fun c => by
      funext ⟨i, j⟩
      exact congrFun ((b i).equivFun.apply_symm_apply (fun q => c ⟨i, q⟩)) j
    map_add' := fun x y => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_add ((b i).repr) (x i) (y i))
    map_smul' := fun c x => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_smul ((b i).repr) c (x i)) }
  let bπ : Module.Basis (Σ i, Fin (Module.finrank ℂ (V i))) ℂ
      (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) := Module.Basis.ofEquivFun coord
  have hbπ : FDRep.BasisIsAlgebraic (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) bπ := by
    rintro g ⟨i, p⟩ ⟨j, q⟩
    change _root_.IsAlgebraic ℚ (LinearMap.toMatrix bπ bπ ((RepresentationTheory.Representation.FiniteProducts.finiteProduct V).ρ g)
      ⟨i, p⟩ ⟨j, q⟩)
    by_cases hij : i = j
    · subst j
      have heq : LinearMap.toMatrix bπ bπ ((RepresentationTheory.Representation.FiniteProducts.finiteProduct V).ρ g)
          ⟨i, p⟩ ⟨i, q⟩ = LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q := by
        rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply,
          Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨i, q⟩ 1)) i)) p = _
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun j =>
            (Pi.single ⟨i, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, j⟩))) p = _
        congr 3
        apply (b i).equivFun.injective
        rw [(b i).equivFun.apply_symm_apply]
        ext j
        simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      rw [heq]
      exact hb i g p q
    · have hz : LinearMap.toMatrix bπ bπ ((RepresentationTheory.Representation.FiniteProducts.finiteProduct V).ρ g)
          ⟨i, p⟩ ⟨j, q⟩ = 0 := by
        rw [LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply,
          Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨j, q⟩ 1)) i)) p = 0
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩))) p = 0
        have hfun : (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩) = 0 := by
          funext r
          have hne : (⟨j, q⟩ : Σ k, Fin (Module.finrank ℂ (V k))) ≠ ⟨i, r⟩ := by
            intro h
            exact hij (Sigma.mk.inj_iff.mp h).1.symm
          simp [hne]
        rw [hfun, map_zero, map_zero]
        simp
      rw [hz]
      exact isAlgebraic_zero
  exact FDRep.isAlgebraic_of_basis bπ hbπ

/-- If a finite family gives pairwise nonisomorphic representatives of all simple representations and each representative is algebraic, then every representation is algebraic. -/
theorem FDRep.isAlgebraic_of_simple_representatives [Fintype G]
    {I : Type} [Fintype I] (T : I → FDRep ℂ G)
    (hsimple : ∀ i, Simple (T i))
    (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (hAlg : ∀ i, FDRep.IsAlgebraic (T i)) (V : FDRep ℂ G) :
    FDRep.IsAlgebraic V := by
  classical
  let n := RepresentationTheory.FDRep.CharacterDecomposition.indexedNatForRepresentation T V
  let U : (Σ i, Fin (n i)) → FDRep ℂ G := fun p => T p.1
  have hpi : FDRep.IsAlgebraic (RepresentationTheory.Representation.FiniteProducts.finiteProduct U) :=
    FDRep.isAlgebraic_auxiliaryFamilyConstruction U (fun p => hAlg p.1)
  let eV : V ≅ RepresentationTheory.FDRep.CharacterDecomposition.representationFromIndexedNats T n :=
    (RepresentationTheory.FDRep.CharacterDecomposition.iso_representationFromIndexedNats_indexedNatForRepresentation T hsimple hinj hcomplete V).some
  let eπ : RepresentationTheory.Representation.FiniteProducts.finiteProduct U ≅ RepresentationTheory.FDRep.CharacterDecomposition.representationFromIndexedNats T n :=
    RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct U
  exact hpi.ofIso ((eV.trans eπ.symm).symm)

/-- A predicate, relative to an intermediate field of the complexes, on a basis of a representation. -/
def FDRep.BasisIsDefinedOver (K : IntermediateField ℚ ℂ) {I : Type} [Fintype I]
    [DecidableEq I] (V : FDRep ℂ G) (b : Module.Basis I ℂ V) : Prop :=
  ∀ g i j, LinearMap.toMatrix b b (V.ρ g) i j ∈ K

/-- The field-relative basis predicate is invariant under reindexing the basis. -/
theorem FDRep.BasisIsDefinedOver.reindex {K : IntermediateField ℚ ℂ}
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {V : FDRep ℂ G} {b : Module.Basis I ℂ V} (h : FDRep.BasisIsDefinedOver K V b)
    (e : I ≃ J) : FDRep.BasisIsDefinedOver K V (b.reindex e) := by
  classical
  intro g i j
  simpa [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply] using h g (e.symm i) (e.symm j)

/-- A representation is defined over an intermediate field when it has a basis satisfying the field-relative basis predicate. -/
theorem FDRep.isDefinedOver_of_basis {K : IntermediateField ℚ ℂ}
    {I : Type} [Fintype I] [DecidableEq I] {V : FDRep ℂ G}
    (b : Module.Basis I ℂ V) (h : FDRep.BasisIsDefinedOver K V b) : FDRep.IsDefinedOver K V := by
  let e : I ≃ Fin (Module.finrank ℂ V) :=
    (Fintype.equivFin I).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  exact ⟨b.reindex e, h.reindex e⟩

/-- Being defined over a fixed intermediate field passes across an isomorphism of representations. -/
theorem FDRep.IsDefinedOver.ofIso {K : IntermediateField ℚ ℂ} {V W : FDRep ℂ G}
    (e : V ≅ W) (hV : FDRep.IsDefinedOver K V) : FDRep.IsDefinedOver K W := by
  obtain ⟨b, hb⟩ := hV
  let φ : V ≃ₗ[ℂ] W := FDRep.isoToLinearEquiv e
  let bW : Module.Basis (Fin (Module.finrank ℂ V)) ℂ W := b.map φ
  have hbW : FDRep.BasisIsDefinedOver K W bW := by
    intro g i j
    have hinter : W.ρ g (φ (b j)) = φ (V.ρ g (b j)) := by
      rw [FDRep.Iso.conj_ρ e g, LinearEquiv.conj_apply]
      simp [φ]
    simpa [bW, φ, LinearMap.toMatrix_apply, Module.Basis.map_apply, hinter,
      Module.Basis.map] using hb g i j
  exact FDRep.isDefinedOver_of_basis bW hbW

/-- The representation produced by the indicated finite-family construction is defined over a field when every member of the family is defined over that field. -/
theorem FDRep.isDefinedOver_auxiliaryFamilyConstruction {I : Type} [Fintype I] (V : I → FDRep ℂ G)
    {K : IntermediateField ℚ ℂ} (hV : ∀ i, FDRep.IsDefinedOver K (V i)) :
    FDRep.IsDefinedOver K (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) := by
  classical
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : FDRep.BasisIsDefinedOver K (V i) (b i) := by
    simpa [FDRep.BasisIsDefinedOver, b] using (hV i).choose_spec
  let coord : (RepresentationTheory.Representation.FiniteProducts.finiteProduct V : Type) ≃ₗ[ℂ]
      ((p : Σ i, Fin (Module.finrank ℂ (V i))) → ℂ) := {
    toFun := fun x p => (b p.1).repr (x p.1) p.2
    invFun := fun c i => (b i).equivFun.symm (fun j => c ⟨i, j⟩)
    left_inv := fun x => by
      funext i
      exact (b i).equivFun.symm_apply_apply (x i)
    right_inv := fun c => by
      funext ⟨i, j⟩
      exact congrFun ((b i).equivFun.apply_symm_apply (fun q => c ⟨i, q⟩)) j
    map_add' := fun x y => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_add ((b i).repr) (x i) (y i))
    map_smul' := fun c x => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_smul ((b i).repr) c (x i)) }
  let bπ : Module.Basis (Σ i, Fin (Module.finrank ℂ (V i))) ℂ
      (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) := Module.Basis.ofEquivFun coord
  have hbπ : FDRep.BasisIsDefinedOver K (RepresentationTheory.Representation.FiniteProducts.finiteProduct V) bπ := by
    rintro g ⟨i, p⟩ ⟨j, q⟩
    by_cases hij : i = j
    · subst j
      have heq : LinearMap.toMatrix bπ bπ ((RepresentationTheory.Representation.FiniteProducts.finiteProduct V).ρ g)
          ⟨i, p⟩ ⟨i, q⟩ = LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q := by
        rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨i, q⟩ 1)) i)) p = _
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun j =>
            (Pi.single ⟨i, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, j⟩))) p = _
        congr 3
        apply (b i).equivFun.injective
        rw [(b i).equivFun.apply_symm_apply]
        ext j
        simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      rw [heq]
      exact hb i g p q
    · have hz : LinearMap.toMatrix bπ bπ ((RepresentationTheory.Representation.FiniteProducts.finiteProduct V).ρ g)
          ⟨i, p⟩ ⟨j, q⟩ = 0 := by
        rw [LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨j, q⟩ 1)) i)) p = 0
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩))) p = 0
        have hfun : (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩) = 0 := by
          funext r
          have hne : (⟨j, q⟩ : Σ k, Fin (Module.finrank ℂ (V k))) ≠ ⟨i, r⟩ := by
            intro h
            exact hij (Sigma.mk.inj_iff.mp h).1.symm
          simp [hne]
        rw [hfun, map_zero, map_zero]
        simp
      rw [hz]
      exact K.zero_mem
  exact FDRep.isDefinedOver_of_basis bπ hbπ

/-- If a finite family gives pairwise nonisomorphic representatives of all simple representations and each is defined over a field, then every representation is defined over that field. -/
theorem FDRep.isDefinedOver_of_simple_representatives [Fintype G]
    {K : IntermediateField ℚ ℂ} {I : Type} [Fintype I] (T : I → FDRep ℂ G)
    (hsimple : ∀ i, Simple (T i))
    (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (hK : ∀ i, FDRep.IsDefinedOver K (T i)) (V : FDRep ℂ G) : FDRep.IsDefinedOver K V := by
  classical
  let n := RepresentationTheory.FDRep.CharacterDecomposition.indexedNatForRepresentation T V
  let U : (Σ i, Fin (n i)) → FDRep ℂ G := fun p => T p.1
  have hpi : FDRep.IsDefinedOver K (RepresentationTheory.Representation.FiniteProducts.finiteProduct U) :=
    FDRep.isDefinedOver_auxiliaryFamilyConstruction U (fun p => hK p.1)
  let eV : V ≅ RepresentationTheory.FDRep.CharacterDecomposition.representationFromIndexedNats T n :=
    (RepresentationTheory.FDRep.CharacterDecomposition.iso_representationFromIndexedNats_indexedNatForRepresentation T hsimple hinj hcomplete V).some
  let eπ : RepresentationTheory.Representation.FiniteProducts.finiteProduct U ≅ RepresentationTheory.FDRep.CharacterDecomposition.representationFromIndexedNats T n :=
    RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct U
  exact hpi.ofIso ((eV.trans eπ.symm).symm)

/-- A representation defined over an intermediate field remains defined over any larger intermediate field. -/
theorem FDRep.IsDefinedOver.mono {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    {V : FDRep ℂ G} (hV : FDRep.IsDefinedOver K V) : FDRep.IsDefinedOver L V := by
  obtain ⟨b, hb⟩ := hV
  exact ⟨b, fun g i j => hKL (hb g i j)⟩

/-- A complex representation is algebraic exactly when it is defined over the algebraic closure of the rationals inside the complexes. -/
theorem FDRep.isAlgebraic_iff_isDefinedOver_auxiliaryScalarType (V : FDRep ℂ G) :
    FDRep.IsAlgebraic V ↔ FDRep.IsDefinedOver (algebraicClosure ℚ ℂ) V := by
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, fun g i j => ?_⟩
  · exact mem_algebraicClosure_iff.mpr (hb g i j)
  · exact mem_algebraicClosure_iff.mp (hb g i j)

/-- A finite family of algebraic representations of a finite group admits a common field of definition that is finite-dimensional and Galois over the rationals. -/
theorem FDRep.exists_common_finiteGalois_fieldOfDefinition [Fintype G] {I : Type} [Fintype I]
    (V : I → FDRep ℂ G) (hV : ∀ i, FDRep.IsAlgebraic (V i)) :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ ∀ i, FDRep.IsDefinedOver K (V i) := by
  classical
  letI : IsAlgClosure ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsGalois ℚ (algebraicClosure ℚ ℂ) :=
    IsAlgClosure.isGalois ℚ (algebraicClosure ℚ ℂ)
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : ∀ g p q, _root_.IsAlgebraic ℚ
      (LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q) := (hV i).choose_spec
  let CoeffIndex := Σ i : I, G × Fin (Module.finrank ℂ (V i)) ×
    Fin (Module.finrank ℂ (V i))
  let coeff (x : CoeffIndex) : ℂ :=
    LinearMap.toMatrix (b x.1) (b x.1) ((V x.1).ρ x.2.1) x.2.2.1 x.2.2.2
  let coeffA (x : CoeffIndex) : algebraicClosure ℚ ℂ :=
    ⟨coeff x, mem_algebraicClosure_iff.mpr (hb x.1 x.2.1 x.2.2.1 x.2.2.2)⟩
  let s : Set (algebraicClosure ℚ ℂ) := Set.range coeffA
  let L : FiniteGaloisIntermediateField ℚ (algebraicClosure ℚ ℂ) :=
    FiniteGaloisIntermediateField.adjoin ℚ s
  let K : IntermediateField ℚ ℂ :=
    L.toIntermediateField.map (algebraicClosure ℚ ℂ).val
  have hfin : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional
      (IntermediateField.equivMap L.toIntermediateField
        (algebraicClosure ℚ ℂ).val).toLinearEquiv
  have hgal : IsGalois ℚ K :=
    IsGalois.of_algEquiv (IntermediateField.equivMap L.toIntermediateField
      (algebraicClosure ℚ ℂ).val)
  refine ⟨K, hfin, hgal, fun i => ⟨b i, fun g p q => ?_⟩⟩
  change coeff ⟨i, g, p, q⟩ ∈
    L.toIntermediateField.map (algebraicClosure ℚ ℂ).val
  rw [IntermediateField.mem_map]
  refine ⟨coeffA ⟨i, g, p, q⟩, ?_, rfl⟩
  exact FiniteGaloisIntermediateField.subset_adjoin ℚ s ⟨_, rfl⟩

/-- An algebraic representation of a finite group is defined over some finite-dimensional Galois intermediate field over the rationals. -/
theorem FDRep.exists_finiteGalois_fieldOfDefinition (V : FDRep ℂ G)
    [Fintype G] (hV : FDRep.IsAlgebraic V) :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ FDRep.IsDefinedOver K V := by
  simpa using FDRep.exists_common_finiteGalois_fieldOfDefinition (I := Fin 1) (fun _ => V) (fun _ => hV)

/-! ### Algebraic Wedderburn models and simultaneous descent -/

/-- An auxiliary type. -/
abbrev AuxiliaryScalarType : Type := algebraicClosure ℚ ℂ

/-- The auxiliary scalar type is an algebraic closure of the rationals. -/
noncomputable local instance AuxiliaryScalarType.isAlgClosure : IsAlgClosure ℚ AuxiliaryScalarType :=
  algebraicClosure.isAlgClosure ℚ ℂ

/-- The auxiliary scalar type is algebraically closed. -/
noncomputable local instance AuxiliaryScalarType.isAlgClosed : IsAlgClosed AuxiliaryScalarType :=
  IsAlgClosure.isAlgClosed (R := ℚ)

/-- The cardinality of a finite group has nonzero cast in the auxiliary scalar type. -/
local instance AuxiliaryScalarType.natCard_neZero (H : Type) [Group H] [Fintype H] :
    NeZero (Nat.card H : AuxiliaryScalarType) :=
  ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'⟩

/-- The natural cardinality of a finite group is nonzero after the indicated cast. -/
local instance natCard_neZero (H : Type) [Group H] [Fintype H] :
    NeZero (Nat.card H : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'⟩

/-- Auxiliary data associated with a finite group over the auxiliary scalar type. -/
noncomputable def rationalAuxiliaryData (H : Type) [Group H] [Fintype H] :
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData AuxiliaryScalarType H := by
  exact RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default

/-- A monoid homomorphism from a finite group to a family of square complex matrix algebras indexed by auxiliary data. -/
noncomputable def complexBlockRepresentation (H : Type) [Group H] [Fintype H] :
    H →* (∀ i : Fin (rationalAuxiliaryData H).count,
      Matrix (Fin ((rationalAuxiliaryData H).dimension i))
        (Fin ((rationalAuxiliaryData H).dimension i)) ℂ) where
  toFun g i := ((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H g) i).map
    (algebraicClosure ℚ ℂ).val
  map_one' := by
    funext i
    change ((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H 1) i).map
      (algebraicClosure ℚ ℂ).val = 1
    rw [map_one, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  map_mul' g h := by
    funext i
    rw [map_mul, map_mul]
    change ((((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H g)) i) *
      (((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H h)) i)).map
        (algebraicClosure ℚ ℂ).val = _
    rw [Matrix.map_mul]
    rfl

/-- An algebra homomorphism from the complex group algebra to a family of square complex matrix algebras. -/
noncomputable def complexGroupAlgebraBlockMap (H : Type) [Group H] [Fintype H] :
    MonoidAlgebra ℂ H →ₐ[ℂ] (∀ i : Fin (rationalAuxiliaryData H).count,
      Matrix (Fin ((rationalAuxiliaryData H).dimension i))
        (Fin ((rationalAuxiliaryData H).dimension i)) ℂ) :=
  (MonoidAlgebra.lift ℂ _ H) (complexBlockRepresentation H)

/-- After extending coefficients from the auxiliary scalar type, each entry of the complex block map is the value of the corresponding auxiliary coordinate embedded in the complexes. -/
theorem complexGroupAlgebraBlockMap_map_entry {H : Type} [Group H] [Fintype H]
    (a : MonoidAlgebra AuxiliaryScalarType H) (i : Fin (rationalAuxiliaryData H).count)
    (p q : Fin ((rationalAuxiliaryData H).dimension i)) :
    complexGroupAlgebraBlockMap H
        ((MonoidAlgebra.mapAlgHom H (Algebra.ofId AuxiliaryScalarType ℂ)) a) i p q =
      ((rationalAuxiliaryData H).groupAlgebraEquivMatrix a i p q : AuxiliaryScalarType) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => simp [complexGroupAlgebraBlockMap, complexBlockRepresentation]
  | hadd a b ha hb => simp [map_add, ha, hb]
  | hsmul r a ha =>
      simp only [map_smul]
      change complexGroupAlgebraBlockMap H
          ((r : ℂ) • (MonoidAlgebra.mapAlgHom H (Algebra.ofId AuxiliaryScalarType ℂ)) a) i p q = _
      rw [map_smul, Pi.smul_apply, Matrix.smul_apply, ha]
      rfl

/-- A linear equivalence from scalar-extended square matrices over the auxiliary scalar type to square complex matrices. -/
noncomputable def tensorProductMatrixLinearEquiv (n : ℕ) :
    ℂ ⊗[AuxiliaryScalarType] Matrix (Fin n) (Fin n) AuxiliaryScalarType ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (TensorProduct.piRight AuxiliaryScalarType ℂ ℂ (fun _ : Fin n => Fin n → AuxiliaryScalarType)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin n =>
      TensorProduct.piScalarRight AuxiliaryScalarType ℂ ℂ (Fin n)))

/-- The entry of the scalar-extension matrix equivalence on a pure tensor with scalar one is the corresponding auxiliary matrix entry embedded in the complexes. -/
theorem tensorProductMatrixLinearEquiv_tmul_entry (n : ℕ)
    (M : Matrix (Fin n) (Fin n) AuxiliaryScalarType) (p q : Fin n) :
    tensorProductMatrixLinearEquiv n (1 ⊗ₜ[AuxiliaryScalarType] M) p q = (M p q : AuxiliaryScalarType) := by
  change (M p q : ℂ) * 1 = (M p q : ℂ)
  exact mul_one _

/-- A linear equivalence between the scalar extension of a finite family of square auxiliary matrices and the corresponding family of complex matrices. -/
noncomputable def tensorProductMatrixPiLinearEquiv {n : ℕ} (d : Fin n → ℕ) :
    ℂ ⊗[AuxiliaryScalarType] (∀ i, Matrix (Fin (d i)) (Fin (d i)) AuxiliaryScalarType) ≃ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  (TensorProduct.piRight AuxiliaryScalarType ℂ ℂ
    (fun i : Fin n => Matrix (Fin (d i)) (Fin (d i)) AuxiliaryScalarType)).trans
      (LinearEquiv.piCongrRight (fun i => tensorProductMatrixLinearEquiv (d i)))

/-- A complex-linear equivalence from the complex group algebra to a family of square complex matrix algebras. -/
noncomputable def complexGroupAlgebraBlockEquiv (H : Type) [Group H] [Fintype H] :
    MonoidAlgebra ℂ H ≃ₗ[ℂ] (∀ i : Fin (rationalAuxiliaryData H).count,
      Matrix (Fin ((rationalAuxiliaryData H).dimension i))
        (Fin ((rationalAuxiliaryData H).dimension i)) ℂ) :=
  (tensorProductMonoidAlgebraAlgEquiv AuxiliaryScalarType ℂ H).symm.toLinearEquiv ≪≫ₗ
    (rationalAuxiliaryData H).groupAlgebraEquivMatrix.toLinearEquiv.baseChange AuxiliaryScalarType ℂ _ _ ≪≫ₗ
    tensorProductMatrixPiLinearEquiv (rationalAuxiliaryData H).dimension

/-- On a group element, each matrix entry of the complex block equivalence agrees with the embedded auxiliary coordinate. -/
theorem complexGroupAlgebraBlockEquiv_of_entry {H : Type} [Group H] [Fintype H]
    (g : H) (i : Fin (rationalAuxiliaryData H).count)
    (p q : Fin ((rationalAuxiliaryData H).dimension i)) :
    complexGroupAlgebraBlockEquiv H (MonoidAlgebra.of ℂ H g) i p q =
      ((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H g) i p q : AuxiliaryScalarType) := by
  simp [complexGroupAlgebraBlockEquiv, tensorProductMatrixPiLinearEquiv,
    tensorProductMonoidAlgebraAlgEquiv]
  exact tensorProductMatrixLinearEquiv_tmul_entry _ _ _ _

/-- The linear map underlying the block algebra homomorphism equals the linear map underlying the corresponding block equivalence. -/
theorem complexGroupAlgebraBlockMap_toLinearMap {H : Type} [Group H] [Fintype H] :
    (complexGroupAlgebraBlockMap H).toLinearMap = (complexGroupAlgebraBlockEquiv H).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
      ext i p q
      calc
        (complexGroupAlgebraBlockMap H).toLinearMap (MonoidAlgebra.of ℂ H g) i p q =
            ((rationalAuxiliaryData H).groupAlgebraEquivMatrix
              (MonoidAlgebra.of AuxiliaryScalarType H g) i p q : AuxiliaryScalarType) := by
              simp [complexGroupAlgebraBlockMap, complexBlockRepresentation]
        _ = (complexGroupAlgebraBlockEquiv H).toLinearMap
            (MonoidAlgebra.of ℂ H g) i p q := complexGroupAlgebraBlockEquiv_of_entry g i p q |>.symm
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul c x hx => simp only [map_smul, hx]

/-- Auxiliary data associated with a finite group over the complex numbers. -/
noncomputable def complexAuxiliaryData (H : Type) [Group H] [Fintype H] : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ H := by
  refine ⟨(rationalAuxiliaryData H).count, (rationalAuxiliaryData H).dimension,
    (rationalAuxiliaryData H).dimension_neZero, AlgEquiv.ofBijective (complexGroupAlgebraBlockMap H) ?_⟩
  have heq : ∀ x, complexGroupAlgebraBlockMap H x = complexGroupAlgebraBlockEquiv H x :=
    fun x => LinearMap.congr_fun complexGroupAlgebraBlockMap_toLinearMap x
  constructor
  · intro x y hxy
    apply (complexGroupAlgebraBlockEquiv H).injective
    rw [← heq x, ← heq y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := (complexGroupAlgebraBlockEquiv H).surjective y
    exact ⟨x, (heq x).trans hx⟩

/-- Each representation selected by the complex auxiliary data of a finite group is algebraic. -/
theorem FDRep.isAlgebraic_auxiliarySimple {H : Type} [Group H] [Fintype H]
    (i : Fin (complexAuxiliaryData H).count) :
    FDRep.IsAlgebraic ((complexAuxiliaryData H).representation i) := by
  let D := complexAuxiliaryData H
  let b : Module.Basis (Fin (D.dimension i)) ℂ (D.representation i) := by
    change Module.Basis (Fin (D.dimension i)) ℂ (Fin (D.dimension i) → ℂ)
    exact Pi.basisFun ℂ (Fin (D.dimension i))
  apply FDRep.isAlgebraic_of_basis b
  intro g p q
  have hmat : LinearMap.toMatrix b b ((D.representation i).ρ g) =
      D.matrixBlockHom i (MonoidAlgebra.of ℂ H g) := by
    change LinearMap.toMatrixAlgEquiv'
      (Matrix.toLinAlgEquiv' (D.matrixBlockHom i (MonoidAlgebra.of ℂ H g))) = _
    rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
  rw [hmat]
  have hentry : D.matrixBlockHom i (MonoidAlgebra.of ℂ H g) p q =
      (((rationalAuxiliaryData H).groupAlgebraEquivMatrix
        (MonoidAlgebra.of AuxiliaryScalarType H g) i p q : AuxiliaryScalarType) : ℂ) := by
    change complexGroupAlgebraBlockMap H (MonoidAlgebra.of ℂ H g) i p q = _
    simp [complexGroupAlgebraBlockMap, complexBlockRepresentation]
  rw [hentry]
  exact mem_algebraicClosure_iff.mp
    ((rationalAuxiliaryData H).groupAlgebraEquivMatrix (MonoidAlgebra.of AuxiliaryScalarType H g) i p q).2

/-- Every finite-dimensional complex representation of a finite group has the algebraicity property. -/
theorem FDRep.isAlgebraic_of_finite [Fintype G] (V : FDRep ℂ G) :
    FDRep.IsAlgebraic V := by
  let D := complexAuxiliaryData G
  exact FDRep.isAlgebraic_of_simple_representatives D.representation
    D.simple_representation D.representation_index_eq_of_iso D.exists_iso_representation_of_simple
    FDRep.isAlgebraic_auxiliarySimple V

/-- For a finite group, there is a finite-dimensional Galois intermediate field over the rationals over which every complex representation is defined. -/
@[source_ref "Chapter5/Problem5.2.7" (role := primary)]
theorem FDRep.exists_universal_finiteGalois_fieldOfDefinition [Fintype G] :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
        ∀ V : FDRep ℂ G, FDRep.IsDefinedOver K V := by
  let D := complexAuxiliaryData G
  obtain ⟨K, hfd, hgal, hK⟩ :=
    FDRep.exists_common_finiteGalois_fieldOfDefinition D.representation
      FDRep.isAlgebraic_auxiliarySimple
  refine ⟨K, hfd, hgal, ?_⟩
  exact FDRep.isDefinedOver_of_simple_representatives D.representation
    D.simple_representation D.representation_index_eq_of_iso D.exists_iso_representation_of_simple hK

variable [Fintype G] [DecidableEq G]

private theorem char_mul_inv_eq_normSq (V : FDRep ℂ G) (g : G) :
    V.character g * V.character g⁻¹ = ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
  rw [RepresentationTheory.Group.CharacterOperations.character_inv_eq_conj V g, Complex.mul_conj]

/-- For a simple complex representation of a finite group, the sum of its character times its value at the inverse equals the group cardinality. -/
theorem FDRep.sum_character_mul_inv (V : FDRep ℂ G) [Simple V]
    [Invertible (Fintype.card G : ℂ)] :
    ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
  have horth := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple V V
  rw [if_pos ⟨Iso.refl V⟩, smul_eq_mul] at horth
  -- `⅟|G| * S = 1`, so multiplying by `|G|` gives `S = |G|`.
  have h2 : (Fintype.card G : ℂ) * (⅟(Fintype.card G : ℂ) *
      ∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) * 1 := by rw [horth]
  rwa [← mul_assoc, mul_invOf_self, one_mul, mul_one] at h2

/-- For a simple representation of dimension greater than one whose character never vanishes, the product of the squared character norms away from the identity lies strictly between zero and one. -/
@[source_ref "Chapter5/Problem5.2.7" (role := supporting)]
theorem FDRep.normSqCharacterProduct_mem_Ioo (V : FDRep ℂ G) [Simple V] (h : 1 < Module.finrank ℂ V)
    (hne : ∀ g : G, V.character g ≠ 0) :
    0 < ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) ∧
      ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) < 1 := by
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero (α := G))
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  have hs_erase : s = univ.erase 1 := Finset.filter_ne' univ 1
  -- `dim V ≥ 2`, as a real number.
  have hfrn : 2 ≤ Module.finrank ℂ V := h
  have hfr : (2 : ℝ) ≤ (Module.finrank ℂ V : ℝ) := by exact_mod_cast hfrn
  -- `∑_{g} |χ_V(g)|² = |G|`, as a real identity.
  have hsumreal : ∑ g : G, Complex.normSq (V.character g) = (Fintype.card G : ℝ) := by
    have hC : (↑(∑ g : G, Complex.normSq (V.character g)) : ℂ) = (Fintype.card G : ℂ) := by
      rw [Complex.ofReal_sum]
      rw [Finset.sum_congr rfl (fun g _ => (char_mul_inv_eq_normSq V g).symm)]
      exact FDRep.sum_character_mul_inv V
    exact_mod_cast hC
  -- `|χ_V(1)|² = (dim V)²`.
  have h1 : Complex.normSq (V.character (1 : G)) = (Module.finrank ℂ V : ℝ) ^ 2 := by
    rw [FDRep.char_one, Complex.normSq_natCast]; ring
  -- `∑_{g ≠ 1} |χ_V(g)|² = |G| - (dim V)²`.
  have hSs : ∑ g ∈ s, Complex.normSq (V.character g)
      = (Fintype.card G : ℝ) - (Module.finrank ℂ V : ℝ) ^ 2 := by
    have hsplit := Finset.add_sum_erase univ
      (fun g => Complex.normSq (V.character g)) (Finset.mem_univ (1 : G))
    rw [hs_erase]
    have hrw : ∑ g ∈ univ.erase 1, Complex.normSq (V.character g)
        = (∑ g : G, Complex.normSq (V.character g)) - Complex.normSq (V.character 1) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)
    rw [hrw, hsumreal, h1]
  -- `|G| ≥ 4` (since `∑ |χ|² = |G| ≥ |χ_V(1)|² = (dim V)² ≥ 4`).
  have hcardge : (4 : ℝ) ≤ (Fintype.card G : ℝ) := by
    rw [← hsumreal]
    calc (4 : ℝ) ≤ (Module.finrank ℂ V : ℝ) ^ 2 := by nlinarith [hfr]
      _ = Complex.normSq (V.character 1) := h1.symm
      _ ≤ ∑ g : G, Complex.normSq (V.character g) :=
          Finset.single_le_sum (fun g _ => Complex.normSq_nonneg _) (Finset.mem_univ 1)
  -- `s.card = |G| - 1 > 0`.
  have hcard_real : (s.card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    rw [hs_erase, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hcardpos : 0 < s.card := by
    have : (0 : ℝ) < (s.card : ℝ) := by rw [hcard_real]; linarith
    exact_mod_cast this
  -- Each factor is positive, hence so is the product.
  have hβpos : 0 < ∏ g ∈ s, Complex.normSq (V.character g) :=
    Finset.prod_pos (fun g _ => Complex.normSq_pos.mpr (hne g))
  refine ⟨hβpos, ?_⟩
  -- The sum over `s` is strictly below the number of terms.
  have hlt : ∑ g ∈ s, Complex.normSq (V.character g) < (s.card : ℝ) := by
    rw [hSs, hcard_real]; nlinarith [hfr]
  -- AM-GM with all weights `1`.
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ))
    (fun g => Complex.normSq (V.character g)) (fun i _ => zero_le_one)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hcardpos)
    (fun i _ => Complex.normSq_nonneg _)
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hgm
  -- `β ^ (1/card) ≤ (∑)/card < 1`, hence `β < 1`.
  have hrhs : (∑ g ∈ s, Complex.normSq (V.character g)) / (s.card : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast hcardpos)]; exact hlt
  have hβt : (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) < 1 :=
    lt_of_le_of_lt hgm hrhs
  by_contra hge
  push Not at hge
  have : 1 ≤ (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) :=
    Real.one_le_rpow hge (by positivity)
  linarith

/-- A simple finite-group representation of complex dimension greater than one has a group element at which its character vanishes. -/
@[source_ref "Chapter5/Problem5.2.7" (role := primary)]
theorem FDRep.exists_character_eq_zero_of_simple (V : FDRep ℂ G) [Simple V]
    (h : 1 < Module.finrank ℂ V) : ∃ g : G, V.character g = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hβpos, hβlt⟩ := FDRep.normSqCharacterProduct_mem_Ioo V h hcon
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  obtain ⟨q, hq⟩ := RepresentationTheory.FiniteGroup.CharacterArithmetic.character_pairing_product_is_rat V
  rw [← hs_def] at hq
  -- `algebraMap ℚ ℂ q = ↑q` as a real, matched against the real product `β`.
  have hqcast : algebraMap ℚ ℂ q = ((q : ℝ) : ℂ) := by
    rw [Complex.ofReal_ratCast]; simp
  have hβeq : (q : ℝ) = ∏ g ∈ s, Complex.normSq (V.character g) := by
    have hC : ((q : ℝ) : ℂ) = ∏ g ∈ s, ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
      rw [← hqcast, hq]
      exact Finset.prod_congr rfl (fun g _ => char_mul_inv_eq_normSq V g)
    rw [← Complex.ofReal_prod] at hC
    exact_mod_cast hC
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := by rw [hβeq]; exact hβpos
    exact_mod_cast this
  have hq1 : q < 1 := by
    have : (q : ℝ) < 1 := by rw [hβeq]; exact hβlt
    exact_mod_cast this
  exact RepresentationTheory.FiniteGroup.CharacterArithmetic.character_pairing_product_not_rat_between_zero_one V (hs_def ▸ hq) hq0 hq1

end RepresentationTheory.FiniteGroup.RationalForms
