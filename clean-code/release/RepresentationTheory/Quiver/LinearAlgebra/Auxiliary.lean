/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.QuiverRepresentation.Auxiliary
import Mathlib.LinearAlgebra.Isomorphisms

section Reversal

/-- Converts the first displayed auxiliary input at a vertex into the second. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) :
    @RepresentationTheory.QuiverVertexPredicates.vertexCondition Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i j i at e
  by_cases hj : j = i
  · rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq hj rfl] at e
    rw [hj] at e; exact (hi i).false e
  · rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hj rfl] at e
    exact (hi j).false e

/-- Converts the second displayed auxiliary input at a vertex into the first. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) :
    @RepresentationTheory.QuiverVertexPredicates.vertexProperty Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i i j at e
  by_cases hj : j = i
  · rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq rfl hj] at e
    rw [hj] at e; exact (hi i).false e
  · rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hj] at e
    exact (hi j).false e

end Reversal

section Iso

/-- Auxiliary data parametrized by two values of the displayed type. -/
structure RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) : Type _ where

  /-- The linear equivalence at a vertex supplied by auxiliary data. -/
  linearEquivAt : ∀ v : Q, ρ₁.obj v ≃ₗ[k] ρ₂.obj v

  /-- The vertexwise linear equivalences commute with the displayed maps along quiver morphisms. -/
  linearEquivAt_map : ∀ {a b : Q} (e : a ⟶ b) (x : ρ₁.obj a),
    (linearEquivAt b) (ρ₁.map e x) = ρ₂.map e ((linearEquivAt a) x)

@[ext]
private theorem Quiver.ext' {V : Type*} {inst₁ inst₂ : Quiver V}
    (h : ∀ a b, @Quiver.Hom V inst₁ a b = @Quiver.Hom V inst₂ a b) :
    inst₁ = inst₂ := by
  cases inst₁; cases inst₂
  congr 1; funext a b; exact h a b

/-- The displayed quiver structure indexed by a vertex is equal to the ambient quiver structure. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq
    (Q : Type*) [DecidableEq Q] [inst : Quiver Q] (i : Q) :
    @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i = inst := by
  apply Quiver.ext'
  intro a b
  change @RepresentationTheory.QuiverVertexReversal.reversedAtHom Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a b = (a ⟶ b)

  by_cases ha : a = i <;> by_cases hb : b = i
  ·
    trans @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b
    · exact @RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a b ha hb
    · change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i a b = (a ⟶ b)
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq ha hb
  ·
    trans @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) b i
    · exact @RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a b ha hb
    · change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i b i = (a ⟶ b)
      rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hb rfl]
      exact congrArg (· ⟶ b) ha.symm
  ·
    trans @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a
    · exact @RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a b ha hb
    · change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i i a = (a ⟶ b)
      rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl ha]
      exact congrArg (a ⟶ ·) hb.symm
  ·
    trans @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b
    · exact @RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a b ha hb
    · change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i a b = (a ⟶ b)
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb

/-- An auxiliary endomap of the displayed type parametrized by a vertex. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryAt
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q}
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q :=
  RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q i ▸ ρ

/-- A compatible family of vertexwise linear equivalences yields nonempty auxiliary data after the displayed transport. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.nonempty_auxiliaryData_ofLinearEquivAt
    {k : Type*} [CommSemiring k] {Q : Type*}
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q _ inst₁}
    {ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q _ inst₂}
    (linearEquivAt : ∀ v : Q,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _ inst₁ ρ₁ v ≃ₗ[k]
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _ inst₂ ρ₂ v)
    (linearEquivAt_map : ∀ {a b : Q} (e : @Quiver.Hom Q inst₂ a b)
      (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _ inst₁ ρ₁ a),
      (linearEquivAt b)
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _ inst₁ ρ₁ a b (h.symm ▸ e) x) =
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _ inst₂ ρ₂ a b e ((linearEquivAt a) x)) :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ Q inst₂ (h ▸ ρ₁) ρ₂) := by
  subst h; exact ⟨⟨linearEquivAt, linearEquivAt_map⟩⟩

end Iso

section MapIso

/-- A family of linear equivalences induces a linear equivalence between the corresponding direct sums. -/
noncomputable def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv
    {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]
    {M₁ M₂ : ι → Type*}
    [∀ a, AddCommMonoid (M₁ a)] [∀ a, Module k (M₁ a)]
    [∀ a, AddCommMonoid (M₂ a)] [∀ a, Module k (M₂ a)]
    (e : ∀ a, M₁ a ≃ₗ[k] M₂ a) :
    DirectSum ι M₁ ≃ₗ[k] DirectSum ι M₂ :=
  DFinsupp.mapRange.linearEquiv e

/-- The displayed direct-sum linear equivalence sends an inserted vector to the insertion of its image in the same indexed summand. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv_lof
    {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]
    {M₁ M₂ : ι → Type*}
    [∀ a, AddCommMonoid (M₁ a)] [∀ a, Module k (M₁ a)]
    [∀ a, AddCommMonoid (M₂ a)] [∀ a, Module k (M₂ a)]
    (e : ∀ a, M₁ a ≃ₗ[k] M₂ a)
    (a : ι) (v : M₁ a) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv e (DirectSum.lof k ι M₁ a v) =
      DirectSum.lof k ι M₂ a (e a v) := by
  change (DFinsupp.mapRange.linearEquiv e) (DFinsupp.single a v) =
    DFinsupp.single a ((e a) v)
  ext b
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply,
      DFinsupp.single_apply, DFinsupp.single_apply]
  split
  · next h => subst h; rfl
  · exact map_zero _

/-- Under the displayed compatibility hypotheses, the given linear equivalence maps the range of one displayed linear map to the range of the other. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryMapRangeEq
    {k : Type*} [CommRing k] {Q : Type*} [Quiver Q]
    {i : Q}
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] [DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (ψ₁ : ρ₁.obj i →ₗ[k] DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.fst))
    (hψ₁ : ψ₁ = ∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
        (DirectSum.lof k _ (fun a => ρ₁.obj a.fst) a).comp (ρ₁.map a.2))
    (ψ₂ : ρ₂.obj i →ₗ[k] DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.fst))
    (hψ₂ : ψ₂ = ∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
        (DirectSum.lof k _ (fun a => ρ₂.obj a.fst) a).comp (ρ₂.map a.2))
    (F : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.fst) ≃ₗ[k]
         DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.fst))
    (hF : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (v : ρ₁.obj a.fst),
        F (DirectSum.lof k _ _ a v) = DirectSum.lof k _ _ a (σ.linearEquivAt a.fst v)) :
    Submodule.map F.toLinearMap (LinearMap.range ψ₁) = LinearMap.range ψ₂ := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    refine ⟨σ.linearEquivAt i v, ?_⟩
    rw [hψ₁, hψ₂]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    congr 1; ext1 a
    rw [hF]
    congr 1
    exact (σ.linearEquivAt_map a.2 v).symm
  · rintro ⟨w, rfl⟩
    refine ⟨ψ₁ ((σ.linearEquivAt i).symm w), ⟨(σ.linearEquivAt i).symm w, rfl⟩, ?_⟩
    rw [hψ₁, hψ₂]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    congr 1; ext1 a
    rw [hF]
    congr 1
    rw [σ.linearEquivAt_map a.2, LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in

/-- Constructs a linear equivalence between the two displayed modules. -/
noncomputable def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (i = i)) :
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₁ i i d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₂ i i d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₁ i i d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₂ i i d
    RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ₁ i i d ≃ₗ[k]
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ₂ i i d :=
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₁ i i d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₂ i i d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₁ i i d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₂ i i d
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ₁ i i d ≃ₗ[k]
        RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ₂ i i d)
    d
    (fun hii => absurd rfl hii)
    (fun _ =>
      Submodule.Quotient.equiv (LinearMap.range (ρ₁.outgoingDirectSumMap i))
        (LinearMap.range (ρ₂.outgoingDirectSumMap i))
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst))
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryMapRangeEq σ _ rfl _ rfl _
          (fun a v => RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv_lof
            (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst) a v)))

set_option maxHeartbeats 1600000 in

private noncomputable def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) v ≃ₗ[k]
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₂) v := by
  by_cases hv : v = i
  · rw [eq_comm] at hv; subst hv
    exact RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv hi σ (inst i i)
  · exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ₁ v hv).trans
      ((σ.linearEquivAt v).trans (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ₂ v hv).symm)

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.transformedVertexEquivQuotient_transformedQuotientMap
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (d : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ d) =
      Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i)) d := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearEquiv.heq_apply
    {k : Type*} [CommSemiring k]
    {α α' : Type u} {β β' : Type v}
    {acα : AddCommMonoid α} {acβ : AddCommMonoid β}
    {acα' : AddCommMonoid α'} {acβ' : AddCommMonoid β'}
    {mα : @Module k α _ acα} {mβ : @Module k β _ acβ}
    {mα' : @Module k α' _ acα'} {mβ' : @Module k β' _ acβ'}
    (hα : α = α') (hβ : β = β')
    (hacα : HEq acα acα') (hacβ : HEq acβ acβ')
    (hmα : HEq mα mα') (hmβ : HEq mβ mβ')
    {e : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _ α β acα acβ mα mβ}
    {e' : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _ α' β' acα' acβ' mα' mβ'}
    (he : HEq e e') {a : α} {a' : α'} (ha : HEq a a') :
    HEq (e a) (e' a') := by
  subst hα; subst hβ
  cases hacα; cases hacβ; cases hmα; cases hmβ; cases he; cases ha
  rfl

open Classical in
set_option maxHeartbeats 1600000 in

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv_factor
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (d : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₂
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i
          (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d)) =
      Submodule.mkQ (LinearMap.range (ρ₂.outgoingDirectSumMap i))
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst) d) := by
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h

  set ψ₁ := ρ₁.outgoingDirectSumMap i with hψ₁def
  set ψ₂ := ρ₂.outgoingDirectSumMap i with hψ₂def
  set F := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst)
    with hFdef

  have hmaps : Submodule.map F.toLinearMap (LinearMap.range ψ₁) = LinearMap.range ψ₂ := by
    rw [hψ₁def, hψ₂def, hFdef]
    exact RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryMapRangeEq σ _ rfl _ rfl _
      (fun a v => RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv_lof
        (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst) a v)

  have heq_chart₁ : HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₁))
      (id : ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.outgoingDirectSumMap i)) →
        ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) ⧸
          LinearMap.range (ρ₁.outgoingDirectSumMap i))) := by
    change HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient ρ₁ (inst i i))) _
    rw [h_di]
    rfl
  have heq_chart₂ : HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₂))
      (id : ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) ⧸
        LinearMap.range (ρ₂.outgoingDirectSumMap i)) →
        ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) ⧸
          LinearMap.range (ρ₂.outgoingDirectSumMap i))) := by
    change HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient ρ₂ (inst i i))) _
    rw [h_di]
    rfl

  have hmapobj : HEq (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i)
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv hi σ (Decidable.isTrue rfl)) := by
    unfold RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt
    simp only [dite_true]
    congr 1

  have hAtAt : (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv hi σ
      (Decidable.isTrue (rfl : i = i))) =
      Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps := rfl

  have hobj : HEq (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i)
      (Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps) :=
    hmapobj.trans (heq_of_eq hAtAt)

  have hz : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d)
      (Submodule.mkQ (LinearMap.range ψ₁) d) := by
    have h1 : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₁
        (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d)) (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d) :=
      RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₁) rfl heq_chart₁
        (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₁) _).symm
        |>.trans (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₁) _)
    rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.transformedVertexEquivQuotient_transformedQuotientMap hi ρ₁] at h1
    exact h1.symm

  have hac₁ : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₁ i i (inst i i))
      (Submodule.Quotient.addCommGroup
        (p := LinearMap.range (ρ₁.outgoingDirectSumMap i))).toAddCommMonoid := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hac₂ : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ₂ i i (inst i i))
      (Submodule.Quotient.addCommGroup
        (p := LinearMap.range (ρ₂.outgoingDirectSumMap i))).toAddCommMonoid := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hmo₁ : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₁ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ₁.outgoingDirectSumMap i))) := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hmo₂ : HEq (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ₂ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ₂.outgoingDirectSumMap i))) := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl

  have hmapw : HEq (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d))
      (Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps
        (Submodule.mkQ (LinearMap.range ψ₁) d)) :=
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearEquiv.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₁)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₂) hac₁ hac₂ hmo₁ hmo₂ hobj hz

  have hfin : RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₂
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i
        (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d)) =
      Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps
        (Submodule.mkQ (LinearMap.range ψ₁) d) := by
    have h := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ₂) rfl heq_chart₂ hmapw

    simpa using eq_of_heq h
  rw [hfin]

  rw [Submodule.Quotient.equiv_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.mkQ_apply]
  rfl

open Classical in
set_option maxHeartbeats 1600000 in

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv_transformedQuotientMap
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (d : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ i
        (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₁ d) =
      RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ₂
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst) d) := by
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)

  apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ₂).injective
  rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.transformedVertexEquivQuotient_transformedQuotientMap hi ρ₂]
  exact RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv_factor hi σ d

set_option maxHeartbeats 3200000 in

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt_map
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {a b : Q} (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) a) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ b
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) a b e x) =
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₂) a b e
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ a x) := by
  have hi_sink := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi
  by_cases ha : a = i
  · subst ha; exact ((hi_sink b).false e).elim
  · by_cases hb : b = i
    · rw [eq_comm] at hb; subst hb
      letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _

      rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished hi ρ₁ ha e x]
      rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished hi ρ₂ ha e]

      rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryLinearEquiv_transformedQuotientMap hi σ]
      rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.DirectSum.auxiliaryLinearEquiv_lof (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => σ.linearEquivAt a.fst)]

      congr 1

      simp only [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt, dif_neg ha,
        LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    ·

      simp only [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt, dif_neg ha, dif_neg hb,
        LinearEquiv.trans_apply]

      rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne hi ρ₁ ha hb e x]

      rw [LinearEquiv.symm_apply_eq]

      rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne hi ρ₂ ha hb e]
      rw [LinearEquiv.apply_symm_apply]
      exact σ.linearEquivAt_map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e)
        ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ₁ a ha) x)

/-- Applying the displayed operation to both arguments yields nonempty auxiliary data. -/
noncomputable def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataNonemptyAfterOperation
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [instQ : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (σ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k (inferInstanceAs (CommSemiring k))
      Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₂)) :=
  ⟨@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.mk k _ Q
    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
    (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁)
    (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₂)
    (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt hi σ)
    (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataLinearEquivAt_map hi σ)⟩

end MapIso

section Helpers

/-- For the supplied auxiliary input, the first projection of every displayed element differs from the specified vertex. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i i j at e
  by_cases hj : j = i
  · rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq rfl hj] at e
    rw [hj] at e; exact ((hi i).false e).elim
  · exact hj

private def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.reversedAtHom_from_selected_eq
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i i j = (j ⟶ i) := by
  unfold RepresentationTheory.QuiverVertexReversal.reversedAtHom
  cases inst i i with
  | isFalse h => exact absurd rfl h
  | isTrue _ =>
    cases inst j i with
    | isTrue h => exact absurd h hj
    | isFalse _ => rfl

/-- The displayed quiver morphism from an element's first projection to the specified vertex. -/
def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) : a.fst ⟶ i :=
  RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne hi a) a.snd

/-- Maps an element of one displayed type to an element of another using the supplied auxiliary input. -/
def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (b : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) :
    @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i :=
  have hne : b.fst ≠ i := fun h =>
    (hi i).false (cast (congrArg (· ⟶ i) h) b.snd)
  ⟨b.fst, cast (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.reversedAtHom_from_selected_eq hne).symm b.snd⟩

set_option maxHeartbeats 800000 in

private theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryReverseHom_eq_cast_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i)
    (e : RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i i j) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom hj e =
    cast (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.reversedAtHom_from_selected_eq hj) e :=

  eq_of_heq ((cast_heq (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hj) e).trans
    (cast_heq (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.reversedAtHom_from_selected_eq hj) e).symm)

/-- The displayed quiver morphism of an auxiliary-map image is the second projection of the original pair. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom_auxiliaryMap
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (b : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap hi b) = b.2 :=
  eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- The auxiliary map preserves the first projection. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (b : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) :
    (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap hi b).fst = b.fst := by
  simp [auxiliaryMap]

/-- Applying the auxiliary map to the pair built from an element's first projection and the displayed quiver morphism returns that element. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap_mk_auxiliaryHom
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (x : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap hi
      ⟨x.fst, RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi x⟩ = x := by
  obtain ⟨j, e⟩ := x
  have hji : j ≠ i := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne hi ⟨j, e⟩
  refine Sigma.ext rfl ?_
  simp only [auxiliaryMap, auxiliaryHom]
  rw [auxiliaryReverseHom_eq_cast_def]
  apply heq_of_eq
  rw [cast_cast]
  exact cast_eq _ _

/-- Constructs an equivalence between two displayed types from the supplied auxiliary input. -/
def RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) :
    @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i ≃
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i where
  toFun x := ⟨x.fst, RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi x⟩
  invFun b := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap hi b
  left_inv x := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap_mk_auxiliaryHom hi x
  right_inv b := by
    refine Sigma.ext (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap_fst hi b) ?_
    exact heq_of_eq (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom_auxiliaryMap hi b)

/-- Under the displayed surjectivity and preimage-existence hypotheses, the given linear map from a direct sum is surjective. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearMap.surjective_of_auxiliaryPreimages
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [Finite (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.auxiliaryDirectSumMap i))
    {M : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i → Type*}
    [∀ a, AddCommMonoid (M a)] [∀ a, Module k (M a)]
    (Φ : DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) M →ₗ[k] ρ.obj i)
    (hΦ_basic : ∀ (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) (v : ρ.obj b.fst),
      ∃ z, Φ z = ρ.map b.2 v) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)

  suffices h : ∀ x, (ρ.auxiliaryDirectSumMap i) x ∈ Set.range Φ by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    obtain ⟨z, hz⟩ := h x
    exact ⟨z, by rw [hz, hx]⟩
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp [map_zero]⟩
  | of b v =>
    obtain ⟨z, hz⟩ := hΦ_basic b v
    refine ⟨z, ?_⟩

    rw [hz]

    delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryDirectSumMap
    erw [DirectSum.toModule_lof]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add]
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩

set_option maxHeartbeats 3200000 in

/-- The displayed finite sum is zero. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliarySum_eq_zero
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i) :
    ∑ x : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i,
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _ inst ρ x.fst i
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom Q _ inst i hi x))
      ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ x.fst
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi x))
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i x.fst x.snd w)) = 0 := by

  simp_rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_from_selected hi ρ]

  change ∑ x : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i,
    ρ.map (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi x)
      (DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1)
        ⟨x.fst, RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi x⟩
        ((ρ.auxiliaryDirectSumMap i).ker.subtype (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ w))) = 0

  classical
  haveI : Fintype (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) :=
    Fintype.ofEquiv _ (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv hi)
  set y := (ρ.auxiliaryDirectSumMap i).ker.subtype (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ w) with hy_def

  let g : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i → ρ.obj i :=
    fun b => ρ.map b.2 (DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
      (fun a => ρ.obj a.1) b y)
  change ∑ x, g (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv hi x) = 0

  rw [(RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv hi).bijective.sum_comp g]

  change ∑ b : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i,
    ρ.map b.2 (DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
      (fun a => ρ.obj a.1) b y) = 0

  rw [show ∑ b : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i,
      ρ.map b.2 (DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
        (fun a => ρ.obj a.1) b y) = (ρ.auxiliaryDirectSumMap i) y from by
    symm
    delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryDirectSumMap
    change (DirectSum.toModule k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (ρ.obj i)
      (fun a => ρ.map a.2)) y = _
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, Finset.sum_const_zero]
    | of i x =>
      erw [DirectSum.toModule_lof]
      rw [Finset.sum_eq_single i]
      · erw [DirectSum.component.lof_self]
      · intro b _ hb
        erw [DirectSum.component.of]; rw [dif_neg (Ne.symm hb), map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    | add x y hx hy =>
      simp only [map_add, hx, hy, Finset.sum_add_distrib]]

  exact (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ w).property

set_option maxHeartbeats 400000 in

/-- An injective map followed by a surjective map has range equal to kernel when the range lies in the kernel and the endpoint finranks add to the middle finrank. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearMap.auxiliaryRangeEqKer
    {k : Type*} [Field k]
    {A B C : Type*}
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup C] [Module k C] [FiniteDimensional k C]
    {ψ' : A →ₗ[k] B} {Φ' : B →ₗ[k] C}
    (hfwd : ψ'.range ≤ Φ'.ker)
    (hΦ_surj : Function.Surjective Φ')
    (hψ_inj : Function.Injective ψ')
    (hdim : Module.finrank k A + Module.finrank k C = Module.finrank k B) :
    ψ'.range = Φ'.ker := by
  apply Submodule.eq_of_le_of_finrank_eq hfwd

  have hr : Module.finrank k ↥ψ'.range = Module.finrank k A :=
    LinearMap.finrank_range_of_inj hψ_inj

  have hk : Module.finrank k ↥Φ'.ker + Module.finrank k C = Module.finrank k B := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ'
    rw [LinearMap.range_eq_top.mpr hΦ_surj, finrank_top] at h1
    omega

  omega

end Helpers

section ReversedArrowCasts

/-- For a morphism whose endpoints are both distinct from the specified vertex, the displayed auxiliary map agrees with the indicated cast. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_eq_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e =
    cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) e :=

  rfl

set_option maxHeartbeats 1600000 in

/-- Applying the displayed auxiliary map twice to a morphism whose endpoints are distinct from the specified vertex returns that morphism. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_involutive
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q inst a b) :
    @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom Q inst_dec inst i a b ha hb
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a b ha hb
        ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e)) = e := by

  have h1 : ∀ (y : @Quiver.Hom Q (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) a b),
      HEq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom Q inst_dec inst i a b ha hb y) y := by
    intro y; rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_eq_cast]; exact cast_heq _ _
  have h2 : ∀ (z : @Quiver.Hom Q
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i) a b),
      HEq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a b ha hb z) z := by
    intro z
    rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_eq_cast Q inst_dec
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a b ha hb z]
    exact cast_heq _ _

  have h3 : HEq ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a b) e
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm
  exact eq_of_heq ((h1 _).trans ((h2 _).trans h3))

/-- For a morphism from the specified vertex to a distinct vertex, the displayed auxiliary map agrees with the indicated cast. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapFrom_eq_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i b) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom hb e =
    cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (i := i) rfl hb) e :=

  rfl

/-- For a morphism from a distinct vertex to the specified vertex, the displayed auxiliary map agrees with the indicated cast. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e =
    cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq (i := i) ha rfl) e :=

  rfl

set_option maxHeartbeats 1600000 in

/-- The displayed quiver morphism of the pair built using the second auxiliary map is the original morphism. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom_mk_auxiliaryMapSecond
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q inst a i) :
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom hi
      ⟨a, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a ha
        ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e)⟩ = e := by
  simp only [auxiliaryHom]
  apply eq_of_heq

  have h1 : ∀ (y : @Quiver.Hom Q (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a),
      HEq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom Q inst_dec inst i a
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne hi ⟨a, y⟩) y) y := by
    intro y
    rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapFrom_eq_cast]
    exact cast_heq _ _

  have h2 : ∀ (z : @Quiver.Hom Q
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i) a i),
      HEq (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a ha z) z := by
    intro z
    rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast Q inst_dec
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i a ha z]
    exact cast_heq _ _

  have h3 : HEq ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a i) e
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

set_option maxHeartbeats 1600000 in

/-- Under the displayed auxiliary input, applying the second displayed map after the first to a morphism from the specified vertex returns that morphism. -/
theorem RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapSecond_apply_auxiliaryMapFirst
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    {b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q inst i b) :
    @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q inst_dec inst i b hb
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i b hb
        ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e)) = e := by
  apply eq_of_heq

  have h1 : ∀ (y : @Quiver.Hom Q (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) b i),
      HEq (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q inst_dec inst i b hb y) y := by
    intro y
    rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast]
    exact cast_heq _ _

  have h2 : ∀ (z : @Quiver.Hom Q
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i) i b),
      HEq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom Q inst_dec
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i b hb z) z := by
    intro z
    rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapFrom_eq_cast Q inst_dec
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i b hb z]
    exact cast_heq _ _

  have h3 : HEq ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom i b) e
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

end ReversedArrowCasts
