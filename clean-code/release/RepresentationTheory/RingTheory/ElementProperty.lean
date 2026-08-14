/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Element properties in rings

This file develops a ring-element property and its behavior under equivalences, products, centers,
Artinian decompositions, and finite-dimensional algebra constructions.
-/

set_option linter.dupNamespace false

universe u

namespace RepresentationTheory.RingTheory.ElementProperty
variable (R : Type u) [Ring R]

/-- A property of elements of a ring. -/
def ElementProperty (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ (∀ y : R, e * y = y * e) ∧
    ¬ ∃ e₁ e₂ : R, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧
      (∀ y, e₁ * y = y * e₁) ∧ (∀ y, e₂ * y = y * e₂) ∧ e₁ * e₂ = 0 ∧ e = e₁ + e₂

variable {R}

/-- In a commutative ring, the property is equivalent to being a nonzero idempotent such that every
idempotent absorbing into it is zero or equal to it. -/
theorem elementProperty_iff {A : Type*} [CommRing A] {e : A} :
    ElementProperty A e ↔
      e ≠ 0 ∧ IsIdempotentElem e ∧
        ∀ x : A, IsIdempotentElem x → x * e = x → x = 0 ∨ x = e := by
  constructor
  · rintro ⟨he0, hei, _, hns⟩
    refine ⟨he0, hei, fun x hx hxe => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hxe'⟩ := hcon
    refine hns ⟨x, e - x, hx0, ?_, hx, ?_, fun y => by ring, fun y => by ring, ?_, by ring⟩
    · exact fun h => hxe' (sub_eq_zero.mp h).symm
    · have hex : e * x = x := by rw [mul_comm]; exact hxe
      change (e - x) * (e - x) = e - x
      have : (e - x) * (e - x) = e * e - e * x - x * e + x * x := by ring
      rw [this, hei.eq, hx.eq, hex, hxe]; ring
    · change x * (e - x) = 0
      have : x * (e - x) = x * e - x * x := by ring
      rw [this, hxe, hx.eq]; ring
  · rintro ⟨he0, hei, hsub⟩
    refine ⟨he0, hei, fun y => by rw [mul_comm], ?_⟩
    rintro ⟨e₁, e₂, h1, h2, hi1, hi2, _, _, hor, hsum⟩
    have h1e : e₁ * e = e₁ := by
      rw [hsum, mul_add, hor, add_zero]; exact hi1.eq
    rcases hsub e₁ hi1 h1e with h | h
    · exact h1 h
    · apply h2
      have : e₂ = e - e₁ := by rw [hsum]; ring
      rw [this, h]; ring

/-- A ring equivalence sends an element satisfying the property to one satisfying the corresponding
property. -/
theorem ElementProperty.map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A ≃+* B) {e : A} (he : ElementProperty A e) :
    ElementProperty B (φ e) := by
  rw [elementProperty_iff] at he ⊢
  obtain ⟨h0, hi, hsub⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · simpa using (map_ne_zero_iff φ φ.injective).mpr h0
  · change φ e * φ e = φ e
    rw [← map_mul, hi.eq]
  · intro x hx hxe
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : IsIdempotentElem y := by
      have := hx.eq
      rw [← map_mul] at this
      exact φ.injective this
    have hye : y * e = y := by
      apply φ.injective
      rw [map_mul]; exact hxe
    rcases hsub y hy hye with h | h
    · left; rw [h, map_zero]
    · right; rw [h]

/-- A coordinate unit in a finite dependent product of fields satisfies the property. -/
theorem elementProperty_pi_single {ι : Type*} [Finite ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, Field (K i)] (i : ι) :
    ElementProperty (∀ j, K j) (Pi.single i 1) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [elementProperty_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : (Pi.single i (1 : K i)) i = (0 : ∀ j, K j) i := by rw [h]
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  · exact (CompleteOrthogonalIdempotents.single K).idem i
  · intro x hx hxe
    have hxidem : ∀ j, x j * x j = x j := fun j => congr_fun hx.eq j
    have hxne : ∀ j, j ≠ i → x j = 0 := by
      intro j hj
      have := congr_fun hxe j
      rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero] at this
      exact this.symm
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hxidem i) with hi0 | hi1
    · left
      ext j
      by_cases hj : j = i
      · subst hj; rw [hi0]; rfl
      · rw [hxne j hj]; rfl
    · right
      ext j
      by_cases hj : j = i
      · subst hj; rw [hi1, Pi.single_eq_same]
      · rw [hxne j hj, Pi.single_eq_of_ne hj]

/-- An Artinian commutative ring has a complete orthogonal idempotent family whose entries are
exactly the elements satisfying the property. -/
theorem exists_completeOrthogonalIdempotents_elementProperty_of_isArtinianRing
    (A : Type u) [CommRing A] [IsArtinianRing A] :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → A),
      CompleteOrthogonalIdempotents e ∧
      (∀ i, ElementProperty A (e i)) ∧
      (∀ f, ElementProperty A f → ∃ i, e i = f) := by
  classical
  let ι := MaximalSpectrum A
  haveI : Fintype ι := Fintype.ofFinite ι
  let K : ι → Type _ := fun I => A ⧸ I.asIdeal
  letI hK : ∀ I : ι, Field (K I) := fun I => @Ideal.Quotient.field A _ I.asIdeal I.isMaximal
  let φ : (A ⧸ nilradical A) ≃+* (∀ I : ι, K I) :=
    (IsArtinianRing.quotNilradicalEquivPi A).toRingEquiv
  let ψ : A →+* (∀ I : ι, K I) :=
    φ.toRingHom.comp (Ideal.Quotient.mk (nilradical A))
  have hψ_surj : Function.Surjective ψ :=
    φ.surjective.comp Ideal.Quotient.mk_surjective
  have hker : ∀ x ∈ RingHom.ker ψ, IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hφ : φ ((Ideal.Quotient.mk (nilradical A)) x) = 0 := hx
    have hx0 := φ.map_eq_zero_iff.mp hφ
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical] at hx0
    exact hx0
  have hp := CompleteOrthogonalIdempotents.single K
  obtain ⟨e, he, hψe⟩ :=
    hp.lift_of_isNilpotent_ker ψ hker (fun i => RingHom.mem_range.mpr (hψ_surj _))
  have hψei : ∀ i, ψ (e i) = Pi.single i 1 := fun i => congr_fun hψe i
  have hp_indec := fun i => elementProperty_pi_single K i
  have he_indec : ∀ i, ElementProperty A (e i) := by
    intro i
    refine ⟨?_, he.idem i, fun y => by rw [mul_comm], ?_⟩
    · intro h
      have hz : ψ (e i) = 0 := by rw [h, map_zero]
      rw [hψei i] at hz
      exact (hp_indec i).1 hz
    · rintro ⟨e₁, e₂, h1, h2, hi1, hi2, _, _, hor, hsum⟩
      have key : ψ e₁ = 0 ∨ ψ e₂ = 0 := by
        by_contra hcon
        push Not at hcon
        have hidem1 : IsIdempotentElem (ψ e₁) := by
          change ψ e₁ * ψ e₁ = ψ e₁; rw [← map_mul, hi1.eq]
        have hidem2 : IsIdempotentElem (ψ e₂) := by
          change ψ e₂ * ψ e₂ = ψ e₂; rw [← map_mul, hi2.eq]
        have hortho : ψ e₁ * ψ e₂ = 0 := by rw [← map_mul, hor, map_zero]
        have hsum' : ψ e₁ + ψ e₂ = ψ (e i) := by rw [← map_add, hsum]
        exact (hp_indec i).2.2.2 ⟨ψ e₁, ψ e₂, hcon.1, hcon.2, hidem1, hidem2,
          fun y => by rw [mul_comm], fun y => by rw [mul_comm], hortho,
          (hsum'.trans (hψei i)).symm⟩
      rcases key with h | h
      · exact h1 (IsIdempotentElem.eq_zero_of_isNilpotent hi1
          (hker e₁ (RingHom.mem_ker.mpr h)))
      · exact h2 (IsIdempotentElem.eq_zero_of_isNilpotent hi2
          (hker e₂ (RingHom.mem_ker.mpr h)))
  have surj : ∀ f, ElementProperty A f → ∃ i, e i = f := by
    intro f hf
    rw [elementProperty_iff] at hf
    obtain ⟨hf0, hfi, hfsub⟩ := hf
    have hsum : ∑ i, f * e i = f := by rw [← Finset.mul_sum, he.complete, mul_one]
    have hidem : ∀ i, IsIdempotentElem (f * e i) := by
      intro i
      change (f * e i) * (f * e i) = f * e i
      have : (f * e i) * (f * e i) = (f * f) * (e i * e i) := by ring
      rw [this, hfi.eq, (he.idem i).eq]
    have hbelow : ∀ i, (f * e i) * f = f * e i := by
      intro i
      have : (f * e i) * f = (f * f) * e i := by ring
      rw [this, hfi.eq]
    have hne : ∃ i, f * e i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (by rw [← hsum]; exact Finset.sum_eq_zero (fun i _ => hc i))
    obtain ⟨i, hi⟩ := hne
    rcases hfsub (f * e i) (hidem i) (hbelow i) with h | h
    · exact absurd h hi
    · refine ⟨i, ?_⟩
      obtain ⟨_, _, hei_sub⟩ := (elementProperty_iff).mp (he_indec i)
      rcases hei_sub f hfi h with hh | hh
      · exact absurd hh hf0
      · exact hh.symm
  exact ⟨ι, inferInstance, e, he, he_indec, surj⟩

/-- An element of the center subalgebra satisfies the property there if and only if its underlying
ring element does. -/
theorem elementProperty_center_iff
    {k : Type*} [Field k] [Algebra k R] (z : ↥(Subalgebra.center k R)) :
    ElementProperty R (z : R) ↔
      ElementProperty ↥(Subalgebra.center k R) z := by
  set v := Subalgebra.val (Subalgebra.center k R) with hv
  have hcentral : ∀ w : ↥(Subalgebra.center k R), ∀ y : R, (w : R) * y = y * (w : R) :=
    fun w y => (Subalgebra.mem_center_iff.mp w.property y).symm
  constructor
  · rintro ⟨h0, hi, _, hns⟩
    refine ⟨fun h => h0 (by rw [h]; rfl), Subtype.ext hi.eq, fun y => mul_comm z y, ?_⟩
    rintro ⟨z₁, z₂, hz1, hz2, hzi1, hzi2, _, _, hzor, hzsum⟩
    exact hns ⟨(z₁ : R), (z₂ : R),
      fun h => hz1 (Subtype.ext h), fun h => hz2 (Subtype.ext h),
      congrArg v hzi1.eq, congrArg v hzi2.eq, hcentral z₁, hcentral z₂,
      congrArg v hzor, congrArg v hzsum⟩
  · rintro ⟨h0, hi, _, hns⟩
    refine ⟨fun h => h0 (Subtype.ext h), congrArg v hi.eq, hcentral z, ?_⟩
    rintro ⟨e₁, e₂, h1, h2, hi1, hi2, hc1, hc2, hor, hsum⟩
    have hm1 : e₁ ∈ Subalgebra.center k R := Subalgebra.mem_center_iff.mpr (fun b => (hc1 b).symm)
    have hm2 : e₂ ∈ Subalgebra.center k R := Subalgebra.mem_center_iff.mpr (fun b => (hc2 b).symm)
    exact hns ⟨⟨e₁, hm1⟩, ⟨e₂, hm2⟩,
      fun h => h1 (congrArg v h), fun h => h2 (congrArg v h),
      Subtype.ext hi1.eq, Subtype.ext hi2.eq, fun y => mul_comm _ y, fun y => mul_comm _ y,
      Subtype.ext hor, Subtype.ext hsum⟩

/-- A finite-dimensional algebra has a family summing to one whose distinct entries multiply to
zero and whose entries are exactly the elements satisfying the property. -/
theorem exists_orthogonalFamily_elementProperty_of_finiteDimensional
    {k : Type*} [Field k] [Algebra k R] [FiniteDimensional k R] :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → R),
      (∑ i, e i = 1) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ i, ElementProperty R (e i)) ∧
      (∀ f, ElementProperty R f → ∃ i, e i = f) := by
  classical
  letI : IsArtinianRing ↥(Subalgebra.center k R) :=
    isArtinian_of_tower k (inferInstance : IsArtinian k ↥(Subalgebra.center k R))
  obtain ⟨ι, _, z, hz, hz_indec, hz_surj⟩ :=
    exists_completeOrthogonalIdempotents_elementProperty_of_isArtinianRing ↥(Subalgebra.center k R)
  refine ⟨ι, ‹Fintype ι›, fun i => (z i : R), ?_, ?_, ?_, ?_⟩
  · change ∑ i, Subalgebra.val (Subalgebra.center k R) (z i) = 1
    rw [← map_sum, hz.complete, map_one]
  · intro i j hij
    change Subalgebra.val (Subalgebra.center k R) (z i)
      * Subalgebra.val (Subalgebra.center k R) (z j) = 0
    rw [← map_mul, hz.ortho hij, map_zero]
  · intro i
    exact (elementProperty_center_iff (z i)).mpr (hz_indec i)
  · intro f hf
    have hfc : f ∈ Subalgebra.center k R :=
      Subalgebra.mem_center_iff.mpr (fun b => (hf.2.2.1 b).symm)
    have hzf : ElementProperty ↥(Subalgebra.center k R) ⟨f, hfc⟩ :=
      (elementProperty_center_iff (⟨f, hfc⟩ : ↥(Subalgebra.center k R))).mp hf
    obtain ⟨i, hi⟩ := hz_surj ⟨f, hfc⟩ hzf
    exact ⟨i, congrArg (Subalgebra.val _) hi⟩

/-- The elements satisfying the property in a finite-dimensional algebra form a finite type. -/
theorem finite_elementProperty_of_finiteDimensional
    (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Finite {e : R // ElementProperty R e} := by
  obtain ⟨ι, _, e, _, _, he_indec, he_surj⟩ :=
    exists_orthogonalFamily_elementProperty_of_finiteDimensional (R := R) (k := k)
  refine Finite.of_surjective (fun i => (⟨e i, he_indec i⟩ : {e : R // _})) ?_
  rintro ⟨f, hf⟩
  obtain ⟨i, hi⟩ := he_surj f hf
  exact ⟨i, Subtype.ext hi⟩

end RepresentationTheory.RingTheory.ElementProperty
