/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.FieldAlgebraProperties
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Auxiliary conditions on finite algebras
-/

universe u

namespace RepresentationTheory

/-- Converts the second auxiliary condition into the first. -/
theorem FieldAlgebraProperties.fieldAlgebraProperty'.toAuxiliary {k : Type u} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    (h : FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k A) :
    FieldAlgebraProperties.fieldAlgebraProperty k A := by
  intro xq yq
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yq
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
  refine Submodule.mem_sInf.mpr fun m hm => ?_
  haveI : IsSimpleModule A (A ⧸ m) := isSimpleModule_iff_isCoatom.mpr hm
  let v : A ⧸ m := Submodule.Quotient.mk (1 : A)
  have hv : v ≠ 0 := by
    rw [Ne, show v = Submodule.Quotient.mk (1 : A) from rfl, Submodule.Quotient.mk_eq_zero]
    exact fun h1 => hm.1 ((Ideal.eq_top_iff_one m).mpr h1)
  have hone : Module.finrank k (A ⧸ m) = 1 := h (A ⧸ m)
  rw [finrank_eq_one_iff_of_nonzero' v hv] at hone
  have hscalar : ∀ a : A, ∃ c : k, a • v = c • v := fun a =>
    let ⟨c, hc⟩ := hone (a • v); ⟨c, hc.symm⟩
  obtain ⟨cx, hcx⟩ := hscalar x
  obtain ⟨cy, hcy⟩ := hscalar y
  have hkill : (x * y - y * x) • v = 0 := by
    rw [sub_smul, mul_smul, mul_smul, hcx, hcy, smul_comm y cx v, smul_comm x cy v,
      hcx, hcy, smul_comm cx cy v, sub_self]
  rwa [show v = Submodule.Quotient.mk (1 : A) from rfl, ← Submodule.Quotient.mk_smul,
    smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at hkill

/-- Converts the first auxiliary condition into the second over an algebraically closed field
for a finite algebra. -/
theorem FieldAlgebraProperties.fieldAlgebraProperty.toAuxiliaryOfIsAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    (h : FieldAlgebraProperties.fieldAlgebraProperty k A) :
    FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k A := by
  intro M _instACG _instMod _instSimple _instModk _instST
  have hcomm_act : ∀ (r s : A) (m : M), r • (s • m) = s • (r • m) := by
    intro r s m
    have hcomm : r * s - s * r ∈ Ring.jacobson A := by
      have hq := h (Ideal.Quotient.mk _ r) (Ideal.Quotient.mk _ s)
      rwa [← map_mul, ← map_mul, Ideal.Quotient.eq] at hq
    have hann : r * s - s * r ∈ Module.annihilator A M :=
      IsSemisimpleModule.jacobson_le_annihilator A M hcomm
    have h0 := Module.mem_annihilator.mp hann m
    rwa [sub_smul, mul_smul, mul_smul, sub_eq_zero] at h0
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hspan : Submodule.span A {m₀} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {m₀}) with hb | ht
    · exfalso
      have hmem : m₀ ∈ (⊥ : Submodule A M) := hb ▸ Submodule.subset_span rfl
      rw [Submodule.mem_bot] at hmem
      exact hm₀ hmem
    · exact ht
  have hsurj : ∀ m : M, ∃ r : A, r • m₀ = m := fun m =>
    Submodule.mem_span_singleton.mp (hspan ▸ (Submodule.mem_top : m ∈ ⊤))
  haveI : FiniteDimensional k M := by
    let f : A →ₗ[k] M :=
      { toFun := fun r => r • m₀
        map_add' := fun a b => add_smul a b m₀
        map_smul' := fun c a => by simp only [RingHom.id_apply]; rw [← smul_assoc] }
    exact Module.Finite.of_surjective f fun m => hsurj m
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := M)
  have hscalar : ∀ r : A, ∃ c : k, ∀ m : M, r • m = c • m := by
    intro r
    let φ : M →ₗ[A] M :=
      { toFun := fun m => r • m
        map_add' := fun a b => smul_add r a b
        map_smul' := fun s m => by simp only [RingHom.id_apply]; exact hcomm_act r s m }
    obtain ⟨c, hc⟩ := hschur.2 φ
    refine ⟨c, fun m => ?_⟩
    have hm := LinearMap.ext_iff.mp hc m
    simp only [Module.algebraMap_end_apply] at hm
    exact hm.symm
  rw [finrank_eq_one_iff_of_nonzero' m₀ hm₀]
  intro m
  obtain ⟨r, hr⟩ := hsurj m
  obtain ⟨c, hc⟩ := hscalar r
  exact ⟨c, by rw [← hr, hc]⟩

/-- Over an algebraically closed field, the two auxiliary conditions are equivalent for finite
algebras. -/
theorem Algebra.Auxiliary.auxiliary_iff_auxiliary {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A] :
    FieldAlgebraProperties.fieldAlgebraProperty k A ↔
      FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k A :=
  ⟨FieldAlgebraProperties.fieldAlgebraProperty.toAuxiliaryOfIsAlgClosed,
    FieldAlgebraProperties.fieldAlgebraProperty'.toAuxiliary⟩

end RepresentationTheory
