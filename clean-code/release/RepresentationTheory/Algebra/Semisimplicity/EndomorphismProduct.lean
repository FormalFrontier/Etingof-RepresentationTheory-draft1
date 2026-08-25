/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.RingTheory.SimpleModuleAnnihilator
import RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity
import RepresentationTheory.Alignment.Attribute

/-! # Endomorphism-algebra products -/

namespace RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct

universe u in
set_option linter.unusedFintypeInType false in
/-- Under the displayed finite-dimensional simple-module hypotheses, the indicated quotient algebra is equivalent to a product of endomorphism algebras. -/
@[source_ref "Chapter3/Theorem3.5.4" (role := primary),
  source_ref "Chapter3/Corollary3.5.5/Derived2" (role := supporting)]
theorem nonempty_algEquiv_quotient_endProduct (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    Nonempty ((A ⧸
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) ≃ₐ[k]
        (∀ i, Module.End k (V i))) := by
  haveI : ∀ i, SMulCommClass A k (V i) := fun i =>
    { smul_comm := fun a c v => smul_algebra_smul_comm c a v }
  let φ : A →ₐ[k] (∀ i, Module.End k (V i)) :=
    Pi.algHom k (fun i => Module.End k (V i)) (fun i => Algebra.lsmul k k (V i))
  have hφ_surj : Function.Surjective φ :=
    RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.family_algebra_smul_surjective
      k A ι V h_noniso
  have hrad_le_ker :
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A ≤
        RingHom.ker φ.toRingHom := by
    intro a ha
    rw [RingHom.mem_ker]
    ext i : 1
    ext v : 1
    change a • v = 0
    exact
      (RepresentationTheory.RingTheory.SimpleModuleAnnihilator.mem_simpleModuleAnnihilator_iff
        A a).mp ha (V i) v
  have hker_le_rad : RingHom.ker φ.toRingHom ≤
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A := by
    intro a ha
    change a ∈
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A
    unfold RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    simp only [Ideal.mem_sInf, Set.mem_setOf_eq]
    intro J hJ
    haveI : IsSimpleModule A (A ⧸ J) := by
      rwa [isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    haveI : FiniteDimensional k (A ⧸ J) :=
      Module.Finite.of_surjective ((Submodule.mkQ J).restrictScalars k)
        (Submodule.Quotient.mk_surjective _)
    obtain ⟨j, ⟨e⟩⟩ := h_complete (A ⧸ J)
    have ha_ker : a ∈ RingHom.ker φ.toRingHom := ha
    rw [RingHom.mem_ker] at ha_ker
    have ha_Vj : ∀ v : V j, a • v = 0 := by
      intro v
      have := congr_fun ha_ker j
      exact LinearMap.congr_fun this v
    have ha_quot : ∀ x : A ⧸ J, a • x = 0 := by
      intro x
      have : a • (e x) = 0 := ha_Vj (e x)
      rw [← e.map_smul] at this
      exact e.injective (by rwa [map_zero])
    have h1 : a • (Submodule.Quotient.mk (p := J) (1 : A) : A ⧸ J) = 0 := ha_quot _
    rwa [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      Submodule.Quotient.mk_eq_zero] at h1
  have hker_eq : RingHom.ker φ.toRingHom =
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A :=
    le_antisymm hker_le_rad hrad_le_ker
  exact ⟨(Ideal.quotientEquivAlgOfEq k hker_eq.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ_surj)⟩

end RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct
