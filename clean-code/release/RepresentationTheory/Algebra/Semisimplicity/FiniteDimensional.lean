/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity
import RepresentationTheory.Alignment.Attribute

open Module

universe u

namespace RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional

/-- The displayed finite-dimensional algebra conditions are equivalent under the stated hypotheses. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary),
  source_ref "Chapter4/Theorem4.1.1/Derived9" (role := primary)]
theorem finiteDimensional_tfae (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    [ RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraModuleSemisimple k A,
      ∑ i, finrank k (V i) ^ 2 = finrank k A,
      ∃ (n : ℕ) (d : Fin n → ℕ), (∀ j, NeZero (d j)) ∧
        Nonempty (A ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k),
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
        [FiniteDimensional k M], IsSemisimpleModule A M,
      IsSemisimpleModule A A ].TFAE := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have key : finrank k (A ⧸ RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) = ∑ i, finrank k (V i) ^ 2 := by
    obtain ⟨e⟩ := RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct.nonempty_algEquiv_quotient_endProduct k A ι V h_noniso h_complete
    calc finrank k (A ⧸ RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A)
        = finrank k (∀ i, End k (V i)) := e.toLinearEquiv.finrank_eq
      _ = ∑ i, finrank k (End k (V i)) := finrank_pi_fintype k
      _ = ∑ i, finrank k (V i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sq, ← finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)]
  have bridge : finrank k (A ⧸ RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A)
      + finrank k ((RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A).restrictScalars k) = finrank k A := by
    have h := Submodule.finrank_quotient_add_finrank ((RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A).restrictScalars k)
    rwa [(Submodule.Quotient.restrictScalarsEquiv k (RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A)).finrank_eq] at h
  have semisimple_bridge := RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraModuleSemisimple_iff k A
  tfae_have 1 → 2 := by
    intro h1
    have h1' : RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A = ⊥ := h1
    have : ((RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A).restrictScalars k) = ⊥ := by
      rw [h1', Submodule.restrictScalars_bot]
    rw [← bridge, this, finrank_bot, add_zero, key]
  tfae_have 2 → 1 := by
    intro h2
    have hr : finrank k ((RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A).restrictScalars k) = 0 := by
      have := bridge
      rw [key, ← h2] at this
      omega
    have hrad : RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A = ⊥ := by
      rw [← Submodule.restrictScalars_eq_bot_iff (S := k)]
      exact Submodule.finrank_eq_zero.mp hr
    exact hrad
  tfae_have 1 → 3 := by
    intro h1
    haveI : IsSemisimpleRing A := h1.isSemisimpleRing
    exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k A
  tfae_have 3 → 1 := by
    rintro ⟨n, d, _, ⟨e⟩⟩
    exact semisimple_bridge.mpr e.toRingEquiv.symm.isSemisimpleRing
  tfae_have 1 → 4 := by
    intro h1 M _ _ _ _ _
    haveI : IsSemisimpleRing A := h1.isSemisimpleRing
    exact IsSemisimpleRing.isSemisimpleModule
  tfae_have 4 → 5 := fun h4 => h4 A
  tfae_have 5 → 1 := by
    intro h5
    exact RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraModuleSemisimple_of_isSemisimpleRing k A h5
  tfae_finish

/-- A subsingleton ring is semisimple. -/
theorem isSemisimpleRing_of_subsingleton (A : Type*) [Ring A] [Subsingleton A] :
    IsSemisimpleRing A :=
  inferInstance

/-- A finite-dimensional subsingleton algebra satisfies the displayed auxiliary property. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem auxiliaryProperty_of_subsingleton (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Subsingleton A] :
    RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.FiniteAlgebraModuleSemisimple k A :=
  RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity.finiteAlgebraModuleSemisimple_of_isSemisimpleRing k A (isSemisimpleRing_of_subsingleton A)

/-- A subsingleton ring is not simple. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem not_isSimpleRing_of_subsingleton (A : Type*) [Ring A] [Subsingleton A] :
    ¬ IsSimpleRing A := by
  intro h
  haveI := h
  exact false_of_nontrivial_of_subsingleton A

/-- Every module over a subsingleton ring is subsingleton. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem subsingleton_module_of_subsingleton_ring (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] : Subsingleton M :=
  Module.subsingleton A M

/-- A module over a subsingleton ring is not simple. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem not_isSimpleModule_of_subsingleton (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] : ¬ IsSimpleModule A M := by
  intro h
  haveI := Module.subsingleton A M
  haveI := IsSimpleModule.nontrivial A M
  exact false_of_nontrivial_of_subsingleton M

/-- A module over a subsingleton ring does not satisfy the displayed auxiliary property. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem not_auxiliaryProperty_of_subsingleton (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    ¬ RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A M := by
  intro h
  haveI := h.1
  haveI := Module.subsingleton A M
  exact false_of_nontrivial_of_subsingleton M

/-- A subsingleton algebra is algebraically equivalent to the indicated zero-indexed matrix algebra. -/
@[source_ref "Chapter3/Proposition3.5.8" (role := primary)]
theorem nonempty_algEquiv_finZero_matrix (k : Type*) (A : Type*)
    [Field k] [Ring A] [Subsingleton A] [Algebra k A] :
    Nonempty (A ≃ₐ[k] Π (_ : Fin 0), Matrix (Fin 0) (Fin 0) k) :=
  ⟨{ toFun := fun _ => 0
     invFun := fun _ => 0
     left_inv := fun _ => Subsingleton.elim _ _
     right_inv := fun _ => Subsingleton.elim _ _
     map_mul' := fun _ _ => Subsingleton.elim _ _
     map_add' := fun _ _ => Subsingleton.elim _ _
     commutes' := fun _ => Subsingleton.elim _ _ }⟩

end RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional
