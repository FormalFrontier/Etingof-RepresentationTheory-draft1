/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.IndependentSpanningFamilies
import RepresentationTheory.Alignment.Attribute

/-! # Finite module decompositions -/

































namespace RepresentationTheory.Algebra.Module.FiniteDecompositions






/-- Under the displayed module property, every endomorphism is either bijective or nilpotent. -/
theorem bijective_or_nilpotent (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W) (θ : W →ₗ[A] W) :
    Function.Bijective θ ∨ IsNilpotent θ :=
  RepresentationTheory.Algebra.Module.EndomorphismDichotomy.bijective_or_nilpotent_of_auxiliaryProperty k A W hW θ




/-- Under the displayed module property, a finite sum of nilpotent endomorphisms is nilpotent. -/
theorem sum_nilpotent (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W)
    {n : ℕ} (θ : Fin n → (W →ₗ[A] W)) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) :=
  RepresentationTheory.Algebra.Module.EndomorphismDichotomy.sum_nilpotent_of_auxiliaryProperty k A W hW θ hθ




/-- A finite-dimensional module has a finite internal family of submodules satisfying the displayed module property. -/
theorem exists_internal_family (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i)) ∧
      iSup W = ⊤ ∧ iSupIndep W :=
  RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.exists_iSupIndep_eq_top k A V






/-- Two finite internal spanning families of nonzero submodules satisfying the displayed property have equal lengths and matching equivalent members. -/
theorem internal_family_unique_up_to_permutation (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i))
    (hW'_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥) (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) :=
  RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.eq_card_and_exists_equiv_of_iSupIndep k A V W W'
    hW_indec hW'_indec hW_ne hW'_ne hW_sup hW_ind hW'_sup hW'_ind

end RepresentationTheory.Algebra.Module.FiniteDecompositions

/-- Under the displayed module property, every endomorphism is either bijective or nilpotent. -/
alias _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.bijective_or_nilpotent_of_auxiliaryProperty := _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.bijective_or_nilpotent

/--
A finite-dimensional module has a finite internal family of submodules satisfying the displayed
module property.
-/
alias _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family_satisfying_auxiliaryProperty := _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family

/--
Two finite internal spanning families of nonzero submodules satisfying the displayed auxiliary
property have equal lengths and a displayed correspondence between equivalent members.
-/
alias _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.internal_families_equal_length_and_corresponding_equiv := _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.internal_family_unique_up_to_permutation

/-- Under the displayed module property, a finite sum of nilpotent endomorphisms is nilpotent. -/
alias _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.sum_nilpotent_of_auxiliaryProperty := _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.sum_nilpotent

attribute [source_ref "Chapter3/Problem3.8.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.bijective_or_nilpotent_of_auxiliaryProperty

attribute [source_ref "Chapter3/Problem3.8.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family_satisfying_auxiliaryProperty

attribute [source_ref "Chapter3/Problem3.8.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.internal_families_equal_length_and_corresponding_equiv

attribute [source_ref "Chapter3/Problem3.8.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.FiniteDecompositions.sum_nilpotent_of_auxiliaryProperty
