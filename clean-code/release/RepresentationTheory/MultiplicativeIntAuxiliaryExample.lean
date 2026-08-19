/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.RingTheory.Polynomial.JordanBlockModule

open RepresentationTheory.RingTheory.Polynomial.JordanBlockModule

namespace RepresentationTheory.MultiplicativeIntAuxiliaryExample

namespace multiplicativeInt_infinite_and_exists_auxiliary_nonirreducible_representation

/-- An auxiliary predicate on a representation of a monoid over a field. -/
def auxiliaryRepresentationProperty {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) : Prop :=
  Nontrivial (Subrepresentation ρ) ∧
    ∀ S T : Subrepresentation ρ, IsCompl S T → S = ⊥ ∨ T = ⊥

/-- The square of the specified auxiliary endomorphism is zero. -/
lemma auxiliaryEndomorphism_sq_eq_zero :
    (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) ^ 2 = 0 := by
  apply LinearMap.ext; intro v; funext i
  rw [auxiliaryFact_aux2, dif_neg (by omega)]
  simp

/-- The specified auxiliary endomorphism sends the distinguished auxiliary vector to zero. -/
lemma auxiliaryEndomorphism_apply_auxiliaryVector_eq_zero :
    jordanNilpotent 2 (jordanEigenvector 2 : Fin 2 → ℂ) = 0 := by
  funext i
  simp only [auxiliaryFact_aux1, Pi.zero_apply]
  split
  · apply Pi.single_eq_of_ne
    intro hh; rw [Fin.ext_iff] at hh; simp at hh
  · rfl

/-- An auxiliary invertible complex-linear endomorphism of the two-coordinate function space. -/
noncomputable def auxiliaryAutomorphism : (Module.End ℂ (Fin 2 → ℂ))ˣ where
  val := jordanOperator 1 2
  inv := 1 - jordanNilpotent 2
  val_inv := by
    have hjb : jordanOperator (1 : ℂ) 2 = 1 + jordanNilpotent 2 := by
      rw [jordanOperator, one_smul, ← Module.End.one_eq_id]
    have : jordanOperator (1 : ℂ) 2 * (1 - jordanNilpotent 2) =
        1 - jordanNilpotent 2 ^ 2 := by
      rw [hjb, pow_two]
      simp only [sub_eq_add_neg, add_mul, mul_add, one_mul, mul_one]
      have hneg :
          (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) *
              -(jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) =
            -((jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) *
              (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ))) := by
        simpa using
          (Algebra.mul_smul_comm (-1 : ℂ)
            (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ))
            (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)))
      rw [hneg]
      abel
    rw [this, auxiliaryEndomorphism_sq_eq_zero, sub_zero]
  inv_val := by
    have hjb : jordanOperator (1 : ℂ) 2 = 1 + jordanNilpotent 2 := by
      rw [jordanOperator, one_smul, ← Module.End.one_eq_id]
    have : (1 - jordanNilpotent 2) * jordanOperator (1 : ℂ) 2 =
        1 - jordanNilpotent 2 ^ 2 := by
      rw [hjb, pow_two]
      simp only [sub_eq_add_neg, add_mul, mul_add, one_mul, mul_one]
      have hneg :
          -(jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) *
              (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) =
            -((jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) *
              (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ))) := by
        simpa using
          (Algebra.smul_mul_assoc (-1 : ℂ)
            (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ))
            (jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)))
      rw [hneg]
      abel
    rw [this, auxiliaryEndomorphism_sq_eq_zero, sub_zero]

/-- The linear endomorphism underlying the auxiliary automorphism equals the specified auxiliary endomorphism. -/
lemma auxiliaryAutomorphism_val_eq_auxiliaryEndomorphism :
    (auxiliaryAutomorphism : Module.End ℂ (Fin 2 → ℂ)) = jordanOperator 1 2 := rfl

/-- The auxiliary automorphism fixes the distinguished auxiliary vector. -/
lemma auxiliaryAutomorphism_apply_auxiliaryVector :
    (auxiliaryAutomorphism : Module.End ℂ (Fin 2 → ℂ)) (jordanEigenvector 2) =
      jordanEigenvector 2 := by
  rw [auxiliaryAutomorphism_val_eq_auxiliaryEndomorphism,
    jordanOperator_jordanEigenvector, one_smul]

/-- The inverse auxiliary automorphism fixes the distinguished auxiliary vector. -/
lemma auxiliaryAutomorphism_inv_apply_auxiliaryVector :
    ((auxiliaryAutomorphism⁻¹ : (Module.End ℂ (Fin 2 → ℂ))ˣ) :
      Module.End ℂ (Fin 2 → ℂ)) (jordanEigenvector 2) = jordanEigenvector 2 := by
  change (1 - jordanNilpotent 2 : Module.End ℂ (Fin 2 → ℂ)) (jordanEigenvector 2) =
    jordanEigenvector 2
  rw [LinearMap.sub_apply, auxiliaryEndomorphism_apply_auxiliaryVector_eq_zero,
    Module.End.one_apply, sub_zero]

/-- A complex representation of the multiplicative copy of the integers on two-coordinate functions. -/
@[source_ref "Chapter4/Remark4.6.4" (role := supporting)]
noncomputable def multiplicativeIntRepresentation :
    Representation ℂ (Multiplicative ℤ) (Fin 2 → ℂ) :=
  (Units.coeHom _).comp (zpowersHom _ auxiliaryAutomorphism)

/-- Evaluating the integer representation at an element gives the corresponding integer power of the auxiliary automorphism. -/
lemma multiplicativeIntRepresentation_apply (n : Multiplicative ℤ) :
    multiplicativeIntRepresentation n =
      ((auxiliaryAutomorphism ^ Multiplicative.toAdd n :
        (Module.End ℂ (Fin 2 → ℂ))ˣ) : Module.End ℂ (Fin 2 → ℂ)) := rfl

/-- The representation operator at the multiplicative image of one is the specified auxiliary endomorphism. -/
lemma multiplicativeIntRepresentation_ofAdd_one :
    multiplicativeIntRepresentation (Multiplicative.ofAdd (1 : ℤ)) = jordanOperator 1 2 := by
  rw [multiplicativeIntRepresentation_apply, toAdd_ofAdd, zpow_one,
    auxiliaryAutomorphism_val_eq_auxiliaryEndomorphism]

/-- Every operator in the integer representation fixes the distinguished auxiliary vector. -/
lemma multiplicativeIntRepresentation_apply_auxiliaryVector (n : Multiplicative ℤ) :
    multiplicativeIntRepresentation n (jordanEigenvector 2 : Fin 2 → ℂ) =
      jordanEigenvector 2 := by
  rw [multiplicativeIntRepresentation_apply]
  generalize Multiplicative.toAdd n = m
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, Module.End.one_apply]
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, Module.End.mul_apply,
        auxiliaryAutomorphism_apply_auxiliaryVector, ih]
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, Module.End.mul_apply,
        auxiliaryAutomorphism_inv_apply_auxiliaryVector, ih]

/-- An auxiliary subrepresentation of the specified representation. -/
noncomputable def auxiliarySubrepresentation : Subrepresentation multiplicativeIntRepresentation where
  toSubmodule := Submodule.span ℂ {(jordanEigenvector 2 : Fin 2 → ℂ)}
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_span_singleton] at hv ⊢
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, by rw [map_smul, multiplicativeIntRepresentation_apply_auxiliaryVector]⟩

/-- The underlying submodule of the auxiliary subrepresentation is the span of the distinguished auxiliary vector. -/
lemma auxiliarySubrepresentation_toSubmodule :
    auxiliarySubrepresentation.toSubmodule =
      Submodule.span ℂ {(jordanEigenvector 2 : Fin 2 → ℂ)} := rfl

/-- The auxiliary subrepresentation is not the bottom subrepresentation. -/
lemma auxiliarySubrepresentation_ne_bot : auxiliarySubrepresentation ≠ ⊥ := by
  intro h
  have h2 : auxiliarySubrepresentation.toSubmodule = ⊥ := by rw [h]; rfl
  rw [auxiliarySubrepresentation_toSubmodule, Submodule.span_singleton_eq_bot] at h2
  exact jordanEigenvector_ne_zero 2 h2

/-- The auxiliary subrepresentation is not the top subrepresentation. -/
lemma auxiliarySubrepresentation_ne_top : auxiliarySubrepresentation ≠ ⊤ := by
  intro h
  have h2 : auxiliarySubrepresentation.toSubmodule = ⊤ := by rw [h]; rfl
  have he1 : (Pi.single (1 : Fin 2) (1 : ℂ)) ∈
      Submodule.span ℂ {(jordanEigenvector 2 : Fin 2 → ℂ)} := by
    rw [← auxiliarySubrepresentation_toSubmodule, h2]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at he1
  obtain ⟨c, hc⟩ := he1
  have hco := congrFun hc (1 : Fin 2)
  rw [Pi.single_eq_same] at hco
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [jordanEigenvector, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hne,
    mul_zero] at hco
  exact one_ne_zero hco.symm

/-- The integer representation is not irreducible. -/
@[source_ref "Chapter4/Remark4.6.4" (role := supporting)]
theorem multiplicativeIntRepresentation_not_isIrreducible :
    ¬ Representation.IsIrreducible multiplicativeIntRepresentation := by
  intro h
  haveI := h
  rcases eq_bot_or_eq_top auxiliarySubrepresentation with hb | ht
  · exact auxiliarySubrepresentation_ne_bot hb
  · exact auxiliarySubrepresentation_ne_top ht

/-- Every nonzero subrepresentation of the specified representation contains the distinguished auxiliary vector. -/
lemma nonzeroSubrepresentation_contains_auxiliaryVector
    {S : Subrepresentation multiplicativeIntRepresentation} (hS : S ≠ ⊥) :
    (jordanEigenvector 2 : Fin 2 → ℂ) ∈ S.toSubmodule := by
  have hinv : ∀ m ∈ S.toSubmodule, jordanOperator (1 : ℂ) 2 m ∈ S.toSubmodule := by
    intro m hm
    have := S.apply_mem_toSubmodule (Multiplicative.ofAdd 1) hm
    rwa [multiplicativeIntRepresentation_ofAdd_one] at this
  have hbot : S.toSubmodule ≠ ⊥ := by
    intro h; exact hS (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
  exact jordanEigenvector_mem_of_invariant 1 2 hbot hinv

/-- The integer representation satisfies the auxiliary representation property. -/
@[source_ref "Chapter4/Remark4.6.4" (role := supporting)]
theorem auxiliaryRepresentationProperty_multiplicativeIntRepresentation :
    auxiliaryRepresentationProperty multiplicativeIntRepresentation := by
  refine ⟨⟨auxiliarySubrepresentation, ⊥, auxiliarySubrepresentation_ne_bot⟩, ?_⟩
  intro S T hcompl
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hS, hT⟩ := hcon
  have hSe0 : (jordanEigenvector 2 : Fin 2 → ℂ) ∈ S.toSubmodule :=
    nonzeroSubrepresentation_contains_auxiliaryVector hS
  have hTe0 : (jordanEigenvector 2 : Fin 2 → ℂ) ∈ T.toSubmodule :=
    nonzeroSubrepresentation_contains_auxiliaryVector hT
  have hmem : (jordanEigenvector 2 : Fin 2 → ℂ) ∈ (S ⊓ T).toSubmodule := by
    rw [Subrepresentation.toSubmodule_inf]; exact Submodule.mem_inf.mpr ⟨hSe0, hTe0⟩
  rw [hcompl.inf_eq_bot] at hmem
  rw [show (⊥ : Subrepresentation multiplicativeIntRepresentation).toSubmodule =
      (⊥ : Submodule ℂ (Fin 2 → ℂ)) from rfl, Submodule.mem_bot] at hmem
  exact jordanEigenvector_ne_zero 2 hmem

end multiplicativeInt_infinite_and_exists_auxiliary_nonirreducible_representation

open multiplicativeInt_infinite_and_exists_auxiliary_nonirreducible_representation in
/-- The multiplicative copy of the integers is infinite and admits a representation satisfying the auxiliary property that is not irreducible. -/
@[source_ref "Chapter4/Remark4.6.4" (role := primary)]
theorem multiplicativeInt_infinite_and_exists_auxiliary_nonirreducible_representation :
    Infinite (Multiplicative ℤ) ∧
      ∃ ρ : Representation ℂ (Multiplicative ℤ) (Fin 2 → ℂ),
        auxiliaryRepresentationProperty ρ ∧ ¬ Representation.IsIrreducible ρ :=
  ⟨inferInstance, multiplicativeIntRepresentation,
    auxiliaryRepresentationProperty_multiplicativeIntRepresentation,
    multiplicativeIntRepresentation_not_isIrreducible⟩

end RepresentationTheory.MultiplicativeIntAuxiliaryExample
