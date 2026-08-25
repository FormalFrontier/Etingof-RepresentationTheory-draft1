/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Auxiliary.PartitionIndexedAlgebra
import RepresentationTheory.SimpleModulesAndPartitionBounds

namespace RepresentationTheory.Representation.PermutationGroupSpectrum

open scoped Classical
open Polynomial

private lemma pow_sumTranspositions_mul_specht (m : ℕ) (la : Nat.Partition m) (k : ℕ)
    {y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m}
    (hy : y ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m la) :
    _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m ^ k * y =
      ((_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) ^ k) • y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm,
      _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_of_mem m la y hy,
      smul_smul, ← pow_succ]

private lemma aeval_sumTranspositions_mul_specht (m : ℕ) (la : Nat.Partition m) (p : ℂ[X])
    {y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m}
    (hy : y ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m la) :
    (Polynomial.aeval
        (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) p) * y =
      (p.eval
        (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ)) • y := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [map_add, add_mul, hp, hq, eval_add, add_smul]
  · intro k c
    rw [Polynomial.aeval_monomial, eval_monomial, mul_assoc,
      pow_sumTranspositions_mul_specht m la k hy, ← Algebra.smul_def, smul_smul]

private lemma aeval_sumTranspositions_comm (m : ℕ) (p : ℂ[X])
    (a : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) :
    Commute
      (Polynomial.aeval
        (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) p) a := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simpa only [map_add] using hp.add_left hq
  · intro k c
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left c a).mul_left
      ((show Commute
          (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) a
        from _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_commutes m a).pow_left k)

/-- States that the displayed endomorphism for a finite-dimensional complex representation of permutations of `Fin m` is semisimple and that each of its eigenvalues is an integer cast to `Complex`. -/
theorem representationEndomorphism_isSemisimple_and_eigenvalues_eq_intCast
    (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin m)) V) :
    (ρ.asAlgebraHom
      (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m)).IsSemisimple ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue
      (ρ.asAlgebraHom
        (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m)) μ →
      ∃ la : Nat.Partition m,
        μ = (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ)) := by
  classical
  set T : Module.End ℂ V :=
    ρ.asAlgebraHom
      (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) with hT
  set S : Finset ℂ := Finset.univ.image
    (fun la : Nat.Partition m =>
      (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ)) with hS
  set p : ℂ[X] := ∏ c ∈ S, (X - C c) with hp
  set q : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m :=
    Polynomial.aeval
      (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) p with hq
  have hsep := (Polynomial.separable_prod_X_sub_C_iff' (f := fun c : ℂ => c) (s := S)).mpr
    (fun x _ y _ h => h)
  have hsf : Squarefree p := by rw [hp]; exact hsep.squarefree
  haveI : IsSemisimpleModule
      (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρ.asModule := inferInstance
  have hqann : ∀ x : ρ.asModule, q • x = (0 : ρ.asModule) := by
    have hcomm : ∀ a : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m,
        q * a = a * q := fun a => by
      rw [hq]; exact (aeval_sumTranspositions_comm m p a).eq
    let N : Submodule
        (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρ.asModule :=
      { carrier := {x | q • x = 0}
        zero_mem' := by simp
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at *
          rw [smul_add, hx, hy, add_zero]
        smul_mem' := fun a {x} hx => by
          simp only [Set.mem_setOf_eq] at *
          rw [← mul_smul, hcomm a, mul_smul, hx, smul_zero] }
    have hNtop : N = ⊤ := by
      rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top
        (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρ.asModule]
      refine sSup_le ?_
      intro W hW
      haveI : IsSimpleModule
          (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) W := hW
      intro w hw
      change q • w = 0
      obtain ⟨la, ⟨φ⟩⟩ :=
        _root_.RepresentationTheory.SimpleModulesAndPartitionBounds.exists_linear_equiv_membership_subtype_over_permutation_monoid_algebra
          ℂ m (W : Type _)
      have hmod :
          _root_.RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule ℂ m la =
            _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m la := by
        unfold _root_.RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule
          _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule
        rw [_root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int ℂ m la,
          _root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.complexPartitionSymmetrizer_eq_map_int m la]
      set z : W := ⟨w, hw⟩ with hz
      have hφz_mem :
          (↑(φ z) : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ∈
            _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m la :=
        hmod ▸ (φ z).2
      have h1 :
          q * (↑(φ z) : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) = 0 := by
        rw [hq, aeval_sumTranspositions_mul_specht m la p hφz_mem]
        have hev : p.eval
            (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) = 0 := by
          rw [hp, eval_prod]
          refine Finset.prod_eq_zero
            (i := (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ)) ?_ ?_
          · rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ la)
          · simp
        rw [hev, zero_smul]
      have h2 : q • φ z = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_smul, smul_eq_mul, h1, Submodule.coe_zero]
      have h3 : q • z = 0 := by
        apply φ.injective
        rw [map_zero, map_smul, h2]
      have h4 : (↑(q • z) : ρ.asModule) = ↑(0 : W) := by rw [h3]
      rwa [Submodule.coe_smul, Submodule.coe_zero, show (↑z : ρ.asModule) = w from rfl] at h4
    intro x
    have hx : x ∈ N := by rw [hNtop]; exact Submodule.mem_top
    exact hx
  have hpT : Polynomial.aeval T p = 0 := by
    have heq : Polynomial.aeval T p = ρ.asAlgebraHom q := by
      rw [hT, hq]; exact Polynomial.aeval_algHom_apply ρ.asAlgebraHom
        (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) p
    rw [heq]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.zero_apply]
    have key := ρ.asModuleEquiv_map_smul q (ρ.asModuleEquiv.symm v)
    rw [ρ.asModuleEquiv.apply_symm_apply] at key
    rw [← key, hqann (ρ.asModuleEquiv.symm v), map_zero]
  refine ⟨Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsf hpT, ?_⟩
  intro μ hμ
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have happ := Module.End.aeval_apply_of_hasEigenvector (p := p) hx
  rw [hpT, LinearMap.zero_apply] at happ
  have hpev : p.eval μ = 0 := by
    rcases smul_eq_zero.mp happ.symm with h | h
    · exact h
    · exact absurd h hx.2
  rw [hp, eval_prod] at hpev
  obtain ⟨c, hcS, hc0⟩ := Finset.prod_eq_zero_iff.mp hpev
  have hμc : μ = c := by
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hc0
    exact hc0
  obtain ⟨la, _, hla⟩ := Finset.mem_image.mp (hS ▸ hcS)
  exact ⟨la, hμc.trans hla.symm⟩

end RepresentationTheory.Representation.PermutationGroupSpectrum
