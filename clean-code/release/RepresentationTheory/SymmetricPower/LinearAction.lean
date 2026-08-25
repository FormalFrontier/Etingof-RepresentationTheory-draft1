/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis
import RepresentationTheory.SymmetricPower.Basis
import RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct BigOperators
open Module
open RepresentationTheory.SymmetricPower.Basis.SymmetricPower.Basis

namespace RepresentationTheory.SymmetricPower.LinearAction

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]

section Combinatorics

variable {n d : ℕ}

private lemma count_map_eq_card_filter (r : Fin n → Fin d) (j : Fin d) :
    Multiset.count j (Multiset.map r Finset.univ.val)
      = (Finset.univ.filter (fun m => r m = j)).card := by
  classical
  rw [Multiset.count_map]
  exact congrArg Multiset.card (Multiset.filter_congr (fun a _ => eq_comm))

private lemma factorization_prod_prime_eq_card_filter (r : Fin n → Fin d) (j : Fin d) :
    (∏ m, Nat.nth Nat.Prime (r m)).factorization (Nat.nth Nat.Prime j)
      = (Finset.univ.filter (fun m => r m = j)).card := by
  classical
  have hinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective Nat.infinite_setOf_prime
  rw [Nat.factorization_prod (fun m _ => (Nat.prime_nth_prime (r m)).ne_zero),
    Finsupp.finsetSum_apply]
  have hterm : ∀ m, (Nat.nth Nat.Prime (r m)).factorization (Nat.nth Nat.Prime j)
      = if r m = j then 1 else 0 := by
    intro m
    rw [(Nat.prime_nth_prime (r m)).factorization]
    simp only [Finsupp.single_apply, hinj.eq_iff, Fin.val_inj]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_boole, Nat.cast_id]

private lemma prod_prime_eq_imp_ofFn_perm {p q : Fin n → Fin d}
    (h : ∏ m, Nat.nth Nat.Prime (p m) = ∏ m, Nat.nth Nat.Prime (q m)) :
    List.Perm (List.ofFn p) (List.ofFn q) := by
  classical
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
  refine Multiset.ext.mpr (fun j => ?_)
  rw [count_map_eq_card_filter, count_map_eq_card_filter,
    ← factorization_prod_prime_eq_card_filter p j,
    ← factorization_prod_prime_eq_card_filter q j, h]

/-- The displayed values constructed from two finite index maps agree when the associated lists are permutations. -/
lemma indexMapValue_eq_of_list_perm {p q : Fin n → Fin d}
    (h : List.Perm (List.ofFn p) (List.ofFn q)) :
    (indexOfFunction p : Index n (Fin d)) = indexOfFunction q := by
  classical
  set σp := Tuple.sort p with hσp
  set σq := Tuple.sort q with hσq
  have hp' : List.Perm (List.ofFn (p ∘ σp)) (List.ofFn p) := Equiv.Perm.ofFn_comp_perm σp p
  have hq' : List.Perm (List.ofFn (q ∘ σq)) (List.ofFn q) := Equiv.Perm.ofFn_comp_perm σq q
  have hperm : List.Perm (List.ofFn (p ∘ σp)) (List.ofFn (q ∘ σq)) :=
    hp'.trans (h.trans hq'.symm)
  have hsp : (List.ofFn (p ∘ σp)).SortedLE := (List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort p)
  have hsq : (List.ofFn (q ∘ σq)).SortedLE := (List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort q)
  have heq : List.ofFn (p ∘ σp) = List.ofFn (q ∘ σq) := hperm.eq_of_sortedLE hsp hsq
  have hfun : p ∘ σp = q ∘ σq := List.ofFn_injective heq
  refine Quotient.sound ⟨σq.symm.trans σp, ?_⟩
  funext i
  have := congrFun hfun (σq.symm i)
  simpa using this.symm

end Combinatorics

section Diagonal

variable {n d : ℕ}

/-- Assigns a scalar to a value of the displayed indexed type from a function on a finite type. -/
noncomputable def finFunctionWeight (t : Fin d → k) : Index n (Fin d) → k :=
  Quotient.lift (fun p => ∏ m, t (p m))
    (by rintro p q ⟨σ, rfl⟩; exact (Equiv.prod_comp σ (fun m => t (p m))).symm)

/-- On the displayed value built from a finite index map, the weight is the product of the selected scalars. -/
@[simp] lemma finFunctionWeight_apply_indexMap (t : Fin d → k) (p : Fin n → Fin d) :
    finFunctionWeight t (indexOfFunction p) = ∏ m, t (p m) := rfl

/-- If a linear map scales every basis vector by its assigned scalar, the displayed symmetric-power element is scaled by the product indexed by the given map. -/
lemma symmetricPower_map_apply_constructedElement_of_smul_basis
    (bV : Basis (Fin d) k V) (t : Fin d → k)
    (g : V →ₗ[k] V) (hg : ∀ l, g (bV l) = t l • bV l) (p : Fin n → Fin d) :
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap g
        (basis bV (indexOfFunction p))
      = (∏ m, t (p m)) • basis bV (indexOfFunction p) := by
  rw [basis_ofFunction, tensorBasis, Basis.piTensorProduct_apply,
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap_mk,
    PiTensorProduct.map_tprod]
  simp only [hg]
  rw [MultilinearMap.map_smul_univ, map_smul]

end Diagonal

/-- Membership preservation under all displayed maps arising from linear equivalences forces a symmetric-power submodule to be either bottom or top. -/
@[source_ref "Chapter4/Problem4.12.3" (role := primary)]
theorem symmetricPower_submodule_bot_or_top_of_forall_linearEquiv_map_mem
    [CharZero k] [Module.Finite k V] {n : ℕ}
    (W : Submodule k (SymmetricPower k (Fin n) V))
    (hW : ∀ g : V ≃ₗ[k] V, ∀ w ∈ W,
      RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
        (g : V →ₗ[k] V) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  set d := finrank k V with hd
  let bV : Basis (Fin d) k V := finBasis k V
  let b : Basis (Index n (Fin d)) k (SymmetricPower k (Fin n) V) :=
    basis bV
  let t : Fin d → k := fun i => ((Nat.nth Nat.Prime i : ℕ) : k)
  have ht : ∀ i, t i ≠ 0 := fun i => by
    simp only [t, Ne, Nat.cast_eq_zero]; exact (Nat.prime_nth_prime i).ne_zero
  let u : Fin d → kˣ := fun i => Units.mk0 (t i) (ht i)
  let H : V ≃ₗ[k] V := bV.equiv (bV.unitsSMul u) (Equiv.refl _)
  have hH : ∀ j : Fin d, H (bV j) = t j • bV j := by
    intro j
    simp only [H, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]
    rfl
  set T : Module.End k (SymmetricPower k (Fin n) V) :=
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
      (H : V →ₗ[k] V) with hT_def
  have hTdiag : ∀ M, T (b M) = finFunctionWeight t M • b M := by
    intro M
    refine Quotient.inductionOn M (fun p => ?_)
    exact symmetricPower_map_apply_constructedElement_of_smul_basis
      bV t (H : V →ₗ[k] V) hH p
  have hinj : Function.Injective (finFunctionWeight t (n := n) (d := d)) := by
    refine fun M N => Quotient.inductionOn₂ M N (fun p q hpq => ?_)
    have hpq' : (∏ m, t (p m)) = ∏ m, t (q m) := hpq
    have hnat : (∏ m, Nat.nth Nat.Prime (p m)) = ∏ m, Nat.nth Nat.Prime (q m) := by
      simp only [t, ← Nat.cast_prod] at hpq'
      exact Nat.cast_injective hpq'
    exact indexMapValue_eq_of_list_perm (prod_prime_eq_imp_ofFn_perm hnat)
  have hWT : ∀ x ∈ W, T x ∈ W := fun x hx => hW H x hx
  refine RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis.eq_bot_or_top_of_invariant_of_eigenbasis_connected
    b hTdiag hinj hWT
    (RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps.objectRelation
      (n := n) (d := d))
    RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps.objectRelation_reflTransGen
    (fun M N hMW hMN => ?_)
  exact RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps.Submodule.mem_of_objectRelation
    bV hTdiag hinj hWT hW M N hMW hMN

/-- A symmetric-power submodule containing the displayed image of each of its elements under every linear equivalence is equal to bottom or top. -/
@[source_ref "Chapter4/Problem4.12.3" (role := primary)]
theorem symmetricPower_submodule_eq_bot_or_eq_top_of_forall_linearEquiv_map_mem
    [CharZero k] [Module.Finite k V] (n : ℕ) :
    ∀ W : Submodule k (SymmetricPower k (Fin n) V),
    (∀ g : V ≃ₗ[k] V, ∀ w ∈ W,
      RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
        (g : V →ₗ[k] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤ :=
  fun W hW => symmetricPower_submodule_bot_or_top_of_forall_linearEquiv_map_mem W hW

end RepresentationTheory.SymmetricPower.LinearAction
