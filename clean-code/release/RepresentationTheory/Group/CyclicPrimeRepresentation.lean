/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Representations of cyclic groups of prime order -/

namespace RepresentationTheory.Group.CyclicPrimeRepresentation

open scoped MonoidAlgebra in
/-- Every group element acts as the identity in a finite simple representation of the cyclic group
of prime order over a field of that characteristic. -/
@[source_ref "Chapter4/Example4.1.3/Derived2" (role := supporting),
  source_ref "Chapter4/Example4.1.3" (role := primary)]
theorem apply_eq_id_of_isSimpleModule
    (k : Type*) (p : ℕ) [Field k] [hp : Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Multiplicative (ZMod p)) V)
    (hirr : IsSimpleModule (MonoidAlgebra k (Multiplicative (ZMod p))) ρ.asModule) :
    ∀ g : Multiplicative (ZMod p), ρ g = LinearMap.id := by
  haveI hirr' : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hirr
  haveI : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (Multiplicative (ZMod p))) ρ.asModule
  haveI : Nontrivial V := (ρ.asModuleEquiv).toEquiv.symm.nontrivial
  intro g
  have hgp : g ^ p = 1 := by
    have h := pow_card_eq_one (x := g)
    rwa [Fintype.card_multiplicative, ZMod.card] at h
  have hρp : (ρ g) ^ p = 1 := by
    rw [← map_pow, hgp, map_one]
  have hnil : (ρ g - 1) ^ p = 0 := by
    haveI : CharP (Module.End k V) p :=
      charP_of_injective_algebraMap' k p
    rw [sub_pow_char_of_commute p (Commute.one_right _)]
    rw [one_pow, hρp, sub_self]
  have key : ∀ (h : Multiplicative (ZMod p)) (v : V), ρ g (ρ h v) = ρ h (ρ g v) := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  let f : Representation.IntertwiningMap ρ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (ρ g - 1) (by
      intro h v
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, key h v])
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | hf0
  · exfalso
    have hinj' : Function.Injective (⇑(ρ g - 1)) := hinj
    have hinj_iter : Function.Injective (⇑(ρ g - 1))^[p] := hinj'.iterate p
    rw [← Module.End.coe_pow, hnil] at hinj_iter
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    exact hab (hinj_iter (by simp))
  · have hzero : ρ g - 1 = 0 := by
      ext v
      have hv := DFunLike.congr_fun hf0 v
      simpa [f] using hv
    rwa [sub_eq_zero] at hzero

end RepresentationTheory.Group.CyclicPrimeRepresentation
