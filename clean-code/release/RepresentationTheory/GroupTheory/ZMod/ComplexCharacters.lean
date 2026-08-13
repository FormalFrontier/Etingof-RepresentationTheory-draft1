/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Complex characters of integers modulo a natural number
-/

namespace RepresentationTheory.GroupTheory.ZMod.ComplexCharacters

variable (N : ℕ) [NeZero N]

/-- The cast of the exponent of the multiplicative form of integers modulo a nonzero natural number is nonzero. -/
instance exponent_cast_neZero :
    NeZero ((Monoid.exponent (Multiplicative (ZMod N)) : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is multiplicatively equivalent to that cyclic group. -/
noncomputable def complex_characters_mulEquiv :
    (Multiplicative (ZMod N) →* ℂˣ) ≃* Multiplicative (ZMod N) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Multiplicative (ZMod N)) ℂ).some

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is finite. -/
instance finite_complex_characters : Finite (Multiplicative (ZMod N) →* ℂˣ) :=
  Finite.of_equiv _ (complex_characters_mulEquiv N).symm.toEquiv

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is cyclic. -/
instance isCyclic_complex_characters : IsCyclic (Multiplicative (ZMod N) →* ℂˣ) :=
  isCyclic_of_surjective (complex_characters_mulEquiv N).symm
    (complex_characters_mulEquiv N).symm.surjective

/-- The character group from the multiplicative form of integers modulo a nonzero natural number to the complex units has cardinality that natural number. -/
theorem card_complex_characters : Nat.card (Multiplicative (ZMod N) →* ℂˣ) = N := by
  rw [Nat.card_congr (complex_characters_mulEquiv N).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

/-- The number of complex characters fixed by inversion is the greatest common divisor of the modulus and two. -/
theorem card_self_inverse_complex_characters :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} = Nat.gcd 2 N := by
  have hEquiv :
      {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} ≃
        (powMonoidHom 2 : (Multiplicative (ZMod N) →* ℂˣ) →* _).ker :=
    Equiv.subtypeEquivRight fun χ => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_two, mul_eq_one_iff_eq_inv]
  rw [Nat.card_congr hEquiv, IsCyclic.card_powMonoidHom_ker, card_complex_characters,
    Nat.gcd_comm]

/-- The number of complex characters not fixed by inversion is the modulus minus its greatest common divisor with two. -/
theorem card_non_self_inverse_complex_characters :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} = N - Nat.gcd 2 N := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  have hsplit :
      Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹}
        = Fintype.card (Multiplicative (ZMod N) →* ℂˣ)
          - Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} :=
    Fintype.card_subtype_compl (fun χ => χ = χ⁻¹)
  rw [Nat.card_eq_fintype_card, hsplit, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_complex_characters, card_self_inverse_complex_characters]

/-- For an involution of a finite type, two divides the number of elements that are not fixed. -/
theorem two_dvd_card_ne_fixed_of_involutive {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → α} (hf : Function.Involutive f) :
    2 ∣ Fintype.card {a // f a ≠ a} := by
  set e : Equiv.Perm α := Function.Involutive.toPerm f hf with he
  have he2 : e ^ 2 = 1 := by ext a; simp [he, pow_two, Equiv.Perm.mul_apply, hf a]
  have hcard : Fintype.card {a // f a ≠ a} = e.support.card := by
    rw [Fintype.card_subtype]; congr 1
  rw [hcard, ← Equiv.Perm.sum_cycleType]
  apply Multiset.dvd_sum
  intro n hn
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hd : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one he2)
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- Two divides the number of complex characters that are not fixed by inversion. -/
theorem two_dvd_card_non_self_inverse_complex_characters :
    2 ∣ Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h := two_dvd_card_ne_fixed_of_involutive
    (f := (·⁻¹ : (Multiplicative (ZMod N) →* ℂˣ) → _)) inv_involutive
  rwa [Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => ne_comm))] at h

/-- Half the number of complex characters not fixed by inversion equals half the difference between the modulus and its greatest common divisor with two. -/
theorem card_non_self_inverse_complex_characters_div_two :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} / 2 =
      (N - Nat.gcd 2 N) / 2 := by
  rw [card_non_self_inverse_complex_characters]

end RepresentationTheory.GroupTheory.ZMod.ComplexCharacters
