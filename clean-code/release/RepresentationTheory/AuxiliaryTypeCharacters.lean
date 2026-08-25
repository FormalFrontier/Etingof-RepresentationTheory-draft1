/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.SpecialLinear.Commutator
import RepresentationTheory.Alignment.Attribute

/-!
# Characters of an auxiliary type

This module defines an auxiliary general linear group over a finite field and records structural
results about its complex characters.
-/

open Matrix

namespace RepresentationTheory.AuxiliaryTypeCharacters

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- An auxiliary type depending on a prime and a natural number. -/
abbrev AuxiliaryType := GeneralLinearGroup (Fin 2) (GaloisField p n)

/-- A homomorphism from the auxiliary type to the units of the finite field. -/
noncomputable abbrev auxiliaryTypeToUnits : AuxiliaryType p n →* (GaloisField p n)ˣ :=
  Matrix.GeneralLinearGroup.det

/-- The homomorphism from the auxiliary type to field units is surjective. -/
theorem auxiliaryTypeToUnits_surjective : Function.Surjective (auxiliaryTypeToUnits p n) :=
  Matrix.GeneralLinearGroup.det_surjective

/-- Identifies the range of the special linear inclusion with the displayed kernel. -/
theorem specialLinear_range_eq_ker_auxiliaryTypeToUnits :
    (SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField p n)).range =
      (auxiliaryTypeToUnits p n).ker := by
  ext g
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨s, rfl⟩
    apply Units.ext
    simp
  · intro hdet
    exact ⟨⟨g, Units.ext_iff.mp hdet⟩, Units.ext rfl⟩

/-- The kernel of the displayed homomorphism is the commutator subgroup. -/
theorem ker_auxiliaryTypeToUnits (hn : 0 < n) (hq : 2 < Nat.card (GaloisField p n)) :
    (auxiliaryTypeToUnits p n).ker = commutator (AuxiliaryType p n) := by
  rw [← specialLinear_range_eq_ker_auxiliaryTypeToUnits,
    RepresentationTheory.SpecialLinear.Commutator.generalLinear_commutator_eq_specialLinear_range p n
      hn hq]

/-- The displayed kernel is contained in the kernel of every complex character. -/
theorem ker_auxiliaryTypeToUnits_le_ker_character (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n))
    (ρ : AuxiliaryType p n →* ℂˣ) : (auxiliaryTypeToUnits p n).ker ≤ ρ.ker := by
  rw [ker_auxiliaryTypeToUnits p n hn hq]
  exact Abelianization.commutator_subset_ker ρ

/-- An equivalence between characters of field units and characters of the auxiliary type. -/
@[source_ref "Chapter5/Discussion_1dim_reps" (role := supporting),
  source_ref "Chapter5/Discussion_1dim_reps/Derived01" (role := supporting)]
noncomputable def unitsCharacterEquiv (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) :
    ((GaloisField p n)ˣ →* ℂˣ) ≃ (AuxiliaryType p n →* ℂˣ) :=
  (MonoidHom.liftOfSurjective (auxiliaryTypeToUnits p n)
    (auxiliaryTypeToUnits_surjective p n)).symm.trans
    (Equiv.subtypeUnivEquiv (fun ρ => ker_auxiliaryTypeToUnits_le_ker_character p n hn hq ρ))

/-- The character equivalence is given by composition with the displayed homomorphism. -/
@[simp, source_ref "Chapter5/Discussion_1dim_reps/Derived01" (role := supporting)]
theorem unitsCharacterEquiv_apply (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) (ξ : (GaloisField p n)ˣ →* ℂˣ) :
    unitsCharacterEquiv p n hn hq ξ = ξ.comp (auxiliaryTypeToUnits p n) :=
  rfl

/-- Computes the number of homomorphisms from the auxiliary type to complex units. -/
@[source_ref "Chapter5/Discussion_1dim_reps" (role := supporting),
  source_ref "Chapter5/Discussion_1dim_reps/Derived01" (role := supporting)]
theorem card_auxiliaryType_complexCharacters (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) :
    Nat.card (AuxiliaryType p n →* ℂˣ) = Nat.card (GaloisField p n) - 1 := by
  haveI : NeZero ((Monoid.exponent (GaloisField p n)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← Nat.card_congr (unitsCharacterEquiv p n hn hq),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (GaloisField p n)ˣ ℂ,
    Nat.card_units]

end RepresentationTheory.AuxiliaryTypeCharacters
