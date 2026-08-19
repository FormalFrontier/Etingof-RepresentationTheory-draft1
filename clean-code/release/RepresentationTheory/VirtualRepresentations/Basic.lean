/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.FDRep.SimpleCharacters
import RepresentationTheory.Alignment.Attribute

/-!
# Virtual representations

This module defines virtual complex representations of a finite group, together with their
coefficients, characters, and dimensions.
-/

open CategoryTheory
open RepresentationTheory.FDRep.SimpleCharacters

namespace RepresentationTheory.VirtualRepresentations.Basic

/-- The type of virtual complex representations of a finite group. -/
@[source_ref "Chapter5/Introduction_5.7" (role := supporting),
  source_ref "Chapter5/Definition5.7.1" (role := supporting)]
abbrev VirtualRepresentation (G : Type) [Group G] [Fintype G] : Type _ :=
  SimpleCharacter ℂ G →₀ ℤ

namespace VirtualRepresentation

variable {G : Type} [Group G] [Fintype G]

/-- The integer coefficient of a simple representation in a virtual representation. -/
noncomputable def coeff (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) : ℤ :=
  V (SimpleCharacter.ofSimple W hW)

/-- Isomorphic simple representations have equal coefficients in a virtual representation. -/
theorem coeff_eq_of_iso (V : VirtualRepresentation G) {W W' : FDRep ℂ G}
    (hW : Simple W) (hW' : Simple W') (e : W ≅ W') : V.coeff W hW = V.coeff W' hW' := by
  rw [coeff, coeff, SimpleCharacter.ofSimple_eq_of_iso hW hW' e]

/-- The coefficient of a fixed representation is independent of the proof that it is simple. -/
theorem coeff_independent_of_simple (V : VirtualRepresentation G) {W : FDRep ℂ G}
    (hW hW' : Simple W) : V.coeff W hW = V.coeff W hW' :=
  V.coeff_eq_of_iso hW hW' (Iso.refl W)

/-- Every simple coefficient of the zero virtual representation is zero. -/
@[simp]
theorem coeff_zero (W : FDRep ℂ G) (hW : Simple W) :
    (0 : VirtualRepresentation G).coeff W hW = 0 := rfl

/-- The coefficient of a simple representation in a sum is the sum of its coefficients. -/
@[simp]
theorem coeff_add (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V + V').coeff W hW = V.coeff W hW + V'.coeff W hW := rfl

/-- The coefficient in the negative of a virtual representation is the negative coefficient. -/
@[simp]
theorem coeff_neg (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (-V).coeff W hW = -V.coeff W hW := rfl

/-- The coefficient in a difference is the difference of the coefficients. -/
@[simp]
theorem coeff_sub (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V - V').coeff W hW = V.coeff W hW - V'.coeff W hW := rfl

/-- Two virtual representations are equal when all their simple coefficients agree. -/
theorem ext {V V' : VirtualRepresentation G}
    (h : ∀ (W : FDRep ℂ G) (hW : Simple W), V.coeff W hW = V'.coeff W hW) : V = V' := by
  ext c
  induction c using SimpleCharacter.induction_on with
  | _ W hW => exact h W hW

/-- The virtual representation given by an integer multiple of a simple representation. -/
noncomputable def simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    VirtualRepresentation G :=
  Finsupp.single (SimpleCharacter.ofSimple W hW) n

/-- Isomorphic simple representations have equal virtual integer multiples. -/
theorem simpleMultiple_eq_of_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    (e : W ≅ W') (n : ℤ) : simpleMultiple W hW n = simpleMultiple W' hW' n := by
  rw [simpleMultiple, simpleMultiple, SimpleCharacter.ofSimple_eq_of_iso hW hW' e]

/-- The zero multiple of a simple representation is the zero virtual representation. -/
@[simp]
theorem simpleMultiple_zero (W : FDRep ℂ G) (hW : Simple W) : simpleMultiple W hW 0 = 0 :=
  Finsupp.single_zero _

/-- The virtual representation attached to a sum of integers is the sum of the corresponding
simple multiples. -/
@[simp]
theorem simpleMultiple_add (W : FDRep ℂ G) (hW : Simple W) (m n : ℤ) :
    simpleMultiple W hW (m + n) = simpleMultiple W hW m + simpleMultiple W hW n :=
  Finsupp.single_add _ _ _

/-- The coefficient of a simple representation in its own integer multiple is that integer. -/
theorem coeff_simpleMultiple_self (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (simpleMultiple W hW n).coeff W hW = n := by
  simp [coeff, simpleMultiple]

/-- An integer multiple of a simple representation is zero exactly when the integer is zero. -/
@[simp]
theorem simpleMultiple_eq_zero_iff (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    simpleMultiple W hW n = 0 ↔ n = 0 :=
  Finsupp.single_eq_zero

/-- Simple representations are isomorphic when equal nonzero integer multiples of them define
the same virtual representation. -/
theorem iso_of_simpleMultiple_eq {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : simpleMultiple W hW n = simpleMultiple W' hW' n) :
    Nonempty (W ≅ W') := by
  rw [← SimpleCharacter.ofSimple_eq_iff_nonempty_iso hW hW']
  simpa [simpleMultiple, Finsupp.single_eq_single_iff, hn] using h

/-- Nonzero multiples of nonisomorphic simple representations are distinct. -/
theorem simpleMultiple_ne_of_not_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : IsEmpty (W ≅ W')) :
    simpleMultiple W hW n ≠ simpleMultiple W' hW' n :=
  fun heq => (iso_of_simpleMultiple_eq hW hW' hn heq).elim h.elim

/-- An auxiliary theorem whose formal statement is unavailable. -/
theorem auxiliary {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    (e : W ≅ W') : simpleMultiple W hW 1 + simpleMultiple W' hW' (-1) = 0 := by
  rw [simpleMultiple_eq_of_iso hW hW' e 1, simpleMultiple, simpleMultiple,
    ← Finsupp.single_add, add_neg_cancel, Finsupp.single_zero]

/-- The additive homomorphism sending a virtual representation to its complex-valued character. -/
@[source_ref "Chapter5/Definition5.7.1" (role := supporting)]
noncomputable def character : VirtualRepresentation G →+ (G → ℂ) :=
  Finsupp.liftAddHom (α := SimpleCharacter ℂ G) (M := ℤ) (N := G → ℂ)
    fun c => zmultiplesHom (G → ℂ) (SimpleCharacter.value c)

/-- The character value of a virtual representation is the finite sum of its coefficients times
the associated character values. -/
@[source_ref "Chapter5/Definition5.7.1" (role := primary)]
theorem character_apply (V : VirtualRepresentation G) (g : G) :
    character V g = ∑ c ∈ V.support, (V c : ℂ) * SimpleCharacter.value c g := by
  rw [character, Finsupp.liftAddHom_apply]
  simp only [Finsupp.sum, zmultiplesHom_apply, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply,
    Pi.intCast_apply]

/-- The character of the zero virtual representation is zero. -/
@[simp]
theorem character_zero : character (0 : VirtualRepresentation G) = 0 :=
  map_zero _

/-- The character of a sum of virtual representations is the sum of their characters. -/
@[simp]
theorem character_add (V V' : VirtualRepresentation G) :
    character (V + V') = character V + character V' :=
  map_add _ _ _

/-- The character of the negative of a virtual representation is the negative of its character. -/
@[simp]
theorem character_neg (V : VirtualRepresentation G) : character (-V) = -character V :=
  map_neg _ _

/-- The character of a difference of virtual representations is the difference of their
characters. -/
@[simp]
theorem character_sub (V V' : VirtualRepresentation G) :
    character (V - V') = character V - character V' :=
  map_sub _ _ _

/-- The character of a single supported coefficient is the corresponding integer multiple of
its character. -/
@[simp, source_ref "Chapter5/Definition5.7.1" (role := supporting)]
theorem character_single (c : SimpleCharacter ℂ G) (n : ℤ) :
    character (Finsupp.single c n) = n • SimpleCharacter.value c :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The character of an integer multiple of a simple representation is that integer times its
character. -/
@[simp]
theorem character_simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    character (simpleMultiple W hW n) = n • W.character := by
  rw [simpleMultiple, character_single, SimpleCharacter.value_ofSimple]

/-- The virtual character associated with one copy of a simple representation is its ordinary
character. -/
theorem character_simple (W : FDRep ℂ G) (hW : Simple W) :
    character (simpleMultiple W hW 1) = W.character := by
  rw [character_simpleMultiple, one_smul]

/-- The integer-valued dimension of a virtual representation. -/
noncomputable def dim (V : VirtualRepresentation G) : ℤ :=
  V.sum fun c n => n * (SimpleCharacter.dimension c : ℤ)

/-- The dimension is the sum over the support of each coefficient times the corresponding
dimension. -/
theorem dim_eq_sum_support (V : VirtualRepresentation G) :
    V.dim = ∑ c ∈ V.support, V c * (SimpleCharacter.dimension c : ℤ) := rfl

/-- A virtual character evaluated at the identity is the integer cast of its dimension. -/
theorem character_one (V : VirtualRepresentation G) : character V 1 = (V.dim : ℂ) := by
  rw [character_apply, dim_eq_sum_support]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by rw [SimpleCharacter.value_one]

/-- The dimension of the zero virtual representation is zero. -/
@[simp]
theorem dim_zero : (0 : VirtualRepresentation G).dim = 0 :=
  Finsupp.sum_zero_index

/-- The dimension of an integer multiple of a simple representation is the integer times its
finite dimension. -/
@[simp]
theorem dim_simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (simpleMultiple W hW n).dim = n * (Module.finrank ℂ W : ℤ) := by
  rw [dim, simpleMultiple, Finsupp.sum_single_index (by rw [zero_mul]),
    SimpleCharacter.dimension_ofSimple]

end VirtualRepresentation

end RepresentationTheory.VirtualRepresentations.Basic
