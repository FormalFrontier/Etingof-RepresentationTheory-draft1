/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib

/-!
# Simple characters of finite-dimensional representations
-/

open CategoryTheory

namespace RepresentationTheory.FDRep.SimpleCharacters

/-- Auxiliary object data for a full subcategory of finite-dimensional representations. -/
abbrev SimpleObjectData (k G : Type*) [Field k] [Monoid G] : Type _ :=
  ObjectProperty.FullSubcategory (fun V : FDRep k G => Simple V)

/-- Data representing an isomorphism class of simple finite-dimensional representations of a
monoid. -/
def SimpleCharacter (k G : Type*) [Field k] [Monoid G] : Type _ :=
  Quotient (isIsomorphicSetoid (SimpleObjectData k G))

namespace SimpleCharacter

variable {k G : Type*} [Field k] [Monoid G]

/-- An isomorphism between auxiliary simple-object data induces an isomorphism between their
underlying objects. -/
def simpleObjectIso {P Q : SimpleObjectData k G} (e : P ≅ Q) : P.obj ≅ Q.obj :=
  (ObjectProperty.ι (fun V : FDRep k G => Simple V)).mapIso e

/-- An isomorphism of the underlying objects induces an isomorphism between the auxiliary
simple-object data. -/
def simpleObjectIsoOfUnderlying {P Q : SimpleObjectData k G} (e : P.obj ≅ Q.obj) : P ≅ Q :=
  ObjectProperty.isoMk _ e

/-- Simple-character data associated with a simple finite-dimensional representation. -/
def ofSimple (V : FDRep k G) (hV : Simple V) : SimpleCharacter k G :=
  Quotient.mk _ ⟨V, hV⟩

/-- Two simple representations determine equal data exactly when they are isomorphic. -/
theorem ofSimple_eq_iff_nonempty_iso {V W : FDRep k G} (hV : Simple V) (hW : Simple W) :
    ofSimple V hV = ofSimple W hW ↔ Nonempty (V ≅ W) := by
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact ⟨simpleObjectIso e⟩
  · rintro ⟨e⟩
    exact Quotient.sound
      ⟨simpleObjectIsoOfUnderlying (P := ⟨V, hV⟩) (Q := ⟨W, hW⟩) e⟩

/-- Isomorphic simple representations determine equal simple-character data. -/
theorem ofSimple_eq_of_iso {V W : FDRep k G} (hV : Simple V) (hW : Simple W) (e : V ≅ W) :
    ofSimple V hV = ofSimple W hW :=
  (ofSimple_eq_iff_nonempty_iso hV hW).mpr ⟨e⟩

/-- The data associated with a simple representation does not depend on the chosen simplicity
proof. -/
theorem ofSimple_proof_irrel {V : FDRep k G} (hV hV' : Simple V) :
    ofSimple V hV = ofSimple V hV' :=
  ofSimple_eq_of_iso hV hV' (Iso.refl V)

/-- Mapping auxiliary simple objects to their simple-character data is surjective. -/
theorem ofSimple_surjective_fromSimpleObjects :
    Function.Surjective (fun P : SimpleObjectData k G => ofSimple P.obj P.property) :=
  fun c => Quotient.inductionOn c fun P => ⟨P, rfl⟩

/-- Every simple-character datum is obtained from some simple finite-dimensional
representation. -/
theorem exists_ofSimple_eq (c : SimpleCharacter k G) :
    ∃ (V : FDRep k G) (hV : Simple V), ofSimple V hV = c := by
  obtain ⟨P, hP⟩ := ofSimple_surjective_fromSimpleObjects c
  exact ⟨P.obj, P.property, hP⟩

/-- A property holding for the data of every simple representation holds for all
simple-character data. -/
@[elab_as_elim]
protected theorem induction_on {p : SimpleCharacter k G → Prop} (c : SimpleCharacter k G)
    (h : ∀ (V : FDRep k G) (hV : Simple V), p (ofSimple V hV)) : p c :=
  Quotient.inductionOn c fun P => h P.obj P.property

/-- An isomorphism-invariant assignment on simple representations descends to simple-character
data. -/
def rec {α : Sort*} (f : ∀ V : FDRep k G, Simple V → α)
    (hf : ∀ (V W : FDRep k G) (hV : Simple V) (hW : Simple W),
      (V ≅ W) → f V hV = f W hW) :
    SimpleCharacter k G → α :=
  Quotient.lift (fun P => f P.obj P.property) (by
    rintro P Q ⟨e⟩
    exact hf _ _ _ _ (simpleObjectIso e))

/-- The descended assignment evaluates on data from a simple representation as the original
assignment. -/
@[simp]
theorem rec_ofSimple {α : Sort*} (f : ∀ V : FDRep k G, Simple V → α)
    (hf : ∀ (V W : FDRep k G) (hV : Simple V) (hW : Simple W),
      (V ≅ W) → f V hV = f W hW)
    (V : FDRep k G) (hV : Simple V) : rec f hf (ofSimple V hV) = f V hV :=
  rfl

/-- A finite-dimensional representative attached to simple-character data. -/
noncomputable def representation (c : SimpleCharacter k G) : FDRep k G :=
  (Quotient.out (s := isIsomorphicSetoid (SimpleObjectData k G)) c).obj

/-- The representative attached to simple-character data is a simple object. -/
instance simple_representation (c : SimpleCharacter k G) : Simple (representation c) :=
  (Quotient.out (s := isIsomorphicSetoid (SimpleObjectData k G)) c).property

/-- Forming simple-character data from its representative recovers the original datum. -/
@[simp]
theorem ofSimple_representation (c : SimpleCharacter k G) :
    ofSimple (representation c) (simple_representation c) = c :=
  Quotient.out_eq c

/-- Using any simplicity proof for the representative recovers the original simple-character
datum. -/
theorem ofSimple_representation_withProof (c : SimpleCharacter k G)
    (h : Simple (representation c)) : ofSimple (representation c) h = c :=
  (ofSimple_proof_irrel h (simple_representation c)).trans (ofSimple_representation c)

/-- The representative of the data from a simple representation is isomorphic to that
representation. -/
theorem representation_ofSimple_iso {V : FDRep k G} (hV : Simple V) :
    Nonempty (representation (ofSimple V hV) ≅ V) :=
  (ofSimple_eq_iff_nonempty_iso (simple_representation _) hV).mp
    (ofSimple_representation (ofSimple V hV))

/-- Representatives of two simple-character data are isomorphic exactly when the data are
equal. -/
@[simp]
theorem representation_iso_iff_eq (c d : SimpleCharacter k G) :
    Nonempty (representation c ≅ representation d) ↔ c = d := by
  rw [← ofSimple_eq_iff_nonempty_iso (simple_representation c) (simple_representation d),
    ofSimple_representation, ofSimple_representation]

/-- The field-valued function on the monoid associated with simple-character data. -/
noncomputable def value (c : SimpleCharacter k G) : G → k :=
  rec (fun V _ => V.character) (fun _ _ _ _ e => FDRep.char_iso e) c

/-- The value function attached to a simple representation is its character. -/
@[simp]
theorem value_ofSimple (V : FDRep k G) (hV : Simple V) :
    value (ofSimple V hV) = V.character :=
  rfl

/-- The character of the representative equals the value function of the simple-character
data. -/
@[simp]
theorem character_representation (c : SimpleCharacter k G) :
    (representation c).character = value c := by
  rw [← value_ofSimple (representation c) (simple_representation c), ofSimple_representation]

/-- The natural-number dimension associated with simple-character data. -/
noncomputable def dimension (c : SimpleCharacter k G) : ℕ :=
  rec (fun V _ => Module.finrank k V)
    (fun _ _ _ _ e => LinearEquiv.finrank_eq
      ((forget₂ (FDRep k G) (FGModuleCat k) ⋙ forget₂ (FGModuleCat k) (ModuleCat k)).mapIso
        e).toLinearEquiv) c

/-- The dimension attached to a simple representation equals its vector-space dimension. -/
@[simp]
theorem dimension_ofSimple (V : FDRep k G) (hV : Simple V) :
    dimension (ofSimple V hV) = Module.finrank k V :=
  rfl

/-- The vector-space dimension of the representative equals the stored dimension. -/
@[simp]
theorem finrank_representation (c : SimpleCharacter k G) :
    Module.finrank k (representation c) = dimension c := by
  rw [← dimension_ofSimple (representation c) (simple_representation c),
    ofSimple_representation]

/-- The value at the identity equals the field cast of the stored dimension. -/
@[simp]
theorem value_one (c : SimpleCharacter k G) : value c 1 = (dimension c : k) := by
  induction c using SimpleCharacter.induction_on with
  | _ V hV => rw [value_ofSimple, dimension_ofSimple, FDRep.char_one]

end SimpleCharacter

end RepresentationTheory.FDRep.SimpleCharacters
