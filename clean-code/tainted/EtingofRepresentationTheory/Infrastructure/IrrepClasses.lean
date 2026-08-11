/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import Mathlib

/-!
# Isomorphism classes of irreducible representations

This file isolates `Etingof.IrrepClasses k G`, the type of isomorphism classes of
irreducible (simple) finite-dimensional representations of `G` over `k`, together with
the quotient API needed to work with it.

The type was originally introduced inside `Chapter4/Exercise4_2_3.lean` for a counting
argument. It is however the correct index type for *any* statement about "the irreducibles
of `G` up to isomorphism" — in particular for Definition 5.7.1, where a virtual
representation is a formal integer combination of irreducibles *modulo isomorphism*. Since
`Chapter4/Exercise4_2_3.lean` sits on top of a substantial tower of imports, the definition
lives here instead, in a file that depends on nothing but Mathlib.

## Main definitions

* `Etingof.SimpleFDRep k G` — the full subcategory of `FDRep k G` on the simple objects.
* `Etingof.IrrepClasses k G` — its objects modulo isomorphism
  (`CategoryTheory.isIsomorphicSetoid`).
* `Etingof.IrrepClasses.mk` — the class of a simple representation.
* `Etingof.IrrepClasses.lift` — the induced map out of `IrrepClasses k G` for a function on
  simple representations that is constant on isomorphism classes.
* `Etingof.IrrepClasses.repOf` — a chosen simple representative of a class.
* `Etingof.IrrepClasses.character` — the character, descended to isomorphism classes. This
  is well defined precisely because isomorphic representations have equal characters
  (`FDRep.char_iso`).

## Main statements

* `Etingof.IrrepClasses.mk_eq_mk_iff` — two simple representations have the same class
  exactly when they are isomorphic. This is the extensionality principle that makes
  `IrrepClasses` the right index type: it is what fails for coefficient data indexed by
  literal `FDRep k G` objects.
-/

open CategoryTheory

namespace Etingof

/-- The full subcategory of `FDRep k G` on the simple (irreducible) objects. -/
abbrev SimpleFDRep (k G : Type*) [Field k] [Monoid G] : Type _ :=
  ObjectProperty.FullSubcategory (fun V : FDRep k G => Simple V)

/-- The type of isomorphism classes of irreducible (simple) representations of `G` over
`k`: isomorphism classes of objects in the full subcategory of `FDRep k G` on the simple
objects. -/
def IrrepClasses (k G : Type*) [Field k] [Monoid G] : Type _ :=
  Quotient (isIsomorphicSetoid (SimpleFDRep k G))

namespace IrrepClasses

variable {k G : Type*} [Field k] [Monoid G]

/-- An isomorphism of simple representatives, read in the ambient category `FDRep k G`. -/
def isoOfSubIso {P Q : SimpleFDRep k G} (e : P ≅ Q) : P.obj ≅ Q.obj :=
  (ObjectProperty.ι (fun V : FDRep k G => Simple V)).mapIso e

/-- An ambient isomorphism between two simple representations, read as an isomorphism of the
corresponding objects of `SimpleFDRep k G`. Inverse to `isoOfSubIso`. -/
def subIsoOfIso {P Q : SimpleFDRep k G} (e : P.obj ≅ Q.obj) : P ≅ Q :=
  ObjectProperty.isoMk _ e

/-- The isomorphism class of a simple representation. -/
def mk (V : FDRep k G) (hV : Simple V) : IrrepClasses k G :=
  Quotient.mk _ ⟨V, hV⟩

/-- **Extensionality for irreducible classes.** Two simple representations determine the
same element of `IrrepClasses k G` exactly when they are isomorphic. -/
theorem mk_eq_mk_iff {V W : FDRep k G} (hV : Simple V) (hW : Simple W) :
    mk V hV = mk W hW ↔ Nonempty (V ≅ W) := by
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact ⟨isoOfSubIso e⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨subIsoOfIso (P := ⟨V, hV⟩) (Q := ⟨W, hW⟩) e⟩

/-- Isomorphic simple representations have the same class. -/
theorem mk_eq_mk_of_iso {V W : FDRep k G} (hV : Simple V) (hW : Simple W) (e : V ≅ W) :
    mk V hV = mk W hW :=
  (mk_eq_mk_iff hV hW).mpr ⟨e⟩

/-- The class of a simple representation does not depend on the simplicity proof. -/
theorem mk_congr_proof {V : FDRep k G} (hV hV' : Simple V) : mk V hV = mk V hV' :=
  mk_eq_mk_of_iso hV hV' (Iso.refl V)

theorem mk_surjective : Function.Surjective (fun P : SimpleFDRep k G => mk P.obj P.property) :=
  fun c => Quotient.inductionOn c fun P => ⟨P, rfl⟩

/-- Every irreducible class is the class of some simple representation. -/
theorem exists_mk (c : IrrepClasses k G) :
    ∃ (V : FDRep k G) (hV : Simple V), mk V hV = c := by
  obtain ⟨P, hP⟩ := mk_surjective c
  exact ⟨P.obj, P.property, hP⟩

@[elab_as_elim]
protected theorem inductionOn {p : IrrepClasses k G → Prop} (c : IrrepClasses k G)
    (h : ∀ (V : FDRep k G) (hV : Simple V), p (mk V hV)) : p c :=
  Quotient.inductionOn c fun P => h P.obj P.property

/-- A function on simple representations that is constant on isomorphism classes descends to
`IrrepClasses k G`. -/
def lift {α : Sort*} (f : ∀ V : FDRep k G, Simple V → α)
    (hf : ∀ (V W : FDRep k G) (hV : Simple V) (hW : Simple W), (V ≅ W) → f V hV = f W hW) :
    IrrepClasses k G → α :=
  Quotient.lift (fun P => f P.obj P.property) (by
    rintro P Q ⟨e⟩
    exact hf _ _ _ _ (isoOfSubIso e))

@[simp]
theorem lift_mk {α : Sort*} (f : ∀ V : FDRep k G, Simple V → α)
    (hf : ∀ (V W : FDRep k G) (hV : Simple V) (hW : Simple W), (V ≅ W) → f V hV = f W hW)
    (V : FDRep k G) (hV : Simple V) : lift f hf (mk V hV) = f V hV :=
  rfl

/-- A chosen simple representative of an irreducible class. -/
noncomputable def repOf (c : IrrepClasses k G) : FDRep k G :=
  (Quotient.out (s := isIsomorphicSetoid (SimpleFDRep k G)) c).obj

instance instSimpleRepOf (c : IrrepClasses k G) : Simple (repOf c) :=
  (Quotient.out (s := isIsomorphicSetoid (SimpleFDRep k G)) c).property

@[simp]
theorem mk_repOf (c : IrrepClasses k G) : mk (repOf c) (instSimpleRepOf c) = c :=
  Quotient.out_eq c

theorem mk_repOf' (c : IrrepClasses k G) (h : Simple (repOf c)) : mk (repOf c) h = c :=
  (mk_congr_proof h (instSimpleRepOf c)).trans (mk_repOf c)

/-- The chosen representative of the class of `V` is isomorphic to `V`. -/
theorem nonempty_iso_repOf_mk {V : FDRep k G} (hV : Simple V) :
    Nonempty (repOf (mk V hV) ≅ V) :=
  (mk_eq_mk_iff (instSimpleRepOf _) hV).mp (mk_repOf (mk V hV))

/-- **Distinctness of the chosen representatives.** Two chosen representatives are
isomorphic only if the classes coincide; this is what lets a family indexed by irreducible
classes be fed to statements requiring pairwise non-isomorphic irreducibles. -/
@[simp]
theorem nonempty_repOf_iso_repOf_iff (c d : IrrepClasses k G) :
    Nonempty (repOf c ≅ repOf d) ↔ c = d := by
  rw [← mk_eq_mk_iff (instSimpleRepOf c) (instSimpleRepOf d), mk_repOf, mk_repOf]

/-! ### Characters of irreducible classes

Isomorphic representations have equal characters (`FDRep.char_iso`), so the character is a
function of the isomorphism class alone. -/

/-- The character of an irreducible class: the common character of all simple
representations in it. -/
noncomputable def character (c : IrrepClasses k G) : G → k :=
  lift (fun V _ => V.character) (fun _ _ _ _ e => FDRep.char_iso e) c

@[simp]
theorem character_mk (V : FDRep k G) (hV : Simple V) :
    character (mk V hV) = V.character :=
  rfl

@[simp]
theorem character_repOf (c : IrrepClasses k G) : (repOf c).character = character c := by
  rw [← character_mk (repOf c) (instSimpleRepOf c), mk_repOf]

/-- The dimension of an irreducible class: the common dimension of all simple
representations in it. -/
noncomputable def finrank (c : IrrepClasses k G) : ℕ :=
  lift (fun V _ => Module.finrank k V)
    (fun _ _ _ _ e => LinearEquiv.finrank_eq
      ((forget₂ (FDRep k G) (FGModuleCat k) ⋙ forget₂ (FGModuleCat k) (ModuleCat k)).mapIso
        e).toLinearEquiv) c

@[simp]
theorem finrank_mk (V : FDRep k G) (hV : Simple V) :
    finrank (mk V hV) = Module.finrank k V :=
  rfl

@[simp]
theorem finrank_repOf (c : IrrepClasses k G) : Module.finrank k (repOf c) = finrank c := by
  rw [← finrank_mk (repOf c) (instSimpleRepOf c), mk_repOf]

/-- The character at the identity is the dimension. -/
@[simp]
theorem character_one (c : IrrepClasses k G) : character c 1 = (finrank c : k) := by
  induction c using IrrepClasses.inductionOn with
  | _ V hV => rw [character_mk, finrank_mk, FDRep.char_one]

end IrrepClasses

end Etingof
