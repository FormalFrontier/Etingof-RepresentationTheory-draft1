/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Opposite
import RepresentationTheory.Alignment.Attribute

/-!
# Actions of rings and algebras

Constructions relating module structures to algebra homomorphisms into linear endomorphisms.
-/

namespace RepresentationTheory.Algebra.ModuleActions

/-- An auxiliary type associated with a ring and an additive commutative group. -/
@[source_ref "Chapter2/Example2.3.3/Derived4" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
abbrev RingAddCommGroupAuxiliary (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module A V

/-- A second auxiliary type associated with a ring and an additive commutative group. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
abbrev RingAddCommGroupAuxiliary' (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module Aᵐᵒᵖ V

namespace RingAddCommGroupAuxiliary

section Associativity

variable {A V : Type*} [Ring A] [AddCommGroup V]

/-- Scalar multiplication by a product agrees with successive scalar multiplication. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
theorem mul_smul [Module A V] (a b : A) (v : V) :
    (a * b) • v = a • (b • v) :=
  SemigroupAction.mul_smul a b v

/-- The action of the opposite of a product is successive action in reversed order. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
theorem op_mul_smul [Module Aᵐᵒᵖ V] (a b : A) (v : V) :
    MulOpposite.op (a * b) • v = MulOpposite.op b • (MulOpposite.op a • v) := by
  change (MulOpposite.op b * MulOpposite.op a) • v = _
  exact SemigroupAction.mul_smul _ _ _

end Associativity

section ToAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The scalar action of an algebra defines a homomorphism to linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived9" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
def actionAlgHom : A →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

/-- Evaluating the action homomorphism at an algebra element gives its scalar action. -/
@[simp]
theorem actionAlgHom_apply (a : A) (v : V) : actionAlgHom k A V a v = a • v := rfl

end ToAlgHom

section OfAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V]

/-- Constructs a module structure from an algebra homomorphism into linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
abbrev moduleOfAlgHom (ρ : A →ₐ[k] Module.End k V) : Module A V :=
  Module.compHom V ρ.toRingHom

/-- The induced action of an algebra element is its image endomorphism applied to the vector. -/
theorem moduleOfAlgHom_smul_apply (ρ : A →ₐ[k] Module.End k V) (a : A) (v : V) :
    letI := moduleOfAlgHom k A V ρ
    a • v = ρ a v := rfl

/-- The module structure induced by an algebra homomorphism is compatible with the base-ring
action. -/
theorem moduleOfAlgHom_isScalarTower (ρ : A →ₐ[k] Module.End k V) :
    letI := moduleOfAlgHom k A V ρ
    IsScalarTower k A V := by
  letI := moduleOfAlgHom k A V ρ
  refine IsScalarTower.of_algebraMap_smul fun r x => ?_
  rw [moduleOfAlgHom_smul_apply k A V ρ (algebraMap k A r) x, ρ.commutes r,
    Module.algebraMap_end_apply]

/-- The action homomorphism determined by a module structure equals any homomorphism that induces
that structure. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
theorem actionAlgHom_eq (ρ : A →ₐ[k] Module.End k V) :
    letI := moduleOfAlgHom k A V ρ
    letI := moduleOfAlgHom_isScalarTower k A V ρ
    actionAlgHom k A V = ρ := by
  letI := moduleOfAlgHom k A V ρ
  letI := moduleOfAlgHom_isScalarTower k A V ρ
  ext a v
  exact (actionAlgHom_apply k A V a v).trans (moduleOfAlgHom_smul_apply k A V ρ a v)

end OfAlgHom

section RoundTrip

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Reconstructing a module structure from its associated action homomorphism returns the existing
structure. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
theorem moduleOfAlgHom_actionAlgHom :
    moduleOfAlgHom k A V (actionAlgHom k A V) = (inferInstance : Module A V) := rfl

end RoundTrip

section RightToAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module Aᵐᵒᵖ V] [IsScalarTower k Aᵐᵒᵖ V]

/-- The action of the opposite algebra yields an algebra homomorphism into linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
def oppositeActionAlgHom : Aᵐᵒᵖ →ₐ[k] Module.End k V :=
  actionAlgHom k Aᵐᵒᵖ V

/-- The opposite-action homomorphism evaluates to the given opposite-ring scalar action. -/
@[simp]
theorem oppositeActionAlgHom_apply (a : A) (v : V) :
    oppositeActionAlgHom k A V (MulOpposite.op a) v = MulOpposite.op a • v :=
  rfl

end RightToAlgHom

end RingAddCommGroupAuxiliary

end RepresentationTheory.Algebra.ModuleActions
