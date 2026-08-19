/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Batteries.Util.ProofWanted
import RepresentationTheory.Algebra.Lie.Basic

/-!
# Faithful finite-dimensional representations of Lie algebras
-/

namespace RepresentationTheory.Algebra.Lie.FaithfulFiniteDimensionalRepresentation

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [Field k]
variable (L : Type u) [LieRing L] [LieAlgebra k L]

/-- An injective Lie homomorphism into a finite-dimensional algebra yields a faithful representation of the Lie algebra. -/
theorem exists_faithfulRepresentation_of_injective_lieHom {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A] (f : L →ₗ⁅k⁆ A) (hf : Function.Injective f) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    (Algebra.lmul k A).toLieHom.comp f, ?_⟩
  exact Algebra.lmul_injective.comp hf

/-- An algebra map from the universal enveloping algebra that is injective on the canonical Lie image yields a faithful representation. -/
theorem exists_faithfulRepresentation_of_envelopingMap_injective {A : Type u} [Ring A]
    [Algebra k A] [FiniteDimensional k A]
    (q : UniversalEnvelopingAlgebra k L →ₐ[k] A)
    (hq : Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x))) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  exact exists_faithfulRepresentation_of_injective_lieHom k L
    (q.toLieHom.comp (UniversalEnvelopingAlgebra.ι k)) hq

/-- A faithful finite-dimensional representation gives an algebra map from the universal enveloping algebra that is injective on the canonical Lie image. -/
theorem exists_envelopingMap_injective_of_faithfulRepresentation
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : L →ₗ⁅k⁆ Module.End k V) (hρ : Function.Injective ρ) :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
        Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  refine ⟨Module.End k V, inferInstance, inferInstance, inferInstance,
    UniversalEnvelopingAlgebra.lift k ρ, ?_⟩
  intro x y hxy
  apply hρ
  simpa using hxy

/-- Existence of a faithful representation is equivalent to existence of a suitable algebra map from the universal enveloping algebra that is injective on the canonical Lie image. -/
theorem exists_faithfulRepresentation_iff_exists_envelopingMap_injective :
    (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
        (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ) ↔
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
        (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
          Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  constructor
  · rintro ⟨V, _, _, _, ρ, hρ⟩
    exact exists_envelopingMap_injective_of_faithfulRepresentation k L ρ hρ
  · rintro ⟨A, _, _, _, q, hq⟩
    exact exists_faithfulRepresentation_of_envelopingMap_injective k L q hq

proof_wanted ado [FiniteDimensional k L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ

end RepresentationTheory.Algebra.Lie.FaithfulFiniteDimensionalRepresentation
