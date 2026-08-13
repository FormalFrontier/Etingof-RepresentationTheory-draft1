/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RepresentationTheory.Character
import RepresentationTheory.Algebra.Module.Dual.SimpleFamilies

open FDRep

namespace RepresentationTheory.ConjugationInvariantCharacters

universe u v

variable (k : Type u) (G : Type v) [Group G]

section Semiring

variable [Semiring k]

/-- An auxiliary type depending on two input types. -/
@[source_ref "Chapter4/Introduction_4.2" (role := supporting)]
abbrev AuxiliaryFunctionSpace := G → k

/-- A scalar submodule of the auxiliary function space associated with a group. -/
@[source_ref "Chapter4/Introduction_4.2" (role := primary)]
def conjugationInvariantSubmodule : Submodule k (AuxiliaryFunctionSpace k G) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y
    simp only [Pi.add_apply]
    rw [hf x y, hg x y]
  smul_mem' := by
    intro r f hf x y
    simp only [Pi.smul_apply]
    rw [hf x y]

/-- An auxiliary function belongs to the displayed submodule exactly when it is invariant under conjugation. -/
@[simp, source_ref "Chapter4/Introduction_4.2" (role := primary)]
theorem mem_conjugationInvariantSubmodule_iff (f : AuxiliaryFunctionSpace k G) :
    f ∈ conjugationInvariantSubmodule k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl

end Semiring

variable [Field k]

/-- The character of a finite-dimensional group representation belongs to the conjugation-invariant submodule. -/
@[source_ref "Chapter4/Introduction_4.2" (role := primary)]
theorem character_mem_conjugationInvariantSubmodule (V : FDRep k G) :
    V.character ∈ conjugationInvariantSubmodule k G := by
  intro g h
  exact V.char_conj g h

/-- A finite-dimensional representation character equals the referenced auxiliary map evaluated on the monoid-algebra image of a group element. -/
@[source_ref "Chapter4/Introduction_4.2" (role := primary)]
theorem character_eq_auxiliaryMap_apply (V : FDRep k G) (g : G) :
    V.character g =
      RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k (MonoidAlgebra k G)
        (Representation.asModule V.ρ) (MonoidAlgebra.of k G g) := by
  letI : Module (MonoidAlgebra k G) (Representation.asModule V.ρ) :=
    Representation.instModuleMonoidAlgebraAsModule V.ρ
  change LinearMap.trace k V (V.ρ g) =
    LinearMap.trace k (Representation.asModule V.ρ)
      ((Algebra.lsmul k k (Representation.asModule V.ρ)) (MonoidAlgebra.of k G g))
  rw [← LinearMap.trace_conj' (V.ρ g) (Representation.asModuleEquiv V.ρ).symm]
  congr 1
  ext x
  change (Representation.asModuleEquiv V.ρ).symm
      (V.ρ g ((Representation.asModuleEquiv V.ρ) x)) =
    ((MonoidAlgebra.of k G g) • x : Representation.asModule V.ρ)
  apply (Representation.asModuleEquiv V.ρ).injective
  rw [LinearEquiv.apply_symm_apply,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

end RepresentationTheory.ConjugationInvariantCharacters
