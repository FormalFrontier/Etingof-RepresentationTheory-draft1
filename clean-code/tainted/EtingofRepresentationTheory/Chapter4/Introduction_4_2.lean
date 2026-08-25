import Mathlib.RepresentationTheory.Character
import EtingofRepresentationTheory.Chapter3.Theorem3_6_2

/-!
# Section 4.2: Characters and class functions

This file packages the definitions from the section introduction.  The ambient function space
`F(G, k)` is Lean's function type `G → k`; `classFunctions k G` is its subspace consisting of
functions constant on conjugacy classes.
-/

open FDRep

namespace Etingof

universe u v

variable (k : Type u) (G : Type v) [Group G]

section Semiring

variable [Semiring k]

/-- The space `F(G, k)` of `k`-valued functions on `G`. -/
abbrev FunctionSpace := G → k

/-- The subspace `F_c(G, k)` of functions constant on conjugacy classes. -/
def classFunctionSubmodule : Submodule k (FunctionSpace k G) where
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

@[simp]
theorem mem_classFunctionSubmodule_iff (f : FunctionSpace k G) :
    f ∈ classFunctionSubmodule k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl

end Semiring

variable [Field k]

/-- The character of a finite-dimensional representation is a class function. -/
theorem FDRep.character_mem_classFunctionSubmodule (V : FDRep k G) :
    V.character ∈ classFunctionSubmodule k G := by
  intro g h
  exact V.char_conj g h

/-- The group character is the restriction to `G ⊆ k[G]` of the character of the
associated `k[G]`-module. -/
theorem FDRep.character_eq_algebraCharacter (V : FDRep k G) (g : G) :
    V.character g =
      Etingof.character k (MonoidAlgebra k G) (Representation.asModule V.ρ)
        (MonoidAlgebra.of k G g) := by
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

end Etingof
