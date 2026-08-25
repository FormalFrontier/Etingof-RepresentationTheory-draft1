import EtingofRepresentationTheory.Chapter3.Theorem3_6_2

/-!
# Introduction to Section 3.6: Characters vanish on commutators

The character of a finite dimensional representation `V` of an algebra `A` is the linear
function `χ_V : A → k`, `χ_V(a) = Tr|_V(ρ(a))` (defined as `Etingof.character` in
`Theorem3_6_2`).

This file formalizes the prose claim from the section introduction: if `[A, A]` is the
span of the commutators `[x, y] = xy - yx`, then `[A, A] ⊆ ker χ_V`, because the trace is
cyclic (`tr(ρ(x)ρ(y)) = tr(ρ(y)ρ(x))`, `LinearMap.trace_mul_comm`). Consequently the
character factors through the quotient `A/[A, A]`.
-/

open Module

variable (k : Type*) (A : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [Free k V] [Module.Finite k V]

namespace Etingof

/-- The character is a class function on commutators: `χ_V(xy) = χ_V(yx)`. This is the
cyclic property of the trace, since `ρ` is an algebra homomorphism. -/
theorem character_mul_comm (x y : A) :
    character k A V (x * y) = character k A V (y * x) := by
  simp only [character, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  exact LinearMap.trace_mul_comm k _ _

/-- The commutator submodule `[A, A]`: the `k`-span of all commutators `xy - yx`. -/
def commutatorSubmodule : Submodule k A :=
  Submodule.span k {z : A | ∃ x y : A, z = x * y - y * x}

/-- Every commutator lies in the kernel of the character: `[A, A] ⊆ ker χ_V`. -/
theorem commutatorSubmodule_le_ker_character :
    commutatorSubmodule k A ≤ LinearMap.ker (character k A V) := by
  rw [commutatorSubmodule, Submodule.span_le]
  rintro z ⟨x, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
  rw [character_mul_comm, sub_self]

/-- The character viewed as a map on the quotient `A/[A, A] → k`. This is the factorization
`χ_V : A/[A, A] → k` asserted in the prose. -/
noncomputable def characterQuotient : (A ⧸ commutatorSubmodule k A) →ₗ[k] k :=
  Submodule.liftQ _ (character k A V) (commutatorSubmodule_le_ker_character k A V)

/-- The quotient character recovers the character after composing with the projection:
`characterQuotient ∘ mkQ = character`. -/
theorem characterQuotient_mk (a : A) :
    characterQuotient k A V (Submodule.Quotient.mk a) = character k A V a :=
  rfl

end Etingof
