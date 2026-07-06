import Mathlib

/-!
# Problem 2.14.3: The tensor-Hom adjunction for Lie algebra representations

Let `V, W, U` be finite dimensional representations of a Lie algebra `𝔤`. The problem asks to show
that `Hom_𝔤(V ⊗ W, U)` is isomorphic to `Hom_𝔤(V, U ⊗ W*)`.

## Formalization

Representations of `𝔤` are Lie modules; `Hom_𝔤(A, B)` is the space of Lie-module homomorphisms
`A →ₗ⁅k,L⁆ B`. The tensor product `V ⊗ W` carries its Lie-module structure from
`Mathlib.Algebra.Lie.TensorProduct`, and `W* = Module.Dual k W` carries the contragredient
Lie-module structure from `Module.Dual.instLieModule`. The isomorphism is `k`-linear.

This is the **statement pass**: recorded as the existence of a `k`-linear equivalence with a
`sorry` proof.
-/

namespace Etingof.Problem2_14_3

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V W U : Type*}
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
  [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]
  [AddCommGroup U] [Module k U] [LieRingModule L U] [LieModule k L U]
  [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k U]

/-- **Problem 2.14.3.** For finite dimensional representations `V, W, U` of a Lie algebra `𝔤`,
`Hom_𝔤(V ⊗ W, U) ≅ Hom_𝔤(V, U ⊗ W*)`. -/
theorem exists_tensorHom_adjunction :
    Nonempty ((TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (V →ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W))) := by
  sorry

end Etingof.Problem2_14_3
