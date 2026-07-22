import Mathlib.Algebra.Module.LinearMap.End

/-!
# Problem 2.3.17: `End_A(A) = Aᵒᵖ`

> Let `A` be an associative algebra, and let `V` be a representation of `A`. By
> `End_A(V)` one denotes the algebra of all homomorphisms of representations
> `V → V`. Show that `End_A(A) = Aᵒᵖ`, the algebra `A` with opposite
> multiplication.

Here `A` is viewed as the **regular representation**: a left module over itself.
An endomorphism of representations `A → A` is a left `A`-linear map, i.e. an
element of `Module.End A A = A →ₗ[A] A`. Such a map `f` is determined by
`a := f 1`, because `f x = f (x • 1) = x • f 1 = x * a`; that is, `f` is *right*
multiplication by `a`. Composition of two such maps corresponds to multiplication
of the elements in the **opposite** order:
`(f ∘ g) 1 = f (g 1) = f (1 * b) = b * a`, where `a = f 1`, `b = g 1`. Hence the
endomorphism algebra is `A` with its multiplication reversed, `Aᵒᵖ`.

## Mathlib correspondence

Mathlib packages exactly this fact as `RingEquiv.moduleEndSelf`, the ring
isomorphism `Aᵐᵒᵖ ≃+* Module.End A A` given by sending `MulOpposite.op a` to
right multiplication by `a`. Its inverse sends `f` to `MulOpposite.op (f 1)`.
We record Problem 2.3.17 in the book's stated direction — `End_A(A) ≅ Aᵒᵖ` — by
taking the symmetric equivalence.
-/

namespace Etingof

/-- **Problem 2.3.17.** The endomorphism algebra of the regular representation of
`A` (the left `A`-module `A`) is `Aᵒᵖ`, the algebra `A` with the opposite
multiplication. Concretely `End_A(A) = Module.End A A ≃+* Aᵐᵒᵖ`, sending an
`A`-linear map `f` to `MulOpposite.op (f 1)` (each `f` is right multiplication by
`f 1`, and composition reverses the order of multiplication). -/
noncomputable def EndSelfEquivOp (A : Type*) [Ring A] :
    Module.End A A ≃+* Aᵐᵒᵖ :=
  (RingEquiv.moduleEndSelf A).symm

/-- The isomorphism of Problem 2.3.17 sends an `A`-linear endomorphism `f` of the
regular representation to `MulOpposite.op (f 1)`: every such `f` is right
multiplication by the element `f 1`. -/
@[simp]
theorem EndSelfEquivOp_apply (A : Type*) [Ring A] (f : Module.End A A) :
    EndSelfEquivOp A f = MulOpposite.op (f 1) :=
  rfl

/-- The inverse of the Problem 2.3.17 isomorphism sends `MulOpposite.op a` to
right multiplication by `a`: `(EndSelfEquivOp A).symm (op a)` is the endomorphism
`x ↦ x * a` of the regular representation. -/
theorem EndSelfEquivOp_symm_op_apply (A : Type*) [Ring A] (a x : A) :
    (EndSelfEquivOp A).symm (MulOpposite.op a) x = x * a := by
  simp only [EndSelfEquivOp, RingEquiv.symm_symm]
  rfl

end Etingof
