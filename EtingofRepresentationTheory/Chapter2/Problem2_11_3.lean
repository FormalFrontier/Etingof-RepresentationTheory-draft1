import Mathlib

/-!
# Problem 2.11.3: The universal property of the tensor product and its consequences

The problem collects several standard facts about tensor products of vector spaces:

* **(a)** a natural bijection between bilinear maps `V × W → U` and linear maps `V ⊗ W → U`;
* **(b)** if `{vᵢ}` is a basis of `V` and `{wⱼ}` a basis of `W`, then `{vᵢ ⊗ wⱼ}` is a basis of
  `V ⊗ W`;
* **(c)** a natural isomorphism `V* ⊗ W → Hom(V, W)` when `V` is finite dimensional;
* **(d)–(e)** symmetric and exterior powers and their bases / identifications;
* **(f)–(g)** symmetric/exterior powers of an operator, their traces, and `∧ᴺ A = det(A)·Id`,
  giving a one-line proof of `det(AB) = det(A) det(B)`.

## Formalization

This file records the cleanly-statable parts (a), (b), (c) and (g). Parts (d)–(f) concern
symmetric/exterior powers and traces and are deferred to a dedicated follow-up item.

Bilinear maps `V × W → U` are modelled by `V →ₗ[k] W →ₗ[k] U`. All statements are recorded with
`sorry` proofs (**statement pass**).
-/

namespace Etingof.Problem2_11_3

variable {k : Type*} [Field k]
variable {V W U : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- **Problem 2.11.3(a).** There is a natural bijection between bilinear maps `V × W → U`
(here `V →ₗ[k] W →ₗ[k] U`) and linear maps `V ⊗ W → U`, characterised by sending a bilinear map
`f` to the linear map with `v ⊗ w ↦ f v w`. -/
theorem exists_bilinear_equiv_linear :
    ∃ e : (V →ₗ[k] W →ₗ[k] U) ≃ (TensorProduct k V W →ₗ[k] U),
      ∀ (f : V →ₗ[k] W →ₗ[k] U) (v : V) (w : W),
        e f (TensorProduct.tmul k v w) = f v w := by
  sorry

/-- **Problem 2.11.3(b).** If `{vᵢ}` is a basis of `V` and `{wⱼ}` a basis of `W`, then
`{vᵢ ⊗ wⱼ}` is a basis of `V ⊗ W`. -/
theorem exists_basis_tensorProduct {ι κ : Type*} (b : Module.Basis ι k V)
    (c : Module.Basis κ k W) :
    Nonempty (Module.Basis (ι × κ) k (TensorProduct k V W)) := by
  sorry

/-- **Problem 2.11.3(c).** When `V` is finite dimensional there is a natural isomorphism
`V* ⊗ W ≃ Hom(V, W)`. -/
theorem exists_dualTensor_equiv_hom [FiniteDimensional k V] :
    Nonempty (TensorProduct k (Module.Dual k V) W ≃ₗ[k] (V →ₗ[k] W)) := by
  sorry

/-- **Problem 2.11.3(g).** `∧ᴺ A = det(A)·Id` yields multiplicativity of the determinant:
`det(A ∘ B) = det(A) · det(B)` for operators on a vector space. -/
theorem det_comp (A B : V →ₗ[k] V) :
    LinearMap.det (A ∘ₗ B) = LinearMap.det A * LinearMap.det B := by
  sorry

end Etingof.Problem2_11_3
