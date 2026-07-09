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

Bilinear maps `V × W → U` are modelled by `V →ₗ[k] W →ₗ[k] U`. All statements are fully proved.
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
  refine ⟨(TensorProduct.lift.equiv (RingHom.id k) V W U).toEquiv, ?_⟩
  intro f v w
  simp only [LinearEquiv.coe_toEquiv, TensorProduct.lift.equiv_apply]

/-- **Problem 2.11.3(b).** If `{vᵢ}` is a basis of `V` and `{wⱼ}` a basis of `W`, then
`{vᵢ ⊗ wⱼ}` is a basis of `V ⊗ W`. The basis is `b.tensorProduct c`, and its `(i, j)` vector is
exactly `vᵢ ⊗ wⱼ`. -/
theorem exists_basis_tensorProduct {ι κ : Type*} (b : Module.Basis ι k V)
    (c : Module.Basis κ k W) :
    ∃ B : Module.Basis (ι × κ) k (TensorProduct k V W),
      ∀ (i : ι) (j : κ), B (i, j) = TensorProduct.tmul k (b i) (c j) := by
  refine ⟨b.tensorProduct c, ?_⟩
  intro i j
  simp [Module.Basis.tensorProduct_apply]

/-- **Problem 2.11.3(c).** When `V` is finite dimensional there is a natural isomorphism
`V* ⊗ W ≃ Hom(V, W)`. The witnessing equivalence is the natural map `dualTensorHom`, sending a
pure tensor `f ⊗ w` to the linear map `v ↦ f v • w`. -/
theorem exists_dualTensor_equiv_hom [FiniteDimensional k V] :
    ∃ e : TensorProduct k (Module.Dual k V) W ≃ₗ[k] (V →ₗ[k] W),
      ∀ (f : Module.Dual k V) (w : W) (v : V),
        e (TensorProduct.tmul k f w) v = f v • w := by
  refine ⟨dualTensorHomEquiv k V W, ?_⟩
  intro f w v
  simp [dualTensorHomEquiv, dualTensorHom_apply]

/-- **Problem 2.11.3(g).** `∧ᴺ A = det(A)·Id` yields multiplicativity of the determinant:
`det(A ∘ B) = det(A) · det(B)` for operators on a vector space. -/
theorem det_comp (A B : V →ₗ[k] V) :
    LinearMap.det (A ∘ₗ B) = LinearMap.det A * LinearMap.det B :=
  LinearMap.det_comp A B

end Etingof.Problem2_11_3
