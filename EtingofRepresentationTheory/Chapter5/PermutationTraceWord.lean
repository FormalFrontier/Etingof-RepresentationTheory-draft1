import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# The tensor-trace ↔ trace-word (cycle-trace) identity

This file develops book step 4 of the Problem 5.24.2 hint, self-contained in the Schur–Weyl
tensor framework of `Theorem5_18_4.lean`.

For a permutation `σ : Equiv.Perm (Fin n)` and endomorphisms `A : Fin n → Module.End k V`, the
**permuted tensor operator** is
`permTensorOp σ A := symGroupAction σ ∘ₗ PiTensorProduct.map A : End (V^⊗n)`,
i.e. the operator that applies `A i` on tensor factor `i` and then permutes the factors by `σ`.

The main result (`permTensorOp_trace_eq_prod_cycle`) is that its trace over the tensor factors
factors as a product over the `σ`-orbits of `Fin n`, one *trace of the ordered operator product
around the cycle* per orbit:

```
trace (permTensorOp σ A) = ∏_{orbits O of σ} trace (∏_{j around O} A j).
```

The proof has two independent parts:

* `permTensorOp_trace_eq_matrixSum` (**fully proved**): reduce the tensor trace to a sum over
  basis multi-indices `p : Fin n → ι` of `∏ i, (A i)_{p (σ i), p i}`, the diagonal matrix entries
  of the permutation operator. This is pure trace/basis bookkeeping.

* `matrixSum_eq_prod_cycle` (the combinatorial core): the multi-index sum factors over the
  `σ`-orbits, because the permutation operator forces `p` to be constant along each cycle and the
  chain of matrix entries around a cycle resums to a matrix trace. The single-cycle case is
  `matrixSum_cycle_eq_trace`.
-/

open scoped TensorProduct

namespace Etingof

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The permuted tensor operator: apply `A i` on tensor factor `i`, then permute the factors by
`σ`. Concretely `symGroupAction σ ∘ₗ (⨂ᵢ A i)` on `V^⊗n`. -/
noncomputable def permTensorOp (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    Module.End k (TensorPower k V n) :=
  (symGroupAction k V n σ).toLinearMap ∘ₗ PiTensorProduct.map A

/-- The chosen basis of `V` used throughout: `Module.Free.chooseBasis k V`. Its index type
`Module.Free.ChooseBasisIndex k V` is a `Fintype` since `V` is finite-dimensional. -/
noncomputable abbrev chosenBasis : Module.Basis (Module.Free.ChooseBasisIndex k V) k V :=
  Module.Free.chooseBasis k V

/-- **Reduction to a coordinate sum.** The trace of the permuted tensor operator equals the sum,
over basis multi-indices `p : Fin n → ι`, of the product over factors `i` of the matrix entry
`(A i)_{p (σ i), p i}`. This is the diagonal of the permutation operator in the tensor-power basis
`Basis.piTensorProduct`. -/
theorem permTensorOp_trace_eq_matrixSum (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    LinearMap.trace k _ (permTensorOp k V n σ A)
      = ∑ p : Fin n → Module.Free.ChooseBasisIndex k V,
          ∏ i : Fin n,
            LinearMap.toMatrix (chosenBasis k V) (chosenBasis k V) (A i) (p (σ i)) (p i) := by
  classical
  set b : Module.Basis (Module.Free.ChooseBasisIndex k V) k V := chosenBasis k V with hb
  set B : Module.Basis (Fin n → Module.Free.ChooseBasisIndex k V) k (TensorPower k V n) :=
    Basis.piTensorProduct (fun _ : Fin n => b) with hB
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- the `p`-diagonal entry of the operator in the basis `B`
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  -- compute the operator on the basis vector `B p`
  have hBp : B p = ⨂ₜ[k] i, b (p i) := Basis.piTensorProduct_apply (fun _ => b) p
  have hop : permTensorOp k V n σ A (B p)
      = ⨂ₜ[k] j, (A (σ.symm j)) (b (p (σ.symm j))) := by
    rw [hBp, permTensorOp, LinearMap.comp_apply, PiTensorProduct.map_tprod]
    change symGroupAction k V n σ (⨂ₜ[k] i, (A i) (b (p i))) = _
    rw [symGroupAction, PiTensorProduct.reindex_tprod]
  rw [hop, hB, Basis.piTensorProduct_repr_tprod_apply]
  -- reindex the product `∏ j` by `j = σ i`
  rw [← Equiv.prod_comp σ
        (fun j => b.repr ((A (σ.symm j)) (b (p (σ.symm j)))) (p j))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.symm_apply_apply, LinearMap.toMatrix_apply]

end Etingof
