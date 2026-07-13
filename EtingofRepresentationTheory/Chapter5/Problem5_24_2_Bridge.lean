import Mathlib
import EtingofRepresentationTheory.Chapter5.Problem5_24_2_Core
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Problem 5.24.2, steps 1–2: the coordinate ↔ tensor bridge

This file builds the linear bridge between the coordinate ring of matrix invariants
(`Etingof.MatrixTupleRing`, developed in `Problem5_24_2.lean`) and the Schur–Weyl tensor framework
(`Etingof.TensorPower`, `symGroupImage`, in `Theorem5_18_4.lean`), following steps 1–2 of the book's
hint for Problem 5.24.2.

## The setup

Take `V = ℂ^N = Fin N → ℂ`, so `End V ≃ Matrix (Fin N) (Fin N) ℂ` and
`End(V)^{⊗n} ≃ End(V^{⊗n}) = Module.End ℂ (TensorPower ℂ V n)`. The `GL(V)`-invariant part of
`End(V)^{⊗n}` (endomorphisms of `V^{⊗n}` commuting with the diagonal `GL(V)`-action) is exactly
`symGroupImage ℂ V n`, the `ℂ`-span of the permutation operators `symGroupAction σ` — this is the
content of Schur–Weyl duality (`Theorem5_18_4_centralizers`).

## The evaluation pairing

For a *slot-to-letter assignment* `slot : Fin n → Fin k` (slot `j` carries the letter `slot j`,
i.e. the generic matrix `X_{slot j}`), we define a `ℂ`-linear evaluation pairing

```
endTensorEval slot : Module.End ℂ (V^{⊗n}) →ₗ[ℂ] MatrixTupleRing k N
```

sending an endomorphism `M` of `V^{⊗n}` to the complete contraction of its matrix (in the standard
tensor basis) against the generic tensor `⨂ⱼ X_{slot j}`. Concretely,
`endTensorEval slot M = Matrix.trace ((toMatrix M).map C * genericTensorMatrix slot)`, where `C`
coerces the `ℂ`-entries of `toMatrix M` into the coordinate ring and `genericTensorMatrix slot` is
the matrix (over the coordinate ring) of the operator `⨂ⱼ X_{slot j}` on `V^{⊗n}`.

The value on a permutation operator `symGroupAction σ` is a product of trace-of-word functions
`traceWord`, one per cycle of `σ`: this is the tensor-trace ↔ trace-word identity supplied by
the sibling sub-issue. The assembly sub-issue combines that identity with Schur–Weyl
permutation-spanning (`Theorem5_18_4_centralizers`) and the range identification stated here
(`weightedHomogeneous_invariant_mem_range_endTensorEval`) to discharge the remaining `sorry` in
`Problem5_24_2.lean` (`weightedHomogeneous_invariant_mem_adjoin`).
-/

noncomputable section

namespace Etingof

open scoped TensorProduct
open MvPolynomial Module

variable (k N n : ℕ)

/-- The vector space `V = ℂ^N` underlying Problem 5.24.2. `End V ≃ Matrix (Fin N) (Fin N) ℂ`, and
`TensorPower ℂ (BridgeV N) n = V^{⊗n}` is the Schur–Weyl tensor space with `End(V)^{⊗n}` its
endomorphism algebra. -/
abbrev BridgeV : Type := Fin N → ℂ

/-- The standard basis of `V^{⊗n}` (`V = ℂ^N`) indexed by `Fin n → Fin N`: the tensor of the
standard basis vectors `e_{f j}` over the slots `j`. Used to take matrices of endomorphisms of
`V^{⊗n}`. -/
noncomputable def tensorBasis :
    Basis (Fin n → Fin N) ℂ (TensorPower ℂ (BridgeV N) n) :=
  Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N))

/-- The matrix, over the coordinate ring `MatrixTupleRing k N`, of the operator `⨂ⱼ X_{slot j}`
acting on `V^{⊗n}` in the standard tensor basis: its `(f, g)` entry is the product over slots of the
generic matrix entries `(X_{slot j})_{f j, g j} = X (slot j, f j, g j)`. -/
noncomputable def genericTensorMatrix (slot : Fin n → Fin k) :
    Matrix (Fin n → Fin N) (Fin n → Fin N) (MatrixTupleRing k N) :=
  fun f g => ∏ j : Fin n, MvPolynomial.X (slot j, f j, g j)

/-- The `ℂ`-linear "complete contraction" pairing on matrices: a `ℂ`-matrix `M` (thought of as the
matrix of an endomorphism of `V^{⊗n}`) is sent to `Tr((M.map C) · genericTensorMatrix slot)`, i.e.
`∑_{f g} C (M f g) · (genericTensorMatrix slot) g f`, a polynomial in the coordinate ring. This is
the underlying linear map of `endTensorEval`, taken on matrices so that linearity is manifest. -/
noncomputable def evalMatrix (slot : Fin n → Fin k) :
    Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ →ₗ[ℂ] MatrixTupleRing k N where
  toFun M := ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
    algebraMap ℂ (MatrixTupleRing k N) (M f g) * genericTensorMatrix k N n slot g f
  map_add' M M' := by
    simp only [Matrix.add_apply, map_add, add_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Algebra.smul_def, mul_assoc]

/-- **Coordinate ↔ tensor evaluation pairing (steps 1–2).** The `ℂ`-linear map sending an
endomorphism `M` of `V^{⊗n}` (an element of `End(V)^{⊗n}`) to the polynomial obtained by contracting
`M` completely against the generic tensor `⨂ⱼ X_{slot j}`, where `slot : Fin n → Fin k` assigns to
each tensor slot the letter (generic matrix) placed there.

It is `evalMatrix slot` precomposed with `LinearMap.toMatrix` in the standard tensor basis. On a
permutation operator `symGroupAction σ` its value is a product of trace-of-word functions
(one per cycle of `σ`), the tensor-trace ↔ trace-word identity of the sibling sub-issue. -/
noncomputable def endTensorEval (slot : Fin n → Fin k) :
    Module.End ℂ (TensorPower ℂ (BridgeV N) n) →ₗ[ℂ] MatrixTupleRing k N :=
  evalMatrix k N n slot ∘ₗ
    (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)).toLinearMap

/-- Unfolding of `endTensorEval`: the value on `M` is `∑_{f g}` of the `(f,g)` matrix entry of `M`
(in the standard tensor basis) coerced into the coordinate ring, times the `(g,f)` entry of the
generic tensor matrix. -/
theorem endTensorEval_apply (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    endTensorEval k N n slot M =
      ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
        algebraMap ℂ (MatrixTupleRing k N)
            (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M f g)
          * genericTensorMatrix k N n slot g f := by
  rfl

/-- **Range identification (statement).** Every fixed-multidegree conjugation-invariant polynomial
lies in the image, under the evaluation pairing `endTensorEval slot`, of the `GL(V)`-invariant part
of `End(V)^{⊗n}` — namely `symGroupImage ℂ V n`, the `ℂ`-span of the permutation operators.

Here `slot : Fin n → Fin k` is any slot assignment compatible with the multidegree `d`, meaning slot
`j` carries letter `i` for exactly `d i` slots (`hslot`); in particular `n = ∑ᵢ dᵢ` is the total
degree.

This is book step 2 of the Problem 5.24.2 hint: the degree-`d` invariants
`⨂ᵢ Sᵈⁱ(V ⊗ V*)` are realized as `GL(V)`-invariant tensors in `(V ⊗ V*)^{⊗n} = End(V)^{⊗n}`. The
deep content — surjectivity of `endTensorEval` from the invariant tensors onto the degree-`d`
invariants, i.e. the First Fundamental Theorem via Schur–Weyl — is left as a `sorry` here; it is
discharged in the assembly sub-issue by combining the Schur–Weyl permutation-spanning theorem
(`Theorem5_18_4_centralizers`) with the tensor-trace ↔ trace-word identity. -/
theorem weightedHomogeneous_invariant_mem_range_endTensorEval
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i)
    {p : MatrixTupleRing k N}
    (hhom : IsWeightedHomogeneous (matrixWeight k N) p d)
    (hinv : p ∈ invariantSubalgebra k N) :
    ∃ M ∈ symGroupImage ℂ (BridgeV N) n, endTensorEval k N n slot M = p := by
  sorry

end Etingof
