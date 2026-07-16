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

/-- `endTensorEval` is `evalMatrix` applied to the matrix of `M` in the standard tensor basis. -/
theorem endTensorEval_eq_evalMatrix (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    endTensorEval k N n slot M
      = evalMatrix k N n slot (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M) :=
  rfl

/-! ## GL-equivariance of the evaluation pairing

The evaluation pairing intertwines conjugation of an endomorphism `M` of `V^{⊗n}` by the diagonal
operator `g^{⊗n}` with the simultaneous-conjugation automorphism `conjAlgHom g` of the coordinate
ring. This is book step of the Schur–Weyl argument: `endTensorEval slot` is `GL(V)`-equivariant.
-/

/-- `evalMatrix` written as a matrix trace: contracting `A` completely against the generic tensor is
the trace of `(A.map C) · genericTensorMatrix slot`. -/
theorem evalMatrix_eq_trace (slot : Fin n → Fin k)
    (A : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ) :
    evalMatrix k N n slot A
      = Matrix.trace ((A.map (algebraMap ℂ (MatrixTupleRing k N)))
          * genericTensorMatrix k N n slot) := by
  change (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      algebraMap ℂ (MatrixTupleRing k N) (A f g) * genericTensorMatrix k N n slot g f) = _
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.map_apply]

/-- The matrix, in the standard tensor basis, of the diagonal tensor-power operator
`PiTensorProduct.map (fun _ => mulVecLin h) = h^{⊗n}` on `V^{⊗n}`: its `(p, q)` entry is the product
over slots of the matrix entries `h (p j) (q j)`. -/
theorem toMatrix_piTensorMap_mulVecLin (h : Matrix (Fin N) (Fin N) ℂ) (p q : Fin n → Fin N) :
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin h)) p q
      = ∏ j : Fin n, h (p j) (q j) := by
  rw [LinearMap.toMatrix_apply, tensorBasis, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← LinearMap.toMatrix_apply (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (Matrix.mulVecLin h) (p j) (q j), LinearMap.toMatrix_eq_toMatrix',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

/-- Conjugation acts on a single coordinate variable by expanding the matrix conjugation
`X (i, r, c) ↦ (g · Xᵢ · g⁻¹)_{r,c}` into a double sum over the intermediate indices. -/
theorem conjAlgHom_X_sum (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (i : Fin k) (r c : Fin N) :
    conjAlgHom k N g (MvPolynomial.X (i, r, c))
      = ∑ s : Fin N, ∑ t : Fin N,
          algebraMap ℂ (MatrixTupleRing k N) ((↑g : Matrix (Fin N) (Fin N) ℂ) r s)
            * MvPolynomial.X (i, s, t)
            * algebraMap ℂ (MatrixTupleRing k N) ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c) := by
  rw [conjAlgHom, MvPolynomial.aeval_X]
  simp only [Matrix.mul_apply, Matrix.map_apply, genericMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Entrywise conjugation of the generic tensor matrix.** Applying `conjAlgHom g` entrywise to the
generic tensor matrix conjugates it by the tensor-power matrices of `g` and `g⁻¹`:
`(genericTensorMatrix slot).map (conjAlgHom g) = (g^{⊗n}) · genericTensorMatrix slot · (g⁻¹)^{⊗n}`
(all as matrices over the coordinate ring). This is the matrix form of the substitution
`X (i, r, c) ↦ (g Xᵢ g⁻¹)_{r,c}` propagated across the tensor slots. -/
theorem genericTensorMatrix_map_conjAlgHom (slot : Fin n → Fin k)
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    (genericTensorMatrix k N n slot).map (conjAlgHom k N g)
      = (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
            (PiTensorProduct.map (fun _ : Fin n =>
              Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))).map
              (algebraMap ℂ (MatrixTupleRing k N))
        * genericTensorMatrix k N n slot
        * (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
            (PiTensorProduct.map (fun _ : Fin n =>
              Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)))).map
              (algebraMap ℂ (MatrixTupleRing k N)) := by
  classical
  refine Matrix.ext fun e f => ?_
  -- Left side: apply `conjAlgHom` to the monomial `∏ⱼ X (slot j, e j, f j)`, expand each factor as
  -- a double sum, and collect the product of sums into a double sum over intermediate index
  -- functions `a, b : Fin n → Fin N` (one application of `prod_univ_sum` per matrix index).
  rw [Matrix.map_apply]
  change conjAlgHom k N g (∏ j : Fin n, MvPolynomial.X (slot j, e j, f j)) = _
  rw [map_prod]
  simp_rw [conjAlgHom_X_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  -- Right side: expand the two matrix products into a `∑ b ∑ a` and swap to `∑ a ∑ b`.
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- Match a single `(a, b)` term.
  simp only [Matrix.map_apply, toMatrix_piTensorMap_mulVecLin, genericTensorMatrix]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← map_prod, ← map_prod]

/-- **GL-equivariance of the evaluation pairing.** The pairing `endTensorEval slot` intertwines
conjugation of an endomorphism `M` of `V^{⊗n}` by the diagonal operator `g^{⊗n}` with the
simultaneous-conjugation automorphism `conjAlgHom g` of the coordinate ring:
`endTensorEval slot ((g^{⊗n})⁻¹ · M · g^{⊗n}) = conjAlgHom g (endTensorEval slot M)`.

Here `g^{⊗n} = PiTensorProduct.map (fun _ => mulVecLin g)` is the diagonal `GL(V)`-action on
`V^{⊗n}`, and `(g^{⊗n})⁻¹` is the corresponding operator for `g⁻¹`. This is the equivariance glue
that lets the range identification transport `GL(V)`-invariance of tensors to conjugation-invariance
of polynomials. -/
theorem endTensorEval_conj (slot : Fin n → Fin k) (g : (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    endTensorEval k N n slot
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
          * M
          * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = conjAlgHom k N g (endTensorEval k N n slot M) := by
  set G : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
    with hG
  set G' : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)))
    with hG'
  set A : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M with hA
  -- Left side: the matrix of the conjugated endomorphism is `G' · A · G`; evaluate as a trace.
  have hlhs : endTensorEval k N n slot
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
        * M
        * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = Matrix.trace ((G'.map (algebraMap ℂ (MatrixTupleRing k N))
            * A.map (algebraMap ℂ (MatrixTupleRing k N))
            * G.map (algebraMap ℂ (MatrixTupleRing k N))) * genericTensorMatrix k N n slot) := by
    rw [endTensorEval_eq_evalMatrix, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
      evalMatrix_eq_trace, ← hG, ← hG', ← hA, Matrix.map_mul, Matrix.map_mul]
  -- Right side: push `conjAlgHom` through the trace, fixing scalar entries and conjugating the
  -- generic tensor matrix.
  have hrhs : conjAlgHom k N g (endTensorEval k N n slot M)
      = Matrix.trace ((G'.map (algebraMap ℂ (MatrixTupleRing k N))
            * A.map (algebraMap ℂ (MatrixTupleRing k N))
            * G.map (algebraMap ℂ (MatrixTupleRing k N))) * genericTensorMatrix k N n slot) := by
    rw [endTensorEval_eq_evalMatrix, ← hA, evalMatrix_eq_trace,
      AddMonoidHom.map_trace (conjAlgHom k N g), Matrix.map_mul,
      genericTensorMatrix_map_conjAlgHom, ← hG, ← hG']
    -- `(A.map C).map (conjAlgHom g) = A.map C` since `conjAlgHom` fixes scalars.
    have hAfix : (A.map (algebraMap ℂ (MatrixTupleRing k N))).map (conjAlgHom k N g)
        = A.map (algebraMap ℂ (MatrixTupleRing k N)) := by
      rw [Matrix.map_map]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, AlgHom.commutes]
    rw [hAfix, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [hlhs, hrhs]

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
