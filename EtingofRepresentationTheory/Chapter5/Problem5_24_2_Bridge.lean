import Mathlib
import EtingofRepresentationTheory.Chapter5.Problem5_24_2_Core
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer

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

/-- **The GL-equivariant section (crux).** There is a section `σ` of the evaluation pairing
`endTensorEval slot` on the multidegree-`d` part of the coordinate ring that is `GL(V)`-equivariant:
it sends each `matrixWeight`-homogeneous polynomial `p` of multidegree `d` to an endomorphism `σ p`
of `V^{⊗n}` with `endTensorEval slot (σ p) = p` (section property), and intertwines the
simultaneous-conjugation automorphism `conjAlgHom g` on polynomials with conjugation by the diagonal
operator `g^{⊗n}` on `End(V^{⊗n})` (equivariance).

This is the reductivity heart of the First Fundamental Theorem (book step 2), obtained — following
the single-matrix `PolynomialTensorBridge` — by an explicit block-symmetrization section rather than
an abstract Reynolds operator. Its construction and the two properties are the deliverable of the
section sub-issue; the assembly `weightedHomogeneous_invariant_mem_range_endTensorEval` below
consumes it, turning `GL`-invariance of `p` into commutation of `σ p` with every diagonal operator
and hence membership in `symGroupImage`. -/
theorem exists_endTensorEval_equivariant_section
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i) :
    ∃ σ : MatrixTupleRing k N → Module.End ℂ (TensorPower ℂ (BridgeV N) n),
      (∀ p : MatrixTupleRing k N, IsWeightedHomogeneous (matrixWeight k N) p d →
          endTensorEval k N n slot (σ p) = p) ∧
      (∀ (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (p : MatrixTupleRing k N),
          IsWeightedHomogeneous (matrixWeight k N) p d →
          σ (conjAlgHom k N g p)
            = PiTensorProduct.map
                  (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
              * σ p
              * PiTensorProduct.map
                  (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))) := by
  sorry

/-- **Range identification (assembly).** Every fixed-multidegree conjugation-invariant polynomial
lies in the image, under `endTensorEval slot`, of `symGroupImage ℂ V n` — the `GL(V)`-invariant part
of `End(V)^{⊗n}`. This is book step 2 of the FFT.

Given the `GL`-equivariant section `σ` (`exists_endTensorEval_equivariant_section`), the lift is
`M := σ p`. The section property gives `endTensorEval slot M = p`. For membership in
`symGroupImage`, invariance `conjAlgHom g p = p` combined with equivariance shows `M` is fixed by
conjugation by every diagonal unit operator `g^{⊗n}` (`M = (g^{⊗n})⁻¹ M g^{⊗n}`), i.e.
`Commute (g^{⊗n}) M`. Since the
`g^{⊗n}` generate `diagonalActionImage` (`adjoin_unitsTensorPow_eq_diagonalActionImage`) and
`symGroupImage` is its centralizer (`Theorem5_18_4_centralizers`), `M ∈ symGroupImage`. -/
theorem weightedHomogeneous_invariant_mem_range_endTensorEval
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i)
    {p : MatrixTupleRing k N}
    (hhom : IsWeightedHomogeneous (matrixWeight k N) p d)
    (hinv : p ∈ invariantSubalgebra k N) :
    ∃ M ∈ symGroupImage ℂ (BridgeV N) n, endTensorEval k N n slot M = p := by
  classical
  obtain ⟨σ, hsec, hequiv⟩ :=
    exists_endTensorEval_equivariant_section k N n d slot hslot
  refine ⟨σ p, ?_, hsec p hhom⟩
  -- `σ p` commutes with every diagonal unit operator `g^{⊗n}`.
  have key : ∀ g' : (Module.End ℂ (BridgeV N))ˣ,
      Commute (PiTensorProduct.map (fun _ : Fin n => (g' : Module.End ℂ (BridgeV N)))) (σ p) := by
    intro g'
    -- The matrix unit `g` corresponding to `g'` under `End(ℂ^N) ≃ Matrix`.
    set A : Matrix (Fin N) (Fin N) ℂ :=
      LinearMap.toMatrix' (↑g' : Module.End ℂ (Fin N → ℂ)) with hA
    set A' : Matrix (Fin N) (Fin N) ℂ :=
      LinearMap.toMatrix' (↑g'⁻¹ : Module.End ℂ (Fin N → ℂ)) with hA'
    have hAA' : A * A' = 1 := by
      rw [hA, hA', ← LinearMap.toMatrix'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        LinearMap.toMatrix'_one]
    have hA'A : A' * A = 1 := by
      rw [hA, hA', ← LinearMap.toMatrix'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        LinearMap.toMatrix'_one]
    set g : (Matrix (Fin N) (Fin N) ℂ)ˣ := ⟨A, A', hAA', hA'A⟩ with hg
    have hP : Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)
        = (↑g' : Module.End ℂ (BridgeV N)) := by
      change Matrix.mulVecLin A = _
      rw [hA, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    have hPinv : Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)
        = (↑g'⁻¹ : Module.End ℂ (BridgeV N)) := by
      change Matrix.mulVecLin A' = _
      rw [hA', ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    -- Invariance of `p` at this `g`.
    have hpinv : conjAlgHom k N g p = p := by
      rw [invariantSubalgebra, Algebra.mem_iInf] at hinv
      have hg' := hinv g
      rwa [AlgHom.mem_equalizer, AlgHom.id_apply] at hg'
    -- Equivariance of the section, specialized and rewritten via invariance and `hP`, `hPinv`.
    have heq := hequiv g p hhom
    rw [hpinv] at heq
    simp only [hP, hPinv] at heq
    set P : Module.End ℂ (TensorPower ℂ (BridgeV N) n) :=
      PiTensorProduct.map (fun _ : Fin n => (g' : Module.End ℂ (BridgeV N))) with hPdef
    set Q : Module.End ℂ (TensorPower ℂ (BridgeV N) n) :=
      PiTensorProduct.map (fun _ : Fin n => (↑g'⁻¹ : Module.End ℂ (BridgeV N))) with hQdef
    -- `P` and `Q` are mutually inverse diagonal operators.
    have hPQ : P * Q = 1 := by
      rw [hPdef, hQdef, ← PiTensorProduct.map_mul]
      have hid : (fun _ : Fin n =>
            (↑g' : Module.End ℂ (BridgeV N)) * (↑g'⁻¹ : Module.End ℂ (BridgeV N)))
          = fun _ : Fin n => (1 : Module.End ℂ (BridgeV N)) := by
        funext _
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hid, PiTensorProduct.map_one]
    -- `heq : σ p = Q * σ p * P` and `P * Q = 1` give `P * σ p = σ p * P`.
    change Commute P (σ p)
    rw [Commute, SemiconjBy]
    nth_rewrite 1 [heq]
    rw [← mul_assoc, ← mul_assoc, hPQ, one_mul]
  -- Membership in `symGroupImage` via the Schur–Weyl centralizer identity.
  rw [(Theorem5_18_4_centralizers ℂ (BridgeV N) n).1, Subalgebra.mem_centralizer_iff]
  intro y hy
  rw [← adjoin_unitsTensorPow_eq_diagonalActionImage (V := BridgeV N) ℂ n] at hy
  have hcomm : Commute (σ p) y :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (by
      rintro _ ⟨g', rfl⟩
      exact (key g').symm)
  exact hcomm.symm

/-! ### Surjectivity onto degree-`d` polynomials (the combinatorial core)

The remaining fact needed for the First Fundamental Theorem assembly (#6789) is that *every*
`matrixWeight`-homogeneous polynomial of multidegree `d` lies in the range of `endTensorEval slot`
(before imposing `GL`-invariance): the generic-tensor monomials `∏ⱼ X_{slot j, gⱼ, fⱼ}` already
exhaust the degree-`d` part of the coordinate ring. This is purely combinatorial — realizing each
degree-`d` exponent vector `u` by a slot assignment `(f, g)` — and is proved here independently of
Schur–Weyl. -/

/-- **Per-fibre realizability.** Given a finite set `S` and a `ℕ`-valued `Finsupp` `m` whose total
mass equals `S.card`, there is a function `h` on the index type with
`∑_{j ∈ S} single (h j) 1 = m`: distribute the `m`-multiset over the `S.card` points of `S`.
Proved by induction on `S`, peeling one support element of `m` for each new point of `S`. -/
private lemma exists_fun_sum_single {ι β : Type*} [Nonempty β] (S : Finset ι) :
    ∀ m : β →₀ ℕ, m.sum (fun _ x => x) = S.card →
      ∃ h : ι → β, ∑ j ∈ S, Finsupp.single (h j) 1 = m := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.card_empty] at hm
    refine ⟨fun _ => Classical.arbitrary β, ?_⟩
    rw [Finset.sum_empty]
    symm
    rw [← Finsupp.support_eq_empty]
    by_contra hne
    obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hne
    have hpos : 0 < m.sum (fun _ x => x) := by
      rw [Finsupp.sum]
      exact Finset.sum_pos' (fun i _ => Nat.zero_le _)
        ⟨v, hv, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hv)⟩
    omega
  | insert a S' ha ih =>
    intro m hm
    rw [Finset.card_insert_of_notMem ha] at hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Finsupp.sum_zero_index] at hm
      omega
    obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.mpr hm0
    have hmb : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.1 hb)
    have hle : Finsupp.single b 1 ≤ m := by
      rw [Finsupp.le_iff]
      intro i hi
      have hi' : i = b := Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
      subst hi'
      rw [Finsupp.single_eq_same]
      exact hmb
    set m' := m - Finsupp.single b 1 with hm'def
    have hsplit : m = Finsupp.single b 1 + m' := by
      rw [hm'def, add_tsub_cancel_of_le hle]
    have hm'sum : m'.sum (fun _ x => x) = S'.card := by
      have hadd : m.sum (fun _ x => x)
          = (Finsupp.single b 1).sum (fun _ x => x) + m'.sum (fun _ x => x) := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      rw [Finsupp.sum_single_index rfl] at hadd
      omega
    obtain ⟨h', hh'⟩ := ih m' hm'sum
    refine ⟨Function.update h' a b, ?_⟩
    rw [Finset.sum_insert ha, Function.update_self]
    have hcong : ∑ j ∈ S', Finsupp.single (Function.update h' a b j) 1
        = ∑ j ∈ S', Finsupp.single (h' j) 1 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (by rintro rfl; exact ha hj)]
    rw [hcong, hh']
    exact hsplit.symm

/-- The per-letter mass `∑_{v.1 = i} u v` of an exponent vector `u`, packaged as the total mass of
the `i`-th curried slice `u.curry i`, equals the `i`-th component of its `matrixWeight`-weight. Both
sides are additive in `u`, so this reduces to the single-variable case. -/
private lemma curry_sum_eq_weight (u : (Fin k × Fin N × Fin N) →₀ ℕ) (i : Fin k) :
    (u.curry i).sum (fun _ x => x) = (Finsupp.weight (matrixWeight k N) u) i := by
  classical
  induction u using Finsupp.induction_linear with
  | zero =>
    have hz : (0 : (Fin k × Fin N × Fin N) →₀ ℕ).curry = 0 := by
      rw [← Finsupp.coe_curryAddEquiv]; exact map_zero _
    rw [hz, Finsupp.zero_apply, Finsupp.sum_zero_index, map_zero, Finsupp.zero_apply]
  | add x y ihx ihy =>
    have hc : (x + y).curry i = x.curry i + y.curry i := by
      have h := map_add Finsupp.curryAddEquiv x y
      simp only [Finsupp.coe_curryAddEquiv] at h
      rw [h, Finsupp.add_apply]
    rw [hc, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ihx, ihy,
      map_add, Finsupp.add_apply]
  | single v c =>
    rw [Finsupp.curry_single, Finsupp.weight_single]
    simp only [matrixWeight]
    by_cases h : v.1 = i
    · rw [Finsupp.single_apply, if_pos h, Finsupp.sum_single_index rfl,
        Finsupp.smul_apply, Finsupp.single_apply, if_pos h, smul_eq_mul, mul_one]
    · rw [Finsupp.single_apply, if_neg h, Finsupp.sum_zero_index,
        Finsupp.smul_apply, Finsupp.single_apply, if_neg h, smul_zero]

/-- **Realizability.** If, for every letter `i`, the per-letter mass of `u` matches the number of
slots carrying letter `i` (`hcard`), then `u` is the exponent vector of a generic-tensor monomial:
there are `f g : Fin n → Fin N` with `∑ⱼ single (slot j, g j, f j) 1 = u`. Assemble a per-letter
distribution (`exists_fun_sum_single`) fibrewise via `slot`, then reassemble through
`Finsupp.curry`. -/
private lemma exists_fg_realizes (slot : Fin n → Fin k) (u : (Fin k × Fin N × Fin N) →₀ ℕ)
    (hcard : ∀ i : Fin k,
      (u.curry i).sum (fun _ x => x) = (Finset.univ.filter fun j => slot j = i).card) :
    ∃ f g : Fin n → Fin N, ∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1 = u := by
  classical
  rcases isEmpty_or_nonempty (Fin N × Fin N) with hE | hNE
  · -- Empty letters: `u = 0` and there are no slots.
    have hemptyProd : IsEmpty (Fin k × Fin N × Fin N) := ⟨fun p => hE.false p.2⟩
    have hu0 : u = 0 := by ext v; exact (hemptyProd.false v).elim
    have hn : IsEmpty (Fin n) := by
      refine ⟨fun j => ?_⟩
      have hmem : j ∈ Finset.univ.filter fun j' => slot j' = slot j := by simp
      have hpos : 0 < (Finset.univ.filter fun j' => slot j' = slot j).card :=
        Finset.card_pos.mpr ⟨j, hmem⟩
      have hz : (u.curry (slot j)).sum (fun _ x => x) = 0 := by
        have : u.curry (slot j) = 0 := by ext b; exact (hE.false b).elim
        rw [this]; simp
      rw [hcard (slot j)] at hz
      omega
    haveI := hn
    exact ⟨fun j => (hn.false j).elim, fun j => (hn.false j).elim, by rw [hu0]; simp⟩
  · haveI := hNE
    have perfib : ∀ i : Fin k, ∃ h : Fin n → Fin N × Fin N,
        ∑ j ∈ Finset.univ.filter (fun j => slot j = i), Finsupp.single (h j) 1 = u.curry i :=
      fun i => exists_fun_sum_single _ _ (hcard i)
    choose h hh using perfib
    refine ⟨fun j => (h (slot j) j).2, fun j => (h (slot j) j).1, ?_⟩
    have key : ∑ j : Fin n, Finsupp.single (slot j) (Finsupp.single (h (slot j) j) (1 : ℕ))
        = u.curry := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [← Finset.sum_filter]
      have hrw : ∑ j ∈ Finset.univ.filter (fun j => slot j = i),
            Finsupp.single (h (slot j) j) 1
          = ∑ j ∈ Finset.univ.filter (fun j => slot j = i), Finsupp.single (h i j) 1 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_filter] at hj
        rw [hj.2]
      rw [hrw]
      exact hh i
    apply Finsupp.curryAddEquiv.injective
    rw [map_sum]
    simp only [Finsupp.coe_curryAddEquiv, Finsupp.curry_single]
    exact key

/-- A product of `monomial (single vⱼ 1) 1` is the monomial of the summed exponent vector: the map
`e ↦ monomial e 1` turns sums of exponents into products of monomials. -/
private lemma prod_monomial_single {ι : Type*} (s : Finset ι)
    (v : ι → (Fin k × Fin N × Fin N)) :
    (∏ j ∈ s, MvPolynomial.monomial (Finsupp.single (v j) 1) (1 : ℂ))
      = MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (v j) 1) (1 : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact MvPolynomial.one_def
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, MvPolynomial.monomial_mul, one_mul]

/-- **Surjectivity onto the degree-`d` part (FFT range identification, B1).** Every polynomial in
the coordinate ring `MatrixTupleRing k N` that is `matrixWeight`-homogeneous of multidegree `d` lies
in the range of the evaluation pairing `endTensorEval slot`, for any slot assignment `slot`
compatible with `d` (slot `j` carries letter `i` for exactly `d i` slots).

The range contains every generic-tensor monomial `∏ⱼ X_{slot j, gⱼ, fⱼ}` (it is the value of
`endTensorEval slot` on the standard matrix unit, since only one term of the complete contraction
survives). A degree-`d` polynomial is a `ℂ`-combination of such monomials — each exponent vector in
its support is realizable by a slot assignment (`exists_fg_realizes`) — and the range is a
submodule. -/
theorem weightedHomogeneous_mem_range_endTensorEval
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i)
    {p : MatrixTupleRing k N}
    (hhom : IsWeightedHomogeneous (matrixWeight k N) p d) :
    p ∈ LinearMap.range (endTensorEval k N n slot) := by
  classical
  -- The range contains every generic-tensor monomial.
  have hmono : ∀ f g : Fin n → Fin N,
      (∏ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : MatrixTupleRing k N))
        ∈ LinearMap.range (endTensorEval k N n slot) := by
    intro f g
    refine ⟨(LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)).symm (Matrix.single f g 1), ?_⟩
    rw [endTensorEval, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change ∑ a : Fin n → Fin N, ∑ b : Fin n → Fin N,
        algebraMap ℂ (MatrixTupleRing k N) (Matrix.single f g 1 a b)
          * genericTensorMatrix k N n slot b a
      = ∏ j : Fin n, MvPolynomial.X (slot j, g j, f j)
    rw [Finset.sum_eq_single_of_mem f (Finset.mem_univ f)]
    · rw [Finset.sum_eq_single_of_mem g (Finset.mem_univ g)]
      · rw [Matrix.single_apply_same, map_one, one_mul]
        rfl
      · intro b _ hb
        rw [Matrix.single_apply_of_col_ne f f (Ne.symm hb) 1, map_zero, zero_mul]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (Ne.symm ha) g b 1, map_zero, zero_mul]
  -- Reduce `p` to its monomials; each is realizable.
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hwt : Finsupp.weight (matrixWeight k N) u = d := hhom (MvPolynomial.mem_support_iff.1 hu)
  obtain ⟨f, g, hfg⟩ := exists_fg_realizes k N n slot u fun i => by
    rw [curry_sum_eq_weight, hwt]; exact (hslot i).symm
  have hmem : MvPolynomial.monomial u (1 : ℂ) ∈ LinearMap.range (endTensorEval k N n slot) := by
    have hX : ∀ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : MatrixTupleRing k N)
        = MvPolynomial.monomial (Finsupp.single (slot j, g j, f j) 1) 1 := fun j => by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    have hprod : (∏ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : MatrixTupleRing k N))
        = MvPolynomial.monomial u 1 := by
      simp_rw [hX]
      rw [prod_monomial_single, hfg]
    rw [← hprod]
    exact hmono f g
  rw [show MvPolynomial.monomial u (MvPolynomial.coeff u p)
      = MvPolynomial.coeff u p • MvPolynomial.monomial u (1 : ℂ) by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ hmem

end Etingof
