import Mathlib
import EtingofRepresentationTheory.Chapter5.Problem5_24_2_Core
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer

/-!
# Problem 5.24.2, steps 1–2: the coordinate ↔ tensor correspondence

This file builds the linear correspondence between the coordinate ring of matrix invariants
(`Etingof.MatrixTupleRing`, developed in `Problem5_24_2.lean`) and the Schur–Weyl tensor framework
(`Etingof.TensorPower`, `symGroupImage`, in `Theorem5_18_4.lean`), following steps 1–2 of the book's
hint for Problem 5.24.2.

## The setup

Take `V = ℂ^N = Fin N → ℂ`, so `End V ≃ Matrix (Fin N) (Fin N) ℂ` and
`End(V)^{⊗n} ≃ End(V^{⊗n}) = Module.End ℂ (TensorPower ℂ V n)`. The `GL(V)`-invariant part of
`End(V)^{⊗n}` (endomorphisms of `V^{⊗n}` commuting with the diagonal `GL(V)`-action) is exactly
`symGroupImage ℂ V n`, the `ℂ`-span of the permutation operators `symGroupAction σ`; this is the
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
`traceWord`, one per cycle of `σ`: this is the tensor-trace ↔ trace-word identity. Combining that
identity with Schur–Weyl permutation-spanning (`Theorem5_18_4_centralizers`) and the range
identification stated here (`weightedHomogeneous_invariant_mem_range_endTensorEval`) proves
`weightedHomogeneous_invariant_mem_adjoin` in `Problem5_24_2.lean`.
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
(one per cycle of `σ`), the tensor-trace ↔ trace-word identity. -/
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
`V^{⊗n}`, and `(g^{⊗n})⁻¹` is the corresponding operator for `g⁻¹`. This equivariance lets the
range identification transport `GL(V)`-invariance of tensors to conjugation-invariance
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

/-! ### Surjectivity onto degree-`d` polynomials (the combinatorial core)

The remaining fact needed for the First Fundamental Theorem is that every
`matrixWeight`-homogeneous polynomial of multidegree `d` lies in the range of `endTensorEval slot`
(before imposing `GL`-invariance): the generic-tensor monomials `∏ⱼ X_{slot j, gⱼ, fⱼ}` already
exhaust the degree-`d` part of the coordinate ring. This is purely combinatorial (realizing each
degree-`d` exponent vector `u` by a slot assignment `(f, g)`), and is proved here independently of
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

/-- **Surjectivity onto the degree-`d` part (FFT range identification).** Every polynomial in
the coordinate ring `MatrixTupleRing k N` that is `matrixWeight`-homogeneous of multidegree `d` lies
in the range of the evaluation pairing `endTensorEval slot`, for any slot assignment `slot`
compatible with `d` (slot `j` carries letter `i` for exactly `d i` slots).

The range contains every generic-tensor monomial `∏ⱼ X_{slot j, gⱼ, fⱼ}` (it is the value of
`endTensorEval slot` on the standard matrix unit, since only one term of the complete contraction
survives). A degree-`d` polynomial is a `ℂ`-combination of such monomials (each exponent vector in
its support is realizable by a slot assignment, `exists_fg_realizes`), and the range is a
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

/-! ## Block-symmetrization: the Reynolds operator on `End(V^{⊗n})`

The `GL`-equivariant section is built by block-symmetrization. The *block symmetric group* of a slot
assignment `slot` is the set of permutations `τ` of the `n` tensor slots that preserve the letter
carried by each slot (`slot ∘ τ = slot`). Averaging the conjugation `M ↦ P_τ · M · P_τ⁻¹` by the
permutation operators `P_τ = symGroupAction τ` over this finite group is a `ℂ`-linear projection
`reynolds` onto the block-symmetric endomorphisms. It has three key properties:

* `endTensorEval_reynolds`: `endTensorEval slot` is unchanged by `reynolds` (the generic tensor is
  block-symmetric);
* `reynolds_conj`: `reynolds` commutes with the diagonal `GL`-conjugation `M ↦ g^{⊗n}⁻¹ M g^{⊗n}`
  (permutation operators commute with diagonal operators, Schur–Weyl);
* `reynolds_injective`: `endTensorEval slot` is injective on the image of `reynolds`.

Together these let any fibrewise section (chosen from the surjectivity
`weightedHomogeneous_mem_range_endTensorEval`) be block-symmetrized into an equivariant one: the
equivariance follows by injectivity from the trace identity `endTensorEval_conj`. -/

open scoped Classical in
/-- The block symmetric group of a slot assignment `slot`: the permutations of the `n` tensor slots
that preserve the letter each slot carries (`slot ∘ τ = slot`). -/
noncomputable def blockPerms (slot : Fin n → Fin k) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun τ => slot ∘ τ = slot

/-- The identity permutation preserves every slot assignment, so `blockPerms` is nonempty; in
particular its cardinality is nonzero, which is what makes the Reynolds average well-defined. -/
theorem one_mem_blockPerms (slot : Fin n → Fin k) : (1 : Equiv.Perm (Fin n)) ∈ blockPerms k n slot := by
  classical
  rw [blockPerms, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by ext j; rfl⟩

theorem blockPerms_card_ne_zero (slot : Fin n → Fin k) : (blockPerms k n slot).card ≠ 0 := by
  exact Finset.card_ne_zero.mpr ⟨1, one_mem_blockPerms k n slot⟩

/-- The block-symmetrization Reynolds operator on `End(V^{⊗n})`: the average of the conjugations
`P_τ · M · P_τ⁻¹` by the permutation operators `P_τ = symGroupAction τ` over the block symmetric
group `blockPerms slot`. -/
noncomputable def reynolds (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    Module.End ℂ (TensorPower ℂ (BridgeV N) n) :=
  ((blockPerms k n slot).card : ℂ)⁻¹ • ∑ τ ∈ blockPerms k n slot,
    (symGroupAction ℂ (BridgeV N) n τ).toLinearMap * M
      * (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap

/-- The matrix, in the standard tensor basis, of the permutation operator `symGroupAction σ`: its
`(p, q)` entry is `1` when `p = q ∘ σ⁻¹` and `0` otherwise. It is a permutation matrix on the index
set `Fin n → Fin N`. -/
theorem toMatrix_symGroupAction (σ : Equiv.Perm (Fin n)) (p q : Fin n → Fin N) :
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
        (symGroupAction ℂ (BridgeV N) n σ).toLinearMap p q
      = if p = q ∘ (σ⁻¹ : Equiv.Perm (Fin n)) then 1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply]
  change (tensorBasis N n).repr
      ((symGroupAction ℂ (BridgeV N) n σ) (tensorBasis N n q)) p = _
  rw [tensorBasis, Basis.piTensorProduct_apply, symGroupAction, PiTensorProduct.reindex_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : p = q ∘ (σ⁻¹ : Equiv.Perm (Fin n))
  · rw [if_pos h]
    refine Finset.prod_eq_one fun i _ => if_pos ?_
    subst h; rfl
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) (if_neg fun heq => ?_)
    exact hi heq.symm

/-- **Block-invariance of the generic tensor matrix.** Conjugating the generic tensor matrix by the
permutation matrices of a block permutation `τ` (`slot ∘ τ = slot`) leaves it unchanged: permuting
slots within each letter block reorders the identical factors of `⨂ⱼ X_{slot j}`. -/
theorem genericTensorMatrix_symConj (slot : Fin n → Fin k)
    {τ : Equiv.Perm (Fin n)} (hτ : slot ∘ τ = slot) :
    (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap).map
          (algebraMap ℂ (MatrixTupleRing k N))
        * genericTensorMatrix k N n slot
        * (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ).toLinearMap).map
          (algebraMap ℂ (MatrixTupleRing k N))
      = genericTensorMatrix k N n slot := by
  classical
  refine Matrix.ext fun e f => ?_
  -- Entrywise values of the two permutation matrices (mapped to the coordinate ring).
  have hpermL : ∀ a : Fin n → Fin N,
      (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ).toLinearMap).map
          (algebraMap ℂ (MatrixTupleRing k N)) a f
        = if a = f ∘ (τ⁻¹ : Equiv.Perm (Fin n)) then (1 : MatrixTupleRing k N) else 0 := by
    intro a
    rw [Matrix.map_apply, toMatrix_symGroupAction]
    by_cases h : a = f ∘ (τ⁻¹ : Equiv.Perm (Fin n)) <;> simp [h]
  have hpermR : ∀ b : Fin n → Fin N,
      (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap).map
          (algebraMap ℂ (MatrixTupleRing k N)) e b
        = if e = b ∘ (τ : Equiv.Perm (Fin n)) then (1 : MatrixTupleRing k N) else 0 := by
    intro b
    rw [Matrix.map_apply, toMatrix_symGroupAction, inv_inv]
    by_cases h : e = b ∘ (τ : Equiv.Perm (Fin n)) <;> simp [h]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (f ∘ (τ⁻¹ : Equiv.Perm (Fin n)))]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e ∘ (τ⁻¹ : Equiv.Perm (Fin n)))]
    · rw [hpermR (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))), hpermL (f ∘ (τ⁻¹ : Equiv.Perm (Fin n))),
        if_pos (show e = (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))) ∘ (τ : Equiv.Perm (Fin n)) by
          funext j; simp),
        if_pos rfl, one_mul, mul_one]
      -- `gTM (e∘τ⁻¹) (f∘τ⁻¹) = gTM e f`: reindex the slot product by `τ`.
      simp only [genericTensorMatrix]
      rw [← Equiv.prod_comp τ (fun j => MvPolynomial.X
        (slot j, (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))) j, (f ∘ (τ⁻¹ : Equiv.Perm (Fin n))) j))]
      have hinv : ∀ x : Fin n, (τ⁻¹ : Equiv.Perm (Fin n)) (τ x) = x :=
        fun x => Equiv.symm_apply_apply τ x
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Function.comp_apply, hinv, show slot (τ j) = slot j from congrFun hτ j]
    · intro b _ hbne
      rw [hpermR b, if_neg (fun he => hbne (by
        funext j; have := congrFun he ((τ⁻¹ : Equiv.Perm (Fin n)) j); simpa using this.symm)),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ hane
    rw [hpermL a, if_neg hane, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Block-invariance of the evaluation pairing.** Conjugating an endomorphism by a block
permutation operator `P_τ` (`τ ∈ blockPerms slot`) leaves its evaluation unchanged: the generic
tensor `⨂ⱼ X_{slot j}` is invariant under permuting slots within each letter block. -/
theorem endTensorEval_symGroupConj (slot : Fin n → Fin k)
    {τ : Equiv.Perm (Fin n)} (hτ : τ ∈ blockPerms k n slot)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    endTensorEval k N n slot
        ((symGroupAction ℂ (BridgeV N) n τ).toLinearMap * M
          * (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap)
      = endTensorEval k N n slot M := by
  classical
  have hslotτ : slot ∘ τ = slot := by
    rw [blockPerms, Finset.mem_filter] at hτ; exact hτ.2
  rw [endTensorEval_eq_evalMatrix, endTensorEval_eq_evalMatrix,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, evalMatrix_eq_trace, evalMatrix_eq_trace,
    Matrix.map_mul, Matrix.map_mul]
  set C := algebraMap ℂ (MatrixTupleRing k N)
  set PL := (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
    (symGroupAction ℂ (BridgeV N) n τ).toLinearMap).map C with hPL
  set PR := (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
    (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap).map C with hPR
  set A := (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M).map C with hA
  set G := genericTensorMatrix k N n slot with hG
  -- `trace((PL A PR) G) = trace(A (PR G PL)) = trace(A G)` by cyclicity and block-invariance.
  have key : PR * G * PL = G := genericTensorMatrix_symConj k N n slot hslotτ
  have hassoc : PL * A * PR * G = PL * (A * PR * G) := by
    rw [mul_assoc (PL * A) PR G, mul_assoc PL A (PR * G), ← mul_assoc A PR G]
  rw [hassoc, Matrix.trace_mul_comm,
    show A * PR * G * PL = A * (PR * G * PL) from by
      rw [mul_assoc (A * PR) G PL, mul_assoc A PR (G * PL), ← mul_assoc PR G PL],
    key]

/-- **`endTensorEval` is unchanged by the Reynolds operator.** Each conjugate summand has the same
evaluation (`endTensorEval_symGroupConj`), and the `(card)⁻¹` normalization cancels the count. -/
theorem endTensorEval_reynolds (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    endTensorEval k N n slot (reynolds k N n slot M) = endTensorEval k N n slot M := by
  classical
  rw [reynolds, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun τ hτ => endTensorEval_symGroupConj k N n slot hτ M]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast blockPerms_card_ne_zero k n slot), one_smul]

/-- **The Reynolds operator commutes with diagonal `GL`-conjugation.** Because each permutation
operator `P_τ` commutes with the diagonal operator `g^{⊗n}` (Schur–Weyl,
`symGroupAction_comm_diagonalAction`), averaging the conjugation-by-`P_τ` commutes with conjugating
by `g^{⊗n}`. This makes the image of `reynolds` stable under the diagonal `GL`-action. -/
theorem reynolds_conj (slot : Fin n → Fin k) (g : (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    reynolds k N n slot
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
          * M
          * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
        * reynolds k N n slot M
        * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)) := by
  classical
  set Q := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
    with hQ
  set P := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))
    with hP
  rw [reynolds, reynolds, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ hτ => ?_
  set Pτ := (symGroupAction ℂ (BridgeV N) n τ).toLinearMap with hPτ
  set Pτ' := (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap with hPτ'
  have hcQ : Commute Pτ Q := by
    rw [Commute, SemiconjBy, hPτ, hQ, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact symGroupAction_comm_diagonalAction ℂ (BridgeV N) n τ
      (Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
  have hcP' : Commute Pτ' P := by
    rw [Commute, SemiconjBy, hPτ', hP, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact symGroupAction_comm_diagonalAction ℂ (BridgeV N) n τ⁻¹
      (Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))
  -- `Pτ (Q M P) Pτ' = Q (Pτ M Pτ') P` by sliding `Q` left past `Pτ` and `P` right past `Pτ'`.
  simp only [mul_assoc]
  rw [show P * Pτ' = Pτ' * P from hcP'.symm.eq, ← mul_assoc Pτ Q,
    show Pτ * Q = Q * Pτ from hcQ.eq, mul_assoc Q Pτ]

/-- `reynolds` is `ℂ`-linear, so it commutes with subtraction. -/
private theorem reynolds_sub (slot : Fin n → Fin k)
    (M M' : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) :
    reynolds k N n slot (M - M') = reynolds k N n slot M - reynolds k N n slot M' := by
  classical
  rw [reynolds, reynolds, reynolds, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_sub, sub_mul]

/-- **Matrix of a Reynolds summand.** Conjugating `M` by the permutation operators of `τ` and `τ⁻¹`
reindexes its matrix by `τ`: the `(a, b)` entry of `P_τ · M · P_{τ⁻¹}` is `M_{a∘τ, b∘τ}`. -/
private theorem toMatrix_reynolds_summand (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) (τ : Equiv.Perm (Fin n))
    (a b : Fin n → Fin N) :
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
        ((symGroupAction ℂ (BridgeV N) n τ).toLinearMap * M
          * (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap) a b
      = LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M (a ∘ τ) (b ∘ τ) := by
  classical
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
  set A := LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M with hA
  have hPLval : ∀ p : Fin n → Fin N,
      LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ).toLinearMap a p
        = if a = p ∘ (τ⁻¹ : Equiv.Perm (Fin n)) then (1 : ℂ) else 0 := by
    intro p; rw [toMatrix_symGroupAction]
  have hPRval : ∀ q : Fin n → Fin N,
      LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)
          (symGroupAction ℂ (BridgeV N) n τ⁻¹).toLinearMap q b
        = if q = b ∘ (τ : Equiv.Perm (Fin n)) then (1 : ℂ) else 0 := by
    intro q; rw [toMatrix_symGroupAction, inv_inv]
  rw [Matrix.mul_apply, Finset.sum_eq_single (b ∘ (τ : Equiv.Perm (Fin n)))]
  · rw [hPRval, if_pos rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (a ∘ (τ : Equiv.Perm (Fin n)))]
    · rw [hPLval, if_pos (show a = (a ∘ (τ : Equiv.Perm (Fin n))) ∘ (τ⁻¹ : Equiv.Perm (Fin n)) by
          funext j; simp), one_mul]
    · intro p _ hp
      rw [hPLval, if_neg (fun he => hp (by
        funext j; have := congrFun he ((τ : Equiv.Perm (Fin n)) j); simpa using this.symm)),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rw [hPRval, if_neg hq, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Matrix of the Reynolds operator.** Its `(a, b)` entry is the block average of the reindexed
entries `M_{a∘τ, b∘τ}` of `M` over the block symmetric group. -/
private theorem toMatrix_reynolds (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) (a b : Fin n → Fin N) :
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) (reynolds k N n slot M) a b
      = ((blockPerms k n slot).card : ℂ)⁻¹
        • ∑ τ ∈ blockPerms k n slot,
            LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M (a ∘ τ) (b ∘ τ) := by
  classical
  rw [reynolds, map_smul, map_sum, Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact toMatrix_reynolds_summand k N n slot M τ a b

/-- **Block symmetry of the Reynolds operator.** Its matrix is invariant under reindexing rows and
columns by a block permutation `ρ` (`ρ ∈ blockPerms slot`): the block average absorbs the extra
translation. -/
private theorem reynolds_block_symmetric (slot : Fin n → Fin k)
    (M : Module.End ℂ (TensorPower ℂ (BridgeV N) n)) {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ blockPerms k n slot) (a b : Fin n → Fin N) :
    LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) (reynolds k N n slot M)
        (a ∘ ρ) (b ∘ ρ)
      = LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) (reynolds k N n slot M) a b := by
  classical
  have hslotρ : slot ∘ ρ = slot := by rw [blockPerms, Finset.mem_filter] at hρ; exact hρ.2
  have hmem : ∀ σ : Equiv.Perm (Fin n), σ ∈ blockPerms k n slot →
      ρ * σ ∈ blockPerms k n slot := by
    intro σ hσ
    rw [blockPerms, Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    change slot (ρ (σ j)) = slot j
    have h1 : slot (ρ (σ j)) = slot (σ j) := congrFun hslotρ (σ j)
    have h2 : slot (σ j) = slot j := congrFun hσ.2 j
    rw [h1, h2]
  have hslotρinv : slot ∘ (ρ⁻¹ : Equiv.Perm (Fin n)) = slot := by
    funext j
    have h1 : slot (ρ (ρ⁻¹ j)) = slot (ρ⁻¹ j) := congrFun hslotρ (ρ⁻¹ j)
    have hρρ : ρ (ρ⁻¹ j) = j := Equiv.apply_symm_apply ρ j
    rw [hρρ] at h1
    exact h1.symm
  have hmemInv : ∀ σ : Equiv.Perm (Fin n), σ ∈ blockPerms k n slot →
      ρ⁻¹ * σ ∈ blockPerms k n slot := by
    intro σ hσ
    rw [blockPerms, Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    change slot (ρ⁻¹ (σ j)) = slot j
    have h1 : slot (ρ⁻¹ (σ j)) = slot (σ j) := congrFun hslotρinv (σ j)
    have h2 : slot (σ j) = slot j := congrFun hσ.2 j
    rw [h1, h2]
  have hsum : (∑ τ ∈ blockPerms k n slot,
        LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M ((a ∘ ρ) ∘ τ) ((b ∘ ρ) ∘ τ))
      = ∑ τ ∈ blockPerms k n slot,
        LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) M (a ∘ τ) (b ∘ τ) := by
    refine Finset.sum_nbij' (fun τ => ρ * τ) (fun τ => ρ⁻¹ * τ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ; exact hmem σ hσ
    · intro σ hσ; exact hmemInv σ hσ
    · intro σ _; rw [← mul_assoc, inv_mul_cancel, one_mul]
    · intro σ _; rw [← mul_assoc, mul_inv_cancel, one_mul]
    · intro σ _
      congr 1 <;>
        · funext j; simp only [Function.comp_apply, Equiv.Perm.mul_apply]
  rw [toMatrix_reynolds, toMatrix_reynolds, hsum]

/-- The generic tensor matrix entry `(g, f)` is the monomial of the exponent vector realized by the
slot assignment `(f, g)`. -/
private theorem genericTensorMatrix_eq_monomial (slot : Fin n → Fin k) (g f : Fin n → Fin N) :
    genericTensorMatrix k N n slot g f
      = MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) (1 : ℂ) := by
  classical
  rw [genericTensorMatrix]
  have hX : ∀ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : MatrixTupleRing k N)
      = MvPolynomial.monomial (Finsupp.single (slot j, g j, f j) 1) 1 := fun j => by
    rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
  simp_rw [hX]
  rw [prod_monomial_single]

/-- Given two sequences `f g : Fin m → α` with equal underlying multiset, an explicit permutation
`σ` matching them (`g = f ∘ σ`). Peel the head of `g` and match it against an element of `f`'s
domain. -/
private noncomputable def matchingPerm {α : Type*} [DecidableEq α] :
    ∀ {m : ℕ} (f g : Fin m → α),
      Multiset.map f (Finset.univ : Finset (Fin m)).val =
        Multiset.map g (Finset.univ : Finset (Fin m)).val →
      {σ : Equiv.Perm (Fin m) // g = f ∘ σ}
  | 0, _, g, _ => ⟨Equiv.refl _, funext fun i => i.elim0⟩
  | m + 1, f, g, h =>
      let hg0_mem : g 0 ∈ Multiset.map f (Finset.univ : Finset (Fin (m+1))).val := by
        rw [h]; exact Multiset.mem_map.mpr ⟨0, Finset.mem_univ_val _, rfl⟩
      let l₀ : Fin (m+1) := Classical.choose (Multiset.mem_map.mp hg0_mem)
      let l₀_spec :
        l₀ ∈ (Finset.univ : Finset (Fin (m+1))).val ∧ f l₀ = g 0 :=
        Classical.choose_spec (Multiset.mem_map.mp hg0_mem)
      let hl₀ : f l₀ = g 0 := l₀_spec.2
      let f' : Fin m → α := f ∘ l₀.succAbove
      let g' : Fin m → α := g ∘ Fin.succ
      let hpeel_f : Multiset.map f (Finset.univ : Finset (Fin (m+1))).val =
          f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin m)).val := by
        conv_lhs => rw [Fin.univ_succAbove m l₀]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb]
        rfl
      let hpeel_g : Multiset.map g (Finset.univ : Finset (Fin (m+1))).val =
          g 0 ::ₘ Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
        conv_lhs => rw [Fin.univ_succAbove m 0]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb, Fin.succAbove_zero]
        rfl
      let hms : Multiset.map f' (Finset.univ : Finset (Fin m)).val =
          Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
        have hh : f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin m)).val =
            f l₀ ::ₘ Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
          rw [← hpeel_f, h, hpeel_g, hl₀]
        exact (Multiset.cons_inj_right _).mp hh
      let σ'_pkg := matchingPerm f' g' hms
      let σ' : Equiv.Perm (Fin m) := σ'_pkg.1
      let hσ' : g' = f' ∘ σ' := σ'_pkg.2
      let σ_fn : Fin (m+1) → Fin (m+1) :=
        Fin.cases l₀ (fun j => l₀.succAbove (σ' j))
      let hinj : Function.Injective σ_fn := by
        intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => rfl
          | succ b =>
            exfalso
            change l₀ = l₀.succAbove (σ' b) at hij
            exact (Fin.succAbove_ne l₀ (σ' b)) hij.symm
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            exfalso
            change l₀.succAbove (σ' a) = l₀ at hij
            exact (Fin.succAbove_ne l₀ (σ' a)) hij
          | succ b =>
            change l₀.succAbove (σ' a) = l₀.succAbove (σ' b) at hij
            have h1 : σ' a = σ' b := l₀.succAbove_right_injective hij
            have h2 : a = b := σ'.injective h1
            exact congrArg Fin.succ h2
      let hbij : Function.Bijective σ_fn :=
        Finite.injective_iff_bijective.mp hinj
      ⟨Equiv.ofBijective σ_fn hbij, by
        funext i
        induction i using Fin.cases with
        | zero =>
          change g 0 = f (σ_fn 0)
          change g 0 = f l₀
          exact hl₀.symm
        | succ j =>
          change g (Fin.succ j) = f (σ_fn (Fin.succ j))
          change g (Fin.succ j) = f (l₀.succAbove (σ' j))
          have := congrFun hσ' j
          change g' j = f' (σ' j)
          exact this⟩

/-- For any sequence `g : Fin n → α`, the multiset of values equals
`Finsupp.toMultiset (∑ l, single (g l) 1)`. -/
private theorem toMultiset_sum_single_fn {α : Type*} [DecidableEq α] (g : Fin n → α) :
    Finsupp.toMultiset (∑ l : Fin n, Finsupp.single (g l) (1 : ℕ)) =
      Multiset.map g (Finset.univ : Finset (Fin n)).val := by
  classical
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.insert_val, Multiset.ndinsert_of_notMem ha,
      Multiset.map_cons, Multiset.singleton_add]

/-- **Single-orbit realizability.** If a slot-assignment pair `(f, g)` realizes the same exponent
vector as `(f₀, g₀)`, then it is obtained from `(f₀, g₀)` by a block permutation `σ`: matching the
common multiset of triples `(slot j, · j, · j)` produces a slot-preserving `σ` with `f = f₀ ∘ σ`,
`g = g₀ ∘ σ`. -/
private theorem exists_blockPerm_of_sum_single_eq (slot : Fin n → Fin k)
    (f g f₀ g₀ : Fin n → Fin N)
    (h : ∑ j : Fin n, Finsupp.single (slot j, g j, f j) (1 : ℕ)
        = ∑ j : Fin n, Finsupp.single (slot j, g₀ j, f₀ j) (1 : ℕ)) :
    ∃ σ ∈ blockPerms k n slot, f = f₀ ∘ σ ∧ g = g₀ ∘ σ := by
  classical
  have hmulti : Multiset.map (fun j => ((slot j, g₀ j, f₀ j) : Fin k × Fin N × Fin N))
        (Finset.univ : Finset (Fin n)).val
      = Multiset.map (fun j => ((slot j, g j, f j) : Fin k × Fin N × Fin N))
        (Finset.univ : Finset (Fin n)).val := by
    rw [← toMultiset_sum_single_fn, ← toMultiset_sum_single_fn, h]
  obtain ⟨σ, hσ⟩ := matchingPerm
    (fun j => ((slot j, g₀ j, f₀ j) : Fin k × Fin N × Fin N))
    (fun j => ((slot j, g j, f j) : Fin k × Fin N × Fin N)) hmulti
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [blockPerms, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    change slot (σ j) = slot j
    exact hj.1.symm
  · funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    exact hj.2.2
  · funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    exact hj.2.1

/-- **Injectivity core.** A block-symmetric endomorphism (in the image of `reynolds`) whose
evaluation vanishes is zero: reading off the coefficient of each monomial, the block symmetry makes
the matrix constant on each single realizability orbit, and the positive orbit count over `ℂ` forces
every matrix entry to zero. -/
private theorem reynolds_eq_zero_of_endTensorEval_zero (slot : Fin n → Fin k)
    (W₀ : Module.End ℂ (TensorPower ℂ (BridgeV N) n))
    (hW : endTensorEval k N n slot (reynolds k N n slot W₀) = 0) :
    reynolds k N n slot W₀ = 0 := by
  classical
  set W := reynolds k N n slot W₀ with hWdef
  suffices hzero : ∀ f g : Fin n → Fin N,
      LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f g = 0 by
    have hmat : LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W = 0 := by
      ext f g; exact hzero f g
    have hsymm : (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)).symm
          (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W)
        = (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n)).symm 0 := by rw [hmat]
    rwa [LinearEquiv.symm_apply_apply, map_zero] at hsymm
  intro f₀ g₀
  set u₀ : (Fin k × Fin N × Fin N) →₀ ℕ :=
    ∑ j : Fin n, Finsupp.single (slot j, g₀ j, f₀ j) 1 with hu₀
  -- `endTensorEval W` is a sum of monomials, one per pair `(f, g)`.
  have hEval : endTensorEval k N n slot W
      = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1)
            (LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f g) := by
    rw [endTensorEval_apply]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    rw [genericTensorMatrix_eq_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial,
      mul_one]
  -- The coefficient of `monomial u₀` vanishes.
  have hcoeff : (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f g else 0)) = 0 := by
    have hc : MvPolynomial.coeff u₀ (endTensorEval k N n slot W) = 0 := by
      rw [hW, MvPolynomial.coeff_zero]
    rw [hEval] at hc
    simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
    exact hc
  -- Block symmetry makes the surviving entries all equal to the `(f₀, g₀)` entry.
  have hconst : ∀ f g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f g else 0)
        = (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0) := by
    intro f g
    by_cases hfg : (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀
    · rw [if_pos hfg, if_pos hfg]
      obtain ⟨σ, hσbp, hfσ, hgσ⟩ :=
        exists_blockPerm_of_sum_single_eq k N n slot f g f₀ g₀ (by rw [hfg, hu₀])
      have hbs := reynolds_block_symmetric k N n slot W₀ hσbp f₀ g₀
      rw [← hWdef] at hbs
      rw [hfσ, hgσ]
      exact hbs
    · rw [if_neg hfg, if_neg hfg]
  have hcoeff2 : (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0)) = 0 := by
    rw [show (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0))
        = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f g else 0) from
      Finset.sum_congr rfl fun f _ =>
        Finset.sum_congr rfl fun g _ => (hconst f g).symm]
    exact hcoeff
  -- Fold the double sum into a cardinality times the `(f₀, g₀)` entry.
  have hcombine : (∑ p : (Fin n → Fin N) × (Fin n → Fin N),
        (if (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0))
      = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0) :=
    Fintype.sum_prod_type _
  have hpc : (∑ p : (Fin n → Fin N) × (Fin n → Fin N),
        (if (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀ then
          LinearMap.toMatrix (tensorBasis N n) (tensorBasis N n) W f₀ g₀ else 0)) = 0 := by
    rw [hcombine]; exact hcoeff2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hpc
  have hmemfilter : (f₀, g₀) ∈
      (Finset.univ.filter fun p : (Fin n → Fin N) × (Fin n → Fin N) =>
        (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hu₀.symm⟩
  have hcard_ne : ((Finset.univ.filter fun p : (Fin n → Fin N) × (Fin n → Fin N) =>
        (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀).card : ℂ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp ⟨(f₀, g₀), hmemfilter⟩
  exact (mul_eq_zero.mp hpc).resolve_left hcard_ne

/-- **Injectivity of the evaluation pairing on block-symmetric endomorphisms.** Two endomorphisms in
the image of the Reynolds operator with the same evaluation are equal: the block-symmetric
endomorphisms are exactly the span of the uniform averages of matrix units over the fibres of
`endTensorEval slot`, so distinct evaluations come from distinct block-symmetric endomorphisms. -/
theorem reynolds_injective (slot : Fin n → Fin k)
    (M M' : Module.End ℂ (TensorPower ℂ (BridgeV N) n))
    (h : endTensorEval k N n slot (reynolds k N n slot M)
          = endTensorEval k N n slot (reynolds k N n slot M')) :
    reynolds k N n slot M = reynolds k N n slot M' := by
  -- Outline. By linearity of `reynolds` and `endTensorEval` it suffices
  -- to show: if `W` is block-symmetric (`W = reynolds W₀` for some `W₀`) and `endTensorEval W = 0`
  -- then `W = 0`. Write `W_{a,b} := toMatrix W a b`. Two facts close this:
  --   (1) `toMatrix (reynolds W₀) a b = (card)⁻¹ • ∑_{σ ∈ blockPerms} W₀_{a∘σ, b∘σ}` (from
  --       `toMatrix_symGroupAction`, mirroring `genericTensorMatrix_symConj`), so `W_{a∘σ, b∘σ} =
  --       W_{a,b}` for `σ ∈ blockPerms`, i.e. block-symmetry of `W`.
  --   (2) The coefficient of `monomial u 1` in `endTensorEval W` is `∑_{(a,b) : u(b,a) = u} W_{a,b}`
  --       where `u(b,a) = ∑ⱼ single (slot j, b j, a j) 1`; and the index set `{(a,b) : u(b,a) = u}`
  --       is a single `blockPerms`-orbit under `(a,b) ↦ (a∘σ, b∘σ)` (multiset-matching, mirroring
  --       `PolynomialTensorBridge.matchingPerm`). Block-symmetry makes `W` constant on that orbit,
  --       so the coefficient is `(orbit card) • W_{a,b}`; `endTensorEval W = 0` forces every
  --       coefficient to vanish (monomials are linearly independent), hence every `W_{a,b} = 0`.
  classical
  have hz : endTensorEval k N n slot (reynolds k N n slot (M - M')) = 0 := by
    rw [reynolds_sub, map_sub, h, sub_self]
  have hzero : reynolds k N n slot (M - M') = 0 :=
    reynolds_eq_zero_of_endTensorEval_zero k N n slot (M - M') hz
  rw [reynolds_sub, sub_eq_zero] at hzero
  exact hzero

/-- **Conjugation preserves multidegree.** The simultaneous-conjugation automorphism `conjAlgHom g`
of the coordinate ring preserves the `matrixWeight`-multidegree: it substitutes each variable
`X (i, r, c)` (weight `single i 1`) by a `ℂ`-combination of variables `X (i, s, t)` with the same
letter `i`, hence the same weight. -/
theorem conjAlgHom_isWeightedHomogeneous (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (d : Fin k →₀ ℕ)
    {p : MatrixTupleRing k N} (hp : IsWeightedHomogeneous (matrixWeight k N) p d) :
    IsWeightedHomogeneous (matrixWeight k N) (conjAlgHom k N g p) d := by
  classical
  -- Each generator `X (i, r, c)` maps to a `ℂ`-combination of variables `X (i, s, t)` with the same
  -- letter `i`, hence weight `matrixWeight (i, r, c) = single i 1` is preserved.
  have hgen : ∀ v : Fin k × Fin N × Fin N,
      IsWeightedHomogeneous (matrixWeight k N) (conjAlgHom k N g (X v)) (matrixWeight k N v) := by
    rintro ⟨i, r, c⟩
    rw [conjAlgHom_X_sum]
    refine IsWeightedHomogeneous.sum _ _ _ (fun s _ =>
      IsWeightedHomogeneous.sum _ _ _ (fun t _ => ?_))
    have hXst : IsWeightedHomogeneous (matrixWeight k N) (X (i, s, t) : MatrixTupleRing k N)
        (matrixWeight k N (i, s, t)) := isWeightedHomogeneous_X ℂ (matrixWeight k N) (i, s, t)
    have hw : matrixWeight k N (i, s, t) = matrixWeight k N (i, r, c) := rfl
    rw [← hw, show algebraMap ℂ (MatrixTupleRing k N) ((↑g : Matrix (Fin N) (Fin N) ℂ) r s)
          * X (i, s, t)
          * algebraMap ℂ (MatrixTupleRing k N) ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c)
        = MvPolynomial.C ((↑g : Matrix (Fin N) (Fin N) ℂ) r s
            * (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c) * X (i, s, t) by
      rw [map_mul, MvPolynomial.algebraMap_eq]; ring]
    exact hXst.C_mul _
  -- Powers of a weighted-homogeneous element scale the weight.
  have hpow : ∀ (φ : MatrixTupleRing k N) (m : Fin k →₀ ℕ) (e : ℕ),
      IsWeightedHomogeneous (matrixWeight k N) φ m →
      IsWeightedHomogeneous (matrixWeight k N) (φ ^ e) (e • m) := by
    intro φ m e hφ
    induction e with
    | zero => simpa using isWeightedHomogeneous_one ℂ (matrixWeight k N)
    | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ
  -- A monomial of weight `d` maps to a weighted-homogeneous polynomial of weight `d`.
  have hmon : ∀ (u : (Fin k × Fin N × Fin N) →₀ ℕ) (c : ℂ),
      Finsupp.weight (matrixWeight k N) u = d →
      IsWeightedHomogeneous (matrixWeight k N) (conjAlgHom k N g (monomial u c)) d := by
    intro u c hwu
    rw [MvPolynomial.monomial_eq, map_mul,
      show conjAlgHom k N g (C c) = C c from by
        rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ c]
    simp only [Finsupp.prod, map_prod, map_pow]
    have hdeg : ∑ v ∈ u.support, (u v) • matrixWeight k N v = d := by
      rw [← hwu, Finsupp.weight_apply]; rfl
    have hprod := IsWeightedHomogeneous.prod u.support
      (fun v => conjAlgHom k N g (X v) ^ (u v))
      (fun v => (u v) • matrixWeight k N v)
      (fun v _ => hpow (conjAlgHom k N g (X v)) (matrixWeight k N v) (u v) (hgen v))
    rw [hdeg] at hprod
    exact hprod.C_mul c
  rw [p.as_sum, map_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun u hu =>
    hmon u _ (hp (MvPolynomial.mem_support_iff.mp hu)))

/-- **The GL-equivariant section.** There is a section `σ` of the evaluation pairing
`endTensorEval slot` on the multidegree-`d` part of the coordinate ring that is `GL(V)`-equivariant:
it sends each `matrixWeight`-homogeneous polynomial `p` of multidegree `d` to an endomorphism `σ p`
of `V^{⊗n}` with `endTensorEval slot (σ p) = p` (section property), and intertwines the
simultaneous-conjugation automorphism `conjAlgHom g` on polynomials with conjugation by the diagonal
operator `g^{⊗n}` on `End(V^{⊗n})` (equivariance).

This is the reductivity heart of the First Fundamental Theorem (book step 2), obtained (following
the single-matrix `PolynomialTensorBridge`) by an explicit block-symmetrization section rather than
an abstract Reynolds operator. The theorem `weightedHomogeneous_invariant_mem_range_endTensorEval`
below uses it: `GL`-invariance of `p` gives commutation of `σ p` with every diagonal operator, and
hence membership in `symGroupImage`. -/
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
  classical
  -- A fibrewise (not yet equivariant) section, chosen from the surjectivity result.
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : MatrixTupleRing k N → Module.End ℂ (TensorPower ℂ (BridgeV N) n),
      ∀ p : MatrixTupleRing k N, IsWeightedHomogeneous (matrixWeight k N) p d →
        endTensorEval k N n slot (σ₀ p) = p := by
    refine ⟨fun p => if h : IsWeightedHomogeneous (matrixWeight k N) p d
      then (LinearMap.mem_range.mp
        (weightedHomogeneous_mem_range_endTensorEval k N n d slot hslot h)).choose else 0, ?_⟩
    intro p hp
    simp only [dif_pos hp]
    exact (LinearMap.mem_range.mp
      (weightedHomogeneous_mem_range_endTensorEval k N n d slot hslot hp)).choose_spec
  -- The equivariant section is the block-symmetrization of `σ₀`.
  refine ⟨fun p => reynolds k N n slot (σ₀ p), ?_, ?_⟩
  · -- Section property: `reynolds` preserves the evaluation, and `σ₀` is already a section.
    intro p hp
    rw [endTensorEval_reynolds]
    exact hσ₀ p hp
  · -- Equivariance: both sides are `reynolds` of endomorphisms with equal evaluation.
    intro g p hp
    rw [← reynolds_conj]
    refine reynolds_injective k N n slot _ _ ?_
    rw [endTensorEval_reynolds, endTensorEval_reynolds, endTensorEval_conj,
      hσ₀ p hp, hσ₀ (conjAlgHom k N g p) (conjAlgHom_isWeightedHomogeneous k N g d hp)]

/-- **Range identification.** Every fixed-multidegree conjugation-invariant polynomial
lies in the image, under `endTensorEval slot`, of `symGroupImage ℂ V n`, the `GL(V)`-invariant part
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


end Etingof
