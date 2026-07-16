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
