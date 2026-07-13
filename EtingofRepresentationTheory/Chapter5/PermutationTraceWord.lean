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

/-! ## The cycle structure of `σ` -/

/-- Orbit length of `i` under `σ`: the minimal period of the map `σ` at `i`. It is `1` for a fixed
point and `ℓ` for a point on an `ℓ`-cycle. -/
noncomputable def cyclePeriod {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) : ℕ :=
  Function.minimalPeriod (⇑σ) i

/-- Chosen orbit representatives of `σ`: the `≤`-minimal element of each `σ`-orbit. Two elements lie
in the same orbit iff `σ.SameCycle` relates them (including fixed points, where the orbit is a
singleton). -/
noncomputable def orbitReps {m : ℕ} (σ : Equiv.Perm (Fin m)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j : Fin m, σ.SameCycle i j → i ≤ j)

/-! ## The combinatorial core (matrix side) -/

/-! ## Walk-sum expansion of a matrix product

An ordered product of matrices, evaluated at an entry, expands as a sum over "walks": tuples of
intermediate indices, weighted by the product of the traversed matrix entries. Setting the two
endpoints equal and summing recovers the trace as a sum over *closed* walks. This is the analytic
engine behind the single-orbit telescoping. -/

section WalkSum

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ordered product of a `Fin ℓ`-indexed family of matrices: `N 0 * N 1 * … * N (ℓ-1)`. -/
def bigProd {ℓ : ℕ} (N : Fin ℓ → Matrix ι ι R) : Matrix ι ι R := (List.ofFn N).prod

@[simp] lemma bigProd_zero (N : Fin 0 → Matrix ι ι R) : bigProd N = 1 := by
  simp [bigProd]

lemma bigProd_cons {ℓ : ℕ} (M : Matrix ι ι R) (N : Fin ℓ → Matrix ι ι R) :
    bigProd (Fin.cons M N) = M * bigProd N := by
  simp [bigProd, List.ofFn_succ]

/-- Edge-product weight of a walk `v : Fin (ℓ+1) → ι` through the matrices `N`:
the product of the entries `N t` read at consecutive vertices `v t → v (t+1)`. -/
def walkWeight {ℓ : ℕ} (N : Fin ℓ → Matrix ι ι R) (v : Fin (ℓ + 1) → ι) : R :=
  ∏ t : Fin ℓ, N t (v t.castSucc) (v t.succ)

omit [Fintype ι] [DecidableEq ι] in
lemma walkWeight_cons {ℓ : ℕ} (N : Fin (ℓ + 1) → Matrix ι ι R) (z : ι)
    (v : Fin (ℓ + 1) → ι) :
    walkWeight N (Fin.cons z v) = N 0 z (v 0) * walkWeight (Fin.tail N) v := by
  unfold walkWeight
  rw [Fin.prod_univ_succ]
  congr 1

/-- **Open walk-sum for a matrix product entry.** The `(x, y)` entry of `N 0 * … * N (ℓ-1)` is the
sum over vertex functions `v : Fin (ℓ+1) → ι` of the edge-product weight, restricted to the walks
that start at `x` and end at `y`. -/
theorem bigProd_apply (ℓ : ℕ) (N : Fin ℓ → Matrix ι ι R) (x y : ι) :
    (bigProd N) x y
      = ∑ v : Fin (ℓ + 1) → ι,
          (if v 0 = x ∧ v (Fin.last ℓ) = y then walkWeight N v else 0) := by
  induction ℓ generalizing x with
  | zero =>
    rw [bigProd_zero, Matrix.one_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _
      (fun z => if z = x ∧ z = y then (1 : R) else 0)]
    · by_cases hxy : x = y
      · subst hxy
        rw [Finset.sum_eq_single x]
        · simp
        · intro z _ hz; simp [hz]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hxy]
        · intro z _; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hxy rfl
    · intro v
      simp only [walkWeight, Finset.univ_eq_empty, Finset.prod_empty, Equiv.funUnique_apply,
        Fin.last_zero, Fin.default_eq_zero]
  | succ ℓ ih =>
    -- peel the first matrix
    have hsplit : bigProd N = N 0 * bigProd (Fin.tail N) := by
      conv_lhs => rw [← Fin.cons_self_tail N]
      rw [bigProd_cons]
    rw [hsplit, Matrix.mul_apply]
    -- expand each inner entry by the induction hypothesis (start vertex = z)
    simp_rw [ih (Fin.tail N)]
    -- RHS: reindex the vertex sum by splitting off the first vertex via `Fin.cons`
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (ℓ + 2) => ι)),
      Fintype.sum_prod_type]
    have hlast : (Fin.last (ℓ + 1) : Fin (ℓ + 2)) = (Fin.last ℓ).succ := (Fin.succ_last ℓ).symm
    have hce : ∀ (z : ι) (w : Fin (ℓ + 1) → ι),
        (Fin.consEquiv (fun _ : Fin (ℓ + 2) => ι)) (z, w) = Fin.cons z w := fun _ _ => rfl
    simp only [hce, Fin.cons_zero, hlast, Fin.cons_succ, walkWeight_cons]
    -- both sides equal a common form summed over `v : Fin (ℓ+1) → ι`
    trans (∑ v : Fin (ℓ + 1) → ι,
        if v (Fin.last ℓ) = y then N 0 x (v 0) * walkWeight (Fin.tail N) v else 0)
    · -- left side = common
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h0 : ∀ z ∈ (Finset.univ : Finset ι), z ≠ v 0 →
          N 0 x z * (if v 0 = z ∧ v (Fin.last ℓ) = y then walkWeight (Fin.tail N) v else 0)
            = 0 := by
        intro z _ hz; rw [if_neg (by rintro ⟨h, _⟩; exact hz h.symm), mul_zero]
      rw [Finset.sum_eq_single_of_mem (v 0) (Finset.mem_univ _) h0]
      by_cases hd : v (Fin.last ℓ) = y <;> simp [hd]
    · -- right side = common
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h0 : ∀ z ∈ (Finset.univ : Finset ι), z ≠ x →
          (if z = x ∧ v (Fin.last ℓ) = y then N 0 z (v 0) * walkWeight (Fin.tail N) v else 0)
            = 0 := by
        intro z _ hz; rw [if_neg (by rintro ⟨h, _⟩; exact hz h)]
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) h0]
      by_cases hd : v (Fin.last ℓ) = y <;> simp [hd]

/-- **Trace as a sum over closed walks.** The trace of the ordered product `N 0 * … * N (ℓ-1)`
is the sum over closed walks `v : Fin (ℓ+1) → ι` (those with `v (last) = v 0`) of the
edge-product weight. -/
theorem trace_bigProd (ℓ : ℕ) (N : Fin ℓ → Matrix ι ι R) :
    Matrix.trace (bigProd N)
      = ∑ v : Fin (ℓ + 1) → ι, (if v (Fin.last ℓ) = v 0 then walkWeight N v else 0) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [bigProd_apply ℓ N]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have h0 : ∀ x ∈ (Finset.univ : Finset ι), x ≠ v 0 →
      (if v 0 = x ∧ v (Fin.last ℓ) = x then walkWeight N v else 0) = 0 := by
    intro x _ hx; rw [if_neg (by rintro ⟨h, _⟩; exact hx h.symm)]
  rw [Finset.sum_eq_single_of_mem (v 0) (Finset.mem_univ _) h0]
  by_cases hd : v (Fin.last ℓ) = v 0 <;> simp [hd]

end WalkSum

section MatrixCombinatorics

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The ordered matrix product around the orbit of `i`, going backwards along `σ`:
`M i * M (σ⁻¹ i) * M (σ⁻² i) * … * M (σ^{-(ℓ-1)} i)` where `ℓ = cyclePeriod σ i`. Its trace is the
per-orbit factor in the cycle-trace identity, and it is independent of the chosen representative up
to cyclic rotation. -/
noncomputable def matrixCycleProd (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) (i : Fin m) :
    Matrix ι ι R :=
  (((List.range (cyclePeriod σ i)).map (fun t => M ((σ⁻¹ ^ t) i)))).prod

/-- **Combinatorial core.** The multi-index sum `∑_p ∏_i M_i (p (σ i)) (p i)` factors over the
`σ`-orbits: the permutation forces `p` to be constant along each cycle, and the chain of matrix
entries around a cycle resums to the trace of the ordered matrix product. One factor per orbit
representative.

This is the heart of the tensor-trace ↔ trace-word identity. Proof roadmap (two steps):

* **Single orbit (telescoping).** For an orbit representative `r`, the local sum
  `∑ (q : orbit r → ι) ∏_{i ∈ orbit r} M i (q (σ i)) (q i)` telescopes to
  `Tr (matrixCycleProd σ M r)`: parametrizing `q` by `a t := q (σ^t r)` turns the product into
  `∏_t M_{σ^t r} (a_{t+1 mod ℓ}, a_t)`, and summing over `a ∈ ι^ℓ` collapses the matrix chain to a
  trace (cyclic invariance fixes the representative).

* **Orbit-partition assembly.** Reindex `p : Fin m → ι` along the `σ`-orbit partition as
  `∏ r ∈ orbitReps σ, (orbit r → ι)`, split `∏ i` as `∏ r, ∏_{i ∈ orbit r}`, and apply
  `Fintype.prod_sum` (a product of sums is a sum of products) to turn
  `∏_r (local sum)` into `∑_p ∏_i`. -/
theorem matrixSum_eq_prod_orbit (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) :
    ∑ p : Fin m → ι, ∏ i : Fin m, M i (p (σ i)) (p i)
      = ∏ i ∈ orbitReps σ, Matrix.trace (matrixCycleProd σ M i) := by
  sorry

end MatrixCombinatorics

/-! ## The cycle-trace identity -/

/-- The ordered operator product around the orbit of `i`, the endomorphism analogue of
`matrixCycleProd`: `A i * A (σ⁻¹ i) * … * A (σ^{-(ℓ-1)} i)`. -/
noncomputable def cycleOperator (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V)
    (i : Fin n) : Module.End k V :=
  (((List.range (cyclePeriod σ i)).map (fun t => A ((σ⁻¹ ^ t) i)))).prod

/-- The trace of the ordered operator product equals the trace of the ordered matrix product in the
chosen basis. -/
theorem trace_cycleOperator (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) (i : Fin n) :
    LinearMap.trace k V (cycleOperator k V n σ A i)
      = Matrix.trace (matrixCycleProd σ
          (fun j => LinearMap.toMatrix (chosenBasis k V) (chosenBasis k V) (A j)) i) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (chosenBasis k V)]
  congr 1
  rw [cycleOperator, matrixCycleProd]
  change LinearMap.toMatrixAlgEquiv (chosenBasis k V) (List.prod _) = _
  rw [map_list_prod, List.map_map]
  rfl

/-- **The tensor-trace ↔ trace-word (cycle-trace) identity.** The trace over the tensor factors of
the permuted tensor operator factors as a product over the `σ`-orbits, one *trace of the ordered
operator product around the cycle* per orbit:

`trace (permTensorOp σ A) = ∏_{orbit reps i} trace (A i · A (σ⁻¹ i) · … · A (σ^{-(ℓ-1)} i))`.

This is book step 4 of the Problem 5.24.2 hint. -/
theorem permTensorOp_trace_eq_prod_cycle (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    LinearMap.trace k _ (permTensorOp k V n σ A)
      = ∏ i ∈ orbitReps σ, LinearMap.trace k V (cycleOperator k V n σ A i) := by
  rw [permTensorOp_trace_eq_matrixSum, matrixSum_eq_prod_orbit]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [trace_cycleOperator]

end Etingof
