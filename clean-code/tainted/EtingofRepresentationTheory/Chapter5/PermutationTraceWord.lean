import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# The tensor-trace ↔ trace-word (cycle-trace) identity

This file develops book step 4 of the Problem 5.24.2 hint, self-contained in the Schur–Weyl
tensor framework of `Theorem5_18_4.lean`.

For a permutation `σ : Equiv.Perm (Fin n)` and endomorphisms `A : Fin n → Module.End k V`, the
permuted tensor operator is
`permTensorOp σ A := symGroupAction σ ∘ₗ PiTensorProduct.map A : End (V^⊗n)`,
i.e. the operator that applies `A i` on tensor factor `i` and then permutes the factors by `σ`.

The main result (`permTensorOp_trace_eq_prod_cycle`) is that its trace over the tensor factors
factors as a product over the `σ`-orbits of `Fin n`, one trace of the ordered operator product
around the cycle per orbit:

```
trace (permTensorOp σ A) = ∏_{orbits O of σ} trace (∏_{j around O} A j).
```

The proof has two independent parts:

* `permTensorOp_trace_eq_matrixSum`: reduce the tensor trace to a sum over
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
endpoints equal and summing recovers the trace as a sum over closed walks. This underlies the
single-orbit telescoping. -/

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

omit [Fintype ι] [DecidableEq ι] in
/-- On the cyclically-closed extension `Fin.snoc a (a 0)`, the value read at `t.succ` is the cyclic
successor value `a (t + 1)` (`t + 1` in `Fin (ℓ'+1)`, wrapping at the end). -/
lemma snoc_self_zero_succ {ℓ' : ℕ} (a : Fin (ℓ' + 1) → ι) (t : Fin (ℓ' + 1)) :
    (Fin.snoc a (a 0) : Fin (ℓ' + 2) → ι) t.succ = a (t + 1) := by
  rcases eq_or_ne t (Fin.last ℓ') with h | h
  · subst h
    rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last h
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    congr 1
    ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last s), Fin.val_castSucc, Fin.val_succ]

/-- **Trace as a cyclic walk-sum.** For a nonempty index set `Fin ℓ` (`NeZero ℓ`), the trace of the
ordered product `N 0 * … * N (ℓ-1)` is the sum over cyclic index assignments `a : Fin ℓ → ι` of the
product of entries `N t (a t) (a (t+1))`, with `t+1` the cyclic successor in `Fin ℓ`. This is the
"trace of a list product = closed-walk sum" identity in cyclic form. -/
theorem trace_bigProd_cyclic {ℓ : ℕ} [NeZero ℓ] (N : Fin ℓ → Matrix ι ι R) :
    Matrix.trace (bigProd N)
      = ∑ a : Fin ℓ → ι, ∏ t : Fin ℓ, N t (a t) (a (t + 1)) := by
  obtain ⟨ℓ', rfl⟩ : ∃ k, ℓ = k + 1 :=
    ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm⟩
  rw [trace_bigProd, ← Finset.sum_filter]
  refine (Finset.sum_bij' (fun a _ => Fin.snoc a (a 0)) (fun v _ t => v t.castSucc)
    ?_ ?_ ?_ ?_ ?_).symm
  · -- forward map lands in the closed-walk filter
    intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.snoc_last]
    conv_rhs => rw [show (0 : Fin (ℓ' + 2)) = Fin.castSucc (0 : Fin (ℓ' + 1)) from
      (Fin.castSucc_zero).symm, Fin.snoc_castSucc]
  · -- backward map lands in univ
    intro v _; exact Finset.mem_univ _
  · -- left inverse
    intro a _; funext t; rw [Fin.snoc_castSucc]
  · -- right inverse
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    funext i
    change (Fin.snoc (fun t => v t.castSucc) (v (Fin.castSucc 0)) : Fin (ℓ' + 2) → ι) i = v i
    rw [Fin.castSucc_zero, ← hv]
    exact congrFun (Fin.snoc_init_self v) i
  · -- summands agree
    intro a _
    unfold walkWeight
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [Fin.snoc_castSucc, snoc_self_zero_succ]

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

/-! ### Orbit-representative infrastructure

Each `σ`-orbit is tagged by its `≤`-minimal element, the *representative*. `repOf σ x` is the
representative of `x`'s orbit; it is constant along cycles, lands in `orbitReps σ`, and fixes the
elements of `orbitReps σ`. `fiberMap σ r` is the action of `σ` on the fiber (orbit) of `r`. -/

open scoped Classical in
/-- The representative of the `σ`-orbit of `x`: the `≤`-minimal element `SameCycle`-related
to `x`. -/
noncomputable def repOf (σ : Equiv.Perm (Fin m)) (x : Fin m) : Fin m :=
  (Finset.univ.filter (fun j => σ.SameCycle x j)).min'
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl σ x⟩⟩

lemma sameCycle_repOf (σ : Equiv.Perm (Fin m)) (x : Fin m) : σ.SameCycle x (repOf σ x) := by
  classical
  have h := Finset.min'_mem (Finset.univ.filter (fun j => σ.SameCycle x j))
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl σ x⟩⟩
  exact (Finset.mem_filter.mp h).2

lemma repOf_le (σ : Equiv.Perm (Fin m)) (x : Fin m) {j : Fin m} (h : σ.SameCycle x j) :
    repOf σ x ≤ j :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

lemma repOf_eq_of_sameCycle (σ : Equiv.Perm (Fin m)) {x y : Fin m} (h : σ.SameCycle x y) :
    repOf σ x = repOf σ y := by
  classical
  unfold repOf
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hj => h.symm.trans hj, fun hj => h.trans hj⟩

lemma mem_orbitReps_iff (σ : Equiv.Perm (Fin m)) {r : Fin m} :
    r ∈ orbitReps σ ↔ ∀ j, σ.SameCycle r j → r ≤ j := by
  simp [orbitReps]

lemma repOf_mem_orbitReps (σ : Equiv.Perm (Fin m)) (x : Fin m) : repOf σ x ∈ orbitReps σ := by
  rw [mem_orbitReps_iff]
  exact fun j hj => repOf_le σ x ((sameCycle_repOf σ x).trans hj)

lemma repOf_eq_self (σ : Equiv.Perm (Fin m)) {r : Fin m} (hr : r ∈ orbitReps σ) :
    repOf σ r = r := by
  rw [mem_orbitReps_iff] at hr
  exact le_antisymm (repOf_le σ r (Equiv.Perm.SameCycle.refl σ r)) (hr _ (sameCycle_repOf σ r))

lemma repOf_apply (σ : Equiv.Perm (Fin m)) (x : Fin m) : repOf σ (σ x) = repOf σ x :=
  repOf_eq_of_sameCycle σ ((Equiv.Perm.SameCycle.refl σ x).apply_left)

/-- The action of `σ` on the fiber (orbit) of a representative `r`. -/
def fiberMap (σ : Equiv.Perm (Fin m)) (r : Fin m) (x : {x : Fin m // repOf σ x = r}) :
    {x : Fin m // repOf σ x = r} :=
  ⟨σ x.1, by rw [repOf_apply]; exact x.2⟩

/-! ### Orbit period arithmetic

The single-orbit telescoping parametrizes the fiber of `r` by `t ↦ σ⁻¹^t r`, `t : Fin ℓ`,
`ℓ = cyclePeriod σ r`. The lemmas below supply the facts this parametrization needs: positivity of
the period, that `σ^ℓ` and `σ⁻¹^ℓ` fix `r`, and that `σ⁻¹` has the same minimal period at `r` as
`σ`. -/

/-- `r` is a periodic point of the finite permutation `σ`, so its cycle period is positive. -/
lemma cyclePeriod_pos (σ : Equiv.Perm (Fin m)) (i : Fin m) : 0 < cyclePeriod σ i :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts i)

/-- `σ ^ ℓ` fixes `r`, where `ℓ = cyclePeriod σ r` is its minimal period under `σ`. -/
lemma pow_cyclePeriod_apply (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    (σ ^ cyclePeriod σ r) r = r := by
  have h : (⇑σ)^[cyclePeriod σ r] r = r := Function.isPeriodicPt_minimalPeriod (⇑σ) r
  rwa [← Equiv.Perm.coe_pow] at h

/-- `σ⁻¹ ^ ℓ` also fixes `r`. -/
lemma inv_pow_cyclePeriod_apply (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    (σ⁻¹ ^ cyclePeriod σ r) r = r := by
  have h := pow_cyclePeriod_apply σ r
  rw [inv_pow]
  exact (Equiv.symm_apply_eq (σ ^ cyclePeriod σ r)).mpr h.symm

/-- The minimal period of `σ⁻¹` at `r` coincides with that of `σ`: the two have the same periodic
iterates at `r`. -/
lemma minimalPeriod_inv_coe (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    Function.minimalPeriod (⇑σ⁻¹) r = Function.minimalPeriod (⇑σ) r := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  have e : ∀ τ : Equiv.Perm (Fin m), Function.IsPeriodicPt (⇑τ) n r ↔ (τ ^ n) r = r := by
    intro τ
    change (⇑τ)^[n] r = r ↔ (τ ^ n) r = r
    rw [← Equiv.Perm.coe_pow]
  rw [e σ⁻¹, e σ, inv_pow]
  constructor
  · intro h; exact ((Equiv.symm_apply_eq (σ ^ n)).mp h).symm
  · intro h; exact (Equiv.symm_apply_eq (σ ^ n)).mpr h.symm

/-- In `Fin ℓ` (`ℓ > 0`), `0 - 1` has value `ℓ - 1`. -/
lemma val_zero_sub_one {ℓ : ℕ} [NeZero ℓ] : ((0 : Fin ℓ) - 1).val = ℓ - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 :=
    ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm⟩
  simp [zero_sub, Fin.coe_neg_one]

/-- The ordered orbit product `matrixCycleProd σ M r` is `bigProd` of the `Fin ℓ`-indexed family of
backward matrices `t ↦ M (σ⁻¹^t r)`. This rewrites the `List.range … |>.map` product used to define
`matrixCycleProd` into the `List.ofFn` form that `trace_bigProd_cyclic` consumes. -/
lemma matrixCycleProd_eq_bigProd (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) (r : Fin m) :
    matrixCycleProd σ M r
      = bigProd (fun t : Fin (cyclePeriod σ r) => M ((σ⁻¹ ^ (t : ℕ)) r)) := by
  rw [matrixCycleProd, bigProd]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- **Single-orbit telescoping.** On one `σ`-orbit (the fiber of a representative `r`), the local
multi-index sum resums to the trace of the ordered matrix product `matrixCycleProd σ M r`. The
fiber is parametrized backward by `t ↦ σ⁻¹^t r` (`t : Fin ℓ`, `ℓ = cyclePeriod σ r`); reindexing the
multi-index sum and product along this bijection, then shifting by one, turns the local sum into the
cyclic walk-sum `trace_bigProd_cyclic` computes. -/
theorem matrixSum_cycle_eq_trace (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R)
    {r : Fin m} (hr : r ∈ orbitReps σ) :
    ∑ q : {x : Fin m // repOf σ x = r} → ι,
        ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (q (fiberMap σ r x)) (q x)
      = Matrix.trace (matrixCycleProd σ M r) := by
  classical
  haveI : NeZero (cyclePeriod σ r) := ⟨(cyclePeriod_pos σ r).ne'⟩
  -- same-cycle witnesses for the backward orbit parametrization `t ↦ σ⁻¹^t r`
  have hsame : ∀ k : ℕ, σ.SameCycle ((σ⁻¹ ^ k) r) r := fun k =>
    ⟨(k : ℤ), by
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]⟩
  -- the orbit bijection `φ : Fin ℓ ≃ fiber r`
  let φf : Fin (cyclePeriod σ r) → {x : Fin m // repOf σ x = r} :=
    fun t => ⟨(σ⁻¹ ^ (t : ℕ)) r, by
      rw [repOf_eq_of_sameCycle σ (hsame (t : ℕ)), repOf_eq_self σ hr]⟩
  have hφf_inj : Function.Injective φf := by
    intro t1 t2 h
    have h1 : (σ⁻¹ ^ (t1 : ℕ)) r = (σ⁻¹ ^ (t2 : ℕ)) r := Subtype.ext_iff.mp h
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑σ⁻¹) (x := r)
    rw [minimalPeriod_inv_coe σ r] at hinj
    exact Fin.ext (hinj (Set.mem_Iio.mpr t1.isLt) (Set.mem_Iio.mpr t2.isLt)
      (by simpa only [Equiv.Perm.coe_pow] using h1))
  have hφf_surj : Function.Surjective φf := by
    rintro ⟨x, hx⟩
    have hsc : σ.SameCycle x r := by have h := sameCycle_repOf σ x; rwa [hx] at h
    have hsc' : (σ⁻¹).SameCycle r x := by rw [Equiv.Perm.sameCycle_inv]; exact hsc.symm
    obtain ⟨i, _, hi⟩ := hsc'.exists_pow_eq'
    refine ⟨⟨i % cyclePeriod σ r, Nat.mod_lt _ (cyclePeriod_pos σ r)⟩, ?_⟩
    apply Subtype.ext
    change (σ⁻¹ ^ (i % cyclePeriod σ r)) r = x
    have hmod : (⇑σ⁻¹)^[i % Function.minimalPeriod (⇑σ⁻¹) r] r = (⇑σ⁻¹)^[i] r :=
      Function.iterate_mod_minimalPeriod_eq
    rw [minimalPeriod_inv_coe σ r] at hmod
    calc (σ⁻¹ ^ (i % cyclePeriod σ r)) r
        = (⇑σ⁻¹)^[i % cyclePeriod σ r] r := by rw [Equiv.Perm.coe_pow]
      _ = (⇑σ⁻¹)^[i] r := hmod
      _ = (σ⁻¹ ^ i) r := by rw [Equiv.Perm.coe_pow]
      _ = x := hi
  let φ : Fin (cyclePeriod σ r) ≃ {x : Fin m // repOf σ x = r} :=
    Equiv.ofBijective φf ⟨hφf_inj, hφf_surj⟩
  have hφ : ∀ t, (φ t).1 = (σ⁻¹ ^ (t : ℕ)) r := fun _ => rfl
  -- the backward telescoping step: `σ · σ⁻¹^(k+1) = σ⁻¹^k`
  have hstep : ∀ k : ℕ, σ ((σ⁻¹ ^ (k + 1)) r) = (σ⁻¹ ^ k) r := by
    intro k; rw [pow_succ', Equiv.Perm.mul_apply]; simp
  -- the shift relation: applying `σ` on the fiber is `φ` of the predecessor index
  have hfib : ∀ t, fiberMap σ r (φ t) = φ (t - 1) := by
    intro t
    apply Subtype.ext
    change σ ((φ t).1) = (φ (t - 1)).1
    rw [hφ, hφ]
    by_cases ht : t = 0
    · subst ht
      simp only [Fin.val_zero, pow_zero, Equiv.Perm.one_apply, val_zero_sub_one]
      have h := hstep (cyclePeriod σ r - 1)
      rwa [Nat.sub_add_cancel (cyclePeriod_pos σ r), inv_pow_cyclePeriod_apply] at h
    · rw [Fin.val_sub_one_of_ne_zero ht]
      have hv : t.val ≠ 0 := by rwa [Ne, Fin.val_eq_zero_iff]
      have h := hstep (t.val - 1)
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h
  -- the sum-level shift `a ↦ a ∘ (· - 1)`
  let shift : (Fin (cyclePeriod σ r) → ι) ≃ (Fin (cyclePeriod σ r) → ι) :=
    { toFun := fun a s => a (s - 1)
      invFun := fun a s => a (s + 1)
      left_inv := fun a => by funext s; simp
      right_inv := fun a => by funext s; simp }
  -- the abbreviation `E` for the arrow reindexing `a ↦ a ∘ φ.symm`
  set E : (Fin (cyclePeriod σ r) → ι) ≃ ({x : Fin m // repOf σ x = r} → ι) :=
    Equiv.arrowCongr φ (Equiv.refl ι) with hE
  calc
    (∑ q : {x : Fin m // repOf σ x = r} → ι,
        ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (q (fiberMap σ r x)) (q x))
        = ∑ a : Fin (cyclePeriod σ r) → ι,
            ∏ t : Fin (cyclePeriod σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a (t - 1)) (a t) := by
          rw [← Equiv.sum_comp E (fun q : {x : Fin m // repOf σ x = r} → ι =>
            ∏ x, M x.1 (q (fiberMap σ r x)) (q x))]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [← Equiv.prod_comp φ (fun x => M x.1 (E a (fiberMap σ r x)) (E a x))]
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [hfib]
          simp only [hE, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
            Equiv.symm_apply_apply]
          rw [hφ]
      _ = ∑ a : Fin (cyclePeriod σ r) → ι,
            ∏ t : Fin (cyclePeriod σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a t) (a (t + 1)) := by
          rw [← Equiv.sum_comp shift (fun a : Fin (cyclePeriod σ r) → ι =>
            ∏ t : Fin (cyclePeriod σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a t) (a (t + 1)))]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.prod_congr rfl (fun t _ => ?_)
          simp only [shift, Equiv.coe_fn_mk, add_sub_cancel_right]
      _ = Matrix.trace (bigProd (fun t : Fin (cyclePeriod σ r) => M ((σ⁻¹ ^ (t : ℕ)) r))) :=
          (trace_bigProd_cyclic _).symm
      _ = Matrix.trace (matrixCycleProd σ M r) := by rw [matrixCycleProd_eq_bigProd]

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

* **Orbit partition.** Reindex `p : Fin m → ι` along the `σ`-orbit partition as
  `∏ r ∈ orbitReps σ, (orbit r → ι)`, split `∏ i` as `∏ r, ∏_{i ∈ orbit r}`, and apply
  `Fintype.prod_sum` (a product of sums is a sum of products) to turn
  `∏_r (local sum)` into `∑_p ∏_i`. -/
theorem matrixSum_eq_prod_orbit (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) :
    ∑ p : Fin m → ι, ∏ i : Fin m, M i (p (σ i)) (p i)
      = ∏ i ∈ orbitReps σ, Matrix.trace (matrixCycleProd σ M i) := by
  classical
  -- The reindexing between colorings `p` and orbitwise colorings `g`.
  let E : (Fin m → ι) ≃ (∀ r : Fin m, {x : Fin m // repOf σ x = r} → ι) :=
    { toFun := fun p r x => p x.1
      invFun := fun g i => g (repOf σ i) ⟨i, rfl⟩
      left_inv := fun p => rfl
      right_inv := fun g => by funext r x; obtain ⟨i, rfl⟩ := x; rfl }
  -- The product over `Fin m` splits as a product over orbit fibers.
  have hpart : ∀ h : Fin m → R,
      ∏ i : Fin m, h i = ∏ r : Fin m, ∏ x : {x : Fin m // repOf σ x = r}, h x.1 := by
    intro h
    rw [← Equiv.prod_comp (Equiv.sigmaFiberEquiv (repOf σ)) h, Fintype.prod_sigma]
    rfl
  calc
    ∑ p : Fin m → ι, ∏ i : Fin m, M i (p (σ i)) (p i)
        = ∑ p : Fin m → ι, ∏ r : Fin m,
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (p (σ x.1)) (p x.1) := by
          exact Finset.sum_congr rfl (fun p _ => hpart (fun i => M i (p (σ i)) (p i)))
      _ = ∑ g : (∀ r : Fin m, {x : Fin m // repOf σ x = r} → ι), ∏ r : Fin m,
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (g r (fiberMap σ r x)) (g r x) := by
          rw [← Equiv.sum_comp E (fun g => ∏ r : Fin m,
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (g r (fiberMap σ r x)) (g r x))]
          exact Finset.sum_congr rfl (fun p _ => rfl)
      _ = ∏ r : Fin m, ∑ q : {x : Fin m // repOf σ x = r} → ι,
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (q (fiberMap σ r x)) (q x) :=
          (Fintype.prod_sum (fun (r : Fin m) (q : {x : Fin m // repOf σ x = r} → ι) =>
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (q (fiberMap σ r x)) (q x))).symm
      _ = ∏ r ∈ orbitReps σ, ∑ q : {x : Fin m // repOf σ x = r} → ι,
            ∏ x : {x : Fin m // repOf σ x = r}, M x.1 (q (fiberMap σ r x)) (q x) := by
          refine (Finset.prod_subset (Finset.subset_univ _) (fun r _ hr => ?_)).symm
          have hempty : IsEmpty {x : Fin m // repOf σ x = r} :=
            ⟨fun x => hr (x.2 ▸ repOf_mem_orbitReps σ x.1)⟩
          simp [Finset.prod_of_isEmpty]
      _ = ∏ r ∈ orbitReps σ, Matrix.trace (matrixCycleProd σ M r) :=
          Finset.prod_congr rfl (fun r hr => matrixSum_cycle_eq_trace σ M hr)

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
the permuted tensor operator factors as a product over the `σ`-orbits, one trace of the ordered
operator product around the cycle per orbit:

`trace (permTensorOp σ A) = ∏_{orbit reps i} trace (A i · A (σ⁻¹ i) · … · A (σ^{-(ℓ-1)} i))`.

This is book step 4 of the Problem 5.24.2 hint. -/
theorem permTensorOp_trace_eq_prod_cycle (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    LinearMap.trace k _ (permTensorOp k V n σ A)
      = ∏ i ∈ orbitReps σ, LinearMap.trace k V (cycleOperator k V n σ A i) := by
  rw [permTensorOp_trace_eq_matrixSum, matrixSum_eq_prod_orbit]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [trace_cycleOperator]

end Etingof
