import EtingofRepresentationTheory.Chapter3.Introduction3_6

/-!
# The commutator span of a matrix algebra is the traceless matrices

This file exposes the standalone identity used inside the proof of Theorem 3.6.2(ii):

> First we prove that `[Mat_d(k), Mat_d(k)] = sl_d(k)`, the set of all matrices with trace 0.

Concretely, for a full matrix algebra `Matrix n n k` over a commutative ring `k`, the
commutator submodule `commutatorSubmodule k (Matrix n n k)` (the `k`-span of all `x*y - y*x`,
i.e. `[Mat_n(k), Mat_n(k)]`) equals the kernel of the matrix trace `Matrix.traceLinearMap`,
i.e. the traceless matrices `sl_n(k)`.

The forward inclusion is the cyclicity of the trace, `tr(xy) = tr(yx)`. The reverse
inclusion is Etingof's matrix-unit spanning argument:

* off-diagonal units are commutators, `E_{ij} = [E_{ii}, E_{ij}]` for `i ≠ j`;
* diagonal differences are commutators, `E_{ii} - E_{jj} = [E_{ij}, E_{ji}]`.

Writing a traceless matrix in the matrix-unit basis and correcting the diagonal against a
fixed reference index (using `tr M = 0`) exhibits it as a combination of these commutators.
The `n`-empty case (`d = 0`) is handled separately: the only matrix is `0`. The `d = 1` case
is subsumed by the general argument, where the reference index makes every diagonal
difference vanish and the sole traceless matrix is again `0`.
-/

namespace Etingof

open Matrix

/-- **Commutators span the traceless matrices.** For a full matrix algebra `Matrix n n k`
over a commutative ring `k`, the commutator submodule `[Mat_n(k), Mat_n(k)]` (the `k`-span
of all `x*y - y*x`) is exactly the kernel of the matrix trace, i.e. the traceless matrices
`sl_n(k)`. This is the standalone identity `[Mat_d(k), Mat_d(k)] = sl_d(k)` proved inside
Etingof Theorem 3.6.2(ii). -/
theorem commutatorSubmodule_matrix_eq_ker_trace
    (k : Type*) [CommRing k] (n : Type*) [Fintype n] [DecidableEq n] :
    commutatorSubmodule k (Matrix n n k) =
      LinearMap.ker (Matrix.traceLinearMap n k k) := by
  apply le_antisymm
  · -- Forward: every commutator is traceless, since `tr (x * y) = tr (y * x)`.
    rw [commutatorSubmodule, Submodule.span_le]
    rintro z ⟨x, y, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm, sub_self]
  · -- Reverse: a traceless matrix is a combination of commutators.
    intro M hM
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hM
    rcases isEmpty_or_nonempty n with hn | hn
    · -- No indices (`d = 0`): the only matrix is `0`.
      have hM0 : M = 0 := Subsingleton.elim _ _
      rw [hM0]; exact Submodule.zero_mem _
    · obtain ⟨i₀⟩ := hn
      -- Off-diagonal units are commutators: `E_{ij} = [E_{ii}, E_{ij}]` for `i ≠ j`.
      have hoff : ∀ i j : n, i ≠ j →
          Matrix.single i j (1 : k) ∈ commutatorSubmodule k (Matrix n n k) := by
        intro i j hij
        rw [commutatorSubmodule]
        apply Submodule.subset_span
        refine ⟨Matrix.single i i 1, Matrix.single i j 1, ?_⟩
        have p1 : Matrix.single i i (1 : k) * Matrix.single i j 1 = Matrix.single i j 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        have p2 : Matrix.single i j (1 : k) * Matrix.single i i 1 = 0 := by
          apply Matrix.single_mul_single_of_ne; exact hij.symm
        rw [p1, p2, sub_zero]
      -- Diagonal differences are commutators: `E_{ii} - E_{i₀i₀} = [E_{i,i₀}, E_{i₀,i}]`.
      have hdiag : ∀ i : n,
          Matrix.single i i (1 : k) - Matrix.single i₀ i₀ (1 : k)
            ∈ commutatorSubmodule k (Matrix n n k) := by
        intro i
        rw [commutatorSubmodule]
        apply Submodule.subset_span
        refine ⟨Matrix.single i i₀ 1, Matrix.single i₀ i 1, ?_⟩
        have q1 : Matrix.single i i₀ (1 : k) * Matrix.single i₀ i 1 = Matrix.single i i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        have q2 : Matrix.single i₀ i (1 : k) * Matrix.single i i₀ 1 = Matrix.single i₀ i₀ 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [q1, q2]
      -- The diagonal correction against the reference index sums to `0` since `tr M = 0`.
      have hcorr :
          (∑ i : n, ∑ j : n,
            (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0)) = 0 := by
        have hinner : ∀ i : n,
            (∑ j : n, (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0))
              = (M i i) • Matrix.single i₀ i₀ 1 := by
          intro i; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
        rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.sum_smul]
        have htr : (∑ i, M i i) = M.trace := rfl
        rw [htr, hM, zero_smul]
      -- Rewrite `M` as a sum of terms each visibly in `[Mat_n(k), Mat_n(k)]`.
      have key : M = ∑ i : n, ∑ j : n,
          (Matrix.single i j (M i j) -
            (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0)) := by
        simp_rw [Finset.sum_sub_distrib]
        rw [← Matrix.matrix_eq_sum_single, hcorr, sub_zero]
      rw [key]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases hp : i = j
      · -- Diagonal term: `E_{ii} · M_{ii} - M_{ii} • E_{i₀i₀} = M_{ii} • (E_{ii} - E_{i₀i₀})`.
        subst hp
        rw [if_pos rfl]
        have e1 : Matrix.single i i (M i i) = (M i i) • Matrix.single i i (1 : k) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [e1, ← smul_sub]
        exact Submodule.smul_mem _ _ (hdiag i)
      · -- Off-diagonal term: `E_{ij} · M_{ij} = M_{ij} • E_{ij}`.
        rw [if_neg hp, sub_zero]
        have e2 : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [e2]
        exact Submodule.smul_mem _ _ (hoff i j hp)

/-- The `Fin d` specialization of `commutatorSubmodule_matrix_eq_ker_trace`: the commutator
span `[Mat_d(k), Mat_d(k)]` equals the traceless matrices `sl_d(k)`, exactly as displayed in
the proof of Etingof Theorem 3.6.2(ii). -/
theorem commutatorSubmodule_matrix_fin_eq_ker_trace
    (k : Type*) [CommRing k] (d : ℕ) :
    commutatorSubmodule k (Matrix (Fin d) (Fin d) k) =
      LinearMap.ker (Matrix.traceLinearMap (Fin d) k k) :=
  commutatorSubmodule_matrix_eq_ker_trace k (Fin d)

end Etingof
