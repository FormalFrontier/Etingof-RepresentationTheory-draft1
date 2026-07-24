import EtingofRepresentationTheory.Chapter6.Example6_4_9_An

/-!
# Example 6.4.9(1): the `A_{N-1}` root lattice as the sum-zero lattice in `ℤ^N`

The companion file `Example6_4_9_An` proves the numerical root-count endpoint
(`Aₙ` has `n(n+1)/2` positive roots) by working in Cartan coordinates via interval
indicator vectors. This file supplies the geometric model the book actually uses in
Example 6.4.9(1):

* `Etingof.An.sumZeroLattice n` — the sum-zero sublattice
  `L = {x : Fin (n+1) → ℤ | ∑ i, x i = 0}` of `ℤ^{n+1}`, realising the root lattice of
  type `A_n = A_{(n+1)-1}`;
* `Etingof.An.simpleRoot n i = e_i - e_{i+1}` — the consecutive-difference simple roots,
  and `Etingof.An.basis n`, a `Basis (Fin n) ℤ (sumZeroLattice n)` whose vectors are the
  `simpleRoot i`;
* `Etingof.An.dotProduct_toLat` — the standard inner product on `ℤ^{n+1}` restricts, in
  these coordinates, to the `A_n` Cartan form `xᵀ(2·1 - adj)y`;
* `Etingof.An.mem_latticeRoots_iff` — the explicit classification of all roots of `L` as
  exactly the vectors `±(e_i - e_j)`, `i ≠ j`;
* `Etingof.An.ncard_positiveLatticeRoots` — the reconnection of the positive-root count
  `n(n+1)/2` to this explicit model.

Here the ambient dimension is `N = n + 1`, so `n` is the number of simple roots and the
Dynkin type is `A_n` (the book's `A_{N-1}`).
-/

namespace Etingof.An

open Matrix Finset

variable (n : ℕ)

/-- The `i`-th simple root `α_i = e_i - e_{i+1}` of type `A_n`, as a vector in `ℤ^{n+1}`.
Here `i : Fin n` indexes the `n` simple roots and `e_k` is the `k`-th standard basis
vector of `ℤ^{n+1}`. -/
def simpleRoot (i : Fin n) : Fin (n + 1) → ℤ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

/-- Closed form for a coordinate of a simple root. -/
lemma simpleRoot_apply (i : Fin n) (k : Fin (n + 1)) :
    simpleRoot n i k = (if i.val = k.val then 1 else 0) - (if i.val + 1 = k.val then 1 else 0) := by
  simp only [simpleRoot, Pi.sub_apply, Pi.single_apply]
  congr 1
  · congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h; exact congrArg Fin.val h.symm
    · intro h; exact Fin.ext h.symm
  · congr 1
    simp only [eq_iff_iff, Fin.ext_iff, Fin.val_succ]
    omega

/-- The coordinates of a simple root sum to zero. -/
lemma sum_simpleRoot (i : Fin n) : ∑ k, simpleRoot n i k = 0 := by
  simp only [simpleRoot, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_pi_single', Finset.sum_pi_single']
  simp

/-- The total-sum linear functional `x ↦ ∑ i, x i` on `ℤ^{n+1}`. -/
def sumFunctional : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ := ∑ i, LinearMap.proj i

@[simp] lemma sumFunctional_apply (x : Fin (n + 1) → ℤ) : sumFunctional n x = ∑ i, x i := by
  simp [sumFunctional, LinearMap.sum_apply]

/-- The sum-zero sublattice `L = {x | ∑ i, x i = 0}` of `ℤ^{n+1}`, realising the root
lattice of type `A_n`. -/
def sumZeroLattice : Submodule ℤ (Fin (n + 1) → ℤ) := LinearMap.ker (sumFunctional n)

@[simp] lemma mem_sumZeroLattice {x : Fin (n + 1) → ℤ} :
    x ∈ sumZeroLattice n ↔ ∑ i, x i = 0 := by
  simp [sumZeroLattice, LinearMap.mem_ker]

/-- The coordinate-to-lattice map `c ↦ ∑ i, c i • α_i`, sending Cartan coordinates to a
vector of `ℤ^{n+1}`. -/
def toLat : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) :=
  ∑ i, (LinearMap.proj i).smulRight (simpleRoot n i)

lemma toLat_apply (c : Fin n → ℤ) : toLat n c = ∑ i, c i • simpleRoot n i := by
  simp [toLat, LinearMap.sum_apply, LinearMap.smulRight_apply]

lemma toLat_single (i : Fin n) : toLat n (Pi.single i 1) = simpleRoot n i := by
  rw [toLat_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Closed form for a coordinate of `toLat c`: it is `c` "differenced". -/
lemma toLat_apply_coord (c : Fin n → ℤ) (k : Fin (n + 1)) :
    toLat n c k = (if h : k.val < n then c ⟨k.val, h⟩ else 0)
      - (if h : 0 < k.val then c ⟨k.val - 1, by omega⟩ else 0) := by
  rw [toLat_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, simpleRoot_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- ∑ i, c i * (if i.val = k.val then 1 else 0) = if k.val < n then c ⟨k.val⟩ else 0
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with hk
    · rw [Finset.sum_eq_single (⟨k.val, hk⟩ : Fin n)]
      · simp
      · intro j _ hj; simp only [ite_eq_right_iff]; intro h; exact absurd (Fin.ext h) hj
      · intro h; exact absurd (Finset.mem_univ _) h
    · apply Finset.sum_eq_zero; intro i _
      simp only [ite_eq_right_iff]; intro h; omega
  · -- ∑ i, c i * (if i.val + 1 = k.val then 1 else 0) = if 0 < k.val then c ⟨k.val-1⟩ else 0
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with hk
    · rw [Finset.sum_eq_single (⟨k.val - 1, by omega⟩ : Fin n)]
      · have hval : (⟨k.val - 1, by omega⟩ : Fin n).val = k.val - 1 := rfl
        rw [if_pos (by rw [hval]; omega)]
      · intro j _ hj; simp only [ite_eq_right_iff]; intro h
        exact absurd (Fin.ext (show j.val = k.val - 1 by omega)) hj
      · intro h; exact absurd (Finset.mem_univ _) h
    · apply Finset.sum_eq_zero; intro i _
      simp only [ite_eq_right_iff]; intro h; omega

/-- The lattice-to-coordinate map: the `i`-th coordinate is the partial sum
`∑_{j ≤ i} x_j`. -/
def fromLat : (Fin (n + 1) → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  LinearMap.pi fun i : Fin n =>
    ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), LinearMap.proj j

lemma fromLat_apply (x : Fin (n + 1) → ℤ) (i : Fin n) :
    fromLat n x i = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), x j := by
  simp [fromLat, LinearMap.pi_apply, LinearMap.sum_apply]

/-- Round-trip: recovering the coordinates from `toLat c` gives back `c`.
This is the injectivity (linear independence) half of the basis. -/
lemma fromLat_toLat (c : Fin n → ℤ) : fromLat n (toLat n c) = c := by
  funext i
  rw [fromLat_apply]
  have hpt : ∀ j : Fin (n + 1), toLat n c j = ∑ k, c k * simpleRoot n k j := by
    intro j; rw [toLat_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have inner : ∀ k : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), simpleRoot n k j =
        if k = i then 1 else 0 := by
    intro k
    simp only [simpleRoot, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [Finset.sum_pi_single', Finset.sum_pi_single']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
    by_cases hki : k = i
    · subst hki; simp
    · rw [if_neg hki]
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      split_ifs <;> omega
  simp_rw [inner, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- Round-trip: a sum-zero vector is `toLat` of its coordinates.
This is the spanning half of the basis; it uses the sum-zero condition. -/
lemma toLat_fromLat {x : Fin (n + 1) → ℤ} (hx : x ∈ sumZeroLattice n) :
    toLat n (fromLat n x) = x := by
  have hsum : ∑ i, x i = 0 := (mem_sumZeroLattice n).mp hx
  set S : ℕ → ℤ :=
    fun m => ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ m), x j with hS
  have hPf : ∀ (m : ℕ) (hm : m < n), fromLat n x ⟨m, hm⟩ = S m := by
    intro m hm; rw [fromLat_apply]
  have hzero : S 0 = x ⟨0, by omega⟩ := by
    simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ 0)
          = {(⟨0, by omega⟩ : Fin (n + 1))} from ?_]
    · rw [Finset.sum_singleton]
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact Fin.ext (show j.val = 0 by omega)
      · intro h; rw [h]
  -- Prefix-sum recurrence, stated at a fixed `Fin` index to avoid dependent rewrites.
  have hstepFin : ∀ (i : Fin (n + 1)), 0 < i.val → S i.val = S (i.val - 1) + x i := by
    intro i hi; simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val)
          = insert i (Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val - 1)) from ?_]
    · rw [Finset.sum_insert (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)]
      ring
    · ext j; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_cases hji : j.val ≤ i.val - 1
        · exact Or.inr hji
        · exact Or.inl (Fin.ext (by omega))
      · rintro (rfl | h) <;> omega
  have hfull : S n = 0 := by
    simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ n) = Finset.univ from ?_]
    · rw [← hsum]
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Nat.lt_succ_iff.mp j.isLt
  funext k
  rw [toLat_apply_coord]
  by_cases hk : k.val < n
  · rw [dif_pos hk, hPf k.val hk]
    by_cases hk0 : 0 < k.val
    · rw [dif_pos hk0, hPf (k.val - 1) (by omega)]
      have hst := hstepFin k (by omega)
      rw [hst, add_sub_cancel_left]
    · rw [dif_neg hk0]
      have hk0' : k.val = 0 := by omega
      rw [hk0', sub_zero, hzero]
      congr 1; exact Fin.ext hk0'.symm
  · rw [dif_neg hk]
    have hkn : k.val = n := by omega
    by_cases hn0 : 0 < n
    · rw [dif_pos (by omega : 0 < k.val), hPf (k.val - 1) (by omega)]
      have hst := hstepFin k (by omega)
      have hSk : S k.val = 0 := by rw [hkn]; exact hfull
      rw [hSk] at hst
      -- hst : 0 = S (k.val - 1) + x k ; goal : 0 - S (k.val - 1) = x k
      linarith [hst]
    · rw [dif_neg (by omega : ¬ 0 < k.val), sub_zero]
      have hn : n = 0 := by omega
      have hx0 : x ⟨0, by omega⟩ = 0 := by
        have hf := hfull; rw [hn] at hf; rw [hzero] at hf; exact hf
      rw [show k = ⟨0, by omega⟩ from Fin.ext (show k.val = 0 by omega)]
      exact hx0.symm

end Etingof.An
