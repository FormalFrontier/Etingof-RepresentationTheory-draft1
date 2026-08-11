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

set_option backward.isDefEq.respectTransparency false

namespace Etingof.An

open Matrix Finset Module

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

/-- `toLat`, corestricted to the sum-zero lattice it lands in. -/
def toLatL : (Fin n → ℤ) →ₗ[ℤ] sumZeroLattice n :=
  LinearMap.codRestrict (sumZeroLattice n) (toLat n) fun c => by
    rw [mem_sumZeroLattice, toLat_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_simpleRoot, mul_zero, Finset.sum_const_zero]

@[simp] lemma coe_toLatL (c : Fin n → ℤ) : (toLatL n c : Fin (n + 1) → ℤ) = toLat n c := rfl

/-- The coordinates `↔` sum-zero-lattice linear equivalence. The forward map sends a
Cartan coordinate vector `c` to `∑ i, c i • α_i`; the inverse takes prefix sums. -/
def latticeEquiv : (Fin n → ℤ) ≃ₗ[ℤ] sumZeroLattice n :=
  LinearEquiv.ofLinear (toLatL n) (fromLat n ∘ₗ (sumZeroLattice n).subtype)
    (by
      refine LinearMap.ext fun y => Subtype.ext ?_
      change toLat n (fromLat n y.val) = y.val
      exact toLat_fromLat n y.2)
    (by
      refine LinearMap.ext fun c => ?_
      change fromLat n (toLat n c) = c
      exact fromLat_toLat n c)

@[simp] lemma latticeEquiv_apply (c : Fin n → ℤ) :
    (latticeEquiv n c : Fin (n + 1) → ℤ) = toLat n c := rfl

/-- The consecutive-difference simple roots `α_i = e_i - e_{i+1}` form a basis of the
sum-zero lattice `L` of type `A_n`. -/
noncomputable def basis : Basis (Fin n) ℤ (sumZeroLattice n) :=
  (Pi.basisFun ℤ (Fin n)).map (latticeEquiv n)

/-- The `i`-th basis vector is the simple root `α_i = e_i - e_{i+1}`. -/
@[simp] lemma coe_basis (i : Fin n) : (basis n i : Fin (n + 1) → ℤ) = simpleRoot n i := by
  rw [basis, Basis.map_apply, Pi.basisFun_apply, latticeEquiv_apply, toLat_single]

/-- Gram matrix of the simple roots: the standard inner product takes the same values on
the `α_i` as the `A_n` Cartan form `B` (namely `(α_i,α_i) = 2`, `(α_i,α_j) = -1` for
adjacent `i, j`, and `0` otherwise). This is the book's isometry statement. -/
lemma dotProduct_simpleRoot (hn : 1 ≤ n) (i j : Fin n) :
    dotProduct (simpleRoot n i) (simpleRoot n j)
      = (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - (Etingof.DynkinType.A n hn).adj) i j := by
  rw [show simpleRoot n j = Pi.single j.castSucc 1 - Pi.single j.succ 1 from rfl,
    dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  simp only [simpleRoot_apply, Fin.val_castSucc, Fin.val_succ,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Etingof.DynkinType.adj]
  split_ifs <;> simp_all [Fin.ext_iff] ; omega

/-- Isometry: the standard inner product on `ℤ^{n+1}`, restricted to the sum-zero lattice
and read in the simple-root coordinates, is the `A_n` Cartan form `xᵀ(2·1 - adj)y`. -/
lemma dotProduct_toLat (hn : 1 ≤ n) (c d : Fin n → ℤ) :
    dotProduct (toLat n c) (toLat n d)
      = dotProduct c ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
          (Etingof.DynkinType.A n hn).adj).mulVec d) := by
  rw [toLat_apply, toLat_apply, sum_dotProduct]
  simp only [smul_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_simpleRoot n hn]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The roots of the sum-zero lattice `L`: nonzero elements of squared length `2` for the
standard inner product (equivalently, by `dotProduct_toLat`, roots of the `A_n` Cartan
form). -/
def latticeRoots : Set (Fin (n + 1) → ℤ) :=
  {x | x ∈ sumZeroLattice n ∧ x ≠ 0 ∧ dotProduct x x = 2}

/-- **Explicit classification of the roots.** The roots of the type-`A_n` sum-zero lattice
are exactly the vectors `±(e_i - e_j)` with `i ≠ j`. -/
theorem mem_latticeRoots_iff (x : Fin (n + 1) → ℤ) :
    x ∈ latticeRoots n ↔
      ∃ i j : Fin (n + 1), i ≠ j ∧ x = Pi.single i 1 - Pi.single j 1 := by
  constructor
  · rintro ⟨hmem, _, hq⟩
    have hsum : ∑ k, x k = 0 := (mem_sumZeroLattice n).mp hmem
    have hqq : ∑ k, x k ^ 2 = 2 := by rw [← hq]; simp [dotProduct, pow_two]
    -- every coordinate lies in `{-1, 0, 1}`
    have hb2 : ∀ k, x k ^ 2 ≤ 2 := fun k =>
      hqq ▸ Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (mem_univ k)
    have hpm : ∀ k, x k = -1 ∨ x k = 0 ∨ x k = 1 := by
      intro k
      have hb := hb2 k
      have hlo : -1 ≤ x k := by
        by_contra h; push Not at h
        have hle : x k ≤ -2 := by omega
        nlinarith [hb, sq_nonneg (x k + 2)]
      have hhi : x k ≤ 1 := by
        by_contra h; push Not at h
        have hge : 2 ≤ x k := by omega
        nlinarith [hb, sq_nonneg (x k - 2)]
      interval_cases (x k) <;> tauto
    -- the support has exactly two elements
    have hsq : ∀ k, x k ^ 2 = if x k ≠ 0 then 1 else 0 := by
      intro k; rcases hpm k with h | h | h <;> simp [h]
    have hcard : (univ.filter (fun k => x k ≠ 0)).card = 2 := by
      have h := hqq
      rw [Finset.sum_congr rfl (fun k _ => hsq k), Finset.sum_boole] at h
      exact_mod_cast h
    obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hcard
    -- coordinates off `{i, j}` vanish; the two on `{i, j}` are `±1`
    have hzero : ∀ k, k ≠ i → k ≠ j → x k = 0 := by
      intro k hki hkj
      by_contra h
      have hmemk : k ∈ univ.filter (fun k => x k ≠ 0) := Finset.mem_filter.mpr ⟨mem_univ k, h⟩
      rw [hT] at hmemk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemk
      tauto
    have hxi : x i ≠ 0 := by
      have : i ∈ univ.filter (fun k => x k ≠ 0) := by rw [hT]; simp
      exact (Finset.mem_filter.mp this).2
    have hxj : x j ≠ 0 := by
      have : j ∈ univ.filter (fun k => x k ≠ 0) := by rw [hT]; simp
      exact (Finset.mem_filter.mp this).2
    have hsij : x i + x j = 0 := by
      have hsupp : ∑ k ∈ univ.filter (fun k => x k ≠ 0), x k = ∑ k, x k :=
        Finset.sum_filter_ne_zero univ
      rw [hT, Finset.sum_pair hij, hsum] at hsupp
      exact hsupp
    -- a reusable builder: two opposite `±1` coordinates spell out `e_p - e_q`
    have key : ∀ (p q : Fin (n + 1)), x p = 1 → x q = -1 → p ≠ q →
        (∀ k, k ≠ p → k ≠ q → x k = 0) → x = Pi.single p 1 - Pi.single q 1 := by
      intro p q hp hq hpq hz
      funext k
      by_cases hkp : k = p
      · subst hkp
        rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpq, hp, sub_zero]
      · by_cases hkq : k = q
        · subst hkq
          rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hpq), Pi.single_eq_same, hq, zero_sub]
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hkp, Pi.single_eq_of_ne hkq, hz k hkp hkq, sub_zero]
    have hxi' : x i = -1 ∨ x i = 1 := by
      rcases hpm i with h | h | h; exacts [Or.inl h, absurd h hxi, Or.inr h]
    rcases hxi' with hi1 | hi1
    · have hj1 : x j = 1 := by omega
      exact ⟨j, i, hij.symm, key j i hj1 hi1 hij.symm (fun k hkj hki => hzero k hki hkj)⟩
    · have hj1 : x j = -1 := by omega
      exact ⟨i, j, hij, key i j hi1 hj1 hij hzero⟩
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sumZeroLattice]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [Finset.sum_pi_single', Finset.sum_pi_single']
      simp
    · intro h
      have hi := congr_fun h i
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        sub_zero, Pi.zero_apply] at hi
      exact one_ne_zero hi
    · rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Pi.single_eq_of_ne (Ne.symm hij)]
      ring

/-- Root-notion reconnection: a coordinate vector `c` is a root of the `A_n` Cartan form
(the abstract `Etingof.IsRoot`) iff its image `toLat c` is a root of the explicit sum-zero
lattice. Composed with `mem_latticeRoots_iff` this identifies the Cartan-form roots with the
`±(e_i - e_j)`. -/
theorem isRoot_iff_toLat_mem (hn : 1 ≤ n) (c : Fin n → ℤ) :
    Etingof.IsRoot n (Etingof.DynkinType.A n hn).adj c ↔ toLat n c ∈ latticeRoots n := by
  unfold Etingof.IsRoot latticeRoots
  simp only [Set.mem_setOf_eq]
  rw [dotProduct_toLat n hn]
  constructor
  · rintro ⟨hne, hq⟩
    exact ⟨(toLatL n c).2, fun h => hne (by rw [← fromLat_toLat n c, h, map_zero]), hq⟩
  · rintro ⟨_, hne, hq⟩
    exact ⟨fun h => hne (by rw [h, map_zero]), hq⟩

/-- The positive roots of the explicit `A_n` lattice model: the `e_i - e_j` with `i < j`. -/
def positiveLatticeRoots : Set (Fin (n + 1) → ℤ) :=
  {x | ∃ i j : Fin (n + 1), i < j ∧ x = Pi.single i 1 - Pi.single j 1}

/-- The difference map `(i, j) ↦ e_i - e_j` is injective. -/
private lemma diff_injOn :
    Set.InjOn (fun p : Fin (n + 1) × Fin (n + 1) =>
        (Pi.single p.1 1 - Pi.single p.2 1 : Fin (n + 1) → ℤ))
      {p | p.1 < p.2} := by
  -- The value `+1` occurs exactly at the first index, `-1` exactly at the second.
  have hval1 : ∀ (a b k : Fin (n + 1)), a ≠ b →
      ((Pi.single a 1 - Pi.single b 1 : Fin (n + 1) → ℤ) k = 1 ↔ k = a) := by
    intro a b k hab
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
    constructor
    · intro h; by_contra hka; rw [if_neg hka] at h; split_ifs at h <;> omega
    · intro h; subst h; rw [if_pos rfl, if_neg hab, sub_zero]
  have hvaln : ∀ (a b k : Fin (n + 1)), a ≠ b →
      ((Pi.single a 1 - Pi.single b 1 : Fin (n + 1) → ℤ) k = -1 ↔ k = b) := by
    intro a b k hab
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
    constructor
    · intro h; by_contra hkb; rw [if_neg hkb] at h; split_ifs at h <;> omega
    · intro h; subst h; rw [if_neg (Ne.symm hab), if_pos rfl, zero_sub]
  rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have hne₁ : i₁ ≠ j₁ := ne_of_lt h₁
  have hne₂ : i₂ ≠ j₂ := ne_of_lt h₂
  have hci : (Pi.single i₁ 1 - Pi.single j₁ 1 : Fin (n + 1) → ℤ) i₁
      = (Pi.single i₂ 1 - Pi.single j₂ 1 : Fin (n + 1) → ℤ) i₁ := congr_fun heq i₁
  have hcj : (Pi.single i₁ 1 - Pi.single j₁ 1 : Fin (n + 1) → ℤ) j₁
      = (Pi.single i₂ 1 - Pi.single j₂ 1 : Fin (n + 1) → ℤ) j₁ := congr_fun heq j₁
  rw [(hval1 i₁ j₁ i₁ hne₁).mpr rfl] at hci
  rw [(hvaln i₁ j₁ j₁ hne₁).mpr rfl] at hcj
  exact Prod.ext ((hval1 i₂ j₂ i₁ hne₂).mp hci.symm) ((hvaln i₂ j₂ j₁ hne₂).mp hcj.symm)

/-- Count of strictly-ordered index pairs. -/
private lemma card_strictPairs :
    (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).card = n * (n + 1) / 2 := by
  have hD : (univ : Finset (Fin (n + 1))).offDiag.card = n * (n + 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.succ_mul,
      Nat.add_sub_cancel]
  have hAB : (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).card
      = (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [mem_filter, mem_univ, true_and] at *; exact hp
    · intro p₁ h₁ p₂ h₂ he; simp only [Prod.mk.injEq] at he; exact Prod.ext he.2 he.1
    · intro p hp; simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simp [hp], by simp⟩
  have hunion : univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
        ∪ univ.filter (fun p => p.2 < p.1) = (univ : Finset (Fin (n + 1))).offDiag := by
    ext p; simp only [mem_union, mem_filter, mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
    · intro hne; rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2))
      (univ.filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]; intro p h₁ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    exact absurd h₁ (not_lt.mpr (le_of_lt h₂))
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, hD, ← hAB] at hcu
  omega

/-- **Reconnection of the positive-root count.** The explicit lattice model has exactly
`n(n+1)/2` positive roots — matching `Etingof.Example_6_4_9_An`. -/
theorem ncard_positiveLatticeRoots : Set.ncard (positiveLatticeRoots n) = n * (n + 1) / 2 := by
  have hset : positiveLatticeRoots n =
      ↑((univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).image
        (fun p => (Pi.single p.1 1 - Pi.single p.2 1 : Fin (n + 1) → ℤ))) := by
    ext x
    simp only [positiveLatticeRoots, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, j, hij, rfl⟩; exact ⟨(i, j), hij, rfl⟩
    · rintro ⟨⟨i, j⟩, hij, rfl⟩; exact ⟨i, j, hij, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, card_strictPairs]
  intro p hp q hq he
  exact diff_injOn n (by simpa using (mem_filter.mp hp).2) (by simpa using (mem_filter.mp hq).2) he

end Etingof.An
