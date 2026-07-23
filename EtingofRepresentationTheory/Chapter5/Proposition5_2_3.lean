import Mathlib

/-!
# Proposition 5.2.3: Equivalence of Algebraic Number Definitions

Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers
and algebraic integers.

## The two proof ingredients

* `(5.2.1 → 5.2.2)`: a root of a monic polynomial is an eigenvalue of a matrix. The book
  proves this by writing down the **companion matrix** of the polynomial and checking that
  its characteristic polynomial is the polynomial itself.
* `(5.2.2 → 5.2.1)`: an eigenvalue of a matrix is a root of its (monic) characteristic
  polynomial.

## Two levels of formalization

The final equivalences `Etingof.Proposition5_2_3_algebraic` and
`Etingof.Proposition5_2_3_integer` are proved through the **left-multiplication matrix**
`Algebra.leftMulMatrix` on a power basis. This is a valid alternative realization of the
forward direction whose characteristic polynomial is the minimal polynomial of the
generator; it establishes the stated `↔` but does not name or display the companion matrix.

The book's actual construction — the explicit companion matrix and the displayed identity
`charpoly (companion p) = p` — is formalized separately in the
`Etingof.Proposition5_2_3` namespace:

* `Etingof.Proposition5_2_3.companionMatrix` is the explicit `Fin n × Fin n` matrix shown in
  the text (subdiagonal ones, negated coefficients in the last column);
* `Etingof.Proposition5_2_3.charpoly_companionMatrix` proves `charpoly (companionMatrix p) = p`;
* `Etingof.Proposition5_2_3.charpoly_map_companionMatrix_isRoot` exposes the resulting
  root-to-eigenvalue step over any base change.
-/

open Polynomial Matrix

namespace Etingof.Proposition5_2_3

variable {R : Type*} [CommRing R]

/-- The **companion matrix** of a polynomial `p` of degree `n = p.natDegree`, indexed by
`Fin n`. It carries ones on the subdiagonal and the negated coefficients of `p` in the last
column, matching the matrix displayed in the proof of Proposition 5.2.3:
`[[0,…,0,-aₙ], [1,…,0,-a_{n-1}], …, [0,…,1,-a₁]]`.

For the zero-degree case (`n = 0`, e.g. `p = 1`) this is the empty `0 × 0` matrix, whose
characteristic polynomial is `1 = p`, so `charpoly_companionMatrix` holds there as well. -/
def companionMatrix (p : R[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j =>
    if (j : ℕ) = p.natDegree - 1 then -p.coeff i
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- The top power of the canonical root reduces to a combination of the lower powers via the
coefficients of the monic polynomial: in `AdjoinRoot p`, `x ^ n = ∑_{k<n} (-p.coeff k) • x ^ k`. -/
theorem root_pow_natDegree (p : R[X]) (hp : p.Monic) :
    (AdjoinRoot.root p) ^ p.natDegree
      = ∑ k : Fin p.natDegree, (-p.coeff k) • (AdjoinRoot.root p) ^ (k : ℕ) := by
  set x := AdjoinRoot.root p
  have h0 : (aeval x) p = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at h0
  have hx : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i := by
    linear_combination h0
  rw [hx, ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i • x ^ i) p.natDegree]
  simp only [neg_smul]
  rw [Finset.sum_neg_distrib]

/-- The coordinate of a power `root p ^ m`, with `m` below the degree, in the power basis of
`AdjoinRoot p`: it is the indicator of `m = i`. -/
theorem repr_root_pow (p : R[X]) (hp : p.Monic) {m : ℕ} (hm : m < p.natDegree)
    (i : Fin p.natDegree) :
    (AdjoinRoot.powerBasis' hp).basis.repr (AdjoinRoot.root p ^ m) i
      = if m = (i : ℕ) then 1 else 0 := by
  have hb : AdjoinRoot.root p ^ m = (AdjoinRoot.powerBasis' hp).basis ⟨m, hm⟩ := by
    rw [PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
  rw [hb, Module.Basis.repr_self, Finsupp.single_apply]
  simp [Fin.ext_iff]

/-- The companion matrix is exactly the matrix of multiplication by the root in the power
basis of `AdjoinRoot p`. This is the indexing convention that makes the last column carry the
negated coefficients and the subdiagonal carry ones. -/
theorem companionMatrix_eq_leftMulMatrix (p : R[X]) (hp : p.Monic) :
    companionMatrix p =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.powerBasis' hp).gen := by
  ext i j
  rw [companionMatrix, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, ← pow_succ']
  by_cases hj : (j : ℕ) = p.natDegree - 1
  · rw [if_pos hj]
    have hjn : (j : ℕ) + 1 = p.natDegree := by omega
    rw [hjn, root_pow_natDegree p hp, map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Finsupp.smul_apply, repr_root_pow p hp (Fin.is_lt _), smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (by simpa [Fin.ext_iff, eq_comm] using hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hj]
    have hjn : (j : ℕ) + 1 < p.natDegree := by omega
    rw [repr_root_pow p hp hjn i]
    simp [eq_comm]

/-- The minimal polynomial of the canonical root of a monic polynomial `p` is `p` itself.
This holds over any nontrivial commutative ring: `p` divides the (monic) minimal polynomial,
and both have degree `p.natDegree`, so they agree. -/
theorem minpoly_adjoinRoot_root [Nontrivial R] (p : R[X]) (hp : p.Monic) :
    minpoly R (AdjoinRoot.root p) = p := by
  haveI : Module.Finite R (AdjoinRoot p) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hp).basis
  haveI : Module.Free R (AdjoinRoot p) := Module.Free.of_basis (AdjoinRoot.powerBasis' hp).basis
  have hint : IsIntegral R (AdjoinRoot.root p) := by
    refine ⟨p, hp, ?_⟩
    change (Polynomial.aeval (AdjoinRoot.root p)) p = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hmono : (minpoly R (AdjoinRoot.root p)).Monic := minpoly.monic hint
  obtain ⟨c, hc⟩ : p ∣ minpoly R (AdjoinRoot.root p) := by
    have h := minpoly.aeval R (AdjoinRoot.root p)
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h
    exact h
  have hcmonic : c.Monic := hp.of_mul_monic_left (hc ▸ hmono)
  have hle : (minpoly R (AdjoinRoot.root p)).natDegree ≤ p.natDegree := by
    have h := minpoly.natDegree_le (A := R) (AdjoinRoot.root p)
    rwa [(AdjoinRoot.powerBasis' hp).finrank, AdjoinRoot.powerBasis'_dim] at h
  have hdeg : (minpoly R (AdjoinRoot.root p)).natDegree = p.natDegree + c.natDegree := by
    rw [hc, hp.natDegree_mul hcmonic]
  have hc0 : c.natDegree = 0 := by omega
  rw [hc, eq_one_of_monic_natDegree_zero hcmonic hc0, mul_one]

/-- **Displayed formula of Proposition 5.2.3.** The characteristic polynomial of the companion
matrix of a monic polynomial `p` is `p` itself. -/
theorem charpoly_companionMatrix [Nontrivial R] (p : R[X]) (hp : p.Monic) :
    (companionMatrix p).charpoly = p := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hp)
  rw [AdjoinRoot.powerBasis'_gen, minpoly_adjoinRoot_root p hp] at h
  rw [companionMatrix_eq_leftMulMatrix p hp]
  exact h

/-- **Root-to-eigenvalue step.** If `z` in a base-changed ring `S` is a root of a monic
polynomial `p`, then it is a root of the characteristic polynomial of the base-changed
companion matrix, i.e. an eigenvalue of that matrix. This is the forward direction
`(5.2.1 → 5.2.2)` realized through the explicit companion matrix. -/
theorem charpoly_map_companionMatrix_isRoot [Nontrivial R] {S : Type*} [CommRing S]
    (φ : R →+* S) (p : R[X]) (hp : p.Monic) (z : S) (hz : p.eval₂ φ z = 0) :
    (Matrix.charpoly ((companionMatrix p).map φ)).IsRoot z := by
  rw [Matrix.charpoly_map, charpoly_companionMatrix p hp, Polynomial.IsRoot, Polynomial.eval_map]
  exact hz

end Etingof.Proposition5_2_3

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers:
z is a root of a rational polynomial iff z is an eigenvalue of a rational matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_algebraic (z : ℂ) :
    (∃ p : Polynomial ℚ, p ≠ 0 ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z) := by
  constructor
  · -- Forward: algebraic → eigenvalue of a rational matrix
    -- Uses the left multiplication matrix on the power basis of ℚ⟮z⟯
    intro ⟨p, hp, hpz⟩
    have hint : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp ⟨p, hp, hpz⟩
    let pb := IntermediateField.adjoin.powerBasis hint
    refine ⟨pb.dim, Algebra.leftMulMatrix pb.basis pb.gen, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact minpoly.aeval ℚ z
  · -- Backward: eigenvalue of rational matrix → algebraic
    -- The characteristic polynomial is nonzero and annihilates z
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic.ne_zero, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic integers:
z is a root of a monic integer polynomial iff z is an eigenvalue of an integer matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_integer (z : ℂ) :
    (∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z) := by
  constructor
  · -- Forward: root of monic integer polynomial → eigenvalue of integer matrix
    -- Uses the left multiplication matrix on AdjoinRoot p, and the algebra hom to ℂ
    intro ⟨p, hp, hpz⟩
    let pb := AdjoinRoot.powerBasis' hp
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨pb.dim, M, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    -- Use the algebra hom φ : AdjoinRoot p →ₐ[ℤ] ℂ sending root p ↦ z
    have heval : p.eval₂ (↑(Algebra.ofId ℤ ℂ)) z = 0 := hpz
    let φ : AdjoinRoot p →ₐ[ℤ] ℂ :=
      AdjoinRoot.liftAlgHom p (Algebra.ofId ℤ ℂ) z heval
    -- pb.gen = root p, and φ(root p) = z
    have hgen : φ pb.gen = z :=
      AdjoinRoot.liftAlgHom_root (p := p) (Algebra.ofId ℤ ℂ) z heval
    rw [← hgen]
    have := Polynomial.aeval_algHom_apply φ pb.gen (minpoly ℤ pb.gen)
    rw [this, minpoly.aeval, map_zero]
  · -- Backward: eigenvalue of integer matrix → root of monic integer polynomial
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩

/-- The companion-matrix realization of the forward direction `(5.2.1 → 5.2.2)` for algebraic
numbers: a root `z ∈ ℂ` of a monic rational polynomial is an eigenvalue of the (rational)
companion matrix. Complements `Etingof.Proposition5_2_3_algebraic`, whose forward direction
instead uses the left-multiplication matrix. -/
theorem Etingof.Proposition5_2_3_companion_algebraic (z : ℂ) (p : Polynomial ℚ) (hp : p.Monic)
    (hpz : Polynomial.aeval z p = 0) :
    (Matrix.charpoly
      ((Etingof.Proposition5_2_3.companionMatrix p).map (algebraMap ℚ ℂ))).IsRoot z :=
  Etingof.Proposition5_2_3.charpoly_map_companionMatrix_isRoot (algebraMap ℚ ℂ) p hp z hpz

/-- The companion-matrix realization of the forward direction `(5.2.1 → 5.2.2)` for algebraic
integers: a root `z ∈ ℂ` of a monic integer polynomial is an eigenvalue of the (integer)
companion matrix. Complements `Etingof.Proposition5_2_3_integer`. -/
theorem Etingof.Proposition5_2_3_companion_integer (z : ℂ) (p : Polynomial ℤ) (hp : p.Monic)
    (hpz : Polynomial.aeval z p = 0) :
    (Matrix.charpoly
      ((Etingof.Proposition5_2_3.companionMatrix p).map (algebraMap ℤ ℂ))).IsRoot z :=
  Etingof.Proposition5_2_3.charpoly_map_companionMatrix_isRoot (algebraMap ℤ ℂ) p hp z hpz
