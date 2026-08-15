/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Matrices for polynomial adjoin roots
-/

open Polynomial Matrix

namespace RepresentationTheory.Polynomial.AdjoinRoot.Matrix

variable {R : Type*} [CommRing R]

/-- An auxiliary square matrix indexed by the natural degree of a polynomial. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := supporting)]
def Polynomial.auxiliaryMatrix (p : R[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j =>
    if (j : ℕ) = p.natDegree - 1 then -p.coeff i
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- A monic polynomial gives an expression for the degree-th power of its distinguished root using lower powers. -/
theorem AdjoinRoot.root_pow_natDegree_eq_sum (p : R[X]) (hp : p.Monic) :
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

/-- The coordinate vector of a root power below the degree is the corresponding standard basis vector. -/
theorem AdjoinRoot.powerBasis_repr_root_pow (p : R[X]) (hp : p.Monic) {m : ℕ}
    (hm : m < p.natDegree) (i : Fin p.natDegree) :
    (AdjoinRoot.powerBasis' hp).basis.repr (AdjoinRoot.root p ^ m) i
      = if m = (i : ℕ) then 1 else 0 := by
  have hb : AdjoinRoot.root p ^ m = (AdjoinRoot.powerBasis' hp).basis ⟨m, hm⟩ := by
    rw [PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
  rw [hb, Module.Basis.repr_self, Finsupp.single_apply]
  simp [Fin.ext_iff]

/-- For a monic polynomial, the auxiliary matrix is the matrix of multiplication by the distinguished root. -/
theorem Polynomial.auxiliaryMatrix_eq_leftMulMatrix (p : R[X]) (hp : p.Monic) :
    Polynomial.auxiliaryMatrix p =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.powerBasis' hp).gen := by
  ext i j
  rw [Polynomial.auxiliaryMatrix, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, ← pow_succ']
  by_cases hj : (j : ℕ) = p.natDegree - 1
  · rw [if_pos hj]
    have hjn : (j : ℕ) + 1 = p.natDegree := by omega
    rw [hjn, AdjoinRoot.root_pow_natDegree_eq_sum p hp, map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Finsupp.smul_apply,
      AdjoinRoot.powerBasis_repr_root_pow p hp (Fin.is_lt _), smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (by simpa [Fin.ext_iff, eq_comm] using hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hj]
    have hjn : (j : ℕ) + 1 < p.natDegree := by omega
    rw [AdjoinRoot.powerBasis_repr_root_pow p hp hjn i]
    simp [eq_comm]

/-- The distinguished root of a monic polynomial has the original polynomial as its minimal polynomial. -/
theorem AdjoinRoot.minpoly_root_eq_of_monic [Nontrivial R] (p : R[X]) (hp : p.Monic) :
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

/-- The characteristic polynomial of the auxiliary matrix of a monic polynomial is that polynomial. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := primary)]
theorem Polynomial.charpoly_auxiliaryMatrix_eq_of_monic [Nontrivial R] (p : R[X]) (hp : p.Monic) :
    (Polynomial.auxiliaryMatrix p).charpoly = p := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hp)
  rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root_eq_of_monic p hp] at h
  rw [Polynomial.auxiliaryMatrix_eq_leftMulMatrix p hp]
  exact h

/-- A root of a monic polynomial remains a root of the characteristic polynomial after mapping its auxiliary matrix. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := primary)]
theorem Polynomial.isRoot_charpoly_map_auxiliaryMatrix_of_monic [Nontrivial R]
    {S : Type*} [CommRing S] (φ : R →+* S) (p : R[X]) (hp : p.Monic) (z : S)
    (hz : p.eval₂ φ z = 0) :
    (Matrix.charpoly ((Polynomial.auxiliaryMatrix p).map φ)).IsRoot z := by
  rw [Matrix.charpoly_map, Polynomial.charpoly_auxiliaryMatrix_eq_of_monic p hp,
    Polynomial.IsRoot, Polynomial.eval_map]
  exact hz

end RepresentationTheory.Polynomial.AdjoinRoot.Matrix

/-- A complex number is algebraic over the rationals exactly when it is a root of a characteristic polynomial of a rational matrix. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := supporting)]
theorem RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isAlgebraic_iff_isRoot_rat_matrix_charpoly
    (z : ℂ) :
    (∃ p : Polynomial ℚ, p ≠ 0 ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z) := by
  constructor
  ·
    intro ⟨p, hp, hpz⟩
    have hint : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp ⟨p, hp, hpz⟩
    let pb := IntermediateField.adjoin.powerBasis hint
    refine ⟨pb.dim, Algebra.leftMulMatrix pb.basis pb.gen, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact minpoly.aeval ℚ z
  ·
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic.ne_zero, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩

/-- A complex number is a root of some monic integer polynomial exactly when it is a root of a characteristic polynomial from an integer matrix. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := primary)]
theorem RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.exists_int_monic_root_iff_exists_int_matrix_charpoly_root
    (z : ℂ) :
    (∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z) := by
  constructor
  ·
    intro ⟨p, hp, hpz⟩
    let pb := AdjoinRoot.powerBasis' hp
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨pb.dim, M, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    have heval : p.eval₂ (↑(Algebra.ofId ℤ ℂ)) z = 0 := hpz
    let φ : AdjoinRoot p →ₐ[ℤ] ℂ :=
      AdjoinRoot.liftAlgHom p (Algebra.ofId ℤ ℂ) z heval
    have hgen : φ pb.gen = z :=
      AdjoinRoot.liftAlgHom_root (p := p) (Algebra.ofId ℤ ℂ) z heval
    rw [← hgen]
    have := Polynomial.aeval_algHom_apply φ pb.gen (minpoly ℤ pb.gen)
    rw [this, minpoly.aeval, map_zero]
  ·
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩

/-- Mapping the auxiliary matrix of a monic rational polynomial to the complex numbers produces a characteristic polynomial vanishing at each complex zero of the original polynomial. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := supporting)]
theorem RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isRoot_rat_matrix_charpoly_of_rat_monic
    (z : ℂ) (p : Polynomial ℚ) (hp : p.Monic) (hpz : Polynomial.aeval z p = 0) :
    (Matrix.charpoly
      ((RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.auxiliaryMatrix p).map
        (algebraMap ℚ ℂ))).IsRoot z :=
  RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.isRoot_charpoly_map_auxiliaryMatrix_of_monic
    (algebraMap ℚ ℂ) p hp z hpz

/-- Mapping the auxiliary matrix of a monic integer polynomial to the complex numbers produces a characteristic polynomial vanishing at each complex zero of the original polynomial. -/
@[source_ref "Chapter5/Proposition5.2.3" (role := supporting)]
theorem RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isRoot_int_matrix_charpoly_of_int_monic
    (z : ℂ) (p : Polynomial ℤ) (hp : p.Monic) (hpz : Polynomial.aeval z p = 0) :
    (Matrix.charpoly
      ((RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.auxiliaryMatrix p).map
        (algebraMap ℤ ℂ))).IsRoot z :=
  RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.isRoot_charpoly_map_auxiliaryMatrix_of_monic
    (algebraMap ℤ ℂ) p hp z hpz
