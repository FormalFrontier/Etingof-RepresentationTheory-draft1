/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import RepresentationTheory.Quiver.AuxiliaryPathStructures
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.GradedAlgebra.HilbertSeries

open scoped ExteriorAlgebra

/-- A grading of an algebra by natural numbers whose homogeneous components are finite-dimensional over the base field. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
structure LocallyFiniteGrading (k A : Type*) [Field k] [Ring A] [Algebra k A] where

  /-- The homogeneous submodule of a locally finite grading in a specified natural degree. -/
  component : ℕ → Submodule k A

  /-- The homogeneous components of a locally finite grading form an internal direct sum. -/
  isInternal : DirectSum.IsInternal component

  /-- The product of elements in homogeneous components of degrees `n` and `m` lies in the component of degree `n + m`. -/
  mul_mem_component_add : ∀ {n m : ℕ} {x y : A}, x ∈ component n → y ∈ component m → x * y ∈ component (n + m)

  /-- Every homogeneous component of a locally finite grading is finite as a module over the base field. -/
  component_moduleFinite : ∀ n, Module.Finite k (component n)

/-- The integer-coefficient Hilbert series of a locally finite algebra grading. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
noncomputable def hilbertSeries {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (G : LocallyFiniteGrading k A) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    letI : Module.Finite k (G.component n) := G.component_moduleFinite n
    (Module.finrank k (G.component n) : ℤ)

/-- The coefficient of the Hilbert series in degree `n` is the integer cast of the finrank of the corresponding homogeneous component. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting), simp]
theorem hilbertSeries_coeff {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (G : LocallyFiniteGrading k A) (n : ℕ) :
    PowerSeries.coeff n (hilbertSeries G) =
      letI : Module.Finite k (G.component n) := G.component_moduleFinite n
      (Module.finrank k (G.component n) : ℤ) :=
  PowerSeries.coeff_mk _ _

/-- The degree-`n` homogeneous submodule of polynomials in `m` variables has the stated binomial-coefficient finrank. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem finrank_mvPolynomialHomogeneousSubmodule (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin m) k n) = (n + m - 1).choose n := by
  classical

  set s : Finset (Fin m →₀ ℕ) := (Finset.univ : Finset (Fin m)).finsuppAntidiag n with hs
  have hset : {d : Fin m →₀ ℕ | d.degree = n} = (↑s : Set (Fin m →₀ ℕ)) := by
    ext d
    simp only [Set.mem_setOf_eq, hs, Finset.mem_coe, Finset.mem_finsuppAntidiag,
      Finsupp.degree_eq_sum]
    exact ⟨fun h => ⟨h, Finset.subset_univ _⟩, fun h => h.1⟩

  have hsub : MvPolynomial.homogeneousSubmodule (Fin m) k n
      = MvPolynomial.restrictSupport k (↑s : Set (Fin m →₀ ℕ)) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hset]
    rfl
  rw [hsub, Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k
    (↑s : Set (Fin m →₀ ℕ))), Nat.card_coe_set_eq, Set.ncard_coe_finset, hs,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin, Nat.add_comm]

/-- The power series with the displayed multichoose coefficients is an inverse of `(1 - X) ^ m`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem one_sub_X_pow_mul_powerSeries_multichoose (k : Type*) [Field k] (m : ℕ) :
    (1 - PowerSeries.X : PowerSeries k) ^ m *
      PowerSeries.mk (fun n => ((n + m - 1).choose n : k)) = 1 := by
  rcases m with _ | d
  ·
    ext l
    rw [pow_zero, one_mul, PowerSeries.coeff_mk]
    rcases l with _ | e
    · simp
    · rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero e),
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  ·

    have hval : (PowerSeries.invOneSubPow k (d + 1)).val
        = PowerSeries.mk (fun l => ((l + (d + 1) - 1).choose l : k)) := by
      rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
      apply PowerSeries.ext
      intro l
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      congr 1

      have harg : l + (d + 1) - 1 = d + l := by omega
      rw [harg, ← Nat.choose_symm (Nat.le_add_left l d)]
      congr 1
      omega
    have key := (PowerSeries.invOneSubPow k (d + 1)).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, hval] at key
    exact key

/-- The algebra equivalence between the free algebra and the monoid algebra of the free monoid on the same generators. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
noncomputable def freeAlgebraEquivMonoidAlgebraFreeMonoid (k : Type*) [Field k] (m : ℕ) :
    FreeAlgebra k (Fin m) ≃ₐ[k] MonoidAlgebra k (FreeMonoid (Fin m)) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin m)

/-- A natural-number-indexed submodule of the monoid algebra on the free monoid over `Fin m`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
noncomputable def freeMonoidDegreeSubmodule (k : Type*) [Field k] (m n : ℕ) :
    Submodule k (MonoidAlgebra k (FreeMonoid (Fin m))) :=
  Submodule.map (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap
    (Finsupp.supported k k {w : FreeMonoid (Fin m) | w.length = n})

/-- The number of lists of length `n` over a type of cardinality `m` is `m ^ n`. -/
theorem card_lists_length_eq_pow (m n : ℕ) :
    Nat.card {l : List (Fin m) // l.length = n} = m ^ n := by

  have e : {l : List (Fin m) // l.length = n} ≃ (Fin n → Fin m) :=
    Equiv.vectorEquivFin (Fin m) n
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- The degree-`n` submodule of the free-monoid algebra on `m` generators has finrank `m ^ n`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem finrank_freeMonoidDegreeSubmodule (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (freeMonoidDegreeSubmodule k m n) = m ^ n := by
  let b : Module.Basis {w : FreeMonoid (Fin m) // w.length = n} k
      (freeMonoidDegreeSubmodule k m n) :=
    (Finsupp.basisSingleOne.map
      (Finsupp.supportedEquivFinsupp (R := k)
        {w : FreeMonoid (Fin m) | w.length = n}).symm).map
      ((MonoidAlgebra.coeffLinearEquiv k).symm.submoduleMap
        (Finsupp.supported k k {w : FreeMonoid (Fin m) | w.length = n}))
  calc
    Module.finrank k (freeMonoidDegreeSubmodule k m n) =
        Nat.card {w : FreeMonoid (Fin m) // w.length = n} :=
      Module.finrank_eq_nat_card_basis b
    _ = m ^ n := card_lists_length_eq_pow m n

/-- The power series with coefficients `m ^ n` is an inverse of `1 - m • X`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem one_sub_nat_smul_X_mul_powerSeries_pow (k : Type*) [Field k] (m : ℕ) :
    (1 - (m : ℕ) • PowerSeries.X : PowerSeries k) *
      PowerSeries.mk (fun n => ((m ^ n : ℕ) : k)) = 1 := by

  ext d
  rw [sub_mul, one_mul, smul_mul_assoc, map_sub, map_nsmul, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  rcases d with _ | e
  ·
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ·
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, nsmul_eq_mul]
    push_cast [pow_succ]
    ring

/-- The `n`-th exterior power of an `m`-dimensional finite function space has finrank `m.choose n`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem finrank_exteriorPower_finFunction (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (⋀[k]^n (Fin m → k)) = m.choose n := by

  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The power series with binomial coefficients `m.choose n` is `(1 + X) ^ m`. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem powerSeries_choose_eq_one_add_X_pow (k : Type*) [Field k] (m : ℕ) :
    PowerSeries.mk (fun n => ((m.choose n : ℕ) : k)) = (1 + PowerSeries.X : PowerSeries k) ^ m := by

  have hcoe : ((1 + PowerSeries.X : PowerSeries k) ^ m) =
      ((((1 + Polynomial.X) ^ m : Polynomial k) : PowerSeries k)) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [hcoe]
  ext n
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- A natural-number-indexed submodule associated with a quiver over a field. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
noncomputable def quiverDegreeSubmodule (k : Type*) [Field k] (Q : Type*) [Quiver Q]
    [DecidableEq Q] (n : ℕ) : Submodule k (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) :=
  Finsupp.supported k k {p : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q | p.2.2.length = n}

/-- The natural-number adjacency matrix of a quiver with finitely many arrows between each pair of vertices. -/
def adjacencyMatrix (Q : Type*) [Quiver Q] [∀ i j : Q, Fintype (i ⟶ j)] :
    Matrix Q Q ℕ :=
  fun i j => Fintype.card (i ⟶ j)

/-- An auxiliary definition whose formal type is unavailable in this packet. -/
def auxiliaryUnprintableDeclaration {Q : Type*} [Quiver Q] (i j : Q) (n : ℕ) :
    {p : Quiver.Path i j // p.length = n + 1} ≃
      Σ b : Q, {p : Quiver.Path i b // p.length = n} × (b ⟶ j) where
  toFun p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => exact ⟨_, ⟨p', by rw [Quiver.Path.length_cons] at h; omega⟩, e⟩
  invFun x := ⟨x.2.1.1.cons x.2.2, by rw [Quiver.Path.length_cons, x.2.1.2]⟩
  left_inv p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => rfl
  right_inv x := by
    obtain ⟨b, ⟨p', hp'⟩, e⟩ := x
    rfl

/-- For a finite quiver with finite arrow types, the paths of any fixed length between two vertices form a finite type. -/
instance finite_paths_of_length {Q : Type*} [Quiver Q] [Finite Q] [∀ i j : Q, Finite (i ⟶ j)]
    (i j : Q) (n : ℕ) : Finite {p : Quiver.Path i j // p.length = n} := by
  induction n generalizing j with
  | zero =>
    haveI : Subsingleton {p : Quiver.Path i j // p.length = 0} := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨p, hp⟩ := a
      obtain ⟨q, hq⟩ := b
      have hij : i = j := Quiver.Path.eq_of_length_zero p hp
      subst hij
      rw [Subtype.mk_eq_mk, Quiver.Path.eq_nil_of_length_zero p hp,
        Quiver.Path.eq_nil_of_length_zero q hq]
    exact Finite.of_injective (fun _ => (0 : Fin 1)) fun a b _ => Subsingleton.elim a b
  | succ n ih =>
    haveI : ∀ b : Q, Finite {p : Quiver.Path i b // p.length = n} := ih
    exact Finite.of_equiv _ (auxiliaryUnprintableDeclaration i j n).symm

/-- The number of quiver paths of a fixed length between two vertices is the corresponding entry of that power of the adjacency matrix. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem card_paths_length_eq_adjacencyMatrix_pow (Q : Type*) [Quiver Q] [Fintype Q]
    [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) (n : ℕ) :
    Nat.card {p : Quiver.Path i j // p.length = n} = (adjacencyMatrix Q ^ n) i j := by
  induction n generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      haveI : Nonempty {p : Quiver.Path i i // p.length = 0} :=
        ⟨⟨Quiver.Path.nil, Quiver.Path.length_nil⟩⟩
      haveI : Subsingleton {p : Quiver.Path i i // p.length = 0} :=
        ⟨fun a b => Subtype.ext ((Quiver.Path.eq_nil_of_length_zero _ a.2).trans
          (Quiver.Path.eq_nil_of_length_zero _ b.2).symm)⟩
      exact Nat.card_unique
    · rw [if_neg h]
      haveI : IsEmpty {p : Quiver.Path i j // p.length = 0} :=
        ⟨fun p => h (Quiver.Path.eq_of_length_zero p.1 p.2)⟩
      exact Nat.card_of_isEmpty
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Nat.card_congr (auxiliaryUnprintableDeclaration i j n), Nat.card_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_prod, ih b, Nat.card_eq_fintype_card]
    rfl

/-- Summing the numbers of length-`n` paths over all endpoint pairs equals the sum of the entries of the `n`-th adjacency-matrix power. -/
theorem sum_card_paths_length_eq_sum_adjacencyMatrix_pow (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Fintype (i ⟶ j)] (n : ℕ) :
    ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n}
      = ∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact card_paths_length_eq_adjacencyMatrix_pow Q i j n

/-- The finrank of the degree-`n` quiver submodule is the total number of quiver paths of length `n` over all endpoint pairs. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem finrank_quiverDegreeSubmodule (k : Type*) [Field k]
    (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Finite (i ⟶ j)] (n : ℕ) :
    Module.finrank k (quiverDegreeSubmodule k Q n) =
      ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} := by
  let T := Σ i : Q, Σ j : Q, {p : Quiver.Path i j // p.length = n}
  let e : {p : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q // p.2.2.length = n} ≃ T := {
    toFun p := ⟨p.1.1, p.1.2.1, ⟨p.1.2.2, p.2⟩⟩
    invFun p := ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
    left_inv p := by rcases p with ⟨⟨i, j, p⟩, hp⟩; rfl
    right_inv p := by rcases p with ⟨i, j, p, hp⟩; rfl }
  let b : Module.Basis {p : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q // p.2.2.length = n} k
      (quiverDegreeSubmodule k Q n) :=
    Finsupp.basisSingleOne.map
      (Finsupp.supportedEquivFinsupp (R := k)
        {p : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q | p.2.2.length = n}).symm
  calc
    Module.finrank k (quiverDegreeSubmodule k Q n) =
        Nat.card {p : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q // p.2.2.length = n} :=
      Module.finrank_eq_nat_card_basis b
    _ = Nat.card T := Nat.card_congr e
    _ = ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.card_sigma]

section HilbertSeries

variable (k : Type*) [CommRing k] (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

open PowerSeries
open scoped Matrix

/-- The quiver adjacency matrix embedded entrywise as constant power series over a commutative ring. -/
noncomputable def adjacencyConstantMatrix : Matrix Q Q (PowerSeries k) :=
  (adjacencyMatrix Q).map fun a => C (a : k)

omit [Fintype Q] [DecidableEq Q] in
/-- An entry of the constant power-series adjacency matrix is the constant series of the corresponding arrow count. -/
@[simp]
theorem adjacencyConstantMatrix_apply (i j : Q) :
    adjacencyConstantMatrix k Q i j = C ((adjacencyMatrix Q i j : ℕ) : k) :=
  rfl

/-- The matrix of power series whose coefficients count quiver paths by length and endpoint pair. -/
noncomputable def pathGeneratingMatrix : Matrix Q Q (PowerSeries k) :=
  fun i j => mk fun n => (((adjacencyMatrix Q ^ n) i j : ℕ) : k)

/-- The degree-`n` coefficient of the path-generating matrix is the cast of the corresponding adjacency-matrix power. -/
@[simp]
theorem pathGeneratingMatrix_coeff (i j : Q) (n : ℕ) :
    coeff n (pathGeneratingMatrix k Q i j) = (((adjacencyMatrix Q ^ n) i j : ℕ) : k) :=
  coeff_mk n _

/-- The degree-`d` coefficient of the adjacency matrix times the path-generating matrix is the cast of the degree-`d + 1` adjacency-matrix power. -/
theorem coeff_adjacency_mul_pathGeneratingMatrix (i j : Q) (d : ℕ) :
    coeff d ((adjacencyConstantMatrix k Q * pathGeneratingMatrix k Q) i j)
      = (((adjacencyMatrix Q ^ (d + 1)) i j : ℕ) : k) := by
  rw [Matrix.mul_apply, map_sum, pow_succ', Matrix.mul_apply]
  push_cast
  exact Finset.sum_congr rfl fun b _ => by rw [adjacencyConstantMatrix_apply, coeff_C_mul, pathGeneratingMatrix_coeff]

/-- One minus `X` times the constant adjacency matrix is a left inverse of the path-generating matrix. -/
theorem one_sub_X_smul_adjacency_mul_pathGeneratingMatrix :
    (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q) * pathGeneratingMatrix k Q = 1 := by
  have key : (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q) * pathGeneratingMatrix k Q
      = pathGeneratingMatrix k Q - (X : PowerSeries k) • (adjacencyConstantMatrix k Q * pathGeneratingMatrix k Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [key]
  ext i j d
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, pathGeneratingMatrix_coeff]
  rcases d with _ | e
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, sub_zero, pow_zero,
      Matrix.one_apply, Matrix.one_apply]
    split <;> simp
  · rw [coeff_succ_X_mul, coeff_adjacency_mul_pathGeneratingMatrix, sub_self, Matrix.one_apply]
    split <;> simp

/-- The determinant of one minus `X` times the constant adjacency matrix is a unit. -/
theorem isUnit_det_one_sub_X_smul_adjacency :
    IsUnit (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q).det :=
  Matrix.isUnit_det_of_right_inverse (one_sub_X_smul_adjacency_mul_pathGeneratingMatrix k Q)

/-- The inverse of one minus `X` times the constant adjacency matrix is the path-generating matrix. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem one_sub_X_smul_adjacency_inv :
    (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q)⁻¹ = pathGeneratingMatrix k Q :=
  Matrix.inv_eq_right_inv (one_sub_X_smul_adjacency_mul_pathGeneratingMatrix k Q)

/-- The path-generating matrix is a left inverse of one minus `X` times the constant adjacency matrix. -/
theorem pathGeneratingMatrix_mul_one_sub_X_smul_adjacency :
    pathGeneratingMatrix k Q * (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q) = 1 :=
  mul_eq_one_comm.mp (one_sub_X_smul_adjacency_mul_pathGeneratingMatrix k Q)

omit [Quiver Q] [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] in

/-- Multiplying a finite matrix by all-ones vectors on both sides equals the sum of all its entries. -/
theorem ones_dot_matrix_mul_ones (A : Matrix Q Q (PowerSeries k)) :
    (fun _ => 1) ᵥ* A ⬝ᵥ (fun _ => 1) = ∑ i : Q, ∑ j : Q, A i j := by
  simp only [Matrix.vecMul, dotProduct, one_mul, mul_one]
  exact Finset.sum_comm

/-- The generating series for total quiver path counts is obtained by multiplying the inverse adjacency-series matrix by all-ones vectors. -/
@[source_ref "Chapter2/Problem2.8.11" (role := supporting)]
theorem pathCountSeries_eq_ones_mul_matrixInverse_mul_ones :
    (mk fun n => ((∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} : ℕ) : k))
      = (fun _ => 1) ᵥ* (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q)⁻¹ ⬝ᵥ (fun _ => 1) := by
  rw [ones_dot_matrix_mul_ones, one_sub_X_smul_adjacency_inv]
  ext d
  rw [coeff_mk, sum_card_paths_length_eq_sum_adjacencyMatrix_pow, map_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => (pathGeneratingMatrix_coeff k Q i j d).symm

/-- The generating series for sums of entries of adjacency-matrix powers is obtained from the inverse adjacency-series matrix and all-ones vectors. -/
theorem adjacencyPowerSumSeries_eq_ones_mul_matrixInverse_mul_ones :
    (mk fun n => ((∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j : ℕ) : k))
      = (fun _ => 1) ᵥ* (1 - (X : PowerSeries k) • adjacencyConstantMatrix k Q)⁻¹ ⬝ᵥ (fun _ => 1) := by
  rw [← pathCountSeries_eq_ones_mul_matrixInverse_mul_ones k Q]
  congr 1
  funext n
  rw [sum_card_paths_length_eq_sum_adjacencyMatrix_pow]

end HilbertSeries

end RepresentationTheory.GradedAlgebra.HilbertSeries

attribute [nolint defsWithUnderscore]
  RepresentationTheory.GradedAlgebra.HilbertSeries.LocallyFiniteGrading.component
  RepresentationTheory.GradedAlgebra.HilbertSeries.hilbertSeries
  RepresentationTheory.GradedAlgebra.HilbertSeries.freeAlgebraEquivMonoidAlgebraFreeMonoid
  RepresentationTheory.GradedAlgebra.HilbertSeries.freeMonoidDegreeSubmodule
  RepresentationTheory.GradedAlgebra.HilbertSeries.quiverDegreeSubmodule
  RepresentationTheory.GradedAlgebra.HilbertSeries.adjacencyMatrix
  RepresentationTheory.GradedAlgebra.HilbertSeries.auxiliaryUnprintableDeclaration
  RepresentationTheory.GradedAlgebra.HilbertSeries.adjacencyConstantMatrix
  RepresentationTheory.GradedAlgebra.HilbertSeries.pathGeneratingMatrix
