/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.GenericBaseChange
import Mathlib

open Matrix MvPolynomial MulAction

namespace RepresentationTheory.Quiver.Representation.DenseOrbit

variable {k : Type} [Field k] {n : ℕ} [Quiver.{0} (Fin n)]
  [∀ i j : Fin n, Fintype (i ⟶ j)]

/-- The coordinate-value function obtained by reading every arrow-matrix entry of a quiver
representation. -/
def representationCoordinateValues (m : Fin n → ℕ)
    (x : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) :
    RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m → k :=
  fun w => x w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2

/-- The quiver representation assembled from a function assigning a scalar to each arrow-matrix
coordinate. -/
def representationOfCoordinateValues (m : Fin n → ℕ)
    (c : RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m → k) :
    RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m :=
  fun i j e => Matrix.of fun a b => c ⟨i, j, e, (a, b)⟩

omit [Field k] in
/-- Reading the coordinates of the representation assembled from a coordinate-value function
returns the original function. -/
@[simp]
theorem representationCoordinateValues_representationOfCoordinateValues
    (m : Fin n → ℕ)
    (c : RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m → k) :
    representationCoordinateValues m (representationOfCoordinateValues m c) = c := by
  funext w
  rcases w with ⟨i, j, e, a, b⟩
  rfl

/-- A subset of the representation space is polynomially dense when every polynomial vanishing
on it vanishes identically. -/
def IsPolynomiallyDense (m : Fin n → ℕ)
    (X : Set (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)) :
    Prop :=
  ∀ f : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) k,
    (∀ x ∈ X, aeval (representationCoordinateValues m x) f = 0) → f = 0

/-- For a base-change action with finitely many orbits over an infinite field, one orbit is
polynomially dense in the representation space. -/
theorem exists_polynomiallyDense_orbit [Infinite k] (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient
      (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
      (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    ∃ v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m,
      IsPolynomiallyDense m (orbit
        (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) v₀) := by
  classical
  by_contra h
  push Not at h
  set Q := orbitRel.Quotient
    (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) with hQ
  letI : Fintype Q := Fintype.ofFinite Q
  have hw : ∀ q : Q,
      ∃ f : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) k,
        (∀ x ∈ orbit
          (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) q.out,
          aeval (representationCoordinateValues m x) f = 0) ∧ f ≠ 0 := by
    intro q
    have hq := h q.out
    unfold IsPolynomiallyDense at hq
    push Not at hq
    exact hq
  choose f hfvan hf0 using hw
  set F : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) k :=
    ∏ q : Q, f q with hF
  have hFne : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => hf0 q
  have hF0 : F = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_zero]
    set x := representationOfCoordinateValues m c with hx
    have hxc : representationCoordinateValues m x = c :=
      representationCoordinateValues_representationOfCoordinateValues m c
    set q₀ : Q := Quotient.mk'' x with hq0
    have h1 : q₀.orbit = orbit
        (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) q₀.out :=
      orbitRel.Quotient.orbit_eq_orbit_out q₀ Quotient.out_eq'
    have h2 : q₀.orbit = orbit
        (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) x :=
      orbitRel.Quotient.orbit_mk x
    have hxmem : x ∈ orbit
        (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) q₀.out := by
      rw [← h1, h2]; exact mem_orbit_self x
    have hzero : aeval (representationCoordinateValues m x) (f q₀) = 0 :=
      hfvan q₀ x hxmem
    have : (eval c) F = aeval (representationCoordinateValues m x) F := by rw [← hxc]; rfl
    rw [this, hF, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q₀) hzero
  exact hFne hF0

section Reduction

variable (m : Fin n → ℕ)
variable {B : Type} [CommRing B]
  [Algebra (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) B]
  [IsLocalization (Submonoid.powers
    (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)) B]
  [Algebra k B]
  [IsScalarTower k
    (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) B]

/-- The assignment of coordinate variables obtained from the matrix entries of a base-change
group element. -/
def baseChangeCoordinateValues
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) :
    RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m → k :=
  fun w => (g w.1 : Matrix (Fin (m w.1)) (Fin (m w.1)) k) w.2.1 w.2.2

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- Entrywise evaluation of the generic base-change coordinate matrix at a group element recovers
the matrix underlying its component at the chosen vertex. -/
theorem aeval_baseChangeCoordinateMatrix
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (i : Fin n) :
    (aeval (baseChangeCoordinateValues m g)).mapMatrix
        (RepresentationTheory.Quiver.GenericBaseChange.genericVertexMatrix (k := k) m i) =
      (g i : Matrix _ _ k) := by
  ext a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply,
    RepresentationTheory.Quiver.GenericBaseChange.genericVertexMatrix, aeval_X]
  rfl

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- The distinguished denominator of the base-change coordinate ring evaluates to a unit at every
base-change group element. -/
theorem isUnit_aeval_baseChangeDenominator
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) :
    IsUnit (aeval (baseChangeCoordinateValues m g)
      (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct
        (k := k) m)) := by
  rw [RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct, map_prod,
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [AlgHom.map_det, aeval_baseChangeCoordinateMatrix]
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp (g i).isUnit).ne_zero

/-- The algebra homomorphism that evaluates the localized base-change coordinate ring at a
base-change group element. -/
noncomputable def baseChangePointEval
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) :
    B →ₐ[k] k :=
  IsLocalization.liftAlgHom (f := aeval (baseChangeCoordinateValues m g))
    (fun y => by
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [show (y : MvPolynomial
        (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) =
          RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct
            (k := k) m ^ j from hj.symm, map_pow]
      exact (isUnit_aeval_baseChangeDenominator m g).pow j)

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- On polynomials embedded in the localization, evaluation at a base-change group element agrees
with multivariate polynomial evaluation at its coordinate values. -/
theorem baseChangePointEval_algebraMap
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (p : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :
    baseChangePointEval (B := B) m g
        (algebraMap
          (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) B p) =
      aeval (baseChangeCoordinateValues m g) p := by
  rw [baseChangePointEval, IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ p

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- Entrywise evaluation of the localized generic matrix at a base-change group element yields its
matrix at the chosen vertex. -/
theorem baseChangePointEval_genericMatrix
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (i : Fin n) :
    (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix
      (k := k) (B := B) m i).map (baseChangePointEval (B := B) m g) =
        (g i : Matrix _ _ k) := by
  ext a b
  simp only [RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix,
    Matrix.map_apply]
  rw [baseChangePointEval_algebraMap]
  simp [RepresentationTheory.Quiver.GenericBaseChange.genericVertexMatrix,
    baseChangeCoordinateValues]

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- Entrywise evaluation of the localized generic inverse matrix at a base-change group element
yields the inverse of its matrix at the chosen vertex. -/
theorem baseChangePointEval_genericInverseMatrix
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (i : Fin n) :
    (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv
      (k := k) (B := B) m i).map (baseChangePointEval (B := B) m g) =
        (((g i)⁻¹ : GL (Fin (m i)) k) : Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hmul : (g i : Matrix _ _ k) *
      (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv
        (k := k) (B := B) m i).map (baseChangePointEval (B := B) m g) = 1 := by
    rw [← baseChangePointEval_genericMatrix (B := B) m g i, ← Matrix.map_mul,
      RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix_mul_inv,
      show ((1 : Matrix (Fin (m i)) (Fin (m i)) B).map
        (baseChangePointEval (B := B) m g)) = 1 from
          Matrix.map_one (⇑(baseChangePointEval (B := B) m g)) (map_zero _) (map_one _)]
  have h1 : ((g i : Matrix _ _ k))⁻¹ =
      (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv
        (k := k) (B := B) m i).map (baseChangePointEval m g) :=
    Matrix.inv_eq_right_inv hmul
  have h2 : ((g i : Matrix _ _ k))⁻¹ =
      (((g i)⁻¹ : GL (Fin (m i)) k) : Matrix (Fin (m i)) (Fin (m i)) k) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  rw [← h1, h2]

/-- Composing evaluation at a base-change group element with the coordinate-ring pullback of an
orbit map equals evaluation at the transformed representation. -/
theorem baseChangePointEval_comp_orbitMapPullback
    (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
    (v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) :
    (baseChangePointEval (B := B) m g).comp
        (RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom
          (B := B) m v₀) =
      aeval (representationCoordinateValues m (g • v₀)) := by
  apply MvPolynomial.algHom_ext
  intro w
  have hmid : ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B)).map
      (baseChangePointEval (B := B) m g) = v₀ w.1 w.2.1 w.2.2.1 := by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]
    simp
  have key : ∀ M : Matrix (Fin (m w.2.1)) (Fin (m w.1)) B,
      (baseChangePointEval (B := B) m g) (M w.2.2.2.1 w.2.2.2.2) =
        (M.map (baseChangePointEval (B := B) m g)) w.2.2.2.1 w.2.2.2.2 :=
    fun _ => rfl
  rw [AlgHom.comp_apply,
    RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom_apply_X, aeval_X,
    representationCoordinateValues,
    RepresentationTheory.Quiver.Representation.MatrixModel.baseChange_smul_apply,
    key, Matrix.map_mul, Matrix.map_mul, baseChangePointEval_genericMatrix,
    baseChangePointEval_genericInverseMatrix, hmid]

/-- Polynomial density of a representation's orbit makes the coordinate-ring pullback along its
orbit map injective. -/
theorem orbitMapPullback_injective_of_polynomiallyDense
    (v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)
    (hdense : IsPolynomiallyDense m (orbit
      (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) v₀)) :
    Function.Injective
      (RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom
        (B := B) m v₀) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply hdense
  intro x hx
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  have := congrArg (baseChangePointEval (B := B) m g) hf
  rw [map_zero, ← AlgHom.comp_apply, baseChangePointEval_comp_orbitMapPullback] at this
  exact this

/-- If the base-change action has finitely many orbits over an infinite field, some representation
has an injective coordinate-ring pullback along its orbit map. -/
theorem exists_injective_orbitMapPullback [Infinite k]
    [Finite (orbitRel.Quotient
      (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m)
      (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    ∃ v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m,
      Function.Injective
        (RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom
          (B := B) m v₀) := by
  obtain ⟨v₀, hv₀⟩ := exists_polynomiallyDense_orbit (k := k) m
  exact ⟨v₀, orbitMapPullback_injective_of_polynomiallyDense m v₀ hv₀⟩

end Reduction

end RepresentationTheory.Quiver.Representation.DenseOrbit
