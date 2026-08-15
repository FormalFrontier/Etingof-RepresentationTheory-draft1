/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Representation.DenseOrbit
import RepresentationTheory.Algebra.MvPolynomial.VariableCount
import RepresentationTheory.Algebra.TranscendenceDegree.PolynomialScaling
import Mathlib

open Matrix MvPolynomial MulAction

namespace RepresentationTheory.Quiver.FiniteOrbitDimensionBounds

/-- An embedding of a polynomial algebra into a localization of another polynomial algebra cannot increase the number of algebraically independent variables. -/
theorem MvPolynomial.card_le_card_of_injective_algHom_to_localization
    {k : Type} [Field k] {σ τ : Type} [Fintype σ] [Fintype τ]
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial τ k)}
    [Algebra (MvPolynomial τ k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial τ k) B]
    (φ : MvPolynomial σ k →ₐ[k] B) (hφ : Function.Injective φ) :
    Fintype.card σ ≤ Fintype.card τ := by
  classical

  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let eτ : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ

  let h : MvPolynomial τ k ≃+* MvPolynomial (Fin (Fintype.card τ)) k :=
    (renameEquiv k eτ).toRingEquiv
  letI algB : Algebra (MvPolynomial (Fin (Fintype.card τ)) k) B :=
    ((algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom).toAlgebra
  haveI locB : IsLocalization (S.map h) B :=
    IsLocalization.isLocalization_of_base_ringEquiv S B h

  haveI towerB : IsScalarTower k (MvPolynomial (Fin (Fintype.card τ)) k) B := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have e1 : (algebraMap (MvPolynomial (Fin (Fintype.card τ)) k) B)
        = (algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom :=
      RingHom.algebraMap_toAlgebra _
    have e2 : h.symm.toRingHom (algebraMap k (MvPolynomial (Fin (Fintype.card τ)) k) x)
        = algebraMap k (MvPolynomial τ k) x :=
      (renameEquiv k eτ).symm.commutes x
    rw [e1, RingHom.comp_apply, e2, ← IsScalarTower.algebraMap_apply k (MvPolynomial τ k) B]

  let φ' : MvPolynomial (Fin (Fintype.card σ)) k →ₐ[k] B :=
    φ.comp (renameEquiv k eσ.symm).toAlgHom
  have hφ' : Function.Injective φ' := by
    have : (φ' : MvPolynomial (Fin (Fintype.card σ)) k → B)
        = φ ∘ (renameEquiv k eσ.symm) := by
      ext p; simp [φ']
    rw [show (⇑φ') = _ from this]
    exact hφ.comp (renameEquiv k eσ.symm).injective
  exact RepresentationTheory.Algebra.MvPolynomial.VariableCount.MvPolynomial.variable_count_le_of_injective_algHom_of_isLocalization (S := S.map h) φ' hφ'

variable {k : Type} [Field k] [Infinite k] {n : ℕ}
  [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

/-- For a finite quiver over an infinite field, a finite base-change orbit space bounds the number of representation coordinates by the number of vertex-endomorphism coordinates. -/
theorem Quiver.card_representation_coordinates_le_card_vertex_endomorphism_coordinates_of_finite_orbits (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    Fintype.card (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) ≤ Fintype.card (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) := by

  haveI : IsDomain (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) :=
    IsLocalization.isDomain_localization
      (M := Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct_ne_zero (k := k) m))
  obtain ⟨v₀, hv₀⟩ :=
    RepresentationTheory.Quiver.Representation.DenseOrbit.exists_injective_orbitMapPullback
      (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) (k := k) m
  exact MvPolynomial.card_le_card_of_injective_algHom_to_localization
    (S := Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))
    (RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m v₀) hv₀

set_option linter.unusedFintypeInType false in

/-- For representations of a finite quiver over an infinite field, a finite base-change orbit space bounds the dimension of the representation space by that of the product of vertex endomorphism spaces. -/
theorem Quiver.finrank_representation_space_le_finrank_vertex_endomorphisms_of_finite_orbits (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    Module.finrank k (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)
      ≤ Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hle := Quiver.card_representation_coordinates_le_card_vertex_endomorphism_coordinates_of_finite_orbits (k := k) m
  rwa [RepresentationTheory.Quiver.GenericBaseChange.card_arrowMatrixIndex, RepresentationTheory.Quiver.GenericBaseChange.card_vertexMatrixIndex, ← RepresentationTheory.Quiver.Representation.MatrixModel.finrank_matrixData (k := k) m,
    ← RepresentationTheory.Quiver.Representation.MatrixModel.finrank_vertexMatrixFamily (k := k) m] at hle

/-- The algebra automorphism that multiplies every coordinate variable associated with a dimension vector by a chosen unit. -/
noncomputable def MvPolynomial.uniformUnitScalingAlgEquiv (m : Fin n → ℕ) (c : kˣ) :
    MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k ≃ₐ[k] MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k :=
  AlgEquiv.ofAlgHom
    (aeval fun t : RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m => (c : k) • X t)
    (aeval fun t : RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m => ((c⁻¹ : kˣ) : k) • X t)
    (by
      apply MvPolynomial.algHom_ext
      intro t
      simp only [AlgHom.comp_apply, aeval_X, map_smul, AlgHom.coe_id, id_eq]
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
    (by
      apply MvPolynomial.algHom_ext
      intro t
      simp only [AlgHom.comp_apply, aeval_X, map_smul, AlgHom.coe_id, id_eq]
      rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])

omit [Quiver.{0} (Fin n)] [Infinite k] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- Uniform unit scaling sends each coordinate indeterminate to the chosen scalar times that indeterminate. -/
@[simp]
theorem MvPolynomial.uniformUnitScalingAlgEquiv_apply_X (m : Fin n → ℕ) (c : kˣ) (t : RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) :
    MvPolynomial.uniformUnitScalingAlgEquiv m c (X t) = (c : k) • X t := by
  rw [MvPolynomial.uniformUnitScalingAlgEquiv, AlgEquiv.ofAlgHom_apply, aeval_X]

/-- The fraction-field automorphism obtained by extending uniform unit scaling of the coordinate polynomial ring. -/
noncomputable def MvPolynomial.uniformUnitScalingFractionRingAlgEquiv (m : Fin n → ℕ) (c : kˣ) :
    FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) ≃ₐ[k] FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.uniformUnitScalingAlgEquiv m c)

omit [Quiver.{0} (Fin n)] [Infinite k] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- On embedded coordinate polynomials, fraction-field scaling agrees with polynomial scaling followed by the canonical inclusion. -/
@[simp]
theorem MvPolynomial.uniformUnitScalingFractionRingAlgEquiv_algebraMap (m : Fin n → ℕ) (c : kˣ) (x : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :
    MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m c (algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)
        (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) x)
      = algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))
          (MvPolynomial.uniformUnitScalingAlgEquiv m c x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (MvPolynomial.uniformUnitScalingAlgEquiv m c) x

/-- A ring endomorphism fixes the matrix product A V C⁻¹ when it fixes V, scales A and C by the same unit, and C is invertible. -/
theorem Matrix.map_mul_mul_inv_eq_self_of_common_unit_scaling {K : Type*} [Field K] {p q : ℕ}
    {F : Type*} [FunLike F K K] [RingHomClass F K K] (Φ : F) (μ : Kˣ)
    {A : Matrix (Fin p) (Fin p) K} {V : Matrix (Fin p) (Fin q) K}
    {C : Matrix (Fin q) (Fin q) K}
    (hA : A.map Φ = (μ : K) • A) (hV : V.map Φ = V)
    (hCm : C.map Φ = (μ : K) • C) (hCdet : IsUnit C.det) :
    (A * V * C⁻¹).map Φ = A * V * C⁻¹ := by
  have hCinv : (C⁻¹).map Φ = (μ : K)⁻¹ • C⁻¹ := by
    have h1 : (C * C⁻¹).map Φ = (1 : Matrix (Fin q) (Fin q) K).map Φ := by
      rw [Matrix.mul_nonsing_inv C hCdet]
    rw [Matrix.map_mul, hCm, Matrix.map_one (⇑Φ) (map_zero Φ) (map_one Φ)] at h1

    have hsc : ((μ : K) • C)⁻¹ = (μ : K)⁻¹ • C⁻¹ := by
      have h := Matrix.inv_smul' C μ hCdet
      rwa [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val] at h
    rw [← hsc, ← Matrix.inv_eq_right_inv h1]
  rw [Matrix.map_mul, Matrix.map_mul, hA, hV, hCinv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (Units.ne_zero μ), one_smul]

/-- For a nonzero dimension vector with finitely many base-change orbits, the representation-coordinate index type is strictly smaller than the vertex-endomorphism-coordinate index type. -/
theorem Quiver.card_representation_coordinates_lt_card_vertex_endomorphism_coordinates_of_finite_orbits (m : Fin n → ℕ) (hm : m ≠ 0)
    [Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    Fintype.card (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) < Fintype.card (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) := by
  classical

  haveI : IsDomain (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) :=
    IsLocalization.isDomain_localization
      (M := Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct_ne_zero (k := k) m))

  obtain ⟨v₀, hv₀⟩ :=
    RepresentationTheory.Quiver.Representation.DenseOrbit.exists_injective_orbitMapPullback
      (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) (k := k) m

  have halg_inj : Function.Injective
      (algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))) :=
    IsFractionRing.injective _ _

  have hf_units : ∀ y : Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m),
      IsUnit (IsScalarTower.toAlgHom k (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)
        (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) (y : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) := by
    intro y
    have hy : (y : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) ∈ nonZeroDivisors (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :=
      powers_le_nonZeroDivisors_of_noZeroDivisors (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct_ne_zero (k := k) m) y.2
    rw [IsScalarTower.toAlgHom_apply]
    exact (Ne.isUnit ((map_ne_zero_iff _ halg_inj).mpr (nonZeroDivisors.ne_zero hy)))

  let ιB : Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)) →ₐ[k]
      FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) := IsLocalization.liftAlgHom hf_units
  have hιB_alg : ∀ x : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k,
      ιB (algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)
            (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) x)
        = algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) x := by
    intro x
    change IsLocalization.liftAlgHom hf_units _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl

  have hιB_inj : Function.Injective ιB := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨x, s⟩, hs⟩ :=
      IsLocalization.surj (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)) b
    have happ := congrArg ιB hs
    rw [map_mul, hb, zero_mul, hιB_alg] at happ
    have hx0 : x = 0 := (map_eq_zero_iff _ halg_inj).mp happ.symm
    rw [hx0, map_zero] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact h
    · exact absurd h (IsLocalization.map_units _ s).ne_zero

  set φ : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m) k →ₐ[k] FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :=
    ιB.comp (RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom
      (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m v₀) with hφ
  have hφ_inj : Function.Injective φ := by
    rw [hφ, AlgHom.coe_comp]; exact hιB_inj.comp hv₀

  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hm
  rw [Pi.zero_apply] at hi₀
  set t₀ : RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m :=
    ⟨i₀, (⟨0, Nat.pos_of_ne_zero hi₀⟩, ⟨0, Nat.pos_of_ne_zero hi₀⟩)⟩ with ht₀
  set g : FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) :=
    algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) (X t₀)
    with hg_def
  have hg : g ≠ 0 := (map_ne_zero_iff _ halg_inj).mpr (MvPolynomial.X_ne_zero t₀)

  have hsmul : ∀ (c : k) (z : MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k),
      algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) (c • z)
        = c • algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)
            (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) z := by
    intro c z
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]

  have hscale_g : ∀ μ : kˣ, MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ g = (μ : k) • g := by
    intro μ
    rw [hg_def, MvPolynomial.uniformUnitScalingFractionRingAlgEquiv_algebraMap, MvPolynomial.uniformUnitScalingAlgEquiv_apply_X, hsmul]

  have hscale_f : ∀ (μ : kˣ) (w : RepresentationTheory.Quiver.GenericBaseChange.ArrowMatrixIndex m), MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ (φ (X w)) = φ (X w) := by
    intro μ w

    set μ' : (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))ˣ :=
      Units.map (algebraMap k (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))).toMonoidHom μ with hμ'
    have hμ'val : (μ' : FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))
        = algebraMap k (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) (μ : k) := by
      rw [hμ', Units.coe_map]; rfl

    have hentry : ∀ (i' : Fin n) (a b : Fin (m i')),
        ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
            (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m i').map ιB) a b
          = algebraMap (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k) (FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k))
              (X (⟨i', (a, b)⟩ : RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m)) := by
      intro i' a b
      simp only [Matrix.map_apply, RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix, RepresentationTheory.Quiver.GenericBaseChange.genericVertexMatrix]
      exact hιB_alg _

    have hAscale : ∀ i' : Fin n,
        ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
            (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m i').map ιB).map
            (MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ)
          = (μ' : FractionRing (MvPolynomial (RepresentationTheory.Quiver.GenericBaseChange.VertexMatrixIndex m) k)) •
            ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
              (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m i').map ιB) := by
      intro i'; ext a b
      rw [Matrix.map_apply, hentry, MvPolynomial.uniformUnitScalingFractionRingAlgEquiv_algebraMap, MvPolynomial.uniformUnitScalingAlgEquiv_apply_X, hsmul,
        Matrix.smul_apply, hentry, hμ'val, algebraMap_smul]

    have hVfix : (((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
          (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))))).map ιB).map (MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ)
        = ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
          (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))))).map ιB := by
      ext a b
      simp only [Matrix.map_apply]
      rw [AlgHom.commutes, AlgEquiv.commutes]

    have hCBinv : (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv (k := k)
          (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB
        = ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
          (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB)⁻¹ := by
      have h1 : ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
            (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB)
          * ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv (k := k)
            (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB) = 1 := by
        rw [← Matrix.map_mul, RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix_mul_inv,
          Matrix.map_one (⇑ιB) (map_zero ιB) (map_one ιB)]
      exact (Matrix.inv_eq_right_inv h1).symm

    have hCdet : IsUnit (((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
        (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB).det) := by
      rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
      exact (RepresentationTheory.Quiver.GenericBaseChange.isUnit_det_mappedGenericVertexMatrix (k := k)
        (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB

    have hmatrix : (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
          (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.2.1
        * (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
            (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))))
        * RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrixInv (k := k)
            (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB
        = (RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
              (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.2.1).map ιB
          * ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
              (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))))).map ιB
          * ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
              (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB)⁻¹ := by
      rw [Matrix.map_mul, Matrix.map_mul, hCBinv]
    have hexp : φ (X w)
        = (((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
              (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.2.1).map ιB)
          * (((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
              (Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))))).map ιB)
          * ((RepresentationTheory.Quiver.GenericBaseChange.mappedGenericVertexMatrix (k := k)
              (B := Localization (Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m))) m w.1).map ιB)⁻¹)
            w.2.2.2.1 w.2.2.2.2 := by
      rw [hφ, AlgHom.comp_apply, RepresentationTheory.Quiver.GenericBaseChange.genericBaseChangeAlgHom_apply_X, ← hmatrix, Matrix.map_apply]
    rw [hexp]
    exact (Matrix.map_apply).symm.trans
      (congrFun (congrFun (Matrix.map_mul_mul_inv_eq_self_of_common_unit_scaling (MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ) μ'
        (hAscale w.2.1) hVfix (hAscale w.1) hCdet) _) _)

  exact RepresentationTheory.Algebra.TranscendenceDegree.PolynomialScaling.card_lt_of_injective_mvPolynomial_algHom_to_fractionRing_of_scaled_element_of_fixed_generators φ hφ_inj g hg
    (fun μ => MvPolynomial.uniformUnitScalingFractionRingAlgEquiv m μ) hscale_g hscale_f

set_option linter.unusedFintypeInType false in

/-- For a nonzero dimension vector with finitely many base-change orbits, the representation space has strictly smaller dimension than the product of the vertex endomorphism spaces. -/
theorem Quiver.finrank_representation_space_lt_finrank_vertex_endomorphisms_of_finite_orbits (m : Fin n → ℕ) (hm : m ≠ 0)
    [Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))] :
    Module.finrank k (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)
      < Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hlt := Quiver.card_representation_coordinates_lt_card_vertex_endomorphism_coordinates_of_finite_orbits (k := k) m hm
  rwa [RepresentationTheory.Quiver.GenericBaseChange.card_arrowMatrixIndex, RepresentationTheory.Quiver.GenericBaseChange.card_vertexMatrixIndex, ← RepresentationTheory.Quiver.Representation.MatrixModel.finrank_matrixData (k := k) m,
    ← RepresentationTheory.Quiver.Representation.MatrixModel.finrank_vertexMatrixFamily (k := k) m] at hlt

end RepresentationTheory.Quiver.FiniteOrbitDimensionBounds
