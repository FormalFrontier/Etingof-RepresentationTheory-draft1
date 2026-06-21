import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialGLRightAction
import EtingofRepresentationTheory.Chapter5.DetLocalization

/-!
# The right-translation `GL_N`-action on the localization `O = A[det⁻¹]`

This file extends the right-translation representation `polyRightRep` on
`A = k[Xᵢⱼ]` (`PolynomialGLRightAction.lean`) to the determinant localization
`O = A[det⁻¹] = Localization.Away (detPoly k N)`. It is the representation the
det⁻¹-elimination kernel lemma (K) (issue #4694, route doc
`progress/kernel-lemma-K-route.md`) is phrased over: (K) is a statement about a
finite-dimensional right-`GL_N`-stable subspace `W ⊆ O`, so the `GL_N`-action on
`O` is the object the abstract statement quantifies over.

## Construction

For `g ∈ GL_N`, the right translation `rTransAlgHom (g : Matrix)` is an algebra
endomorphism of `A` carrying `detPoly` to `det g · detPoly` (`rTransAlgHom_det`).
Because `det g` is a unit, this sends the powers of `detPoly` to units of `O`, so
the localization universal property (`IsLocalization.lift`) extends it to a
`k`-algebra endomorphism `localRightAlgHom g : O →ₐ[k] O`. Multiplicativity in
`g` is inherited from `rTransAlgHom_mul` by the uniqueness of lifts
(`IsLocalization.ringHom_ext`), giving a genuine `Representation k GL_N O`
(`localRightRep`).

## Key facts

* `localRightRep_algebraMap` — the structure map `A → O` is `GL_N`-equivariant:
  `localRightRep g (algebraMap A O a) = algebraMap A O (polyRightRep g a)`. So
  the filtration submodule `A_0 = A ↪ O` is a subrepresentation, and `O` is an
  honest extension of the polynomial right-translation representation.
* `localRightRep_invSelf` — the formal inverse `det⁻¹ = invSelf detPoly`
  transforms by the inverse determinant character: `R_g det⁻¹ = (det g)⁻¹ · det⁻¹`.
  This is the `χ⁻¹` semi-invariance that drives the det-power filtration twist.
-/

namespace Etingof.LocalizationGLAction

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization

variable {k : Type*} [Field k] {N : ℕ}

/-- Abbreviation for the localization `O = A[det⁻¹]`. -/
local notation3 "O" => Localization.Away (detPoly k N)

/-- For a matrix `M`, the `k`-algebra hom `A →ₐ[k] O` obtained by composing the
right translation `rTransAlgHom M` with the structure map `A → O`. -/
noncomputable def rTransToAway (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] Localization.Away (detPoly k N) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N))).comp (rTransAlgHom M)

@[simp] theorem rTransToAway_apply (M : Matrix (Fin N) (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    rTransToAway M a = algebraMap _ (Localization.Away (detPoly k N)) (rTransAlgHom M a) :=
  rfl

/-- Determinant semi-invariance at the level of `detPoly` (a restatement of
`rTransAlgHom_det` phrased with `detPoly` so it rewrites without unfolding). -/
theorem rTransAlgHom_detPoly (M : Matrix (Fin N) (Fin N) k) :
    rTransAlgHom M (detPoly k N) = MvPolynomial.C M.det * detPoly k N :=
  rTransAlgHom_det M

/-- For `g ∈ GL_N`, the powers of `detPoly` map to units of `O` under
`rTransToAway (g : Matrix)`: `rTransAlgHom g detPoly = det g · detPoly` and both
`det g` and `detPoly` are units in `O`. -/
theorem isUnit_rTransToAway_detPoly_pow (g : Matrix.GeneralLinearGroup (Fin N) k)
    (y : Submonoid.powers (detPoly k N)) :
    IsUnit (rTransToAway (g : Matrix (Fin N) (Fin N) k) (y : MvPolynomial (Fin N × Fin N) k)) := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn]
  change IsUnit (rTransToAway (g : Matrix (Fin N) (Fin N) k) (detPoly k N ^ n))
  rw [rTransToAway_apply, map_pow, map_pow]
  refine IsUnit.pow n ?_
  -- `rTransAlgHom g detPoly = C (det g) * detPoly`
  rw [rTransAlgHom_detPoly, map_mul]
  refine IsUnit.mul ?_ ?_
  · -- `algebraMap (C (det g))` is a unit: `det g` is a unit in `k`
    have hdet : IsUnit ((g : Matrix (Fin N) (Fin N) k).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
    exact (hdet.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).map
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)))
  · -- `algebraMap detPoly` is a unit in the localization at `detPoly`
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (detPoly k N)) (detPoly k N)

/-- The right-translation `k`-algebra endomorphism of `O = A[det⁻¹]` attached to
`g ∈ GL_N`: the localization extension (`IsLocalization.liftAlgHom`) of the
right translation `rTransAlgHom (g : Matrix)` on `A`. Well-defined because `g`
carries `detPoly` to a unit multiple of itself
(`isUnit_rTransToAway_detPoly_pow`). -/
noncomputable def localRightAlgHom (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Localization.Away (detPoly k N) →ₐ[k] Localization.Away (detPoly k N) :=
  IsLocalization.liftAlgHom (f := rTransToAway (g : Matrix (Fin N) (Fin N) k))
    (isUnit_rTransToAway_detPoly_pow g)

/-- The defining property: `localRightAlgHom g` extends the right translation on
`A`. On the image of `a ∈ A` it is `algebraMap (rTransAlgHom (g) a)`. -/
@[simp] theorem localRightAlgHom_algebraMap (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    localRightAlgHom g (algebraMap _ (Localization.Away (detPoly k N)) a)
      = algebraMap _ _ (rTransAlgHom (g : Matrix (Fin N) (Fin N) k) a) := by
  simp only [localRightAlgHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  rfl

/-- `localRightAlgHom 1 = id`. -/
theorem localRightAlgHom_one :
    localRightAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)
      = AlgHom.id k (Localization.Away (detPoly k N)) := by
  apply IsLocalization.algHom_ext (R := k) (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (detPoly k N)) (B := Localization.Away (detPoly k N))
    (Submonoid.powers (detPoly k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change localRightAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
    = AlgHom.id k (Localization.Away (detPoly k N))
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
  rw [localRightAlgHom_algebraMap, AlgHom.id_apply, Units.val_one, rTransAlgHom_one,
    AlgHom.id_apply]

/-- Multiplicativity: `localRightAlgHom (g₁ g₂) = localRightAlgHom g₁ ∘ localRightAlgHom g₂`. -/
theorem localRightAlgHom_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
    localRightAlgHom (g₁ * g₂)
      = (localRightAlgHom g₁).comp (localRightAlgHom g₂) := by
  apply IsLocalization.algHom_ext (R := k) (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (detPoly k N)) (B := Localization.Away (detPoly k N))
    (Submonoid.powers (detPoly k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change localRightAlgHom (g₁ * g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
    = (localRightAlgHom g₁).comp (localRightAlgHom g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
  rw [localRightAlgHom_algebraMap, AlgHom.comp_apply, localRightAlgHom_algebraMap,
    localRightAlgHom_algebraMap, Units.val_mul, rTransAlgHom_mul, AlgHom.comp_apply]

/-- The **right-translation representation of `GL_N` on the localization
`O = A[det⁻¹]`**: `g ↦ localRightAlgHom g`. This is the representation the
det⁻¹-elimination kernel lemma (K) is phrased over — (K) constrains
finite-dimensional right-`GL_N`-stable subspaces of `O`. -/
noncomputable def localRightRep (k : Type*) [Field k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (Localization.Away (detPoly k N)) where
  toFun g := (localRightAlgHom g).toLinearMap
  map_one' := by
    change (localRightAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)).toLinearMap = _
    rw [localRightAlgHom_one]; rfl
  map_mul' g₁ g₂ := by
    change (localRightAlgHom (g₁ * g₂)).toLinearMap = _
    rw [localRightAlgHom_mul]; rfl

@[simp] theorem localRightRep_apply (g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (detPoly k N)) :
    localRightRep k N g x = localRightAlgHom g x :=
  rfl

/-- **The structure map `A → O` is `GL_N`-equivariant.** The right-translation
representation on `O` restricts on the polynomial subring to the right
translation `polyRightRep` on `A`; i.e. `A ↪ O` is a morphism of representations.
This identifies the filtration bottom `A_0 = A` with a subrepresentation of `O`. -/
theorem localRightRep_algebraMap (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    localRightRep k N g (algebraMap _ (Localization.Away (detPoly k N)) a)
      = algebraMap _ _ (polyRightRep k N g a) :=
  localRightAlgHom_algebraMap g a

end Etingof.LocalizationGLAction
