import EtingofRepresentationTheory.Chapter8.BarResolution
import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Problem 8.2.6(ii), the crux: `CohomologyClass (barResolution) 1 ≃+ Problem3_9_1.Ext1`

`Problem_8_2_6_ii` reduces (via `ProjectiveResolution.extAddEquivCohomologyClass` applied to the
relative bar resolution `Etingof.barResolution k A W`) to a single additive isomorphism between the
degree-`1` cohomology of the `Hom(−, V)` cochain complex of the bar resolution and the
cocycle/coboundary group `Problem3_9_1.Ext1 k A V W`. This file supplies that isomorphism as
`Etingof.cohomologyClassEquivExt1`.

The construction identifies a degree-`n` cochain into the single complex `V[0]` with an
`A`-linear map `barModule n →ₗ[A] V` (`homEquivDeg`), then with a `k`-multilinear coefficient map
via the tensor–hom adjunction (`coeffEquiv0`, `coeffEquiv1`). Under these identifications the
cochain differential `δ` becomes precomposition with the bar differential `barDiff`, so the
degree-`1` cocycle condition becomes `Problem3_9_1.IsCocycle` and degree-`1` coboundaries become
`Problem3_9_1.coboundaryOf`. Assembling the two quotients gives the isomorphism.
-/

universe u

namespace Etingof

open CategoryTheory TensorProduct PiTensorProduct CochainComplex.HomComplex
open Etingof.BarResolution

variable (k A W V : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- Precomposition with an isomorphism, as an additive equivalence of hom-groups. -/
def isoPrecompHomEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y : C} (α : X ≅ X') :
    (X ⟶ Y) ≃+ (X' ⟶ Y) where
  toFun f := α.inv ≫ f
  invFun g := α.hom ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

@[simp] lemma isoPrecompHomEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (f : X ⟶ Y) :
    isoPrecompHomEquiv α f = α.inv ≫ f := rfl

@[simp] lemma isoPrecompHomEquiv_symm_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (g : X' ⟶ Y) :
    (isoPrecompHomEquiv α).symm g = α.hom ≫ g := rfl

/-- The bar cochain complex `Hom(barResolution, −)` lives here: it is the integer-graded
extension of the bar chain complex. -/
noncomputable abbrev barCochainComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (Etingof.barResolution k A W).cochainComplex

/-- The single complex `V[0]`, target of the cochains. -/
noncomputable abbrev singleV : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A V)

/-- A degree-`n` cochain of `barResolution` into `V[0]` is the same as an `A`-linear map
`barModule n →ₗ[A] V`. -/
noncomputable def homEquivDeg (n : ℕ) :
    Cochain (barCochainComplex k A W) (singleV A V) n ≃+ (barModule k A W n →ₗ[A] V) :=
  (Cochain.toSingleEquiv (K := barCochainComplex k A W) (X := ModuleCat.of A V)
      (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by push_cast; ring)).trans
    ((isoPrecompHomEquiv
        ((Etingof.barResolution k A W).cochainComplexXIso (-(n : ℤ)) n (by push_cast; ring))).trans
      ModuleCat.homAddEquiv)

/-- The `k`-linear identification `barCoeff 1 = (⨂¹A) ⊗ W ≃ₗ A ⊗ W`. -/
noncomputable def barCoeffOneEquiv : barCoeff k A W 1 ≃ₗ[k] A ⊗[k] W :=
  TensorProduct.congr (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) (LinearEquiv.refl k W)

@[simp] lemma barCoeffOneEquiv_symm_tmul (a : A) (w : W) :
    (barCoeffOneEquiv k A W).symm (a ⊗ₜ[k] w) = (tprod k ![a]) ⊗ₜ[k] w := by
  have h : (PiTensorProduct.subsingletonEquiv (s := fun _ : Fin 1 => A) (0 : Fin 1)).symm a
      = tprod k ![a] := by
    rw [PiTensorProduct.subsingletonEquiv_symm_apply']
    congr 1
    funext i; fin_cases i; rfl
  simp only [barCoeffOneEquiv, TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, h]

/-- Tensor–hom adjunction for the (possibly noncommutative) algebra `A`: `A`-linear maps out of
`A ⊗[k] X` are the same as `k`-linear maps out of `X`, via `x ↦ 1 ⊗ x`. Built by hand, since the
commutative `LinearMap.liftBaseChangeEquiv` requires `A` commutative. -/
noncomputable def coeffHomEquiv (X : Type u) [AddCommGroup X] [Module k X] :
    (A ⊗[k] X →ₗ[A] V) ≃+ (X →ₗ[k] V) where
  toFun f := (f.restrictScalars k).comp (TensorProduct.mk k A X 1)
  invFun g := AlgebraTensorModule.lift (LinearMap.toSpanSingleton A (X →ₗ[k] V) g)
  left_inv f := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    simp only [AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, TensorProduct.mk_apply]
    rw [← f.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  right_inv g := by
    ext x
    simp only [AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, TensorProduct.mk_apply, one_smul]
  map_add' f f' := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, TensorProduct.mk_apply]

@[simp] lemma coeffHomEquiv_apply (X : Type u) [AddCommGroup X] [Module k X]
    (f : A ⊗[k] X →ₗ[A] V) (x : X) :
    coeffHomEquiv k A V X f x = f ((1 : A) ⊗ₜ[k] x) := rfl

/-- An `A`-linear map `barModule 1 →ₗ[A] V` is the same data as a `k`-bilinear cocycle-shaped map
`A →ₗ[k] W →ₗ[k] V`, via the tensor–hom adjunction and `⨂¹A ≅ A`. -/
noncomputable def coeffEquiv1 : (barModule k A W 1 →ₗ[A] V) ≃+ (A →ₗ[k] W →ₗ[k] V) :=
  (coeffHomEquiv k A V (barCoeff k A W 1)).trans
    (((LinearEquiv.arrowCongr (barCoeffOneEquiv k A W) (LinearEquiv.refl k V)).toAddEquiv).trans
      (TensorProduct.lift.equiv (RingHom.id k) A W V).symm.toAddEquiv)

lemma coeffEquiv1_apply (f : barModule k A W 1 →ₗ[A] V) (a : A) (w : W) :
    coeffEquiv1 k A W V f a w = f ((1 : A) ⊗ₜ[k] ((tprod k ![a]) ⊗ₜ[k] w)) := by
  show f ((1 : A) ⊗ₜ[k] (barCoeffOneEquiv k A W).symm (a ⊗ₜ[k] w)) = _
  rw [barCoeffOneEquiv_symm_tmul]

/-- An `A`-linear map `barModule 0 →ₗ[A] V` is the same data as a `k`-linear map `W →ₗ[k] V`. -/
noncomputable def coeffEquiv0 : (barModule k A W 0 →ₗ[A] V) ≃+ (W →ₗ[k] V) :=
  (coeffHomEquiv k A V (barCoeff k A W 0)).trans
    (LinearEquiv.arrowCongr (barCoeffZeroEquiv k A W) (LinearEquiv.refl k V)).toAddEquiv

lemma coeffEquiv0_apply (f : barModule k A W 0 →ₗ[A] V) (w : W) :
    coeffEquiv0 k A W V f w = f ((1 : A) ⊗ₜ[k] (barCoeffZeroEquiv k A W).symm w) := rfl

/-- The degree-`1` cochain-to-cocycle map: `Cochain 1 ≃+ (A →ₗ W →ₗ V)`. -/
noncomputable def Ψ1 :
    Cochain (barCochainComplex k A W) (singleV A V) 1 ≃+ (A →ₗ[k] W →ₗ[k] V) :=
  (homEquivDeg k A W V 1).trans (coeffEquiv1 k A W V)

/-- The degree-`0` cochain-to-map: `Cochain 0 ≃+ (W →ₗ V)`. -/
noncomputable def Ψ0 :
    Cochain (barCochainComplex k A W) (singleV A V) 0 ≃+ (W →ₗ[k] V) :=
  (homEquivDeg k A W V 0).trans (coeffEquiv0 k A W V)

/-! ### The differential becomes precomposition with `barDiff` -/

/-- Under `homEquivDeg`, the cochain differential `δ 1 2` becomes precomposition with
`barDiff 1`: `homEquivDeg 2 (δ 1 2 z) = (homEquivDeg 1 z) ∘ₗ barDiff 1`. -/
lemma homEquivDeg_δ_one (z : Cochain (barCochainComplex k A W) (singleV A V) 1) :
    homEquivDeg k A W V 2 (δ 1 2 z) = (homEquivDeg k A W V 1 z).comp (barDiff k A W 1) := by
  sorry

/-- Under `homEquivDeg`, the coboundary `δ 0 1 β` becomes `-(barDiff 0)` precomposed:
`homEquivDeg 1 (δ 0 1 β) = -((homEquivDeg 0 β) ∘ₗ barDiff 0)`. -/
lemma homEquivDeg_δ_zero (β : Cochain (barCochainComplex k A W) (singleV A V) 0) :
    homEquivDeg k A W V 1 (δ 0 1 β) = -(homEquivDeg k A W V 0 β).comp (barDiff k A W 0) := by
  sorry

/-! ### Cocycle correspondence -/

/-- The image `Ψ1 z` is a `Problem3_9_1`-cocycle iff the cochain `z` is a cocycle
(`δ 1 2 z = 0`). -/
lemma isCocycle_Ψ1_iff (z : Cochain (barCochainComplex k A W) (singleV A V) 1) :
    Problem3_9_1.IsCocycle k A V W (Ψ1 k A W V z) ↔ δ 1 2 z = 0 := by
  sorry

/-! ### Coboundary correspondence -/

/-- `Ψ1` sends the coboundary of a degree-`0` cochain to a `Problem3_9_1`-coboundary. -/
lemma Ψ1_δ_zero_mem_coboundaries
    (β : Cochain (barCochainComplex k A W) (singleV A V) 0) :
    Ψ1 k A W V (δ 0 1 β) ∈ Problem3_9_1.coboundaries k A V W := by
  sorry

/-! ### Assembly -/

/-- **Problem 8.2.6(ii), crux.** The degree-`1` cohomology of `Hom(barResolution, V)` is
canonically isomorphic to `Ext¹` in the cocycle/coboundary presentation of Problem 3.9.1. -/
noncomputable def cohomologyClassEquivExt1 :
    CohomologyClass (barCochainComplex k A W) (singleV A V) 1
      ≃+ Problem3_9_1.Ext1 k A V W := by
  sorry

end Etingof
