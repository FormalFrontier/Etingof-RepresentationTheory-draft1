import EtingofRepresentationTheory.Chapter8.BarResolution
import EtingofRepresentationTheory.Chapter8.IsoPrecompHomEquiv
import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

set_option backward.isDefEq.respectTransparency false

/-!
# Problem 8.2.6(ii): `CohomologyClass (barResolution) 1 ≃+ Problem3_9_1.Ext1`

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

/-- Unfolded form of `homEquivDeg`: it sends a cochain `z` to the linear map underlying
`iso.inv ≫ (toSingleEquiv z)`, where `iso : cochainComplex.X (-n) ≅ barObj n`. -/
lemma homEquivDeg_apply (n : ℕ) (z : Cochain (barCochainComplex k A W) (singleV A V) n) :
    homEquivDeg k A W V n z =
      (((Etingof.barResolution k A W).cochainComplexXIso (-(n : ℤ)) n (by push_cast; ring)).inv ≫
        Cochain.toSingleEquiv (K := barCochainComplex k A W) (X := ModuleCat.of A V)
          (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by push_cast; ring) z).hom := rfl

/-- The chain differential of the bar resolution in the standard indexing: `d (n+1) n = barDiff n`. -/
lemma barResolution_complex_d (n : ℕ) :
    (Etingof.barResolution k A W).complex.d (n + 1) n = ModuleCat.ofHom (barDiff k A W n) :=
  ChainComplex.of_d (fun n => barObj k A W n)
    (fun n => ModuleCat.ofHom (barDiff k A W n)) n

/-- Two `A`-linear maps `barModule (n+1) →ₗ[A] V` agree once they agree on the pure generators. -/
theorem barModule_hom_ext_V {n : ℕ} {F G : barModule k A W (n + 1) →ₗ[A] V}
    (h : ∀ (a₀ : A) (v : Fin (n + 1) → A) (w : W),
      F (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)) = G (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))) :
    F = G := by
  refine TensorProduct.AlgebraTensorModule.ext fun a₀ x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod r v =>
          simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            LinearMap.map_smul_of_tower]
          rw [h a₀ v w]
      | add x y hx hy =>
          rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

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
      LinearMap.coe_comp, LinearMap.coe_restrictScalars,
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
  change f ((1 : A) ⊗ₜ[k] (barCoeffOneEquiv k A W).symm (a ⊗ₜ[k] w)) = _
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
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-((1 : ℕ) : ℤ)) (by norm_num)
  have h2 : (2 : ℤ).negOnePow = 1 := by
    rw [show (2 : ℤ) = 2 * 1 by ring]; exact Int.negOnePow_two_mul 1
  have hd21 : (Etingof.barResolution k A W).complex.d 2 1 = ModuleCat.ofHom (barDiff k A W 1) :=
    barResolution_complex_d k A W 1
  rw [homEquivDeg_apply, homEquivDeg_apply,
    Cochain.δ_toSingleMk g (by norm_num) 2 (-((2 : ℕ) : ℤ)) (by norm_num), h2, one_smul,
    Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d (Etingof.barResolution k A W)
      (-((2 : ℕ) : ℤ)) (-((1 : ℕ) : ℤ)) 2 1 (by norm_num) (by norm_num), hd21]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_comp]
  rfl

/-- Under `homEquivDeg`, the coboundary `δ 0 1 β` becomes `-(barDiff 0)` precomposed:
`homEquivDeg 1 (δ 0 1 β) = -((homEquivDeg 0 β) ∘ₗ barDiff 0)`. -/
lemma homEquivDeg_δ_zero (β : Cochain (barCochainComplex k A W) (singleV A V) 0) :
    homEquivDeg k A W V 1 (δ 0 1 β) = -(homEquivDeg k A W V 0 β).comp (barDiff k A W 0) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective β (-((0 : ℕ) : ℤ)) (by norm_num)
  have hd10 : (Etingof.barResolution k A W).complex.d 1 0 = ModuleCat.ofHom (barDiff k A W 0) :=
    barResolution_complex_d k A W 0
  rw [homEquivDeg_apply, homEquivDeg_apply,
    Cochain.δ_toSingleMk g (by norm_num) 1 (-((1 : ℕ) : ℤ)) (by norm_num), Int.negOnePow_one,
    Units.neg_smul, one_smul, map_neg, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d (Etingof.barResolution k A W)
      (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) 1 0 (by norm_num) (by norm_num), hd10]
  simp only [Preadditive.comp_neg, Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_neg,
    ModuleCat.hom_comp]
  rfl

/-! ### Cocycle correspondence -/

/-- The image `Ψ1 z` is a `Problem3_9_1`-cocycle iff the cochain `z` is a cocycle
(`δ 1 2 z = 0`). -/
lemma isCocycle_Ψ1_iff (z : Cochain (barCochainComplex k A W) (singleV A V) 1) :
    Problem3_9_1.IsCocycle k A V W (Ψ1 k A W V z) ↔ δ 1 2 z = 0 := by
  have hinj : δ 1 2 z = 0 ↔ (homEquivDeg k A W V 1 z).comp (barDiff k A W 1) = 0 := by
    rw [← homEquivDeg_δ_one]
    exact (map_eq_zero_iff _ (homEquivDeg k A W V 2).injective).symm
  rw [hinj]
  set f := homEquivDeg k A W V 1 z with hfdef
  -- `Ψ1 z a w = f (1 ⊗ (tprod ![a] ⊗ w))`.
  have hF : ∀ (a : A) (w : W), Ψ1 k A W V z a w = f ((1 : A) ⊗ₜ[k] (tprod k ![a] ⊗ₜ[k] w)) := by
    intro a w; exact coeffEquiv1_apply k A W V f a w
  -- The core face computation on the spanning generators.
  have core : ∀ (a b : A) (w : W),
      f (barDiff k A W 1 ((1 : A) ⊗ₜ[k] (tprod k ![a, b] ⊗ₜ[k] w)))
        = a • Ψ1 k A W V z b w - Ψ1 k A W V z (a * b) w + Ψ1 k A W V z a (b • w) := by
    intro a b w
    have htail : Fin.tail (![a, b] : Fin 2 → A) = ![b] := by funext i; fin_cases i; rfl
    have hinit : Fin.init (![a, b] : Fin 2 → A) = ![a] := by funext i; fin_cases i; rfl
    have hcon : Fin.contractNth (0 : Fin 1).castSucc (· * ·) (![a, b] : Fin 2 → A) = ![a * b] := by
      funext i; fin_cases i; simp [Fin.contractNth]
    have hlast : (![a, b] : Fin 2 → A) (Fin.last 1) = b := rfl
    rw [barDiff_tmul_tprod]
    simp only [Fin.sum_univ_one, htail, hinit, hcon, hlast, Matrix.cons_val_zero,
      Fin.val_zero, one_mul, pow_succ,
      pow_zero, mul_neg, neg_neg, mul_one, neg_smul, one_smul, map_add, map_neg,
      LinearMap.map_smul_of_tower]
    rw [show a ⊗ₜ[k] (tprod k ![b] ⊗ₜ[k] w)
          = a • ((1 : A) ⊗ₜ[k] (tprod k ![b] ⊗ₜ[k] w)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, ← hF b w, ← hF (a * b) w, ← hF a (b • w)]
    abel
  constructor
  · intro hcocy
    apply barModule_hom_ext_V
    intro a₀ v w
    set a := v 0 with ha
    set b := v 1 with hb
    have hv : v = ![a, b] := by funext i; fin_cases i <;> rfl
    have hlin : a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)
        = a₀ • ((1 : A) ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.zero_apply, hlin, map_smul, LinearMap.comp_apply, hv, core]
    have hc := LinearMap.congr_fun (hcocy a b) w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Problem3_9_1.rho,
      Algebra.lsmul_coe] at hc
    rw [hc]
    rw [show a • Ψ1 k A W V z b w - (a • Ψ1 k A W V z b w + Ψ1 k A W V z a (b • w))
        + Ψ1 k A W V z a (b • w) = 0 by abel, smul_zero]
  · intro hcomp a b
    ext w
    have h0 : f (barDiff k A W 1 ((1 : A) ⊗ₜ[k] (tprod k ![a, b] ⊗ₜ[k] w))) = 0 :=
      LinearMap.congr_fun hcomp _
    rw [core] at h0
    simp only [Problem3_9_1.rho, LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe]
    rw [eq_comm, ← sub_eq_zero]
    rw [show a • Ψ1 k A W V z b w + Ψ1 k A W V z a (b • w) - Ψ1 k A W V z (a * b) w
        = a • Ψ1 k A W V z b w - Ψ1 k A W V z (a * b) w + Ψ1 k A W V z a (b • w) by abel]
    exact h0

/-! ### Coboundary correspondence -/

/-- `Ψ1` sends the coboundary of a degree-`0` cochain to the `Problem3_9_1`-coboundary of `-Ψ0 β`. -/
lemma Ψ1_δ_zero_eq (β : Cochain (barCochainComplex k A W) (singleV A V) 0) :
    Ψ1 k A W V (δ 0 1 β) = Problem3_9_1.coboundaryOf k A V W (-(Ψ0 k A W V β)) := by
  set g0 := homEquivDeg k A W V 0 β with hg0
  have hΨ0 : ∀ w : W, Ψ0 k A W V β w = g0 ((1 : A) ⊗ₜ[k] (barCoeffZeroEquiv k A W).symm w) :=
    fun w => coeffEquiv0_apply k A W V g0 w
  have hbc : ∀ (u : Fin 0 → A) (y : W),
      (barCoeffZeroEquiv k A W).symm y = tprod k u ⊗ₜ[k] y := by
    intro u y; rw [LinearEquiv.symm_apply_eq]; exact (barCoeffZeroEquiv_tprod k A W u y).symm
  have core0 : ∀ (a : A) (w : W),
      g0 (barDiff k A W 0 ((1 : A) ⊗ₜ[k] (tprod k ![a] ⊗ₜ[k] w)))
        = a • Ψ0 k A W V β w - Ψ0 k A W V β (a • w) := by
    intro a w
    have hlast0 : (![a] : Fin 1 → A) (Fin.last 0) = a := rfl
    rw [barDiff_tmul_tprod]
    simp only [Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, one_mul, pow_one,
      zero_add, neg_smul, one_smul, map_add, map_neg,
      LinearMap.map_smul_of_tower]
    rw [hlast0, ← hbc (Fin.tail ![a]) w, ← hbc (Fin.init ![a]) (a • w),
      show a ⊗ₜ[k] (barCoeffZeroEquiv k A W).symm w
          = a • ((1 : A) ⊗ₜ[k] (barCoeffZeroEquiv k A W).symm w) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      g0.map_smul, ← hΨ0 w, ← hΨ0 (a • w)]
    abel
  have hΨ1 : Ψ1 k A W V (δ 0 1 β)
      = coeffEquiv1 k A W V (-(g0.comp (barDiff k A W 0))) := by
    change coeffEquiv1 k A W V (homEquivDeg k A W V 1 (δ 0 1 β)) = _
    rw [homEquivDeg_δ_zero]
  ext a w
  rw [Problem3_9_1.coboundaryOf_apply, hΨ1, coeffEquiv1_apply]
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, smul_neg]
  rw [core0]
  abel

/-- `Ψ1` sends the coboundary of a degree-`0` cochain to a `Problem3_9_1`-coboundary. -/
lemma Ψ1_δ_zero_mem_coboundaries
    (β : Cochain (barCochainComplex k A W) (singleV A V) 0) :
    Ψ1 k A W V (δ 0 1 β) ∈ Problem3_9_1.coboundaries k A V W := by
  rw [Ψ1_δ_zero_eq]
  exact Submodule.subset_span (Set.mem_range_self _)

/-! ### The isomorphism -/

/-- The degree-`1` bar cocycles are additively equivalent to the cocycles of
Problem 3.9.1.  On underlying cochains this is exactly the tensor–hom chart `Ψ1`. -/
noncomputable def barCocycleEquivProblem3Cocycle :
    Cocycle (barCochainComplex k A W) (singleV A V) 1 ≃+
      ↥(Problem3_9_1.cocycles k A V W) := by
  have hcocy : (cocycle (barCochainComplex k A W) (singleV A V) 1).map
        ((Ψ1 k A W V).toAddMonoidHom)
      = (Problem3_9_1.cocycles k A V W).toAddSubgroup := by
    ext F
    simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom,
      Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (isCocycle_Ψ1_iff k A W V z).mpr
        ((Cocycle.mem_iff 1 2 (by norm_num) z).mp hz)
    · intro hF
      refine ⟨(Ψ1 k A W V).symm F,
        (Cocycle.mem_iff 1 2 (by norm_num) _).mpr ?_, by simp⟩
      rw [← isCocycle_Ψ1_iff, AddEquiv.apply_symm_apply]
      exact hF
  exact
    ((Ψ1 k A W V).addSubgroupMap
      (cocycle (barCochainComplex k A W) (singleV A V) 1)).trans
      (AddEquiv.addSubgroupCongr hcocy)

@[simp]
theorem barCocycleEquivProblem3Cocycle_coe
    (z : Cocycle (barCochainComplex k A W) (singleV A V) 1) :
    ((barCocycleEquivProblem3Cocycle k A W V z :
        ↥(Problem3_9_1.cocycles k A V W)) : A →ₗ[k] W →ₗ[k] V) =
      Ψ1 k A W V (z : Cochain (barCochainComplex k A W) (singleV A V) 1) :=
  rfl

/-- On elements, the cocycle comparison is the tensor–hom chart: evaluate the bar cochain on
`1 ⊗ (a ⊗ w)`. -/
@[simp]
theorem barCocycleEquivProblem3Cocycle_apply
    (z : Cocycle (barCochainComplex k A W) (singleV A V) 1) (a : A) (w : W) :
    (barCocycleEquivProblem3Cocycle k A W V z :
        ↥(Problem3_9_1.cocycles k A V W)).1 a w =
      homEquivDeg k A W V 1
        (z : Cochain (barCochainComplex k A W) (singleV A V) 1)
        ((1 : A) ⊗ₜ[k] ((tprod k ![a]) ⊗ₜ[k] w)) := by
  rw [barCocycleEquivProblem3Cocycle_coe]
  exact coeffEquiv1_apply k A W V _ a w

/-- The Problem-3.9.1 coboundaries, regarded as an additive subgroup of its cocycles. -/
abbrev problem3CoboundariesInCocycles (k A V W : Type u)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    AddSubgroup ↥(Problem3_9_1.cocycles k A V W) :=
  ((Problem3_9_1.coboundaries k A V W).submoduleOf
    (Problem3_9_1.cocycles k A V W)).toAddSubgroup

/-- The bar-coboundary subgroup is carried exactly onto the Problem-3.9.1
coboundary subgroup by `barCocycleEquivProblem3Cocycle`. -/
theorem barCocycleEquivProblem3Cocycle_map_coboundaries :
    (coboundaries (barCochainComplex k A W) (singleV A V) 1).map
        (barCocycleEquivProblem3Cocycle k A W V).toAddMonoidHom =
      problem3CoboundariesInCocycles k A V W := by
  let e : Cocycle (barCochainComplex k A W) (singleV A V) 1 ≃+
      ↥(Problem3_9_1.cocycles k A V W) :=
    barCocycleEquivProblem3Cocycle k A W V
  have hmem : ∀ c : ↥(Problem3_9_1.cocycles k A V W),
      c ∈ (Problem3_9_1.coboundaries k A V W).submoduleOf (Problem3_9_1.cocycles k A V W)
        ↔ (↑c : A →ₗ[k] W →ₗ[k] V) ∈ Problem3_9_1.coboundaries k A V W :=
    fun _ => Submodule.mem_comap
  ext c
  simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom,
    Submodule.mem_toAddSubgroup, hmem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x 0 (by norm_num)).mp hx
    rw [barCocycleEquivProblem3Cocycle_coe, ← hβ, Ψ1_δ_zero_eq]
    exact Submodule.subset_span (Set.mem_range_self _)
  · intro hc
    obtain ⟨X, hX⟩ := (Problem3_9_1.mem_coboundaries_iff k A V W _).mp hc
    refine ⟨e.symm c, ?_, by simp [e]⟩
    rw [mem_coboundaries_iff _ 0 (by norm_num)]
    refine ⟨(Ψ0 k A W V).symm (-X), ?_⟩
    apply (Ψ1 k A W V).injective
    have h1 : Ψ1 k A W V (↑(e.symm c)) = (↑c : A →ₗ[k] W →ₗ[k] V) := by
      rw [← barCocycleEquivProblem3Cocycle_coe k A W V (e.symm c)]
      simp [e]
    have hcoe : (↑(e.symm c) : Cochain (barCochainComplex k A W) (singleV A V) 1)
        = (Ψ1 k A W V).symm (↑c : A →ₗ[k] W →ₗ[k] V) :=
      (AddEquiv.eq_symm_apply (Ψ1 k A W V)).mpr h1
    rw [Ψ1_δ_zero_eq, AddEquiv.apply_symm_apply, neg_neg, hcoe,
      AddEquiv.apply_symm_apply, hX]

/-- **Problem 8.2.6(ii).** The degree-`1` cohomology of `Hom(barResolution, V)` is
canonically isomorphic to `Ext¹` in the cocycle/coboundary presentation of Problem 3.9.1. -/
noncomputable def cohomologyClassEquivExt1 :
    CohomologyClass (barCochainComplex k A W) (singleV A V) 1
      ≃+ Problem3_9_1.Ext1 k A V W :=
  QuotientAddGroup.congr _ _ (barCocycleEquivProblem3Cocycle k A W V)
    (barCocycleEquivProblem3Cocycle_map_coboundaries k A W V)

set_option maxHeartbeats 1000000 in
-- Unfolding the quotient congruence is expensive because its source is a nested
-- cocycle/coboundary subtype quotient, so give this representative formula local headroom.
/-- The canonical cohomology comparison sends a represented bar-cohomology class to the
class of the corresponding Problem-3.9.1 cocycle. -/
@[simp]
theorem cohomologyClassEquivExt1_mk
    (z : Cocycle (barCochainComplex k A W) (singleV A V) 1) :
    cohomologyClassEquivExt1 k A W V (CohomologyClass.mk z) =
      QuotientAddGroup.mk'
        (problem3CoboundariesInCocycles k A V W)
        (barCocycleEquivProblem3Cocycle k A W V z) :=
  rfl

end Etingof
