/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.TensorBarResolution
import RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv
import RepresentationTheory.Algebra.Module.ExtensionCocycles
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

set_option backward.isDefEq.respectTransparency false


















universe u

namespace RepresentationTheory.HomologicalAlgebra.CochainComplexComparison

open _root_.CategoryTheory TensorProduct PiTensorProduct CochainComplex.HomComplex
open RepresentationTheory.Algebra.Homology.TensorBarResolution

variable (k A W V : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- An auxiliary integer-indexed cochain complex of A-modules associated to a k-algebra and an A-module. -/


noncomputable abbrev auxiliaryCochainComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).cochainComplex

/-- An auxiliary integer-indexed cochain complex of A-modules attached to an A-module. -/

noncomputable abbrev auxiliaryTargetCochainComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A V)

/-- An additive equivalence between degree-n cochains in the auxiliary Hom complex and linear maps from the degree-n auxiliary module. -/


noncomputable def cochainLinearMapEquiv (n : ℕ) :
    Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) n ≃+ (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W n →ₗ[A] V) :=
  (Cochain.toSingleEquiv (K := auxiliaryCochainComplex k A W) (X := ModuleCat.of A V)
      (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by push_cast; ring)).trans
    ((RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv.homPrecomposeIsoAddEquiv
        ((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).cochainComplexXIso (-(n : ℤ)) n (by push_cast; ring))).trans
      ModuleCat.homAddEquiv)

/-- The cochain linear-map equivalence is obtained from the corresponding morphism through the projective-resolution cochain comparison. -/


lemma cochainLinearMapEquiv_apply (n : ℕ) (z : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) n) :
    cochainLinearMapEquiv k A W V n z =
      (((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).cochainComplexXIso (-(n : ℤ)) n (by push_cast; ring)).inv ≫
        Cochain.toSingleEquiv (K := auxiliaryCochainComplex k A W) (X := ModuleCat.of A V)
          (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by push_cast; ring) z).hom := rfl

/-- The differential in the displayed projective resolution complex is the associated auxiliary module morphism. -/

lemma projectiveResolution_d_eq_auxiliary (n : ℕ) :
    (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.d (n + 1) n = ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W n) :=
  ChainComplex.of_d (fun n => RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTermModule k A W n)
    (fun n => ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W n)) n

/-- Two linear maps from the successor-degree auxiliary module are equal when they agree on all displayed pure tensor generators. -/

theorem linearMap_ext_of_tmul_tprod_eq {n : ℕ} {F G : RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W (n + 1) →ₗ[A] V}
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

/-- A linear equivalence from the degree-one auxiliary module to the tensor product of A with W over k. -/

noncomputable def degreeOneLinearEquivTensorProduct : RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTail k A W 1 ≃ₗ[k] A ⊗[k] W :=
  TensorProduct.congr (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) (LinearEquiv.refl k W)

/-- The inverse degree-one linear equivalence sends a pure tensor to the corresponding nested tensor built from a one-entry tuple. -/
@[simp] lemma degreeOneLinearEquivTensorProduct_symm_tmul (a : A) (w : W) :
    (degreeOneLinearEquivTensorProduct k A W).symm (a ⊗ₜ[k] w) = (tprod k ![a]) ⊗ₜ[k] w := by
  have h : (PiTensorProduct.subsingletonEquiv (s := fun _ : Fin 1 => A) (0 : Fin 1)).symm a
      = tprod k ![a] := by
    rw [PiTensorProduct.subsingletonEquiv_symm_apply']
    congr 1
    funext i; fin_cases i; rfl
  simp only [degreeOneLinearEquivTensorProduct, TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, h]

/-- An additive equivalence between A-linear maps out of A tensor X and k-linear maps out of X. -/



noncomputable def scalarExtensionLinearMapEquiv (X : Type u) [AddCommGroup X] [Module k X] :
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

/-- The scalar-extension linear-map equivalence evaluates a map at x by applying it to the pure tensor of one and x. -/
@[simp] lemma scalarExtensionLinearMapEquiv_apply (X : Type u) [AddCommGroup X] [Module k X]
    (f : A ⊗[k] X →ₗ[A] V) (x : X) :
    scalarExtensionLinearMapEquiv k A V X f x = f ((1 : A) ⊗ₜ[k] x) := rfl

/-- An additive equivalence between linear maps from the degree-one auxiliary module and curried k-linear maps on A and W. -/


noncomputable def degreeOneLinearMapEquiv : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W 1 →ₗ[A] V) ≃+ (A →ₗ[k] W →ₗ[k] V) :=
  (scalarExtensionLinearMapEquiv k A V (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTail k A W 1)).trans
    (((LinearEquiv.arrowCongr (degreeOneLinearEquivTensorProduct k A W) (LinearEquiv.refl k V)).toAddEquiv).trans
      (TensorProduct.lift.equiv (RingHom.id k) A W V).symm.toAddEquiv)

/-- The degree-one linear-map equivalence evaluates by applying the original map to the canonical nested tensor of its two arguments. -/
lemma degreeOneLinearMapEquiv_apply (f : RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W 1 →ₗ[A] V) (a : A) (w : W) :
    degreeOneLinearMapEquiv k A W V f a w = f ((1 : A) ⊗ₜ[k] ((tprod k ![a]) ⊗ₜ[k] w)) := by
  change f ((1 : A) ⊗ₜ[k] (degreeOneLinearEquivTensorProduct k A W).symm (a ⊗ₜ[k] w)) = _
  rw [degreeOneLinearEquivTensorProduct_symm_tmul]

/-- An additive equivalence between linear maps from the degree-zero auxiliary module and k-linear maps from W. -/

noncomputable def degreeZeroLinearMapEquiv : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W 0 →ₗ[A] V) ≃+ (W →ₗ[k] V) :=
  (scalarExtensionLinearMapEquiv k A V (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTail k A W 0)).trans
    (LinearEquiv.arrowCongr (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W) (LinearEquiv.refl k V)).toAddEquiv

/-- The degree-zero linear-map equivalence evaluates by applying the original map to the canonical tensor representative of an element of W. -/
lemma degreeZeroLinearMapEquiv_apply (f : RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm k A W 0 →ₗ[A] V) (w : W) :
    degreeZeroLinearMapEquiv k A W V f w = f ((1 : A) ⊗ₜ[k] (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W).symm w) := rfl

/-- An additive equivalence between degree-one cochains in the auxiliary Hom complex and curried k-linear maps on A and W. -/

noncomputable def degreeOneCochainLinearMapEquiv :
    Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1 ≃+ (A →ₗ[k] W →ₗ[k] V) :=
  (cochainLinearMapEquiv k A W V 1).trans (degreeOneLinearMapEquiv k A W V)

/-- An additive equivalence between degree-zero cochains in the auxiliary Hom complex and k-linear maps from W to V. -/

noncomputable def degreeZeroCochainLinearMapEquiv :
    Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 0 ≃+ (W →ₗ[k] V) :=
  (cochainLinearMapEquiv k A W V 0).trans (degreeZeroLinearMapEquiv k A W V)



/-- Under the cochain linear-map equivalence, the coboundary from degree one is composition with the degree-one auxiliary differential. -/


lemma cochainLinearMapEquiv_coboundary_one (z : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) :
    cochainLinearMapEquiv k A W V 2 (δ 1 2 z) = (cochainLinearMapEquiv k A W V 1 z).comp (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 1) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-((1 : ℕ) : ℤ)) (by norm_num)
  have h2 : (2 : ℤ).negOnePow = 1 := by
    rw [show (2 : ℤ) = 2 * 1 by ring]; exact Int.negOnePow_two_mul 1
  have hd21 : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.d 2 1 = ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 1) :=
    projectiveResolution_d_eq_auxiliary k A W 1
  rw [cochainLinearMapEquiv_apply, cochainLinearMapEquiv_apply,
    Cochain.δ_toSingleMk g (by norm_num) 2 (-((2 : ℕ) : ℤ)) (by norm_num), h2, one_smul,
    Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W)
      (-((2 : ℕ) : ℤ)) (-((1 : ℕ) : ℤ)) 2 1 (by norm_num) (by norm_num), hd21]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_comp]
  rfl

/-- Under the cochain linear-map equivalence, the coboundary from degree zero is the negative of composition with the degree-zero auxiliary differential. -/


lemma cochainLinearMapEquiv_coboundary_zero (β : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 0) :
    cochainLinearMapEquiv k A W V 1 (δ 0 1 β) = -(cochainLinearMapEquiv k A W V 0 β).comp (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 0) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective β (-((0 : ℕ) : ℤ)) (by norm_num)
  have hd10 : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.d 1 0 = ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 0) :=
    projectiveResolution_d_eq_auxiliary k A W 0
  rw [cochainLinearMapEquiv_apply, cochainLinearMapEquiv_apply,
    Cochain.δ_toSingleMk g (by norm_num) 1 (-((1 : ℕ) : ℤ)) (by norm_num), Int.negOnePow_one,
    Units.neg_smul, one_smul, map_neg, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W)
      (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) 1 0 (by norm_num) (by norm_num), hd10]
  simp only [Preadditive.comp_neg, Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_neg,
    ModuleCat.hom_comp]
  rfl



/-- The auxiliary condition on the degree-one linear-map transform holds exactly when the cochain has zero coboundary. -/


lemma auxiliaryCondition_iff_coboundary_eq_zero (z : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.IsExtensionCocycle k A V W (degreeOneCochainLinearMapEquiv k A W V z) ↔ δ 1 2 z = 0 := by
  have hinj : δ 1 2 z = 0 ↔ (cochainLinearMapEquiv k A W V 1 z).comp (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 1) = 0 := by
    rw [← cochainLinearMapEquiv_coboundary_one]
    exact (map_eq_zero_iff _ (cochainLinearMapEquiv k A W V 2).injective).symm
  rw [hinj]
  set f := cochainLinearMapEquiv k A W V 1 z with hfdef

  have hF : ∀ (a : A) (w : W), degreeOneCochainLinearMapEquiv k A W V z a w = f ((1 : A) ⊗ₜ[k] (tprod k ![a] ⊗ₜ[k] w)) := by
    intro a w; exact degreeOneLinearMapEquiv_apply k A W V f a w

  have core : ∀ (a b : A) (w : W),
      f (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 1 ((1 : A) ⊗ₜ[k] (tprod k ![a, b] ⊗ₜ[k] w)))
        = a • degreeOneCochainLinearMapEquiv k A W V z b w - degreeOneCochainLinearMapEquiv k A W V z (a * b) w + degreeOneCochainLinearMapEquiv k A W V z a (b • w) := by
    intro a b w
    have htail : Fin.tail (![a, b] : Fin 2 → A) = ![b] := by funext i; fin_cases i; rfl
    have hinit : Fin.init (![a, b] : Fin 2 → A) = ![a] := by funext i; fin_cases i; rfl
    have hcon : Fin.contractNth (0 : Fin 1).castSucc (· * ·) (![a, b] : Fin 2 → A) = ![a * b] := by
      funext i; fin_cases i; simp [Fin.contractNth]
    have hlast : (![a, b] : Fin 2 → A) (Fin.last 1) = b := rfl
    rw [RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary_aux_1]
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
    apply linearMap_ext_of_tmul_tprod_eq
    intro a₀ v w
    set a := v 0 with ha
    set b := v 1 with hb
    have hv : v = ![a, b] := by funext i; fin_cases i <;> rfl
    have hlin : a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)
        = a₀ • ((1 : A) ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.zero_apply, hlin, map_smul, LinearMap.comp_apply, hv, core]
    have hc := LinearMap.congr_fun (hcocy a b) w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, RepresentationTheory.Algebra.Module.ExtensionCocycles.algebraEndomorphismFamily,
      Algebra.lsmul_coe] at hc
    rw [hc]
    rw [show a • degreeOneCochainLinearMapEquiv k A W V z b w - (a • degreeOneCochainLinearMapEquiv k A W V z b w + degreeOneCochainLinearMapEquiv k A W V z a (b • w))
        + degreeOneCochainLinearMapEquiv k A W V z a (b • w) = 0 by abel, smul_zero]
  · intro hcomp a b
    ext w
    have h0 : f (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 1 ((1 : A) ⊗ₜ[k] (tprod k ![a, b] ⊗ₜ[k] w))) = 0 :=
      LinearMap.congr_fun hcomp _
    rw [core] at h0
    simp only [RepresentationTheory.Algebra.Module.ExtensionCocycles.algebraEndomorphismFamily, LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe]
    rw [eq_comm, ← sub_eq_zero]
    rw [show a • degreeOneCochainLinearMapEquiv k A W V z b w + degreeOneCochainLinearMapEquiv k A W V z a (b • w) - degreeOneCochainLinearMapEquiv k A W V z (a * b) w
        = a • degreeOneCochainLinearMapEquiv k A W V z b w - degreeOneCochainLinearMapEquiv k A W V z (a * b) w + degreeOneCochainLinearMapEquiv k A W V z a (b • w) by abel]
    exact h0



/-- The degree-one cochain equivalence sends the coboundary of a degree-zero cochain to the auxiliary transform of the negated corresponding linear map. -/

lemma degreeOneCochainLinearMapEquiv_coboundary (β : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 0) :
    degreeOneCochainLinearMapEquiv k A W V (δ 0 1 β) = RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundary k A V W (-(degreeZeroCochainLinearMapEquiv k A W V β)) := by
  set g0 := cochainLinearMapEquiv k A W V 0 β with hg0
  have hΨ0 : ∀ w : W, degreeZeroCochainLinearMapEquiv k A W V β w = g0 ((1 : A) ⊗ₜ[k] (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W).symm w) :=
    fun w => degreeZeroLinearMapEquiv_apply k A W V g0 w
  have hbc : ∀ (u : Fin 0 → A) (y : W),
      (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W).symm y = tprod k u ⊗ₜ[k] y := by
    intro u y; rw [LinearEquiv.symm_apply_eq]; exact (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv_apply_tmul k A W u y).symm
  have core0 : ∀ (a : A) (w : W),
      g0 (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 0 ((1 : A) ⊗ₜ[k] (tprod k ![a] ⊗ₜ[k] w)))
        = a • degreeZeroCochainLinearMapEquiv k A W V β w - degreeZeroCochainLinearMapEquiv k A W V β (a • w) := by
    intro a w
    have hlast0 : (![a] : Fin 1 → A) (Fin.last 0) = a := rfl
    rw [RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary_aux_1]
    simp only [Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, one_mul, pow_one,
      zero_add, neg_smul, one_smul, map_add, map_neg,
      LinearMap.map_smul_of_tower]
    rw [hlast0, ← hbc (Fin.tail ![a]) w, ← hbc (Fin.init ![a]) (a • w),
      show a ⊗ₜ[k] (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W).symm w
          = a • ((1 : A) ⊗ₜ[k] (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorTailZeroEquiv k A W).symm w) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      g0.map_smul, ← hΨ0 w, ← hΨ0 (a • w)]
    abel
  have hΨ1 : degreeOneCochainLinearMapEquiv k A W V (δ 0 1 β)
      = degreeOneLinearMapEquiv k A W V (-(g0.comp (RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary k A W 0))) := by
    change degreeOneLinearMapEquiv k A W V (cochainLinearMapEquiv k A W V 1 (δ 0 1 β)) = _
    rw [cochainLinearMapEquiv_coboundary_zero]
  ext a w
  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundary_apply_apply, hΨ1, degreeOneLinearMapEquiv_apply]
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, smul_neg]
  rw [core0]
  abel

/-- The image of a degree-zero coboundary under the degree-one cochain equivalence belongs to the displayed auxiliary subgroup. -/

lemma degreeOneCochainLinearMapEquiv_coboundary_mem_auxiliary
    (β : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 0) :
    degreeOneCochainLinearMapEquiv k A W V (δ 0 1 β) ∈ RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries k A V W := by
  rw [degreeOneCochainLinearMapEquiv_coboundary]
  exact Submodule.subset_span (Set.mem_range_self _)



/-- An additive equivalence from degree-one cocycles in the auxiliary Hom complex to the displayed auxiliary subtype. -/


noncomputable def cocycleEquivAuxiliarySubtype :
    Cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1 ≃+
      ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W) := by
  have hcocy : (cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1).map
        ((degreeOneCochainLinearMapEquiv k A W V).toAddMonoidHom)
      = (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W).toAddSubgroup := by
    ext F
    simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom,
      Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (auxiliaryCondition_iff_coboundary_eq_zero k A W V z).mpr
        ((Cocycle.mem_iff 1 2 (by norm_num) z).mp hz)
    · intro hF
      refine ⟨(degreeOneCochainLinearMapEquiv k A W V).symm F,
        (Cocycle.mem_iff 1 2 (by norm_num) _).mpr ?_, by simp⟩
      rw [← auxiliaryCondition_iff_coboundary_eq_zero, AddEquiv.apply_symm_apply]
      exact hF
  exact
    ((degreeOneCochainLinearMapEquiv k A W V).addSubgroupMap
      (cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1)).trans
      (AddEquiv.addSubgroupCongr hcocy)

/-- The underlying element of the cocycle equivalence is the degree-one cochain-to-linear-map transform. -/
@[simp]
theorem cocycleEquivAuxiliarySubtype_coe
    (z : Cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) :
    ((cocycleEquivAuxiliarySubtype k A W V z :
        ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W)) : A →ₗ[k] W →ₗ[k] V) =
      degreeOneCochainLinearMapEquiv k A W V (z : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) :=
  rfl

/-- Evaluation of the cocycle equivalence agrees with evaluation of the corresponding degree-one cochain on the canonical tensor generated by the given elements. -/


@[simp]
theorem cocycleEquivAuxiliarySubtype_apply
    (z : Cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) (a : A) (w : W) :
    (cocycleEquivAuxiliarySubtype k A W V z :
        ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W)).1 a w =
      cochainLinearMapEquiv k A W V 1
        (z : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1)
        ((1 : A) ⊗ₜ[k] ((tprod k ![a]) ⊗ₜ[k] w)) := by
  rw [cocycleEquivAuxiliarySubtype_coe]
  exact degreeOneLinearMapEquiv_apply k A W V _ a w

/-- An auxiliary additive subgroup of the subtype determined by the displayed membership condition. -/

abbrev auxiliaryCoboundarySubgroup (k A V W : Type u)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    AddSubgroup ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W) :=
  ((RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries k A V W).submoduleOf
    (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W)).toAddSubgroup

/-- The cocycle equivalence maps degree-one coboundaries onto the auxiliary coboundary subgroup. -/


theorem map_coboundaries_eq_auxiliaryCoboundarySubgroup :
    (coboundaries (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1).map
        (cocycleEquivAuxiliarySubtype k A W V).toAddMonoidHom =
      auxiliaryCoboundarySubgroup k A V W := by
  let e : Cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1 ≃+
      ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W) :=
    cocycleEquivAuxiliarySubtype k A W V
  have hmem : ∀ c : ↥(RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W),
      c ∈ (RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries k A V W).submoduleOf (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule k A V W)
        ↔ (↑c : A →ₗ[k] W →ₗ[k] V) ∈ RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries k A V W :=
    fun _ => Submodule.mem_comap
  ext c
  simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom,
    Submodule.mem_toAddSubgroup, hmem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x 0 (by norm_num)).mp hx
    rw [cocycleEquivAuxiliarySubtype_coe, ← hβ, degreeOneCochainLinearMapEquiv_coboundary]
    exact Submodule.subset_span (Set.mem_range_self _)
  · intro hc
    obtain ⟨X, hX⟩ := (RepresentationTheory.Algebra.Module.ExtensionCocycles.mem_coboundaries_iff k A V W _).mp hc
    refine ⟨e.symm c, ?_, by simp [e]⟩
    rw [mem_coboundaries_iff _ 0 (by norm_num)]
    refine ⟨(degreeZeroCochainLinearMapEquiv k A W V).symm (-X), ?_⟩
    apply (degreeOneCochainLinearMapEquiv k A W V).injective
    have h1 : degreeOneCochainLinearMapEquiv k A W V (↑(e.symm c)) = (↑c : A →ₗ[k] W →ₗ[k] V) := by
      rw [← cocycleEquivAuxiliarySubtype_coe k A W V (e.symm c)]
      simp [e]
    have hcoe : (↑(e.symm c) : Cochain (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1)
        = (degreeOneCochainLinearMapEquiv k A W V).symm (↑c : A →ₗ[k] W →ₗ[k] V) :=
      (AddEquiv.eq_symm_apply (degreeOneCochainLinearMapEquiv k A W V)).mpr h1
    rw [degreeOneCochainLinearMapEquiv_coboundary, AddEquiv.apply_symm_apply, neg_neg, hcoe,
      AddEquiv.apply_symm_apply, hX]

/-- An additive equivalence from degree-one cohomology classes in the auxiliary Hom complex to an auxiliary quotient. -/


noncomputable def firstCohomologyEquivAuxiliaryQuotient :
    CohomologyClass (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1
      ≃+ RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData k A V W :=
  QuotientAddGroup.congr _ _ (cocycleEquivAuxiliarySubtype k A W V)
    (map_coboundaries_eq_auxiliaryCoboundarySubgroup k A W V)

set_option maxHeartbeats 1000000 in


/-- The first-cohomology equivalence sends the class of a cocycle to the quotient class of its image under the cocycle equivalence. -/


@[simp]
theorem firstCohomologyEquivAuxiliaryQuotient_mk
    (z : Cocycle (auxiliaryCochainComplex k A W) (auxiliaryTargetCochainComplex A V) 1) :
    firstCohomologyEquivAuxiliaryQuotient k A W V (CohomologyClass.mk z) =
      QuotientAddGroup.mk'
        (auxiliaryCoboundarySubgroup k A V W)
        (cocycleEquivAuxiliarySubtype k A W V z) :=
  rfl

end RepresentationTheory.HomologicalAlgebra.CochainComplexComparison
