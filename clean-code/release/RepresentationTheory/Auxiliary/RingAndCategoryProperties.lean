/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.RingData
import RepresentationTheory.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import RepresentationTheory.PolynomialModule.Finsupp


/-!
# Auxiliary ring and category properties
-/

namespace RepresentationTheory.Auxiliary.RingAndCategoryProperties

universe u

open RepresentationTheory CategoryTheory Limits


/-- A small semisimple ring satisfies the auxiliary property in degree zero. -/
theorem Auxiliary.property_zero_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R] [Small.{u} R] :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R 0 := by
  intro M
  have : Module.Projective R M := Module.projective_of_isSemisimpleRing R M
  have : Projective M := M.projective_of_categoryTheory_projective
  infer_instance

section EquivalencePreservesProjectiveDimension

variable {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {D : Type*} [Category D] [Abelian D]


/-- An equivalence of abelian categories preserves the bound on projective dimension. -/
theorem CategoryTheory.HasProjectiveDimensionLT.ofEquivalence (E : C ≌ D) {X : C} :
    ∀ {n : ℕ}, HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT (E.functor.obj X) n := by
  intro n
  induction n generalizing X with
  | zero =>
    intro h
    exact (E.functor.map_isZero
      (isZero_of_hasProjectiveDimensionLT_zero X)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr h
      have : Projective (E.functor.obj X) := (E.map_projective_iff X).mpr hproj
      exact projective_iff_hasProjectiveDimensionLT_one.mp this
    | succ m =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (m + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (m + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (m + 1) (by omega)) h
      have hEK := ih hK
      have hEP : Projective (E.functor.obj pp.p) := (E.map_projective_iff pp.p).mpr pp.projective
      have hEP_pd : HasProjectiveDimensionLT (E.functor.obj pp.p) (m + 2) :=
        hasProjectiveDimensionLT_of_ge (E.functor.obj pp.p) 1 (m + 2) (by omega)
      exact (hSE.map_of_exact E.functor).hasProjectiveDimensionLT_X₃ (m + 1) hEK hEP_pd

end EquivalencePreservesProjectiveDimension


/-- A ring equivalence from R to S transfers the auxiliary property at the same index from S to R. -/
theorem Auxiliary.property_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (d : ℕ) (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty S d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d := by
  intro M


  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e

  have hN : HasProjectiveDimensionLE (E.inverse.obj M) d := h (E.inverse.obj M)

  have hFN := CategoryTheory.HasProjectiveDimensionLT.ofEquivalence E hN


  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _ (E.counitIso.app M) (d + 1) hFN


private theorem extendScalars_preservesProjectiveDimensionLT
    {R : Type u} [CommRing R] [Small.{u} R]
    (M : ModuleCat.{u} R) :
    ∀ (n : ℕ), HasProjectiveDimensionLT M n →
    HasProjectiveDimensionLT
      ((ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M) n := by
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  have hFlat : C.Flat := by
    change (algebraMap R (Polynomial R)).Flat; rw [RingHom.flat_algebraMap_iff]; infer_instance
  haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hFlat
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u} C).leftAdjoint_preservesColimits
  haveI : F.PreservesHomology := inferInstance
  haveI : F.Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj.{u} C)
  intro n
  induction n generalizing M with
  | zero =>
    intro h
    exact (F.map_isZero (isZero_of_hasProjectiveDimensionLT_zero M)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr h
      have : Projective (F.obj M) :=
        Functor.PreservesProjectiveObjects.projective_obj hproj
      exact projective_iff_hasProjectiveDimensionLT_one.mp this
    | succ k =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation M
      let SC := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (k + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (k + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (k + 1) (by omega)) h
      have hFK := ih (kernel pp.f) hK
      have hFSE : (SC.map F).ShortExact := hSE.map_of_exact F
      exact hFSE.hasProjectiveDimensionLT_X₃ (k + 1) hFK
        (hasProjectiveDimensionLT_of_ge (F.obj pp.p) 1 (k + 2) (by omega))


private noncomputable def xActionAsRLinear {R : Type u} [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    (ModuleCat.restrictScalars (Polynomial.C (R := R))).obj M ⟶
    (ModuleCat.restrictScalars (Polynomial.C (R := R))).obj M :=


  (ModuleCat.restrictScalars (Polynomial.C (R := R))).map
    ((Polynomial.X : Polynomial R) • (𝟙 M))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in


private theorem koszulSES_shortExact {R : Type u} [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    let C := Polynomial.C (R := R)
    let F := ModuleCat.extendScalars.{u, u, u} C
    let G := ModuleCat.restrictScalars.{u} C
    let FGM := F.obj (G.obj M)
    let ε := (ModuleCat.extendRestrictScalarsAdj.{u} C).counit.app M
    let d := (Polynomial.X : Polynomial R) • (𝟙 FGM) - F.map (xActionAsRLinear M)
    (ShortComplex.mk d ε (by

      set adj := ModuleCat.extendRestrictScalarsAdj.{u} C
      have nat := adj.counit.naturality ((Polynomial.X : Polynomial R) • 𝟙 M)
      simp only [Functor.comp_map, Functor.id_map] at nat


      change d ≫ adj.counit.app M = 0
      change (Polynomial.X • 𝟙 FGM - F.map (xActionAsRLinear M)) ≫ adj.counit.app M = 0
      rw [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
        show F.map (xActionAsRLinear M) = F.map (G.map (Polynomial.X • 𝟙 M)) from rfl,
        nat, Linear.comp_smul]
      erw [Category.comp_id]; exact sub_self _
      )).ShortExact := by
  set C := Polynomial.C (R := R) with C_def
  set F := ModuleCat.extendScalars.{u, u, u} C with F_def
  set G := ModuleCat.restrictScalars.{u} C with G_def
  set FGM := F.obj (G.obj M) with FGM_def
  set adj := ModuleCat.extendRestrictScalarsAdj.{u} C
  set ε := adj.counit.app M
  set d := (Polynomial.X : Polynomial R) • (𝟙 FGM) - F.map (xActionAsRLinear M)
  set N := (G.obj M : Type u)
  intro C' F' G' FGM' ε' d'

  haveI : Mono d' := by
    rw [ModuleCat.mono_iff_injective, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have hdt : d'.hom t = 0 := LinearMap.mem_ker.mp ht

    suffices h : RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N t = 0 from RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp_injective N h

    set f := RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N t with f_def
    apply RepresentationTheory.PolynomialModule.Finsupp.finsupp_eq_zero_of_apply_eq_map_succ (xActionAsRLinear M).hom (map_zero (xActionAsRLinear M).hom) f
    intro k


    have hshift_gen : ∀ (s : ↑FGM'),
        (RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (d'.hom s)) (k + 1) =
        (RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N s) k - (xActionAsRLinear M).hom ((RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N s) (k + 1)) := by
      intro s
      refine TensorProduct.induction_on s ?_ ?_ ?_
      · simp [map_zero]
      · intro p m

        have hd_sub : d'.hom (p ⊗ₜ[R] m) =
            ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
            (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
          change (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
            F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
          exact LinearMap.sub_apply _ _ _

        have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
            (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
        have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
            (p ⊗ₜ[R] m) = p ⊗ₜ[R] ((xActionAsRLinear M).hom m) := rfl
        rw [hd_sub, map_sub, h_smul, h_map]
        simp only [RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp, TensorProduct.lift.tmul, LinearMap.coe_mk,
          AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]


        congr 1
        ·
          congr 1
          exact Polynomial.coeff_X_mul (show Polynomial R from p) k
        ·
          exact (map_smul (xActionAsRLinear M).hom _ _).symm
      · intro s₁ s₂ ih₁ ih₂
        simp only [map_add, Finsupp.add_apply] at ih₁ ih₂ ⊢
        simp only [ih₁, ih₂]; abel
    have h1 := hshift_gen t
    simp only [hdt, map_zero, Finsupp.zero_apply] at h1

    exact sub_eq_zero.mp h1.symm

  haveI : Epi ε' := by
    rw [ModuleCat.epi_iff_surjective]
    intro m
    refine ⟨(1 : Polynomial R) ⊗ₜ[R] (m : (G'.obj M : Type u)), ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.Counit.map_hom_apply]
    simp [TensorProduct.lift.tmul, one_smul]


  constructor
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  set xAct := (xActionAsRLinear M).hom with xAct_def
  set f := RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N x₂ with f_def

  have hshift_gen : ∀ (s : ↑FGM') (k : ℕ),
      (RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (d'.hom s)) (k + 1) =
      (RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N s) k - xAct ((RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N s) (k + 1)) := by
    intro s k
    refine TensorProduct.induction_on s ?_ ?_ ?_
    · simp [map_zero]
    · intro p m
      have hd_sub : d'.hom (p ⊗ₜ[R] m) =
          ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
          (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
        change (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
          F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
        exact LinearMap.sub_apply _ _ _
      have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
          (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
      have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
          (p ⊗ₜ[R] m) = p ⊗ₜ[R] (xAct m) := rfl
      rw [hd_sub, map_sub, h_smul, h_map]
      simp only [RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp, TensorProduct.lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]
      congr 1
      · congr 1
        exact Polynomial.coeff_X_mul (show Polynomial R from p) k
      · exact (map_smul xAct _ _).symm
    · intro s₁ s₂ ih₁ ih₂
      simp only [map_add, Finsupp.add_apply] at ih₁ ih₂ ⊢
      simp only [ih₁, ih₂]; abel

  have hshift_zero : ∀ (s : ↑FGM'),
      (RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (d'.hom s)) 0 = -xAct ((RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N s) 0) := by
    intro s
    refine TensorProduct.induction_on s ?_ ?_ ?_
    · simp [map_zero]
    · intro p m
      have hd_sub : d'.hom (p ⊗ₜ[R] m) =
          ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
          (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
        change (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
          F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
        exact LinearMap.sub_apply _ _ _
      have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
          (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
      have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
          (p ⊗ₜ[R] m) = p ⊗ₜ[R] (xAct m) := rfl
      rw [hd_sub, map_sub, h_smul, h_map]
      simp only [RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp, TensorProduct.lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]


      have h_zero : ((Polynomial.X : Polynomial R) • (p : _)).toFinsupp.coeff 0 = 0 := by
        change Polynomial.coeff ((Polynomial.X : Polynomial R) * (show Polynomial R from p)) 0 = _
        exact Polynomial.coeff_X_mul_zero _
      rw [h_zero, zero_smul, zero_sub, neg_inj]
      exact (map_smul xAct _ _).symm
    · intro s₁ s₂ ih₁ ih₂
      simp only [map_add, Finsupp.add_apply, map_add, neg_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]


  set B := if h : f.support.Nonempty then f.support.max' h + 1 else 0 with B_def

  set g_fun : ℕ → N := fun k =>
    (Finset.range (B + 1)).sum (fun j => (xAct ^ j) (f (k + 1 + j))) with g_fun_def

  have g_fun_zero : ∀ k, B ≤ k → g_fun k = 0 := by
    intro k hk
    simp only [g_fun_def]
    apply Finset.sum_eq_zero
    intro j _
    have : f (k + 1 + j) = 0 := by
      by_contra hmem_ne
      have hmem := Finsupp.mem_support_iff.mpr hmem_ne
      simp only [B_def] at hk
      split_ifs at hk with h
      · exact Nat.not_succ_le_self (f.support.max' h)
          (le_trans (Nat.succ_le_of_lt (by omega))
            (Finset.le_max' _ _ hmem))
      · exact h ⟨_, hmem⟩
    rw [this, map_zero]

  set g := Finsupp.onFinset (Finset.range B) g_fun (fun k hk => by
    simp only [Finset.mem_range]
    by_contra h
    push Not at h
    exact hk (g_fun_zero k h)) with g_def

  have g_rec : ∀ k, g k = f (k + 1) + xAct (g (k + 1)) := by
    intro k
    change g_fun k = f (k + 1) + xAct (g_fun (k + 1))
    simp only [g_fun_def]


    rw [Finset.sum_range_succ' (fun j => (xAct ^ j) (f (k + 1 + j)))]
    have h0 : (xAct ^ 0) (f (k + 1 + 0)) = f (k + 1) := by simp [pow_zero]
    rw [h0, add_comm]
    congr 1


    rw [map_sum, Finset.sum_range_succ]


    have hB_zero : xAct ((xAct ^ B) (f (k + 2 + B))) = 0 := by
      have : f (k + 2 + B) = 0 := by
        by_contra hmem_ne
        have hmem := Finsupp.mem_support_iff.mpr hmem_ne
        have hB_bound : ∀ n ∈ f.support, n < B := by
          intro n hn
          simp only [B_def]
          split_ifs with h
          · exact Nat.lt_succ_of_le (Finset.le_max' _ _ hn)
          · exact absurd ⟨n, hn⟩ h
        exact absurd (hB_bound _ hmem) (by omega)
      rw [this, map_zero, map_zero]
    rw [hB_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : k + 1 + (j + 1) = k + 2 + j := by omega
    have h2 : k + 1 + 1 + j = k + 2 + j := by omega
    rw [h1, h2, pow_succ' xAct j]; rfl


  refine ⟨RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N g, ?_⟩
  apply RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp_injective N

  ext k

  have hg_coord : RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N (R := R) g) = g :=
    RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial_rightInverse_tensorPolynomialToFinsupp (R := R) N g
  cases k with
  | zero =>

    rw [hshift_zero]
    rw [show RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N g) = g from hg_coord]


    have hx₂_eq : x₂ = RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N (R := R) f :=
      (RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial_leftInverse_tensorPolynomialToFinsupp (R := R) N x₂).symm
    rw [hx₂_eq] at hx₂

    have hXpow : ∀ (k : ℕ) (m : (G'.obj M : Type u)),
        ((Polynomial.X : Polynomial R) ^ k) • m = (xAct ^ k) m := by
      intro k; induction k with
      | zero => intro m; simp [pow_zero, one_smul]
      | succ k ih =>
        intro m; rw [pow_succ, mul_smul, ih, pow_succ xAct k]


        rfl

    have hcounit_inv : ε'.hom (RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N (R := R) f) =
        f.sum (fun k m => (xAct ^ k) m) := by
      simp only [RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.sum]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro k _
      erw [ModuleCat.ExtendRestrictScalarsAdj.Counit.map_hom_apply]
      simp only [TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      exact hXpow k (f k)

    have hsum_zero : f.sum (fun k m => (xAct ^ k) m) = 0 := by
      rw [← hcounit_inv]; exact hx₂

    have hB_bound : ∀ n ∈ f.support, n < B := by
      intro n hn; simp only [B_def]
      split_ifs with h
      · exact Nat.lt_succ_of_le (Finset.le_max' _ _ hn)
      · exact absurd ⟨n, hn⟩ h
    rw [neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm, ← f_def]
    change f 0 + xAct (g_fun 0) = 0
    rw [show xAct (g_fun 0) = xAct ((Finset.range (B + 1)).sum
        (fun j => (xAct ^ j) (f (0 + 1 + j)))) from rfl]
    rw [RepresentationTheory.PolynomialModule.Finsupp.finsupp_sum_powers_eq_zero_add_map_sum_range xAct f B hB_bound]
    exact hsum_zero
  | succ k =>

    rw [hshift_gen]
    rw [show RepresentationTheory.PolynomialModule.Finsupp.tensorPolynomialToFinsupp N (RepresentationTheory.PolynomialModule.Finsupp.finsuppToTensorPolynomial N g) = g from hg_coord]

    rw [g_rec k]
    abel

/-- For a small commutative ring, the auxiliary property at index d implies the property at index d + 1 for its polynomial ring. -/
theorem Auxiliary.property_polynomial_succ {R : Type u} [CommRing R] [Small.{u} R] (d : ℕ)
    (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (Polynomial R) (d + 1) := by
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  set G := ModuleCat.restrictScalars.{u} C
  intro M

  have hSES := koszulSES_shortExact M

  have hFGM_pd : HasProjectiveDimensionLE (F.obj (G.obj M)) d := by
    exact extendScalars_preservesProjectiveDimensionLT (G.obj M) (d + 1) (h (G.obj M))


  exact hSES.hasProjectiveDimensionLT_X₃ (d + 1) hFGM_pd
    (hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 2) (by omega))


private instance isSemisimpleRing_mvPolynomial_fin_zero (k : Type u) [Field k] :
    IsSemisimpleRing (MvPolynomial (Fin 0) k) :=
  (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv.isSemisimpleRing

/-- A multivariate polynomial ring indexed by Fin n over a field satisfies the auxiliary property at index n. -/
theorem Auxiliary.property_mvPolynomial_variable_count (k : Type u) [Field k] :
    ∀ n, RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (MvPolynomial (Fin n) k) n
  | 0 => Auxiliary.property_zero_of_isSemisimpleRing _
  | n + 1 => by

    have ih := Auxiliary.property_mvPolynomial_variable_count k n

    have e := (MvPolynomial.finSuccEquiv k n).toRingEquiv


    have h_poly := Auxiliary.property_polynomial_succ n ih

    exact Auxiliary.property_of_ringEquiv e (n + 1) h_poly

section PolynomialLowerBound

open Polynomial


private theorem Polynomial.X_mul_eq_zero {R : Type u} [CommRing R] {p : R[X]} (h : X * p = 0) :
    p = 0 := by
  ext n
  have h1 := congr_arg (Polynomial.coeff · (n + 1)) h
  simp only [coeff_X_mul, coeff_zero] at h1
  exact h1


private theorem not_hasHomologicalDimensionLE_zero_polynomial
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (Polynomial R) 0 := by
  intro hall

  let φ : R →ₗ[R] R := 0
  let A := Module.AEval' φ
  let MA := ModuleCat.of (Polynomial R) A

  have hpd : HasProjectiveDimensionLE MA 0 := hall MA
  have hproj : Projective MA :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hpd
  have hmod : Module.Projective (Polynomial R) A :=
    MA.projective_of_module_projective

  let one_A : A := Module.AEval'.of φ (1 : R)
  let surj := LinearMap.toSpanSingleton (Polynomial R) A one_A
  have hsurj : Function.Surjective surj := by
    intro a
    refine ⟨Polynomial.C ((Module.AEval'.of φ).symm a), ?_⟩
    simp only [surj, LinearMap.toSpanSingleton_apply]
    rw [Module.AEval.C_smul,
      ← (Module.AEval'.of φ).map_smul, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]

  obtain ⟨sect, hsect⟩ :=
    Module.projective_lifting_property surj LinearMap.id hsurj


  have X_smul_zero : ∀ a : A, (X : R[X]) • a = 0 := by
    intro a
    rw [show a = Module.AEval'.of φ ((Module.AEval'.of φ).symm a) from
      ((Module.AEval'.of φ).apply_symm_apply a).symm,
      Module.AEval'.X_smul_of, LinearMap.zero_apply, map_zero]
  have hzero : ∀ a : A, sect a = 0 := by
    intro a
    apply Polynomial.X_mul_eq_zero
    calc X * sect a
        = sect ((X : R[X]) • a) := (sect.map_smul (X : R[X]) a).symm
      _ = sect 0 := by rw [X_smul_zero]
      _ = 0 := map_zero sect

  have hall_zero : ∀ a : A, a = 0 := by
    intro a
    have h := LinearMap.ext_iff.mp hsect a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hzero a,
      map_zero] at h
    exact h.symm

  have : one_A ≠ 0 := by
    intro h
    exact one_ne_zero ((Module.AEval'.of φ).injective
      (h.trans (map_zero (Module.AEval'.of φ)).symm))
  exact this (hall_zero one_A)


private theorem Polynomial.divX_X_mul (R : Type u) [CommRing R] (p : R[X]) :
    Polynomial.divX (X * p) = p := by
  ext n
  simp [coeff_divX, coeff_X_mul]

set_option backward.isDefEq.respectTransparency false in


private theorem polynomial_X_mul_mono_extendScalars (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    Mono ((Polynomial.X : Polynomial R) •
      (𝟙 ((ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M))) := by
  rw [ModuleCat.mono_iff_injective]
  set FM := (ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M


  set C := Polynomial.C (R := R)
  let S' := (ModuleCat.restrictScalars C).obj (ModuleCat.of (Polynomial R) (Polynomial R))


  have divX_C_mul : ∀ (r : R) (q : Polynomial R),
      Polynomial.divX (Polynomial.C r * q) = Polynomial.C r * Polynomial.divX q := by
    intro r q; apply Polynomial.ext; intro n
    simp [Polynomial.coeff_divX, Polynomial.coeff_C_mul]
  let g : TensorProduct R (S' : Type u) (M : Type u) →ₗ[R]
      TensorProduct R (S' : Type u) (M : Type u) :=
    TensorProduct.lift
      { toFun := fun (p : (S' : Type u)) =>
          { toFun := fun (m : (M : Type u)) =>
              (Polynomial.divX (p : Polynomial R) : (S' : Type u)) ⊗ₜ[R] m
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
            map_smul' := fun r m => by
              simp only [RingHom.id_apply]; exact TensorProduct.tmul_smul r _ m }
        map_add' := fun p q => by
          ext m; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [Polynomial.divX_add]; exact (TensorProduct.add_tmul _ _ m)
        map_smul' := fun r p => by
          ext m
          simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
          rw [TensorProduct.smul_tmul']
          congr 1
          exact divX_C_mul r p }
  have hli : Function.LeftInverse g
      (ConcreteCategory.hom ((Polynomial.X : Polynomial R) • 𝟙 FM)) := by
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro p m
      change g ((Polynomial.X : Polynomial R) • (p ⊗ₜ[R] m)) = p ⊗ₜ m
      rw [ModuleCat.ExtendScalars.smul_tmul]
      simp only [g, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      congr 1
      exact Polynomial.divX_X_mul R p
    · intro x y hx hy
      simp only [map_add, hx, hy]
  exact hli.injective


private noncomputable def polynomialExtensionSES (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    let FM := (ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M
    let f : FM ⟶ FM := (Polynomial.X : Polynomial R) • (𝟙 FM)
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := polynomial_X_mul_mono_extendScalars R M
  epi_g := inferInstance


private theorem ext_eq_zero_of_X_action_vanishing
    {R : Type u} [CommRing R]
    {A : ModuleCat.{u} (Polynomial R)} {Y : ModuleCat.{u} (Polynomial R)}
    (hY : (Polynomial.X : Polynomial R) • (𝟙 Y) = (0 : Y ⟶ Y))
    {Q : ModuleCat.{u} (Polynomial R)} {g : A ⟶ Q}
    {w : ((Polynomial.X : Polynomial R) • (𝟙 A)) ≫ g = 0}
    (hSES : (ShortComplex.mk ((Polynomial.X : Polynomial R) • (𝟙 A)) g w).ShortExact)
    {n : ℕ}
    [Small.{u} (Polynomial R)]
    (hQ : HasProjectiveDimensionLE Q (n + 1))
    (e : Abelian.Ext A Y (n + 1)) : e = 0 := by

  have hδ : hSES.extClass.comp e (show 1 + (n + 1) = n + 2 by omega) = 0 :=
    Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 2) (by omega)

  obtain ⟨e₂, he₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES Y e
    (show 1 + (n + 1) = n + 2 by omega) hδ


  have h_precomp : (Abelian.Ext.mk₀ ((Polynomial.X : Polynomial R) • (𝟙 A))).comp
      e₂ (zero_add (n + 1)) = (Polynomial.X : Polynomial R) • e₂ := by
    rw [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.mk₀_id_comp]

  have h_smul_zero : (Polynomial.X : Polynomial R) • e₂ = 0 := by
    rw [Abelian.Ext.smul_eq_comp_mk₀ e₂ (Polynomial.X : Polynomial R)]
    rw [hY, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

  rw [← he₂, h_precomp, h_smul_zero]

set_option backward.isDefEq.respectTransparency false in


private theorem ext_subsingleton_of_polynomial_trivial_action
    (R : Type u) [CommRing R] [Small.{u} R]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} R) (i : ℕ)
    (h : ∀ (Y : ModuleCat.{u} (Polynomial R)),
      (Polynomial.X : Polynomial R) • (𝟙 Y) = (0 : Y ⟶ Y) →
      Subsingleton (Abelian.Ext ((ModuleCat.extendScalars.{u, u, u}
        (Polynomial.C (R := R))).obj M) Y i)) :
    Subsingleton (Abelian.Ext M N i) := by
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  set G := ModuleCat.restrictScalars.{u} C

  let φ : N →ₗ[R] N := 0
  let N₀ := ModuleCat.of (Polynomial R) (Module.AEval' φ)

  have hX : (Polynomial.X : Polynomial R) • (𝟙 N₀) = (0 : N₀ ⟶ N₀) := by
    ext x
    change (Polynomial.X : Polynomial R) • x = (0 : N₀ ⟶ N₀) x
    change (Polynomial.X : Polynomial R) • x = 0
    obtain ⟨m, rfl⟩ := (Module.AEval'.of φ).surjective x
    rw [Module.AEval'.X_smul_of, LinearMap.zero_apply, map_zero]

  have hN₀ := h N₀ hX


  have hFlat : C.Flat := by
    change (algebraMap R R[X]).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  haveI : F.PreservesHomology := by
    haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hFlat
    haveI := (ModuleCat.extendRestrictScalarsAdj.{u} C).leftAdjoint_preservesColimits
    infer_instance

  have hGN₀ := RepresentationTheory.Algebra.Category.ModuleCat.Projective.ModuleCat.subsingleton_ext_restrictScalars_of_subsingleton_ext_extendScalars C M N₀ i hN₀


  have smul_compat : ∀ (r : R) (m : G.obj N₀), (r • m : G.obj N₀) = r • (show N from m) := by
    intro r m
    change Polynomial.C r • (show N₀ from m) = r • (show N from m)
    rw [Module.AEval.C_smul]
  let e : (G.obj N₀) ≃ₗ[R] N :=
    { toFun := fun m => (show N from m)
      invFun := fun m => (show G.obj N₀ from m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => smul_compat r m }

  let iso : G.obj N₀ ≅ N := e.toModuleIso


  constructor
  intro a b

  have ha := hGN₀.elim (a.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i))
    (b.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i))

  have hrt : ∀ (x : Abelian.Ext M N i),
      (x.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) = x := by
    intro x
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero i) (zero_add 0) (by omega)]
    rw [Abelian.Ext.mk₀_comp_mk₀, iso.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  calc a = (a.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) := (hrt a).symm
    _ = (b.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) := by rw [ha]
    _ = b := hrt b


private theorem pd_le_of_polynomial_gldim (R : Type u) [CommRing R] (d : ℕ)
    (M : ModuleCat.{u} R)
    (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (Polynomial R) (d + 1)) :
    HasProjectiveDimensionLE M d := by
  letI : Small.{u} R := ⟨⟨R, ⟨Equiv.refl R⟩⟩⟩
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩

  set F := ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))
  set FM := F.obj M
  set f : FM ⟶ FM := (Polynomial.X : Polynomial R) • (𝟙 FM)
  set Q := cokernel f

  have hSES := polynomialExtensionSES R M

  have hQ : HasProjectiveDimensionLE Q (d + 1) := h Q

  change HasProjectiveDimensionLT M (d + 1)
  rw [hasProjectiveDimensionLT_iff]
  intro i hi N e


  have hss : Subsingleton (Abelian.Ext M N i) :=
    ext_subsingleton_of_polynomial_trivial_action R M N i (fun Y hY => by
      constructor; intro a b


      have hFM_pd : HasProjectiveDimensionLE FM (d + 1) := h FM


      suffices ∀ (x : Abelian.Ext FM Y i), x = 0 from
        (this a).trans (this b).symm
      intro x

      obtain rfl | hi' := Nat.eq_or_lt_of_le hi
      ·
        exact ext_eq_zero_of_X_action_vanishing hY hSES hQ x
      ·
        exact Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x (d + 2) (by omega))
  exact hss.elim e 0


private theorem hasHomologicalDimensionLE_of_polynomial_succ
    (R : Type u) [CommRing R] [Nontrivial R] (d : ℕ)
    (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (Polynomial R) (d + 1)) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d := by
  intro M
  exact pd_le_of_polynomial_gldim R d M h

end PolynomialLowerBound


/-- If a multivariate polynomial ring indexed by Fin n over a field has the auxiliary property at index d, then n is at most d. -/
theorem Auxiliary.variable_count_le_of_property (k : Type u) [Field k] :
    ∀ n d, RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (MvPolynomial (Fin n) k) d → n ≤ d
  | 0, d, _ => Nat.zero_le d
  | n + 1, d, hd => by

    have e := (MvPolynomial.finSuccEquiv k n).symm.toRingEquiv
    have hpoly : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (Polynomial (MvPolynomial (Fin n) k)) d :=
      Auxiliary.property_of_ringEquiv e d hd

    match d with
    | 0 => exact absurd hpoly (not_hasHomologicalDimensionLE_zero_polynomial _)
    | d' + 1 =>
      have hR := hasHomologicalDimensionLE_of_polynomial_succ _ d' hpoly
      have ih := Auxiliary.variable_count_le_of_property k n d' hR
      omega


/-- For a multivariate polynomial ring indexed by Fin n over a field, the auxiliary value is the cast of n. -/
theorem Auxiliary.mvPolynomial_value_eq_natCast (k : Type u) [Field k] (n : ℕ) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant (MvPolynomial (Fin n) k) = n := by
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  apply le_antisymm
  · exact iInf₂_le n (Auxiliary.property_mvPolynomial_variable_count k n)
  · apply le_iInf₂
    intro d hd
    exact_mod_cast Auxiliary.variable_count_le_of_property k n d hd

end RepresentationTheory.Auxiliary.RingAndCategoryProperties

