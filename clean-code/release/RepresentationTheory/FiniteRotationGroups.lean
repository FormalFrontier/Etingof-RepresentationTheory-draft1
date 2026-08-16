/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.QuaternionRotationMaps
import RepresentationTheory.Alignment.Attribute

/-! # Finite Rotation Groups -/

open Matrix

namespace RepresentationTheory.FiniteRotationGroups

   
                                                   

                                                                                         
                                                                                    
                                                                                       
                                                                                         
                                                                                             
                                                                                

                                                                                        
                                                                                      
  

                                                                                               
                                                                                           
                                                                             

                                                                                            
                                           
                                                                                              
                                                                                           
                                               
/-- Every nonidentity displayed orthogonal transformation fixes a nonzero vector. -/
theorem exists_ne_zero_fixed_vector (g : specialOrthogonalGroup (Fin 3) ℝ) (_hg : g ≠ 1) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := (g : Matrix (Fin 3) (Fin 3) ℝ) with hM
  obtain ⟨hortho, hdet⟩ := mem_specialOrthogonalGroup_iff.mp (SetLike.coe_mem g)
  have hMtM : Mᵀ * M = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hortho
  have hdetT : Mᵀ.det = 1 := by rw [det_transpose]; exact hdet
                                                                           
  have hkey : (M - 1).det = 0 := by
    have e1 : (M - 1).det = (1 - Mᵀ).det := by
      have hprod : Mᵀ * (M - 1) = 1 - Mᵀ := by rw [mul_sub, mul_one, hMtM]
      calc (M - 1).det = Mᵀ.det * (M - 1).det := by rw [hdetT, one_mul]
        _ = (Mᵀ * (M - 1)).det := (det_mul _ _).symm
        _ = (1 - Mᵀ).det := by rw [hprod]
    have e2 : (1 - Mᵀ).det = (1 - M).det := by
      rw [show (1 : Matrix (Fin 3) (Fin 3) ℝ) - Mᵀ = (1 - M)ᵀ by
        rw [transpose_sub, transpose_one], det_transpose]
    have e3 : (1 - M).det = -((M - 1).det) := by
      rw [show (1 : Matrix (Fin 3) (Fin 3) ℝ) - M = -(M - 1) by abel, det_neg,
        Fintype.card_fin]
      ring
    have hself : (M - 1).det = -((M - 1).det) := e1.trans (e2.trans e3)
    linarith
                                                          
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hkey
  refine ⟨v, hv0, ?_⟩
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hMv
  exact hMv

   
                                   

                                                                                       
                                                                         
                                                                                   
                                                                                    
                                                                                           
                                                      
  

section CommonAxis

open scoped RealInnerProductSpace
open Matrix EuclideanSpace Submodule WithLp Module

                                                                                            
private lemma toEuclideanLin_inner_eq {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : Mᵀ * M = 1)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪toEuclideanLin M x, toEuclideanLin M y⟫ = ⟪x, y⟫ := by
  have hdot : ∀ a b : Fin 3 → ℝ, (M *ᵥ a) ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ b := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hM, one_mulVec]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    ofLp_toEuclideanLin_apply, ofLp_toEuclideanLin_apply]
  simp only [star_trivial]
  exact hdot _ _

                                                                            
private lemma toEuclideanLin_comp (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    (toEuclideanLin M).comp (toEuclideanLin N) = toEuclideanLin (M * N) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, toEuclideanLin_apply M, ofLp_toEuclideanLin_apply, mulVec_mulVec,
    toEuclideanLin_apply (M * N)]

                                                                                         
private lemma det_toEuclideanLin (M : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (toEuclideanLin M) = M.det := by
  rw [toEuclideanLin_eq_toLin, LinearMap.det_toLin]

                                                                       
private lemma toEuclideanLin_one :
    toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp

                                                                 
private lemma so3_transpose_mul (g : specialOrthogonalGroup (Fin 3) ℝ) :
    (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (g : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp (SetLike.coe_mem g)).1

                                                                                           
private noncomputable def euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinear (toEuclideanLin (↑g)) (toEuclideanLin (↑g)ᵀ)
      (by rw [toEuclideanLin_comp,
          show ((g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) = 1 from
            mul_eq_one_comm.mpr (so3_transpose_mul g), toEuclideanLin_one])
      (by rw [toEuclideanLin_comp, so3_transpose_mul g, toEuclideanLin_one]))
    (fun x y => toEuclideanLin_inner_eq (so3_transpose_mul g) x y)

@[simp] private lemma euclideanIso_apply (g : specialOrthogonalGroup (Fin 3) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : euclideanIso g x = toEuclideanLin (↑g) x := rfl

                                                                    
private lemma euclideanIso_fix (g : specialOrthogonalGroup (Fin 3) ℝ)
    (w : EuclideanSpace ℝ (Fin 3))
    (hw : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ofLp w = ofLp w) : euclideanIso g w = w := by
  apply WithLp.ofLp_injective
  rw [euclideanIso_apply, ofLp_toEuclideanLin_apply, hw]

                                                                             
private lemma euclideanIso_mul (g h : specialOrthogonalGroup (Fin 3) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    euclideanIso (g * h) x = euclideanIso g (euclideanIso h x) := by
  apply WithLp.ofLp_injective
  simp only [euclideanIso_apply, ofLp_toEuclideanLin_apply, Submonoid.coe_mul, mulVec_mulVec]

                                            
private lemma euclideanIso_det (g : specialOrthogonalGroup (Fin 3) ℝ) :
    LinearMap.det (euclideanIso g).toLinearMap = 1 := by
  have hEq : (euclideanIso g).toLinearMap = toEuclideanLin (↑g) := rfl
  rw [hEq, det_toEuclideanLin]
  exact (mem_specialOrthogonalGroup_iff.mp (SetLike.coe_mem g)).2

                                                                                          
                                                                                          
                                                                                           
                                            
/-- A cyclicity conclusion under the hypotheses shown in the formal statement. -/
theorem cyclicGroup_011638
    (H : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite H]
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (hfix : ∀ g : H, ((g : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v) :
    IsCyclic H := by
  classical
                                                                
  set v₀ : EuclideanSpace ℝ (Fin 3) := toLp 2 v with hv₀def
  have hofLpv₀ : ofLp v₀ = v := rfl
  have hv₀ : v₀ ≠ 0 := by
    intro h; exact hv (by rw [← hofLpv₀, h, ofLp_zero])
                                                      
  have hWfin : finrank ℝ (ℝ ∙ v₀)ᗮ = 2 := by
    haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
      ⟨by norm_num [finrank_euclideanSpace_fin]⟩
    exact Submodule.finrank_orthogonal_span_singleton (n := 2) hv₀
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := (ℝ ∙ v₀)ᗮ with hWdef
  haveI : Fact (finrank ℝ W = 2) := ⟨hWfin⟩
                                                                     
  let bW : Basis (Fin 2) ℝ W := Module.finBasisOfFinrankEq ℝ W hWfin
  let o : Orientation ℝ W (Fin 2) := bW.orientation
  set x : W := bW 0 with hxdef
  have hx0 : x ≠ 0 := bW.ne_zero 0
                                                            
  have hfixg : ∀ g : H, euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ) v₀ = v₀ := fun g =>
    euclideanIso_fix _ v₀ (by rw [hofLpv₀]; exact hfix g)
  have hWinv : ∀ g : H,
      W.map ((euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearEquiv :
        EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = W := by
    intro g
    rw [hWdef, Submodule.map_orthogonal_equiv]
    congr 1
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, hfixg g]
                                       
  let ρ : H → (W ≃ₗᵢ[ℝ] W) := fun g =>
    (LinearIsometryEquiv.submoduleMap W (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ))).trans
      (LinearIsometryEquiv.ofEq _ W (hWinv g))
  have coeρ : ∀ (g : H) (y : W),
      ((ρ g y : W) : EuclideanSpace ℝ (Fin 3))
        = euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ) (y : W) := by
    intro g y
    change ((LinearIsometryEquiv.ofEq _ W (hWinv g)
      (LinearIsometryEquiv.submoduleMap W
        (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)) y) : W) :
        EuclideanSpace ℝ (Fin 3)) = _
    rw [LinearIsometryEquiv.coe_ofEq_apply, LinearIsometryEquiv.submoduleMap_apply_coe]
                           
  have ρmul : ∀ (g h : H) (y : W), ρ (g * h) y = ρ g (ρ h y) := by
    intro g h y
    apply Subtype.ext
    rw [coeρ, coeρ, coeρ, Subgroup.coe_mul, euclideanIso_mul]
                                                              
  have hdet : ∀ g : H, (0 : ℝ) < LinearMap.det ((ρ g).toLinearEquiv : W →ₗ[ℝ] W) := by
    intro g
    have hmaps : W ≤ W.comap (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap := by
      intro y hy
      have : (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearEquiv.toLinearMap
          = (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap := rfl
      have hmem : (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)) y ∈ W := by
        have := hWinv g ▸ Submodule.mem_map_of_mem (f := (euclideanIso
          (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearEquiv.toLinearMap) hy
        simpa using this
      exact hmem
                                      
    have hrestrict :
        (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap.restrict hmaps
          = (ρ g).toLinearMap := by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply]
      exact (coeρ g y).symm
                                                                    
    have hquot : W.mapQ W (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap hmaps
        = LinearMap.id := by
      have hv₀W : v₀ ∉ W := by
        rw [hWdef]
        intro hmem
        have h0 : ⟪v₀, v₀⟫ = (0 : ℝ) :=
          (Submodule.mem_orthogonal _ _).mp hmem v₀ (Submodule.mem_span_singleton_self _)
        exact hv₀ (inner_self_eq_zero.mp h0)
      have hne : W.mkQ v₀ ≠ 0 := by
        rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hv₀W
      have hspan : Submodule.span ℝ {W.mkQ v₀} = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hq : finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ W) + finrank ℝ W
            = finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.finrank_quotient_add_finrank W
        rw [hWfin, finrank_euclideanSpace_fin] at hq
        rw [finrank_span_singleton hne]
        omega
      refine LinearMap.ext_on hspan ?_
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      congr 1
      exact hfixg g
    have hE : LinearMap.det (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap = 1 :=
      euclideanIso_det g
    rw [LinearMap.det_eq_det_mul_det (W := W) _ hmaps, hrestrict, hquot,
      LinearMap.det_id, mul_one] at hE
    rw [show ((ρ g).toLinearEquiv : W →ₗ[ℝ] W) = (ρ g).toLinearMap from rfl, hE]
    norm_num
                                                                           
  have hrot : ∀ g : H, ρ g = o.rotation (o.oangle x (ρ g x)) := by
    intro g
    obtain ⟨α, hα⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos (hdet g)
    have : o.oangle x (ρ g x) = α := by rw [hα, o.oangle_rotation_self_right hx0]
    rw [this, hα]
                                     
  have θmul : ∀ g h : H,
      o.oangle x (ρ (g * h) x) = o.oangle x (ρ g x) + o.oangle x (ρ h x) := by
    intro g h
    have hg := hrot g
    have hh := hrot h
    set a := o.oangle x (ρ g x)
    set b := o.oangle x (ρ h x)
    rw [ρmul, hh, hg, o.rotation_rotation, o.oangle_rotation_self_right hx0]
                                      
  let φ : H →* Circle :=
    { toFun := fun g => (o.oangle x (ρ g x)).toCircle
      map_one' := by
        have h1 : ρ (1 : H) x = x := by
          apply Subtype.ext
          rw [coeρ]
          apply euclideanIso_fix
          simp
        rw [h1, o.oangle_self, Real.Angle.toCircle_zero]
      map_mul' := fun g h => by
        simp only [θmul g h, Real.Angle.toCircle_add] }
                      
  have hφinj : Function.Injective φ := by
    intro g h hgh
    have hθ : o.oangle x (ρ g x) = o.oangle x (ρ h x) := by
      have := congrArg (fun c : Circle => (Complex.arg (c : ℂ) : Real.Angle)) hgh
      simpa only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Real.Angle.arg_toCircle] using this
    have hρeq : ρ g = ρ h := by rw [hrot g, hrot h, hθ]
                                                                               
    have hagree : (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap
        = (euclideanIso (h : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap := by
      have hle : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≤
          LinearMap.eqLocus (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap
            (euclideanIso (h : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap := by
        have hsup : (ℝ ∙ v₀) ⊔ W = ⊤ := by
          rw [hWdef]; exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
        rw [← hsup]
        refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst hz
          simp only [SetLike.mem_coe, LinearMap.mem_eqLocus]
          rw [show (euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap v₀
            = euclideanIso (g : specialOrthogonalGroup (Fin 3) ℝ) v₀ from rfl,
            show (euclideanIso (h : specialOrthogonalGroup (Fin 3) ℝ)).toLinearMap v₀
            = euclideanIso (h : specialOrthogonalGroup (Fin 3) ℝ) v₀ from rfl, hfixg g, hfixg h]
        · intro z hz
          simp only [LinearMap.mem_eqLocus]
          have := congrArg (fun e : W ≃ₗᵢ[ℝ] W => ((e ⟨z, hz⟩ : W) : EuclideanSpace ℝ (Fin 3))) hρeq
          simp only [coeρ] at this
          exact this
      have := (top_le_iff.mp hle)
      exact LinearMap.ext fun z => (LinearMap.mem_eqLocus.mp (this ▸ Submodule.mem_top))
                                                                              
    have hmat : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
        = ((h : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
      have : toEuclideanLin ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
          = toEuclideanLin ((h : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) :=
        hagree
      exact toEuclideanLin.injective this
    exact Subtype.ext (Subtype.ext hmat)
                                                             
  exact isCyclic_of_injective_ringHom (Circle.coeHom.comp φ)
    (Circle.coe_injective.comp hφinj)

end CommonAxis

   
                              

                                                                                            
                                                                                            
                                                                                                   
                                                                      
  

                                                            
                                                                                               
/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011812 (g : specialOrthogonalGroup (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ a) ⬝ᵥ ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ b) = a ⬝ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, so3_transpose_mul g, one_mulVec]

                                                                                              
                                           
/-- An auxiliary type whose internal description is not exposed by the displayed formal type. -/
def AuxiliaryType011608 : Type := {v : Fin 3 → ℝ // v ⬝ᵥ v = 1}

namespace AuxiliaryType011608

/-- The equality displayed in the formal statement. -/
@[ext] lemma ext {v w : AuxiliaryType011608} (h : v.1 = w.1) : v = w := Subtype.ext h

                                                                                                 
/-- The action of the displayed orthogonal group on the auxiliary vector type. -/
instance instMulAction : MulAction (specialOrthogonalGroup (Fin 3) ℝ) AuxiliaryType011608 where
  smul g v := ⟨(g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1, by
    rw [matrixAction_011812]; exact v.2⟩
  one_smul v := by
    apply Subtype.ext
    change ((1 : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1 = v.1
    rw [Submonoid.coe_one, one_mulVec]
  mul_smul g h v := by
    apply Subtype.ext
    change (((g * h) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1
        = (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((h : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1)
    rw [Submonoid.coe_mul, mulVec_mulVec]

/-- A matrix identity for the displayed action or transformation. -/
@[simp] lemma smul_val (g : specialOrthogonalGroup (Fin 3) ℝ) (v : AuxiliaryType011608) :
    (g • v).1 = (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1 := rfl

end AuxiliaryType011608

                                                                                       
/-- The set-valued construction associated with an orthogonal transformation. -/
def rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ) : Set (Fin 3 → ℝ) :=
  {v | v ⬝ᵥ v = 1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v}

                                                                                         
/-- A predicate that a vector is fixed by every element of the given subgroup. -/
def IsFixedVector (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) (v : Fin 3 → ℝ) : Prop :=
  v ⬝ᵥ v = 1 ∧ ∃ g ∈ G, g ≠ 1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v

                                                                                  
/-- The set-valued construction assigning rotation axes to a subgroup. -/
def rotationAxes (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) : Set (Fin 3 → ℝ) :=
  {v | IsFixedVector G v}

section Poles
open scoped RealInnerProductSpace
open Matrix EuclideanSpace Submodule WithLp Module

                                                                                              
          
private lemma inner_toLp (a b : Fin 3 → ℝ) :
    ⟪(toLp 2 a : EuclideanSpace ℝ (Fin 3)), toLp 2 b⟫ = a ⬝ᵥ b := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  exact dotProduct_comm b a

                                                                                              
                                                                                           
                                                                                               
                                        
private lemma euclidean_fixed_mem_axis
    (g : specialOrthogonalGroup (Fin 3) ℝ) (hg : g ≠ 1)
    (u₀ : EuclideanSpace ℝ (Fin 3)) (hu₀unit : ⟪u₀, u₀⟫ = 1)
    (hfix₀ : euclideanIso g u₀ = u₀)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : euclideanIso g x = x) :
    x ∈ ℝ ∙ u₀ := by
  classical
  have hu₀ : u₀ ≠ 0 := fun h => by simp [h] at hu₀unit
                                                        
  have hWfin : finrank ℝ (ℝ ∙ u₀)ᗮ = 2 := by
    haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
      ⟨by norm_num [finrank_euclideanSpace_fin]⟩
    exact Submodule.finrank_orthogonal_span_singleton (n := 2) hu₀
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := (ℝ ∙ u₀)ᗮ with hWdef
  haveI : Fact (finrank ℝ W = 2) := ⟨hWfin⟩
  let bW : Basis (Fin 2) ℝ W := Module.finBasisOfFinrankEq ℝ W hWfin
  let o : Orientation ℝ W (Fin 2) := bW.orientation
                                                          
  have hWinv : W.map ((euclideanIso g).toLinearEquiv :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = W := by
    rw [hWdef, Submodule.map_orthogonal_equiv]
    congr 1
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, hfix₀]
                                           
  let ρ : W ≃ₗᵢ[ℝ] W :=
    (LinearIsometryEquiv.submoduleMap W (euclideanIso g)).trans
      (LinearIsometryEquiv.ofEq _ W hWinv)
  have coeρ : ∀ y : W, ((ρ y : W) : EuclideanSpace ℝ (Fin 3)) = euclideanIso g (y : W) := by
    intro y
    change ((LinearIsometryEquiv.ofEq _ W hWinv
      (LinearIsometryEquiv.submoduleMap W (euclideanIso g) y) : W) :
        EuclideanSpace ℝ (Fin 3)) = _
    rw [LinearIsometryEquiv.coe_ofEq_apply, LinearIsometryEquiv.submoduleMap_apply_coe]
                                                                 
  have hdet : (0 : ℝ) < LinearMap.det (ρ.toLinearEquiv : W →ₗ[ℝ] W) := by
    have hmaps : W ≤ W.comap (euclideanIso g).toLinearMap := by
      intro y hy
      have hmem : (euclideanIso g) y ∈ W := by
        have := hWinv ▸ Submodule.mem_map_of_mem
          (f := (euclideanIso g).toLinearEquiv.toLinearMap) hy
        simpa using this
      exact hmem
    have hrestrict :
        (euclideanIso g).toLinearMap.restrict hmaps = ρ.toLinearMap := by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply]
      exact (coeρ y).symm
    have hquot : W.mapQ W (euclideanIso g).toLinearMap hmaps = LinearMap.id := by
      have hu₀W : u₀ ∉ W := by
        rw [hWdef]
        intro hmem
        have h0 : ⟪u₀, u₀⟫ = (0 : ℝ) :=
          (Submodule.mem_orthogonal _ _).mp hmem u₀ (Submodule.mem_span_singleton_self _)
        exact hu₀ (inner_self_eq_zero.mp h0)
      have hne : W.mkQ u₀ ≠ 0 := by
        rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hu₀W
      have hspan : Submodule.span ℝ {W.mkQ u₀} = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hq : finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ W) + finrank ℝ W
            = finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.finrank_quotient_add_finrank W
        rw [hWfin, finrank_euclideanSpace_fin] at hq
        rw [finrank_span_singleton hne]
        omega
      refine LinearMap.ext_on hspan ?_
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        show (euclideanIso g).toLinearMap u₀ = u₀ from hfix₀]
    have hE : LinearMap.det (euclideanIso g).toLinearMap = 1 := euclideanIso_det g
    rw [LinearMap.det_eq_det_mul_det (W := W) _ hmaps, hrestrict, hquot,
      LinearMap.det_id, mul_one] at hE
    rw [show (ρ.toLinearEquiv : W →ₗ[ℝ] W) = ρ.toLinearMap from rfl, hE]
    norm_num
  obtain ⟨α, hα⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos hdet
                                                                                       
  have key : ∀ w : W, ρ w = w → w = 0 := by
    intro w hw
    by_contra hw0
                       
    have hangle : o.oangle w (ρ w) = α := by rw [hα, o.oangle_rotation_self_right hw0]
    rw [hw, o.oangle_self] at hangle
                                                                        
    have hρrefl : ρ = LinearIsometryEquiv.refl ℝ W := by
      rw [hα, ← hangle, o.rotation_zero]
    have hallfix : (euclideanIso g).toLinearMap = LinearMap.id := by
      have hle : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≤
          LinearMap.eqLocus (euclideanIso g).toLinearMap LinearMap.id := by
        have hsup : (ℝ ∙ u₀) ⊔ W = ⊤ := by
          rw [hWdef]; exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
        rw [← hsup]
        refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst hz
          simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.id_coe, id_eq]
          exact hfix₀
        · intro z hz
          simp only [LinearMap.mem_eqLocus, LinearMap.id_coe, id_eq]
          have hz' := coeρ ⟨z, hz⟩
          rw [hρrefl] at hz'
          simpa using hz'.symm
      have htop := top_le_iff.mp hle
      exact LinearMap.ext fun z => (LinearMap.mem_eqLocus.mp (htop ▸ Submodule.mem_top))
                                                         
    have hmat : (g : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      have hlin : toEuclideanLin (g : Matrix (Fin 3) (Fin 3) ℝ)
          = toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [toEuclideanLin_one]; exact hallfix
      exact toEuclideanLin.injective hlin
    exact hg (Subtype.ext (hmat.trans (Submonoid.coe_one _).symm))
                                                                                          
  set p : EuclideanSpace ℝ (Fin 3) := (⟪u₀, x⟫) • u₀ with hpdef
  set w : EuclideanSpace ℝ (Fin 3) := x - p with hwdef
  have hpmem : p ∈ ℝ ∙ u₀ := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u₀)
  have hwW : w ∈ W := by
    rw [hWdef, Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [hwdef, hpdef, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, hu₀unit]
    ring
                                                                       
  have hgp : euclideanIso g p = p := by
    rw [hpdef, map_smul, hfix₀]
  have hgw : euclideanIso g w = w := by
    rw [hwdef, map_sub, hx, hgp]
  have hρw : ρ ⟨w, hwW⟩ = ⟨w, hwW⟩ := by
    apply Subtype.ext
    rw [coeρ]
    exact hgw
  have hw0 : w = 0 := congrArg (Subtype.val) (key ⟨w, hwW⟩ hρw)
  have hxp : x = p := by
    have : x - p = 0 := hwdef ▸ hw0
    exact sub_eq_zero.mp this
  rw [hxp]; exact hpmem

                                                                                         
                                                                                         
                                                  
/-- The set attached to a nonidentity rotation is the displayed antipodal pair of unit vectors. -/
theorem rotationAxisSet_eq_pair (g : specialOrthogonalGroup (Fin 3) ℝ) (hg : g ≠ 1) :
    ∃ v₀ : Fin 3 → ℝ, v₀ ⬝ᵥ v₀ = 1 ∧ rotationAxisSet g = {v₀, -v₀} := by
  classical
                                                               
  obtain ⟨v, hv0, hvfix⟩ := exists_ne_zero_fixed_vector g hg
  have hvpos : 0 < v ⬝ᵥ v := by
    have hne : (toLp 2 v : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
      intro h; exact hv0 (by have := congrArg ofLp h; simpa using this)
    have hself := real_inner_self_eq_norm_sq (toLp 2 v : EuclideanSpace ℝ (Fin 3))
    rw [inner_toLp] at hself
    rw [hself]
    exact pow_pos (norm_pos_iff.2 hne) 2
  set c : ℝ := Real.sqrt (v ⬝ᵥ v) with hc
  have hcpos : 0 < c := by rw [hc]; exact Real.sqrt_pos.2 hvpos
  have hcsq : c * c = v ⬝ᵥ v := by rw [hc]; exact Real.mul_self_sqrt (le_of_lt hvpos)
  set v₀ : Fin 3 → ℝ := c⁻¹ • v with hv₀def
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hv₀unit : v₀ ⬝ᵥ v₀ = 1 := by
    have h : v₀ ⬝ᵥ v₀ = (c⁻¹ * c⁻¹) * (v ⬝ᵥ v) := by
      rw [hv₀def, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [h, ← hcsq]; field_simp
  have hv₀fix : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v₀ = v₀ := by
    rw [hv₀def, mulVec_smul, hvfix]
  refine ⟨v₀, hv₀unit, ?_⟩
                                 
  set u₀ : EuclideanSpace ℝ (Fin 3) := toLp 2 v₀ with hu₀def
  have hofLpu₀ : ofLp u₀ = v₀ := rfl
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    apply hv0
    have : v₀ = 0 := by rw [← hofLpu₀, h, ofLp_zero]
    rw [hv₀def] at this
    have := smul_eq_zero.1 this
    rcases this with h1 | h1
    · exact absurd (inv_eq_zero.1 h1) hcne
    · exact h1
  have hfixu₀ : euclideanIso g u₀ = u₀ :=
    euclideanIso_fix g u₀ (by rw [hofLpu₀]; exact hv₀fix)
  have hu₀norm : ‖u₀‖ = 1 := by
    have : ⟪u₀, u₀⟫ = 1 := by rw [hu₀def, inner_toLp]; exact hv₀unit
    have h2 : ‖u₀‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact this
    nlinarith [norm_nonneg u₀]
                      
  ext y
  simp only [rotationAxisSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyunit, hyfix⟩
                                   
    set u : EuclideanSpace ℝ (Fin 3) := toLp 2 y with hudef
    have hofLpu : ofLp u = y := rfl
    have hfixu : euclideanIso g u = u := euclideanIso_fix g u (by rw [hofLpu]; exact hyfix)
    have humem : u ∈ ℝ ∙ u₀ :=
      euclidean_fixed_mem_axis g hg u₀ (by rw [hu₀def, inner_toLp]; exact hv₀unit) hfixu₀ hfixu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp humem
                
    have hunorm : ‖u‖ = 1 := by
      have : ⟪u, u⟫ = 1 := by rw [hudef, inner_toLp]; exact hyunit
      have h2 : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact this
      nlinarith [norm_nonneg u]
                               
    have htnorm : |t| = 1 := by
      have : ‖u‖ = |t| * ‖u₀‖ := by rw [← ht, norm_smul, Real.norm_eq_abs]
      rw [hunorm, hu₀norm, mul_one] at this
      exact this.symm
    have htpm : t = 1 ∨ t = -1 := abs_eq (by norm_num) |>.mp htnorm
                                    
    have hyeq : y = t • v₀ := by
      rw [← hofLpu, ← ht, ← hofLpu₀]
      rfl
    rcases htpm with h1 | h1
    · left; rw [hyeq, h1, one_smul]
    · right; rw [hyeq, h1, neg_one_smul]
  · rintro (rfl | rfl)
    · exact ⟨hv₀unit, hv₀fix⟩
    · refine ⟨?_, ?_⟩
      · rw [dotProduct_neg, neg_dotProduct, neg_neg]; exact hv₀unit
      · rw [mulVec_neg, hv₀fix]

                                                                                         
/-- The set associated with a nonidentity displayed rotation is finite. -/
theorem finite_rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ) (hg : g ≠ 1) :
    (rotationAxisSet g).Finite := by
  obtain ⟨v₀, _, hset⟩ := rotationAxisSet_eq_pair g hg
  rw [hset]
  exact (Set.finite_singleton _).insert _

                                                                                          
                                                                                               
             
/-- The displayed set of rotation axes of a finite subgroup is finite. -/
theorem finite_rotationAxes (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] :
    (rotationAxes G).Finite := by
  classical
                                                  
  have hidx : {g : specialOrthogonalGroup (Fin 3) ℝ | g ∈ G ∧ g ≠ 1}.Finite :=
    (Set.toFinite (G : Set (specialOrthogonalGroup (Fin 3) ℝ))).subset
      (fun g hg => hg.1)
                                                                  
  refine Set.Finite.subset (hidx.biUnion (fun g hg => finite_rotationAxisSet g hg.2)) ?_
  intro v hv
  obtain ⟨hunit, g, hgG, hgne, hgfix⟩ := hv
  exact Set.mem_biUnion (show g ∈ {g | g ∈ G ∧ g ≠ 1} from ⟨hgG, hgne⟩)
    (show v ∈ rotationAxisSet g from ⟨hunit, hgfix⟩)

end Poles

                                                                                              
                                                            
                                                                                          
                                                                                          
                                                                                        
                                                                                           
/-- A multiset satisfying the displayed divisibility and sum conditions has one of the listed forms. -/
theorem stabilizer_cardMultiset_cases (n : ℕ) (hn : 2 ≤ n) (m : Multiset ℕ)
    (hm2 : ∀ x ∈ m, 2 ≤ x) (hmdvd : ∀ x ∈ m, x ∣ n)
    (heq : 2 * (1 - (n : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum) :
    m = {n, n} ∨ (∃ k, n = 2 * k ∧ m = {2, 2, k}) ∨
    m = {2, 3, 3} ∨ m = {2, 3, 4} ∨ m = {2, 3, 5} := by
                                      
  have hnpos : 0 < n := by omega
  have hnpQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
  have hnne : (n : ℚ) ≠ 0 := ne_of_gt hnpQ
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
                                                      
  set N : ℚ := (n : ℚ)⁻¹ with hN
  set f : ℕ → ℚ := fun x => 1 - (x : ℚ)⁻¹ with hf
  have hNpos : 0 < N := by rw [hN]; positivity
  have hNle : N ≤ 1 / 2 := by
    rw [hN]
    have : (n : ℚ)⁻¹ ≤ (2 : ℚ)⁻¹ := inv_anti₀ (by norm_num) hnQ
    simpa using this
                                                                                      
  simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map, Function.comp_def] at heq
                                                   
  have hS : (m.map f).sum = 2 - 2 * N := by rw [hf, ← heq]; ring
  have hS1 : (1 : ℚ) ≤ (m.map f).sum := by rw [hS]; linarith
  have hS2 : (m.map f).sum < 2 := by rw [hS]; linarith
                                                     
  have inv_mono : ∀ p q : ℕ, 0 < p → p ≤ q → (q : ℚ)⁻¹ ≤ (p : ℚ)⁻¹ := by
    intro p q hp hpq
    have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    have hqQ : (p : ℚ) ≤ (q : ℚ) := by exact_mod_cast hpq
    exact inv_anti₀ hpQ hqQ
                                                                        
  have hlo : ∀ y ∈ m.map f, (1 : ℚ) / 2 ≤ y := by
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx2 : 2 ≤ x := hm2 x hx
    have : (x : ℚ)⁻¹ ≤ 1 / 2 := by
      have := inv_mono 2 x (by norm_num) hx2
      simpa using this
    rw [hf]; dsimp only; linarith
  have hlb : (m.card : ℚ) * (1 / 2) ≤ (m.map f).sum := by
    have := Multiset.card_nsmul_le_sum hlo
    rwa [Multiset.card_map, nsmul_eq_mul] at this
  have hcard3 : m.card ≤ 3 := by
    have h4 : (m.card : ℚ) < 4 := by linarith
    have : m.card < 4 := by exact_mod_cast h4
    omega
                                                             
  have hc_ne0 : m.card ≠ 0 := by
    rw [Ne, Multiset.card_eq_zero]
    rintro rfl
    simp only [Multiset.map_zero, Multiset.sum_zero] at hS1
    linarith
  have hc_ne1 : m.card ≠ 1 := by
    rw [Ne, Multiset.card_eq_one]
    rintro ⟨a, rfl⟩
    simp only [Multiset.map_singleton, Multiset.sum_singleton, hf] at hS1
    have ha2 : 2 ≤ a := hm2 a (by simp)
    have hapos : (0 : ℚ) < (a : ℚ)⁻¹ := by
      have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by omega)
      positivity
    linarith
  have hc23 : m.card = 2 ∨ m.card = 3 := by omega
  rcases hc23 with h2 | h3
  ·                                                                    
    rw [Multiset.card_eq_two] at h2
    obtain ⟨a, b, rfl⟩ := h2
    have hmem_a : a ∈ ({a, b} : Multiset ℕ) := by simp
    have hmem_b : b ∈ ({a, b} : Multiset ℕ) := by simp
    have ha2 : 2 ≤ a := hm2 a hmem_a
    have hb2 : 2 ≤ b := hm2 b hmem_b
    have hadvd : a ∣ n := hmdvd a hmem_a
    have hbdvd : b ∣ n := hmdvd b hmem_b
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, hf] at hS
    have hsum2 : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ = 2 * N := by linarith
    have hAgeN : N ≤ (a : ℚ)⁻¹ := by
      rw [hN]; exact inv_mono a n (by omega) (Nat.le_of_dvd hnpos hadvd)
    have hBgeN : N ≤ (b : ℚ)⁻¹ := by
      rw [hN]; exact inv_mono b n (by omega) (Nat.le_of_dvd hnpos hbdvd)
    have hAeq : (a : ℚ)⁻¹ = N := by linarith
    have hBeq : (b : ℚ)⁻¹ = N := by linarith
    have ha_eq : a = n := by
      have h := hAeq; rw [hN] at h
      have : (a : ℚ) = (n : ℚ) := inv_injective h
      exact_mod_cast this
    have hb_eq : b = n := by
      have h := hBeq; rw [hN] at h
      have : (b : ℚ) = (n : ℚ) := inv_injective h
      exact_mod_cast this
    left; rw [ha_eq, hb_eq]
  ·                                                           
    have hl_len : (m.sort (· ≤ ·)).length = 3 := by rw [Multiset.length_sort]; exact h3
    have hl_sorted : (m.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort m (· ≤ ·)
    have hl_coe : (↑(m.sort (· ≤ ·)) : Multiset ℕ) = m := Multiset.sort_eq m (· ≤ ·)
    obtain ⟨a, b, c, hl⟩ := List.length_eq_three.mp hl_len
    rw [hl] at hl_sorted hl_coe
    rw [List.pairwise_cons] at hl_sorted
    obtain ⟨ha_all, hl_sorted⟩ := hl_sorted
    rw [List.pairwise_cons] at hl_sorted
    obtain ⟨hb_all, _⟩ := hl_sorted
    have hab : a ≤ b := ha_all b (by simp)
    have hbc : b ≤ c := hb_all c (by simp)
    have hm_eq : m = {a, b, c} := by rw [← hl_coe]; rfl
    have hmem_a : a ∈ m := by rw [hm_eq]; simp
    have hmem_b : b ∈ m := by rw [hm_eq]; simp
    have hmem_c : c ∈ m := by rw [hm_eq]; simp
    have ha2 : 2 ≤ a := hm2 a hmem_a
    have hb2 : 2 ≤ b := hm2 b hmem_b
    have hc2 : 2 ≤ c := hm2 c hmem_c
    rw [hm_eq] at hS
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, hf] at hS
    have habc : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1 + 2 * N := by linarith
                                      
    have ha_eq : a = 2 := by
      by_contra hne
      have ha3 : 3 ≤ a := by omega
      have hb3 : 3 ≤ b := le_trans ha3 hab
      have hc3 : 3 ≤ c := le_trans hb3 hbc
      have hA : (a : ℚ)⁻¹ ≤ 1 / 3 :=
        le_trans (inv_mono 3 a (by norm_num) ha3) (by norm_num)
      have hB : (b : ℚ)⁻¹ ≤ 1 / 3 :=
        le_trans (inv_mono 3 b (by norm_num) hb3) (by norm_num)
      have hC : (c : ℚ)⁻¹ ≤ 1 / 3 :=
        le_trans (inv_mono 3 c (by norm_num) hc3) (by norm_num)
      linarith
    subst ha_eq
    have h2inv : ((2 : ℕ) : ℚ)⁻¹ = 1 / 2 := by norm_num
    have hBC : (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1 / 2 + 2 * N := by linarith [habc, h2inv]
                                           
    have hb_lt : b < 4 := by
      by_contra hbb
      rw [not_lt] at hbb
      have hc4 : 4 ≤ c := le_trans hbb hbc
      have hB : (b : ℚ)⁻¹ ≤ 1 / 4 :=
        le_trans (inv_mono 4 b (by norm_num) hbb) (by norm_num)
      have hC : (c : ℚ)⁻¹ ≤ 1 / 4 :=
        le_trans (inv_mono 4 c (by norm_num) hc4) (by norm_num)
      linarith
    interval_cases b
    ·                                                
      have hCval : (c : ℚ)⁻¹ = 2 * N := by linarith [hBC, h2inv]
      have hcpos : (0 : ℚ) < (c : ℚ) := by exact_mod_cast (show 0 < c by omega)
      have hcne : (c : ℚ) ≠ 0 := ne_of_gt hcpos
      rw [hN] at hCval
      have hnc : (n : ℚ) = 2 * c := by
        field_simp at hCval
        linarith [hCval]
      have : n = 2 * c := by exact_mod_cast hnc
      right; left; exact ⟨c, this, hm_eq⟩
    ·                                                                 
      have h3inv : ((3 : ℕ) : ℚ)⁻¹ = 1 / 3 := by norm_num
      have hCval2 : (c : ℚ)⁻¹ = 1 / 6 + 2 * N := by linarith [hBC, h3inv]
      have hc_ge : 3 ≤ c := by omega
      have hc_lt : c < 6 := by
        by_contra hcc
        rw [not_lt] at hcc
        have hC6 : (c : ℚ)⁻¹ ≤ 1 / 6 :=
          le_trans (inv_mono 6 c (by norm_num) hcc) (by norm_num)
        linarith
      interval_cases c
      · right; right; left; exact hm_eq
      · right; right; right; left; exact hm_eq
      · right; right; right; right; exact hm_eq

section PoleCounting
open Matrix MulAction

                                                                                         
                                                                                            
                                          
/-- A vector fixed by a subgroup remains fixed after applying one of its elements. -/
lemma isFixedVector_smul {G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ∈ G) {v : Fin 3 → ℝ} (hv : IsFixedVector G v) :
    IsFixedVector G ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) := by
  obtain ⟨hunit, h, hhG, hhne, hhfix⟩ := hv
  refine ⟨by rw [matrixAction_011812]; exact hunit, g * h * g⁻¹,
    G.mul_mem (G.mul_mem hg hhG) (G.inv_mem hg), ?_, ?_⟩
  ·                                      
    intro hcontra
    apply hhne
    calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [hcontra]
      _ = 1 := by group
  ·                                                                                 
    rw [mulVec_mulVec, ← Submonoid.coe_mul, show g * h * g⁻¹ * g = g * h from by group,
      Submonoid.coe_mul, ← mulVec_mulVec, hhfix]

                                                                     
/-- The displayed action of a subgroup on its rotation-axis set. -/
instance rotationAxesAction (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) :
    MulAction (↥G) (↥(rotationAxes G)) where
  smul x P := ⟨((x : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ P.1,
    isFixedVector_smul x.2 P.2⟩
  one_smul P := by
    apply Subtype.ext
    change (((1 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ P.1 = P.1
    simp
  mul_smul x y P := by
    apply Subtype.ext
    change (((x * y : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ P.1
        = ((x : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          (((y : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ P.1)
    rw [show ((x * y : ↥G) : specialOrthogonalGroup (Fin 3) ℝ)
        = (x : specialOrthogonalGroup (Fin 3) ℝ) * (y : specialOrthogonalGroup (Fin 3) ℝ) from rfl,
      Submonoid.coe_mul, mulVec_mulVec]

/-- A matrix identity for the displayed action or transformation. -/
@[simp] lemma matrixAction_011755 {G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    (x : ↥G) (P : ↥(rotationAxes G)) :
    ((x • P : ↥(rotationAxes G)) : Fin 3 → ℝ)
      = ((x : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ P.1 := rfl

                                                                                             
                                                                                              
                                                                                          
                                                                                           
                                                                                             
                                                                 

                                                                                             
                                                                                           
                                                                                                
                                                                                  
/-- A finite subgroup admits a multiset of stabilizer cardinalities with the displayed properties. -/
theorem exists_stabilizer_cardMultiset (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (hn : 2 ≤ Nat.card G) :
    ∃ m : Multiset ℕ,
      (∀ x ∈ m, 2 ≤ x) ∧ (∀ x ∈ m, x ∣ Nat.card G) ∧
      2 * (1 - (Nat.card G : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum ∧
      (m = {Nat.card G, Nat.card G} ∨
       (∃ k, Nat.card G = 2 * k ∧ m = {2, 2, k}) ∨
       m = {2, 3, 3} ∨ m = {2, 3, 4} ∨ m = {2, 3, 5}) ∧
      (∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (stabilizer (↥G) b) = x) := by
  classical
  haveI : Finite ↥(rotationAxes G) := (finite_rotationAxes G).to_subtype
  haveI hFG : Fintype ↥G := Fintype.ofFinite _
  haveI : Fintype ↥(rotationAxes G) := Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient ↥G ↥(rotationAxes G)) := Fintype.ofFinite _
  haveI : ∀ b : ↥(rotationAxes G), Fintype (stabilizer ↥G b) := fun _ => Fintype.ofFinite _
  haveI : ∀ b : ↥(rotationAxes G), Fintype (orbit ↥G b) := fun _ => Fintype.ofFinite _
  haveI : ∀ g : ↥G, Fintype (fixedBy ↥(rotationAxes G) g) := fun _ => Fintype.ofFinite _
  set Ω := orbitRel.Quotient ↥G ↥(rotationAxes G) with hΩ
                                                                                          
  set n : ℕ := Fintype.card ↥G with hn_fc
  set mω : Ω → ℕ := fun ω => Fintype.card (stabilizer ↥G ω.out) with hmω
  set oω : Ω → ℕ := fun ω => Fintype.card (orbit ↥G ω.out) with hoω
  have hnpos : 0 < n := by rw [hn_fc]; exact Fintype.card_pos
  have hNn : Nat.card G = n := by rw [hn_fc, Nat.card_eq_fintype_card]
  rw [hNn] at hn
                                     
  have horbstab : ∀ ω : Ω, oω ω * mω ω = n := fun ω =>
    card_orbit_mul_card_stabilizer_eq_card_group ↥G ω.out
                                                  
  have hmdvd : ∀ ω : Ω, mω ω ∣ n := by
    intro ω
    have h := Subgroup.card_subgroup_dvd_card (stabilizer ↥G ω.out)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    exact h
                                                                               
  have hm2 : ∀ ω : Ω, 2 ≤ mω ω := by
    intro ω
    change 2 ≤ Fintype.card ↥(stabilizer ↥G ω.out)
    obtain ⟨_, h, hhG, hhne, hhfix⟩ := ω.out.2
    have hstab : (⟨h, hhG⟩ : ↥G) ∈ stabilizer ↥G ω.out := by
      rw [mem_stabilizer_iff]
      apply Subtype.ext
      change (h : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (ω.out : ↥(rotationAxes G)).1 = (ω.out : ↥(rotationAxes G)).1
      exact hhfix
    have hne : (⟨⟨h, hhG⟩, hstab⟩ : stabilizer ↥G ω.out) ≠ (1 : stabilizer ↥G ω.out) := by
      intro hcon
      apply hhne
      have h1 : (((⟨⟨h, hhG⟩, hstab⟩ : stabilizer ↥G ω.out) : ↥G) :
          specialOrthogonalGroup (Fin 3) ℝ)
          = (((1 : stabilizer ↥G ω.out) : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) := by
        rw [hcon]
      simpa using h1
    have h1 : 1 < Fintype.card ↥(stabilizer ↥G ω.out) :=
      Fintype.one_lt_card_iff_nontrivial.mpr (nontrivial_of_ne _ _ hne)
    omega
                                                          
  have hFix1 : Fintype.card ↥(fixedBy ↥(rotationAxes G) (1 : ↥G)) = Fintype.card ↥(rotationAxes G) :=
    Fintype.card_congr
      (Equiv.subtypeUnivEquiv (fun x => mem_fixedBy.mpr (one_smul (↥G) x)))
                                                                                    
  have hFix2 : ∀ g : ↥G, g ≠ 1 → Fintype.card ↥(fixedBy ↥(rotationAxes G) g) = 2 := by
    intro g hg
    have hg0 : (g : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := by
      intro h; exact hg (Subtype.ext (by simpa using h))
    obtain ⟨v₀, hv₀unit, hset⟩ := rotationAxisSet_eq_pair (g : _) hg0
    have hv₀ne : v₀ ≠ -v₀ := by
      intro h
      have hd : v₀ ⬝ᵥ v₀ = -(v₀ ⬝ᵥ v₀) := by
        nth_rewrite 1 [h]
        rw [neg_dotProduct]
      rw [hv₀unit] at hd
      norm_num at hd
    set f : ↥(fixedBy ↥(rotationAxes G) g) → (Fin 3 → ℝ) := fun x => x.1.1 with hf
    have hfinj : Function.Injective f := fun a b hab => Subtype.ext (Subtype.ext hab)
    have hrange : Set.range f = rotationAxisSet (g : _) := by
      ext y
      constructor
      · rintro ⟨⟨⟨v, hvpole⟩, hvfix⟩, rfl⟩
        refine ⟨hvpole.1, ?_⟩
        have := mem_fixedBy.mp hvfix
        have h2 := congrArg (fun z => (z : ↥(rotationAxes G)).1) this
        simpa using h2
      · rintro ⟨hyunit, hyfix⟩
        have hypole : IsFixedVector G y :=
          ⟨hyunit, (g : _), g.2, hg0, hyfix⟩
        refine ⟨⟨⟨y, hypole⟩, ?_⟩, rfl⟩
        rw [mem_fixedBy]
        apply Subtype.ext
        change (g : specialOrthogonalGroup (Fin 3) ℝ).1 *ᵥ y = y
        exact hyfix
    have e := Equiv.ofInjective f hfinj
    rw [hrange, hset] at e
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair hv₀ne]
                                     
  have hburnside : (∑ g : ↥G, Fintype.card ↥(fixedBy ↥(rotationAxes G) g)) = Fintype.card Ω * n :=
    sum_card_fixedBy_eq_card_orbits_mul_card_group ↥G ↥(rotationAxes G)
                                                                      
  have hsplit : (∑ g : ↥G, Fintype.card ↥(fixedBy ↥(rotationAxes G) g))
      = Fintype.card ↥(rotationAxes G) + 2 * (n - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥G)), hFix1,
      Finset.sum_congr rfl (fun g hg => hFix2 g (Finset.ne_of_mem_erase hg)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← hn_fc, smul_eq_mul]
    ring
                                             
  have hPsum : Fintype.card ↥(rotationAxes G) = ∑ ω : Ω, n / mω ω :=
    card_eq_sum_card_group_div_card_stabilizer ↥G ↥(rotationAxes G)
                                                
  have hIII : Fintype.card Ω * n = (∑ ω : Ω, n / mω ω) + 2 * (n - 1) := by
    rw [← hburnside, hsplit, hPsum]
                                                         
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
                                                            
  have hoval : ∀ ω : Ω, (oω ω : ℚ) = (n : ℚ) * (mω ω : ℚ)⁻¹ := by
    intro ω
    have hprod : (oω ω : ℚ) * (mω ω : ℚ) = (n : ℚ) := by exact_mod_cast horbstab ω
    have hmpos : (mω ω : ℚ) ≠ 0 := by
      have : 0 < mω ω := lt_of_lt_of_le (by norm_num) (hm2 ω)
      exact_mod_cast this.ne'
    field_simp
    linarith [hprod]
                                         
  have hdivval : ∀ ω : Ω, ((n / mω ω : ℕ) : ℚ) = (oω ω : ℚ) := by
    intro ω
    rw [Nat.cast_div (hmdvd ω)]
    · rw [hoval ω]; ring
    · have : 0 < mω ω := lt_of_lt_of_le (by norm_num) (hm2 ω)
      exact_mod_cast this.ne'
                                       
  have hterm : ∀ ω : Ω, (1 : ℚ) - (mω ω : ℚ)⁻¹ = ((n : ℚ) - (oω ω : ℚ)) / (n : ℚ) := by
    intro ω
    rw [hoval ω]
    field_simp
                      
  have hsum : (∑ ω : Ω, ((1 : ℚ) - (mω ω : ℚ)⁻¹)) = 2 * (1 - (n : ℚ)⁻¹) := by
    have hcast : (Fintype.card Ω : ℚ) * (n : ℚ)
        = (∑ ω : Ω, ((n / mω ω : ℕ) : ℚ)) + 2 * ((n : ℚ) - 1) := by
      have := congrArg (fun z : ℕ => (z : ℚ)) hIII
      push_cast [Nat.cast_sub hnpos] at this ⊢
      convert this using 2
    calc (∑ ω : Ω, ((1 : ℚ) - (mω ω : ℚ)⁻¹))
        = ∑ ω : Ω, ((n : ℚ) - (oω ω : ℚ)) / (n : ℚ) := by
          exact Finset.sum_congr rfl (fun ω _ => hterm ω)
      _ = (∑ ω : Ω, ((n : ℚ) - (oω ω : ℚ))) / (n : ℚ) := by rw [← Finset.sum_div]
      _ = ((Fintype.card Ω : ℚ) * (n : ℚ) - ∑ ω : Ω, (oω ω : ℚ)) / (n : ℚ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 2 * (1 - (n : ℚ)⁻¹) := by
          rw [hcast, Finset.sum_congr rfl (fun ω _ => (hdivval ω).symm)]
          field_simp
          ring
                                                                
  refine ⟨(Finset.univ : Finset Ω).val.map mω, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨ω, _, rfl⟩ := hx
    exact hm2 ω
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨ω, _, rfl⟩ := hx
    rw [hNn]; exact hmdvd ω
  · rw [hNn]
    simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map, Function.comp_def]
    exact hsum.symm
  · rw [hNn]
    exact stabilizer_cardMultiset_cases n hn ((Finset.univ : Finset Ω).val.map mω)
      (by intro x hx; rw [Multiset.mem_map] at hx; obtain ⟨ω, _, rfl⟩ := hx; exact hm2 ω)
      (by intro x hx; rw [Multiset.mem_map] at hx; obtain ⟨ω, _, rfl⟩ := hx; exact hmdvd ω)
      (by
        simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map, Function.comp_def]
        exact hsum.symm)
  ·                                                                                          
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨ω, _, rfl⟩ := hx
    exact ⟨ω.out, by rw [Nat.card_eq_fintype_card, hmω]⟩

                                                                                            
                                                                                               
                                                                                                
                                                                                             
                                                                                         
/-- A cyclicity conclusion under the hypotheses shown in the formal statement. -/
theorem cyclicGroup_011643
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (b : ↥(rotationAxes G)) :
    IsCyclic (stabilizer (↥G) b) := by
  classical
                                                                                 
  let φ : stabilizer (↥G) b →* specialOrthogonalGroup (Fin 3) ℝ :=
    (G.subtype).comp ((stabilizer (↥G) b).subtype)
  have hφinj : Function.Injective φ := fun x y hxy => Subtype.ext (Subtype.ext hxy)
                                           
  have hbunit : (b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1 = 1 := b.2.1
  have hv0 : (b : ↥(rotationAxes G)).1 ≠ 0 := by
    intro h; rw [h] at hbunit; simp at hbunit
                                            
  have hfix : ∀ g : φ.range,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (b : ↥(rotationAxes G)).1 = (b : ↥(rotationAxes G)).1 := by
    rintro ⟨g, x, rfl⟩
    have hx := (mem_stabilizer_iff).mp x.2
    have hval := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) hx
    rwa [matrixAction_011755] at hval
                                                                                           
  haveI : Finite (stabilizer (↥G) b) := inferInstance
  haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : IsCyclic φ.range :=
    cyclicGroup_011638 φ.range (b : ↥(rotationAxes G)).1 hv0 hfix
  exact (MulEquiv.isCyclic (MonoidHom.ofInjective hφinj)).mpr inferInstance

end PoleCounting

   
                       

                                                                                       
                                                                                     
                                                                                           
                                                                                         
                                                                                                

                                                                                          
                                                                                                  
/-- Existence of the displayed multiplicative equivalence under the stated hypotheses. -/
theorem multiplicativeEquivalence_011715
    {G : Type*} [Group G] [Finite G] (k : ℕ) [NeZero k]
    (ρ s : G) (hρ : orderOf ρ = k) (hs : orderOf s = 2)
    (hconj : s * ρ * s⁻¹ = ρ⁻¹) (hsnotin : s ∉ Subgroup.zpowers ρ)
    (hcard : Nat.card G = 2 * k) :
    Nonempty (G ≃* DihedralGroup k) := by
  classical
                                                                 
  set ρz : ZMod k → G := fun i => ρ ^ i.val with hρz
  have hρz_add : ∀ i j : ZMod k, ρz (i + j) = ρz i * ρz j := by
    intro i j
    change ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val
    rw [← pow_add]
    apply pow_eq_pow_iff_modEq.mpr
    rw [hρ, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hρz_zero : ρz 0 = 1 := by
    change ρ ^ (0 : ZMod k).val = 1
    rw [ZMod.val_zero, pow_zero]
  have hρz_neg : ∀ i : ZMod k, ρz (-i) = (ρz i)⁻¹ := by
    intro i
    rw [eq_inv_iff_mul_eq_one, ← hρz_add, neg_add_cancel, hρz_zero]
                                                       
  have hs2 : s * s = 1 := by
    have h : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    rwa [pow_two] at h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hconj_pow : ∀ i : ZMod k, s * ρz i * s⁻¹ = (ρz i)⁻¹ := by
    intro i
    change s * ρ ^ i.val * s⁻¹ = (ρ ^ i.val)⁻¹
    have hsc : SemiconjBy s ρ ρ⁻¹ := by
      change s * ρ = ρ⁻¹ * s
      rw [← hconj, mul_assoc, inv_mul_cancel, mul_one]
    have hp := hsc.pow_right i.val
    rw [SemiconjBy, inv_pow] at hp
    rw [hp, mul_assoc, mul_inv_cancel, mul_one]
                                                                   
  have hcomm : ∀ i : ZMod k, ρz i * s = s * (ρz i)⁻¹ := by
    intro i
    have h := hconj_pow i
    rw [hsinv] at h
    calc ρz i * s = s * (s * ρz i * s) := by
            rw [← mul_assoc, ← mul_assoc, hs2, one_mul]
      _ = s * (ρz i)⁻¹ := by rw [h]
                                                                         
  let F : DihedralGroup k → G := fun x =>
    match x with
    | DihedralGroup.r i => ρz i
    | DihedralGroup.sr i => s * ρz i
  have hmul : ∀ a b : DihedralGroup k, F (a * b) = F a * F b := by
    rintro (i | i) (j | j)
    · change ρz (i + j) = ρz i * ρz j
      exact hρz_add i j
    · change s * ρz (j - i) = ρz i * (s * ρz j)
      have e1 : ρz i * (s * ρz j) = ρz i * s * ρz j := by group
      rw [e1, hcomm i]
      have e2 : s * (ρz i)⁻¹ * ρz j = s * ((ρz i)⁻¹ * ρz j) := by group
      rw [e2, ← hρz_neg, ← hρz_add, neg_add_eq_sub]
    · change s * ρz (i + j) = s * ρz i * ρz j
      rw [hρz_add, mul_assoc]
    · change ρz (j - i) = s * ρz i * (s * ρz j)
      have e1 : s * ρz i * (s * ρz j) = s * (ρz i * s) * ρz j := by group
      rw [e1, hcomm i]
      have e2 : s * (s * (ρz i)⁻¹) * ρz j = (s * s) * ((ρz i)⁻¹ * ρz j) := by group
      rw [e2, hs2, one_mul, ← hρz_neg, ← hρz_add, neg_add_eq_sub]
  let φ : DihedralGroup k →* G := MonoidHom.mk' F hmul
                                                                                  
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) hi
    · have hpow : ρ ^ i.val = 1 := hi
      have hdvd : orderOf ρ ∣ i.val := orderOf_dvd_of_pow_eq_one hpow
      rw [hρ] at hdvd
      have hval : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
      rw [show (DihedralGroup.r i : DihedralGroup k) = DihedralGroup.r 0 by
        rw [(ZMod.val_eq_zero i).mp hval], DihedralGroup.r_zero]
    · exfalso
      have hsval : s * ρ ^ i.val = 1 := hi
      have hs_eq : s = (ρ ^ i.val)⁻¹ := eq_inv_iff_mul_eq_one.mpr hsval
      exact hsnotin (by
        rw [hs_eq]; exact inv_mem (Subgroup.npow_mem_zpowers ρ i.val))
                                                           
  haveI : Fintype G := Fintype.ofFinite G
  have hcardeq : Fintype.card (DihedralGroup k) = Fintype.card G := by
    rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcard]
  exact ⟨(MulEquiv.ofBijective φ
    ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcardeq⟩)).symm⟩

                                                                                                 
                                                                                    
                                                                                                 
                                                                                  
/-- If every group element fixes the displayed point, the group is cyclic. -/
theorem isCyclic_of_fixed_point
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (b : ↥(rotationAxes G)) (hb : ∀ g : ↥G, g • b = b) :
    IsCyclic G := by
  have hunit : (b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1 = 1 := b.2.1
  have hv0 : (b : ↥(rotationAxes G)).1 ≠ 0 := by
    intro h; rw [h] at hunit; simp at hunit
  refine cyclicGroup_011638 G (b : ↥(rotationAxes G)).1 hv0 (fun g => ?_)
  have hg := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) (hb g)
  rwa [matrixAction_011755] at hg

                                                                                                 
                                                                                                   
                                                                                                  
                                                                                           
/-- If a point stabilizer has the full group cardinality, the displayed group is cyclic. -/
theorem isCyclic_of_stabilizer_card_eq_card
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (b : ↥(rotationAxes G)) (hb : Nat.card (MulAction.stabilizer (↥G) b) = Nat.card (↥G)) :
    IsCyclic G := by
  have htop : MulAction.stabilizer (↥G) b = ⊤ := Subgroup.eq_top_of_card_eq _ hb
  refine isCyclic_of_fixed_point G b (fun g => ?_)
  exact (MulAction.mem_stabilizer_iff).mp (htop ▸ Subgroup.mem_top g)

                                                                                             
                                                                                                
                                                                                
                                                                                      
                                                              
/-- The displayed two-entry stabilizer-cardinality multiset implies that the group is cyclic. -/
theorem isCyclic_of_stabilizer_cardMultiset_eq_pair
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {Nat.card (↥G), Nat.card (↥G)})
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    IsCyclic G := by
  obtain ⟨b, hb⟩ := hpole (Nat.card (↥G)) (by rw [hclass]; simp)
  exact isCyclic_of_stabilizer_card_eq_card G b hb

section DihedralGeom
open scoped RealInnerProductSpace
open Matrix EuclideanSpace Submodule WithLp Module

                                                                                                
                                                                                           
                                                                                                    
                                     
private lemma so3_swap_induced_plane (g : specialOrthogonalGroup (Fin 3) ℝ)
    (β₀ : EuclideanSpace ℝ (Fin 3)) (hβ₀unit : ⟪β₀, β₀⟫ = (1 : ℝ))
    (hswap₀ : euclideanIso g β₀ = -β₀) :
    ∃ (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (_ : finrank ℝ W = 2)
      (f : W ≃ₗᵢ[ℝ] W),
      (ℝ ∙ β₀) ⊔ W = ⊤ ∧ β₀ ∉ W ∧
      (∀ y : W, ((f y : W) : EuclideanSpace ℝ (Fin 3)) = euclideanIso g (y : W)) ∧
      LinearMap.det (f.toLinearEquiv : W →ₗ[ℝ] W) < 0 ∧
      (∀ y : W, f (f y) = y) := by
  have hβ₀ : β₀ ≠ 0 := fun h => by simp [h] at hβ₀unit
  have hWfin : finrank ℝ (ℝ ∙ β₀)ᗮ = 2 := by
    haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
      ⟨by norm_num [finrank_euclideanSpace_fin]⟩
    exact Submodule.finrank_orthogonal_span_singleton (n := 2) hβ₀
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := (ℝ ∙ β₀)ᗮ with hWdef
  haveI : Fact (finrank ℝ W = 2) := ⟨hWfin⟩
  have hβ₀W : β₀ ∉ W := by
    rw [hWdef]
    intro hmem
    have h0 : ⟪β₀, β₀⟫ = (0 : ℝ) :=
      (Submodule.mem_orthogonal _ _).mp hmem β₀ (Submodule.mem_span_singleton_self _)
    exact hβ₀ (inner_self_eq_zero.mp h0)
  have hsup : (ℝ ∙ β₀) ⊔ W = ⊤ := by
    rw [hWdef]; exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
                                                         
  have hWinv : W.map ((euclideanIso g).toLinearEquiv :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = W := by
    rw [hWdef, Submodule.map_orthogonal_equiv]
    congr 1
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, hswap₀, ← Set.neg_singleton, Submodule.span_neg]
  let f : W ≃ₗᵢ[ℝ] W :=
    (LinearIsometryEquiv.submoduleMap W (euclideanIso g)).trans
      (LinearIsometryEquiv.ofEq _ W hWinv)
  have coef : ∀ y : W, ((f y : W) : EuclideanSpace ℝ (Fin 3)) = euclideanIso g (y : W) := by
    intro y
    change ((LinearIsometryEquiv.ofEq _ W hWinv
      (LinearIsometryEquiv.submoduleMap W (euclideanIso g) y) : W) :
        EuclideanSpace ℝ (Fin 3)) = _
    rw [LinearIsometryEquiv.coe_ofEq_apply, LinearIsometryEquiv.submoduleMap_apply_coe]
                                                                                        
  have hmaps : W ≤ W.comap (euclideanIso g).toLinearMap := by
    intro y hy
    have hmem : (euclideanIso g) y ∈ W := by
      have := hWinv ▸ Submodule.mem_map_of_mem
        (f := (euclideanIso g).toLinearEquiv.toLinearMap) hy
      simpa using this
    exact hmem
  have hrestrict : (euclideanIso g).toLinearMap.restrict hmaps = f.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    exact (coef y).symm
  have hquot : W.mapQ W (euclideanIso g).toLinearMap hmaps = -LinearMap.id := by
    have hne : W.mkQ β₀ ≠ 0 := by
      rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hβ₀W
    have hspan : Submodule.span ℝ {W.mkQ β₀} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hq : finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ W) + finrank ℝ W
          = finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.finrank_quotient_add_finrank W
      rw [hWfin, finrank_euclideanSpace_fin] at hq
      rw [finrank_span_singleton hne]
      omega
    refine LinearMap.ext_on hspan ?_
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.neg_apply, LinearMap.id_apply,
      show (euclideanIso g).toLinearMap β₀ = -β₀ from hswap₀, ← Submodule.mkQ_apply, map_neg,
      Submodule.mkQ_apply]
  have hfrankQ : finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ W) = 1 := by
    have hq : finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ W) + finrank ℝ W
        = finrank ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.finrank_quotient_add_finrank W
    rw [hWfin, finrank_euclideanSpace_fin] at hq; omega
  have hE : LinearMap.det (euclideanIso g).toLinearMap = 1 := euclideanIso_det g
  rw [LinearMap.det_eq_det_mul_det (W := W) _ hmaps, hrestrict, hquot] at hE
  have hdetQ : LinearMap.det (-LinearMap.id : (EuclideanSpace ℝ (Fin 3) ⧸ W) →ₗ[ℝ] _) = -1 := by
    rw [show (-LinearMap.id : (EuclideanSpace ℝ (Fin 3) ⧸ W) →ₗ[ℝ] _)
        = (-1 : ℝ) • LinearMap.id from by ext x; simp, LinearMap.det_smul, hfrankQ, LinearMap.det_id]
    norm_num
  rw [hdetQ] at hE
  have hdetf : LinearMap.det (f.toLinearEquiv : W →ₗ[ℝ] W) < 0 := by
    have : LinearMap.det f.toLinearMap = -1 := by linarith [hE]
    rw [show (f.toLinearEquiv : W →ₗ[ℝ] W) = f.toLinearMap from rfl, this]; norm_num
                                                                                        
  let o : Orientation ℝ W (Fin 2) := (Module.finBasisOfFinrankEq ℝ W hWfin).orientation
  have hmapo : Orientation.map (Fin 2) f.toLinearEquiv o = -o :=
    (o.map_eq_neg_iff_det_neg f.toLinearEquiv (by rw [Fintype.card_fin, hWfin])).mpr hdetf
  have hf2 : ∀ y : W, f (f y) = y := by
    intro y
    rcases eq_or_ne y 0 with hy | hy
    · rw [hy, map_zero, map_zero]
    · have hfy : f y ≠ 0 := fun h => hy (f.injective (by rw [h, map_zero]))
      have hf2y : f (f y) ≠ 0 := fun h => hfy (f.injective (by rw [h, map_zero]))
      have step1 : o.oangle (f y) (f (f y)) = -o.oangle y (f y) := by
        have h := o.oangle_map (f y) (f (f y)) f
        rw [f.symm_apply_apply, f.symm_apply_apply, hmapo,
          o.oangle_neg_orientation_eq_neg] at h
        exact neg_eq_iff_eq_neg.mp h
      have step2 : o.oangle y (f (f y)) = 0 := by
        rw [← o.oangle_add hy hfy hf2y, step1, add_neg_cancel]
      have hnorm : ‖(y : W)‖ = ‖(f (f y) : W)‖ := by rw [f.norm_map, f.norm_map]
      have hrot := (o.rotation_oangle_eq_iff_norm_eq y (f (f y))).mpr hnorm
      rw [step2, o.rotation_zero] at hrot
      simp only [LinearIsometryEquiv.coe_refl, id_eq] at hrot
      exact hrot.symm
  exact ⟨W, hWfin, f, hsup, hβ₀W, coef, hdetf, hf2⟩

private lemma so3_sq_of_swap (g : specialOrthogonalGroup (Fin 3) ℝ)
    (β : Fin 3 → ℝ) (hβ : β ⬝ᵥ β = 1)
    (hswap : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = -β) :
    g * g = 1 := by
  classical
  set β₀ : EuclideanSpace ℝ (Fin 3) := toLp 2 β with hβ₀def
  have hofLp : ofLp β₀ = β := rfl
  have hβ₀unit : ⟪β₀, β₀⟫ = (1 : ℝ) := by rw [inner_toLp]; exact hβ
  have hswap₀ : euclideanIso g β₀ = -β₀ := by
    apply WithLp.ofLp_injective
    rw [euclideanIso_apply, ofLp_toEuclideanLin_apply, hofLp, hswap, ofLp_neg, hofLp]
  obtain ⟨W, _hWfin, f, hsup, _hβ₀W, coef, _hdetf, hf2⟩ :=
    so3_swap_induced_plane g β₀ hβ₀unit hswap₀
                                                                                          
  have hgg2 : (euclideanIso g).toLinearMap.comp (euclideanIso g).toLinearMap = LinearMap.id := by
    have hle : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≤
        LinearMap.eqLocus ((euclideanIso g).toLinearMap.comp (euclideanIso g).toLinearMap)
          LinearMap.id := by
      rw [← hsup]
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        subst hz
        simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.id_coe,
          id_eq]
        change euclideanIso g (euclideanIso g β₀) = β₀
        rw [hswap₀, map_neg, hswap₀, neg_neg]
      · intro z hz
        simp only [LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.id_coe, id_eq]
        change euclideanIso g (euclideanIso g z) = z
        have e1 : euclideanIso g z = ((f ⟨z, hz⟩ : W) : EuclideanSpace ℝ (Fin 3)) :=
          (coef ⟨z, hz⟩).symm
        have e2 : euclideanIso g ((f ⟨z, hz⟩ : W) : EuclideanSpace ℝ (Fin 3))
            = ((f (f ⟨z, hz⟩) : W) : EuclideanSpace ℝ (Fin 3)) := (coef (f ⟨z, hz⟩)).symm
        rw [e1, e2, hf2]
    have htop := top_le_iff.mp hle
    exact LinearMap.ext fun z => (LinearMap.mem_eqLocus.mp (htop ▸ Submodule.mem_top))
                                          
  have hmat : (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have hlin : toEuclideanLin ((g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ))
        = toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [← toEuclideanLin_comp, toEuclideanLin_one]
      exact hgg2
    exact toEuclideanLin.injective hlin
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_one]
  exact hmat

                                                                                                 
                                                                                                 
                                                                                        
private lemma so3_conj_of_swap (g ρ : specialOrthogonalGroup (Fin 3) ℝ)
    (β : Fin 3 → ℝ) (hβ : β ⬝ᵥ β = 1)
    (hswap : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = -β)
    (hρfix : (ρ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = β) :
    g * ρ * g⁻¹ = ρ⁻¹ := by
                                                         
  have hgg : g * g = 1 := so3_sq_of_swap g β hβ hswap
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
                                                                          
  have hswap' : ((g * ρ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β
      = -β := by
    rw [Submonoid.coe_mul, ← mulVec_mulVec, hρfix, hswap]
  have hgρ : (g * ρ) * (g * ρ) = 1 := so3_sq_of_swap (g * ρ) β hβ hswap'
                                                          
  rw [hginv]
  have h1 : g * ρ * g * ρ = 1 := by rw [mul_assoc (g * ρ) g ρ]; exact hgρ
  exact mul_eq_one_iff_eq_inv.mp h1

end DihedralGeom

                                                                               
                                                                                                
                                                                                           
                                                                                               
                                                                                    
                                                                                                
                                                                                           

                                                                                         
                                                                                              
                                                                        
                                                                 
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011616
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (k : ℕ) (hk : 2 ≤ k)
    (hcard : Nat.card (↥G) = 2 * k)
    (b : ↥(rotationAxes G)) (hbcard : Nat.card (MulAction.stabilizer (↥G) b) = k)
    (ρ : ↥G) (hρord : orderOf ρ = k) (hρfix : ρ • b = b) :
    ∃ s : ↥G, orderOf s = 2 ∧
      ((s • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = -((b : ↥(rotationAxes G)) : Fin 3 → ℝ) ∧
      s * ρ * s⁻¹ = ρ⁻¹ := by
  classical
  haveI hinj : Function.Injective (G.subtype) := Subgroup.subtype_injective G
                                                 
  set β : Fin 3 → ℝ := (b : ↥(rotationAxes G)).1 with hβdef
  have hβunit : β ⬝ᵥ β = 1 := b.2.1
                                                    
  have hρfixv : ((ρ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = β := by
    have h := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) hρfix
    rwa [matrixAction_011755] at h
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hρord; omega
                                                                                   
  set H : Subgroup (↥G) := MulAction.stabilizer (↥G) b with hHdef
  have hρmemH : ρ ∈ H := (MulAction.mem_stabilizer_iff).mpr hρfix
  have hHcard : Nat.card H = k := hbcard
  have hHindex : H.index = 2 := by
    have h := Subgroup.card_mul_index H
    rw [hHcard, hcard] at h
    have h2 : k * H.index = k * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  haveI hHnormal : H.Normal := Subgroup.normal_of_index_eq_two hHindex
                                  
  have hHnetop : H ≠ ⊤ := by
    intro h; rw [h, Subgroup.index_top] at hHindex; omega
  obtain ⟨g, -, hgnotH⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_top hHnetop)
  have hgb_ne : g • b ≠ b := fun h => hgnotH ((MulAction.mem_stabilizer_iff).mpr h)
                                                                                             
                                                                 
  set τ : ↥G := g * ρ * g⁻¹ with hτdef
  have hτH : τ ∈ H := hHnormal.conj_mem ρ hρmemH g
  have hτfix : τ • b = b := (MulAction.mem_stabilizer_iff).mp hτH
  set σ : specialOrthogonalGroup (Fin 3) ℝ := (τ : specialOrthogonalGroup (Fin 3) ℝ) with hσdef
  have hσfixβ : (σ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = β := by
    have h := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) hτfix
    rwa [matrixAction_011755] at h
  have hσne1 : σ ≠ 1 := by
    intro h
    have hτv : (τ : specialOrthogonalGroup (Fin 3) ℝ) = 1 := by rw [← hσdef]; exact h
    have hτ1 : τ = 1 := hinj (by simpa using hτv)
    have hg1 : g * ρ * g⁻¹ = 1 := by rw [← hτdef]; exact hτ1
    have hρ1 : ρ = 1 := by
      calc ρ = g⁻¹ * (g * ρ * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hg1]
        _ = 1 := by group
    exact hρne1 hρ1
                                                                         
  have hσfixgb : (σ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ)
      = ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) := by
    have haction : τ • (g • b) = g • b := by
      rw [← mul_smul, hτdef, show g * ρ * g⁻¹ * g = g * ρ from by group, mul_smul, hρfix]
    have h := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) haction
    rwa [matrixAction_011755] at h
                                                                                           
  obtain ⟨v₀, hv₀unit, hset⟩ := rotationAxisSet_eq_pair σ hσne1
  have hβmem : β = v₀ ∨ β = -v₀ := by
    have : β ∈ rotationAxisSet σ := ⟨hβunit, hσfixβ⟩
    rw [hset] at this; simpa [Set.mem_insert_iff] using this
  have hgbv_unit : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) ⬝ᵥ ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ)
      = 1 := (g • b).2.1
  have hgbvmem : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = v₀
      ∨ ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = -v₀ := by
    have : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) ∈ rotationAxisSet σ := ⟨hgbv_unit, hσfixgb⟩
    rw [hset] at this; simpa [Set.mem_insert_iff] using this
  have hne : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) ≠ β := by
    intro h; exact hgb_ne (Subtype.ext h)
                                                             
  have hgbv_eq : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = -β := by
    rcases hβmem with hβ0 | hβ0 <;> rcases hgbvmem with hg0 | hg0
    · exact absurd (hg0.trans hβ0.symm) hne
    · rw [hg0, hβ0]
    · rw [hg0, hβ0, neg_neg]
    · exact absurd (hg0.trans hβ0.symm) hne
  have hswapv : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β = -β := by
    have h : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ)
        = ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ β :=
      matrixAction_011755 g b
    rw [← h]; exact hgbv_eq
                                         
  refine ⟨g, ?_, ?_, ?_⟩
  ·                                                                      
    have hgg : g * g = 1 := by
      apply hinj
      rw [map_mul, map_one]
      exact so3_sq_of_swap (G.subtype g) β hβunit hswapv
    have hgne1 : g ≠ 1 := by
      intro h; exact hgb_ne (by rw [h, one_smul])
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hgg) hgne1
  ·              
    rw [hgbv_eq, hβdef]
  ·                        
    apply hinj
    rw [map_mul, map_mul, map_inv]
    exact so3_conj_of_swap (G.subtype g) (G.subtype ρ) β hβunit hswapv hρfixv

                                                                                                    
                                                                                              
                                                                                         
                                                                                           
                                                                                              
                                                                                           
                                                                                            
/-- The displayed stabilizer-cardinality multiset identifies the group with a dihedral group. -/
theorem mulEquiv_dihedral_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (k : ℕ) (hk : 2 ≤ k)
    (hcard : Nat.card (↥G) = 2 * k)
    (hpole : ∀ x ∈ ({2, 2, k} : Multiset ℕ),
      ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    Nonempty (G ≃* DihedralGroup k) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
                                                  
  obtain ⟨b, hbcard⟩ := hpole k (by simp)
                                                                                         
  haveI : Fintype (MulAction.stabilizer (↥G) b) := Fintype.ofFinite _
  obtain ⟨ρ', hρ'gen⟩ := (cyclicGroup_011643 G b).exists_generator
  have hρ'ord : orderOf ρ' = k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hρ'gen]
    simp only [Nat.card_eq_fintype_card] at hbcard ⊢
    exact hbcard
  set ρ : ↥G := (MulAction.stabilizer (↥G) b).subtype ρ' with hρdef
  have hρord : orderOf ρ = k := by
    rw [hρdef, orderOf_injective (MulAction.stabilizer (↥G) b).subtype
      (Subgroup.subtype_injective _) ρ', hρ'ord]
  have hρmem : ρ ∈ MulAction.stabilizer (↥G) b := ρ'.2
  have hρfix : ρ • b = b := MulAction.mem_stabilizer_iff.mp hρmem
                                                                
  obtain ⟨s, hsord, hsswap, hconj⟩ :=
    cardinalityFormula_011616 G k hk hcard b hbcard ρ hρord hρfix
                                                                                
  have hsnotin : s ∉ Subgroup.zpowers ρ := by
    intro hmem
    have hsfix : s • b = b :=
      MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hρmem) hmem)
    have hbb : ((b : ↥(rotationAxes G)) : Fin 3 → ℝ) = -((b : ↥(rotationAxes G)) : Fin 3 → ℝ) := by
      have e1 : ((s • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = ((b : ↥(rotationAxes G)) : Fin 3 → ℝ) := by
        rw [hsfix]
      rw [hsswap] at e1; exact e1.symm
    have hb1 : (b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1 = 1 := b.2.1
    have hd : (b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1
        = -((b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1) := by
      nth_rewrite 1 [hbb]; rw [neg_dotProduct]
    rw [hb1] at hd; norm_num at hd
                                                             
  exact multiplicativeEquivalence_011715 k ρ s hρord hsord hconj hsnotin hcard

                                                                                          
                                                                                           
                                                                                          
                                                                                            
                                                                                          
                  

                                                              
/-- The displayed stabilizer data identifies the group with the alternating group on four elements. -/
theorem mulEquiv_alternatingGroupFinFour_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 3})
    (heq : 2 * (1 - (Nat.card (↥G) : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
                                                                        
  have hcard : Nat.card (↥G) = 12 := by
    have hpos : 0 < Nat.card (↥G) := Nat.card_pos
    have hne : (Nat.card (↥G) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hclass] at heq
    have hsum : (({2, 3, 3} : Multiset ℕ).map (fun x => 1 - (x : ℚ)⁻¹)).sum = 11 / 6 := by
      simp only [Multiset.insert_eq_cons]
      norm_num
    rw [hsum] at heq
    have hq : (Nat.card (↥G) : ℚ) = 12 := by
      field_simp [hne] at heq
      linarith
    exact_mod_cast hq
                                                                                                  
                                  
  obtain ⟨b, hb⟩ := hpole 3 (by rw [hclass]; decide)
  have horbit_card : Nat.card (↥(MulAction.orbit ↥G b)) = 4 := by
    have hos : Nat.card (↥(MulAction.orbit ↥G b)) * Nat.card (↥(MulAction.stabilizer ↥G b))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G b)
    rw [hb, hcard] at hos
    omega
                                                                                                 
                                                    
  have hinj : Function.Injective (MulAction.toPermHom ↥G ↥(MulAction.orbit ↥G b)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hgne
    have hg0 : (g : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := by
      intro h
      exact hgne (Subtype.ext (h.trans (OneMemClass.coe_one G).symm))
    obtain ⟨v₀, _hv₀unit, hset⟩ := rotationAxisSet_eq_pair (g : _) hg0
                                                            
    have hfixorb : ∀ x : ↥(MulAction.orbit ↥G b), g • x = x := by
      intro x
      have h1 : (MulAction.toPermHom ↥G ↥(MulAction.orbit ↥G b)) g x = x := by rw [hg]; rfl
      exact h1
    have hfixvec : ∀ x : ↥(MulAction.orbit ↥G b),
        ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.1.1 = x.1.1 := by
      intro x
      have h2 : (g • x.1 : ↥(rotationAxes G)) = x.1 := by
        have h3 := congrArg (Subtype.val) (hfixorb x)
        exact h3
      have h4 := congrArg (Subtype.val) h2
      rwa [matrixAction_011755] at h4
                                                                                              
    have hmem : ∀ x : ↥(MulAction.orbit ↥G b),
        x.1.1 ∈ rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ) :=
      fun x => ⟨x.1.2.1, hfixvec x⟩
    haveI : Finite ↥(rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ)) :=
      (finite_rotationAxisSet (g : _) hg0).to_subtype
    have hFinj : Function.Injective
        (fun x : ↥(MulAction.orbit ↥G b) =>
          (⟨x.1.1, hmem x⟩ : ↥(rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ)))) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using hxy
    have hle : Nat.card (↥(MulAction.orbit ↥G b))
        ≤ Nat.card (↥(rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ))) :=
      Nat.card_le_card_of_injective _ hFinj
    have hle2 : Nat.card (↥(rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ))) ≤ 2 := by
      rw [hset, Nat.card_coe_set_eq]
      calc ({v₀, -v₀} : Set (Fin 3 → ℝ)).ncard
            ≤ ({-v₀} : Set (Fin 3 → ℝ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [horbit_card] at hle
    omega
                                                                                                
  haveI : Finite ↥(MulAction.orbit ↥G b) := (Finite.finite_mulAction_orbit b).to_subtype
  haveI : Fintype ↥(MulAction.orbit ↥G b) := Fintype.ofFinite _
  have hfin4 : Fintype.card ↥(MulAction.orbit ↥G b) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact horbit_card
  let e := Fintype.equivFinOfCardEq hfin4
  let ψ : ↥G →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥G ↥(MulAction.orbit ↥G b))
  have hψinj : Function.Injective ψ := by
    intro p q hpq
    exact hinj (e.permCongrHom.injective hpq)
  let H := ψ.range
  have hGH : ↥G ≃* ↥H := MonoidHom.ofInjective hψinj
  have hHcard : Nat.card (↥H) = 12 := by rw [← Nat.card_congr hGH.toEquiv, hcard]
                                                                                        
  have hindex : H.index = 2 := by
    have hmul : H.index * Nat.card (↥H) = Nat.card (Equiv.Perm (Fin 4)) := Subgroup.index_mul_card H
    have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by rw [Nat.card_perm, Nat.card_fin]; decide
    rw [hHcard, hperm] at hmul
    omega
  have hHeq : H = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨hGH.trans (MulEquiv.subgroupCongr hHeq)⟩

                                                                                      
                                                                                               
                                                               

                                                                                                
                                                                                               
                                                                                                 
                                                                         
                                                                                               
                                                                                                 
                                 

                                                                                
                                    
/-- Under the displayed cardinality hypotheses, some group element sends the point to its negative. -/
theorem exists_smul_eq_neg
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (hcard : Nat.card (↥G) = 24)
    (b : ↥(rotationAxes G)) (hb : Nat.card (MulAction.stabilizer (↥G) b) = 3) :
    ∃ g : ↥G, ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ)
      = -((b : ↥(rotationAxes G)) : Fin 3 → ℝ) := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite _
  haveI : Finite ↥(rotationAxes G) := (finite_rotationAxes G).to_subtype
  haveI : Fintype ↥(rotationAxes G) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
                                            
  have hfact3 : (Nat.card ↥G).factorization 3 = 1 := by
    rw [hcard, show (24 : ℕ) = 3 * 8 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
                                                                                       
  let P : Sylow 3 ↥G := Sylow.ofCard (MulAction.stabilizer ↥G b) (by rw [hb, hfact3, pow_one])
  haveI : Finite (Sylow 3 ↥G) := P.finite_of_finiteIndex
  haveI : Fintype (Sylow 3 ↥G) := Fintype.ofFinite _
                                                                             
  have hsmul_iff : ∀ (x : ↥G) (Q : ↥(rotationAxes G)),
      x • Q = Q ↔
        ((x : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ Q.1 = Q.1 := by
    intro x Q
    rw [Subtype.ext_iff, matrixAction_011755]
                                 
  have hnbpole : IsFixedVector G (-(b : ↥(rotationAxes G)).1) := by
    obtain ⟨hunit, g, hg, hne, hfix⟩ := b.2
    refine ⟨?_, g, hg, hne, ?_⟩
    · rw [dotProduct_neg, neg_dotProduct, neg_neg]; exact hunit
    · rw [mulVec_neg, hfix]
  set nb : ↥(rotationAxes G) := ⟨-(b : ↥(rotationAxes G)).1, hnbpole⟩ with hnbdef
  have hnbval : (nb : ↥(rotationAxes G)).1 = -(b : ↥(rotationAxes G)).1 := rfl
                                                                        
  have hstab_eq : MulAction.stabilizer ↥G nb = MulAction.stabilizer ↥G b := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, hsmul_iff, hnbval, mulVec_neg, neg_inj]
  have hnb3 : Nat.card (MulAction.stabilizer ↥G nb) = 3 := by rw [hstab_eq]; exact hb
                              
  have horbit_card : Nat.card (↥(MulAction.orbit ↥G b)) = 8 := by
    have hos : Nat.card (↥(MulAction.orbit ↥G b)) * Nat.card (↥(MulAction.stabilizer ↥G b))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G b)
    rw [hb, hcard] at hos
    omega
                                                                               
  have hPcoe : (P : Subgroup ↥G) = MulAction.stabilizer ↥G b := Sylow.coe_ofCard _ _
  have hPcard : Nat.card (P : Subgroup ↥G) = 3 := by rw [hPcoe]; exact hb
  have hPindex : (P : Subgroup ↥G).index = 8 := by
    have h := Subgroup.index_mul_card (P : Subgroup ↥G)
    rw [hPcard, hcard] at h; omega
  have hn3dvd : Nat.card (Sylow 3 ↥G) ∣ 8 := hPindex ▸ Sylow.card_dvd_index P
  have hn3mod : Nat.card (Sylow 3 ↥G) % 3 = 1 % 3 := card_sylow_modEq_one (p := 3) (G := ↥G)
  have hn3pos : 0 < Nat.card (Sylow 3 ↥G) := Nat.card_pos
  have hn3le : Nat.card (Sylow 3 ↥G) ≤ 4 := by
    have hle8 : Nat.card (Sylow 3 ↥G) ≤ 8 := Nat.le_of_dvd (by norm_num) hn3dvd
    set n3 := Nat.card (Sylow 3 ↥G) with hn3def
    interval_cases n3 <;> omega
                                                                                                 
  set φ : ↥(rotationAxes G) → Sylow 3 ↥G := fun v =>
    if h : Nat.card (MulAction.stabilizer ↥G v) = 3
    then Sylow.ofCard (MulAction.stabilizer ↥G v) (by rw [h, hfact3, pow_one])
    else P
    with hφdef
  have hφpos : ∀ (v : ↥(rotationAxes G)), Nat.card (MulAction.stabilizer ↥G v) = 3 →
      ((φ v : Sylow 3 ↥G) : Subgroup ↥G) = MulAction.stabilizer ↥G v := by
    intro v hv
    rw [hφdef]; dsimp only; rw [dif_pos hv]; exact Sylow.coe_ofCard _ _
                                            
  set P₃F : Finset ↥(rotationAxes G) :=
    Finset.univ.filter (fun v => Nat.card (MulAction.stabilizer ↥G v) = 3) with hP₃Fdef
  have hmemP₃F : ∀ v, v ∈ P₃F ↔ Nat.card (MulAction.stabilizer ↥G v) = 3 := by
    intro v; rw [hP₃Fdef, Finset.mem_filter]; simp
                                                                
  have hfiber : ∀ S : Sylow 3 ↥G, (P₃F.filter (fun v => φ v = S)).card ≤ 2 := by
    intro S
    rcases Finset.eq_empty_or_nonempty (P₃F.filter (fun v => φ v = S)) with hE | ⟨v₀, hv₀⟩
    · simp [hE]
    · rw [Finset.mem_filter] at hv₀
      obtain ⟨hv₀P, hv₀S⟩ := hv₀
      have hv₀3 := (hmemP₃F v₀).mp hv₀P
                                            
      have hScoe : (S : Subgroup ↥G) = MulAction.stabilizer ↥G v₀ := by
        rw [← hv₀S]; exact hφpos v₀ hv₀3
      have hScard : Nat.card (S : Subgroup ↥G) = 3 := by rw [hScoe]; exact hv₀3
                                       
      haveI hSnt : Nontrivial ↥(S : Subgroup ↥G) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
      obtain ⟨s0, hs0⟩ := exists_ne (1 : ↥(S : Subgroup ↥G))
      have hs1 : (s0 : ↥G) ≠ 1 := fun h => hs0 (Subtype.ext h)
      have hs1' : ((s0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := fun h =>
        hs1 (Subtype.ext (h.trans (OneMemClass.coe_one G).symm))
      obtain ⟨u, huunit, hset⟩ := rotationAxisSet_eq_pair _ hs1'
                                                                  
      have hmaps : ∀ v ∈ P₃F.filter (fun v => φ v = S),
          (v : ↥(rotationAxes G)).1 ∈ ({u, -u} : Finset (Fin 3 → ℝ)) := by
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvP, hvS⟩ := hv
        have hv3 := (hmemP₃F v).mp hvP
        have hScoe_v : (S : Subgroup ↥G) = MulAction.stabilizer ↥G v := by
          rw [← hvS]; exact hφpos v hv3
        have hsstab : (s0 : ↥G) ∈ MulAction.stabilizer ↥G v := hScoe_v ▸ s0.2
        have hfixvec :
            (((s0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.1
              = v.1 :=
          (hsmul_iff (s0 : ↥G) v).mp (MulAction.mem_stabilizer_iff.mp hsstab)
        have hmem : v.1 ∈ rotationAxisSet ((s0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :=
          ⟨v.2.1, hfixvec⟩
        rw [hset] at hmem
        simpa using hmem
      calc (P₃F.filter (fun v => φ v = S)).card
          ≤ ({u, -u} : Finset (Fin 3 → ℝ)).card :=
            Finset.card_le_card_of_injOn (f := fun v => (v : ↥(rotationAxes G)).1) hmaps
              (fun a _ b _ hab => Subtype.ext hab)
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
                         
  have hP₃card : {v : ↥(rotationAxes G) | Nat.card (MulAction.stabilizer ↥G v) = 3}.ncard ≤ 8 := by
    have hcoe : {v : ↥(rotationAxes G) | Nat.card (MulAction.stabilizer ↥G v) = 3} = ↑P₃F := by
      ext v; simp only [Set.mem_setOf_eq, Finset.mem_coe, hmemP₃F]
    rw [hcoe, Set.ncard_coe_finset]
    calc P₃F.card
        ≤ 2 * (P₃F.image φ).card := Finset.card_le_mul_card_image P₃F 2 (fun S _ => hfiber S)
      _ ≤ 2 * Nat.card (Sylow 3 ↥G) := by
          gcongr
          rw [Nat.card_eq_fintype_card]
          exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
      _ ≤ 2 * 4 := by gcongr
      _ = 8 := by norm_num
                                                                   
  have hOsub : MulAction.orbit ↥G b ⊆
      {v : ↥(rotationAxes G) | Nat.card (MulAction.stabilizer ↥G v) = 3} := by
    intro w hw
    have hforbit : MulAction.orbit ↥G w = MulAction.orbit ↥G b := MulAction.orbit_eq_iff.mpr hw
    have horbw : Nat.card (↥(MulAction.orbit ↥G w)) = 8 := by rw [hforbit]; exact horbit_card
    have hos : Nat.card (↥(MulAction.orbit ↥G w)) * Nat.card (↥(MulAction.stabilizer ↥G w))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G w)
    rw [horbw, hcard] at hos
    change Nat.card (MulAction.stabilizer ↥G w) = 3
    omega
  have hOncard : (MulAction.orbit ↥G b).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact horbit_card
  have hOeq : MulAction.orbit ↥G b
      = {v : ↥(rotationAxes G) | Nat.card (MulAction.stabilizer ↥G v) = 3} :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hOncard]; exact hP₃card) (Set.toFinite _)
  have hnbO : nb ∈ MulAction.orbit ↥G b := by rw [hOeq]; exact hnb3
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hnbO
  exact ⟨g, by rw [hg]⟩

section OctahedralFaithful
open scoped RealInnerProductSpace
open Matrix EuclideanSpace Submodule WithLp Module MulAction

set_option maxHeartbeats 400000 in
                                                                                    
                                                                                           
                                                                                           
                                                                                   

                                                                                         
                                                                                           
                                                                                             
                                                                                   
                                                                                             
                                                                                                
                                                                                  
/-- An element acting by either identity or negation on every point of the displayed orbit is the identity. -/
theorem eq_one_of_smul_eq_or_neg
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G]
    (hcard : Nat.card (↥G) = 24)
    (b : ↥(rotationAxes G)) (hb : Nat.card (MulAction.stabilizer (↥G) b) = 3)
    (g : ↥G)
    (hg : ∀ w : ↥(MulAction.orbit ↥G b),
      ((g • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
          = ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
      ∨ ((g • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
          = -(((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1)) :
    g = 1 := by
  classical
                                                        
  have horbit_card : Nat.card (↥(MulAction.orbit ↥G b)) = 8 := by
    have hos : Nat.card (↥(MulAction.orbit ↥G b)) * Nat.card (↥(MulAction.stabilizer ↥G b))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G b)
    rw [hb, hcard] at hos
    omega
  haveI : Finite ↥(MulAction.orbit ↥G b) := (Finite.finite_mulAction_orbit b).to_subtype
                                                                                   
  have haction : ∀ w : ↥(MulAction.orbit ↥G b),
      ((g • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
        = ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
            ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1 := by
    intro w
    change (g • (w : ↥(rotationAxes G))).1 = _
    rw [matrixAction_011755]
                                         
  have hunit : ∀ w : ↥(MulAction.orbit ↥G b),
      ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
        ⬝ᵥ ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1 = 1 :=
    fun w => (w : ↥(rotationAxes G)).2.1
                                        
  have hpm : ∀ w : ↥(MulAction.orbit ↥G b),
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
        = ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
      ∨ ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          ((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
        = -(((w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1) := by
    intro w
    have := hg w
    rwa [haction w] at this
  by_contra hgne
  have hg0 : (g : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := by
    intro h
    exact hgne (Subtype.ext (h.trans (OneMemClass.coe_one G).symm))
                                                                                                 
                                    
  have key : ∀ h : specialOrthogonalGroup (Fin 3) ℝ, h ≠ 1 →
      (∀ w : ↥(MulAction.orbit ↥G b),
        (h : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w.1.1 = w.1.1) → False := by
    intro h hne hfix
    obtain ⟨v₀, _hv₀, hset⟩ := rotationAxisSet_eq_pair h hne
    have hmem : ∀ w : ↥(MulAction.orbit ↥G b), w.1.1 ∈ rotationAxisSet h :=
      fun w => ⟨hunit w, hfix w⟩
    haveI : Finite ↥(rotationAxisSet h) := (finite_rotationAxisSet h hne).to_subtype
    have hFinj : Function.Injective
        (fun w : ↥(MulAction.orbit ↥G b) => (⟨w.1.1, hmem w⟩ : ↥(rotationAxisSet h))) := by
      intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using hxy
    have hle : Nat.card (↥(MulAction.orbit ↥G b)) ≤ Nat.card (↥(rotationAxisSet h)) :=
      Nat.card_le_card_of_injective _ hFinj
    have hle2 : Nat.card (↥(rotationAxisSet h)) ≤ 2 := by
      rw [hset, Nat.card_coe_set_eq]
      calc ({v₀, -v₀} : Set (Fin 3 → ℝ)).ncard
            ≤ ({-v₀} : Set (Fin 3 → ℝ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [horbit_card] at hle; omega
                                                                                                 
  have hsqfix : ∀ w : ↥(MulAction.orbit ↥G b),
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w.1.1) = w.1.1 := by
    intro w
    rcases hpm w with h | h
    · rw [h, h]
    · rw [h, mulVec_neg, h, neg_neg]
  have hg0sq : (g : specialOrthogonalGroup (Fin 3) ℝ) * (g : specialOrthogonalGroup (Fin 3) ℝ)
      = 1 := by
    by_contra hne
    refine key _ hne (fun w => ?_)
    rw [Submonoid.coe_mul, ← mulVec_mulVec]
    exact hsqfix w
                                                    
  have hgg : g * g = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact hg0sq
  have hord : orderOf g = 2 := by
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · rw [orderOf_eq_one_iff] at h; exact absurd h hgne
    · exact h
                                                                                                 
                                           
  have hneg : ∀ w : ↥(MulAction.orbit ↥G b),
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w.1.1 = -(w.1.1) := by
    intro w
    rcases hpm w with hfix | hneg
    · exfalso
                                                                                                   
      have hgstab : g ∈ MulAction.stabilizer ↥G w.1 := by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        rw [matrixAction_011755]; exact hfix
                                                                             
      have hwmem : w.1 ∈ MulAction.orbit ↥G b := w.2
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp hwmem
      have hcard3 : Nat.card (MulAction.stabilizer ↥G w.1) = 3 := by
        rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := c) (a := b)
          (b := w.1) hc.symm).toEquiv, hb]
                                                                    
      have hdvd : orderOf g ∣ Nat.card (MulAction.stabilizer ↥G w.1) :=
        Subgroup.orderOf_dvd_natCard _ hgstab
      rw [hord, hcard3] at hdvd; omega
    · exact hneg
                                                                         
  obtain ⟨n, hnunit, hnset⟩ :=
    rotationAxisSet_eq_pair (g : specialOrthogonalGroup (Fin 3) ℝ) hg0
  have hnfix : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n = n :=
    (show n ∈ rotationAxisSet (g : specialOrthogonalGroup (Fin 3) ℝ) by
      rw [hnset]; exact Set.mem_insert _ _).2
  have hperp : ∀ w : ↥(MulAction.orbit ↥G b), w.1.1 ⬝ᵥ n = 0 := by
    intro w
    have h := matrixAction_011812 (g : specialOrthogonalGroup (Fin 3) ℝ) w.1.1 n
    rw [hneg w, hnfix, neg_dotProduct] at h
    linarith
                                                                                              
  haveI : Fintype ↥(MulAction.stabilizer ↥G b) := Fintype.ofFinite _
  haveI : Nontrivial ↥(MulAction.stabilizer ↥G b) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hb]
    norm_num
  obtain ⟨r0, hr0⟩ := exists_ne (1 : ↥(MulAction.stabilizer ↥G b))
  have hrne : (r0 : ↥G) ≠ 1 := fun h => hr0 (Subtype.ext h)
  have hrcube : (r0 : ↥G) ^ 3 = 1 := by
    have hdvd : orderOf (r0 : ↥G) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer ↥G b) r0.2
      rwa [hb] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hrfixb : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
      (b : ↥(rotationAxes G)).1 = (b : ↥(rotationAxes G)).1 := by
    have h := congrArg (fun P : ↥(rotationAxes G) => P.1) (MulAction.mem_stabilizer_iff.mp r0.2)
    rwa [matrixAction_011755] at h
                                                                     
  have haction' : ∀ (c : ↥G) (x : ↥(MulAction.orbit ↥G b)),
      ((c • x : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
        = ((c : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.1.1 := by
    intro c x
    change (c • (x : ↥(rotationAxes G))).1 = _
    rw [matrixAction_011755]
                                                                              
  have hperpR : ∀ w : ↥(MulAction.orbit ↥G b),
      ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n)
        ⬝ᵥ w.1.1 = 0 := by
    intro w
    have hvec : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (((r0 : ↥G)⁻¹ • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1 = w.1.1 := by
      rw [← haction' (r0 : ↥G) ((r0 : ↥G)⁻¹ • w), smul_inv_smul]
    have h := matrixAction_011812 ((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) n
      (((r0 : ↥G)⁻¹ • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1
    rw [hvec] at h
    rw [h, dotProduct_comm]
    exact hperp _
                                                                                               
  have hNne : (toLp 2 n : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have h0 : n ⬝ᵥ n = 0 := by rw [← inner_toLp, h, inner_zero_left]
    rw [hnunit] at h0; norm_num at h0
  have hBne : (toLp 2 (b : ↥(rotationAxes G)).1 : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have h0 : (b : ↥(rotationAxes G)).1 ⬝ᵥ (b : ↥(rotationAxes G)).1 = 0 := by
      rw [← inner_toLp, h, inner_zero_left]
    rw [b.2.1] at h0; norm_num at h0
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  have hTle : Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
      (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3))))
        ≤ (ℝ ∙ (toLp 2 n : EuclideanSpace ℝ (Fin 3)))ᗮ := by
    rw [Submodule.span_le]
    rintro x ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_toLp]
    exact hperp w
  have hPfr : finrank ℝ ((ℝ ∙ (toLp 2 n : EuclideanSpace ℝ (Fin 3)))ᗮ) = 2 :=
    Submodule.finrank_orthogonal_span_singleton (n := 2) hNne
                                                                                           
  have hTfr : 2 ≤ finrank ℝ (Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
      (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3))))) := by
    by_contra hlt
    push Not at hlt
    have hspanle : (ℝ ∙ (toLp 2 (b : ↥(rotationAxes G)).1 : EuclideanSpace ℝ (Fin 3)))
        ≤ Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
          (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3)))) := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨⟨b, MulAction.mem_orbit_self b⟩, rfl⟩
    have hfr1 : finrank ℝ (ℝ ∙ (toLp 2 (b : ↥(rotationAxes G)).1 : EuclideanSpace ℝ (Fin 3))) = 1 :=
      finrank_span_singleton hBne
    have heq : (ℝ ∙ (toLp 2 (b : ↥(rotationAxes G)).1 : EuclideanSpace ℝ (Fin 3)))
        = Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
          (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3)))) :=
      Submodule.eq_of_le_of_finrank_le hspanle (by rw [hfr1]; omega)
    have hpar : ∀ w : ↥(MulAction.orbit ↥G b),
        w.1.1 ∈ ({(b : ↥(rotationAxes G)).1, -(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ)) := by
      intro w
      have hmem : (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3))
          ∈ (ℝ ∙ (toLp 2 (b : ↥(rotationAxes G)).1 : EuclideanSpace ℝ (Fin 3))) := by
        rw [heq]; exact Submodule.subset_span ⟨w, rfl⟩
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hcv : c • (b : ↥(rotationAxes G)).1 = w.1.1 := by
        have h := congrArg WithLp.ofLp hc
        simpa using h
      have hcsq : c * c = 1 := by
        have h1 : (c • (b : ↥(rotationAxes G)).1) ⬝ᵥ (c • (b : ↥(rotationAxes G)).1) = 1 := by
          rw [hcv]; exact hunit w
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, b.2.1] at h1
        linarith
      rcases mul_self_eq_one_iff.mp hcsq with h | h
      · exact Or.inl (by rw [← hcv, h, one_smul])
      · refine Or.inr ?_
        rw [Set.mem_singleton_iff, ← hcv, h, neg_one_smul]
    have hFinj : Function.Injective (fun w : ↥(MulAction.orbit ↥G b) =>
        (⟨w.1.1, hpar w⟩ :
          ↥({(b : ↥(rotationAxes G)).1, -(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ)))) := by
      intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using hxy
    have hle : Nat.card (↥(MulAction.orbit ↥G b))
        ≤ Nat.card (↥({(b : ↥(rotationAxes G)).1, -(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ))) :=
      Nat.card_le_card_of_injective _ hFinj
    have hle2 : Nat.card (↥({(b : ↥(rotationAxes G)).1, -(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ)))
        ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc ({(b : ↥(rotationAxes G)).1, -(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ)).ncard
            ≤ ({-(b : ↥(rotationAxes G)).1} : Set (Fin 3 → ℝ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [horbit_card] at hle; omega
                                                                                            
  have hTeq : Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
      (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3))))
        = (ℝ ∙ (toLp 2 n : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    Submodule.eq_of_le_of_finrank_le hTle (by rw [hPfr]; exact hTfr)
  have hRNmem : (toLp 2 ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) : EuclideanSpace ℝ (Fin 3))
        ∈ (ℝ ∙ (toLp 2 n : EuclideanSpace ℝ (Fin 3))) := by
    have hTperp : Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
        (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3))))
          ≤ (ℝ ∙ (toLp 2 ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
              Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) : EuclideanSpace ℝ (Fin 3)))ᗮ := by
      rw [Submodule.span_le]
      rintro x ⟨w, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_toLp]
      exact hperpR w
    have h2 : (Submodule.span ℝ (Set.range (fun w : ↥(MulAction.orbit ↥G b) =>
        (toLp 2 w.1.1 : EuclideanSpace ℝ (Fin 3)))))ᗮ
          = (ℝ ∙ (toLp 2 n : EuclideanSpace ℝ (Fin 3))) := by
      rw [hTeq, Submodule.orthogonal_orthogonal]
    rw [← h2]
    exact (le_trans (Submodule.le_orthogonal_orthogonal _) (Submodule.orthogonal_le hTperp))
      (Submodule.mem_span_singleton_self _)
                                                             
  rw [Submodule.mem_span_singleton] at hRNmem
  obtain ⟨c, hc⟩ := hRNmem
  have hcv : c • n = (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n := by
    have h := congrArg WithLp.ofLp hc
    simpa using h
  have hcsq : c * c = 1 := by
    have h1 : (c • n) ⬝ᵥ (c • n) = 1 := by rw [hcv, matrixAction_011812]; exact hnunit
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hnunit] at h1
    linarith
  have hrfixn : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n = n := by
    rcases mul_self_eq_one_iff.mp hcsq with h | h
    · rw [← hcv, h, one_smul]
    · exfalso
      have hneg1 : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n = -n := by rw [← hcv, h, neg_one_smul]
      have hm3 : ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) * (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ)) * (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
        have h1 := congrArg (fun x : ↥G =>
          ((x : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) hrcube
        simpa [pow_succ] using h1
      have hcube : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n)) = n := by
        rw [mulVec_mulVec, mulVec_mulVec, hm3, one_mulVec]
      have e1 : (((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) = n := by
        rw [hneg1, mulVec_neg, hneg1, neg_neg]
      rw [e1, hneg1] at hcube
      have hcontra : (1 : ℝ) = -1 := by
        calc (1 : ℝ) = n ⬝ᵥ n := hnunit.symm
          _ = (-n) ⬝ᵥ n := by rw [hcube]
          _ = -(n ⬝ᵥ n) := neg_dotProduct _ _
          _ = -1 := by rw [hnunit]
      norm_num at hcontra
                                                                                              
  have hrso : ((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := by
    intro h
    exact hrne (Subtype.ext (h.trans (OneMemClass.coe_one G).symm))
  obtain ⟨v₁, hv₁unit, hv₁set⟩ :=
    rotationAxisSet_eq_pair ((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) hrso
  have hnmem : n ∈ rotationAxisSet ((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) :=
    ⟨hnunit, hrfixn⟩
  have hbmem : (b : ↥(rotationAxes G)).1
      ∈ rotationAxisSet ((r0 : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) := ⟨b.2.1, hrfixb⟩
  have hbn : (b : ↥(rotationAxes G)).1 ⬝ᵥ n = 0 := hperp ⟨b, MulAction.mem_orbit_self b⟩
  rw [hv₁set] at hnmem hbmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnmem hbmem
  rcases hnmem with hn | hn <;> rcases hbmem with hbv | hbv <;>
    rw [hn, hbv] at hbn <;>
    simp only [dotProduct_neg, neg_dotProduct, neg_neg, hv₁unit] at hbn <;>
    norm_num at hbn

end OctahedralFaithful

                                                                                              
                                                                                                  
set_option maxHeartbeats 800000 in
                                                                                      
                                                                                            
                                                                                              
                 

                                                                                            
                                                                               

                                                                                                   
                                                            
                                                                                               
                                                                                      
                                                                                               
                                                                                     
                                        
                                                                                                  
                                                                                                   
                                                                                                  
                                                                                              
                                                                                               
                                                                                                   
                                                                                                 
                                                                                               
                                                                              

                                                                                                  
                                                                                                   
                                                                                                
                                                                                              
/-- Under the displayed stabilizer hypotheses, an injective homomorphism exists. -/
theorem exists_injective_hom_011630
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 4})
    (hcard : Nat.card (↥G) = 24)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    ∃ φ : ↥G →* Equiv.Perm (Fin 4), Function.Injective φ := by
  classical
                                                                                                  
  obtain ⟨b, hb⟩ := hpole 3 (by rw [hclass]; decide)
  have horbit_card : Nat.card ↥(MulAction.orbit ↥G b) = 8 := by
    have hos : Nat.card ↥(MulAction.orbit ↥G b) * Nat.card (↥(MulAction.stabilizer ↥G b))
        = Nat.card ↥G := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G b)
    rw [hb, hcard] at hos
    omega
  haveI : Finite ↥(MulAction.orbit ↥G b) := (Finite.finite_mulAction_orbit b).to_subtype
                                                                     
  have hvec_smul : ∀ (g : ↥G) (w : ↥(MulAction.orbit ↥G b)),
      (g • w).1.1
        = ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w.1.1 := by
    intro g w
    show ((g • w : ↥(MulAction.orbit ↥G b)) : ↥(rotationAxes G)).1 = _
    change (g • (w : ↥(rotationAxes G))).1 = _
    rw [matrixAction_011755]
                                                                                            
  have hvinj : Function.Injective (fun w : ↥(MulAction.orbit ↥G b) => w.1.1) :=
    fun x y h => Subtype.ext (Subtype.ext h)
                                                                                           
  obtain ⟨g0, hg0⟩ := exists_smul_eq_neg G hcard b hb
  have hanti : ∀ w : ↥(MulAction.orbit ↥G b),
      ∃ w' : ↥(MulAction.orbit ↥G b), w'.1.1 = -(w.1.1) := by
    intro w
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp w.2
    refine ⟨⟨(h * g0) • b, MulAction.mem_orbit b (h * g0)⟩, ?_⟩
    have e1 : ((h * g0) • b : ↥(rotationAxes G)).1 = -((h • b : ↥(rotationAxes G)).1) := by
      rw [mul_smul, matrixAction_011755 h (g0 • b), hg0, mulVec_neg, matrixAction_011755 h b]
    rw [hh] at e1
    exact e1
                                                                                                 
  letI S : Setoid ↥(MulAction.orbit ↥G b) :=
    { r := fun x y => x.1.1 = y.1.1 ∨ x.1.1 = -y.1.1
      iseqv :=
        { refl := fun x => Or.inl rfl
          symm := fun {x y} h => h.imp Eq.symm (fun e => by rw [e, neg_neg])
          trans := fun {x y z} hxy hyz => by
            rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
            · exact Or.inl (h1.trans h2)
            · exact Or.inr (h1.trans h2)
            · exact Or.inr (by rw [h1, h2])
            · exact Or.inl (by rw [h1, h2, neg_neg]) } }
                                                                               
  have hSinv : ∀ (g : ↥G) (a c : ↥(MulAction.orbit ↥G b)), S.r a c → S.r (g • a) (g • c) := by
    intro g a c h
    change (g • a).1.1 = (g • c).1.1 ∨ (g • a).1.1 = -((g • c).1.1)
    rw [hvec_smul, hvec_smul]
    rcases h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, mulVec_neg])
  letI actionD : MulAction ↥G (Quotient S) :=
    { smul := fun g =>
        Quotient.map' (fun w : ↥(MulAction.orbit ↥G b) => (g • w : ↥(MulAction.orbit ↥G b)))
          (hSinv g)
      one_smul := by
        intro q
        refine Quotient.inductionOn' q (fun w => ?_)
        change Quotient.map'
            (fun w : ↥(MulAction.orbit ↥G b) => ((1 : ↥G) • w : ↥(MulAction.orbit ↥G b)))
            (hSinv 1) (Quotient.mk'' w) = Quotient.mk'' w
        rw [Quotient.map'_mk'', one_smul]
      mul_smul := by
        intro g₁ g₂ q
        refine Quotient.inductionOn' q (fun w => ?_)
        change Quotient.map'
            (fun w : ↥(MulAction.orbit ↥G b) => ((g₁ * g₂) • w : ↥(MulAction.orbit ↥G b)))
            (hSinv (g₁ * g₂)) (Quotient.mk'' w)
          = Quotient.map'
              (fun w : ↥(MulAction.orbit ↥G b) => (g₁ • w : ↥(MulAction.orbit ↥G b))) (hSinv g₁)
              (Quotient.map'
                (fun w : ↥(MulAction.orbit ↥G b) => (g₂ • w : ↥(MulAction.orbit ↥G b)))
                (hSinv g₂) (Quotient.mk'' w))
        rw [Quotient.map'_mk'', Quotient.map'_mk'', Quotient.map'_mk'', mul_smul] }
  haveI : Fintype (Quotient S) := Fintype.ofFinite _
                                                                                    
  have hfiber : ∀ d : Quotient S,
      Nat.card {w : ↥(MulAction.orbit ↥G b) // Quotient.mk'' w = d} = 2 := by
    intro d
    obtain ⟨w0, rfl⟩ := Quotient.mk''_surjective d
    obtain ⟨w0', hw0'⟩ := hanti w0
    have hmem' : (Quotient.mk'' w0' : Quotient S) = Quotient.mk'' w0 :=
      Quotient.eq''.mpr (Or.inr hw0')
    have hunit : w0.1.1 ⬝ᵥ w0.1.1 = 1 := w0.1.2.1
    have hvne : w0'.1.1 ≠ w0.1.1 := by
      rw [hw0']
      intro he
      have hcontra : (1 : ℝ) = -1 := by
        calc (1 : ℝ) = w0.1.1 ⬝ᵥ w0.1.1 := hunit.symm
          _ = (-w0.1.1) ⬝ᵥ w0.1.1 := by rw [he]
          _ = -(w0.1.1 ⬝ᵥ w0.1.1) := by rw [neg_dotProduct]
          _ = -1 := by rw [hunit]
      norm_num at hcontra
    rw [Nat.card_eq_two_iff' (⟨w0, rfl⟩ :
        {w : ↥(MulAction.orbit ↥G b) //
          Quotient.mk'' w = (Quotient.mk'' w0 : Quotient S)})]
    refine ⟨⟨w0', hmem'⟩, ?_, ?_⟩
    · intro he
      exact hvne (congrArg (fun z : ↥(MulAction.orbit ↥G b) => z.1.1) (Subtype.ext_iff.mp he))
    · rintro ⟨w, hw⟩ hwne
      have hrel : S.r w w0 := Quotient.eq''.mp hw
      rcases hrel with h | h
      · exact absurd (Subtype.ext (Subtype.ext (Subtype.ext h))) hwne
      · exact Subtype.ext (Subtype.ext (Subtype.ext (by rw [h, ← hw0'])))
  have hsig : Nat.card ↥(MulAction.orbit ↥G b)
      = ∑ d : Quotient S, Nat.card {w : ↥(MulAction.orbit ↥G b) // Quotient.mk'' w = d} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      (Equiv.sigmaFiberEquiv (Quotient.mk'' : ↥(MulAction.orbit ↥G b) → Quotient S)).symm
  have hkey : Nat.card ↥(MulAction.orbit ↥G b) = Fintype.card (Quotient S) * 2 := by
    rw [hsig]
    simp_rw [hfiber]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [horbit_card] at hkey
  have hfin4 : Fintype.card (Quotient S) = 4 := by omega
                                                                                                
  have hinj : Function.Injective (MulAction.toPermHom ↥G (Quotient S)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ q : Quotient S, g • q = q := by
      intro q
      have h1 : (MulAction.toPermHom ↥G (Quotient S) g) q = q := by rw [hg]; rfl
      exact h1
    refine eq_one_of_smul_eq_or_neg G hcard b hb g (fun w => ?_)
    have hq : (g • Quotient.mk'' w : Quotient S) = Quotient.mk'' w := hfix _
    rw [show (g • Quotient.mk'' w : Quotient S) = Quotient.mk'' (g • w) from rfl] at hq
    exact Quotient.eq''.mp hq
                                                                                    
  set ψ : ↥G →* Equiv.Perm (Quotient S) := MulAction.toPermHom ↥G (Quotient S) with hψdef
  let e := Fintype.equivFinOfCardEq hfin4
  refine ⟨e.permCongrHom.toMonoidHom.comp ψ, fun p q hpq => ?_⟩
  exact hinj (e.permCongrHom.injective hpq)

                                                                                        
                                                                                           
                                                                                            
                                                                                                 
                                                                                                
                                                                                                   
/-- The displayed stabilizer data identifies the group with permutations of four elements. -/
theorem mulEquiv_permFinFour_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 4})
    (heq : 2 * (1 - (Nat.card (↥G) : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
                                                                        
  have hcard : Nat.card (↥G) = 24 := by
    have hpos : 0 < Nat.card (↥G) := Nat.card_pos
    have hne : (Nat.card (↥G) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hclass] at heq
    have hsum : (({2, 3, 4} : Multiset ℕ).map (fun x => 1 - (x : ℚ)⁻¹)).sum = 23 / 12 := by
      simp only [Multiset.insert_eq_cons]
      norm_num
    rw [hsum] at heq
    have hq : (Nat.card (↥G) : ℚ) = 24 := by
      field_simp [hne] at heq
      linarith
    exact_mod_cast hq
                                                                                                     
  obtain ⟨φ, hφinj⟩ := exists_injective_hom_011630 G m hclass hcard hpole
                                                                                                  
  haveI : Fintype ↥G := Fintype.ofFinite _
  have hcardG : Fintype.card ↥G = 24 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hcard4 : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]; decide
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card, hcardG, hcard4]
    exact ⟨hφinj, rfl⟩
  exact ⟨MulEquiv.ofBijective φ hbij⟩

                                                                                         
                                                                                           
                                 
/-- The displayed stabilizer-cardinality multiset and sum identity force group cardinality sixty. -/
theorem card_eq_sixty_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 5})
    (heq : 2 * (1 - (Nat.card (↥G) : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum) :
    Nat.card (↥G) = 60 := by
  have hpos : 0 < Nat.card (↥G) := Nat.card_pos
  have hne : (Nat.card (↥G) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hclass] at heq
  have hsum : (({2, 3, 5} : Multiset ℕ).map (fun x => 1 - (x : ℚ)⁻¹)).sum = 59 / 30 := by
    simp only [Multiset.insert_eq_cons]
    norm_num
  rw [hsum] at heq
  have hq : (Nat.card (↥G) : ℚ) = 60 := by
    field_simp [hne] at heq
    linarith
  exact_mod_cast hq

                                                                                             
                                                                                             
                                                                             
                                                                                               
                                                                                               
                                                                                               
                                                                                                     
                                                                                       
/-- A simple group with a subgroup of the displayed index admits an injective homomorphism. -/
theorem exists_injective_hom_011633
    {Grp : Type*} [Group Grp] [Finite Grp] (hsimple : IsSimpleGroup Grp)
    (H : Subgroup Grp) (hindex : H.index = 5) :
    ∃ φ : Grp →* Equiv.Perm (Fin 5), Function.Injective φ := by
  classical
  haveI := hsimple
                                                             
  have hcard5 : Nat.card (Grp ⧸ H) = 5 := by rw [← Subgroup.index_eq_card]; exact hindex
                                                                            
  set ψ : Grp →* Equiv.Perm (Grp ⧸ H) := MulAction.toPermHom Grp (Grp ⧸ H) with hψ
  have hker : ψ.ker = H.normalCore := (Subgroup.normalCore_eq_ker H).symm
                                                                                           
  have hnc : H.normalCore = ⊥ := by
    rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (Subgroup.index_eq_one.mpr (top_le_iff.mp (h ▸ H.normalCore_le)) ▸ hindex)
        (by norm_num)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hnc]
                                                      
  haveI : Fintype (Grp ⧸ H) := Fintype.ofFinite _
  have hfin5 : Fintype.card (Grp ⧸ H) = 5 := by rw [← Nat.card_eq_fintype_card]; exact hcard5
  let e := Fintype.equivFinOfCardEq hfin5
  refine ⟨e.permCongrHom.toMonoidHom.comp ψ, fun p q hpq => ?_⟩
  exact hψinj (e.permCongrHom.injective hpq)

                                                                                
private theorem sylow5_card_eq_five {G : Type*} [Group G] [Finite G] (P : Sylow 5 G)
    (h5 : (5 : ℕ) ∣ Nat.card G) (h25 : ¬ (25 : ℕ) ∣ Nat.card G) :
    Nat.card (P : Subgroup G) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hf : (Nat.card G).factorization 5 = 1 := by
    have h1 : 1 ≤ (Nat.card G).factorization 5 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hne, pow_one]; exact h5
    have h2 : (Nat.card G).factorization 5 ≤ 1 := by
      by_contra hc
      have hge : 2 ≤ (Nat.card G).factorization 5 := by omega
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hne] at hge
      exact h25 (by rw [show (25 : ℕ) = 5 ^ 2 from by norm_num]; exact hge)
    omega
  rw [P.card_eq_multiplicity, hf, pow_one]

                                                                
private lemma count_aux_card_ne_one {G : Type*} [Group G] [Finite G] :
    Nat.card {x : G // x ≠ 1} = Nat.card G - 1 := by
  classical
  haveI : Unique {x : G // x = 1} := ⟨⟨⟨1, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  have hsum : Nat.card G = Nat.card {x : G // x = 1} + Nat.card {x : G // x ≠ 1} := by
    rw [← Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl (fun x : G => x = 1))).symm
  have h1 : Nat.card {x : G // x = 1} = 1 := Nat.card_unique
  omega

                                                                                       
private theorem sylow_card_eq_pow {G : Type*} [Group G] [Finite G] {p e : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hpe : p ^ e ∣ Nat.card G) (hpe1 : ¬ p ^ (e + 1) ∣ Nat.card G) :
    Nat.card (P : Subgroup G) = p ^ e := by
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hp : p.Prime := Fact.out
  have hf : (Nat.card G).factorization p = e := by
    have h1 : e ≤ (Nat.card G).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hne).mp hpe
    have h2 : ¬ (e + 1) ≤ (Nat.card G).factorization p :=
      fun h => hpe1 ((Nat.Prime.pow_dvd_iff_le_factorization hp hne).mpr h)
    omega
  rw [P.card_eq_multiplicity, hf]

                                                                                           
                                                                                               
                                                                                                
                                                                                               
private theorem card_orderOf_eq_prime_mul_card_sylow {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (hp1 : p ∣ Nat.card H) (hp2 : ¬ (p : ℕ) ^ 2 ∣ Nat.card H) :
    Nat.card {g : H // orderOf g = p} = (p - 1) * Nat.card (Sylow p H) := by
  classical
  have hp : p.Prime := Fact.out
  have hcard : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hn1 : (Nat.card H).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card H).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hcard]; simpa using hp1
    have h2 : ¬ 2 ≤ (Nat.card H).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hcard]; exact hp2
    omega
  have hcardP : ∀ P : Sylow p H, Nat.card (P : Subgroup H) = p := by
    intro P
    rw [P.card_eq_multiplicity, hn1, pow_one]
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  have hzp : ∀ g : {g : H // orderOf g = p},
      Nat.card (Subgroup.zpowers g.val) = p ^ (Nat.card H).factorization p := by
    intro g
    rw [Nat.card_zpowers, g.2, hn1, pow_one]
  set f : {g : H // orderOf g = p} → Sylow p H :=
    fun g => Sylow.ofCard (Subgroup.zpowers g.val) (hzp g) with hf
  have hmemf : ∀ g : {g : H // orderOf g = p}, g.val ∈ (f g : Subgroup H) := by
    intro g
    rw [hf]
    simp only [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers _
  have hAcard : Nat.card {g : H // orderOf g = p}
      = ∑ P : Sylow p H, Nat.card {g : {g : H // orderOf g = p} // f g = P} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  have hfiber : ∀ P : Sylow p H,
      Nat.card {g : {g : H // orderOf g = p} // f g = P} = p - 1 := by
    intro P
    have hPcard : Nat.card (P : Subgroup H) = p := hcardP P
    let e : {g : {g : H // orderOf g = p} // f g = P} ≃ {x : (P : Subgroup H) // x ≠ 1} :=
    { toFun := fun g => ⟨⟨g.1.1, by have := hmemf g.1; rw [g.2] at this; exact this⟩, by
        intro h
        have hg1 : g.1.1 = 1 := by
          have := congrArg (Subgroup.subtype (P : Subgroup H)) h
          simpa using this
        have hord : orderOf g.1.1 = p := g.1.2
        rw [hg1, orderOf_one] at hord
        exact hp.ne_one hord.symm⟩
      invFun := fun x => ⟨⟨(x.1 : H), by
          have hdvd : orderOf (x.1 : H) ∣ p := by
            rw [Subgroup.orderOf_coe]
            have h := orderOf_dvd_natCard x.1
            rwa [hPcard] at h
          have hne : orderOf (x.1 : H) ≠ 1 := by
            rw [Subgroup.orderOf_coe]
            intro hh
            exact x.2 (orderOf_eq_one_iff.mp hh)
          rcases (Nat.dvd_prime hp).mp hdvd with h | h
          · exact absurd h hne
          · exact h⟩, by
        apply Sylow.ext
        simp only [hf, Sylow.coe_ofCard]
        apply Subgroup.eq_of_le_of_card_ge
        · rw [Subgroup.zpowers_le]
          exact x.1.2
        · rw [hPcard, Nat.card_zpowers, Subgroup.orderOf_coe]
          have hdvd : orderOf x.1 ∣ p := by
            have h := orderOf_dvd_natCard x.1
            rwa [hPcard] at h
          rcases (Nat.dvd_prime hp).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) x.2
          · rw [h]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl }
    rw [Nat.card_congr e, count_aux_card_ne_one, hPcard]
  rw [hAcard]
  simp only [hfiber]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.mul_comm]

                                                                                         
                                                  
private theorem subsingleton_sylow5_of_card_le {H : Type*} [Group H] [Finite H]
    {k : ℕ} (hk : Nat.card H = 5 * k) (hk4 : k ≤ 4) : Subsingleton (Sylow 5 H) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hk1 : 1 ≤ k := by
    have : 0 < Nat.card H := Nat.card_pos
    omega
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 H))
  have hPcard : Nat.card (P : Subgroup H) = 5 :=
    sylow5_card_eq_five P ⟨k, hk⟩ (by rw [hk]; omega)
  have hidx : (P : Subgroup H).index = k := by
    have hmul := Subgroup.card_mul_index (P : Subgroup H)
    rw [hPcard, hk] at hmul; omega
  have hdvd5 : Nat.card (Sylow 5 H) ∣ k := hidx ▸ P.card_dvd_index
  have hn5le : Nat.card (Sylow 5 H) ≤ 4 := le_trans (Nat.le_of_dvd (by omega) hdvd5) hk4
  have hmod : Nat.card (Sylow 5 H) % 5 = 1 % 5 := card_sylow_modEq_one 5 H
  have hn5pos : 0 < Nat.card (Sylow 5 H) := Nat.card_pos
  have hn5eq : Nat.card (Sylow 5 H) = 1 := by omega
  exact (Nat.card_eq_one_iff_unique.mp hn5eq).1

                                                                                            
                                                                                           
                                                          
private theorem exists_normal_of_subsingleton_sylow5_quot {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] [Subsingleton (Sylow 5 (H ⧸ N))]
    (hq5 : (5 : ℕ) ∣ Nat.card (H ⧸ N)) (hq25 : ¬ (25 : ℕ) ∣ Nat.card (H ⧸ N)) :
    ∃ M : Subgroup H, M.Normal ∧ Nat.card M = 5 * Nat.card N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 5 (H ⧸ N)))
  have hScard : Nat.card (S : Subgroup (H ⧸ N)) = 5 := sylow5_card_eq_five S hq5 hq25
  haveI hSnormal : (S : Subgroup (H ⧸ N)).Normal := S.normal_of_subsingleton
  let f : H →* H ⧸ N := QuotientGroup.mk' N
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
  refine ⟨(S : Subgroup (H ⧸ N)).comap f, inferInstance, ?_⟩
  have hidx : ((S : Subgroup (H ⧸ N)).comap f).index = (S : Subgroup (H ⧸ N)).index :=
    (S : Subgroup (H ⧸ N)).index_comap_of_surjective hfsurj
  have hmulM := Subgroup.card_mul_index ((S : Subgroup (H ⧸ N)).comap f)
  rw [hidx] at hmulM
  have hmulS := Subgroup.card_mul_index (S : Subgroup (H ⧸ N))
  rw [hScard] at hmulS
  have hquot : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hqpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
  have hSidxpos : 0 < (S : Subgroup (H ⧸ N)).index := by omega
  have key : Nat.card ((S : Subgroup (H ⧸ N)).comap f) * (S : Subgroup (H ⧸ N)).index
      = (5 * Nat.card N) * (S : Subgroup (H ⧸ N)).index := by
    rw [hmulM, hquot, ← hmulS]; ring
  exact Nat.eq_of_mul_eq_mul_right hSidxpos key

                                                                                           
                                                                                            
                                                                                         
private theorem subsingleton_sylow5_of_normal_subgroup {H : Type*} [Group H] [Finite H]
    (M : Subgroup H) [M.Normal] [Subsingleton (Sylow 5 M)]
    (h5M : (5 : ℕ) ∣ Nat.card M) (h25H : ¬ (25 : ℕ) ∣ Nat.card H) :
    Subsingleton (Sylow 5 H) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 M))
  have h25M : ¬ (25 : ℕ) ∣ Nat.card M :=
    fun h => h25H (h.trans (Subgroup.card_subgroup_dvd_card M))
  have hPcard : Nat.card (P : Subgroup M) = 5 := sylow5_card_eq_five P h5M h25M
  haveI : (P : Subgroup M).Characteristic := Sylow.characteristic_of_subsingleton P
  have hQnormal : ((P : Subgroup M).map M.subtype).Normal := inferInstance
  have hcardQ : Nat.card ((P : Subgroup M).map M.subtype) = 5 := by
    have e := Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective
    rw [← Nat.card_congr e.toEquiv, hPcard]
  have hpg : IsPGroup 5 ((P : Subgroup M).map M.subtype) :=
    IsPGroup.of_card (hcardQ.trans (show (5 : ℕ) = 5 ^ 1 by norm_num))
  have hQidx : ¬ (5 : ℕ) ∣ ((P : Subgroup M).map M.subtype).index := by
    intro hdvd
    have hmul := Subgroup.card_mul_index ((P : Subgroup M).map M.subtype)
    rw [hcardQ] at hmul
    obtain ⟨j, hj⟩ := hdvd
    exact h25H (by rw [← hmul, hj]; exact ⟨j, by ring⟩)
  let QS : Sylow 5 H := hpg.toSylow hQidx
  have hQScoe : (QS : Subgroup H) = (P : Subgroup M).map M.subtype := hpg.toSylow_coe hQidx
  haveI : Unique (Sylow 5 H) :=
    Sylow.unique_of_normal QS (by rw [hQScoe]; exact hQnormal)
  infer_instance

                                                                                              
                                                                                             
                                                           
private theorem card_thirty_subsingleton_sylow5 {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 30) : Subsingleton (Sylow 5 H) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hns
                                                                                                
  have hn5dvd : Nat.card (Sylow 5 H) ∣ 6 := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 H))
    have hPcard : Nat.card (P : Subgroup H) = 5 :=
      sylow5_card_eq_five P (by rw [hH]; norm_num) (by rw [hH]; norm_num)
    have hidx : (P : Subgroup H).index = 6 := by
      have := Subgroup.card_mul_index (P : Subgroup H); rw [hPcard, hH] at this; omega
    exact hidx ▸ P.card_dvd_index
  have hn5mod : Nat.card (Sylow 5 H) % 5 = 1 % 5 := card_sylow_modEq_one 5 H
  have hn5ne1 : Nat.card (Sylow 5 H) ≠ 1 := fun h => hns (Nat.card_eq_one_iff_unique.mp h).1
  have hn5le : Nat.card (Sylow 5 H) ≤ 6 := Nat.le_of_dvd (by norm_num) hn5dvd
  have hn5 : Nat.card (Sylow 5 H) = 6 := by interval_cases (Nat.card (Sylow 5 H)) <;> omega
  have hc5 : Nat.card {g : H // orderOf g = 5} = 24 := by
    have := card_orderOf_eq_prime_mul_card_sylow (H := H) 5 (by rw [hH]; norm_num)
      (by rw [hH]; norm_num)
    rw [hn5] at this; omega
  have hc3 : Nat.card {g : H // orderOf g = 3} = 2 * Nat.card (Sylow 3 H) := by
    have := card_orderOf_eq_prime_mul_card_sylow (H := H) 3 (by rw [hH]; norm_num)
      (by rw [hH]; norm_num)
    simpa using this
                                                                                          
  have hinj : Function.Injective
      (Sum.elim (Subtype.val : {g : H // orderOf g = 5} → H)
                (Subtype.val : {g : H // orderOf g = 3} → H)) := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exact absurd (by rw [← a.2, hab, b.2] : (5 : ℕ) = 3) (by norm_num)
    · exact absurd (by rw [← a.2, hab, b.2] : (3 : ℕ) = 5) (by norm_num)
    · exact congrArg Sum.inr (Subtype.ext hab)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_sum, hc5, hc3, hH] at hle
  have hn3mod : Nat.card (Sylow 3 H) % 3 = 1 % 3 := card_sylow_modEq_one 3 H
  have hn3pos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
  have hn3 : Nat.card (Sylow 3 H) = 1 := by omega
  haveI : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp hn3).1
                                                                                        
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 H))
  haveI : (Q : Subgroup H).Normal := Q.normal_of_subsingleton
  have hQcard : Nat.card (Q : Subgroup H) = 3 := by
    have hne : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have hf : (Nat.card H).factorization 3 = 1 := by
      have h1 : 1 ≤ (Nat.card H).factorization 3 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hne, pow_one, hH]; norm_num
      have h2 : (Nat.card H).factorization 3 ≤ 1 := by
        by_contra hc
        have hge : 2 ≤ (Nat.card H).factorization 3 := by omega
        rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hne, hH] at hge
        exact absurd hge (by decide)
      omega
    rw [Q.card_eq_multiplicity, hf, pow_one]
  have hquotcard : Nat.card (H ⧸ (Q : Subgroup H)) = 10 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q : Subgroup H)
    rw [hH, hQcard] at this; omega
  haveI : Subsingleton (Sylow 5 (H ⧸ (Q : Subgroup H))) :=
    subsingleton_sylow5_of_card_le (k := 2) (hquotcard.trans (by norm_num)) (by norm_num)
  obtain ⟨M, hMnorm, hMcard⟩ := exists_normal_of_subsingleton_sylow5_quot (Q : Subgroup H)
    (by rw [hquotcard]; norm_num) (by rw [hquotcard]; norm_num)
  haveI : M.Normal := hMnorm
  have hMcard15 : Nat.card M = 15 := by rw [hMcard, hQcard]
  haveI : Subsingleton (Sylow 5 M) :=
    subsingleton_sylow5_of_card_le (k := 3) (hMcard15.trans (by norm_num)) (by norm_num)
  exact hns (subsingleton_sylow5_of_normal_subgroup M (by rw [hMcard15]; norm_num)
    (by rw [hH]; norm_num))

                                                                                               
                                                                                                  
                                                                                           
                                                               
private theorem eq_top_of_five_dvd_card_normal {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (hn5 : Nontrivial (Sylow 5 G))
    (N : Subgroup G) [N.Normal] (h5 : (5 : ℕ) ∣ Nat.card N) : N = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : Nat.card N ∣ 60 := by rw [← hG]; exact Subgroup.card_subgroup_dvd_card N
  by_contra hne
  have hNe60 : Nat.card N ≠ 60 := fun h => hne (Subgroup.eq_top_of_card_eq _ (by rw [h, hG]))
                                                                                    
  have hmem : Nat.card N = 5 ∨ Nat.card N = 10 ∨ Nat.card N = 15 ∨ Nat.card N = 20 ∨
      Nat.card N = 30 := by
    have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card N := Nat.card_pos
    interval_cases (Nat.card N) <;> omega
                                                                                            
                                 
  haveI hSubN : Subsingleton (Sylow 5 N) := by
    rcases hmem with h | h | h | h | h
    · exact subsingleton_sylow5_of_card_le (k := 1) (h.trans (by norm_num)) (by norm_num)
    · exact subsingleton_sylow5_of_card_le (k := 2) (h.trans (by norm_num)) (by norm_num)
    · exact subsingleton_sylow5_of_card_le (k := 3) (h.trans (by norm_num)) (by norm_num)
    · exact subsingleton_sylow5_of_card_le (k := 4) (h.trans (by norm_num)) (by norm_num)
    · exact card_thirty_subsingleton_sylow5 h
  have hSubG : Subsingleton (Sylow 5 G) :=
    subsingleton_sylow5_of_normal_subgroup N h5 (by rw [hG]; norm_num)
  exact (not_nontrivial_iff_subsingleton.mpr hSubG) hn5

                                                                                                
                                                                                           
                                                                                                   
                                                                 
private theorem not_normal_card_mem_two_three_four_six {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (hn5 : Nontrivial (Sylow 5 G))
    (N : Subgroup G) [N.Normal]
    (hcard : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4 ∨ Nat.card N = 6) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hqc : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hG] at hqc
                                                                               
  obtain ⟨hq5, hq25, hSub⟩ : (5 : ℕ) ∣ Nat.card (G ⧸ N) ∧ ¬ (25 : ℕ) ∣ Nat.card (G ⧸ N) ∧
      Subsingleton (Sylow 5 (G ⧸ N)) := by
    rcases hcard with h | h | h | h <;> rw [h] at hqc
    · have hq : Nat.card (G ⧸ N) = 30 := by omega
      exact ⟨by rw [hq]; norm_num, by rw [hq]; norm_num, card_thirty_subsingleton_sylow5 hq⟩
    · have hq : Nat.card (G ⧸ N) = 20 := by omega
      exact ⟨by rw [hq]; norm_num, by rw [hq]; norm_num,
        subsingleton_sylow5_of_card_le (k := 4) (hq.trans (by norm_num)) (by norm_num)⟩
    · have hq : Nat.card (G ⧸ N) = 15 := by omega
      exact ⟨by rw [hq]; norm_num, by rw [hq]; norm_num,
        subsingleton_sylow5_of_card_le (k := 3) (hq.trans (by norm_num)) (by norm_num)⟩
    · have hq : Nat.card (G ⧸ N) = 10 := by omega
      exact ⟨by rw [hq]; norm_num, by rw [hq]; norm_num,
        subsingleton_sylow5_of_card_le (k := 2) (hq.trans (by norm_num)) (by norm_num)⟩
  haveI := hSub
                                                                             
  obtain ⟨M, hMnorm, hMcard⟩ := exists_normal_of_subsingleton_sylow5_quot N hq5 hq25
  haveI : M.Normal := hMnorm
  have h5M : (5 : ℕ) ∣ Nat.card M := ⟨Nat.card N, hMcard⟩
  have hMtop : M = ⊤ := eq_top_of_five_dvd_card_normal hG hn5 M h5M
  have hMcard60 : Nat.card M = 60 := by rw [hMtop, Subgroup.card_top, hG]
  rcases hcard with h | h | h | h <;> rw [h] at hMcard <;> omega

                                                                                                
                                                                                                 
                                  
private theorem exists_normal_prime_of_card_twelve {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : Nat.card N = 12) :
    ∃ M : Subgroup G, M.Normal ∧ (Nat.card M = 3 ∨ Nat.card M = 4) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  by_cases hS3 : Subsingleton (Sylow 3 ↥N)
  ·                                                                             
    haveI := hS3
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥N))
    have hPcard : Nat.card (P : Subgroup ↥N) = 3 := by
      have h := sylow_card_eq_pow (e := 1) P (by rw [hN]; norm_num) (by rw [hN]; decide)
      norm_num at h; exact h
    haveI : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_subsingleton P
    refine ⟨(P : Subgroup ↥N).map N.subtype, inferInstance, Or.inl ?_⟩
    have e := Subgroup.equivMapOfInjective (P : Subgroup ↥N) N.subtype N.subtype_injective
    rw [← Nat.card_congr e.toEquiv, hPcard]
  ·                                                                                          
                                                 
    have hn3 : Nat.card (Sylow 3 ↥N) = 4 := by
      obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 ↥N))
      have hP3card : Nat.card (P3 : Subgroup ↥N) = 3 := by
        have h := sylow_card_eq_pow (e := 1) P3 (by rw [hN]; norm_num) (by rw [hN]; decide)
        norm_num at h; exact h
      have hidx : (P3 : Subgroup ↥N).index = 4 := by
        have := Subgroup.card_mul_index (P3 : Subgroup ↥N); rw [hP3card, hN] at this; omega
      have hdvd : Nat.card (Sylow 3 ↥N) ∣ 4 := hidx ▸ P3.card_dvd_index
      have hmod : Nat.card (Sylow 3 ↥N) % 3 = 1 % 3 := card_sylow_modEq_one 3 ↥N
      have hne1 : Nat.card (Sylow 3 ↥N) ≠ 1 := fun h => hS3 (Nat.card_eq_one_iff_unique.mp h).1
      have hle : Nat.card (Sylow 3 ↥N) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases (Nat.card (Sylow 3 ↥N)) <;> omega
    have hc3 : Nat.card {g : ↥N // orderOf g = 3} = 8 := by
      have := card_orderOf_eq_prime_mul_card_sylow (H := ↥N) 3 (by rw [hN]; norm_num)
        (by rw [hN]; decide)
      rw [hn3] at this; omega
    have hcompl : Nat.card {g : ↥N // ¬ orderOf g = 3} = 4 := by
      have h := Nat.card_congr (Equiv.sumCompl (fun g : ↥N => orderOf g = 3))
      rw [Nat.card_sum, hc3, hN] at h; omega
    haveI hSub2 : Subsingleton (Sylow 2 ↥N) := by
      have key : ∀ T : Sylow 2 ↥N,
          (↑(T : Subgroup ↥N) : Set ↥N) = {g : ↥N | ¬ orderOf g = 3} := by
        intro T
        have hTc : Nat.card (T : Subgroup ↥N) = 4 := by
          have h := sylow_card_eq_pow (e := 2) T (by rw [hN]; norm_num) (by rw [hN]; decide)
          norm_num at h; exact h
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
        · intro g hg
          simp only [SetLike.mem_coe] at hg
          simp only [Set.mem_setOf_eq]
          intro h3
          have hord : orderOf (⟨g, hg⟩ : (T : Subgroup ↥N)) = 3 := by
            rw [Subgroup.orderOf_mk]; exact h3
          have hdvd : orderOf (⟨g, hg⟩ : (T : Subgroup ↥N)) ∣ Nat.card (T : Subgroup ↥N) :=
            orderOf_dvd_natCard _
          rw [hTc, hord] at hdvd
          exact absurd hdvd (by decide)
        · have hTncard : (↑(T : Subgroup ↥N) : Set ↥N).ncard = 4 := by
            rw [← Nat.card_coe_set_eq]; exact hTc
          have hCncard : ({g : ↥N | ¬ orderOf g = 3}).ncard = 4 := by
            rw [← Nat.card_coe_set_eq]; exact hcompl
          exact le_of_eq (hCncard.trans hTncard.symm)
      exact ⟨fun S S' => Sylow.ext (SetLike.coe_injective (by rw [key S, key S']))⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥N))
    have hPcard : Nat.card (P : Subgroup ↥N) = 4 := by
      have h := sylow_card_eq_pow (e := 2) P (by rw [hN]; norm_num) (by rw [hN]; decide)
      norm_num at h; exact h
    haveI : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_subsingleton P
    refine ⟨(P : Subgroup ↥N).map N.subtype, inferInstance, Or.inr ?_⟩
    have e := Subgroup.equivMapOfInjective (P : Subgroup ↥N) N.subtype N.subtype_injective
    rw [← Nat.card_congr e.toEquiv, hPcard]

                                                                                               
                                                                                          
                                                                            

                                                                                              
                                                                                          
                                                                

                                                                                                  
                                                                                               
                                                                                               
                                                                                                  
                                                                                      
                                                                                                 
                                                                                          
                                                                                        
                                                                                                
                                                                                 

                                                                                               
                                                                                                
                                                                                          
                                                                                        
                                                                                  
/-- A simplicity criterion for the finite group appearing in the formal statement. -/
theorem simpleGroup_011652
    {Grp : Type*} [Group Grp] [Finite Grp] (hcard : Nat.card Grp = 60)
    (hn5 : Nontrivial (Sylow 5 Grp)) :
    IsSimpleGroup Grp := by
  haveI : Nontrivial Grp := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  refine { eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  haveI : N.Normal := hN
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
                                                                                   
  have hdvd : Nat.card N ∣ 60 := by
    rw [← hcard]; exact Subgroup.card_subgroup_dvd_card N
  have hNe1 : Nat.card N ≠ 1 := fun h => hNbot (Subgroup.eq_bot_of_card_eq _ h)
  have hNe60 : Nat.card N ≠ 60 := by
    intro h
    exact hNtop (Subgroup.eq_top_of_card_eq _ (by rw [h, hcard]))
                                     
  by_cases h5 : (5 : ℕ) ∣ Nat.card N
  · exact hNtop (eq_top_of_five_dvd_card_normal hcard hn5 N h5)
  ·                                           
    have key : ∀ n : ℕ, n ∣ 60 → n ≠ 1 → n ≠ 60 → ¬ (5 ∣ n) →
        n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12 := by
      intro n hn h1 h60 h5n
      have hle : n ≤ 60 := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> omega
    rcases key (Nat.card N) hdvd hNe1 hNe60 h5 with h | h | h | h | h
    · exact not_normal_card_mem_two_three_four_six hcard hn5 N (Or.inl h)
    · exact not_normal_card_mem_two_three_four_six hcard hn5 N (Or.inr (Or.inl h))
    · exact not_normal_card_mem_two_three_four_six hcard hn5 N (Or.inr (Or.inr (Or.inl h)))
    · exact not_normal_card_mem_two_three_four_six hcard hn5 N (Or.inr (Or.inr (Or.inr h)))
    ·                                                                
      obtain ⟨M, hMnorm, hMcard⟩ := exists_normal_prime_of_card_twelve N h
      haveI : M.Normal := hMnorm
      rcases hMcard with h3 | h4
      · exact not_normal_card_mem_two_three_four_six hcard hn5 M (Or.inr (Or.inl h3))
      · exact not_normal_card_mem_two_three_four_six hcard hn5 M (Or.inr (Or.inr (Or.inl h4)))

                                                                                                 
                                                                                                 
                                                                                                  
                                                                                                  
                                           
private theorem simpleGroup_card_dvd_index_factorial {Grp : Type*} [Group Grp] [Finite Grp]
    (hsimple : IsSimpleGroup Grp) (K : Subgroup Grp) (hK : 2 ≤ K.index) :
    Nat.card Grp ∣ (K.index).factorial := by
  classical
  haveI := hsimple
  set ψ : Grp →* Equiv.Perm (Grp ⧸ K) := MulAction.toPermHom Grp (Grp ⧸ K) with hψ
  have hker : ψ.ker = K.normalCore := (Subgroup.normalCore_eq_ker K).symm
  have hnc : K.normalCore = ⊥ := by
    rcases (Subgroup.normalCore_normal K).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hKtop : K = ⊤ := top_le_iff.mp (h ▸ K.normalCore_le)
      rw [hKtop, Subgroup.index_top] at hK; omega
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hnc]
  have hdvd := Subgroup.card_dvd_of_injective ψ hψinj
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at hdvd

                                                                                                   
                                                                                         
                                                                                            
                                                                                              
                                                                                           
                                                                                                
                                                                                                  
                                                                                    
private theorem exists_index_five_of_sylow2_card_fifteen {Grp : Type*} [Group Grp] [Finite Grp]
    (hsimple : IsSimpleGroup Grp) (hcard : Nat.card Grp = 60)
    (hn2 : Nat.card (Sylow 2 Grp) = 15) : ∃ H : Subgroup Grp, H.index = 5 := by
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
                                                                                  
  have hn5 : Nat.card (Sylow 5 Grp) = 6 := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 Grp))
    have hPcard : Nat.card (P : Subgroup Grp) = 5 :=
      sylow5_card_eq_five P (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    have hidx : (P : Subgroup Grp).index = 12 := by
      have := Subgroup.card_mul_index (P : Subgroup Grp); rw [hPcard, hcard] at this; omega
    have hdvd : Nat.card (Sylow 5 Grp) ∣ 12 := hidx ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow 5 Grp) % 5 = 1 % 5 := card_sylow_modEq_one 5 Grp
    have hne1 : Nat.card (Sylow 5 Grp) ≠ 1 := by
      intro h
      haveI : Subsingleton (Sylow 5 Grp) := (Nat.card_eq_one_iff_unique.mp h).1
      haveI : (P : Subgroup Grp).Normal := P.normal_of_subsingleton
      rcases hsimple.eq_bot_or_eq_top_of_normal (P : Subgroup Grp) inferInstance with hb | ht
      · rw [hb, Subgroup.card_bot] at hPcard; omega
      · rw [ht, Subgroup.card_top, hcard] at hPcard; omega
    have hle : Nat.card (Sylow 5 Grp) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases (Nat.card (Sylow 5 Grp)) <;> omega
  have hc5 : Nat.card {g : Grp // orderOf g = 5} = 24 := by
    have := card_orderOf_eq_prime_mul_card_sylow (H := Grp) 5 (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num)
    rw [hn5] at this; omega
  have hc5c : Nat.card {g : Grp // orderOf g ≠ 5} = 36 := by
    have h := Nat.card_congr (Equiv.sumCompl (fun g : Grp => orderOf g = 5))
    rw [Nat.card_sum, hc5, hcard] at h
    have he : Nat.card {g : Grp // orderOf g ≠ 5} = Nat.card {x : Grp // ¬ orderOf x = 5} := rfl
    rw [he]; omega
                                                                                           
  have hf5 : ∀ (P : Sylow 2 Grp) (x : (P : Subgroup Grp)), orderOf ((x : Grp)) ≠ 5 := by
    intro P x
    have hPcard : Nat.card (P : Subgroup Grp) = 4 := by
      have h := sylow_card_eq_pow (e := 2) P (by rw [hcard]; norm_num) (by rw [hcard]; decide)
      norm_num at h; exact h
    have hdvd : orderOf ((x : Grp)) ∣ 4 := by
      rw [Subgroup.orderOf_coe, ← hPcard]; exact orderOf_dvd_natCard x
    intro h5; rw [h5] at hdvd; exact absurd hdvd (by decide)
  by_cases hinter : ∃ P Q : Sylow 2 Grp, ∃ t : Grp,
      t ∈ (P : Subgroup Grp) ∧ t ∈ (Q : Subgroup Grp) ∧ t ≠ 1 ∧ (P : Subgroup Grp) ≠ Q
  ·                                                                        
    obtain ⟨P₁, P₂, t, ht1, ht2, htne, hPsub⟩ := hinter
    have hP1card : Nat.card (P₁ : Subgroup Grp) = 4 := by
      have h := sylow_card_eq_pow (e := 2) P₁ (by rw [hcard]; norm_num) (by rw [hcard]; decide)
      norm_num at h; exact h
    have hP2card : Nat.card (P₂ : Subgroup Grp) = 4 := by
      have h := sylow_card_eq_pow (e := 2) P₂ (by rw [hcard]; norm_num) (by rw [hcard]; decide)
      norm_num at h; exact h
    haveI hcomm1 : IsMulCommutative (P₁ : Subgroup Grp) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (hP1card.trans (by norm_num))
    haveI hcomm2 : IsMulCommutative (P₂ : Subgroup Grp) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (hP2card.trans (by norm_num))
    set C : Subgroup Grp := Subgroup.centralizer {t} with hC
                                                            
    have hsub_le : ∀ (P : Sylow 2 Grp), t ∈ (P : Subgroup Grp) →
        IsMulCommutative (P : Subgroup Grp) → (P : Subgroup Grp) ≤ C := by
      intro P hmemt hcomm x hx
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh; subst hh
      have hxt := hcomm.is_comm.comm (⟨x, hx⟩ : (P : Subgroup Grp))
        (⟨h, hmemt⟩ : (P : Subgroup Grp))
      have := congrArg (fun z : (P : Subgroup Grp) => (z : Grp)) hxt
      simpa using this.symm
    have hP1le : (P₁ : Subgroup Grp) ≤ C := hsub_le P₁ ht1 hcomm1
    have hP2le : (P₂ : Subgroup Grp) ≤ C := hsub_le P₂ ht2 hcomm2
    have h4dvd : (4 : ℕ) ∣ Nat.card C := hP1card ▸ Subgroup.card_dvd_of_le hP1le
    have hCdvd : Nat.card C ∣ 60 := by rw [← hcard]; exact Subgroup.card_subgroup_dvd_card C
    have hne4 : Nat.card C ≠ 4 := by
      intro h4
      have e1 : (P₁ : Subgroup Grp) = C := Subgroup.eq_of_le_of_card_ge hP1le (by rw [h4, hP1card])
      have e2 : (P₂ : Subgroup Grp) = C := Subgroup.eq_of_le_of_card_ge hP2le (by rw [h4, hP2card])
      exact hPsub (e1.trans e2.symm)
    have hCmem : Nat.card C = 12 ∨ Nat.card C = 20 ∨ Nat.card C = 60 := by
      have hle : Nat.card C ≤ 60 := Nat.le_of_dvd (by norm_num) hCdvd
      have hpos : 0 < Nat.card C := Nat.card_pos
      interval_cases (Nat.card C) <;> omega
                                       
    have htc : t ∉ Subgroup.center Grp := by
      intro htmem
      have hne : Subgroup.center Grp ≠ ⊥ := by
        intro h; rw [h, Subgroup.mem_bot] at htmem; exact htne htmem
      have htop : Subgroup.center Grp = ⊤ :=
        (hsimple.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_left hne
      haveI : IsMulCommutative Grp := Subgroup.center_eq_top_iff.mp htop
      exact absurd (Group.is_simple_iff_prime_card.mp hsimple) (by rw [hcard]; norm_num)
    rcases hCmem with h12 | h20 | h60
    · exact ⟨C, by have := Subgroup.card_mul_index C; rw [h12, hcard] at this; omega⟩
    · exfalso
      have hidx3 : C.index = 3 := by
        have := Subgroup.card_mul_index C; rw [h20, hcard] at this; omega
      have hdd := simpleGroup_card_dvd_index_factorial hsimple C (by rw [hidx3]; norm_num)
      rw [hidx3, hcard] at hdd; exact absurd hdd (by decide)
    · exfalso
      have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h60, hcard])
      have hsub : ({t} : Set Grp) ⊆ Subgroup.center Grp := by
        rw [← Subgroup.centralizer_eq_top_iff_subset]; exact hCtop
      exact htc (hsub (Set.mem_singleton t))
  ·                                                                                             
    exfalso
    push Not at hinter
    have hDcard : Nat.card (Σ P : Sylow 2 Grp, {x : (P : Subgroup Grp) // x ≠ 1}) = 45 := by
      letI : Fintype (Sylow 2 Grp) := Fintype.ofFinite _
      have hfib : ∀ P : Sylow 2 Grp, Nat.card {x : (P : Subgroup Grp) // x ≠ 1} = 3 := by
        intro P
        have hPcard : Nat.card (P : Subgroup Grp) = 4 := by
          have h := sylow_card_eq_pow (e := 2) P (by rw [hcard]; norm_num) (by rw [hcard]; decide)
          norm_num at h; exact h
        rw [count_aux_card_ne_one, hPcard]
      have hfc : Fintype.card (Sylow 2 Grp) = 15 := by rw [← Nat.card_eq_fintype_card, hn2]
      rw [Nat.card_sigma]
      simp only [hfib]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hfc]
    have hinj : Function.Injective
        (fun d : Σ P : Sylow 2 Grp, {x : (P : Subgroup Grp) // x ≠ 1} =>
          (⟨((d.2.1 : (d.1 : Subgroup Grp)) : Grp), hf5 d.1 d.2.1⟩
            : {g : Grp // orderOf g ≠ 5})) := by
      rintro ⟨P, x, hx⟩ ⟨Q, y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy
      have hg1 : ((x : Grp)) ≠ 1 := fun h => hx (Subtype.ext h)
      have hxQ : ((x : Grp)) ∈ (Q : Subgroup Grp) := by rw [hxy]; exact y.2
      have hPQ : (P : Subgroup Grp) = (Q : Subgroup Grp) := hinter P Q (x : Grp) x.2 hxQ hg1
      have hPQ' : P = Q := Sylow.ext hPQ
      subst hPQ'
      exact congrArg (Sigma.mk P) (Subtype.ext (Subtype.ext hxy))
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hDcard, hc5c] at hle
    omega

                                                                                              
                                                                                            
                                                                        

                                                                                                
                                                                                               
                                                                                                
                                                                                                   
                                                                                    
/-- A simplicity criterion for the finite group appearing in the formal statement. -/
theorem simpleGroup_011774
    {Grp : Type*} [Group Grp] [Finite Grp] (hsimple : IsSimpleGroup Grp)
    (hcard : Nat.card Grp = 60) :
    ∃ H : Subgroup Grp, H.index = 5 := by
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Grp))
  have hPcard : Nat.card (P : Subgroup Grp) = 4 := by
    have h := sylow_card_eq_pow (e := 2) P (by rw [hcard]; norm_num) (by rw [hcard]; decide)
    norm_num at h; exact h
  have hidx : (P : Subgroup Grp).index = 15 := by
    have := Subgroup.card_mul_index (P : Subgroup Grp); rw [hPcard, hcard] at this; omega
  have hdvd : Nat.card (Sylow 2 Grp) ∣ 15 := hidx ▸ P.card_dvd_index
  have hne1 : Nat.card (Sylow 2 Grp) ≠ 1 := by
    intro h
    haveI : Subsingleton (Sylow 2 Grp) := (Nat.card_eq_one_iff_unique.mp h).1
    haveI : (P : Subgroup Grp).Normal := P.normal_of_subsingleton
    rcases hsimple.eq_bot_or_eq_top_of_normal (P : Subgroup Grp) inferInstance with hb | ht
    · rw [hb, Subgroup.card_bot] at hPcard; omega
    · rw [ht, Subgroup.card_top, hcard] at hPcard; omega
  have hmem : Nat.card (Sylow 2 Grp) = 3 ∨ Nat.card (Sylow 2 Grp) = 5 ∨
      Nat.card (Sylow 2 Grp) = 15 := by
    have hle : Nat.card (Sylow 2 Grp) ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 2 Grp) := Nat.card_pos
    interval_cases (Nat.card (Sylow 2 Grp)) <;> omega
  rcases hmem with h3 | h5 | h15
  · exfalso
    have hidx3 : (Subgroup.normalizer (P : Set Grp)).index = 3 := by
      rw [← P.card_eq_index_normalizer]; exact h3
    have hdd := simpleGroup_card_dvd_index_factorial hsimple (Subgroup.normalizer (P : Set Grp))
      (by rw [hidx3]; norm_num)
    rw [hidx3, hcard] at hdd; exact absurd hdd (by decide)
  · refine ⟨Subgroup.normalizer (P : Set Grp), ?_⟩
    rw [← P.card_eq_index_normalizer]; exact h5
  · exact exists_index_five_of_sylow2_card_fifteen hsimple hcard h15

                                                                                            
                                                                 

                                                                                                
                                                                                                
                                                                                           
                                                                                           
                                                                                             
                                                                                                 
                                                                                               
                                                                                                
                                                                                          
                                                                                   
                                          
/-- The displayed stabilizer-cardinality multiset implies that the group is simple. -/
theorem isSimpleGroup_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 5})
    (hcard : Nat.card (↥G) = 60)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    IsSimpleGroup (↥G) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
                                                                                         
  obtain ⟨b, hb⟩ := hpole 5 (by rw [hclass]; decide)
  have horbit_card : Nat.card (↥(MulAction.orbit ↥G b)) = 12 := by
    have hos : Nat.card (↥(MulAction.orbit ↥G b)) * Nat.card (↥(MulAction.stabilizer ↥G b))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G b)
    rw [hb, hcard] at hos
    omega
                                                                                        
                                      
  have hoffaxis : ∃ g : ↥G, ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) ≠ (b : ↥(rotationAxes G)).1
      ∧ ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) ≠ -((b : ↥(rotationAxes G)).1) := by
    by_contra hcon
    push Not at hcon
                                                                 
    have hmem : ∀ g : ↥G, ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = (b : ↥(rotationAxes G)).1
        ∨ ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = -((b : ↥(rotationAxes G)).1) := by
      intro g
      by_cases h : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = (b : ↥(rotationAxes G)).1
      · exact Or.inl h
      · exact Or.inr (hcon g h)
                                                                            
    set S : Set (Fin 3 → ℝ) := {(b : ↥(rotationAxes G)).1, -((b : ↥(rotationAxes G)).1)} with hS
    have hmemset : ∀ x : ↥(MulAction.orbit ↥G b), x.1.1 ∈ S := by
      intro x
      obtain ⟨g, hgx⟩ := x.2
      have hval : ((g • b : ↥(rotationAxes G)) : Fin 3 → ℝ) = x.1.1 := congrArg Subtype.val hgx
      rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff, ← hval]
      exact hmem g
    haveI : Finite ↥S := ((Set.finite_singleton _).insert _).to_subtype
    have hinj : Function.Injective
        (fun x : ↥(MulAction.orbit ↥G b) => (⟨x.1.1, hmemset x⟩ : ↥S)) := by
      intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using hxy
    have hle : Nat.card (↥(MulAction.orbit ↥G b)) ≤ Nat.card ↥S :=
      Nat.card_le_card_of_injective _ hinj
    have hle2 : Nat.card ↥S ≤ 2 := by
      rw [hS, Nat.card_coe_set_eq]
      calc ({(b : ↥(rotationAxes G)).1, -((b : ↥(rotationAxes G)).1)} : Set (Fin 3 → ℝ)).ncard
            ≤ ({-((b : ↥(rotationAxes G)).1)} : Set (Fin 3 → ℝ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [horbit_card] at hle
    omega
  obtain ⟨g, hg1, hg2⟩ := hoffaxis
  set c : ↥(rotationAxes G) := g • b with hc
                                                                                             
  have hcstab : Nat.card (↥(MulAction.stabilizer ↥G c)) = 5 := by
    have horbc : Nat.card (↥(MulAction.orbit ↥G c)) = 12 := by
      rw [hc, MulAction.orbit_smul]; exact horbit_card
    have hos : Nat.card (↥(MulAction.orbit ↥G c)) * Nat.card (↥(MulAction.stabilizer ↥G c))
        = Nat.card (↥G) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥G c)
    rw [horbc, hcard] at hos
    omega
                                                                                                 
  have hidxb : (MulAction.stabilizer ↥G b).index = 12 := by
    have h := Subgroup.index_mul_card (MulAction.stabilizer ↥G b)
    rw [hb, hcard] at h; omega
  have hidxc : (MulAction.stabilizer ↥G c).index = 12 := by
    have h := Subgroup.index_mul_card (MulAction.stabilizer ↥G c)
    rw [hcstab, hcard] at h; omega
  have hpgb : IsPGroup 5 (MulAction.stabilizer ↥G b) := IsPGroup.of_card (n := 1) (by rw [hb]; norm_num)
  have hpgc : IsPGroup 5 (MulAction.stabilizer ↥G c) :=
    IsPGroup.of_card (n := 1) (by rw [hcstab]; norm_num)
  let Sb : Sylow 5 ↥G := hpgb.toSylow (by rw [hidxb]; decide)
  let Sc : Sylow 5 ↥G := hpgc.toSylow (by rw [hidxc]; decide)
                                                                                            
                                                             
  have hSne : Sb ≠ Sc := by
    intro hSeq
    have hsub : MulAction.stabilizer ↥G b = MulAction.stabilizer ↥G c :=
      congrArg (fun S : Sylow 5 ↥G => (S : Subgroup ↥G)) hSeq
    haveI : Nontrivial (MulAction.stabilizer ↥G b) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hb]; norm_num
    obtain ⟨ρ, hρne⟩ := exists_ne (1 : MulAction.stabilizer ↥G b)
                                             
    have hρ0 : ((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := by
      intro h
      exact hρne (Subtype.ext (Subtype.ext (h.trans (OneMemClass.coe_one G).symm)))
    obtain ⟨v₀, _hv₀unit, hset⟩ :=
      rotationAxisSet_eq_pair ((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) hρ0
                              
    have hfixb : (((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ (b : ↥(rotationAxes G)).1 = (b : ↥(rotationAxes G)).1 := by
      have hstab := (MulAction.mem_stabilizer_iff).mp ρ.2
      have h := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) hstab
      rwa [matrixAction_011755] at h
                                                        
    have hρc : (ρ : ↥G) ∈ MulAction.stabilizer ↥G c := hsub ▸ ρ.2
    have hfixc : (((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ (c : ↥(rotationAxes G)).1 = (c : ↥(rotationAxes G)).1 := by
      have hstab := (MulAction.mem_stabilizer_iff).mp hρc
      have h := congrArg (fun P : ↥(rotationAxes G) => (P : Fin 3 → ℝ)) hstab
      rwa [matrixAction_011755] at h
    have hbin : (b : ↥(rotationAxes G)).1
        ∈ rotationAxisSet ((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) := ⟨b.2.1, hfixb⟩
    have hcin : (c : ↥(rotationAxes G)).1
        ∈ rotationAxisSet ((ρ : ↥G) : specialOrthogonalGroup (Fin 3) ℝ) := ⟨c.2.1, hfixc⟩
    rw [hset, Set.mem_insert_iff, Set.mem_singleton_iff] at hbin hcin
                                                                                            
    have hcb : (c : ↥(rotationAxes G)).1 = (b : ↥(rotationAxes G)).1
        ∨ (c : ↥(rotationAxes G)).1 = -((b : ↥(rotationAxes G)).1) := by
      rcases hbin with hbv | hbv <;> rcases hcin with hcv | hcv
      · exact Or.inl (by rw [hcv, hbv])
      · exact Or.inr (by rw [hcv, hbv])
      · exact Or.inr (by rw [hcv, hbv, neg_neg])
      · exact Or.inl (by rw [hcv, hbv])
    rcases hcb with h | h
    · exact hg1 h
    · exact hg2 h
                                                                                       
                                   
  exact simpleGroup_011652 hcard ⟨Sb, Sc, hSne⟩

                                                                                          
                                                                                          
                                                                                              
                                                                                                
                                                                                                 
                                                                                         
                                                                                               
                                                                            
                                                                                            
                                                                                   
/-- The displayed stabilizer data yields an injective homomorphism. -/
theorem exists_injective_hom_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 5})
    (hcard : Nat.card (↥G) = 60)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    ∃ φ : ↥G →* Equiv.Perm (Fin 5), Function.Injective φ := by
                                                                                       
                                                                                   
  have hsimple : IsSimpleGroup (↥G) := isSimpleGroup_of_stabilizer_cardMultiset G m hclass hcard hpole
  obtain ⟨H, hindex⟩ := simpleGroup_011774 hsimple hcard
  exact exists_injective_hom_011633 hsimple H hindex

                                                                                          
                                                                                           
                                                                                           
                                                                                               
                                                                                  
                                                                                     
                  

                                                                    
                                                                                         
          
/-- The displayed stabilizer data identifies the group with the alternating group on five elements. -/
theorem mulEquiv_alternatingGroupFinFive_of_stabilizer_cardMultiset
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] (m : Multiset ℕ)
    (hclass : m = {2, 3, 5})
    (heq : 2 * (1 - (Nat.card (↥G) : ℚ)⁻¹) = (m.map (fun x => 1 - (x : ℚ)⁻¹)).sum)
    (hpole : ∀ x ∈ m, ∃ b : ↥(rotationAxes G), Nat.card (MulAction.stabilizer (↥G) b) = x) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
                                                                        
  have hcard : Nat.card (↥G) = 60 := card_eq_sixty_of_stabilizer_cardMultiset G m hclass heq
                                                                                           
  obtain ⟨φ, hφinj⟩ := exists_injective_hom_of_stabilizer_cardMultiset G m hclass hcard hpole
                                                                                 
  let H := φ.range
  have hGH : ↥G ≃* ↥H := MonoidHom.ofInjective hφinj
  have hHcard : Nat.card (↥H) = 60 := by rw [← Nat.card_congr hGH.toEquiv, hcard]
  have hindex : H.index = 2 := by
    have hmul : H.index * Nat.card (↥H) = Nat.card (Equiv.Perm (Fin 5)) := Subgroup.index_mul_card H
    have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by rw [Nat.card_perm, Nat.card_fin]; decide
    rw [hHcard, hperm] at hmul
    omega
  have hHeq : H = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨hGH.trans (MulEquiv.subgroupCongr hHeq)⟩

                                                                                      
                                                                                           
                                                                                        
                                                                                       
                                                                                               
                                                                              
                                                                                                
                                                                         
/-- Every finite displayed rotation subgroup belongs to one of the listed group classes. -/
theorem finiteRotationGroupClassification
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] :
    IsCyclic G ∨
    (∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
                                                                                           
  by_cases hn : 2 ≤ Nat.card (↥G)
  · obtain ⟨m, hm2, _hmdvd, heq, hclass, hpole⟩ := exists_stabilizer_cardMultiset G hn
    rcases hclass with h | ⟨k, hnk, h⟩ | h | h | h
    ·                           
      exact Or.inl (isCyclic_of_stabilizer_cardMultiset_eq_pair G m h hpole)
    ·                                                                                             
      have hk : 2 ≤ k := hm2 k (by rw [h]; simp)
      exact Or.inr (Or.inl ⟨k, mulEquiv_dihedral_of_stabilizer_cardMultiset G k hk hnk (h ▸ hpole)⟩)
    ·                                          
      exact Or.inr (Or.inr (Or.inl (mulEquiv_alternatingGroupFinFour_of_stabilizer_cardMultiset G m h heq hpole)))
    ·                                         
      exact Or.inr (Or.inr (Or.inr (Or.inl (mulEquiv_permFinFour_of_stabilizer_cardMultiset G m h heq hpole))))
    ·                                          
      exact Or.inr (Or.inr (Or.inr (Or.inr (mulEquiv_alternatingGroupFinFive_of_stabilizer_cardMultiset G m h heq hpole))))
  ·                                                                                         
    have h1 : Nat.card (↥G) = 1 := by
      have hpos : 0 < Nat.card (↥G) := Nat.card_pos
      omega
    have : Subsingleton (↥G) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Or.inl (isCyclic_of_subsingleton)

                                                                                              
                                                                                            
                       

                                                                                  
/-- The displayed finite rotation subgroup belongs to one of the listed group classes. -/
@[source_ref "Chapter4/Problem4.12.8" (role := primary)]
theorem finiteRotationGroupClassification_011800
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] :
    IsCyclic G ∨
    (∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 5)) :=
  finiteRotationGroupClassification G

                                                                                           
                                                                                            
                                                                                          
                                                                             
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011822
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (hker : ∀ A : specialUnitaryGroup (Fin 2) ℂ,
      A ∈ h.ker ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
        (A : Matrix (Fin 2) (Fin 2) ℂ) = -1))
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H] :
    ((∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) →
        Nat.card H = 2 * Nat.card (H.map h)) ∧
    ((∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) →
        Nat.card H = Nat.card (H.map h)) := by
                         
  set h' : H →* specialOrthogonalGroup (Fin 3) ℝ := h.comp H.subtype with hh'
                                                               
  have hrange : h'.range = H.map h := by
    rw [hh', MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
                                                                                        
  have hinj : ∀ a b : H,
      ((a : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((b : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) → a = b := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
                                                                                     
  have hmem : ∀ x : H, x ∈ h'.ker ↔
      ((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
      ((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    intro x
    rw [MonoidHom.mem_ker, hh', MonoidHom.comp_apply, Subgroup.coe_subtype,
      ← MonoidHom.mem_ker, hker]
                                              
  have h1mat : (((1 : H) : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
                                                              
  have key1 : ∀ y : H,
      ((y : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 → y = 1 := by
    intro y hy
    apply hinj
    rw [hy]
    exact h1mat.symm
                                          
  have hne : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
    intro he
    have h00 := congrFun (congrFun he 0) 0
    rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    norm_num at h00
                                                                      
  have hcount : Nat.card H = Nat.card (H.map h) * Nat.card h'.ker := by
    have hq : Nat.card (H ⧸ h'.ker) = Nat.card (H.map h) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange h').toEquiv, hrange]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h'.ker, hq]
  refine ⟨?_, ?_⟩
  ·                                                                               
    rintro ⟨A₀, hA₀H, hA₀⟩
    let g : H := ⟨A₀, hA₀H⟩
    have hg_mat : ((g : specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = -1 := hA₀
    have hgker : g ∈ h'.ker := (hmem g).mpr (Or.inr hg_mat)
                                                        
    have keyg : ∀ y : H,
        ((y : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 → y = g := by
      intro y hy
      apply hinj
      rw [hy]
      exact hg_mat.symm
    have hcard : Nat.card h'.ker = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨⟨1, (h'.ker).one_mem⟩, ⟨g, hgker⟩, ?_, ?_⟩
      · intro he
        have h1g : (1 : H) = g := congrArg Subtype.val he
        have e1 : (((1 : H) : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) =
            ((g : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by rw [h1g]
        rw [h1mat, hg_mat] at e1
        exact hne e1
      · rw [Set.eq_univ_iff_forall]
        rintro ⟨y, hyk⟩
        have hy2 := (hmem y).mp hyk
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hy2 with hy1 | hy1
        · exact Or.inl (Subtype.ext (key1 y hy1))
        · exact Or.inr (Subtype.ext (keyg y hy1))
    rw [hcount, hcard, mul_comm]
  ·                                                             
    intro hno
    have hbot : h'.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rcases (hmem x).mp hx with h1 | h1
      · exact key1 x h1
      · exact absurd h1 (hno (x : specialUnitaryGroup (Fin 2) ℂ) x.2)
    rw [hcount, hbot, Subgroup.card_bot, mul_one]

   
                                                             

                                                                                          
                                                                                            
                                                                                             
                                                              

                                                                                         
                                                                                               
                                                                                          
                                                                                            
                                                                   

                                                                
                                                    
                                              
                                             
                                               
  

                                                                                          
                                                                                          
                                                                                             
                                                      
/-- The image of the displayed finite subgroup belongs to one of the listed group classes. -/
theorem finiteImageSubgroupClassification
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H] :
    IsCyclic (H.map h) ∨
    (∃ n : ℕ, Nonempty ((H.map h) ≃* DihedralGroup n)) ∨
    Nonempty ((H.map h) ≃* alternatingGroup (Fin 4)) ∨
    Nonempty ((H.map h) ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty ((H.map h) ≃* alternatingGroup (Fin 5)) := by
  haveI : Finite (H.map h) :=
    Finite.of_surjective (fun x : H => (⟨h x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : H.map h))
      (by rintro ⟨y, hy⟩; obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy; exact ⟨⟨x, hx⟩, rfl⟩)
  exact finiteRotationGroupClassification_011800 (H.map h)

                                                                                             
                                                                                            
                                                                               
                                       
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011825
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (hker : ∀ A : specialUnitaryGroup (Fin 2) ℂ,
      A ∈ h.ker ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
        (A : Matrix (Fin 2) (Fin 2) ℂ) = -1))
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ))
    (hneg : ∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    H = Subgroup.comap h (H.map h) := by
  obtain ⟨A₀, hA₀H, hA₀⟩ := hneg
                                                                                               
  have hkerle : h.ker ≤ H := by
    intro x hx
    rcases (hker x).mp hx with h1 | h1
    ·                                 
      have hx1 : x = 1 :=
        Subtype.ext (h1.trans (by simp : (1 : Matrix (Fin 2) (Fin 2) ℂ) =
          ((1 : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))
      rw [hx1]; exact H.one_mem
    ·                                   
      have hxA₀ : x = A₀ := Subtype.ext (h1.trans hA₀.symm)
      rw [hxA₀]; exact hA₀H
  exact (Subgroup.comap_map_eq_self hkerle).symm

                                                                                            
                                                                                
                                                                                        
                                                                              
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011832
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (hker : ∀ A : specialUnitaryGroup (Fin 2) ℂ,
      A ∈ h.ker ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
        (A : Matrix (Fin 2) (Fin 2) ℂ) = -1))
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ))
    (hno : ∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) :
    Nonempty ((H : Type _) ≃* H.map h) := by
  set h' : H →* specialOrthogonalGroup (Fin 3) ℝ := h.comp H.subtype with hh'
                                                           
  have hrange : h'.range = H.map h := by
    rw [hh', MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
                                                                                       
  have hinj : Function.Injective h' := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxmem : (x : specialUnitaryGroup (Fin 2) ℂ) ∈ h.ker := by
      rw [MonoidHom.mem_ker]
      have := MonoidHom.mem_ker.mp hx
      rwa [hh', MonoidHom.comp_apply, Subgroup.coe_subtype] at this
    rcases (hker _).mp hxmem with h1 | h1
    · exact Subtype.ext (Subtype.ext (h1.trans (by simp)))
    · exact absurd h1 (hno (x : specialUnitaryGroup (Fin 2) ℂ) x.2)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

                                                                                           
                                                                                               
                                                                                              

                                                                                           
              
                                                                                             
                                                                                   
                                                                              
                                                                                             
                                                    

                                                                                   
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011821
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H] :
    ∃ h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ,
      Function.Surjective h ∧
      (∀ A : specialUnitaryGroup (Fin 2) ℂ, A ∈ h.ker ↔
        ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1)) ∧
      (IsCyclic (H.map h) ∨
        (∃ n : ℕ, Nonempty ((H.map h) ≃* DihedralGroup n)) ∨
        Nonempty ((H.map h) ≃* alternatingGroup (Fin 4)) ∨
        Nonempty ((H.map h) ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty ((H.map h) ≃* alternatingGroup (Fin 5))) ∧
      ((∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) →
        H = Subgroup.comap h (H.map h) ∧ Nat.card H = 2 * Nat.card (H.map h)) ∧
      ((∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) →
        Nonempty ((H : Type _) ≃* H.map h) ∧ Nat.card H = Nat.card (H.map h)) := by
  obtain ⟨h, hsurj, hker⟩ := RepresentationTheory.QuaternionRotationMaps.Auxiliary011486
  refine ⟨h, hsurj, hker, finiteImageSubgroupClassification h H, ?_, ?_⟩
  · intro hneg
    exact ⟨Auxiliary011825 h hker H hneg,
      (Auxiliary011822 h hker H).1 hneg⟩
  · intro hno
    exact ⟨Auxiliary011832 h hker H hno,
      (Auxiliary011822 h hker H).2 hno⟩

   
                                                        

                                                                                              
                                                                                             
                                                                                               
                                                                                            
                                   

                                                            
                                      
                                                                                            
                                                                              

                                                                                             
                                                                                              
                                                                                         
                    
  

                                                                                         

                                                                                      
                                                                                          
                                                                                           
                                                                                             
                                                                                         
                                                                              
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011833 (A : specialUnitaryGroup (Fin 2) ℂ) (hA : A * A = 1) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := (A : Matrix (Fin 2) (Fin 2) ℂ) with hMdef
  have hMM : M * M = 1 := by
    have h := congrArg (fun X : specialUnitaryGroup (Fin 2) ℂ =>
      (X : Matrix (Fin 2) (Fin 2) ℂ)) hA
    simpa [hMdef] using h
  have hdet : M.det = 1 := (mem_specialUnitaryGroup_iff.mp A.2).2
  rw [Matrix.det_fin_two] at hdet
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have h := congrFun (congrFun hMM 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    have h := congrFun (congrFun hMM 0) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
      at h
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    have h := congrFun (congrFun hMM 1) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      at h
  have htr : M 0 0 + M 1 1 ≠ 0 := by
    intro h
    have key : (0 : ℂ) = 2 := by linear_combination hdet + e00 - M 0 0 * h
    norm_num at key
  have hb : M 0 1 = 0 := by
    rcases mul_eq_zero.mp (show M 0 1 * (M 0 0 + M 1 1) = 0 by linear_combination e01) with h | h
    · exact h
    · exact absurd h htr
  have hc : M 1 0 = 0 := by
    rcases mul_eq_zero.mp (show M 1 0 * (M 0 0 + M 1 1) = 0 by linear_combination e10) with h | h
    · exact h
    · exact absurd h htr
  have ha2 : M 0 0 * M 0 0 = 1 := by rw [hb] at e00; linear_combination e00
  have had : M 0 0 * M 1 1 = 1 := by rw [hb, hc] at hdet; linear_combination hdet
  have hane : M 0 0 ≠ 0 := by
    intro h
    rw [h] at ha2
    norm_num at ha2
  have hda : M 1 1 = M 0 0 := by
    rcases mul_eq_zero.mp (show M 0 0 * (M 1 1 - M 0 0) = 0 by
      linear_combination had - ha2) with h | h
    · exact absurd h hane
    · exact sub_eq_zero.mp h
  rcases mul_eq_zero.mp (show (M 0 0 - 1) * (M 0 0 + 1) = 0 by linear_combination ha2) with h | h
  · left
    have ha : M 0 0 = 1 := by linear_combination h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, ha]
  · right
    have ha : M 0 0 = -1 := by linear_combination h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, ha]

                                                      

                                            
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011714 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
  intro he
  have h00 := congrFun (congrFun he 0) 0
  rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  norm_num at h00

                                                                                            
/-- Two subgroup elements with equal ambient values are equal. -/
theorem ext_011837 {H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} {x y : H}
    (hxy : ((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = ((y : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : x = y :=
  Subtype.ext (Subtype.ext hxy)

                                                                                       
/-- Coercion of a subgroup product agrees with multiplication of the coerced elements. -/
theorem coe_mul {H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} (x y : H) :
    (((x * y : H) : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = ((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((y : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

                                                                                  
/-- Coercion of the subgroup identity agrees with the ambient identity. -/
theorem coe_one {H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} :
    (((1 : H) : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl

                                        

                                                                                          
                                                                                              
                                            
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011838
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H]
    (hno : ∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) :
    ¬ (2 ∣ Nat.card H) := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have hxx : ((x : specialUnitaryGroup (Fin 2) ℂ)) * ((x : specialUnitaryGroup (Fin 2) ℂ)) = 1 := by
    have h1 : x * x = 1 := by
      have hp := pow_orderOf_eq_one x
      rw [hx, pow_two] at hp
      exact hp
    have h2 := congrArg (fun y : H => (y : specialUnitaryGroup (Fin 2) ℂ)) h1
    simpa using h2
  rcases Auxiliary011833 _ hxx with h | h
  · have : x = 1 := ext_011837 (by rw [h, coe_one])
    rw [this, orderOf_one] at hx
    norm_num at hx
  · exact hno (x : specialUnitaryGroup (Fin 2) ℂ) x.2 h

                                                                                       
/-- An element whose square is the subgroup identity has ambient square equal to one. -/
theorem coe_sq_eq_one {H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} {x : H}
    (hx : x * x = 1) :
    ((x : specialUnitaryGroup (Fin 2) ℂ)) * ((x : specialUnitaryGroup (Fin 2) ℂ)) = 1 := by
  have h := congrArg (fun y : H => (y : specialUnitaryGroup (Fin 2) ℂ)) hx
  simpa using h

                                     

                                                                                           
                      

                                                                                              
                                                                                          
                                                                               
                                                                                          
                                                                           
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011831
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H]
    (hno : ∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) :
    IsCyclic H := by
  obtain ⟨h, _hsurj, hker⟩ := RepresentationTheory.QuaternionRotationMaps.Auxiliary011486
  obtain ⟨e⟩ := Auxiliary011832 h hker H hno
  have hcard : Nat.card H = Nat.card (H.map h) :=
    (Auxiliary011822 h hker H).2 hno
  have h2 := Auxiliary011838 H hno
  rcases finiteImageSubgroupClassification h H with hcy | ⟨n, hd⟩ | ha4 | hs4 | ha5
  · haveI := hcy
    exact isCyclic_of_surjective e.symm e.symm.surjective
  · obtain ⟨ed⟩ := hd
    refine absurd ?_ h2
    rw [hcard, Nat.card_congr ed.toEquiv, DihedralGroup.nat_card]
    exact ⟨n, rfl⟩
  · obtain ⟨ea⟩ := ha4
    refine absurd ?_ h2
    rw [hcard, Nat.card_congr ea.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · obtain ⟨es⟩ := hs4
    refine absurd ?_ h2
    rw [hcard, Nat.card_congr es.toEquiv, Nat.card_perm]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · obtain ⟨ei⟩ := ha5
    refine absurd ?_ h2
    rw [hcard, Nat.card_congr ei.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

                                          

                                                                                             
                                                                                             
                                        

                                                                                              
                                   

                                                           
                                                                                        
                                                                                        
                                                                                             
                                                         

                                                                                              
                                                                           
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011827
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (hker : ∀ A : specialUnitaryGroup (Fin 2) ℂ,
      A ∈ h.ker ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
        (A : Matrix (Fin 2) (Fin 2) ℂ) = -1))
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H]
    (hneg : ∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (hcyc : IsCyclic (H.map h)) :
    IsCyclic H := by
  haveI : Finite (H.map h) :=
    Finite.of_surjective (fun x : H => (⟨h x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : H.map h))
      (by rintro ⟨y, hy⟩; obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy; exact ⟨⟨x, hx⟩, rfl⟩)
  haveI := hcyc
  have hcardH : Nat.card H = 2 * Nat.card (H.map h) :=
    (Auxiliary011822 h hker H).1 hneg
  obtain ⟨A₀, hA₀H, hA₀⟩ := hneg
                                                           
  let ε : H := ⟨A₀, hA₀H⟩
  have hεmat : ((ε : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := hA₀
  have hε2 : ε * ε = 1 := by
    refine ext_011837 ?_
    rw [coe_mul, coe_one, hεmat]
    simp
  have hεne : ε ≠ 1 := by
    intro hcon
    have hmat : ((ε : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [hcon, coe_one]
    rw [hεmat] at hmat
    exact Auxiliary011714 hmat.symm
  have hεord : orderOf ε = 2 := orderOf_eq_prime (by rw [pow_two]; exact hε2) hεne
  have hεcomm : ∀ x : H, Commute x ε := by
    intro x
    refine ext_011837 ?_
    rw [coe_mul, coe_mul, hεmat]
    simp
                                                                                   
  let f : H →* (H.map h) :=
    (h.comp H.subtype).codRestrict (H.map h) (fun x => Subgroup.mem_map_of_mem h x.2)
  have hfval : ∀ x : H, ((f x : H.map h) : specialOrthogonalGroup (Fin 3) ℝ)
      = h (x : specialUnitaryGroup (Fin 2) ℂ) := fun _ => rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : ∀ x : H, f x = 1 ↔
      (((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
       ((x : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
    intro x
    rw [← hker, MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [← hfval x, hx]
      rfl
    · intro hx
      exact Subtype.ext (by rw [hfval x, hx]; rfl)
                                                      
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (H.map h))
  have hγord : orderOf γ = Nat.card (H.map h) := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨g, hg⟩ := hfsurj γ
  set n : ℕ := Nat.card (H.map h) with hn
  have hnpos : 0 < n := Nat.card_pos
  have hndvd : n ∣ orderOf g := by
    rw [← hγord]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← hg, ← map_pow, pow_orderOf_eq_one, map_one]
  have hgn : f (g ^ n) = 1 := by
    rw [map_pow, hg, ← hγord, pow_orderOf_eq_one]
  rcases (hfker _).mp hgn with hgn1 | hgnε
  ·                                                                  
    have hgn1' : g ^ n = 1 := ext_011837 (by rw [hgn1, coe_one])
    have hgord : orderOf g = n :=
      Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hgn1') hndvd
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with he | ho
      · exfalso
        obtain ⟨m, hm⟩ := he
        have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        have hsq : g ^ m * g ^ m = 1 := by rw [← pow_add, ← hm, hgn1']
        have hne1 : g ^ m ≠ 1 := by
          intro hcon
          have := orderOf_dvd_of_pow_eq_one hcon
          rw [hgord] at this
          exact absurd (Nat.le_of_dvd hmpos this) (by omega)
        rcases Auxiliary011833 _ (coe_sq_eq_one hsq) with hmat | hmat
        · exact hne1 (ext_011837 (by rw [hmat, coe_one]))
        · have hfm : f (g ^ m) = 1 := (hfker _).mpr (Or.inr hmat)
          rw [map_pow, hg] at hfm
          have := orderOf_dvd_of_pow_eq_one hfm
          rw [hγord] at this
          exact absurd (Nat.le_of_dvd hmpos this) (by omega)
      · exact ho
    refine isCyclic_of_orderOf_eq_card (g * ε) ?_
    rw [(hεcomm g).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hgord, hεord]; exact Nat.coprime_two_right.mpr hodd), hgord, hεord, hcardH]
    ring
  ·                                                      
    have hgnε' : g ^ n = ε := ext_011837 (by rw [hgnε, hεmat])
    have hdvd2 : orderOf g ∣ 2 * n := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [mul_comm, pow_mul, hgnε', pow_two, hε2]
    obtain ⟨k, hk⟩ := hndvd
    have hk2 : k ∣ 2 := by
      rw [hk, mul_comm 2 n] at hdvd2
      exact (Nat.mul_dvd_mul_iff_left hnpos).mp hdvd2
    have hkne1 : k ≠ 1 := by
      intro hcon
      rw [hcon, mul_one] at hk
      have : g ^ n = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
      exact hεne (hgnε' ▸ this)
    have hkeq : k = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
      · exact absurd h1 hkne1
      · exact h2
    refine isCyclic_of_orderOf_eq_card g ?_
    rw [hk, hkeq, hcardH]
    ring


                         

                                                                                             
                                                                                            
                                                                           

                                                   
                                           
                                          
                                            

                                                                                            
                                                                                          
                                                                                       
                                                                                           
/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.8" (role := supporting)]
theorem Auxiliary011820
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H] :
    IsCyclic H ∨
    ∃ h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ,
      Function.Surjective h ∧
      (∀ A : specialUnitaryGroup (Fin 2) ℂ, A ∈ h.ker ↔
        ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1)) ∧
      H = Subgroup.comap h (H.map h) ∧
      ((∃ n : ℕ, Nonempty ((H.map h) ≃* DihedralGroup n) ∧ Nat.card H = 4 * n) ∨
       (Nonempty ((H.map h) ≃* alternatingGroup (Fin 4)) ∧ Nat.card H = 24) ∨
       (Nonempty ((H.map h) ≃* Equiv.Perm (Fin 4)) ∧ Nat.card H = 48) ∨
       (Nonempty ((H.map h) ≃* alternatingGroup (Fin 5)) ∧ Nat.card H = 120)) := by
  by_cases hneg : ∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1
  · obtain ⟨h, hsurj, hker⟩ := RepresentationTheory.QuaternionRotationMaps.Auxiliary011486
    have hcard2 : Nat.card H = 2 * Nat.card (H.map h) :=
      (Auxiliary011822 h hker H).1 hneg
    have hpre : H = Subgroup.comap h (H.map h) := Auxiliary011825 h hker H hneg
    rcases finiteImageSubgroupClassification h H with hcy | ⟨n, hd⟩ | ha4 | hs4 | ha5
    · exact Or.inl (Auxiliary011827 h hker H hneg hcy)
    · obtain ⟨ed⟩ := hd
      refine Or.inr ⟨h, hsurj, hker, hpre, Or.inl ⟨n, ⟨ed⟩, ?_⟩⟩
      rw [hcard2, Nat.card_congr ed.toEquiv, DihedralGroup.nat_card]
      ring
    · obtain ⟨ea⟩ := ha4
      refine Or.inr ⟨h, hsurj, hker, hpre, Or.inr (Or.inl ⟨⟨ea⟩, ?_⟩)⟩
      rw [hcard2, Nat.card_congr ea.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · obtain ⟨es⟩ := hs4
      refine Or.inr ⟨h, hsurj, hker, hpre, Or.inr (Or.inr (Or.inl ⟨⟨es⟩, ?_⟩))⟩
      rw [hcard2, Nat.card_congr es.toEquiv, Nat.card_perm]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · obtain ⟨ei⟩ := ha5
      refine Or.inr ⟨h, hsurj, hker, hpre, Or.inr (Or.inr (Or.inr ⟨⟨ei⟩, ?_⟩))⟩
      rw [hcard2, Nat.card_congr ei.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
  · push Not at hneg
    exact Or.inl (Auxiliary011831 H hneg)

end RepresentationTheory.FiniteRotationGroups
