/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Group.CharacterDuality
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Alignment.Attribute

   
                                                                             

                                                                                              
                                                                                 
                                                                                         
                                                                             

                                                                                             
                                                                            

                

                                                                                           
                                                                                             
                                                                                            

                                       

                                                                                      
                                                                                              
                                                                                                
                                      
                                                                                             
                                                                                   
                                                                                  
                                                                                         
                                                                                           
                                                                                  
                     

                                                                                 
                                                                                      
  

noncomputable section

namespace RepresentationTheory.AffineGroupRepresentations

open _root_.CategoryTheory

variable {K : Type*} [Field K]

                                                                                            
                             
/-- The type of transformations over a field specified by the displayed signature. -/
@[ext]
structure AffineGroup (K : Type*) [Field K] where
  /-- The construction specified by the displayed formal type. -/
  linearPart : Kˣ
  /-- The construction specified by the displayed formal type. -/
  translationPart : K

namespace AffineGroup

/-- The construction specified by the displayed formal type. -/
instance instMul : Mul (AffineGroup K) :=
  ⟨fun g h => ⟨g.linearPart * h.linearPart, (g.linearPart : K) * h.translationPart + g.translationPart⟩⟩

/-- The construction specified by the displayed formal type. -/
instance instOne : One (AffineGroup K) := ⟨⟨1, 0⟩⟩

/-- The construction specified by the displayed formal type. -/
instance instInv : Inv (AffineGroup K) :=
  ⟨fun g => ⟨g.linearPart⁻¹, -((g.linearPart⁻¹ : K) * g.translationPart)⟩⟩

/-- The equality displayed in the formal statement. -/
@[simp] theorem linearPart_mul (g h : AffineGroup K) : (g * h).linearPart = g.linearPart * h.linearPart := rfl
/-- The equality displayed in the formal statement. -/
@[simp] theorem translationPart_mul (g h : AffineGroup K) : (g * h).translationPart = (g.linearPart : K) * h.translationPart + g.translationPart := rfl
/-- The equality displayed in the formal statement. -/
@[simp] theorem linearPart_one : (1 : AffineGroup K).linearPart = 1 := rfl
/-- The equality displayed in the formal statement. -/
@[simp] theorem translationPart_one : (1 : AffineGroup K).translationPart = 0 := rfl
/-- The equality displayed in the formal statement. -/
@[simp] theorem linearPart_inv (g : AffineGroup K) : g⁻¹.linearPart = g.linearPart⁻¹ := rfl
/-- The equality displayed in the formal statement. -/
@[simp] theorem translationPart_inv (g : AffineGroup K) : g⁻¹.translationPart = -((g.linearPart⁻¹ : K) * g.translationPart) := rfl

/-- The construction specified by the displayed formal type. -/
instance instGroup : Group (AffineGroup K) where
  mul_assoc g h k := by
    ext
    · simp [mul_assoc]
    · simp; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp
    · simp

                                                              
/-- The construction specified by the displayed formal type. -/
def act (g : AffineGroup K) (x : K) : K := (g.linearPart : K) * x + g.translationPart

/-- The equality displayed in the formal statement. -/
@[simp] theorem one_act (x : K) : act (1 : AffineGroup K) x = x := by simp [act]

/-- The equality displayed in the formal statement. -/
theorem mul_act (g h : AffineGroup K) (x : K) : act (g * h) x = act g (act h x) := by
  simp only [act, linearPart_mul, translationPart_mul, Units.val_mul]; ring

/-- The equality displayed in the formal statement. -/
@[simp] theorem act_inv (g : AffineGroup K) (x : K) : act g (act g⁻¹ x) = x := by
  rw [← mul_act, mul_inv_cancel, one_act]

/-- The equality displayed in the formal statement. -/
@[simp] theorem inv_act (g : AffineGroup K) (x : K) : act g⁻¹ (act g x) = x := by
  rw [← mul_act, inv_mul_cancel, one_act]

                                                               
/-- The equivalence specified by the displayed formal signature. -/
def actionEquiv (g : AffineGroup K) : K ≃ K where
  toFun := act g
  invFun := act g⁻¹
  left_inv := inv_act g
  right_inv := act_inv g

/-- The equivalence of the two propositions displayed in the formal type. -/
theorem inv_act_eq_iff (g : AffineGroup K) (x p : K) : act g⁻¹ x = p ↔ x = act g p := by
  constructor
  · intro h; rw [← h]; exact (act_inv g x).symm
  · intro h; rw [h]; exact inv_act g p

                                                                      
/-- The equivalence specified by the displayed formal signature. -/
def equivUnitsProd (K : Type*) [Field K] : AffineGroup K ≃ Kˣ × K where
  toFun g := (g.linearPart, g.translationPart)
  invFun t := ⟨t.1, t.2⟩
  left_inv g := by cases g; rfl
  right_inv t := by rfl

instance [DecidableEq K] : DecidableEq (AffineGroup K) := (equivUnitsProd K).decidableEq

/-- The construction specified by the displayed formal type. -/
instance instFintype [Fintype K] [DecidableEq K] : Fintype (AffineGroup K) := Fintype.ofEquiv _ (equivUnitsProd K).symm

                                           
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem card [Fintype K] [DecidableEq K] :
    Fintype.card (AffineGroup K) = Fintype.card K * (Fintype.card K - 1) := by
  rw [Fintype.card_congr (equivUnitsProd K), Fintype.card_prod, Fintype.card_units, mul_comm]

end AffineGroup

open AffineGroup

                                                                                  
                                                                        

                                                                                         
                                                                                         
                                                                                       
                                                                                           
           
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.6" (role := supporting)]
theorem cardinalityFormula_011354 [Fintype K] (hK : 3 ≤ Fintype.card K) :
    Nat.card (AffineGroup K →* ℂˣ) = Fintype.card K - 1 := by
  classical
                                                                                 
  let projA : AffineGroup K →* Kˣ :=
    { toFun := fun g => g.linearPart, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let s : Kˣ →* AffineGroup K :=
    { toFun := fun a => ⟨a, 0⟩
      map_one' := rfl
      map_mul' := fun a a' => by ext <;> simp }
                                                            
  have key : ∀ u v : ℂˣ, u * v * u⁻¹ * v⁻¹ = 1 := fun u v => by
    rw [mul_comm u v]; group
                                                                                    
  have htrans : ∀ (φ : AffineGroup K →* ℂˣ) (c : K), φ (⟨1, c⟩ : AffineGroup K) = 1 := by
    intro φ c
                                                               
    have hcard : 2 ≤ Fintype.card Kˣ := by rw [Fintype.card_units]; omega
    have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
    have hu : ((a₀ : K) - 1) ≠ 0 := sub_ne_zero.mpr fun h => ha₀ (Units.ext h)
                                                                  
    have hkey : ∀ (a : Kˣ) (c' : K), φ (⟨1, (a : K) * c' - c'⟩ : AffineGroup K) = 1 := by
      intro a c'
      have ha : (a : K) ≠ 0 := Units.ne_zero a
      have hcomm : (⟨1, (a : K) * c' - c'⟩ : AffineGroup K) =
          ⟨a, 0⟩ * ⟨1, c'⟩ * ⟨a, 0⟩⁻¹ * ⟨1, c'⟩⁻¹ := by
        ext
        · simp
        · simp only [translationPart_mul, linearPart_mul, linearPart_inv, translationPart_inv, Units.val_mul,
            Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_zero, add_zero, mul_one,
            mul_neg, one_mul]
          field_simp
          ring
      rw [hcomm]
      simp only [map_mul, map_inv]
      exact key _ _
                                                          
    have h := hkey a₀ (((a₀ : K) - 1)⁻¹ * c)
    have hval : (a₀ : K) * (((a₀ : K) - 1)⁻¹ * c) - ((a₀ : K) - 1)⁻¹ * c = c := by
      field_simp
    rwa [hval] at h
                                                                         
  let E : (AffineGroup K →* ℂˣ) ≃ (Kˣ →* ℂˣ) :=
    { toFun := fun φ => φ.comp s
      invFun := fun χ => χ.comp projA
      left_inv := fun φ => MonoidHom.ext fun g => by
                                                                  
        change φ (⟨g.linearPart, 0⟩ : AffineGroup K) = φ g
        have hg : g = (⟨g.linearPart, 0⟩ : AffineGroup K) * ⟨1, (↑g.linearPart)⁻¹ * g.translationPart⟩ := by
          ext
          · simp
          · simp
        conv_rhs => rw [hg]
        rw [map_mul, htrans φ _, mul_one]
      right_inv := fun χ => MonoidHom.ext fun a => rfl }
  rw [Nat.card_congr E]
                                                                                                   
  haveI : NeZero ((Monoid.exponent Kˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Kˣ ℂ, Nat.card_eq_fintype_card,
    Fintype.card_units]

                                                                      
/-- The submodule specified by the displayed formal signature. -/
def zeroSumSubmodule (K : Type*) [Fintype K] : Submodule ℂ (K → ℂ) where
  carrier := {f | ∑ x, f x = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hf, mul_zero]

                                                                                            
                                     
/-- A membership statement for the displayed set, submodule, or subgroup. -/
theorem membershipCharacterization_011450 [Fintype K]
    (ρ : Representation ℂ (AffineGroup K) (K → ℂ))
    (hρ : ∀ (g : AffineGroup K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x)) :
    ∀ (g : AffineGroup K), ∀ f ∈ zeroSumSubmodule K, ρ g f ∈ zeroSumSubmodule K := by
  intro g f hf
  simp only [zeroSumSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at *
  calc ∑ x, (ρ g f) x = ∑ x, f (act g⁻¹ x) := by simp_rw [hρ]
    _ = ∑ x, f (actionEquiv g⁻¹ x) := rfl
    _ = ∑ x, f x := Equiv.sum_comp (actionEquiv g⁻¹) f
    _ = 0 := hf

                                                             
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011444 [Fintype K] :
    Module.finrank ℂ (zeroSumSubmodule K) = Fintype.card K - 1 := by
  classical
                                                                          
  let L : (K → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ x, f x
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.mul_sum] }
  have hker : LinearMap.ker L = zeroSumSubmodule K := by
    ext f
    simp only [LinearMap.mem_ker, L, LinearMap.coe_mk, AddHom.coe_mk, zeroSumSubmodule,
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  have hsurj : Function.Surjective L := by
    intro c
    refine ⟨fun x => if x = 0 then c else 0, ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_ite_eq' Finset.univ (0 : K) (fun _ => c)]
    simp
  have hrange : Module.finrank ℂ (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [Module.finrank_self]
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, hrange, Module.finrank_pi ℂ] at hnull
  omega

                                                                                          
                                                                                        
/-- The construction specified by the displayed formal type. -/
def deltaKernel (K : Type*) [Fintype K] [DecidableEq K] (t : K) : K → ℂ :=
  (Fintype.card K : ℂ) • Pi.single t (1 : ℂ) - 1

                                                                                             
/-- The equality displayed in the formal statement. -/
theorem valueFormula_011431 [Fintype K] [DecidableEq K] (φ : K → ℂ) :
    ∑ a : Kˣ, φ (a : K) = (∑ y : K, φ y) - φ 0 := by
  classical
  let e : Kˣ ≃ {y : K // y ≠ 0} :=
    { toFun := fun u => ⟨(u : K), u.ne_zero⟩
      invFun := fun y => Units.mk0 y.1 y.2
      left_inv := fun u => by ext; simp
      right_inv := fun y => by ext; simp }
  have h1 : ∑ a : Kˣ, φ (a : K) = ∑ y : {y : K // y ≠ 0}, φ (y : K) :=
    Fintype.sum_equiv e _ _ (fun a => rfl)
  have hmem : ∀ x : K, x ∈ Finset.univ.erase (0 : K) ↔ x ≠ 0 := by
    intro x; simp [Finset.mem_erase]
  rw [h1, ← Finset.sum_subtype _ hmem φ, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : K))]

                                                                          
/-- The equality displayed in the formal statement. -/
theorem valueFormula_011387 [DecidableEq K]
    (ρ : Representation ℂ (AffineGroup K) (K → ℂ))
    (hρ : ∀ (g : AffineGroup K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : AffineGroup K) (p : K) :
    ρ g (Pi.single p (1 : ℂ)) = Pi.single (act g p) (1 : ℂ) := by
  funext x
  rw [hρ, Pi.single_apply, Pi.single_apply]
  simp only [inv_act_eq_iff]

                                                  
/-- The equality displayed in the formal statement. -/
theorem valueFormula_011386
    (ρ : Representation ℂ (AffineGroup K) (K → ℂ))
    (hρ : ∀ (g : AffineGroup K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : AffineGroup K) :
    ρ g (1 : K → ℂ) = 1 := by
  funext x; rw [hρ]; rfl

                                                                     
/-- The equality displayed in the formal statement. -/
theorem valueFormula_011389 [Fintype K] [DecidableEq K]
    (ρ : Representation ℂ (AffineGroup K) (K → ℂ))
    (hρ : ∀ (g : AffineGroup K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : AffineGroup K) (t : K) :
    ρ g (deltaKernel K t) = deltaKernel K (act g t) := by
  unfold deltaKernel
  rw [map_sub, map_smul, valueFormula_011387 ρ hρ, valueFormula_011386 ρ hρ]

                                                                                         
                                                                                      
/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[source_ref "Chapter4/Problem4.12.6" (role := supporting)]
theorem membershipCharacterization_011454 [Fintype K]
    (ρ : Representation ℂ (AffineGroup K) (K → ℂ))
    (hρ : ∀ (g : AffineGroup K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (U : Submodule ℂ (K → ℂ)) (hUle : U ≤ zeroSumSubmodule K)
    (hUinv : ∀ (g : AffineGroup K), ∀ f ∈ U, ρ g f ∈ U) :
    U = ⊥ ∨ U = zeroSumSubmodule K := by
  classical
  rcases eq_or_ne U ⊥ with hU | hU
  · exact Or.inl hU
  refine Or.inr (le_antisymm hUle ?_)
                                                              
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hqne : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
                                                                 
  obtain ⟨f0, hf0U, hf0ne⟩ := (Submodule.ne_bot_iff U).mp hU
  obtain ⟨p, hp⟩ : ∃ p, f0 p ≠ 0 := by
    by_contra h
    exact hf0ne (funext fun x => by simpa using not_exists.mp h x)
                                                                                   
  set g0 : AffineGroup K := ⟨1, -p⟩ with hg0
  set f' : K → ℂ := ρ g0 f0 with hf'def
  have hf'U : f' ∈ U := hUinv g0 f0 hf0U
  have hf'0 : f' 0 = f0 p := by
    rw [hf'def, hρ]; simp [act, hg0]
  have hf'0ne : f' 0 ≠ 0 := by rw [hf'0]; exact hp
  have hf'sum : ∑ x, f' x = 0 := hUle hf'U
                                                               
  set h : K → ℂ := ∑ a : Kˣ, ρ (⟨a, 0⟩ : AffineGroup K) f' with hhdef
  have hhU : h ∈ U := Submodule.sum_mem U (fun a _ => hUinv _ _ hf'U)
                                   
  have hheq : h = (f' 0) • deltaKernel K 0 := by
    funext x
    rw [hhdef, Finset.sum_apply]
    have hval : ∀ a : Kˣ, (ρ (⟨a, 0⟩ : AffineGroup K) f') x = f' ((a : K)⁻¹ * x) := by
      intro a
      rw [hρ]; congr 1
      simp [act, Units.val_inv_eq_inv_val]
    simp_rw [hval]
    by_cases hx : x = 0
    · subst hx
      simp only [mul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_units,
        nsmul_eq_mul, Pi.smul_apply, deltaKernel, Pi.sub_apply, Pi.single_eq_same,
        Pi.one_apply, smul_eq_mul, mul_one]
      rw [Nat.cast_sub hq1, Nat.cast_one]
      ring
    ·                                                                             
      have hxu : x ≠ 0 := hx
      have hreindex : ∑ a : Kˣ, f' ((a : K)⁻¹ * x) = ∑ a : Kˣ, f' (a : K) := by
        apply Fintype.sum_equiv ((Equiv.inv Kˣ).trans (Equiv.mulRight (Units.mk0 x hxu)))
        intro a
        simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
        congr 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [hreindex, valueFormula_011431, hf'sum, zero_sub]
      simp only [Pi.smul_apply, deltaKernel, Pi.sub_apply, Pi.single_apply, if_neg hx,
        Pi.one_apply, smul_eq_mul, mul_zero, zero_sub, mul_neg, mul_one]
                                                                 
  have hspike0U : deltaKernel K 0 ∈ U := by
    have : deltaKernel K 0 = (f' 0)⁻¹ • h := by
      rw [hheq, smul_smul, inv_mul_cancel₀ hf'0ne, one_smul]
    rw [this]; exact U.smul_mem _ hhU
  have hspikeU : ∀ t, deltaKernel K t ∈ U := by
    intro t
    have h1 : ρ (⟨1, t⟩ : AffineGroup K) (deltaKernel K 0) = deltaKernel K t := by
      rw [valueFormula_011389 ρ hρ]; congr 1; simp [act]
    rw [← h1]; exact hUinv _ _ hspike0U
                                                                 
  intro f hf
  have hfsum : ∑ x, f x = 0 := hf
  have hfeq : f = ∑ t : K, (f t / (Fintype.card K : ℂ)) • deltaKernel K t := by
    funext x
    rw [Finset.sum_apply]
    simp_rw [Pi.smul_apply, deltaKernel, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
      Pi.one_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ t : K, f t / (Fintype.card K : ℂ) * ((Fintype.card K : ℂ) *
        (if x = t then (1 : ℂ) else 0)) = f x := by
      have key : ∀ t : K, f t / (Fintype.card K : ℂ) * ((Fintype.card K : ℂ) *
          (if x = t then (1 : ℂ) else 0)) = if x = t then f t else 0 := by
        intro t
        by_cases h : x = t
        · rw [if_pos h, if_pos h, mul_one, div_mul_cancel₀ (f t) hqne]
        · rw [if_neg h, if_neg h, mul_zero, mul_zero]
      simp_rw [key]
      rw [Finset.sum_ite_eq]
      simp
    have e2 : ∑ t : K, f t / (Fintype.card K : ℂ) * 1 = 0 := by
      simp_rw [mul_one, ← Finset.sum_div]
      rw [hfsum, zero_div]
    rw [e1, e2, sub_zero]
  rw [hfeq]
  exact Submodule.sum_mem U (fun t _ => U.smul_mem _ (hspikeU t))

open Module in
                                                                                             
                         
private theorem surj_of_injective_of_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → ℕ) (hf : ∀ j, 0 < f j) (c : ι → Fin n) (hcinj : Function.Injective c)
    (hsum : ∑ i, f (c i) = ∑ j, f j) : Function.Surjective c := by
  classical
  have himg : ∑ j ∈ Finset.image c Finset.univ, f j = ∑ i, f (c i) :=
    Finset.sum_image (fun a _ b _ hab => hcinj hab)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ (Finset.image c Finset.univ))
  rw [himg, hsum] at hsplit
  have hzero : ∑ j ∈ Finset.univ \ Finset.image c Finset.univ, f j = 0 := by omega
  intro j
  have hjmem : j ∈ Finset.image c Finset.univ := by
    by_contra hj
    exact absurd ((Finset.sum_eq_zero_iff.mp hzero) j
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)) (hf j).ne'
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjmem
  exact ⟨i, hi⟩

                                                                                    
                                       
/-- The representation specified by the displayed formal signature. -/
def characterRepresentation (χ : AffineGroup K →* ℂˣ) : Representation ℂ (AffineGroup K) ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

                                                 
/-- A formula for the character or trace of the displayed representation. -/
@[simp] lemma characterFormula_011299 (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (FDRep.of (characterRepresentation χ)).character g = (χ g : ℂ) := by
  have hg : characterRepresentation χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (characterRepresentation χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

                                                                                            
                                              
/-- A simplicity statement for the displayed representation or module. -/
lemma simpleRepresentation_011298 (χ : AffineGroup K →* ℂˣ) :
    IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (characterRepresentation χ).asModule := by
  haveI hℂ : IsSimpleModule ℂ ℂ := inferInstance
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := characterRepresentation χ)).isSimpleOrder_iff]
  haveI : Nontrivial (Subrepresentation (characterRepresentation χ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W'.toSubmodule with h | h
  · left; exact Subrepresentation.toSubmodule_injective h
  · right; exact Subrepresentation.toSubmodule_injective h

                                                                                      
/-- A simplicity statement for the displayed representation or module. -/
lemma simpleRepresentation_011303 (χ : AffineGroup K →* ℂˣ) :
    Simple (FDRep.of (characterRepresentation χ)) :=
  haveI := simpleRepresentation_011298 χ
  RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (characterRepresentation χ)

                                                                                                   
/-- The representation specified by the displayed formal signature. -/
def functionRepresentation : Representation ℂ (AffineGroup K) (K → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (act g⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext x
    simp only [LinearMap.funLeft_apply, inv_one, one_act, Module.End.one_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext x
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev]
    rw [mul_act]

/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011374 (g : AffineGroup K) (f : K → ℂ) (x : K) :
    functionRepresentation g f x = f (act g⁻¹ x) := rfl

                                                                 
/-- The subrepresentation specified by the displayed formal signature. -/
def augmentationSubrepresentation [Fintype K] : Subrepresentation (functionRepresentation (K := K)) where
  toSubmodule := zeroSumSubmodule K
  apply_mem_toSubmodule g v hv := membershipCharacterization_011450 functionRepresentation valueFormula_011374 g v hv

                                                                                     
                                                                                           
                                                                                      
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011266 [Fintype K] (hq : 2 ≤ Fintype.card K) :
    IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (augmentationSubrepresentation (K := K)).toRepresentation.asModule := by
  classical
  haveI hnt0 : Nontrivial ↥(zeroSumSubmodule K) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [cardinalityFormula_011444]; omega
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso
        (ρ := (augmentationSubrepresentation (K := K)).toRepresentation)).isSimpleOrder_iff]
  haveI hntSub : Nontrivial (Subrepresentation (augmentationSubrepresentation (K := K)).toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ↥(zeroSumSubmodule K)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  set U : Submodule ℂ (K → ℂ) := W'.toSubmodule.map (augmentationSubrepresentation (K := K)).toSubmodule.subtype with hUdef
  have hUle : U ≤ zeroSumSubmodule K := by
    rw [hUdef]; rintro x ⟨y, -, rfl⟩; exact y.2
  have hUinv : ∀ (g : AffineGroup K), ∀ f ∈ U, functionRepresentation g f ∈ U := by
    intro g f hf
    rw [hUdef, Submodule.mem_map] at hf ⊢
    obtain ⟨y, hy, rfl⟩ := hf
    exact ⟨(augmentationSubrepresentation (K := K)).toRepresentation g y, W'.apply_mem_toSubmodule g hy, rfl⟩
  rcases membershipCharacterization_011454 functionRepresentation valueFormula_011374 U hUle hUinv with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    have h2 : W'.toSubmodule.map (augmentationSubrepresentation (K := K)).toSubmodule.subtype
        = (⊥ : Submodule ℂ ↥(augmentationSubrepresentation (K := K)).toSubmodule).map (augmentationSubrepresentation (K := K)).toSubmodule.subtype := by
      rw [Submodule.map_bot, ← hUdef]; exact h
    exact Submodule.map_injective_of_injective
      (augmentationSubrepresentation (K := K)).toSubmodule.injective_subtype h2
  · right
    apply Subrepresentation.toSubmodule_injective
    have h2 : W'.toSubmodule.map (augmentationSubrepresentation (K := K)).toSubmodule.subtype
        = (⊤ : Submodule ℂ ↥(augmentationSubrepresentation (K := K)).toSubmodule).map (augmentationSubrepresentation (K := K)).toSubmodule.subtype := by
      rw [Submodule.map_subtype_top, ← hUdef]; exact h
    exact Submodule.map_injective_of_injective
      (augmentationSubrepresentation (K := K)).toSubmodule.injective_subtype h2

                                                                                        
                                                                                          
                                               
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011334 [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (AffineGroup K) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) ρ.asModule) :
    ∃ (U : FDRep ℂ (AffineGroup K)), Simple U ∧ Module.finrank ℂ U = Module.finrank ℂ V := by
  classical
  haveI : NeZero (Nat.card (AffineGroup K) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, card]
    have h2 : 1 < Fintype.card K := Fintype.one_lt_card
    have hne : Fintype.card K * (Fintype.card K - 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    exact_mod_cast hne
  letI M := Representation.asModule ρ
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) M := hρ
  haveI : Module.Finite ℂ M := Module.Finite.equiv (Representation.asModuleEquiv ρ).symm
  haveI : Module.Free ℂ M := Module.Free.of_divisionRing ℂ M
  set dM := Module.finrank ℂ M with hdM
  let eM : M ≃ₗ[ℂ] (Fin dM → ℂ) := (Module.finBasis ℂ M).equivFun
  letI modN : Module (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.moduleTransportAlongLinearEquiv (R := MonoidAlgebra ℂ (AffineGroup K)) eM
  haveI towN : IsScalarTower ℂ (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.isScalarTower_moduleTransportAlongLinearEquiv eM
  let eR : M ≃ₗ[MonoidAlgebra ℂ (AffineGroup K)] (Fin dM → ℂ) := RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.linearEquiv_transportModule eM
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    IsSimpleModule.congr eR.symm
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K))
      (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)).asModule :=
    IsSimpleModule.congr (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.asModuleRepresentationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ))
  refine ⟨FDRep.of (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)),
    RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)), ?_⟩
  have h1 : Module.finrank ℂ (FDRep.of (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ))) = dM := by
    change Module.finrank ℂ (Fin dM → ℂ) = dM
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [h1, hdM]
  exact (Representation.asModuleEquiv ρ).finrank_eq

                                                                                          
                                                                                           
                                                                                                
                                                                                                    
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011335 [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (AffineGroup K) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) ρ.asModule) :
    ∃ (U : FDRep ℂ (AffineGroup K)), Simple U ∧ Module.finrank ℂ U = Module.finrank ℂ V ∧
      Nonempty (ρ.Equiv U.ρ) := by
  classical
  haveI : NeZero (Nat.card (AffineGroup K) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, card]
    have h2 : 1 < Fintype.card K := Fintype.one_lt_card
    have hne : Fintype.card K * (Fintype.card K - 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    exact_mod_cast hne
  letI M := Representation.asModule ρ
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) M := hρ
  haveI : Module.Finite ℂ M := Module.Finite.equiv (Representation.asModuleEquiv ρ).symm
  haveI : Module.Free ℂ M := Module.Free.of_divisionRing ℂ M
  set dM := Module.finrank ℂ M with hdM
  let eM : M ≃ₗ[ℂ] (Fin dM → ℂ) := (Module.finBasis ℂ M).equivFun
  letI modN : Module (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.moduleTransportAlongLinearEquiv (R := MonoidAlgebra ℂ (AffineGroup K)) eM
  haveI towN : IsScalarTower ℂ (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.isScalarTower_moduleTransportAlongLinearEquiv eM
  let eR : M ≃ₗ[MonoidAlgebra ℂ (AffineGroup K)] (Fin dM → ℂ) := RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.linearEquiv_transportModule eM
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (Fin dM → ℂ) :=
    IsSimpleModule.congr eR.symm
  haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K))
      (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)).asModule :=
    IsSimpleModule.congr (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.asModuleRepresentationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ))
  refine ⟨FDRep.of (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)),
    RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule
      (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)), ?_, ?_⟩
  · have h1 : Module.finrank ℂ
        (FDRep.of (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ))) = dM := by
      change Module.finrank ℂ (Fin dM → ℂ) = dM
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [h1, hdM]
    exact (Representation.asModuleEquiv ρ).finrank_eq
  ·                                                                                            
    refine ⟨RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationEquivOfModuleLinearEquiv ρ
      (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ))
      (eR ≪≫ₗ (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.asModuleRepresentationOfMonoidAlgebraModule (k := ℂ) (G := AffineGroup K) (Fin dM → ℂ)).symm)⟩

                                                                                            
                                                                                              
                                                                                             
/-- A simplicity statement for the displayed representation or module. -/
@[source_ref "Chapter4/Problem4.12.6" (role := supporting)]
theorem simpleRepresentation_011343 [Fintype K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = Fintype.card K - 1 := by
  classical
                                      
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rcases eq_or_lt_of_le hq2 with hq_eq | hq_gt
  ·                                                                                         
    have hcardU : Fintype.card Kˣ = 1 := by rw [Fintype.card_units]; omega
    haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    letI grp : Group (AffineGroup K) := inferInstance
    letI : CommGroup (AffineGroup K) :=
      { grp with
        mul_comm := by
          intro x y
          have hxa : x.linearPart = 1 := Subsingleton.elim _ _
          have hya : y.linearPart = 1 := Subsingleton.elim _ _
          ext
          · simp [hxa, hya]
          · simp only [translationPart_mul, hxa, hya, Units.val_one, one_mul]; ring }
    haveI := hσ
    exact Or.inl (RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule σ)
  ·                                               
    have hq3 : 3 ≤ Fintype.card K := hq_gt
                                                                                  
    haveI hNe : NeZero (Nat.card (AffineGroup K) : ℂ) := by
      refine ⟨?_⟩
      rw [Nat.card_eq_fintype_card, card]
      exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
                                                                                    
    obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
      RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ (AffineGroup K)
                                            
    haveI : Finite (AffineGroup K →* ℂˣ) :=
      Nat.finite_of_card_ne_zero (by rw [cardinalityFormula_011354 hq3]; omega)
    haveI : Fintype (AffineGroup K →* ℂˣ) := Fintype.ofFinite _
    have hcardChar : Fintype.card (AffineGroup K →* ℂˣ) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_011354 hq3
                                                                                
    obtain ⟨UV, hUVsimple, hUVfr⟩ :=
      simpleRepresentation_011334 (augmentationSubrepresentation (K := K)).toRepresentation (simpleRepresentation_011266 (by omega))
    have hUVdim : Module.finrank ℂ UV = Fintype.card K - 1 := by
      rw [hUVfr]; exact cardinalityFormula_011444
                                                                                   
    let E : (AffineGroup K →* ℂˣ) ⊕ Unit → FDRep ℂ (AffineGroup K) :=
      Sum.elim (fun χ => FDRep.of (characterRepresentation χ)) (fun _ => UV)
    have hEfinL : ∀ χ : AffineGroup K →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 := fun χ => by
      change Module.finrank ℂ ℂ = 1; exact Module.finrank_self ℂ
    have hEfinR : ∀ u : Unit, Module.finrank ℂ (E (Sum.inr u)) = Fintype.card K - 1 :=
      fun _ => hUVdim
    have hEsimple : ∀ i, Simple (E i) := by
      rintro (χ | u)
      · exact simpleRepresentation_011303 χ
      · exact hUVsimple
    have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
      rintro (χ | u) (χ' | u') ⟨α⟩
      · have hχ : χ = χ' := by
          ext g
          have hg := congrFun (FDRep.char_iso α) g
          rw [show E (Sum.inl χ) = FDRep.of (characterRepresentation χ) from rfl,
              show E (Sum.inl χ') = FDRep.of (characterRepresentation χ') from rfl,
              characterFormula_011299, characterFormula_011299] at hg
          exact hg
        rw [hχ]
      · exfalso
        have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
        rw [hEfinL χ, hEfinR u'] at hfr; omega
      · exfalso
        have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
        rw [hEfinR u, hEfinL χ'] at hfr; omega
      · rw [Subsingleton.elim u u']
                                              
    choose c hc using fun i => hVsurj (E i) (hEsimple i)
    have hc_inj : Function.Injective c := by
      intro i j hij
      obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
      exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
    have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
      LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
                                                             
    have harith : ∀ r : ℕ, 1 ≤ r → r - 1 + (r - 1) ^ 2 = r * (r - 1) := by
      intro r hr; obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = Fintype.card (AffineGroup K) := by
      rw [Fintype.sum_sum_type, card]
      have hL : ∑ χ : AffineGroup K →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2
          = Fintype.card K - 1 := by
        have hone : ∀ χ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 :=
          fun χ => by rw [hEfinL, one_pow]
        rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
          hcardChar, smul_eq_mul, mul_one]
      have hR : ∑ _u : Unit, (Module.finrank ℂ (E (Sum.inr _u))) ^ 2
          = (Fintype.card K - 1) ^ 2 := by simp [hEfinR]
      rw [hL, hR]; exact harith _ (by omega)
    have hVsum' : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = Fintype.card (AffineGroup K) := hVsum
    have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2
        = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
      rw [hVsum', ← hEsum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
    have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
      intro j
      haveI : Simple (V j) := hVsimple j
      haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (Representation.asModule (V j).ρ) :=
        RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep (V j)
      haveI : Nontrivial (Representation.asModule (V j).ρ) :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (AffineGroup K)) (Representation.asModule (V j).ρ)
      haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
      exact pow_pos Module.finrank_pos 2
    have hcsurj : Function.Surjective c :=
      surj_of_injective_of_sum_eq _ hVpos c hc_inj hmatch
    have hEdisj : ∀ i, Module.finrank ℂ (E i) = 1 ∨ Module.finrank ℂ (E i) = Fintype.card K - 1 := by
      rintro (χ | u)
      · exact Or.inl (hEfinL χ)
      · exact Or.inr (hEfinR u)
                                                                     
    obtain ⟨U, hUsimple, hUfr⟩ := simpleRepresentation_011334 σ hσ
    obtain ⟨j, hjU⟩ := hVsurj U hUsimple
    obtain ⟨i, hci⟩ := hcsurj j
    have hUEi : Module.finrank ℂ U = Module.finrank ℂ (E i) := by
      rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hjU.some), ← hci, ← hfinrankc i]
    rw [← hUfr, hUEi]
    exact hEdisj i

                                                                   

                                                                                      
                                                                                           
                                                                                                
                                                                                            
                                                                                            
                                                                                              
                                                       

                                                                                     
                                                                                    
                                                            
/-- The construction specified by the displayed formal type. -/
def fixedPointCount [Fintype K] [DecidableEq K] (g : AffineGroup K) : ℕ :=
  (Finset.univ.filter (fun x : K => act g x = x)).card

                                                                                                
                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011278 [Fintype K] [DecidableEq K] (g : AffineGroup K) :
    (Function.fixedPoints (actionEquiv g⁻¹)).ncard = fixedPointCount g := by
  rw [fixedPointCount, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  change act g⁻¹ x = x ↔ act g x = x
  rw [inv_act_eq_iff]
  exact eq_comm

                                                             
/-- A cardinality or dimension identity for the displayed finite object. -/
@[simp] lemma cardinalityFormula_011291 [Fintype K] [DecidableEq K] :
    fixedPointCount (1 : AffineGroup K) = Fintype.card K := by
  rw [fixedPointCount, Finset.filter_true_of_mem (fun x _ => one_act x)]
  simp

                                                                                                 
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011292 [Fintype K] [DecidableEq K] {b : K} (hb : b ≠ 0) :
    fixedPointCount (⟨1, b⟩ : AffineGroup K) = 0 := by
  rw [fixedPointCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  simp only [act, Units.val_one, one_mul]
  intro h
  exact hb (add_left_cancel (show x + b = x + 0 by rw [add_zero]; exact h))

                                                                                           
                         
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011280 [Fintype K] [DecidableEq K] {g : AffineGroup K} (hg : g.linearPart ≠ 1) :
    fixedPointCount g = 1 := by
  have hu : (g.linearPart : K) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hg (Units.ext h))
  rw [fixedPointCount, Finset.card_eq_one]
  refine ⟨((g.linearPart : K) - 1)⁻¹ * (-g.translationPart), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    simp only [act] at h
    have h2 : ((g.linearPart : K) - 1) * x = -g.translationPart := by linear_combination h
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  · rintro rfl
    simp only [act]
    field_simp
    ring

                                                                                     
/-- The linear map specified by the displayed formal signature. -/
def sumLinearMap (K : Type*) [Fintype K] : (K → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, f x
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

omit [Field K] in
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011428 [Fintype K] (f : K → ℂ) : sumLinearMap K f = ∑ x, f x := rfl

omit [Field K] in
/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011353 [Fintype K] (f : K → ℂ) : f ∈ zeroSumSubmodule K ↔ sumLinearMap K f = 0 := Iff.rfl

                                                                                 
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011375 [Fintype K] [DecidableEq K] (g : AffineGroup K) :
    (functionRepresentation g) = (Equiv.Perm.permMatrix ℂ (actionEquiv g⁻¹)).toLin' := by
  apply LinearMap.ext; intro f; funext x
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, valueFormula_011374]
  rfl

                                                                                                
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011438 [Fintype K] [DecidableEq K] (g : AffineGroup K) :
    LinearMap.trace ℂ (K → ℂ) (functionRepresentation g) = (fixedPointCount g : ℂ) := by
  rw [valueFormula_011375, Matrix.trace_toLin'_eq, Matrix.trace_permutation, cardinalityFormula_011278]

                                                                                                
                                                
                                                                                                 
                                                  
/-- A formula for the character or trace of the displayed representation. -/
@[source_ref "Chapter4/Problem4.12.6" (role := supporting)]
theorem characterFormula_011257 [Fintype K] [DecidableEq K] (g : AffineGroup K) :
    (augmentationSubrepresentation (K := K)).toRepresentation.character g = (fixedPointCount g : ℂ) - 1 := by
  classical
  have hone_ne : (1 : K → ℂ) ≠ 0 := by
    intro h; have h0 := congrFun h (0 : K); simp at h0
  have hsum1 : sumLinearMap K (1 : K → ℂ) = (Fintype.card K : ℂ) := by
    simp [Finset.card_univ]
                                                                                
  set L : Submodule ℂ (K → ℂ) := Submodule.span ℂ {(1 : K → ℂ)} with hLdef
  set N : Fin 2 → Submodule ℂ (K → ℂ) := ![(augmentationSubrepresentation (K := K)).toSubmodule, L] with hN
                                           
  have hcompl : IsCompl (zeroSumSubmodule K) L := by
    have hone : Module.finrank ℂ L = 1 := finrank_span_singleton hone_ne
    have hVdim : Module.finrank ℂ (zeroSumSubmodule K) = Fintype.card K - 1 := cardinalityFormula_011444
    have hdim : Module.finrank ℂ (K → ℂ) ≤
        Module.finrank ℂ (zeroSumSubmodule K) + Module.finrank ℂ L := by
      rw [hVdim, hone, Module.finrank_pi ℂ]; omega
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxV hxL
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have h0 : sumLinearMap K (c • (1 : K → ℂ)) = 0 := (membershipCharacterization_011353 _).mp hxV
    rw [map_smul, hsum1, smul_eq_mul] at h0
    have hqne : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    rcases mul_eq_zero.mp h0 with h | h
    · simp [h]
    · exact absurd h hqne
                                                     
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (by decide : (0 : Fin 2) ≠ 1) huniv).mpr hcompl
                                        
  have hf0 : Set.MapsTo (functionRepresentation g) (N 0) (N 0) := (augmentationSubrepresentation (K := K)).apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (functionRepresentation g) (N 1) (N 1) := by
    intro x hx
    change x ∈ L at hx
    change functionRepresentation g x ∈ L
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, valueFormula_011386 functionRepresentation valueFormula_011374 g]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hf : ∀ i, Set.MapsTo (functionRepresentation g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [characterFormula_011438, Fin.sum_univ_two] at htr
                                            
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((functionRepresentation g).restrict (hf 0))
      = (augmentationSubrepresentation (K := K)).toRepresentation.character g := rfl
                                                                   
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((functionRepresentation g).restrict (hf 1)) = 1 := by
    have hid : (functionRepresentation g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : K → ℂ) ∈ L := x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      change functionRepresentation g (x : K → ℂ) = (x : K → ℂ)
      rw [← hc, map_smul, valueFormula_011386 functionRepresentation valueFormula_011374 g]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton hone_ne
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

                                                                       
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011264 [Fintype K] :
    (augmentationSubrepresentation (K := K)).toRepresentation.character (1 : AffineGroup K) = (Fintype.card K : ℂ) - 1 := by
  classical rw [characterFormula_011257, cardinalityFormula_011291]

                                                                                   
/-- Auxiliary result whose proposition is not displayed in the packet. -/
lemma Auxiliary011265 [Fintype K] {b : K} (hb : b ≠ 0) :
    (augmentationSubrepresentation (K := K)).toRepresentation.character (⟨1, b⟩ : AffineGroup K) = -1 := by
  classical rw [characterFormula_011257, valueFormula_011292 hb]; simp

                                                            
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011263 [Fintype K] {g : AffineGroup K} (hg : g.linearPart ≠ 1) :
    (augmentationSubrepresentation (K := K)).toRepresentation.character g = 0 := by
  classical rw [characterFormula_011257, valueFormula_011280 hg]; simp

                                           

                                                                                           
                                                                                                
                                                                           

                                                                            
                                      
                                                                                             
                                              
                                                                                      
                                                                           

                                                                              
/-- A formula for the character or trace of the displayed representation. -/
@[simp] lemma characterFormula_011302 (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (characterRepresentation χ).character g = (χ g : ℂ) := by
  have hg : characterRepresentation χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ (characterRepresentation χ g) = (χ g : ℂ)
  rw [hg, map_smul, LinearMap.trace_id]
  simp

                                                                                              
                                                                       
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011308 (χ χ' : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (Representation.tprod (characterRepresentation χ) (characterRepresentation χ')).character g
      = (characterRepresentation (χ * χ')).character g := by
  rw [Representation.char_tensor, Pi.mul_apply, characterFormula_011302, characterFormula_011302,
    characterFormula_011302, MonoidHom.mul_apply, Units.val_mul]

                                                                                             
                                                                                          
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011304 [Fintype K] (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (Representation.tprod (characterRepresentation χ) (augmentationSubrepresentation (K := K)).toRepresentation).character g
      = (χ g : ℂ) * (augmentationSubrepresentation (K := K)).toRepresentation.character g := by
  rw [Representation.char_tensor, Pi.mul_apply, characterFormula_011302]

                                                                                        
                                                                                             
                                                
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011268 [Fintype K] (g : AffineGroup K) :
    Representation.character
        (V := TensorProduct ℂ ↥(augmentationSubrepresentation (K := K)).toSubmodule ↥(augmentationSubrepresentation (K := K)).toSubmodule)
        (Representation.tprod (augmentationSubrepresentation (K := K)).toRepresentation
          (augmentationSubrepresentation (K := K)).toRepresentation) g
      = ((augmentationSubrepresentation (K := K)).toRepresentation.character g) ^ 2 := by
  rw [Representation.char_tensor, Pi.mul_apply, sq]

                                                                   

                                                  
                                                                                  
                                                                             

                                                    

                                                                                             
                                                                                         
                                                                                         
                                                                                           
                                                                     
                                      

                                                                                            
                                                                                        
                                                                                                    
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011313 [Fintype K] (hK : 3 ≤ Fintype.card K)
    (φ : AffineGroup K →* ℂˣ) (c : K) : φ (⟨1, c⟩ : AffineGroup K) = 1 := by
  classical
  have key : ∀ u v : ℂˣ, u * v * u⁻¹ * v⁻¹ = 1 := fun u v => by
    rw [mul_comm u v]; group
  have hcard : 2 ≤ Fintype.card Kˣ := by rw [Fintype.card_units]; omega
  have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
  have hu : ((a₀ : K) - 1) ≠ 0 := sub_ne_zero.mpr fun h => ha₀ (Units.ext h)
  have hkey : ∀ (a : Kˣ) (c' : K), φ (⟨1, (a : K) * c' - c'⟩ : AffineGroup K) = 1 := by
    intro a c'
    have ha : (a : K) ≠ 0 := Units.ne_zero a
    have hcomm : (⟨1, (a : K) * c' - c'⟩ : AffineGroup K) =
        ⟨a, 0⟩ * ⟨1, c'⟩ * ⟨a, 0⟩⁻¹ * ⟨1, c'⟩⁻¹ := by
      ext
      · simp
      · simp only [translationPart_mul, linearPart_mul, linearPart_inv, translationPart_inv, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_zero, add_zero, mul_one,
          mul_neg, one_mul]
        field_simp
        ring
    rw [hcomm]
    simp only [map_mul, map_inv]
    exact key _ _
  have h := hkey a₀ (((a₀ : K) - 1)⁻¹ * c)
  have hval : (a₀ : K) * (((a₀ : K) - 1)⁻¹ * c) - ((a₀ : K) - 1)⁻¹ * c = c := by
    field_simp
  rwa [hval] at h

                                                                                    
/-- The monoid homomorphism specified by the displayed formal signature. -/
def linearPartHom : AffineGroup K →* Kˣ where
  toFun g := g.linearPart
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011379 (g : AffineGroup K) : linearPartHom g = g.linearPart := rfl

                                                                                     
                                                                                       
                                 
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011429 [Fintype K] [DecidableEq K] [Fintype (AffineGroup K →* ℂˣ)]
    (hK : 3 ≤ Fintype.card K) (g : AffineGroup K) :
    ∑ χ : AffineGroup K →* ℂˣ, (χ g : ℂ)
      = if g.linearPart = 1 then ((Fintype.card K : ℂ) - 1) else 0 := by
  classical
  by_cases hga : g.linearPart = 1
  ·                                                               
    rw [if_pos hga]
    have hval : ∀ χ : AffineGroup K →* ℂˣ, (χ g : ℂ) = 1 := by
      intro χ
      have hg : g = (⟨1, g.translationPart⟩ : AffineGroup K) := by ext <;> simp [hga]
      rw [hg, cardinalityFormula_011313 hK χ g.translationPart, Units.val_one]
    rw [Finset.sum_congr rfl (fun χ _ => hval χ), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    have hcnt : Fintype.card (AffineGroup K →* ℂˣ) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_011354 hK
    rw [hcnt, Nat.cast_sub (by omega), Nat.cast_one]
  ·                                                               
    rw [if_neg hga]
    haveI : NeZero ((Monoid.exponent Kˣ : ℕ) : ℂ) :=
      ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ψ₀, hψ₀⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Kˣ ℂ (show g.linearPart ≠ 1 from hga)
    set χ₀ : AffineGroup K →* ℂˣ := ψ₀.comp linearPartHom with hχ₀
    have hχ₀g : χ₀ g = ψ₀ g.linearPart := rfl
    have hne1 : (χ₀ g : ℂ) ≠ 1 := by
      intro h
      exact hψ₀ (Units.ext (by rw [Units.val_one, ← hχ₀g]; exact h))
                                                                                     
    refine eq_zero_of_mul_eq_self_left hne1 ?_
    rw [Finset.mul_sum]
    have hstep : ∀ χ : AffineGroup K →* ℂˣ, (χ₀ g : ℂ) * (χ g : ℂ) = ((χ₀ * χ) g : ℂ) := by
      intro χ; rw [MonoidHom.mul_apply, Units.val_mul]
    simp_rw [hstep]
    exact Fintype.sum_bijective (fun χ => χ₀ * χ) (Group.mulLeft_bijective χ₀) _ _ (fun χ => rfl)

                                                                                     
                                                                                              
                                                                    
                                                                                              
                                                              
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011269 [Fintype K]
    [Fintype (AffineGroup K →* ℂˣ)] (hK : 3 ≤ Fintype.card K) (g : AffineGroup K) :
    ((augmentationSubrepresentation (K := K)).toRepresentation.character g) ^ 2
      = (∑ χ : AffineGroup K →* ℂˣ, (χ g : ℂ))
        + ((Fintype.card K : ℂ) - 2) * (augmentationSubrepresentation (K := K)).toRepresentation.character g := by
  classical
  rw [characterFormula_011257 g, cardinalityFormula_011429 hK]
  by_cases hga : g.linearPart = 1
  · rw [if_pos hga]
    by_cases hgb : g.translationPart = 0
    ·                                           
      have hg1 : g = 1 := by ext <;> simp [hga, hgb]
      rw [hg1, cardinalityFormula_011291]
      ring
    ·                                                        
      have hfix : fixedPointCount g = 0 := by
        have hg : g = (⟨1, g.translationPart⟩ : AffineGroup K) := by ext <;> simp [hga]
        rw [hg]; exact valueFormula_011292 hgb
      rw [hfix]; push_cast; ring
  ·                                  
    rw [if_neg hga, valueFormula_011280 hga]
    push_cast; ring

                                               

                                                                                         
                                                                                               
                                                                                                  
                                                                                                 
              

                                                                      
private theorem natCard_affine_ne_zero [Finite (AffineGroup K)] :
    (Nat.card (AffineGroup K) : ℂ) ≠ 0 := by
  have : Nat.card (AffineGroup K) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  exact_mod_cast this

                                                                                     
                                                                                               
                                                                                               
                                                                                              
                                           
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011330 [Fintype (AffineGroup K)]
    {Vρ Wσ : Type*} [AddCommGroup Vρ] [Module ℂ Vρ] [FiniteDimensional ℂ Vρ]
    [AddCommGroup Wσ] [Module ℂ Wσ] [FiniteDimensional ℂ Wσ]
    (ρ : Representation ℂ (AffineGroup K) Vρ) (σ : Representation ℂ (AffineGroup K) Wσ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  haveI : Invertible (Nat.card (AffineGroup K) : ℂ) := invertibleOfNonzero natCard_affine_ne_zero
  by_contra hcon
  have hemp : ¬ Nonempty (σ.Equiv ρ) := fun ⟨e⟩ => hcon ⟨e.symm⟩
  have h1 := Representation.char_orthonormal (ρ := ρ) (σ := σ)
  have h2 := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
  rw [if_neg hemp] at h1
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h2
  rw [← h] at h1
  rw [h1] at h2
  norm_num at h2

                                                                                                
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011297 (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) (c : ℂ) :
    characterRepresentation χ g c = (χ g : ℂ) • c := rfl

                                                                                          
                                                                                               
                                                          
/-- The representation specified by the displayed formal signature. -/
def twistRepresentation (χ : AffineGroup K →* ℂˣ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (AffineGroup K) W) : Representation ℂ (AffineGroup K) W where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply,
      Units.val_mul, map_smul, smul_smul, mul_comm]

/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011411 (χ : AffineGroup K →* ℂˣ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (AffineGroup K) W) (g : AffineGroup K) (x : W) :
    twistRepresentation χ ρ g x = (χ g : ℂ) • ρ g x := rfl

                                                                                          
                                                                                                
                                                                                      
/-- The representation specified by the displayed formal signature. -/
def twistedTensorEquiv (χ : AffineGroup K →* ℂˣ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (AffineGroup K) W) :
    Subrepresentation (twistRepresentation χ ρ) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule g hv
    rw [valueFormula_011411] at h
    have h2 := U.toSubmodule.smul_mem ((χ g : ℂ)⁻¹) h
    rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule g hv
    rw [valueFormula_011411]
    exact U.toSubmodule.smul_mem _ h⟩
  left_inv U := rfl
  right_inv U := rfl
  map_rel_iff' := Iff.rfl

                                                                                                  
/-- The proposition given by the displayed formal type. -/
theorem formalResult_011413 (χ : AffineGroup K →* ℂˣ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (AffineGroup K) W) [ρ.IsIrreducible] :
    (twistRepresentation χ ρ).IsIrreducible :=
  (twistedTensorEquiv χ ρ).isSimpleOrder_iff.mpr inferInstance

                                                                                            
/-- The representation specified by the displayed formal signature. -/
def twistTensorEquiv (χ : AffineGroup K →* ℂˣ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (AffineGroup K) W) :
    (Representation.tprod (characterRepresentation χ) ρ).Equiv (twistRepresentation χ ρ) :=
  Representation.Equiv.mk (TensorProduct.lid ℂ W) fun g => by
    refine TensorProduct.ext' fun c w => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      valueFormula_011297, valueFormula_011411, map_smul, smul_smul, smul_eq_mul]
    rw [mul_comm]

                                                                         
/-- An equivalence statement for the displayed representations. -/
theorem representationEquivalence_011254 {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (AffineGroup K) V}
    {σ : Representation ℂ (AffineGroup K) W} (e : ρ.Equiv σ) [ρ.IsIrreducible] :
    σ.IsIrreducible := by
  haveI hρ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine IsSimpleModule.congr
    (LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap) ?_)
  exact e.symm.toLinearEquiv.bijective

                                                                                   
                                                                                                  
                                                                                         
                                                                         
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011305 [Fintype K]
    (hK : 3 ≤ Fintype.card K) (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (Representation.tprod (characterRepresentation χ) (augmentationSubrepresentation (K := K)).toRepresentation).character g
      = (augmentationSubrepresentation (K := K)).toRepresentation.character g := by
  classical
  rw [characterFormula_011304]
  by_cases hga : g.linearPart = 1
  · have hg : g = (⟨1, g.translationPart⟩ : AffineGroup K) := by ext <;> simp [hga]
    rw [hg, cardinalityFormula_011313 hK χ g.translationPart, Units.val_one, one_mul]
  · rw [characterFormula_011263 hga, mul_zero]

                                                                        
                                                                                          
                                                               
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.6" (role := primary)]
theorem cardinalityFormula_011306 [Fintype K] [DecidableEq K]
    (hK : 3 ≤ Fintype.card K) (χ : AffineGroup K →* ℂˣ) :
    Nonempty ((Representation.tprod (characterRepresentation χ) (augmentationSubrepresentation (K := K)).toRepresentation).Equiv
      (augmentationSubrepresentation (K := K)).toRepresentation) := by
  haveI hV : (augmentationSubrepresentation (K := K)).toRepresentation.IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (simpleRepresentation_011266 (by omega))
  haveI hχ : (characterRepresentation χ).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (simpleRepresentation_011298 χ)
  haveI hsmul : (twistRepresentation χ (augmentationSubrepresentation (K := K)).toRepresentation).IsIrreducible :=
    formalResult_011413 χ _
  haveI htp : (Representation.tprod (characterRepresentation χ) (augmentationSubrepresentation (K := K)).toRepresentation).IsIrreducible :=
    representationEquivalence_011254 (twistTensorEquiv χ _).symm
  exact characterFormula_011330 _ _ (funext fun g => characterFormula_011305 hK χ g)

                                                                                             
                                                                             
                                       
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011412 (χ χ' : AffineGroup K →* ℂˣ) :
    twistRepresentation χ (characterRepresentation χ') = characterRepresentation (χ * χ') := by
  ext g
  simp only [valueFormula_011411, valueFormula_011297, MonoidHom.mul_apply, Units.val_mul, smul_smul]

                                                                                         
                                                                                      
                                                                                                  
                                                                                          
                                                        
/-- The representation specified by the displayed formal signature. -/
def characterTensorEquiv (χ χ' : AffineGroup K →* ℂˣ) :
    (Representation.tprod (characterRepresentation χ) (characterRepresentation χ')).Equiv (characterRepresentation (χ * χ')) :=
  valueFormula_011412 χ χ' ▸ twistTensorEquiv χ (characterRepresentation χ')

                                                                      

                                                                                      
                                                                                               
                                                                                             
                                                                                         
                                                                                           
                                                                                               
                                                 

                                                                                               
                                        
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011312 {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (AffineGroup K) V) (σ : Representation ℂ (AffineGroup K) W) (g : AffineGroup K) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by
  change LinearMap.trace ℂ (V × W) ((ρ.prod σ) g) = _
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

                                                                                            
                                                                
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011311 {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (AffineGroup K) (V i)) (g : AffineGroup K) :
    (Representation.directSum ρ).character g = ∑ i, (ρ i).character g := by
  classical
  simp only [Representation.character]
  have hg : (Representation.directSum ρ) g = DirectSum.lmap (fun i => ρ i g) := rfl
  rw [hg]
  have hf : DirectSum.lmap (fun i => ρ i g)
      = ∑ i, (DirectSum.lof ℂ ι V i) ∘ₗ (ρ i g) ∘ₗ (DirectSum.component ℂ ι V i) := by
    ext i x
    simp only [DirectSum.lmap_lof, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single i]
    · simp [DirectSum.component.lof_self]
    · intro j _ hji
      simp [DirectSum.component.of, Ne.symm hji]
    · simp
  rw [hf, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    DirectSum.component_comp_lof_same, LinearMap.comp_id]

                                                                                        
                                                                             
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011300 (χ : AffineGroup K →* ℂˣ) (g : AffineGroup K) :
    (characterRepresentation χ).character g = (χ g : ℂ) := by
  have hg : characterRepresentation χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ (characterRepresentation χ g) = _
  rw [hg, map_smul, LinearMap.trace_id]
  simp

                                                                              
/-- The representation specified by the displayed formal signature. -/
noncomputable def sumOfLinearCharacters [Fintype (AffineGroup K →* ℂˣ)] :
    Representation ℂ (AffineGroup K) (DirectSum (AffineGroup K →* ℂˣ) (fun _ => ℂ)) :=
  Representation.directSum (fun χ => characterRepresentation χ)

                                                                                 
/-- The representation specified by the displayed formal signature. -/
noncomputable def reducedRegularRepresentation [Fintype K] :
    Representation ℂ (AffineGroup K) (DirectSum (Fin (Fintype.card K - 2)) (fun _ => (zeroSumSubmodule K))) :=
  Representation.directSum (fun _ => (augmentationSubrepresentation (K := K)).toRepresentation)

                                                                                             
                                                                                      
                                                                                          
                 
/-- The representation specified by the displayed formal signature. -/
noncomputable def characterSumProductRepresentation [Fintype K] [Fintype (AffineGroup K →* ℂˣ)] :
    Representation ℂ (AffineGroup K)
      ((DirectSum (AffineGroup K →* ℂˣ) (fun _ => ℂ)) ×
        (DirectSum (Fin (Fintype.card K - 2)) (fun _ => (zeroSumSubmodule K)))) :=
  (sumOfLinearCharacters (K := K)).prod (reducedRegularRepresentation (K := K))

set_option maxHeartbeats 1000000 in
                                                                                            
                                                                       
                                      
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011392 [Fintype K] [Fintype (AffineGroup K →* ℂˣ)]
    (hK : 3 ≤ Fintype.card K) (g : AffineGroup K) :
    Representation.character
        (V := (DirectSum (AffineGroup K →* ℂˣ) (fun _ => ℂ)) ×
          (DirectSum (Fin (Fintype.card K - 2)) (fun _ => (zeroSumSubmodule K))))
        (characterSumProductRepresentation (K := K)) g
      = (∑ χ : AffineGroup K →* ℂˣ, (χ g : ℂ))
        + ((Fintype.card K : ℂ) - 2) * (augmentationSubrepresentation (K := K)).toRepresentation.character g := by
                                                                                        
                                                                                       
                                                                                          
                                                                                              
                                                                                              
  have key := characterFormula_011312 (V := DirectSum (AffineGroup K →* ℂˣ) (fun _ => ℂ))
    (W := DirectSum (Fin (Fintype.card K - 2)) (fun _ => (zeroSumSubmodule K)))
    (sumOfLinearCharacters (K := K)) (reducedRegularRepresentation (K := K)) g
  have kcs := characterFormula_011311 (V := fun _ : (AffineGroup K →* ℂˣ) => ℂ) (fun χ => characterRepresentation χ) g
  have kvc := characterFormula_011311
    (V := fun _ : Fin (Fintype.card K - 2) => ↥(zeroSumSubmodule K))
    (fun _ => (augmentationSubrepresentation (K := K)).toRepresentation) g
  rw [characterSumProductRepresentation, key]
  simp only [sumOfLinearCharacters, reducedRegularRepresentation]
  rw [kcs, kvc]
  congr 1
  · exact Finset.sum_congr rfl (fun χ _ => characterFormula_011300 χ g)
  ·                                                                                     
                                                                                               
                                                          
    change (∑ _i : Fin (Fintype.card K - 2), (augmentationSubrepresentation (K := K)).toRepresentation.character g)
        = ((Fintype.card K : ℂ) - 2) * (augmentationSubrepresentation (K := K)).toRepresentation.character g
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega)]
    push_cast
    ring


                                                                        

                                                                                                 
                                                                                                
                                                                                               
                                                                                                  
                                                                                                  
                                                                

                                                                                     
                                                                                     
                                                                                         
                                                               
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011399 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {UV : FDRep ℂ (AffineGroup K)} (hUVsimple : Simple UV)
    (hUVdim : Module.finrank ℂ UV = Fintype.card K - 1)
    {U : FDRep ℂ (AffineGroup K)} (hU : Simple U) :
    (∃ χ : AffineGroup K →* ℂˣ, Nonempty (U ≅ FDRep.of (characterRepresentation χ))) ∨ Nonempty (U ≅ UV) := by
  classical
  haveI hNe : NeZero (Nat.card (AffineGroup K) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, card]
    exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
                                                                              
  obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ (AffineGroup K)
  haveI : Finite (AffineGroup K →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [cardinalityFormula_011354 hK]; omega)
  haveI : Fintype (AffineGroup K →* ℂˣ) := Fintype.ofFinite _
  have hcardChar : Fintype.card (AffineGroup K →* ℂˣ) = Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_011354 hK
                                                                                  
  let E : (AffineGroup K →* ℂˣ) ⊕ Unit → FDRep ℂ (AffineGroup K) :=
    Sum.elim (fun χ => FDRep.of (characterRepresentation χ)) (fun _ => UV)
  have hEfinL : ∀ χ : AffineGroup K →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 := fun χ => by
    change Module.finrank ℂ ℂ = 1; exact Module.finrank_self ℂ
  have hEfinR : ∀ u : Unit, Module.finrank ℂ (E (Sum.inr u)) = Fintype.card K - 1 :=
    fun _ => hUVdim
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | u)
    · exact simpleRepresentation_011303 χ
    · exact hUVsimple
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | u) (χ' | u') ⟨α⟩
    · have hχ : χ = χ' := by
        ext g
        have hg := congrFun (FDRep.char_iso α) g
        rw [show E (Sum.inl χ) = FDRep.of (characterRepresentation χ) from rfl,
            show E (Sum.inl χ') = FDRep.of (characterRepresentation χ') from rfl,
            characterFormula_011299, characterFormula_011299] at hg
        exact hg
      rw [hχ]
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinL χ, hEfinR u'] at hfr; omega
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinR u, hEfinL χ'] at hfr; omega
    · rw [Subsingleton.elim u u']
                                                                                               
  choose c hc using fun i => hVsurj (E i) (hEsimple i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
    exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
  have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
    LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
  have harith : ∀ r : ℕ, 1 ≤ r → r - 1 + (r - 1) ^ 2 = r * (r - 1) := by
    intro r hr; obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = Fintype.card (AffineGroup K) := by
    rw [Fintype.sum_sum_type, card]
    have hL : ∑ χ : AffineGroup K →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2
        = Fintype.card K - 1 := by
      have hone : ∀ χ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 :=
        fun χ => by rw [hEfinL, one_pow]
      rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
        hcardChar, smul_eq_mul, mul_one]
    have hR : ∑ _u : Unit, (Module.finrank ℂ (E (Sum.inr _u))) ^ 2
        = (Fintype.card K - 1) ^ 2 := by simp [hEfinR]
    rw [hL, hR]; exact harith _ (by omega)
  have hVsum' : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = Fintype.card (AffineGroup K) := hVsum
  have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2
      = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
    rw [hVsum', ← hEsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
  have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
    intro j
    haveI : Simple (V j) := hVsimple j
    haveI : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) (Representation.asModule (V j).ρ) :=
      RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep (V j)
    haveI : Nontrivial (Representation.asModule (V j).ρ) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (AffineGroup K)) (Representation.asModule (V j).ρ)
    haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
    exact pow_pos Module.finrank_pos 2
  have hcsurj : Function.Surjective c :=
    surj_of_injective_of_sum_eq _ hVpos c hc_inj hmatch
                                                                         
  obtain ⟨j, hjU⟩ := hVsurj U hU
  obtain ⟨i, hci⟩ := hcsurj j
  have hUEi : Nonempty (U ≅ E i) :=
    ⟨hjU.some ≪≫ eqToIso (congrArg V hci.symm) ≪≫ (hc i).some.symm⟩
  rcases i with χ | u
  · exact Or.inl ⟨χ, hUEi⟩
  · exact Or.inr hUEi

                                                                                                
                                                                       
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011394 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {U U' : FDRep ℂ (AffineGroup K)} (hU : Simple U) (hU' : Simple U')
    (hUdim : Module.finrank ℂ U = Fintype.card K - 1)
    (hU'dim : Module.finrank ℂ U' = Fintype.card K - 1) :
    Nonempty (U ≅ U') := by
  rcases simpleRepresentation_011399 hK hU' hU'dim hU with ⟨χ, hχ⟩ | h
  · exfalso
    have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hχ.some)
    rw [hUdim, show Module.finrank ℂ (FDRep.of (characterRepresentation χ)) = 1 from Module.finrank_self ℂ] at hfr
    omega
  · exact h

                                                                                              
                                                                                              
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011396 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {U : FDRep ℂ (AffineGroup K)} (hU : Simple U) (hUdim : Module.finrank ℂ U = 1) :
    ∃ χ : AffineGroup K →* ℂˣ, Nonempty (U ≅ FDRep.of (characterRepresentation χ)) := by
                                                                                              
  obtain ⟨UV, hUVsimple, hUVfr⟩ :=
    simpleRepresentation_011334 (augmentationSubrepresentation (K := K)).toRepresentation (simpleRepresentation_011266 (by omega))
  have hUVdim : Module.finrank ℂ UV = Fintype.card K - 1 := by rw [hUVfr]; exact cardinalityFormula_011444
  rcases simpleRepresentation_011399 hK hUVsimple hUVdim hU with h | hUV
  · exact h
  · exfalso
    have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hUV.some)
    rw [hUdim, hUVdim] at hfr; omega

                                                                                                 
                                                                                     
                   

                                                                                             
                                                                                           
                                                                                  
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011271 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule)
    (hdim : Module.finrank ℂ W = Fintype.card K - 1) :
    Nonempty (σ.Equiv (augmentationSubrepresentation (K := K)).toRepresentation) := by
  classical
                                                                                    
  obtain ⟨U, hUsimple, hUfr, ⟨eσ⟩⟩ := simpleRepresentation_011335 σ hσ
  obtain ⟨U', hU'simple, hU'fr, ⟨eV⟩⟩ :=
    simpleRepresentation_011335 (augmentationSubrepresentation (K := K)).toRepresentation (simpleRepresentation_011266 (by omega))
  have hUdim : Module.finrank ℂ U = Fintype.card K - 1 := by rw [hUfr, hdim]
  have hU'dim : Module.finrank ℂ U' = Fintype.card K - 1 := by rw [hU'fr]; exact cardinalityFormula_011444
                                                                                    
  obtain ⟨α⟩ := simpleRepresentation_011394 hK hUsimple hU'simple hUdim hU'dim
                                                                                                    
                                        
  have hcharσ : σ.character = Representation.character U.ρ := Representation.char_iso eσ
  have hcharV : (augmentationSubrepresentation (K := K)).toRepresentation.character = Representation.character U'.ρ :=
    Representation.char_iso eV
  have hcharUU' : Representation.character U.ρ = Representation.character U'.ρ :=
    FDRep.char_iso α
  have hchar : σ.character = (augmentationSubrepresentation (K := K)).toRepresentation.character := by
    rw [hcharσ, hcharUU', ← hcharV]
  haveI hσirr : σ.IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr hσ
  haveI hVirr : (augmentationSubrepresentation (K := K)).toRepresentation.IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (simpleRepresentation_011266 (by omega))
  exact characterFormula_011330 σ (augmentationSubrepresentation (K := K)).toRepresentation hchar

                                                                                                
                                                                                         
                           
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011301 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule)
    (hdim : Module.finrank ℂ W = 1) :
    ∃ χ : AffineGroup K →* ℂˣ, Nonempty (σ.Equiv (characterRepresentation χ)) := by
  classical
  obtain ⟨U, hUsimple, hUfr, ⟨eσ⟩⟩ := simpleRepresentation_011335 σ hσ
  have hUdim : Module.finrank ℂ U = 1 := by rw [hUfr, hdim]
  obtain ⟨χ, ⟨α⟩⟩ := simpleRepresentation_011396 hK hUsimple hUdim
  refine ⟨χ, ?_⟩
  have hcharσ : σ.character = Representation.character U.ρ := Representation.char_iso eσ
  have hcharUχ : Representation.character U.ρ = Representation.character (characterRepresentation χ) :=
    FDRep.char_iso α
  haveI hσirr : σ.IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr hσ
  haveI hχirr : (characterRepresentation χ).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (simpleRepresentation_011298 χ)
  exact characterFormula_011330 σ (characterRepresentation χ) (by rw [hcharσ, hcharUχ])

                                                                                             
                                                                                         
                                                                                                  
                                                                                                   
                                                                                
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011340 [Fintype K] [DecidableEq K] (hK : 3 ≤ Fintype.card K)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule) :
    (∃ χ : AffineGroup K →* ℂˣ, Nonempty (σ.Equiv (characterRepresentation χ))) ∨
      Nonempty (σ.Equiv (augmentationSubrepresentation (K := K)).toRepresentation) := by
  rcases simpleRepresentation_011343 σ hσ with hdim1 | hdimq
  · exact Or.inl (simpleRepresentation_011301 hK σ hσ hdim1)
  · exact Or.inr (simpleRepresentation_011271 hK σ hσ hdimq)


                                                          

                                                                                                 
                                                                                          
                                                                                                  
                                                                                         
                                                                                                  
                                                                                 
                                                                   

                                                                                          
                                                                                                  
                                                                                               
                                                                             
/-- The representation specified by the displayed formal signature. -/
noncomputable def tensorHomEquiv {K : Type} [Field K]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (AffineGroup K) V) (σ : Representation ℂ (AffineGroup K) W)
    (α : FDRep.of ρ ≅ FDRep.of σ) : ρ.Equiv σ :=
  RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationEquivOfModuleLinearEquiv ρ σ
    (Rep.toModuleMonoidAlgebra.mapIso
      ((forget₂ (FDRep ℂ (AffineGroup K)) (Rep ℂ (AffineGroup K))).mapIso α)).toLinearEquiv

                                                                                   
                                                                                                  
                                                                                                  
                                                                                                 
                                       
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011332 {K : Type} [Field K] [Finite (AffineGroup K)]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (AffineGroup K) V) (σ : Representation ℂ (AffineGroup K) W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  have hchar : (FDRep.of ρ).character = (FDRep.of σ).character := h
  obtain ⟨α⟩ := RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq (FDRep.of ρ) (FDRep.of σ) hchar
  exact ⟨tensorHomEquiv ρ σ α⟩

                                                                                                 
                                                                                                 
                                                                                                  
                                                                                             
                                                                                        
                                     
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.6" (role := primary)]
theorem cardinalityFormula_011270 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype (AffineGroup K →* ℂˣ)] (hK : 3 ≤ Fintype.card K) :
    Nonempty (((augmentationSubrepresentation (K := K)).toRepresentation.tprod (augmentationSubrepresentation (K := K)).toRepresentation).Equiv
      (characterSumProductRepresentation (K := K))) := by
  refine characterFormula_011332
    (V := TensorProduct ℂ ↥(augmentationSubrepresentation (K := K)).toSubmodule ↥(augmentationSubrepresentation (K := K)).toSubmodule)
    (W := (DirectSum (AffineGroup K →* ℂˣ) (fun _ => ℂ)) ×
      (DirectSum (Fin (Fintype.card K - 2)) (fun _ => (zeroSumSubmodule K))))
    ((augmentationSubrepresentation (K := K)).toRepresentation.tprod (augmentationSubrepresentation (K := K)).toRepresentation)
    (characterSumProductRepresentation (K := K)) ?_
  funext g
  rw [Representation.char_tensor, Pi.mul_apply, characterFormula_011392 hK g,
    ← characterFormula_011269 hK g, sq]

                                    

                                                                                               
                                                                                                     
                                                                                           
                                                                                              
                                                                                               
                                                                                  

                                                                                        
                                                                                 

                                                                                               
                                                                                       
                                                                                                  
                                                                                    

                                                                                                 
                                                                               
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011333
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W) (hdim : Module.finrank ℂ W = 1) :
    ∃ χ : AffineGroup K →* ℂˣ, Nonempty (σ.Equiv (characterRepresentation χ)) := by
  classical
                                                                             
  let e : W ≃ₗ[ℂ] ℂ := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some.symm
                                                      
  let c : AffineGroup K → ℂ := fun g => e (σ g (e.symm 1))
  have hcdef : ∀ g, c g = e (σ g (e.symm 1)) := fun _ => rfl
                                                       
  have hkey : ∀ (g : AffineGroup K) (x : W), e (σ g x) = c g * e x := by
    intro g x
    have hx : (e x) • e.symm (1 : ℂ) = x := by
      rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
    rw [hcdef]
    calc e (σ g x) = e (σ g ((e x) • e.symm 1)) := by rw [hx]
      _ = (e x) • e (σ g (e.symm 1)) := by simp only [map_smul]
      _ = e (σ g (e.symm 1)) * e x := by rw [smul_eq_mul, mul_comm]
                                                                 
  have hc1 : c 1 = 1 := by
    have hσ1 : σ (1 : AffineGroup K) = 1 := map_one σ
    rw [hcdef, hσ1]
    simp only [Module.End.one_apply, LinearEquiv.apply_symm_apply]
  have hcmul : ∀ g h : AffineGroup K, c (g * h) = c g * c h := by
    intro g h
    have hmul : σ (g * h) = σ g * σ h := map_mul σ g h
    rw [hcdef, hmul, Module.End.mul_apply, hkey g (σ h (e.symm 1)), ← hcdef h]
  have hcne : ∀ g : AffineGroup K, c g ≠ 0 := by
    intro g hg0
    have h1 : c g * c g⁻¹ = 1 := by rw [← hcmul, mul_inv_cancel, hc1]
    rw [hg0, zero_mul] at h1
    exact zero_ne_one h1
                                                      
  let χ : AffineGroup K →* ℂˣ :=
    { toFun := fun g => Units.mk0 (c g) (hcne g)
      map_one' := by ext; simpa only [Units.val_mk0, Units.val_one] using hc1
      map_mul' := fun g h => by ext; simpa only [Units.val_mk0, Units.val_mul] using hcmul g h }
  have hχval : ∀ g, ((χ g : ℂˣ) : ℂ) = c g := fun _ => rfl
  refine ⟨χ, ⟨Representation.Equiv.mk e (fun g => ?_)⟩⟩
  ext x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [hkey g x]
  change c g * e x = ((χ g : ℂˣ) : ℂ) • (e x)
  rw [hχval, smul_eq_mul]

                                                                                             
                                                                                           
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem AffineGroup.mul_self_eq_one_of_card_eq_two [Fintype K] [DecidableEq K]
    (hq2 : Fintype.card K = 2) (g : AffineGroup K) : g * g = 1 := by
  classical
  haveI : Subsingleton Kˣ :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [Fintype.card_units, hq2])
  have hga : g.linearPart = 1 := Subsingleton.elim _ _
                                                                                           
  have h11 : (1 : K) + 1 = 0 := by
    rcases eq_or_ne ((1 : K) + 1) 0 with h | h
    · exact h
    · exfalso
      have hunit : IsUnit ((1 : K) + 1) := isUnit_iff_ne_zero.mpr h
      obtain ⟨u, hu⟩ := hunit
      have hu1 : ((1 : K) + 1) = 1 := by
        rw [← hu, Subsingleton.elim u 1, Units.val_one]
      have : (1 : K) = 0 := by
        have := add_left_cancel (a := (1 : K)) (show (1 : K) + 1 = 1 + 0 by rw [add_zero]; exact hu1)
        exact this
      exact one_ne_zero this
  ext
  · simp [linearPart_mul, hga]
  · have hbb : g.translationPart + g.translationPart = 0 := by
      have : g.translationPart + g.translationPart = (1 + 1) * g.translationPart := by ring
      rw [this, h11, zero_mul]
    simp only [translationPart_mul, hga, Units.val_one, one_mul, translationPart_one]
    exact hbb

                                                                                                
                                                                                                
                        
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011381 [Fintype K] [DecidableEq K] (hq2 : Fintype.card K = 2) :
    Nat.card (AffineGroup K →* ℂˣ) = 2 := by
  classical
  haveI : Subsingleton Kˣ :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [Fintype.card_units, hq2])
  letI grp : Group (AffineGroup K) := inferInstance
  letI : CommGroup (AffineGroup K) :=
    { grp with
      mul_comm := by
        intro x y
        have hxa : x.linearPart = 1 := Subsingleton.elim _ _
        have hya : y.linearPart = 1 := Subsingleton.elim _ _
        ext
        · simp [hxa, hya]
        · simp only [translationPart_mul, hxa, hya, Units.val_one, one_mul]; ring }
  haveI : NeZero ((Monoid.exponent (AffineGroup K) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (AffineGroup K) ℂ,
    Nat.card_eq_fintype_card, card, hq2]

                                                                                                
                                                                                              
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011384 [Fintype K] [DecidableEq K] (hq2 : Fintype.card K = 2)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule) :
    ∃ χ : AffineGroup K →* ℂˣ, Nonempty (σ.Equiv (characterRepresentation χ)) := by
  have hdim : Module.finrank ℂ W = 1 := by
    rcases simpleRepresentation_011343 σ hσ with h | h
    · exact h
    · rw [h, hq2]
  exact cardinalityFormula_011333 σ hdim

                                                                                              
                                                                                              
                        
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011380 [Fintype K] [DecidableEq K] (hq2 : Fintype.card K = 2) :
    ∃ χ : AffineGroup K →* ℂˣ, Nonempty ((augmentationSubrepresentation (K := K)).toRepresentation.Equiv (characterRepresentation χ)) :=
  cardinalityFormula_011333 _
    (by change Module.finrank ℂ ↥(zeroSumSubmodule K) = 1; rw [cardinalityFormula_011444, hq2])

                                                                                               
                                                                                             
                                                                                                 
                                  
/-- Auxiliary result whose proposition is not displayed in the packet. -/
theorem Auxiliary011383 [Fintype K] [DecidableEq K] (hq2 : Fintype.card K = 2)
    (χ : AffineGroup K →* ℂˣ) :
    χ (1 : AffineGroup K) = 1 ∧ (χ (⟨1, 1⟩ : AffineGroup K) = 1 ∨ χ (⟨1, 1⟩ : AffineGroup K) = -1) := by
  refine ⟨map_one χ, ?_⟩
  set x := χ (⟨1, 1⟩ : AffineGroup K) with hxdef
  have hsq : x * x = 1 := by
    rw [hxdef, ← map_mul, AffineGroup.mul_self_eq_one_of_card_eq_two hq2, map_one]
                                                                                         
  have hsqc : ((x : ℂˣ) : ℂ) * ((x : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hsqc with h | h
  · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))

                                                                                                 
                                                                                                
                                                                                    
                                                                                                  
                           
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011382 [Fintype K] [DecidableEq K] (hq2 : Fintype.card K = 2)
    (χ : AffineGroup K →* ℂˣ) :
    Nonempty ((Representation.tprod (characterRepresentation χ) (characterRepresentation χ)).Equiv (characterRepresentation 1)) := by
  have hsq : χ * χ = 1 := by
    ext g
    have hgg : g * g = 1 := AffineGroup.mul_self_eq_one_of_card_eq_two hq2 g
    have hval : (χ g) * (χ g) = 1 := by rw [← map_mul, hgg, map_one]
    simpa only [MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one]
      using congrArg Units.val hval
  exact ⟨hsq ▸ characterTensorEquiv χ χ⟩

                                                                                         
                                                                                                 
                                                                                             
                                                                                                  
                                                                        
/-- A simplicity statement for the displayed representation or module. -/
theorem simpleRepresentation_011341 [Fintype K] [DecidableEq K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (AffineGroup K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (AffineGroup K)) σ.asModule) :
    (∃ χ : AffineGroup K →* ℂˣ, Nonempty (σ.Equiv (characterRepresentation χ))) ∨
      Nonempty (σ.Equiv (augmentationSubrepresentation (K := K)).toRepresentation) := by
  by_cases hq2 : Fintype.card K = 2
  · exact Or.inl (simpleRepresentation_011384 hq2 σ hσ)
  · have hK : 3 ≤ Fintype.card K := by
      have := Fintype.one_lt_card (α := K); omega
    exact simpleRepresentation_011340 hK σ hσ

end RepresentationTheory.AffineGroupRepresentations
