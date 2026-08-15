/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.DirectSum.Finsupp
import RepresentationTheory.PolynomialQuotientZModAuxiliary

   
                                                                               

                                                                                         
                                                                                        
                                                                                              
                                                                                            
                                                                                           
                                                                                
                                                                                            

                                                                                                 
                                                                                       

                                                                                                 
                                                                                               
                                                          
                                                                                        
                                                                                              
                                                                         
                                                                                                 
                                                                                 
                                                                                                 
                                                                                      
                                                                                               
                                                                                            
                                
                                                                                           
                                                                                                   
                                                                                               
                                                                                                 

                                                                                             
                            

                  

                                                                                                 
                                                                                                 
                                                                                          
                                                               
  

namespace RepresentationTheory.Algebra.Module.DirectSumData

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

                                             

                                                                                              
                                                                                               
                                                                                                
                                                      

                                                                    
/-- A ring equivalence from the opposite of a commutative ring to the ring. -/
def commRingOppositeEquiv (A : Type u) [CommRing A] : Aᵐᵒᵖ ≃+* A where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := mul_comm _ _
  map_add' _ _ := rfl

/-- The commutative-ring opposite equivalence sends an opposite element to its underlying element. -/
@[simp] lemma commRingOppositeEquiv_apply (A : Type u) [CommRing A] (x : Aᵐᵒᵖ) :
    commRingOppositeEquiv A x = MulOpposite.unop x := rfl

/-- The ring homomorphism underlying the commutative-ring opposite equivalence equals the homomorphism from the opposite induced by the identity. -/
lemma commRingOppositeEquiv_toRingHom (A : Type u) [CommRing A] :
    (commRingOppositeEquiv A).toRingHom = (RingHom.id A).fromOpposite fun x y => mul_comm x y := rfl

                                                                                               
                                                                                                  
                                                                      
/-- A functor from modules over a commutative ring to modules over its opposite ring. -/
noncomputable def commRingModuleToOpposite (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.restrictScalars (commRingOppositeEquiv A).toRingHom

                                                                                             
/-- A module over a commutative ring, viewed as a module object over the opposite ring. -/
noncomputable def commRingModuleAsOpposite (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  (commRingModuleToOpposite A).obj (ModuleCat.of A M)

                                                                                              
                                                                                  
                                                                                                 
                                                                                             
/-- The opposite-ring module object associated with a module equals that module viewed directly as an opposite-ring module object. -/
lemma commRingModuleAsOpposite_eq (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] :
    letI : Module Aᵐᵒᵖ M := Module.compHom M ((RingHom.id A).fromOpposite fun x y => mul_comm x y)
    commRingModuleAsOpposite A M = ModuleCat.of Aᵐᵒᵖ M := rfl

/-- The functor from modules over a commutative ring to modules over its opposite ring is additive. -/
instance commRingModuleToOpposite_additive (A : Type u) [CommRing A] : (commRingModuleToOpposite A).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive

/-- The functor from modules over a commutative ring to modules over its opposite ring is an equivalence. -/
instance commRingModuleToOpposite_isEquivalence (A : Type u) [CommRing A] : (commRingModuleToOpposite A).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars (commRingOppositeEquiv A).toRingHom).IsEquivalence

/-- The functor from modules over a commutative ring to modules over its opposite ring preserves biproducts indexed by finite types. -/
instance commRingModuleToOpposite_preservesBiproduct (A : Type u) [CommRing A] {J : Type u} [Finite J] (f : J → ModuleCat.{u} A) :
    PreservesBiproduct f (commRingModuleToOpposite A) :=
  preservesBiproduct_of_preservesProduct _

                                          

                                                                                               
                                                                                              
                                                                                          
/-- Data parameterized by a module over a commutative ring. -/
structure Module.DirectSumData (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] where
                                   
  /-- The natural-number parameter associated with the direct-sum data. -/
  natParameter : ℕ
                                                       
  /-- The type of indices associated with the direct-sum data. -/
  Index : Type u
                                                         
  /-- A finite-type instance for the index type. -/
  instFintypeIndex : Fintype Index
                                                                                                 
  /-- A decidable equality instance for the index type. -/
  instDecidableEqIndex : DecidableEq Index
                                                                       
  /-- The ring element used to generate the principal ideal for an index. -/
  quotientGenerator : Index → A
                                                                                              
                               
  /-- A linear equivalence from the module to a product of a finite-indexed function type and a family of principal-ideal quotients. -/
  linearEquivFinFunProdQuotient :
    M ≃ₗ[A] ((Fin natParameter → A) × ((i : Index) → A ⧸ Ideal.span {quotientGenerator i}))

namespace Module.DirectSumData

attribute [instance] instFintypeIndex instDecidableEqIndex

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

                                                                                               
                   
/-- The type indexing the summands associated with the direct-sum data. -/
protected abbrev summandIndex (D : Module.DirectSumData A M) : Type u := Fin D.natParameter ⊕ D.Index

                                                                                             
                                                                                                
/-- The module object associated with a summand index. -/
def summand (D : Module.DirectSumData A M) : D.summandIndex → ModuleCat.{u} A :=
  Sum.elim (fun _ => ModuleCat.of A A) fun i => ModuleCat.of A (A ⧸ Ideal.span {D.quotientGenerator i})

/-- At a left index, the summand equals the ring viewed as a module over itself. -/
@[simp] lemma summand_inl (D : Module.DirectSumData A M) (i : Fin D.natParameter) :
    D.summand (Sum.inl i) = ModuleCat.of A A := rfl

/-- At a right index, the summand equals the corresponding principal-ideal quotient module. -/
@[simp] lemma summand_inr (D : Module.DirectSumData A M) (i : D.Index) :
    D.summand (Sum.inr i) = ModuleCat.of A (A ⧸ Ideal.span {D.quotientGenerator i}) := rfl

open DirectSum in
                                                                               
/-- A linear equivalence from the module to the direct sum of the carriers of its summand objects. -/
noncomputable def linearEquivDirectSum (D : Module.DirectSumData A M) :
    M ≃ₗ[A] ⨁ j, (D.summand j : Type u) :=
  D.linearEquivFinFunProdQuotient ≪≫ₗ
    (LinearEquiv.sumPiEquivProdPi A (Fin D.natParameter) D.Index
      (fun j => (D.summand j : Type u))).symm ≪≫ₗ
    (DirectSum.linearEquivFunOnFintype A D.summandIndex (fun j => (D.summand j : Type u))).symm

                                                                                           
/-- An isomorphism from the module object to the biproduct of its summand objects. -/
noncomputable def moduleIsoBiproduct (D : Module.DirectSumData A M) :
    ModuleCat.of A M ≅ biproduct D.summand :=
  D.linearEquivDirectSum.toModuleIso ≪≫ (ModuleCat.coprodIsoDirectSum D.summand).symm ≪≫
    (biproduct.isoCoproduct D.summand).symm

                                                   

                                                                                                
                                                                                              
             
/-- The opposite-ring module object associated with a summand index. -/
noncomputable def oppositeSummand (D : Module.DirectSumData A M) : D.summandIndex → ModuleCat.{u} Aᵐᵒᵖ :=
  (commRingModuleToOpposite A).obj ∘ D.summand

/-- At a left index, the opposite-ring summand equals the opposite-ring module object associated with the ring acting on itself. -/
@[simp] lemma oppositeSummand_inl (D : Module.DirectSumData A M) (i : Fin D.natParameter) :
    D.oppositeSummand (Sum.inl i) = commRingModuleAsOpposite A A := rfl

/-- At a right index, the opposite-ring summand equals the opposite-ring module object associated with the corresponding principal-ideal quotient. -/
@[simp] lemma oppositeSummand_inr (D : Module.DirectSumData A M) (i : D.Index) :
    D.oppositeSummand (Sum.inr i) = commRingModuleAsOpposite A (A ⧸ Ideal.span {D.quotientGenerator i}) := rfl

                                                                                          
                                 
/-- An isomorphism from the associated opposite-ring module object to a biproduct of opposite-ring module objects. -/
noncomputable def oppositeModuleIsoBiproduct (D : Module.DirectSumData A M) :
    commRingModuleAsOpposite A M ≅ biproduct D.oppositeSummand :=
  (commRingModuleToOpposite A).mapIso D.moduleIsoBiproduct ≪≫ (commRingModuleToOpposite A).mapBiproduct D.summand

                    

end Module.DirectSumData

                                                                                        
                                                                      
                                                                                            
              
/-- A finite module over a commutative principal ideal domain has nonempty direct-sum data. -/
theorem nonempty_directSumData (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Nonempty (Module.DirectSumData A M) := by
  classical
  obtain ⟨n, ι, hι, p, -, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum A M
  refine ⟨{ natParameter := n
            Index := ι
            instFintypeIndex := hι
            instDecidableEqIndex := Classical.decEq ι
            quotientGenerator := fun i => p i ^ e i
            linearEquivFinFunProdQuotient := f ≪≫ₗ ?_ }⟩
  exact LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite A A (Fin n))
    (DirectSum.linearEquivFunOnFintype A ι fun i => A ⧸ Ideal.span {p i ^ e i})

                                                                                                
                          
/-- A finite integer module has nonempty direct-sum data. -/
theorem nonempty_intDirectSumData (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    Nonempty (Module.DirectSumData ℤ M) :=
  nonempty_directSumData ℤ M

open Polynomial in
                                                                                                 
                             
/-- A finite module over a univariate polynomial ring over a field has nonempty direct-sum data. -/
theorem nonempty_polynomialDirectSumData {k : Type u} [Field k] (M : Type u) [AddCommGroup M]
    [Module k[X] M] [Module.Finite k[X] M] : Nonempty (Module.DirectSumData k[X] M) :=
  nonempty_directSumData k[X] M

                                                            

                                                                                             
                                                                                                 
                                                                                                   
                                                           

attribute [local instance] RepresentationTheory.PolynomialQuotientZModAuxiliary.zModOppositeIntModule RepresentationTheory.PolynomialQuotientZModAuxiliary.quotientOppositePolynomialModule

                                                                                              
                                          
/-- A linear equivalence between the integers modulo the ideal generated by a natural number and the corresponding modular integers. -/
noncomputable def intQuotientSpanNatCastLinearEquivZMod (a : ℕ) : (ℤ ⧸ Ideal.span {(a : ℤ)}) ≃ₗ[ℤ] ZMod a :=
  (Int.quotientSpanNatEquivZMod a).toAddEquiv.toIntLinearEquiv

                                                                                               
                                                       
/-- An isomorphism between the integer-module objects of a principal quotient and the corresponding modular integers. -/
noncomputable def intQuotientSpanNatCastModuleIsoZMod (a : ℕ) :
    ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(a : ℤ)}) ≅ ModuleCat.of ℤ (ZMod a) :=
  (intQuotientSpanNatCastLinearEquivZMod a).toModuleIso

                                                                                                
                                                                                                 
                      
/-- An isomorphism from the opposite-ring module object associated with an integer principal quotient to the corresponding modular-integer module object. -/
noncomputable def intQuotientSpanNatCastOppositeModuleIsoZMod (a : ℕ) :
    commRingModuleAsOpposite ℤ (ℤ ⧸ Ideal.span {(a : ℤ)}) ≅ ModuleCat.of ℤᵐᵒᵖ (ZMod a) :=
  (commRingModuleToOpposite ℤ).mapIso (intQuotientSpanNatCastModuleIsoZMod a)

                                                                                        
                                                                            
/-- An isomorphism between the opposite-ring module object associated with a commutative ring acting on itself and its direct opposite-ring module object. -/
noncomputable def regularModuleAsOppositeIso (A : Type u) [CommRing A] : commRingModuleAsOpposite A A ≅ ModuleCat.of Aᵐᵒᵖ A where
  hom := ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' c x := mul_comm (MulOpposite.unop c) x }
  inv := ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' c x := mul_comm x (MulOpposite.unop c) }
  hom_inv_id := rfl
  inv_hom_id := rfl

open Polynomial in
                                                                                           
                                                                                             
              
/-- An isomorphism between the opposite-ring module object associated with a polynomial principal quotient and that quotient viewed directly as an opposite-ring module. -/
noncomputable def polynomialQuotientOppositeModuleIso {k : Type u} [Field k] (f : k[X]) :
    commRingModuleAsOpposite k[X] (k[X] ⧸ Ideal.span {f}) ≅ ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f}) :=
  Iso.refl _

                          

                                                                                           
             
/-- Direct-sum data for the integer module given by the product of the integers and integers modulo four. -/
noncomputable def intProdZModFourDirectSumData : Module.DirectSumData ℤ (ℤ × ZMod 4) where
  natParameter := 1
  Index := Fin 1
  instFintypeIndex := inferInstance
  instDecidableEqIndex := inferInstance
  quotientGenerator _ := ((4 : ℕ) : ℤ)
  linearEquivFinFunProdQuotient :=
    LinearEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
      ((intQuotientSpanNatCastLinearEquivZMod 4).symm ≪≫ₗ
        (LinearEquiv.piUnique ℤ fun _ : Fin 1 => ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}).symm)

                                                                                            
        
/-- Direct-sum data for the integer module of integers modulo six. -/
noncomputable def zmodSixDirectSumData : Module.DirectSumData ℤ (ZMod 6) where
  natParameter := 0
  Index := Fin 1
  instFintypeIndex := inferInstance
  instDecidableEqIndex := inferInstance
  quotientGenerator _ := ((6 : ℕ) : ℤ)
  linearEquivFinFunProdQuotient :=
    (intQuotientSpanNatCastLinearEquivZMod 6).symm ≪≫ₗ
      (LinearEquiv.piUnique ℤ fun _ : Fin 1 => ℤ ⧸ Ideal.span {((6 : ℕ) : ℤ)}).symm ≪≫ₗ
      (LinearEquiv.uniqueProd (R := ℤ) (M₂ := Fin 0 → ℤ)).symm

noncomputable section Examples

                                                                                                 
example : intProdZModFourDirectSumData.summand (Sum.inl (0 : Fin 1)) = ModuleCat.of ℤ ℤ := rfl

example : intProdZModFourDirectSumData.summand (Sum.inr (0 : Fin 1))
    = ModuleCat.of ℤ (ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}) := rfl

                                                                                             
                                                                                          
example : ModuleCat.of ℤ (ℤ × ZMod 4) ≅ biproduct intProdZModFourDirectSumData.summand :=
  intProdZModFourDirectSumData.moduleIsoBiproduct

example : commRingModuleAsOpposite ℤ (ℤ × ZMod 4) ≅ biproduct intProdZModFourDirectSumData.oppositeSummand :=
  intProdZModFourDirectSumData.oppositeModuleIsoBiproduct

                                                                                                
                                                                             
example : intProdZModFourDirectSumData.summand (Sum.inr (0 : Fin 1)) ≅ ModuleCat.of ℤ (ZMod 4) :=
  intQuotientSpanNatCastModuleIsoZMod 4

example : intProdZModFourDirectSumData.oppositeSummand (Sum.inr (0 : Fin 1)) ≅ ModuleCat.of ℤᵐᵒᵖ (ZMod 4) :=
  intQuotientSpanNatCastOppositeModuleIsoZMod 4

example : intProdZModFourDirectSumData.oppositeSummand (Sum.inl (0 : Fin 1)) ≅ ModuleCat.of ℤᵐᵒᵖ ℤ :=
  regularModuleAsOppositeIso ℤ

                                                    
example : zmodSixDirectSumData.summandIndex ≃ Fin 1 := Equiv.emptySum (Fin 0) (Fin 1)

end Examples

end RepresentationTheory.Algebra.Module.DirectSumData
