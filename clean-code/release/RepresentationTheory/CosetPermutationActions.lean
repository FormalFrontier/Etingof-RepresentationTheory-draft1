/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteGroupRepresentation
import RepresentationTheory.Alignment.Attribute

   
                                                

                                                                     
                                                                                             
                                                                                     
                                                                                               
                                                                                     

                                                                                           
                          

             

                                                                                                
                                                                                              
                                                                                            
                                                                                              
                                                                                             
                                                                               
                                                     

                                                                                         
                                                                                             
                                                                                        
                       

                                                  

                                                                                                
                                                                                            
                                                                                              
                                                                   
                                                                                               
                                                                                              
                                                                                              
                                                                                            
                                

               

                                                                                        
                                                                
                                                                          
                                                                                  
                                                 
  

noncomputable section

namespace RepresentationTheory.CosetPermutationActions

open Finset MulAction

                                                                 

                                                                                              
                                                                                               
                                                                                   
                        

section OrbitStabilizer

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {n : ℕ}

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

                                                                                                 
                                                                   
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010990 (act : G →* Equiv.Perm (Fin n)) (i₀ : Fin n)
    (htrans : ∀ j : Fin n, ∃ x : G, act x i₀ = j) :
    n * (univ.filter (fun x : G => act x i₀ = i₀)).card = Fintype.card G := by
  have h := RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011095 act 1 i₀ htrans
  have hfix : (univ.filter (fun i : Fin n => act 1 i = i)).card = n := by
    rw [Finset.filter_true_of_mem (fun i _ => by simp), Finset.card_univ, Fintype.card_fin]
  have hconj : (univ.filter (fun x : G => act (x⁻¹ * 1 * x) i₀ = i₀)).card = Fintype.card G := by
    rw [Finset.filter_true_of_mem (fun x _ => by simp), Finset.card_univ]
  rwa [hfix, hconj] at h

                                                                                              
                         
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010989 (act : G →* Equiv.Perm (Fin n)) (i₀ : Fin n)
    (htrans : ∀ j : Fin n, ∃ x : G, act x i₀ = j) :
    n * Nat.card {g : G // act g i₀ = i₀} = Nat.card G := by
  rw [Nat.card_eq_fintype_card (α := {g : G // act g i₀ = i₀}), Fintype.card_subtype,
    Nat.card_eq_fintype_card (α := G)]
  exact cardinalityFormula_010990 act i₀ htrans

end OrbitStabilizer

                                                

section CosetModel

                                                                                  
                
/-- The homomorphism transporting permutations along the displayed equivalence. -/
def permCongr {X Y : Type*} (e : X ≃ Y) : Equiv.Perm X →* Equiv.Perm Y where
  toFun := e.permCongr
  map_one' := by ext y; simp [Equiv.permCongr_def]
  map_mul' p q := by ext y; simp [Equiv.permCongr_def]

variable {G : Type*} [Group G] (H : Subgroup G) {N : ℕ}

                                                                                             
                                                                
/-- The subgroup specified by the displayed formal signature. -/
def cosetPermutationAction (e : (G ⧸ H) ≃ Fin N) : G →* Equiv.Perm (Fin N) :=
  (permCongr e).comp (MulAction.toPermHom G (G ⧸ H))

/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
@[simp] lemma subgroupRelation_011021 (e : (G ⧸ H) ≃ Fin N) (g : G) (i : Fin N) :
    cosetPermutationAction H e g i = e (g • e.symm i) := rfl

                                                                                            
/-- The permutation action induced from the displayed coset space is transitive. -/
lemma cosetPermutationAction_transitive (e : (G ⧸ H) ≃ Fin N) (i j : Fin N) :
    ∃ g : G, cosetPermutationAction H e g i = j := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.symm i) (e.symm j)
  exact ⟨g, by rw [subgroupRelation_011021, hg, Equiv.apply_symm_apply]⟩

                                                        
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010995 (H : Subgroup G) : Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by
  rw [← Subgroup.index_eq_card]; exact H.index_mul_card

end CosetModel

                         

                                                                                                 
                                                                                              
                                                                                        
                                                                                             
                    

section ModelIndependence

variable {N : ℕ} (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin N)) (i₀ : Fin N)

                                                                                          
/-- The map from the displayed stabilizer quotient to the action space. -/
def cosetToOrbit : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) → Fin N := fun x =>
  Quotient.liftOn' x (fun a => act a i₀) <| by
    intro a b hab
    have hmem : a⁻¹ * b ∈ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀ := QuotientGroup.leftRel_apply.mp hab
    have h1 : act (a⁻¹ * b) i₀ = i₀ := hmem
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_eq] at h1
    exact h1.symm

/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
@[simp] lemma subgroupRelation_011146 (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) :
    cosetToOrbit act i₀ (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) = act a i₀ := rfl

/-- Injectivity of the map displayed in the formal statement. -/
lemma injective_011145 : Function.Injective (cosetToOrbit act i₀) := by
  intro x y h
  induction x using Quotient.inductionOn' with | _ a =>
  induction y using Quotient.inductionOn' with | _ b =>
  have h' : act a i₀ = act b i₀ := h
  refine QuotientGroup.eq.mpr ?_
  change act (a⁻¹ * b) i₀ = i₀
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← h', Equiv.Perm.inv_def,
    Equiv.symm_apply_apply]

/-- Surjectivity of the map displayed in the formal statement. -/
lemma surjective_011147 (htrans : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x i₀ = j) :
    Function.Surjective (cosetToOrbit act i₀) := by
  intro j
  obtain ⟨x, hx⟩ := htrans j
  exact ⟨(x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀), hx⟩

                                                                                              
                                                                                     
/-- An equivalence from the displayed stabilizer quotient to the finite action space. -/
def orbitCosetEquiv (htrans : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x i₀ = j) :
    (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) ≃ Fin N :=
  Equiv.ofBijective _ ⟨injective_011145 act i₀, surjective_011147 act i₀ htrans⟩

/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
@[simp] lemma subgroupRelation_011140 (htrans : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x i₀ = j) (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) :
    orbitCosetEquiv act i₀ htrans (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) = act a i₀ := rfl

                                                                             
/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
lemma subgroupRelation_011141 (htrans : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x i₀ = j)
    (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) :
    orbitCosetEquiv act i₀ htrans (g • x) = act g (orbitCosetEquiv act i₀ htrans x) := by
  induction x using Quotient.inductionOn' with | _ a =>
  change act (g * a) i₀ = act g (act a i₀)
  rw [map_mul, Equiv.Perm.mul_apply]

                                                                                   
/-- A pointwise identity for the displayed group action. -/
lemma actionFormula_011142 (htrans : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x i₀ = j)
    (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (i : Fin N) :
    (orbitCosetEquiv act i₀ htrans).symm (act g i)
      = g • (orbitCosetEquiv act i₀ htrans).symm i := by
  apply (orbitCosetEquiv act i₀ htrans).injective
  rw [Equiv.apply_symm_apply, subgroupRelation_011141, Equiv.apply_symm_apply]

variable {act i₀}

                                                                                          
                                                                                             
                                 
/-- The subgroup specified by the displayed formal signature. -/
def conjugateCosetEquiv {H₁ H₂ : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983} (c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983)
    (hc : ∀ y : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, y ∈ H₂ ↔ c⁻¹ * y * c ∈ H₁) : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁) ≃ (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂) where
  toFun x := Quotient.liftOn' x (fun a => ((a * c⁻¹ : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂)) <| by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H₁ := QuotientGroup.leftRel_apply.mp hab
    refine QuotientGroup.eq.mpr ?_
    rw [hc]
    rw [show c⁻¹ * ((a * c⁻¹)⁻¹ * (b * c⁻¹)) * c = a⁻¹ * b by group]
    exact hmem
  invFun x := Quotient.liftOn' x (fun a => ((a * c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁)) <| by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H₂ := QuotientGroup.leftRel_apply.mp hab
    rw [hc] at hmem
    refine QuotientGroup.eq.mpr ?_
    rw [show (a * c)⁻¹ * (b * c) = c⁻¹ * (a⁻¹ * b) * c by group]
    exact hmem
  left_inv x := by
    induction x using Quotient.inductionOn' with | _ a =>
    change ((a * c⁻¹ * c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁) = (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁)
    rw [inv_mul_cancel_right]
  right_inv x := by
    induction x using Quotient.inductionOn' with | _ a =>
    change ((a * c * c⁻¹ : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂) = (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂)
    rw [mul_inv_cancel_right]

/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
@[simp] lemma subgroupRelation_011160 {H₁ H₂ : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983} (c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983)
    (hc : ∀ y : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, y ∈ H₂ ↔ c⁻¹ * y * c ∈ H₁) (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) :
    conjugateCosetEquiv c hc (a : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁) = ((a * c⁻¹ : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂) := rfl

/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
lemma subgroupRelation_011161 {H₁ H₂ : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983} (c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983)
    (hc : ∀ y : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, y ∈ H₂ ↔ c⁻¹ * y * c ∈ H₁) (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₁) :
    conjugateCosetEquiv c hc (g • x) = g • conjugateCosetEquiv c hc x := by
  induction x using Quotient.inductionOn' with | _ a =>
  change ((g * a * c⁻¹ : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂) = ((g * (a * c⁻¹) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H₂)
  rw [mul_assoc]

                                                                                                
                                                                                     
/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
theorem subgroupRelation_011054 [NeZero N] {H : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983} (e : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ H) ≃ Fin N)
    (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin N)) (htrans : ∀ i j : Fin N, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act g i = j)
    (c : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (hc : ∀ y : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, y ∈ H ↔ c⁻¹ * y * c ∈ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act 0) :
    ∃ φ : Fin N ≃ Fin N, ∀ (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (i : Fin N), φ (act g i) = cosetPermutationAction H e g (φ i) := by
  have htrans0 : ∀ j : Fin N, ∃ x : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act x 0 = j := fun j => htrans 0 j
  set ψ := orbitCosetEquiv act 0 htrans0 with hψ
  set χ := conjugateCosetEquiv c hc with hχ
  refine ⟨(ψ.symm.trans χ).trans e, fun g i => ?_⟩
  change e (χ (ψ.symm (act g i))) = cosetPermutationAction H e g (e (χ (ψ.symm i)))
  rw [actionFormula_011142 act 0 htrans0, hχ, subgroupRelation_011161,
    subgroupRelation_011021, Equiv.symm_apply_apply]

end ModelIndependence

                                   

                                                                                               
                                                                                              
                                           

section Icosahedron

                            

                                                                                        
/-- The subgroup specified by the displayed formal signature. -/
def orderFiveSubgroup : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 := Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3)

                                                                                      
/-- The subgroup specified by the displayed formal signature. -/
def orderThreeSubgroup : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 := Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1)

                                                                                                
                                           
/-- The subgroup specified by the displayed formal signature. -/
def orderTwoSubgroup : Subgroup RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 := Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2)

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010999 : Nat.card orderFiveSubgroup = 5 := by
  rw [orderFiveSubgroup, Nat.card_zpowers, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011120]

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010988 : Nat.card orderThreeSubgroup = 3 := by
  rw [orderThreeSubgroup, Nat.card_zpowers, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011118]

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010987 : Nat.card orderTwoSubgroup = 2 := by
  rw [orderTwoSubgroup, Nat.card_zpowers, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011119]

                                                                           
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010996 : Nat.card (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderFiveSubgroup) = 12 := by
  have h := cardinalityFormula_010995 orderFiveSubgroup
  rw [cardinalityFormula_010999, RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                                                        
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010993 : Nat.card (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderThreeSubgroup) = 20 := by
  have h := cardinalityFormula_010995 orderThreeSubgroup
  rw [cardinalityFormula_010988, RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                                                           
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010991 : Nat.card (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderTwoSubgroup) = 30 := by
  have h := cardinalityFormula_010995 orderTwoSubgroup
  rw [cardinalityFormula_010987, RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                                                       
/-- The equivalence specified by the displayed formal signature. -/
def indexTwelveCosetEquiv : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderFiveSubgroup) ≃ Fin 12 := Finite.equivFinOfCardEq cardinalityFormula_010996

                                                                    
/-- The equivalence specified by the displayed formal signature. -/
def indexTwentyCosetEquiv : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderThreeSubgroup) ≃ Fin 20 := Finite.equivFinOfCardEq cardinalityFormula_010993

                                                                    
/-- The equivalence specified by the displayed formal signature. -/
def indexThirtyCosetEquiv : (RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 ⧸ orderTwoSubgroup) ≃ Fin 30 := Finite.equivFinOfCardEq cardinalityFormula_010991

                                                                                             
/-- The monoid homomorphism specified by the displayed formal signature. -/
def indexTwelveAction : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 12) := cosetPermutationAction orderFiveSubgroup indexTwelveCosetEquiv

                                                                                           
/-- The monoid homomorphism specified by the displayed formal signature. -/
def indexTwentyAction : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 20) := cosetPermutationAction orderThreeSubgroup indexTwentyCosetEquiv

                                                                                           
/-- The monoid homomorphism specified by the displayed formal signature. -/
def indexThirtyAction : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 30) := cosetPermutationAction orderTwoSubgroup indexThirtyCosetEquiv

/-- The displayed action on twelve points is transitive. -/
lemma indexTwelveAction_transitive : ∀ i j : Fin 12, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, indexTwelveAction g i = j :=
  cosetPermutationAction_transitive orderFiveSubgroup indexTwelveCosetEquiv

/-- The displayed action on twenty points is transitive. -/
lemma indexTwentyAction_transitive : ∀ i j : Fin 20, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, indexTwentyAction g i = j :=
  cosetPermutationAction_transitive orderThreeSubgroup indexTwentyCosetEquiv

/-- The displayed action on thirty points is transitive. -/
lemma indexThirtyAction_transitive : ∀ i j : Fin 30, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, indexThirtyAction g i = j :=
  cosetPermutationAction_transitive orderTwoSubgroup indexThirtyCosetEquiv

                                                                                  
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011187 (i : Fin 12) : Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // indexTwelveAction g i = i} = 5 := by
  have h := cardinalityFormula_010989 indexTwelveAction i (fun j => indexTwelveAction_transitive i j)
  rw [RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                                                             
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011067 (i : Fin 20) : Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // indexTwentyAction g i = i} = 3 := by
  have h := cardinalityFormula_010989 indexTwentyAction i (fun j => indexTwentyAction_transitive i j)
  rw [RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                                                             
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011028 (i : Fin 30) : Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // indexThirtyAction g i = i} = 2 := by
  have h := cardinalityFormula_010989 indexThirtyAction i (fun j => indexThirtyAction_transitive i j)
  rw [RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_010986] at h
  omega

                                               

                                                                                                
                                                                                                 
                                                                                                  
                                                                                                  
                                                                                       
                                                                                                 
                                                                                         

                                                                                               
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010998 {N p : ℕ} (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin N)) (i₀ : Fin N)
    (hstab : Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // act g i₀ = i₀} = p) : Nat.card (RepresentationTheory.FiniteGroupRepresentation.pointStabilizer act i₀) = p := by
  rw [← hstab]
  exact Nat.card_congr (Equiv.subtypeEquivRight (RepresentationTheory.FiniteGroupRepresentation.actionFormula_011110 act i₀))

                                                                                               
                                                                         
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := supporting)]
theorem cardinalityFormula_011190 (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // act g i = i} = 5) :
    ∃ φ : Fin 12 ≃ Fin 12, ∀ (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (i : Fin 12), φ (act g i) = indexTwelveAction g (φ i) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011053 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) RepresentationTheory.FiniteGroupRepresentation.orderFormula_011120 RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011084
    (cardinalityFormula_010998 act 0 (hstab 0))
  exact subgroupRelation_011054 indexTwelveCosetEquiv act htrans c hc

                                                                                             
                                                                      
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := supporting)]
theorem cardinalityFormula_011070 (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // act g i = i} = 3) :
    ∃ φ : Fin 20 ≃ Fin 20, ∀ (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (i : Fin 20), φ (act g i) = indexTwentyAction g (φ i) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011053 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) RepresentationTheory.FiniteGroupRepresentation.orderFormula_011118 RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011083
    (cardinalityFormula_010998 act 0 (hstab 0))
  exact subgroupRelation_011054 indexTwentyCosetEquiv act htrans c hc

                                                                                             
                                                                      
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := supporting)]
theorem cardinalityFormula_011031 (act : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983 // act g i = i} = 2) :
    ∃ φ : Fin 30 ≃ Fin 30, ∀ (g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983) (i : Fin 30), φ (act g i) = indexThirtyAction g (φ i) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011044 act (cardinalityFormula_010998 act 0 (hstab 0))
  exact subgroupRelation_011054 indexThirtyCosetEquiv act htrans c hc

                                          

                                                                                              
                                                                                            
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := primary)]
theorem cardinalityFormula_011198 :
    ∃ (S : Fin 4 → Submodule ℂ (Fin 12 → ℂ))
      (hS : ∀ k, ∀ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, ∀ v ∈ S k, RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwelveAction g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, RepresentationTheory.FiniteGroupRepresentation.IsIrreducibleSubmodule (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwelveAction) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 5 ∧
      ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwelveAction) (S 1) (hS 1) g
        ≠ RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwelveAction) (S 2) (hS 2) g :=
  RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011191 indexTwelveAction indexTwelveAction_transitive cardinalityFormula_011187

                                                                                             
                                                                           
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := primary)]
theorem cardinalityFormula_011082 :
    ∃ (S : Fin 6 → Submodule ℂ (Fin 20 → ℂ))
      (hS : ∀ k, ∀ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, ∀ v ∈ S k, RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwentyAction g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, RepresentationTheory.FiniteGroupRepresentation.IsIrreducibleSubmodule (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwentyAction) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwentyAction) (S 1) (hS 1) g
        ≠ RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexTwentyAction) (S 2) (hS 2) g :=
  RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011071 indexTwentyAction indexTwentyAction_transitive cardinalityFormula_011067

                                                                                             
                                                                            
/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.5" (role := primary)]
theorem cardinalityFormula_011043 :
    ∃ (S : Fin 8 → Submodule ℂ (Fin 30 → ℂ))
      (hS : ∀ k, ∀ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, ∀ v ∈ S k, RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexThirtyAction g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, RepresentationTheory.FiniteGroupRepresentation.IsIrreducibleSubmodule (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexThirtyAction) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      Module.finrank ℂ (S 6) = 5 ∧ Module.finrank ℂ (S 7) = 5 ∧
      ∃ g : RepresentationTheory.FiniteGroupRepresentation.AuxiliaryType010983, RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexThirtyAction) (S 1) (hS 1) g
        ≠ RepresentationTheory.FiniteGroupRepresentation.restrictedCharacter (RepresentationTheory.FiniteGroupRepresentation.permutationRepresentation indexThirtyAction) (S 2) (hS 2) g :=
  RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011032 indexThirtyAction indexThirtyAction_transitive cardinalityFormula_011028

end Icosahedron

end RepresentationTheory.CosetPermutationActions
