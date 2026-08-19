/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.FDRep.Biproduct
import RepresentationTheory.TensorSquareSpectralDecomposition
import RepresentationTheory.RepresentationTensorDecompositions
import RepresentationTheory.FiniteGroupRepresentation
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Group.CharacterDuality
import RepresentationTheory.Group.CharacterOperations
import RepresentationTheory.Alignment.Attribute
   
                                                 

                                                                                             
                                                    

                                                      

                

                                                                                              
                                        
                                                                                            
                                                                               
                                                                         
                                                     

                                      
                         
                                                
                                                
                                                
                                                
                                                

                                     

                                                                                        
                                                                                  
                                                                                         
                                                                                             
                                                                                         
                                                                                              
                                                                                               
                                                                                          
                                                                                           
                                                                                         
                            

                                                                                     

                                                                      
                                                                                      
                                         
                                                                    
                                                                                    
                                              
                                                                            
                                                                                 
                                                                                      
                                                                                              
                                                                                     
                                              
                                                                            
                                                                          
                               
                                         
                                                                                   
                                                                      
                                                     

                                                                                            
                                                                                 
                                                                 
                                                                          
                                               
  

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Module _root_.Finset

open scoped Pointwise

noncomputable section

namespace RepresentationTheory.FiniteGroupDegreeFiveCharacters

                                                                                             
/-- An auxiliary ambient type. -/
abbrev Auxiliary.ambientType : Type := ↥(alternatingGroup (Fin 5))

                                                                                         
                                                                                 
/-- An auxiliary construction from a finite-dimensional complex representation of a subgroup to one of the ambient type. -/
abbrev Auxiliary.representationConstruction {H : Subgroup Auxiliary.ambientType} (σ : FDRep ℂ ↥H) : FDRep ℂ Auxiliary.ambientType :=
  FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H σ.ρ)


                                             

                                                                                         
                                                                                              
                                                                           

                                                                          
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012086 {H : Subgroup Auxiliary.ambientType} [DecidablePred (· ∈ H)] (σ : FDRep ℂ ↥H) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g
      = (Fintype.card ↥H : ℂ)⁻¹ *
          ∑ x : Auxiliary.ambientType, if h : x * g * x⁻¹ ∈ H then σ.character ⟨x * g * x⁻¹, h⟩ else 0 := by
  have hchar : (Auxiliary.representationConstruction σ).character g
      = LinearMap.trace ℂ (Representation.IndV H.subtype σ.ρ)
          (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H σ.ρ g) := rfl
  rw [hchar, RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H σ.ρ g]
  rfl

                                                                  
/-- When an element has order equal to a natural number, the filter of conjugating elements whose conjugate of a given element lies in its cyclic subgroup equals the filter of conjugating elements whose conjugate lies among the powers indexed below that number. -/
lemma filter_conjugating_elements_conj_mem_zpowers_eq_filter_conj_mem_powers_range (a g : Auxiliary.ambientType) (m : ℕ) (h : orderOf a = m) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ Subgroup.zpowers a))
      = (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ (Finset.range m).image (a ^ ·))) := by
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact RepresentationTheory.FiniteGroupRepresentation.orderFormula_011112 a m h _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                                             
/-- For indexed representatives, the numbers of conjugating elements whose conjugate of the representative lies in the cyclic subgroup generated by representative two form the vector (60, 0, 4, 0, 0). -/
lemma card_conjugating_elements_conj_representative_mem_zpowers_rep_two (j : Fin 5) :
    (univ.filter
        (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2))).card
      = ![60, 0, 4, 0, 0] j := by
  rw [filter_conjugating_elements_conj_mem_zpowers_eq_filter_conj_mem_powers_range (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 2 RepresentationTheory.FiniteGroupRepresentation.orderFormula_011119]
  fin_cases j <;> decide

                                                                                     
                                      
/-- Every subgroup of cardinality two is conjugate, in the displayed membership sense, to the cyclic subgroup generated by representative two. -/
lemma exists_conjugate_zpowers_rep_two_of_subgroup_card_two (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 2) :
    ∃ d : Auxiliary.ambientType, ∀ y : Auxiliary.ambientType, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) := by
  haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; norm_num)
  obtain ⟨s, hs_mem, hs_ne⟩ := H.nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 2 := by
    rw [← hH]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : H)
    rwa [Subgroup.orderOf_mk] at this
  have hord2 : orderOf s = 2 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs2 : s ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one s
  have hcl : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 2 := RepresentationTheory.FiniteGroupRepresentation.valueFormula_011000 s hs2 hs_ne
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative s
  rw [hcl] at hc
  have hzs : Subgroup.zpowers s = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord2, hH]
  refine ⟨c⁻¹, fun y => ?_⟩
  have hHeq : H = MulAut.conj c • Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) := by
    rw [RepresentationTheory.FiniteGroupRepresentation.subgroupRelation_011010, hc, hzs]
  rw [hHeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]

                                                                                            
/-- For a subgroup of cardinality two, the number of conjugating elements whose conjugate of a given element lies in it equals the corresponding count for the cyclic subgroup generated by representative two. -/
lemma card_conjugating_elements_conj_mem_eq_zpowers_rep_two_of_card_two (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2) (g : Auxiliary.ambientType) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2))).card := by
  obtain ⟨d, hd⟩ := exists_conjugate_zpowers_rep_two_of_subgroup_card_two H hH
  apply Finset.card_bij' (fun x _ => d * x) (fun x _ => d⁻¹ * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd] at hx
    rw [show d * x * g * (d * x)⁻¹ = d * (x * g * x⁻¹) * d⁻¹ by group]
    exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd]
    rw [show d * (d⁻¹ * x * g * (d⁻¹ * x)⁻¹) * d⁻¹ = x * g * x⁻¹ by group]
    exact hx
  · intro x hx; group
  · intro x hx; group

                                                                                              
                                                                    
/-- On indexed representatives, the character of the auxiliary construction applied to a constant-character-one representation of a subgroup of cardinality two has values (30, 0, 2, 0, 0). -/
lemma auxiliary_construction_character_representative_of_card_two_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![30, 0, 2, 0, 0] j := by
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 2 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, card_conjugating_elements_conj_mem_eq_zpowers_rep_two_of_card_two H hH, card_conjugating_elements_conj_representative_mem_zpowers_rep_two, hcard]
  fin_cases j <;> norm_num

                                                                               
/-- The character of the auxiliary construction applied to a representation with constant character one on a subgroup of cardinality two has class values (30, 0, 2, 0, 0). -/
lemma auxiliary_construction_character_of_card_two_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![30, 0, 2, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact auxiliary_construction_character_representative_of_card_two_character_one H hH σ htriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                      
/-- On indexed representatives, the displayed iterated biproduct has character vector (30, 0, 2, 0, 0). -/
lemma character_auxiliaryBiprod_card_two_representative (j : Fin 5) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character
        (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![30, 0, 2, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_zero, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- The displayed iterated biproduct has character values (30, 0, 2, 0, 0), selected by class index. -/
lemma character_auxiliaryBiprod_card_two (g : Auxiliary.ambientType) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![30, 0, 2, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact character_auxiliaryBiprod_card_two_representative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                 

                                                                                              
                                                                                         
/-- The auxiliary construction applied to a simple representation with constant character one on a subgroup of cardinality two is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_character_one_card_two_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅
      RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [auxiliary_construction_character_of_card_two_character_one H hH σ htriv g, character_auxiliaryBiprod_card_two g]

                             

                                                                                           
                                                                                                
                                                                                                
                                                                                                
                                  

                                                                                             
                                                                                   
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012116 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    ∀ x : ↥H, σ.character x = if x = 1 then (1 : ℂ) else -1 := by
  classical
                                                               
  obtain ⟨t', ht'ne, ht'all⟩ : ∃ t' : ↥H, t' ≠ 1 ∧ ∀ x : ↥H, x = 1 ∨ x = t' := by
    obtain ⟨a, b, hab, hpair⟩ := Nat.card_eq_two_iff.mp hH
    have hmem : ∀ z : ↥H, z = a ∨ z = b := by
      intro z
      have hz : z ∈ ({a, b} : Set ↥H) := by rw [hpair]; exact Set.mem_univ z
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hmem 1 with h1 | h1
    · refine ⟨b, fun hb => hab (h1.symm.trans hb.symm), fun x => ?_⟩
      rcases hmem x with hx | hx
      · exact Or.inl (hx.trans h1.symm)
      · exact Or.inr hx
    · refine ⟨a, fun ha => hab (ha.trans h1), fun x => ?_⟩
      rcases hmem x with hx | hx
      · exact Or.inr hx
      · exact Or.inl (hx.trans h1.symm)
                                                                  
  have hself : ∀ h : ↥H, h * h = 1 := fun h => by
    have hpow : h ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hH ▸ orderOf_dvd_natCard h)
    rwa [pow_two] at hpow
  have hinv : ∀ h : ↥H, h⁻¹ = h := fun h => inv_eq_of_mul_eq_one_right (hself h)
  have ht'2 : t' * t' = 1 := hself t'
                                                  
  have hnorm : ∑ h : ↥H, σ.character h * σ.character h⁻¹ = (Nat.card ↥H : ℂ) :=
    (FDRep.simple_iff_char_is_norm_one σ).mp inferInstance
  simp only [hinv] at hnorm
  have hsum2 : ∑ h : ↥H, σ.character h * σ.character h
      = σ.character 1 * σ.character 1 + σ.character t' * σ.character t' :=
    Fintype.sum_eq_add 1 t' (Ne.symm ht'ne)
      (fun x hx => (not_or.mpr hx (ht'all x)).elim)
  rw [hsum2, hH, Nat.cast_ofNat] at hnorm
                                       
  have hchar1 : σ.character 1 = (Module.finrank ℂ σ : ℂ) := FDRep.char_one σ
  rw [hchar1] at hnorm
  set d := Module.finrank ℂ σ with hd_def
  have hnorm2 : (d : ℂ) * (d : ℂ) + σ.character t' * σ.character t' = 2 := hnorm
                                                                                               
                                        
  have hf2 : σ.ρ t' * σ.ρ t' = 1 := by rw [← map_mul, ht'2, map_one]
  set p : Module.End ℂ σ := (2⁻¹ : ℂ) • (1 + σ.ρ t') with hp_def
  have hidem : IsIdempotentElem p := by
    change p * p = p
    have e1 : p * p = (2⁻¹ * 2⁻¹ : ℂ) • ((1 + σ.ρ t') * (1 + σ.ρ t')) := by
      simp only [hp_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    have e2 : (1 + σ.ρ t') * (1 + σ.ρ t') = (2 : ℂ) • (1 + σ.ρ t') := by
      have hexp : (1 + σ.ρ t') * (1 + σ.ρ t') = 1 + σ.ρ t' + σ.ρ t' + σ.ρ t' * σ.ρ t' := by
        noncomm_ring
      rw [hexp, hf2, two_smul]; abel
    rw [e1, e2, smul_smul, hp_def, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]
  have htr : LinearMap.trace ℂ σ p = (Module.finrank ℂ (LinearMap.range p) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range p hidem).trace
  set K := Module.finrank ℂ (LinearMap.range p) with hK_def
  have htr2 : LinearMap.trace ℂ σ p = 2⁻¹ * ((d : ℂ) + σ.character t') := by
    simp only [hp_def, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
    rfl
  have heq : (K : ℂ) = 2⁻¹ * ((d : ℂ) + σ.character t') := htr.symm.trans htr2
  have hchi : σ.character t' = 2 * (K : ℂ) - (d : ℂ) := by linear_combination -2 * heq
                                                             
  have hZ : (d : ℤ) ^ 2 + (2 * (K : ℤ) - (d : ℤ)) ^ 2 = 2 := by
    have hC : (d : ℂ) * (d : ℂ) + (2 * (K : ℂ) - (d : ℂ)) * (2 * (K : ℂ) - (d : ℂ)) = 2 := by
      rw [← hchi]; exact hnorm2
    have hcast : (((d : ℤ) ^ 2 + (2 * (K : ℤ) - (d : ℤ)) ^ 2 : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
      push_cast; linear_combination hC
    exact_mod_cast hcast
  have hd1 : d = 1 := by
    have hsq : (d : ℤ) ^ 2 ≤ 2 := by nlinarith [sq_nonneg (2 * (K : ℤ) - (d : ℤ))]
    have hlt : d < 2 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · exact h
      · exfalso
        have h2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast h
        nlinarith [hsq, h2]
    interval_cases d
    · exfalso
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (2 * (K : ℤ) - ((0 : ℕ) : ℤ)) ^ 2 = 4 * m := ⟨(K : ℤ) ^ 2, by ring⟩
      rw [hm] at hZ; push_cast at hZ; omega
    · rfl
                                                                          
  have hchisq : σ.character t' * σ.character t' = 1 := by
    rw [hd1] at hnorm2; push_cast at hnorm2; linear_combination hnorm2
  have hpm : σ.character t' = 1 ∨ σ.character t' = -1 := by
    have hfac : (σ.character t' - 1) * (σ.character t' + 1) = 0 := by linear_combination hchisq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  have hchit : σ.character t' = -1 := by
    rcases hpm with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hntriv
      apply hw
      rcases ht'all w with rfl | rfl
      · rw [hchar1, hd1]; norm_num
      · exact h
    · exact h
                                     
  intro x
  rcases ht'all x with rfl | rfl
  · rw [if_pos rfl, hchar1, hd1]; norm_num
  · rw [if_neg ht'ne]; exact hchit

set_option maxRecDepth 8000 in
                                                                                             
set_option maxHeartbeats 4000000 in
                                                                                                
                 
/-- The numbers of conjugators carrying each indexed representative to one are given by the vector (60, 0, 0, 0, 0). -/
lemma card_conjugators_to_one (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1)).card = ![60, 0, 0, 0, 0] j := by
  fin_cases j <;> decide

                                                                                         
                                                                     
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012050 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![30, 0, -2, 0, 0] j := by
  classical
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 2 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsign := Auxiliary.statement012116 H hH σ hntriv
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ∑ x : Auxiliary.ambientType, (2 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1 then (1 : ℂ) else 0)
                    - (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then (1 : ℂ) else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx1 : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1
    · have hxH : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H := hx1 ▸ H.one_mem
      have hone : (⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hxH⟩ : ↥H) = 1 := Subtype.ext hx1
      rw [dif_pos hxH, hsign ⟨_, hxH⟩, hone, if_pos rfl, if_pos hx1, if_pos hxH]; ring
    · by_cases hxH : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
      · have hne : (⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hxH⟩ : ↥H) ≠ 1 :=
          fun hEq => hx1 (Subtype.ext_iff.mp hEq)
        rw [dif_pos hxH, hsign ⟨_, hxH⟩, if_neg hne, if_neg hx1, if_pos hxH]; ring
      · rw [dif_neg hxH, if_neg hx1, if_neg hxH]; ring
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    card_conjugators_to_one, card_conjugating_elements_conj_mem_eq_zpowers_rep_two_of_card_two H hH, card_conjugating_elements_conj_representative_mem_zpowers_rep_two, hcard]
  fin_cases j <;> norm_num

                                                                            
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012047 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![30, 0, -2, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012050 H hH σ hntriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                   
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012049 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character
        (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![30, 0, -2, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012048 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![30, 0, -2, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012049 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                     
                                          
/-- The auxiliary construction applied to a simple representation whose character is not constantly one on a subgroup of cardinality two is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_nontrivial_card_two_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅
      RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [Auxiliary.statement012047 H hH σ hntriv g, Auxiliary.statement012048 g]

                                             

                                                                                                 
                                                                                                   
                                                       

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                      
/-- A nonidentity element whose cube is one has class index one. -/
lemma classIndex_eq_one_of_cube_eq_one (s : Auxiliary.ambientType) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 1 := by
  revert s; decide

                                                                      
/-- Every subgroup of cardinality three is conjugate, in the displayed membership sense, to the cyclic subgroup generated by representative one. -/
lemma exists_conjugate_zpowers_rep_one_of_subgroup_card_three (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 3) :
    ∃ d : Auxiliary.ambientType, ∀ y : Auxiliary.ambientType, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) := by
  haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; norm_num)
  obtain ⟨s, hs_mem, hs_ne⟩ := H.nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 3 := by
    rw [← hH]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : H)
    rwa [Subgroup.orderOf_mk] at this
  have hord3 : orderOf s = 3 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs3 : s ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one s
  have hcl : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 1 := classIndex_eq_one_of_cube_eq_one s hs3 hs_ne
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative s
  rw [hcl] at hc
  have hzs : Subgroup.zpowers s = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord3, hH]
  refine ⟨c⁻¹, fun y => ?_⟩
  have hHeq : H = MulAut.conj c • Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) := by
    rw [RepresentationTheory.FiniteGroupRepresentation.subgroupRelation_011010, hc, hzs]
  rw [hHeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]

                                                                                              
/-- For a subgroup of cardinality three, the number of conjugating elements whose conjugate of a given element lies in it equals the corresponding count for the cyclic subgroup generated by representative one. -/
lemma card_conjugating_elements_conj_mem_eq_zpowers_rep_one_of_card_three (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3) (g : Auxiliary.ambientType) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1))).card := by
  obtain ⟨d, hd⟩ := exists_conjugate_zpowers_rep_one_of_subgroup_card_three H hH
  apply Finset.card_bij' (fun x _ => d * x) (fun x _ => d⁻¹ * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd] at hx
    rw [show d * x * g * (d * x)⁻¹ = d * (x * g * x⁻¹) * d⁻¹ by group]
    exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd]
    rw [show d * (d⁻¹ * x * g * (d⁻¹ * x)⁻¹) * d⁻¹ = x * g * x⁻¹ by group]
    exact hx
  · intro x hx; group
  · intro x hx; group

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                                             
/-- For indexed representatives, the numbers of conjugating elements whose conjugate of the representative lies in the cyclic subgroup generated by representative one form the vector (60, 6, 0, 0, 0). -/
lemma card_conjugating_elements_conj_representative_mem_zpowers_rep_one (j : Fin 5) :
    (univ.filter
        (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1))).card
      = ![60, 6, 0, 0, 0] j := by
  rw [filter_conjugating_elements_conj_mem_zpowers_eq_filter_conj_mem_powers_range (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 3 RepresentationTheory.FiniteGroupRepresentation.orderFormula_011118]
  fin_cases j <;> decide

                                 

                                                                                                
                                                                    
/-- On indexed representatives, the character of the auxiliary construction applied to a constant-character-one representation of a subgroup of cardinality three has values (20, 2, 0, 0, 0). -/
lemma auxiliary_construction_character_representative_of_card_three_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![20, 2, 0, 0, 0] j := by
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 3 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, card_conjugating_elements_conj_mem_eq_zpowers_rep_one_of_card_three H hH, card_conjugating_elements_conj_representative_mem_zpowers_rep_one, hcard]
  fin_cases j <;> norm_num

                                                                               
/-- The character of the auxiliary construction applied to a representation with constant character one on a subgroup of cardinality three has class values (20, 2, 0, 0, 0). -/
lemma auxiliary_construction_character_of_card_three_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![20, 2, 0, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact auxiliary_construction_character_representative_of_card_three_character_one H hH σ htriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                      
/-- On indexed representatives, the displayed iterated biproduct has character vector (20, 2, 0, 0, 0). -/
lemma character_auxiliaryBiprod_card_three_representative (j : Fin 5) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character
        (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![20, 2, 0, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_zero, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- The displayed iterated biproduct has character values (20, 2, 0, 0, 0), selected by class index. -/
lemma character_auxiliaryBiprod_card_three (g : Auxiliary.ambientType) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![20, 2, 0, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact character_auxiliaryBiprod_card_three_representative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                            
                                                                                           
/-- The auxiliary construction applied to a simple representation with constant character one on a subgroup of cardinality three is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_character_one_card_three_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [auxiliary_construction_character_of_card_three_character_one H hH σ htriv g, character_auxiliaryBiprod_card_three g]

                                                                                             
                                                      
/-- Conjugate target elements have equal numbers of conjugators from a fixed element. -/
lemma card_conjugators_eq_of_targets_conjugate (g y₁ y₂ : Auxiliary.ambientType) (hconj : ∃ c : Auxiliary.ambientType, c * y₁ * c⁻¹ = y₂) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ = y₂)).card
      = (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ = y₁)).card := by
  obtain ⟨c, hc⟩ := hconj
  apply Finset.card_bij' (fun x _ => c⁻¹ * x) (fun x _ => c * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [show c⁻¹ * x * g * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * g * x⁻¹) * c by group, hx, ← hc]; group
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [show c * x * g * (c * x)⁻¹ = c * (x * g * x⁻¹) * c⁻¹ by group, hx]; exact hc
  · intro x hx; group
  · intro x hx; group

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                                                
                                                                        
/-- The numbers of conjugators carrying each indexed representative to representative one are given by the vector (0, 3, 0, 0, 0). -/
lemma card_conjugators_to_rep_one (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1)).card = ![0, 3, 0, 0, 0] j := by
  fin_cases j <;> decide

                                                                                                 
                                                                     
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012060 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![20, -1, 0, 0, 0] j := by
  classical
                                                                                 
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hcyc : IsCyclic ↥H := isCyclic_of_prime_card hH
  letI cg : CommGroup ↥H := IsCyclic.commGroup
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule σ.ρ
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hone : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : ↥H, σ.character (g * h) = σ.character g * σ.character h := by
    intro g h
    have key : (σ.character (g * h) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character h : ℂ) • LinearMap.id := by
      rw [← hscalar (g * h), map_mul, hscalar g, hscalar h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
                                                           
  set χ : ↥H →* ℂ := { toFun := σ.character, map_one' := hone, map_mul' := hmul } with hχ
  have hχa : ∀ g : ↥H, χ g = σ.character g := fun _ => rfl
                                                                           
  obtain ⟨a₀, ha₀⟩ := hcyc.exists_generator
  have horda₀ : orderOf a₀ = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers ha₀]; exact hH
  set a : Auxiliary.ambientType := (a₀ : Auxiliary.ambientType) with ha_def
  set a2 : Auxiliary.ambientType := a ^ 2 with ha2_def
  have horda : orderOf a = 3 := by
    rw [ha_def, ← horda₀]
    exact orderOf_injective H.subtype (Subgroup.subtype_injective H) a₀
  have ha3 : a ^ 3 = 1 := by rw [← horda]; exact pow_orderOf_eq_one a
  have ha_ne1 : a ≠ 1 := by
    intro h; rw [h, orderOf_one] at horda; exact absurd horda (by norm_num)
  have ha2_ne1 : a2 ≠ 1 := by
    rw [ha2_def]; intro h
    have h2 := orderOf_le_of_pow_eq_one (n := 2) (by norm_num) h
    rw [horda] at h2; omega
  obtain ⟨z, hz_def⟩ : ∃ z : ℂ, z = σ.character a₀ := ⟨σ.character a₀, rfl⟩
  have ha₀3 : a₀ ^ 3 = 1 := by rw [← horda₀]; exact pow_orderOf_eq_one a₀
  have hz3 : z ^ 3 = 1 := by
    have h := map_pow χ a₀ 3
    rw [ha₀3, map_one, hχa, ← hz_def] at h; exact h.symm
  have hchar_a2 : σ.character (a₀ ^ 2) = z ^ 2 := by
    have h := map_pow χ a₀ 2
    rw [hχa, hχa, ← hz_def] at h; exact h
                                   
  have hgen_top : Subgroup.zpowers a₀ = ⊤ := by rw [eq_top_iff]; intro x _; exact ha₀ x
  have hHzp : Subgroup.zpowers a = H := by
    have h1 : (Subgroup.zpowers a₀).map H.subtype = Subgroup.zpowers a :=
      MonoidHom.map_zpowers H.subtype a₀
    rw [hgen_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have ha2coe : a2 = ((a₀ ^ 2 : ↥H) : Auxiliary.ambientType) := by rw [ha2_def, ha_def]; push_cast; ring
  have henum : ∀ y : Auxiliary.ambientType, y ∈ H → y = 1 ∨ y = a ∨ y = a2 := by
    intro y hy
    rw [← hHzp, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011112 a 3 horda] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, hky⟩ := hy
    interval_cases k
    · left; rw [← hky]; simp
    · right; left; rw [← hky]; simp
    · right; right; rw [← hky, ha2_def]
  have ha_mem : a ∈ H := by rw [ha_def]; exact SetLike.coe_mem a₀
  have ha2_mem : a2 ∈ H := by rw [ha2coe]; exact SetLike.coe_mem _
  have hne_aa2 : a ≠ a2 := by
    intro h
    rw [ha2_def, sq] at h
    exact ha_ne1 (mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm))
                                                                                         
  have hconj_a : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * c⁻¹ = a := by
    obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative a
    rw [classIndex_eq_one_of_cube_eq_one a ha3 ha_ne1] at hc; exact ⟨c, hc⟩
  have ha2_3 : a2 ^ 3 = 1 := by rw [ha2_def, ← pow_mul, mul_comm, pow_mul, ha3, one_pow]
  have hconj_a2 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * c⁻¹ = a2 := by
    obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative a2
    rw [classIndex_eq_one_of_cube_eq_one a2 ha2_3 ha2_ne1] at hc; exact ⟨c, hc⟩
                    
  have hz_ne : z ≠ 1 := by
    obtain ⟨h0, hh0⟩ := hntriv
    rcases henum (h0 : Auxiliary.ambientType) (SetLike.coe_mem h0) with he | he | he
    · exact absurd (by rw [show h0 = 1 from Subtype.ext he]; exact hone) hh0
    · intro hz1; apply hh0
      rw [show h0 = a₀ from Subtype.ext (he.trans ha_def), ← hz_def]; exact hz1
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 2 from Subtype.ext (he.trans ha2coe), hchar_a2, hz1]; ring
  have hz_sum : z + z ^ 2 = -1 := by
    have hfac : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h) hz_ne
    · linear_combination h
                                                                         
  rw [Auxiliary.statement012086]
  have hcardℂ : (Fintype.card ↥H : ℂ) = 3 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hterm : ∀ x : Auxiliary.ambientType,
      (if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, h⟩ else 0)
        = σ.character 1 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1 then (1 : ℂ) else 0)
          + z * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a then 1 else 0)
          + z ^ 2 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a2 then 1 else 0) := by
    intro x
    set y := x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ with hy
    by_cases hmem : y ∈ H
    · rcases henum y hmem with h1 | ha | ha2
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = 1 from Subtype.ext h1, if_pos h1,
          if_neg (by intro h; rw [h1] at h; exact ha_ne1 h.symm),
          if_neg (by intro h; rw [h1] at h; exact ha2_ne1 h.symm)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ from Subtype.ext (ha.trans ha_def),
          if_neg (by intro h; rw [ha] at h; exact ha_ne1 h),
          if_pos ha, if_neg (by intro h; rw [ha] at h; exact hne_aa2 h), ← hz_def]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 2 from Subtype.ext (ha2.trans ha2coe),
          hchar_a2, if_neg (by intro h; rw [ha2] at h; exact ha2_ne1 h),
          if_neg (by intro h; rw [ha2] at h; exact hne_aa2 h.symm), if_pos ha2]
        ring
    · rw [dif_neg hmem,
        if_neg (by intro h; exact hmem (by rw [h]; exact H.one_mem)),
        if_neg (by intro h; exact hmem (by rw [h]; exact ha_mem)),
        if_neg (by intro h; exact hmem (by rw [h]; exact ha2_mem))]
      ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    Finset.sum_boole, hone, card_conjugators_to_one,
    card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) a hconj_a,
    card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) a2 hconj_a2, card_conjugators_to_rep_one, hcardℂ]
  fin_cases j <;> norm_num
  all_goals linear_combination hz_sum

                                                                                  
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012057 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![20, -1, 0, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012060 H hH σ hntriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                         
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012059 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = ![20, -1, 0, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012058 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![20, -1, 0, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012059 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                          
                                                        
/-- The auxiliary construction applied to a simple representation whose character is not constantly one on a subgroup of cardinality three is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_nontrivial_card_three_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [Auxiliary.statement012057 H hH σ hntriv g, Auxiliary.statement012058 g]

                              

                                                                                              
                                                                                                  
                          

set_option maxRecDepth 8000 in
                                                                                                 
set_option maxHeartbeats 4000000 in
                                                                                          
                                                                                              
                                                       
/-- For indexed representatives, the numbers of conjugating elements whose conjugate of the representative lies in the cyclic subgroup generated by representative three form the vector (60, 0, 0, 10, 10). -/
lemma card_conjugating_elements_conj_representative_mem_zpowers_rep_three (j : Fin 5) :
    (univ.filter
        (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3))).card
      = ![60, 0, 0, 10, 10] j := by
  rw [filter_conjugating_elements_conj_mem_zpowers_eq_filter_conj_mem_powers_range (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 5 RepresentationTheory.FiniteGroupRepresentation.orderFormula_011120]
  fin_cases j <;> decide

                                                                                     
                                                                                       
              
/-- Every subgroup of cardinality five is conjugate, in the displayed membership sense, to the cyclic subgroup generated by representative three. -/
lemma exists_conjugate_zpowers_rep_three_of_subgroup_card_five (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 5) :
    ∃ d : Auxiliary.ambientType, ∀ y : Auxiliary.ambientType, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 Auxiliary.ambientType := Sylow.ofCard H (by rw [hH, RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011084, pow_one])
  have hQc : Nat.card (Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3)) = 5 := by
    rw [Nat.card_zpowers, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011120]
  let Q : Sylow 5 Auxiliary.ambientType := Sylow.ofCard (Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3))
    (by rw [hQc, RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011084, pow_one])
  obtain ⟨cc, hcc⟩ := MulAction.exists_smul_eq Auxiliary.ambientType P Q
  have hPc : (P : Subgroup Auxiliary.ambientType) = H := Sylow.coe_ofCard _ _
  have hQcoe : (Q : Subgroup Auxiliary.ambientType) = Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) := Sylow.coe_ofCard _ _
  have hco : (Q : Subgroup Auxiliary.ambientType) = MulAut.conj cc • (P : Subgroup Auxiliary.ambientType) := by rw [← hcc]; rfl
  have hzeq : Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) = MulAut.conj cc • H := by
    rw [← hQcoe, ← hPc]; exact hco
  refine ⟨cc, fun y => ?_⟩
  rw [hzeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hy; rw [show cc⁻¹ * (cc * y * cc⁻¹) * cc = y by group]; exact hy
  · intro hy; rw [show cc⁻¹ * (cc * y * cc⁻¹) * cc = y by group] at hy; exact hy

                                                                                              
/-- For a subgroup of cardinality five, the number of conjugating elements whose conjugate of a given element lies in it equals the corresponding count for the cyclic subgroup generated by representative three. -/
lemma card_conjugating_elements_conj_mem_eq_zpowers_rep_three_of_card_five (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5) (g : Auxiliary.ambientType) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3))).card := by
  obtain ⟨d, hd⟩ := exists_conjugate_zpowers_rep_three_of_subgroup_card_five H hH
  apply Finset.card_bij' (fun x _ => d * x) (fun x _ => d⁻¹ * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd] at hx
    rw [show d * x * g * (d * x)⁻¹ = d * (x * g * x⁻¹) * d⁻¹ by group]
    exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd]
    rw [show d * (d⁻¹ * x * g * (d⁻¹ * x)⁻¹) * d⁻¹ = x * g * x⁻¹ by group]
    exact hx
  · intro x hx; group
  · intro x hx; group

                                                                                                
                                                                    
/-- On indexed representatives, the character of the auxiliary construction applied to a constant-character-one representation of a subgroup of cardinality five has values (12, 0, 0, 2, 2). -/
lemma auxiliary_construction_character_representative_of_card_five_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![12, 0, 0, 2, 2] j := by
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 5 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, card_conjugating_elements_conj_mem_eq_zpowers_rep_three_of_card_five H hH, card_conjugating_elements_conj_representative_mem_zpowers_rep_three, hcard]
  fin_cases j <;> norm_num

                                                                               
/-- The character of the auxiliary construction applied to a representation with constant character one on a subgroup of cardinality five has class values (12, 0, 0, 2, 2). -/
lemma auxiliary_construction_character_of_card_five_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![12, 0, 0, 2, 2] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact auxiliary_construction_character_representative_of_card_five_character_one H hH σ htriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                      
/-- On indexed representatives, the displayed iterated biproduct has character vector (12, 0, 0, 2, 2). -/
lemma character_auxiliaryBiprod_card_five_representative (j : Fin 5) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = ![12, 0, 0, 2, 2] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_zero, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- The displayed iterated biproduct has character values (12, 0, 0, 2, 2), selected by class index. -/
lemma character_auxiliaryBiprod_card_five (g : Auxiliary.ambientType) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![12, 0, 0, 2, 2] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact character_auxiliaryBiprod_card_five_representative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                       
                                                                                     
                 
/-- The auxiliary construction applied to a simple representation with constant character one on a subgroup of cardinality five is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_character_one_card_five_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [auxiliary_construction_character_of_card_five_character_one H hH σ htriv g, character_auxiliaryBiprod_card_five g]

                                     

                                                                                          
                                                                                         
                                                                                        
                                                                                             
                                                                                         
                                                                                            

set_option maxRecDepth 8000 in
                                                                                         
                                                                    
set_option maxHeartbeats 4000000 in
                                                                                          
                                                
/-- The nontrivial powers of a nonidentity element with fifth power one have one of the two stated class-index patterns. -/
lemma classIndex_powers_of_order_five (s : Auxiliary.ambientType) (h5 : s ^ 5 = 1) (hne : s ≠ 1) :
    (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 3 ∧ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 2) = 4 ∧ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 3) = 4 ∧ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 4) = 3)
    ∨ (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 4 ∧ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 2) = 3 ∧ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 3) = 3 ∧
        RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (s ^ 4) = 4) := by
  revert s; decide

set_option maxRecDepth 8000 in
                                                                           
set_option maxHeartbeats 4000000 in
                                                                                              
                             
/-- The numbers of conjugators carrying each indexed representative to representative three are given by the vector (0, 0, 0, 5, 0). -/
lemma card_conjugators_to_rep_three (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3)).card
      = ![0, 0, 0, 5, 0] j := by
  fin_cases j <;> decide

set_option maxRecDepth 8000 in
                                                                           
set_option maxHeartbeats 4000000 in
                                                                                              
                             
/-- The numbers of conjugators carrying each indexed representative to representative four are given by the vector (0, 0, 0, 0, 5). -/
lemma card_conjugators_to_rep_four (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4)).card
      = ![0, 0, 0, 0, 5] j := by
  fin_cases j <;> decide

                                                                            
                                                             
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012078 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = ![12, 0, 0, (-1 + (Real.sqrt 5 : ℂ)) / 2, (-1 - (Real.sqrt 5 : ℂ)) / 2] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
                                                                                                
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012080 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = ![12, 0, 0, (-1 - (Real.sqrt 5 : ℂ)) / 2, (-1 + (Real.sqrt 5 : ℂ)) / 2] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                                                
                                                                           
                                                                                                  
                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012071 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    ∃ A B : ℂ, A + B = -1 ∧ A ^ 2 + A - 1 = 0 ∧
      ∀ j, (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![12, 0, 0, A, B] j := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hcyc : IsCyclic ↥H := isCyclic_of_prime_card hH
  letI cg : CommGroup ↥H := IsCyclic.commGroup
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule σ.ρ
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hone : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : ↥H, σ.character (g * h) = σ.character g * σ.character h := by
    intro g h
    have key : (σ.character (g * h) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character h : ℂ) • LinearMap.id := by
      rw [← hscalar (g * h), map_mul, hscalar g, hscalar h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
  set χ : ↥H →* ℂ := { toFun := σ.character, map_one' := hone, map_mul' := hmul } with hχ
  have hχa : ∀ g : ↥H, χ g = σ.character g := fun _ => rfl
  obtain ⟨a₀, ha₀⟩ := hcyc.exists_generator
  have horda₀ : orderOf a₀ = 5 := by rw [orderOf_eq_card_of_forall_mem_zpowers ha₀]; exact hH
  set a : Auxiliary.ambientType := (a₀ : Auxiliary.ambientType) with ha_def
                                                                                      
  have horda : orderOf a = 5 := by
    rw [ha_def]
    exact (orderOf_injective H.subtype (Subgroup.subtype_injective H) a₀).trans horda₀
  have ha5 : a ^ 5 = 1 := by have h := pow_orderOf_eq_one a; rwa [horda] at h
  have ha_ne1 : a ≠ 1 := by
    intro h; rw [h, orderOf_one] at horda; exact absurd horda (by norm_num)
  obtain ⟨z, hz_def⟩ : ∃ z : ℂ, z = σ.character a₀ := ⟨σ.character a₀, rfl⟩
  have ha₀5 : a₀ ^ 5 = 1 := by have h := pow_orderOf_eq_one a₀; rwa [horda₀] at h
  have hz5 : z ^ 5 = 1 := by
    have h := map_pow χ a₀ 5
    rw [ha₀5, map_one, hχa, ← hz_def] at h; exact h.symm
  have hchar_pow : ∀ k : ℕ, σ.character (a₀ ^ k) = z ^ k := by
    intro k
    have h := map_pow χ a₀ k
    rw [hχa, hχa, ← hz_def] at h; exact h
                                        
  have hgen_top : Subgroup.zpowers a₀ = ⊤ := by rw [eq_top_iff]; intro x _; exact ha₀ x
  have hHzp : Subgroup.zpowers a = H := by
    have h1 : (Subgroup.zpowers a₀).map H.subtype = Subgroup.zpowers a :=
      MonoidHom.map_zpowers H.subtype a₀
    rw [hgen_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have ha2coe : a ^ 2 = ((a₀ ^ 2 : ↥H) : Auxiliary.ambientType) := by rw [ha_def]; push_cast; ring
  have ha3coe : a ^ 3 = ((a₀ ^ 3 : ↥H) : Auxiliary.ambientType) := by rw [ha_def]; push_cast; ring
  have ha4coe : a ^ 4 = ((a₀ ^ 4 : ↥H) : Auxiliary.ambientType) := by rw [ha_def]; push_cast; ring
  have henum : ∀ y : Auxiliary.ambientType, y ∈ H → y = 1 ∨ y = a ∨ y = a ^ 2 ∨ y = a ^ 3 ∨ y = a ^ 4 := by
    intro y hy
    rw [← hHzp, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011112 a 5 horda] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, hky⟩ := hy
    interval_cases k
    · left; rw [← hky]; simp
    · right; left; rw [← hky, pow_one]
    · right; right; left; rw [← hky]
    · right; right; right; left; rw [← hky]
    · right; right; right; right; rw [← hky]
  have ha_mem : a ∈ H := by rw [ha_def]; exact SetLike.coe_mem a₀
  have ha2_mem : a ^ 2 ∈ H := by rw [ha2coe]; exact SetLike.coe_mem _
  have ha3_mem : a ^ 3 ∈ H := by rw [ha3coe]; exact SetLike.coe_mem _
  have ha4_mem : a ^ 4 ∈ H := by rw [ha4coe]; exact SetLike.coe_mem _
                                          
  have hne : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → a ^ i ≠ a ^ j := by
    intro i j hi hj hij h
    wlog hlt : i < j generalizing i j
    · exact this j i hj hi (Ne.symm hij) h.symm (by omega)
    have hd : a ^ (j - i) = 1 := by
      have hcancel : a ^ i * a ^ (j - i) = a ^ i * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]; exact h.symm
      exact mul_left_cancel hcancel
    have hle := orderOf_le_of_pow_eq_one (n := j - i) (by omega) hd
    rw [horda] at hle; omega
  have e01 : (1 : Auxiliary.ambientType) ≠ a := by
    have := hne 0 1 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero, pow_one] at this
  have e02 : (1 : Auxiliary.ambientType) ≠ a ^ 2 := by
    have := hne 0 2 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e03 : (1 : Auxiliary.ambientType) ≠ a ^ 3 := by
    have := hne 0 3 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e04 : (1 : Auxiliary.ambientType) ≠ a ^ 4 := by
    have := hne 0 4 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e12 : a ≠ a ^ 2 := by
    have := hne 1 2 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e13 : a ≠ a ^ 3 := by
    have := hne 1 3 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e14 : a ≠ a ^ 4 := by
    have := hne 1 4 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e23 : a ^ 2 ≠ a ^ 3 := hne 2 3 (by norm_num) (by norm_num) (by norm_num)
  have e24 : a ^ 2 ≠ a ^ 4 := hne 2 4 (by norm_num) (by norm_num) (by norm_num)
  have e34 : a ^ 3 ≠ a ^ 4 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
                                         
  have hz_ne : z ≠ 1 := by
    obtain ⟨h0, hh0⟩ := hntriv
    rcases henum (h0 : Auxiliary.ambientType) (SetLike.coe_mem h0) with he | he | he | he | he
    · exact absurd (by rw [show h0 = 1 from Subtype.ext he]; exact hone) hh0
    · intro hz1; apply hh0
      rw [show h0 = a₀ from Subtype.ext (he.trans ha_def), ← hz_def]; exact hz1
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 2 from Subtype.ext (he.trans ha2coe), hchar_pow 2, hz1]; ring
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 3 from Subtype.ext (he.trans ha3coe), hchar_pow 3, hz1]; ring
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 4 from Subtype.ext (he.trans ha4coe), hchar_pow 4, hz1]; ring
  have hz_sum4 : z + z ^ 2 + z ^ 3 + z ^ 4 = -1 := by
    have hfac : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by linear_combination hz5
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : z = 1) hz_ne
    · linear_combination h
  have hcardℂ : (Fintype.card ↥H : ℂ) = 5 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
                                                           
  have hterm : ∀ (j : Fin 5) (x : Auxiliary.ambientType),
      (if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, h⟩ else 0)
        = (1 : ℂ) * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1 then 1 else 0)
          + z * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a then 1 else 0)
          + z ^ 2 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 2 then 1 else 0)
          + z ^ 3 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 3 then 1 else 0)
          + z ^ 4 * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 4 then 1 else 0) := by
    intro j x
    set y := x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ with hy
    by_cases hmem : y ∈ H
    · rcases henum y hmem with h1 | hA | hA2 | hA3 | hA4
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = 1 from Subtype.ext h1, hone,
          if_pos h1, if_neg (by rw [h1]; exact e01), if_neg (by rw [h1]; exact e02),
          if_neg (by rw [h1]; exact e03), if_neg (by rw [h1]; exact e04)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ from Subtype.ext (hA.trans ha_def), ← hz_def,
          if_neg (by rw [hA]; exact e01.symm), if_pos hA, if_neg (by rw [hA]; exact e12),
          if_neg (by rw [hA]; exact e13), if_neg (by rw [hA]; exact e14)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 2 from Subtype.ext (hA2.trans ha2coe),
          hchar_pow 2, if_neg (by rw [hA2]; exact e02.symm), if_neg (by rw [hA2]; exact e12.symm),
          if_pos hA2, if_neg (by rw [hA2]; exact e23), if_neg (by rw [hA2]; exact e24)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 3 from Subtype.ext (hA3.trans ha3coe),
          hchar_pow 3, if_neg (by rw [hA3]; exact e03.symm), if_neg (by rw [hA3]; exact e13.symm),
          if_neg (by rw [hA3]; exact e23.symm), if_pos hA3, if_neg (by rw [hA3]; exact e34)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 4 from Subtype.ext (hA4.trans ha4coe),
          hchar_pow 4, if_neg (by rw [hA4]; exact e04.symm), if_neg (by rw [hA4]; exact e14.symm),
          if_neg (by rw [hA4]; exact e24.symm), if_neg (by rw [hA4]; exact e34.symm), if_pos hA4]
        ring
    · rw [dif_neg hmem,
        if_neg (fun h => hmem (by rw [h]; exact H.one_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha2_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha3_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha4_mem))]
      ring
                                                                                  
  have hraw : ∀ j : Fin 5, (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = (5 : ℂ)⁻¹ * ((1 : ℂ) * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = 1)).card : ℂ)
          + z * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a)).card : ℂ)
          + z ^ 2 * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 2)).card : ℂ)
          + z ^ 3 * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 3)).card : ℂ)
          + z ^ 4 * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = a ^ 4)).card : ℂ)) := by
    intro j
    rw [Auxiliary.statement012086, hcardℂ, Finset.sum_congr rfl (fun x _ => hterm j x),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, Finset.sum_boole]
                                         
  rcases classIndex_powers_of_order_five a ha5 ha_ne1 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  ·                                          
    refine ⟨z + z ^ 4, z ^ 2 + z ^ 3, by linear_combination hz_sum4,
      by linear_combination (z ^ 3 + 2) * hz5 + hz_sum4, ?_⟩
    intro j
    have hca : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * c⁻¹ = a := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative a; rw [h1] at hc; exact ⟨c, hc⟩
    have hca2 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * c⁻¹ = a ^ 2 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 2); rw [h2] at hc; exact ⟨c, hc⟩
    have hca3 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * c⁻¹ = a ^ 3 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 3); rw [h3] at hc; exact ⟨c, hc⟩
    have hca4 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * c⁻¹ = a ^ 4 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 4); rw [h4] at hc; exact ⟨c, hc⟩
    rw [hraw j, card_conjugators_to_one, card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) a hca,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4) (a ^ 2) hca2,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4) (a ^ 3) hca3,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (a ^ 4) hca4, card_conjugators_to_rep_three, card_conjugators_to_rep_four]
    fin_cases j <;> norm_num <;> ring_nf
  ·                                          
    refine ⟨z ^ 2 + z ^ 3, z + z ^ 4, by linear_combination hz_sum4,
      by linear_combination (z + 2) * hz5 + hz_sum4, ?_⟩
    intro j
    have hca : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * c⁻¹ = a := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative a; rw [h1] at hc; exact ⟨c, hc⟩
    have hca2 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * c⁻¹ = a ^ 2 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 2); rw [h2] at hc; exact ⟨c, hc⟩
    have hca3 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * c⁻¹ = a ^ 3 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 3); rw [h3] at hc; exact ⟨c, hc⟩
    have hca4 : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * c⁻¹ = a ^ 4 := by
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (a ^ 4); rw [h4] at hc; exact ⟨c, hc⟩
    rw [hraw j, card_conjugators_to_one, card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4) a hca,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (a ^ 2) hca2,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (a ^ 3) hca3,
      card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4) (a ^ 4) hca4, card_conjugators_to_rep_three, card_conjugators_to_rep_four]
    fin_cases j <;> norm_num <;> ring

                                                                                
/-- For a simple representation of a subgroup of cardinality five, the stated character formula on indexed representatives extends to every group element via its class index. -/
lemma auxiliary_construction_character_eq_of_representatives_card_five (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (_hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] {A B : ℂ}
    (hval : ∀ j, (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![12, 0, 0, A, B] j) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![12, 0, 0, A, B] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact hval (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012077 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![12, 0, 0, (-1 + (Real.sqrt 5 : ℂ)) / 2, (-1 - (Real.sqrt 5 : ℂ)) / 2] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012078 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                               
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012079 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g
      = ![12, 0, 0, (-1 - (Real.sqrt 5 : ℂ)) / 2, (-1 + (Real.sqrt 5 : ℂ)) / 2] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012080 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                            
                                                                                             
                                                
/-- The auxiliary construction applied to a simple representation whose character is not constantly one on a subgroup of cardinality five is isomorphic to one of the two displayed biproducts. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_nontrivial_card_five_iso_auxiliaryBiprod_or (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) ∨
      Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  obtain ⟨A, B, hAB, hAq, hval⟩ := Auxiliary.statement012071 H hH σ hntriv
                                                        
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  have hfac : (A - (-1 + (Real.sqrt 5 : ℂ)) / 2) * (A - (-1 - (Real.sqrt 5 : ℂ)) / 2) = 0 := by
    linear_combination hAq - (1 / 4 : ℂ) * hs
  rcases mul_eq_zero.mp hfac with hA | hA
  ·                                                          
    left
    apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    funext g
    rw [auxiliary_construction_character_eq_of_representatives_card_five H hH σ hval g, Auxiliary.statement012077 g,
      show A = (-1 + (Real.sqrt 5 : ℂ)) / 2 by linear_combination hA,
      show B = (-1 - (Real.sqrt 5 : ℂ)) / 2 by linear_combination hAB - hA]
  ·                                                           
    right
    apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    funext g
    rw [auxiliary_construction_character_eq_of_representatives_card_five H hH σ hval g, Auxiliary.statement012079 g,
      show A = (-1 - (Real.sqrt 5 : ℂ)) / 2 by linear_combination hA,
      show B = (-1 + (Real.sqrt 5 : ℂ)) / 2 by linear_combination hAB - hA]

                              

                                                                                      
                                                                                              
                                                                                              
                                                                                               
                                                                                       

                                                               
/-- A monoid action of the ambient group by permutations of five points. -/
def degreeFiveAction : Auxiliary.ambientType →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype

                                                                               
/-- An auxiliary subgroup of the ambient type. -/
abbrev Auxiliary.subgroup : Subgroup Auxiliary.ambientType := RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction 0

                                                               
/-- An element belongs to the auxiliary subgroup exactly when its permutation action fixes zero. -/
lemma mem_auxiliary_subgroup_iff_action_fixed_zero (a : Auxiliary.ambientType) : a ∈ Auxiliary.subgroup ↔ degreeFiveAction a 0 = 0 := Iff.rfl

/-- Membership in the auxiliary subgroup is decidable. -/
instance auxiliary_subgroup_decidable_mem : DecidablePred (· ∈ Auxiliary.subgroup) := fun a => decidable_of_iff _ (mem_auxiliary_subgroup_iff_action_fixed_zero a).symm

set_option maxRecDepth 12000 in
                                                                    
set_option maxHeartbeats 4000000 in
                                        
/-- The auxiliary subgroup has cardinality twelve. -/
lemma natCard_auxiliary_subgroup_eq_twelve : Nat.card Auxiliary.subgroup = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                      
/-- The degree-five permutation action is transitive. -/
lemma degreeFiveAction_transitive (i j : Fin 5) : ∃ g : Auxiliary.ambientType, degreeFiveAction g i = j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                                 
/-- Exactly twelve group elements fix any chosen point of the degree-five action. -/
lemma card_fixedPointStabilizer_eq_twelve (i : Fin 5) :
    (univ.filter (fun a : Auxiliary.ambientType => degreeFiveAction a i = i)).card = 12 := by
  fin_cases i <;> decide

                                                                             
/-- Each subgroup obtained from a point of the degree-five action has cardinality twelve. -/
lemma natCard_actionSubgroup_eq_twelve (i : Fin 5) : Nat.card (RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction i) = 12 := by
  haveI : DecidablePred (· ∈ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction i) :=
    fun a => decidable_of_iff _ (RepresentationTheory.FiniteGroupRepresentation.actionFormula_011110 degreeFiveAction i a).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [show (univ.filter (· ∈ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction i))
      = univ.filter (fun a : Auxiliary.ambientType => degreeFiveAction a i = i) from by
    apply Finset.filter_congr; intro a _; simp [RepresentationTheory.FiniteGroupRepresentation.actionFormula_011110]]
  exact card_fixedPointStabilizer_eq_twelve i

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                                 
                                                                                        
                       
/-- A subset of the five-point set with cardinality two or three has at most six group elements preserving it setwise. -/
lemma card_setwiseStabilizer_le_six (O : Finset (Fin 5)) (h2 : 2 ≤ O.card) (h3 : O.card ≤ 3) :
    (univ.filter (fun g : Auxiliary.ambientType => ∀ i ∈ O, degreeFiveAction g i ∈ O)).card ≤ 6 := by
  revert h2 h3; revert O; decide

                                                                                               
                                                                                                 
                                                                                                 
                                                                                             
                                
/-- A subgroup of cardinality twelve has a point fixed by all its elements under the given action. -/
lemma exists_common_fixedPoint_of_subgroup_card_twelve (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12) :
    ∃ i : Fin 5, ∀ h : Auxiliary.ambientType, h ∈ H → degreeFiveAction h i = i := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite _
  set act : ↥H →* Equiv.Perm (Fin 5) := degreeFiveAction.comp H.subtype with hact_def
  have hactx : ∀ (x : ↥H) (i : Fin 5), act x i = degreeFiveAction (x : Auxiliary.ambientType) i := fun _ _ => rfl
  set O : Finset (Fin 5) := univ.filter (fun i => ∃ x : ↥H, act x 0 = i) with hO_def
  set s : ℕ := (univ.filter (fun x : ↥H => act x 0 = 0)).card with hs_def
  have hcardH : Fintype.card ↥H = 12 := by rw [← Nat.card_eq_fintype_card]; exact hH
                                                
  have hOmem : ∀ i, i ∈ O ↔ ∃ x : Auxiliary.ambientType, x ∈ H ∧ degreeFiveAction x 0 = i := by
    intro i
    simp only [hO_def, mem_filter, mem_univ, true_and, hactx]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨(x : Auxiliary.ambientType), x.2, hx⟩
    · rintro ⟨x, hxH, hx⟩; exact ⟨⟨x, hxH⟩, hx⟩
                         
  have hinv : ∀ h ∈ H, ∀ i ∈ O, degreeFiveAction h i ∈ O := by
    intro h hh i hi
    rw [hOmem] at hi ⊢
    obtain ⟨x, hxH, hx⟩ := hi
    exact ⟨h * x, H.mul_mem hh hxH, by rw [map_mul, Equiv.Perm.mul_apply, hx]⟩
                                     
  have hfib : Fintype.card ↥H
      = ∑ i : Fin 5, (univ.filter (fun x : ↥H => act x 0 = i)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => mem_univ _)
  have hfiber : ∀ i : Fin 5, (univ.filter (fun x : ↥H => act x 0 = i)).card
      = if i ∈ O then s else 0 := by
    intro i
    by_cases hi : i ∈ O
    · rw [if_pos hi]
      simp only [hO_def, mem_filter, mem_univ, true_and] at hi
      obtain ⟨xi, hxi⟩ := hi
      rw [hs_def]; exact RepresentationTheory.FiniteGroupRepresentation.cardinalityFormula_011116 act 0 i xi hxi
    · rw [if_neg hi, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      exact hi (by simp only [hO_def, mem_filter, mem_univ, true_and]; exact ⟨x, hx⟩)
  have hOs : (12 : ℕ) = O.card * s := by
    rw [← hcardH, hfib, Finset.sum_congr rfl (fun i _ => hfiber i),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
                    
  have hOdvd : O.card ∣ 12 := ⟨s, hOs⟩
  have hOpos : 1 ≤ O.card := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero]
    intro hempty
    have : (0 : Fin 5) ∈ O := by rw [hOmem]; exact ⟨1, H.one_mem, by simp⟩
    rw [hempty] at this; exact absurd this (Finset.notMem_empty _)
  have hOle : O.card ≤ 5 := by have := Finset.card_le_univ O; simpa using this
  have hO5 : O.card ≠ 5 := by rintro h; rw [h] at hOdvd; norm_num at hOdvd
  by_cases hbig : 2 ≤ O.card ∧ O.card ≤ 3
  ·                                                                               
    exfalso
    obtain ⟨h2, h3⟩ := hbig
    have hsub : (univ.filter (· ∈ H))
        ⊆ univ.filter (fun g : Auxiliary.ambientType => ∀ i ∈ O, degreeFiveAction g i ∈ O) := by
      intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      exact fun i hi => hinv g hg i hi
    have hcard12 : (univ.filter (· ∈ H)).card = 12 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]; exact hH
    have hle := Finset.card_le_card hsub
    rw [hcard12] at hle
    have hle6 := card_setwiseStabilizer_le_six O h2 h3
    omega
  ·                                                  
    have hcase : O.card = 1 ∨ O.card = 4 := by omega
    have h0O : (0 : Fin 5) ∈ O := by rw [hOmem]; exact ⟨1, H.one_mem, by simp⟩
    rcases hcase with h1 | h4
    · refine ⟨0, fun h hh => ?_⟩
      have hmem : degreeFiveAction h 0 ∈ O := hinv h hh 0 h0O
      exact Finset.card_le_one.mp (le_of_eq h1) _ hmem _ h0O
    ·                                                         
      have hcompl : (univ \ O).card = 1 := by
        rw [Finset.card_univ_sdiff, Fintype.card_fin, h4]
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcompl
      have hpO : p ∉ O := by
        have : p ∈ univ \ O := by rw [hp]; exact Finset.mem_singleton_self p
        exact (Finset.mem_sdiff.mp this).2
      refine ⟨p, fun h hh => ?_⟩
      by_contra hne
                                                                       
      have himg : Finset.image (fun q => degreeFiveAction h q) O ⊆ O := by
        intro y hy; obtain ⟨q, hqO, rfl⟩ := Finset.mem_image.mp hy; exact hinv h hh q hqO
      have hcardimg : (Finset.image (fun q => degreeFiveAction h q) O).card = O.card :=
        Finset.card_image_of_injective O (degreeFiveAction h).injective
      have himgeq : Finset.image (fun q => degreeFiveAction h q) O = O :=
        Finset.eq_of_subset_of_card_le himg (le_of_eq hcardimg.symm)
                                                                               
      have hpInO : degreeFiveAction h p ∈ O := by
        by_contra hcon
        have : degreeFiveAction h p ∈ univ \ O := Finset.mem_sdiff.mpr ⟨mem_univ _, hcon⟩
        rw [hp, Finset.mem_singleton] at this; exact hne this
      rw [← himgeq] at hpInO
      obtain ⟨q, hqO, hq⟩ := Finset.mem_image.mp hpInO
      have : q = p := (degreeFiveAction h).injective hq
      rw [this] at hqO; exact hpO hqO

                                                                                              
                                                                            

                                                                                             
                                                                                              
                                                                                        
                              
/-- Every subgroup of cardinality twelve is conjugate, in the displayed membership sense, to the auxiliary subgroup. -/
lemma exists_conjugate_auxiliary_subgroup_of_card_twelve (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12) :
    ∃ d : Auxiliary.ambientType, ∀ y : Auxiliary.ambientType, y ∈ H ↔ d * y * d⁻¹ ∈ Auxiliary.subgroup := by
  obtain ⟨i, hi⟩ := exists_common_fixedPoint_of_subgroup_card_twelve H hH
  have hle : H ≤ RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction i :=
    fun h hh => by rw [RepresentationTheory.FiniteGroupRepresentation.actionFormula_011110]; exact hi h hh
  have hHeq : H = RepresentationTheory.FiniteGroupRepresentation.pointStabilizer degreeFiveAction i :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_actionSubgroup_eq_twelve i, hH])
  obtain ⟨d, hd⟩ := degreeFiveAction_transitive i 0
  have hdi : (degreeFiveAction d)⁻¹ 0 = i := by
    rw [← hd, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  refine ⟨d, fun y => ?_⟩
  rw [hHeq, RepresentationTheory.FiniteGroupRepresentation.actionFormula_011110, mem_auxiliary_subgroup_iff_action_fixed_zero]
  constructor
  · intro hy
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hdi, hy]
    exact hd
  · intro hy
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hdi] at hy
    exact (degreeFiveAction d).injective (by rw [hy, ← hd])

                                                                                                
/-- For a subgroup of cardinality twelve, the number of conjugating elements whose conjugate of a given element lies in it equals the corresponding count for the auxiliary subgroup. -/
lemma card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12) (g : Auxiliary.ambientType) :
    (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ H)).card
      = (univ.filter (fun x : Auxiliary.ambientType => x * g * x⁻¹ ∈ Auxiliary.subgroup)).card := by
  obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
  apply Finset.card_bij' (fun x _ => d * x) (fun x _ => d⁻¹ * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd] at hx
    rw [show d * x * g * (d * x)⁻¹ = d * (x * g * x⁻¹) * d⁻¹ by group]
    exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd]
    rw [show d * (d⁻¹ * x * g * (d⁻¹ * x)⁻¹) * d⁻¹ = x * g * x⁻¹ by group]
    exact hx
  · intro x hx; group
  · intro x hx; group

set_option maxRecDepth 12000 in
                                                                                         
set_option maxHeartbeats 4000000 in
                                                                                           
                                                                                          
/-- For indexed representatives, the numbers of conjugating elements whose conjugate of the representative lies in the auxiliary subgroup form the vector (60, 24, 12, 0, 0). -/
lemma card_conjugating_elements_conj_representative_mem_auxiliary_subgroup (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ Auxiliary.subgroup)).card
      = ![60, 24, 12, 0, 0] j := by
  have h : (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ Auxiliary.subgroup))
      = (univ.filter (fun x : Auxiliary.ambientType => degreeFiveAction (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹) 0 = 0)) := by
    apply Finset.filter_congr; intro x _; simp only [mem_auxiliary_subgroup_iff_action_fixed_zero]
  rw [h]; fin_cases j <;> decide

                                                                                                 
                                                                   
/-- On indexed representatives, the character of the auxiliary construction applied to a constant-character-one representation of a subgroup of cardinality twelve has values (5, 2, 1, 0, 0). -/
lemma auxiliary_construction_character_representative_of_card_twelve_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![5, 2, 1, 0, 0] j := by
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 12 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup, hcard]
  fin_cases j <;> norm_num

                                                                               
/-- The character of the auxiliary construction applied to a representation with constant character one on a subgroup of cardinality twelve has class values (5, 2, 1, 0, 0). -/
lemma auxiliary_construction_character_of_card_twelve_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![5, 2, 1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact auxiliary_construction_character_representative_of_card_twelve_character_one H hH σ htriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                             
/-- On indexed representatives, the displayed biproduct has character vector (5, 2, 1, 0, 0). -/
lemma character_auxiliaryBiprod_card_twelve_representative (j : Fin 5) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![5, 2, 1, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_zero, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one]
  fin_cases j <;>
    norm_num [RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

                                                                              
/-- The displayed biproduct has character values (5, 2, 1, 0, 0), selected by class index. -/
lemma character_auxiliaryBiprod_card_twelve (g : Auxiliary.ambientType) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne).character g = ![5, 2, 1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact character_auxiliaryBiprod_card_twelve_representative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                         
                                    
/-- The auxiliary construction applied to a simple representation with constant character one on a subgroup of cardinality twelve is isomorphic to the displayed biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_character_one_card_twelve_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (_hdim : Module.finrank ℂ σ = 1)
    (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [auxiliary_construction_character_of_card_twelve_character_one H hH σ htriv g, character_auxiliaryBiprod_card_twelve g]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
                                                                                                
                                                                     
/-- Every nonidentity involution in the auxiliary subgroup is a commutator of two elements of that subgroup. -/
lemma exists_commutator_eq_of_mem_auxiliary_subgroup_involution :
    ∀ z : Auxiliary.ambientType, z ∈ Auxiliary.subgroup → z ^ 2 = 1 → z ≠ 1 →
      ∃ a ∈ Auxiliary.subgroup, ∃ b ∈ Auxiliary.subgroup, a * b * a⁻¹ * b⁻¹ = z := by
  decide

                                                                                              
                                                                                            
                                                                                                
/-- A one-dimensional representation of a subgroup of cardinality twelve has character one on elements whose image in the ambient group has square one. -/
lemma character_eq_one_on_involutions_of_finrank_one (H : Subgroup Auxiliary.ambientType)
    (hH : Nat.card H = 12) (σ : FDRep ℂ ↥H) (hdim : Module.finrank ℂ (σ : Type) = 1)
    (y : ↥H) (hy2 : (y : Auxiliary.ambientType) ^ 2 = 1) : σ.character y = 1 := by
  classical
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hone : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g k : ↥H, σ.character (g * k) = σ.character g * σ.character k := by
    intro g k
    have key : (σ.character (g * k) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character k : ℂ) • LinearMap.id := by
      rw [← hscalar (g * k), map_mul, hscalar g, hscalar k]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
  by_cases hy1 : (y : Auxiliary.ambientType) = 1
  · rw [show y = 1 from Subtype.ext hy1, hone]
                                                                             
  obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
  have hzmem : d * (y : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd (y : Auxiliary.ambientType)).mp y.2
  have hz2 : (d * (y : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by
    have hconj : (d * (y : Auxiliary.ambientType) * d⁻¹) ^ 2 = d * ((y : Auxiliary.ambientType) ^ 2) * d⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [hconj, hy2]; group
  have hz1 : d * (y : Auxiliary.ambientType) * d⁻¹ ≠ 1 := by
    intro hcon; apply hy1
    rw [show (y : Auxiliary.ambientType) = d⁻¹ * (d * (y : Auxiliary.ambientType) * d⁻¹) * d by group, hcon]; group
  obtain ⟨a, ha, b, hb, hcomm⟩ := exists_commutator_eq_of_mem_auxiliary_subgroup_involution _ hzmem hz2 hz1
  have haH : d⁻¹ * a * d ∈ H := by
    rw [hd, show d * (d⁻¹ * a * d) * d⁻¹ = a by group]; exact ha
  have hbH : d⁻¹ * b * d ∈ H := by
    rw [hd, show d * (d⁻¹ * b * d) * d⁻¹ = b by group]; exact hb
  set p : ↥H := ⟨d⁻¹ * a * d, haH⟩ with hp_def
  set q : ↥H := ⟨d⁻¹ * b * d, hbH⟩ with hq_def
  have hpc : (p : Auxiliary.ambientType) = d⁻¹ * a * d := rfl
  have hqc : (q : Auxiliary.ambientType) = d⁻¹ * b * d := rfl
  have hyeq : y = p * q * p⁻¹ * q⁻¹ := by
    apply Subtype.ext
    push_cast
    rw [hpc, hqc,
      show (d⁻¹ * a * d) * (d⁻¹ * b * d) * (d⁻¹ * a * d)⁻¹ * (d⁻¹ * b * d)⁻¹
        = d⁻¹ * (a * b * a⁻¹ * b⁻¹) * d by group, hcomm]
    group
  rw [hyeq, hmul, hmul, hmul]
  have hp1 : σ.character p * σ.character p⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
  have hq1 : σ.character q * σ.character q⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
  calc σ.character p * σ.character q * σ.character p⁻¹ * σ.character q⁻¹
      = (σ.character p * σ.character p⁻¹) * (σ.character q * σ.character q⁻¹) := by ring
    _ = 1 := by rw [hp1, hq1]; ring

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                           
/-- Every element of the auxiliary subgroup has square one or cube one. -/
lemma sq_eq_one_or_cube_eq_one_of_mem_auxiliary_subgroup : ∀ w : Auxiliary.ambientType, w ∈ Auxiliary.subgroup → w ^ 2 = 1 ∨ w ^ 3 = 1 := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                                
                                                         
/-- Exactly four elements of the auxiliary subgroup have square one. -/
lemma card_auxiliary_subgroup_elements_sq_eq_one_eq_four :
    (univ.filter (fun g : Auxiliary.ambientType => g ∈ Auxiliary.subgroup ∧ g ^ 2 = 1)).card = 4 := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                              
                                                              
/-- The product of two elements of the auxiliary subgroup whose squares are one again has square one. -/
lemma mul_sq_eq_one_of_mem_auxiliary_subgroup : ∀ a : Auxiliary.ambientType, a ∈ Auxiliary.subgroup → a ^ 2 = 1 →
    ∀ b : Auxiliary.ambientType, b ∈ Auxiliary.subgroup → b ^ 2 = 1 → (a * b) ^ 2 = 1 := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                                   
                  
/-- The square of the commutator of two elements of the auxiliary subgroup is one. -/
lemma commutator_sq_eq_one_of_mem_auxiliary_subgroup : ∀ a : Auxiliary.ambientType, a ∈ Auxiliary.subgroup → ∀ b : Auxiliary.ambientType, b ∈ Auxiliary.subgroup →
    (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
                                                                                           
/-- Any two nonidentity involutions in the auxiliary subgroup are conjugate by an element of that subgroup. -/
lemma exists_conjugate_in_auxiliary_subgroup_of_involution : ∀ u : Auxiliary.ambientType, u ∈ Auxiliary.subgroup → u ^ 2 = 1 → u ≠ 1 →
    ∀ v : Auxiliary.ambientType, v ∈ Auxiliary.subgroup → v ^ 2 = 1 → v ≠ 1 →
      ∃ t : Auxiliary.ambientType, t ∈ Auxiliary.subgroup ∧ t * u * t⁻¹ = v := by decide

                                                                                             
                                                                                                
                                                                       
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012013 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ (σ : Type) = 1)
    (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![5, -1, 1, 0, 0] j := by
  classical
                                                       
  have hP1 : ∀ z : ↥H, (z : Auxiliary.ambientType) ^ 2 = 1 → σ.character z = 1 :=
    fun z hz => character_eq_one_on_involutions_of_finrank_one H hH σ hdim z hz
  have hone : σ.character (1 : ↥H) = 1 := hP1 1 (by simp)
  have hcard : (Fintype.card ↥H : ℂ) = 12 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
                                                                       
  have hj0 : (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0) = ![5, -1, 1, 0, 0] 0 := by
    rw [Auxiliary.statement012086, hcard]
    have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
        = ∑ x : Auxiliary.ambientType, if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 * x⁻¹ ∈ H then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 * x⁻¹ ∈ H
      · rw [dif_pos hx, if_pos hx]
        apply hP1
        change (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 * x⁻¹) ^ 2 = 1
        rw [show RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 = 1 from rfl, mul_one, mul_inv_cancel, one_pow]
      · rw [dif_neg hx, if_neg hx]
    rw [hsum, Finset.sum_boole, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hj2 : (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) = ![5, -1, 1, 0, 0] 2 := by
    rw [Auxiliary.statement012086, hcard]
    have hc2 : (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) ^ 2 = 1 := by
      have := RepresentationTheory.FiniteGroupRepresentation.orderFormula_011119; rw [← this]; exact pow_orderOf_eq_one _
    have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2 * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
        = ∑ x : Auxiliary.ambientType, if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2 * x⁻¹ ∈ H then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2 * x⁻¹ ∈ H
      · rw [dif_pos hx, if_pos hx]
        apply hP1
        change (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2 * x⁻¹) ^ 2 = 1
        have heq : (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2 * x⁻¹) ^ 2 = x * ((RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) ^ 2) * x⁻¹ := by
          rw [pow_two, pow_two]; group
        rw [heq, hc2]; group
      · rw [dif_neg hx, if_neg hx]
    rw [hsum, Finset.sum_boole, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hj3 : (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) = ![5, -1, 1, 0, 0] 3 := by
    rw [Auxiliary.statement012086, hcard]
    have hemp : ∀ x : Auxiliary.ambientType, x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * x⁻¹ ∉ H := by
      have hz : univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3 * x⁻¹ ∈ H) = ∅ := by
        rw [← Finset.card_eq_zero, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup]; rfl
      intro x; exact Finset.filter_eq_empty_iff.mp hz (mem_univ x)
    rw [Finset.sum_eq_zero (fun x _ => dif_neg (hemp x))]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hj4 : (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4) = ![5, -1, 1, 0, 0] 4 := by
    rw [Auxiliary.statement012086, hcard]
    have hemp : ∀ x : Auxiliary.ambientType, x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * x⁻¹ ∉ H := by
      have hz : univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 4 * x⁻¹ ∈ H) = ∅ := by
        rw [← Finset.card_eq_zero, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup]; rfl
      intro x; exact Finset.filter_eq_empty_iff.mp hz (mem_univ x)
    rw [Finset.sum_eq_zero (fun x _ => dif_neg (hemp x))]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hj1 : (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) = ![5, -1, 1, 0, 0] 1 := by
    rw [Auxiliary.statement012086, hcard]
    obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
                                                       
    have hdich : ∀ z : ↥H, (z : Auxiliary.ambientType) ^ 2 = 1 ∨ (z : Auxiliary.ambientType) ^ 3 = 1 := by
      intro z
      rcases sq_eq_one_or_cube_eq_one_of_mem_auxiliary_subgroup _ ((hd (z : Auxiliary.ambientType)).mp z.2) with h | h
      · left
        have heq : (d * (z : Auxiliary.ambientType) * d⁻¹) ^ 2 = d * ((z : Auxiliary.ambientType) ^ 2) * d⁻¹ := by
          rw [pow_two, pow_two]; group
        rw [heq] at h
        have hb : (z : Auxiliary.ambientType) ^ 2 = d⁻¹ * (d * ((z : Auxiliary.ambientType) ^ 2) * d⁻¹) * d := by group
        rw [h] at hb; rw [hb]; group
      · right
        have heq : (d * (z : Auxiliary.ambientType) * d⁻¹) ^ 3 = d * ((z : Auxiliary.ambientType) ^ 3) * d⁻¹ := by
          rw [pow_three', pow_three']; group
        rw [heq] at h
        have hb : (z : Auxiliary.ambientType) ^ 3 = d⁻¹ * (d * ((z : Auxiliary.ambientType) ^ 3) * d⁻¹) * d := by group
        rw [h] at hb; rw [hb]; group
                                         
    have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
      intro g
      obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
      have hcc : σ.character g = c := by
        change LinearMap.trace ℂ _ (σ.ρ g) = c
        rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
      rw [hcc]; exact hc
    have hmul : ∀ g k : ↥H, σ.character (g * k) = σ.character g * σ.character k := by
      intro g k
      have key : (σ.character (g * k) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
               = (σ.character g * σ.character k : ℂ) • LinearMap.id := by
        rw [← hscalar (g * k), map_mul, hscalar g, hscalar k]
        ext v
        simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
      have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
      rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one] at htr
                                                          
    have hF1 : ∑ z : ↥H, σ.character z = 0 := by
      obtain ⟨h0, hh0⟩ := hntriv
      have hbij : ∑ z : ↥H, σ.character (h0 * z) = ∑ z : ↥H, σ.character z := by
        have h := Equiv.sum_comp (Equiv.mulLeft h0) (fun z : ↥H => σ.character z)
        simpa using h
      have hpull : ∑ z : ↥H, σ.character (h0 * z) = σ.character h0 * ∑ z : ↥H, σ.character z := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => hmul h0 z)
      rw [hbij] at hpull
      have hzero : (σ.character h0 - 1) * ∑ z : ↥H, σ.character z = 0 := by
        rw [sub_mul, one_mul, ← hpull]; ring
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd (sub_eq_zero.mp h) hh0
      · exact h
                                                                                        
    have hAsum : ∑ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then σ.character z else 0) = 4 := by
      have hstep : ∑ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then σ.character z else 0)
          = ∑ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then (1 : ℂ) else 0) := by
        apply Finset.sum_congr rfl; intro z _
        by_cases hz2 : (z : Auxiliary.ambientType) ^ 2 = 1
        · rw [if_pos hz2, if_pos hz2, hP1 z hz2]
        · rw [if_neg hz2, if_neg hz2]
      rw [hstep, Finset.sum_boole]
      have hb1 : (univ.filter (fun z : ↥H => (z : Auxiliary.ambientType) ^ 2 = 1)).card
          = (univ.filter (fun g : Auxiliary.ambientType => g ∈ H ∧ g ^ 2 = 1)).card := by
        apply Finset.card_bij (fun (z : ↥H) _ => (z : Auxiliary.ambientType))
        · intro z hz
          simp only [mem_filter, mem_univ, true_and] at hz ⊢
          exact ⟨z.2, hz⟩
        · intro z1 _ z2 _ h; exact Subtype.ext h
        · intro g hg
          simp only [mem_filter, mem_univ, true_and] at hg
          exact ⟨⟨g, hg.1⟩, by simp only [mem_filter, mem_univ, true_and]; exact hg.2, rfl⟩
      have hb2 : (univ.filter (fun g : Auxiliary.ambientType => g ∈ H ∧ g ^ 2 = 1)).card
          = (univ.filter (fun g : Auxiliary.ambientType => g ∈ Auxiliary.subgroup ∧ g ^ 2 = 1)).card := by
        apply Finset.card_bij' (fun g _ => d * g * d⁻¹) (fun g _ => d⁻¹ * g * d)
        · intro g hg
          simp only [mem_filter, mem_univ, true_and] at hg ⊢
          refine ⟨(hd g).mp hg.1, ?_⟩
          have hp : (d * g * d⁻¹) ^ 2 = d * (g ^ 2) * d⁻¹ := by rw [pow_two, pow_two]; group
          rw [hp, hg.2]; group
        · intro g hg
          simp only [mem_filter, mem_univ, true_and] at hg ⊢
          refine ⟨?_, ?_⟩
          · rw [hd, show d * (d⁻¹ * g * d) * d⁻¹ = g by group]; exact hg.1
          · have hp : (d⁻¹ * g * d) ^ 2 = d⁻¹ * (g ^ 2) * d := by rw [pow_two, pow_two]; group
            rw [hp, hg.2]; group
        · intro g _; group
        · intro g _; group
      rw [hb1, hb2, card_auxiliary_subgroup_elements_sq_eq_one_eq_four]; norm_num
                                                                        
    have hkey : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
        = ∑ z : ↥H, σ.character z
            * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType))).card : ℂ) := by
      have hcast : ∀ z : ↥H,
          ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType))).card : ℂ)
            = ∑ x : Auxiliary.ambientType, if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType) then (1 : ℂ) else 0 := by
        intro z; rw [Finset.sum_boole]
      simp_rw [hcast, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ ∈ H
      · rw [dif_pos hx, Finset.sum_eq_single (⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹, hx⟩ : ↥H)
            (fun z _ hz => by rw [if_neg (fun hzeq => hz (Subtype.ext hzeq.symm)), mul_zero])
            (fun hnot => absurd (mem_univ _) hnot), if_pos rfl, mul_one]
      · rw [dif_neg hx]
        exact (Finset.sum_eq_zero (fun z _ => by
          rw [if_neg (fun hzeq => hx (by rw [hzeq]; exact z.2)), mul_zero])).symm
                                                                   
    have hN : ∀ z : ↥H,
        σ.character z * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType))).card : ℂ)
          = if (z : Auxiliary.ambientType) ^ 2 = 1 then 0 else 3 * σ.character z := by
      intro z
      by_cases hz2 : (z : Auxiliary.ambientType) ^ 2 = 1
      · rw [if_pos hz2]
        have hc0 : (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType))).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ hxeq
          have hsc : SemiconjBy x (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹) := by
            change x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 = x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ * x; group
          have hord : orderOf (z : Auxiliary.ambientType) = 3 := by
            rw [← hxeq, ← SemiconjBy.orderOf_eq x hsc, RepresentationTheory.FiniteGroupRepresentation.orderFormula_011118]
          have hdvd : orderOf (z : Auxiliary.ambientType) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
          rw [hord] at hdvd; omega
        rw [hc0]; simp
      · rw [if_neg hz2]
        have hcube : (z : Auxiliary.ambientType) ^ 3 = 1 := (hdich z).resolve_left hz2
        have hzne : (z : Auxiliary.ambientType) ≠ 1 := fun hh => hz2 (by rw [hh]; group)
        have hconj : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * c⁻¹ = (z : Auxiliary.ambientType) := by
          obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (z : Auxiliary.ambientType)
          rw [classIndex_eq_one_of_cube_eq_one (z : Auxiliary.ambientType) hcube hzne] at hc; exact ⟨c, hc⟩
        have hcnt : (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ = (z : Auxiliary.ambientType))).card = 3 := by
          rw [card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (z : Auxiliary.ambientType) hconj]
          have h := card_conjugators_to_rep_one 1; simpa using h
        rw [hcnt]; push_cast; ring
                                                                                       
    have htw1 : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1 * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
        = -12 := by
      rw [hkey, Finset.sum_congr rfl (fun z _ => hN z)]
      have hsplit : ∀ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then (0 : ℂ) else 3 * σ.character z)
          = 3 * σ.character z - (if (z : Auxiliary.ambientType) ^ 2 = 1 then 3 * σ.character z else 0) := by
        intro z; by_cases hh : (z : Auxiliary.ambientType) ^ 2 = 1 <;> simp [hh]
      rw [Finset.sum_congr rfl (fun z _ => hsplit z), Finset.sum_sub_distrib,
        ← Finset.mul_sum, hF1]
      have hsecond : ∑ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then 3 * σ.character z else 0)
          = 3 * ∑ z : ↥H, (if (z : Auxiliary.ambientType) ^ 2 = 1 then σ.character z else 0) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro z _; by_cases hh : (z : Auxiliary.ambientType) ^ 2 = 1 <;> simp [hh]
      rw [hsecond, hAsum]; ring
    rw [htw1]; norm_num
  fin_cases j
  · exact hj0
  · exact hj1
  · exact hj2
  · exact hj3
  · exact hj4

                                                                                         
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012010 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)]
    (hH : Nat.card H = 12) (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ (σ : Type) = 1)
    (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![5, -1, 1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012013 H hH σ hdim hntriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                          
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012012 (j : Fin 5) :
    RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo.character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![5, -1, 1, 0, 0] j := by
  rw [RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  fin_cases j <;>
    simp only [RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num

                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012011 (g : Auxiliary.ambientType) :
    RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo.character g = ![5, -1, 1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012012 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                        
                                                          
/-- An auxiliary isomorphism statement for the image of a simple rank-one subgroup representation whose character is not constantly one. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem Auxiliary.simpleFinrankOneNontrivialIso (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [Auxiliary.statement012010 H hH σ hdim hntriv g,
    Auxiliary.statement012011 g]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                                          
                                                                                           
/-- Conjugate indexed representatives have equal indices. -/
lemma eq_of_representatives_conjugate (i j : Fin 5)
    (h : ∃ c : Auxiliary.ambientType, c * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative i * c⁻¹ = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) : i = j := by
  revert i j; decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
                                                                    
/-- The class-index map sends the representative indexed by a point to that point. -/
lemma classIndex_representative (j : Fin 5) : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = j := by
  revert j; decide

                                                                           
/-- The class index of a conjugate equals the class index of the original element. -/
lemma classIndex_conj (x g : Auxiliary.ambientType) : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (x * g * x⁻¹) = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g := by
  apply eq_of_representatives_conjugate
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (x * g * x⁻¹)
  obtain ⟨d, hd⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  refine ⟨d⁻¹ * x⁻¹ * c, ?_⟩
  have e1 : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (x * g * x⁻¹)) = c⁻¹ * (x * g * x⁻¹) * c := by
    conv_rhs => rw [← hc]
    group
  have e2 : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) = d⁻¹ * g * d := by
    conv_rhs => rw [← hd]
    group
  rw [e1, e2]; group

                                                                                            
                                                                                             
                                                                                            
                                                                  

                                                                                            
                                                                                     
                                                                                          
                       
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012028 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H)
    (hcharval : ∀ h : ↥H, σ.character h = (![3, 0, -1, 0, 0] : Fin 5 → ℂ) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (h : Auxiliary.ambientType)))
    (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, -1, 0, 0] j := by
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 12 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  set w : ℂ := (![3, 0, -1, 0, 0] : Fin 5 → ℂ) j with hw
  have hsum : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = w * ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H)).card : ℂ) := by
    have hstep : (∑ x : Auxiliary.ambientType, if h : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
        = ∑ x : Auxiliary.ambientType, if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then w else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
      · rw [dif_pos hx, if_pos hx, hcharval ⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hx⟩, hw]
        congr 1
        change RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹) = j
        rw [classIndex_conj, classIndex_representative]
      · rw [dif_neg hx, if_neg hx]
    rw [hstep, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum, card_conjugating_elements_conj_mem_eq_auxiliary_subgroup_of_card_twelve H hH, card_conjugating_elements_conj_representative_mem_auxiliary_subgroup, hcard, hw]
  fin_cases j <;> norm_num

                                                                                         
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012025 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H)
    (hcharval : ∀ h : ↥H, σ.character h = (![3, 0, -1, 0, 0] : Fin 5 → ℂ) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (h : Auxiliary.ambientType)))
    (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![15, 0, -1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012028 H hH σ hcharval (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                             

                                                                                                
                                                                                                  
                                                                                              
                                                                                             
                                                                                                
                                                                      

section SchurScalar

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
                                                                                                     
private lemma finrank_pos_of_simple' (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  by_contra hcon
  push Not at hcon
  have h0 : Module.finrank ℂ V = 0 := Nat.eq_zero_of_le_zero hcon
  have hsub : Subsingleton (V : Type _) := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (V ⟶ V) := by
    constructor; intro f g
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have hone : Module.finrank ℂ (V ⟶ V) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]; simp
  have hzero : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  omega

omit [Fintype G] in
private lemma finrank_ne_zero_cx' (V : FDRep ℂ G) [Simple V] :
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  have := finrank_pos_of_simple' V
  exact_mod_cast this.ne'

omit [Fintype G] in
                                                                                                 
                                                                                                   
                                                                    
private lemma endo_scalar' (V : FDRep ℂ G) [Simple V]
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id ∧
      LinearMap.trace ℂ V T = c * (Module.finrank ℂ V : ℂ) := by
  have hmemT : T ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply, hT g⁻¹, ← LinearMap.comp_assoc,
      show V.ρ g ∘ₗ V.ρ g⁻¹ = LinearMap.id by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id],
      LinearMap.id_comp]
  have h1dim : Module.finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
  have hid_mem : (LinearMap.id : V →ₗ[ℂ] V) ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro hz
    have : (Module.finrank ℂ V : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := V), hz, map_zero]
    exact finrank_ne_zero_cx' V this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim
    ⟨T, hmemT⟩
  have hTeq : T = c • LinearMap.id := by
    have hval := congrArg Subtype.val hc
    simpa using hval.symm
  refine ⟨c, hTeq, ?_⟩
  rw [hTeq, map_smul, LinearMap.trace_id, smul_eq_mul]

end SchurScalar

                                                                                                  
                                                                                                    
                                                                                                   
                                  
/-- An auxiliary subgroup of a subgroup known to have cardinality twelve. -/
def Auxiliary.subgroupOfCardTwelve (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12) : Subgroup ↥H where
  carrier := {y : ↥H | (y : Auxiliary.ambientType) ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have haA : d * (a : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd (a : Auxiliary.ambientType)).mp a.2
    have hbA : d * (b : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd (b : Auxiliary.ambientType)).mp b.2
    have ha2 : (d * (a : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by
      rw [show (d * (a : Auxiliary.ambientType) * d⁻¹) ^ 2 = d * ((a : Auxiliary.ambientType) ^ 2) * d⁻¹ by
        rw [pow_two, pow_two]; group, ha]; group
    have hb2 : (d * (b : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by
      rw [show (d * (b : Auxiliary.ambientType) * d⁻¹) ^ 2 = d * ((b : Auxiliary.ambientType) ^ 2) * d⁻¹ by
        rw [pow_two, pow_two]; group, hb]; group
    have hmul := mul_sq_eq_one_of_mem_auxiliary_subgroup _ haA ha2 _ hbA hb2
    have hcoe : ((a * b : ↥H) : Auxiliary.ambientType) = (a : Auxiliary.ambientType) * (b : Auxiliary.ambientType) := by push_cast; rfl
    rw [hcoe]
    have key : (d * ((a : Auxiliary.ambientType) * (b : Auxiliary.ambientType)) * d⁻¹) ^ 2 = 1 := by
      rw [show d * ((a : Auxiliary.ambientType) * (b : Auxiliary.ambientType)) * d⁻¹ = (d * (a : Auxiliary.ambientType) * d⁻¹) * (d * (b : Auxiliary.ambientType) * d⁻¹) by
        group]; exact hmul
    rw [show ((a : Auxiliary.ambientType) * (b : Auxiliary.ambientType)) ^ 2
        = d⁻¹ * ((d * ((a : Auxiliary.ambientType) * (b : Auxiliary.ambientType)) * d⁻¹) ^ 2) * d by rw [pow_two, pow_two]; group,
      key]; group
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hcoe : ((a⁻¹ : ↥H) : Auxiliary.ambientType) = (a : Auxiliary.ambientType)⁻¹ := by push_cast; rfl
    rw [hcoe, show ((a : Auxiliary.ambientType)⁻¹) ^ 2 = ((a : Auxiliary.ambientType) ^ 2)⁻¹ by group, ha, inv_one]

                                                                                                 
                                              
/-- The auxiliary subgroup selected inside a subgroup of cardinality twelve has cardinality four. -/
lemma natCard_subgroupOfCardTwelve_eq_four (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12) :
    Nat.card ↥(Auxiliary.subgroupOfCardTwelve H hH) = 4 := by
  classical
  obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
  have fwd_mem : ∀ y : ↥(Auxiliary.subgroupOfCardTwelve H hH), d * ((y : ↥H) : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup ∧
      (d * ((y : ↥H) : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by
    intro y
    refine ⟨(hd _).mp (y : ↥H).2, ?_⟩
    rw [show (d * (((y : ↥H) : Auxiliary.ambientType)) * d⁻¹) ^ 2 = d * ((((y : ↥H) : Auxiliary.ambientType)) ^ 2) * d⁻¹ by
      rw [pow_two, pow_two]; group, show (((y : ↥H) : Auxiliary.ambientType)) ^ 2 = 1 from y.2]; group
  have bwd_memH : ∀ z : {z : Auxiliary.ambientType // z ∈ Auxiliary.subgroup ∧ z ^ 2 = 1}, d⁻¹ * (z : Auxiliary.ambientType) * d ∈ H := by
    intro z
    refine (hd _).mpr ?_
    rw [show d * (d⁻¹ * (z : Auxiliary.ambientType) * d) * d⁻¹ = (z : Auxiliary.ambientType) by group]; exact z.2.1
  have bwd_mem : ∀ z : {z : Auxiliary.ambientType // z ∈ Auxiliary.subgroup ∧ z ^ 2 = 1},
      (⟨d⁻¹ * (z : Auxiliary.ambientType) * d, bwd_memH z⟩ : ↥H) ∈ Auxiliary.subgroupOfCardTwelve H hH := by
    intro z
    change (d⁻¹ * (z : Auxiliary.ambientType) * d) ^ 2 = 1
    rw [show (d⁻¹ * (z : Auxiliary.ambientType) * d) ^ 2 = d⁻¹ * ((z : Auxiliary.ambientType) ^ 2) * d by
      rw [pow_two, pow_two]; group, z.2.2]; group
  let e : ↥(Auxiliary.subgroupOfCardTwelve H hH) ≃ {z : Auxiliary.ambientType // z ∈ Auxiliary.subgroup ∧ z ^ 2 = 1} :=
    { toFun := fun y => ⟨d * ((y : ↥H) : Auxiliary.ambientType) * d⁻¹, fwd_mem y⟩
      invFun := fun z => ⟨⟨d⁻¹ * (z : Auxiliary.ambientType) * d, bwd_memH z⟩, bwd_mem z⟩
      left_inv := fun y => by
        apply Subtype.ext; apply Subtype.ext
        change d⁻¹ * (d * (((y : ↥H) : Auxiliary.ambientType)) * d⁻¹) * d = (((y : ↥H) : Auxiliary.ambientType)); group
      right_inv := fun z => by
        apply Subtype.ext
        change d * (d⁻¹ * (z : Auxiliary.ambientType) * d) * d⁻¹ = (z : Auxiliary.ambientType); group }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_auxiliary_subgroup_elements_sq_eq_one_eq_four

                                                                                               
                                                                                                    
                                                                                     
/-- A character on a subgroup of cardinality twelve takes the same value on all nonidentity elements whose images in the ambient group have square one. -/
lemma character_eq_on_nontrivial_involutions_of_card_twelve (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12) (σ : FDRep ℂ ↥H)
    (h : ↥H) (hh2 : (h : Auxiliary.ambientType) ^ 2 = 1) (hh1 : h ≠ 1)
    (y : ↥H) (hy2 : (y : Auxiliary.ambientType) ^ 2 = 1) (hy1 : y ≠ 1) :
    σ.character y = σ.character h := by
  obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
  have conj_sq : ∀ w : Auxiliary.ambientType, (d * w * d⁻¹) ^ 2 = d * (w ^ 2) * d⁻¹ := by
    intro w; rw [pow_two, pow_two]; group
  have conj_ne : ∀ w : ↥H, w ≠ 1 → d * (w : Auxiliary.ambientType) * d⁻¹ ≠ 1 := by
    intro w hw hc; apply hw
    have hw1 : (w : Auxiliary.ambientType) = 1 := by
      rw [show (w : Auxiliary.ambientType) = d⁻¹ * (d * (w : Auxiliary.ambientType) * d⁻¹) * d by group, hc]; group
    exact Subtype.ext hw1
  have hyA : d * (y : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd (y : Auxiliary.ambientType)).mp y.2
  have hhA : d * (h : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd (h : Auxiliary.ambientType)).mp h.2
  have hyA2 : (d * (y : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by rw [conj_sq, hy2]; group
  have hhA2 : (d * (h : Auxiliary.ambientType) * d⁻¹) ^ 2 = 1 := by rw [conj_sq, hh2]; group
  obtain ⟨t, htA, htconj⟩ :=
    exists_conjugate_in_auxiliary_subgroup_of_involution _ hyA hyA2 (conj_ne y hy1) _ hhA hhA2 (conj_ne h hh1)
  have hsH : d⁻¹ * t * d ∈ H := by
    rw [hd, show d * (d⁻¹ * t * d) * d⁻¹ = t by group]; exact htA
  set s : ↥H := ⟨d⁻¹ * t * d, hsH⟩ with hs
  have hsyconj : s * y * s⁻¹ = h := by
    apply Subtype.ext
    have hcoe : ((s * y * s⁻¹ : ↥H) : Auxiliary.ambientType) = (d⁻¹ * t * d) * (y : Auxiliary.ambientType) * (d⁻¹ * t * d)⁻¹ := by
      push_cast; rfl
    rw [hcoe, show (d⁻¹ * t * d) * (y : Auxiliary.ambientType) * (d⁻¹ * t * d)⁻¹
      = d⁻¹ * (t * (d * (y : Auxiliary.ambientType) * d⁻¹) * t⁻¹) * d by group, htconj]; group
  rw [← hsyconj, FDRep.char_conj]

                                                                                              
                                                                                          
/-- The normalized character sum over a finite subgroup equals the dimension of the invariant subspace. -/
lemma average_character_eq_finrank_invariants {H : Subgroup Auxiliary.ambientType} (σ : FDRep ℂ ↥H) (K : Subgroup ↥H)
    [Fintype ↥K] [Invertible (Fintype.card ↥K : ℂ)] :
    ⅟(Fintype.card ↥K : ℂ) • ∑ g : ↥K, σ.character (g : ↥H)
      = (Module.finrank ℂ
          (Representation.invariants (FDRep.ρ ((Action.res (FGModuleCat ℂ) K.subtype).obj σ))) : ℂ)
          := by
  rw [show (∑ g : ↥K, σ.character (g : ↥H))
      = ∑ g : ↥K, FDRep.character ((Action.res (FGModuleCat ℂ) K.subtype).obj σ) g from
    Finset.sum_congr rfl (fun g _ => rfl)]
  rw [smul_eq_mul, invOf_eq_inv, ← Nat.card_eq_fintype_card]
  exact FDRep.average_char_eq_finrank_invariants
    ((Action.res (FGModuleCat ℂ) K.subtype).obj σ)

                                                                                                
                                                                                        
              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement011923 (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 3)
    (h : ↥H) (hh2 : h ^ 2 = 1) (hh1 : h ≠ 1) :
    σ.character h = -1 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hhA5 : (h : Auxiliary.ambientType) ^ 2 = 1 := by
    have hc : ((h ^ 2 : ↥H) : Auxiliary.ambientType) = (h : Auxiliary.ambientType) ^ 2 := by push_cast; rfl
    rw [← hc, hh2]; rfl
  set a : ℂ := σ.character h with ha_def
                                                                                     
  set T : Module.End ℂ σ := σ.ρ h with hT_def
  have htr_T : LinearMap.trace ℂ σ T = a := by rw [hT_def, ha_def]; rfl
  have hρ2 : T * T = 1 := by rw [hT_def, ← map_mul, ← pow_two, hh2, map_one]
  set p : Module.End ℂ σ := (2⁻¹ : ℂ) • (1 + T) with hp_def
  have hp_idem : IsIdempotentElem p := by
    change p * p = p
    rw [hp_def, smul_mul_smul_comm,
      show (1 + T) * (1 + T) = 1 + T + T + T * T by noncomm_ring, hρ2,
      show (1 : Module.End ℂ σ) + T + T + 1 = (2 : ℂ) • (1 + T) by
        rw [smul_add, two_smul, two_smul]; abel,
      smul_smul, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]
  have htr_p : LinearMap.trace ℂ σ p = 2⁻¹ * (3 + a) := by
    rw [hp_def, map_smul, map_add, htr_T,
      show LinearMap.trace ℂ σ (1 : Module.End ℂ σ) = 3 by
        rw [Module.End.one_eq_id, LinearMap.trace_id, hdim]; norm_num, smul_eq_mul]
  obtain ⟨m, hm_eq, hm3⟩ :
      ∃ m : ℕ, (m : ℂ) = 2⁻¹ * (3 + a) ∧ m ≤ 3 := by
    refine ⟨Module.finrank ℂ (LinearMap.range p), ?_, ?_⟩
    · rw [← htr_p, ((LinearMap.isProj_range_iff_isIdempotentElem p).mpr hp_idem).trace]
    · calc Module.finrank ℂ (LinearMap.range p)
          ≤ Module.finrank ℂ σ := Submodule.finrank_le _
        _ = 3 := hdim
  have hma : 3 + a = 2 * (m : ℂ) := by rw [hm_eq]; ring
                                                                                   
  haveI : Fintype ↥(Auxiliary.subgroupOfCardTwelve H hH) := Fintype.ofFinite _
  have hcard4 : Fintype.card ↥(Auxiliary.subgroupOfCardTwelve H hH) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact natCard_subgroupOfCardTwelve_eq_four H hH
  have hcardC : (Fintype.card ↥(Auxiliary.subgroupOfCardTwelve H hH) : ℂ) = 4 := by rw [hcard4]; norm_num
  haveI : Invertible (Fintype.card ↥(Auxiliary.subgroupOfCardTwelve H hH) : ℂ) :=
    invertibleOfNonzero (by rw [hcardC]; norm_num)
  have hone_term : σ.character (((1 : ↥(Auxiliary.subgroupOfCardTwelve H hH)) : ↥H)) = 3 := by
    rw [show ((1 : ↥(Auxiliary.subgroupOfCardTwelve H hH)) : ↥H) = 1 from OneMemClass.coe_one _, FDRep.char_one, hdim]
    norm_num
  have hconst : ∀ g ∈ (Finset.univ.erase (1 : ↥(Auxiliary.subgroupOfCardTwelve H hH))),
      σ.character ((g : ↥H)) = a := by
    intro g hg
    rw [Finset.mem_erase] at hg
    have hgH1 : (g : ↥H) ≠ 1 := fun hcon => hg.1 (Subtype.ext hcon)
    have hgA5 : ((g : ↥H) : Auxiliary.ambientType) ^ 2 = 1 := g.2
    rw [ha_def]; exact character_eq_on_nontrivial_involutions_of_card_twelve H hH σ h hhA5 hh1 (g : ↥H) hgA5 hgH1
  have hsum : ∑ g : ↥(Auxiliary.subgroupOfCardTwelve H hH), σ.character ((g : ↥H)) = 3 + 3 * a := by
    have h1 : ∑ g : ↥(Auxiliary.subgroupOfCardTwelve H hH), σ.character ((g : ↥H))
        = σ.character (((1 : ↥(Auxiliary.subgroupOfCardTwelve H hH)) : ↥H))
          + ∑ g ∈ Finset.univ.erase (1 : ↥(Auxiliary.subgroupOfCardTwelve H hH)), σ.character ((g : ↥H)) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    rw [h1, hone_term, Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard4]
    change (3 : ℂ) + (4 - 1) • a = 3 + 3 * a
    rw [nsmul_eq_mul]; push_cast; ring
  have havg := average_character_eq_finrank_invariants σ (Auxiliary.subgroupOfCardTwelve H hH)
  rw [hsum] at havg
  set N : ℕ := Module.finrank ℂ (Representation.invariants
    (FDRep.ρ ((Action.res (FGModuleCat ℂ) (Auxiliary.subgroupOfCardTwelve H hH).subtype).obj σ))) with hN_def
  have hn_eq : 3 + 3 * a = 4 * (N : ℂ) := by
    rw [smul_eq_mul, invOf_eq_inv, hcardC] at havg
    have h4 : (4 : ℂ) * ((4 : ℂ)⁻¹ * (3 + 3 * a)) = 4 * (N : ℂ) := by rw [havg]
    rwa [← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_mul] at h4
  have hN3 : N ≤ 3 := by
    rw [hN_def]
    calc Module.finrank ℂ (Representation.invariants
          (FDRep.ρ ((Action.res (FGModuleCat ℂ) (Auxiliary.subgroupOfCardTwelve H hH).subtype).obj σ)))
        ≤ Module.finrank ℂ ((Action.res (FGModuleCat ℂ) (Auxiliary.subgroupOfCardTwelve H hH).subtype).obj σ) :=
          Submodule.finrank_le _
      _ = 3 := hdim
                                                                                   
  have hkeyC : (6 : ℂ) * (m : ℂ) = 4 * (N : ℂ) + 6 := by linear_combination hn_eq - 3 * hma
  have hkey : 6 * m = 4 * N + 6 := by exact_mod_cast hkeyC
  interval_cases m
  · exfalso; omega
  ·                    
    have h1 : (3 : ℂ) + a = 2 * ((1 : ℕ) : ℂ) := hma
    push_cast at h1; linear_combination h1
  · exfalso; omega
  ·                                                                            
    exfalso
    have hN3' : N = 3 := by omega
    have hinv_top : Representation.invariants
        (FDRep.ρ ((Action.res (FGModuleCat ℂ) (Auxiliary.subgroupOfCardTwelve H hH).subtype).obj σ)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← hN_def, hN3']; exact hdim.symm
                                                
    have hV4id : ∀ w : ↥H, (w : Auxiliary.ambientType) ^ 2 = 1 → σ.ρ w = 1 := by
      intro w hw
      have hwV : w ∈ Auxiliary.subgroupOfCardTwelve H hH := hw
      ext x
                                                                            
                                                                            
                                                                             
                                                                         
                                           
      have hx : x ∈ Representation.invariants
          (FDRep.ρ ((Action.res (FGModuleCat ℂ) (Auxiliary.subgroupOfCardTwelve H hH).subtype).obj σ)) :=
        (Submodule.eq_top_iff'.mp hinv_top) x
      have hfix := (Representation.mem_invariants _ x).mp hx (⟨w, hwV⟩ : ↥(Auxiliary.subgroupOfCardTwelve H hH))
      change (σ.ρ w) x = x
      exact hfix
                                                              
    have hcomm : ∀ g k : ↥H, σ.ρ g * σ.ρ k = σ.ρ k * σ.ρ g := by
      intro g k
      obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
      have hgA : d * (g : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd _).mp g.2
      have hkA : d * (k : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd _).mp k.2
      have hcs := commutator_sq_eq_one_of_mem_auxiliary_subgroup _ hgA _ hkA
      have hc : ((g * k * g⁻¹ * k⁻¹ : ↥H) : Auxiliary.ambientType) ^ 2 = 1 := by
        have hcoe : ((g * k * g⁻¹ * k⁻¹ : ↥H) : Auxiliary.ambientType)
            = (g : Auxiliary.ambientType) * (k : Auxiliary.ambientType) * (g : Auxiliary.ambientType)⁻¹ * (k : Auxiliary.ambientType)⁻¹ := by push_cast; rfl
        rw [hcoe]
        have key : (d * ((g : Auxiliary.ambientType) * (k : Auxiliary.ambientType) * (g : Auxiliary.ambientType)⁻¹ * (k : Auxiliary.ambientType)⁻¹) * d⁻¹) ^ 2 = 1 := by
          rw [show d * ((g : Auxiliary.ambientType) * (k : Auxiliary.ambientType) * (g : Auxiliary.ambientType)⁻¹ * (k : Auxiliary.ambientType)⁻¹) * d⁻¹
            = (d * (g : Auxiliary.ambientType) * d⁻¹) * (d * (k : Auxiliary.ambientType) * d⁻¹) * (d * (g : Auxiliary.ambientType) * d⁻¹)⁻¹
              * (d * (k : Auxiliary.ambientType) * d⁻¹)⁻¹ by group]
          exact hcs
        rw [show ((g : Auxiliary.ambientType) * (k : Auxiliary.ambientType) * (g : Auxiliary.ambientType)⁻¹ * (k : Auxiliary.ambientType)⁻¹) ^ 2
          = d⁻¹ * ((d * ((g : Auxiliary.ambientType) * (k : Auxiliary.ambientType) * (g : Auxiliary.ambientType)⁻¹ * (k : Auxiliary.ambientType)⁻¹) * d⁻¹) ^ 2) * d by
            rw [pow_two, pow_two]; group, key]; group
      have hρcomm : σ.ρ (g * k) = σ.ρ (k * g) := by
        have hR : σ.ρ ((k * g)⁻¹) * σ.ρ (k * g) = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        have hPR : σ.ρ (g * k) * σ.ρ ((k * g)⁻¹) = 1 := by
          rw [← map_mul, show (g * k) * (k * g)⁻¹ = g * k * g⁻¹ * k⁻¹ by group]
          exact hV4id _ hc
        calc σ.ρ (g * k)
            = σ.ρ (g * k) * (σ.ρ ((k * g)⁻¹) * σ.ρ (k * g)) := by rw [hR, mul_one]
          _ = (σ.ρ (g * k) * σ.ρ ((k * g)⁻¹)) * σ.ρ (k * g) := by rw [mul_assoc]
          _ = σ.ρ (k * g) := by rw [hPR, one_mul]
      rw [← map_mul, ← map_mul, hρcomm]
                                                                    
    have hscalar : ∀ g : ↥H, ∃ c : ℂ, (σ.ρ g : σ →ₗ[ℂ] σ) = c • LinearMap.id := by
      intro g
      obtain ⟨c, hc, -⟩ := endo_scalar' σ (σ.ρ g)
        (fun k => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]; exact hcomm g k)
      exact ⟨c, hc⟩
                                                  
    have hall : ∀ Tm : σ →ₗ[ℂ] σ, ∃ c : ℂ, Tm = c • LinearMap.id := by
      intro Tm
      obtain ⟨c, hc, -⟩ := endo_scalar' σ Tm (fun g => by
        obtain ⟨cg, hcg⟩ := hscalar g
        rw [hcg, LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp])
      exact ⟨c, hc⟩
    have hid_ne : (LinearMap.id : σ →ₗ[ℂ] σ) ≠ 0 := by
      intro hcon
      haveI : Subsingleton (σ : Type) := ⟨fun x y => by
        have hx : x = 0 := by have := LinearMap.congr_fun hcon x; simpa using this
        have hy : y = 0 := by have := LinearMap.congr_fun hcon y; simpa using this
        rw [hx, hy]⟩
      have hf0 : Module.finrank ℂ σ = 0 := Module.finrank_zero_of_subsingleton
      rw [hdim] at hf0; norm_num at hf0
                                                                                          
    have hspan_top : (ℂ ∙ (LinearMap.id : σ →ₗ[ℂ] σ)) = ⊤ := by
      refine le_antisymm le_top (fun Tm _ => ?_)
      obtain ⟨c, hc⟩ := hall Tm
      rw [hc]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hfr1 : Module.finrank ℂ (σ →ₗ[ℂ] σ) = 1 := by
      have hs := finrank_span_singleton (K := ℂ) hid_ne
      rw [hspan_top, finrank_top] at hs; exact hs
    rw [Module.finrank_linearMap, hdim] at hfr1
    norm_num at hfr1

                                                                                               
                                                                                                  
                                                                                                 
                                                                                    

                                                                                                  
                                                                                                 
                             
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement011929 (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 3) (h : ↥H) :
    σ.character h = (![3, 0, -1, 0, 0] : Fin 5 → ℂ) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (h : Auxiliary.ambientType)) := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
                                      
  have coe_one_iff : (h : Auxiliary.ambientType) = 1 ↔ h = 1 :=
    ⟨fun hc => Subtype.ext (hc.trans (Subgroup.coe_one H).symm), fun hc => by rw [hc]; rfl⟩
  by_cases hh1 : h = 1
  ·                                                             
    subst hh1
    rw [Subgroup.coe_one, show (1 : Auxiliary.ambientType) = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 0 from rfl, classIndex_representative,
      FDRep.char_one, hdim]
    norm_num
  ·                                               
    have hne5 : (h : Auxiliary.ambientType) ≠ 1 := fun hc => hh1 (coe_one_iff.mp hc)
    obtain ⟨d, hd⟩ := exists_conjugate_auxiliary_subgroup_of_card_twelve H hH
    have hmemA : d * (h : Auxiliary.ambientType) * d⁻¹ ∈ Auxiliary.subgroup := (hd _).mp h.2
    have hdich : (h : Auxiliary.ambientType) ^ 2 = 1 ∨ (h : Auxiliary.ambientType) ^ 3 = 1 := by
      rcases sq_eq_one_or_cube_eq_one_of_mem_auxiliary_subgroup _ hmemA with h2 | h3
      · left
        have e2 : d * ((h : Auxiliary.ambientType) ^ 2) * d⁻¹ = 1 := by
          rw [show d * ((h : Auxiliary.ambientType) ^ 2) * d⁻¹ = (d * (h : Auxiliary.ambientType) * d⁻¹) ^ 2 by
            rw [pow_two, pow_two]; group]
          exact h2
        have : (h : Auxiliary.ambientType) ^ 2 = d⁻¹ * 1 * d := by rw [← e2]; group
        rw [this]; group
      · right
        have e3 : d * ((h : Auxiliary.ambientType) ^ 3) * d⁻¹ = 1 := by
          rw [show d * ((h : Auxiliary.ambientType) ^ 3) * d⁻¹ = (d * (h : Auxiliary.ambientType) * d⁻¹) ^ 3 by
            rw [pow_three', pow_three']; group]
          exact h3
        have : (h : Auxiliary.ambientType) ^ 3 = d⁻¹ * 1 * d := by rw [← e3]; group
        rw [this]; group
    rcases hdich with hsq | hcube
    ·                                                          
      have hh2 : h ^ 2 = 1 := by
        have hc : ((h ^ 2 : ↥H) : Auxiliary.ambientType) = 1 := by
          rw [show ((h ^ 2 : ↥H) : Auxiliary.ambientType) = (h : Auxiliary.ambientType) ^ 2 by push_cast; rfl, hsq]
        exact Subtype.ext (hc.trans (Subgroup.coe_one H).symm)
      rw [Auxiliary.statement011923 H hH σ hdim h hh2 hh1,
        RepresentationTheory.FiniteGroupRepresentation.valueFormula_011000 (h : Auxiliary.ambientType) hsq hne5]
      norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ·                                                                                  
      rw [classIndex_eq_one_of_cube_eq_one (h : Auxiliary.ambientType) hcube hne5]
                                                       
      have hnsq : ¬ (h : Auxiliary.ambientType) ^ 2 = 1 := by
        intro hsq2
        apply hne5
        have : (h : Auxiliary.ambientType) = (h : Auxiliary.ambientType) ^ 3 * ((h : Auxiliary.ambientType) ^ 2)⁻¹ := by group
        rw [this, hcube, hsq2]; group
                                                          
      have hcardH : Fintype.card ↥H = 12 := by rw [← Nat.card_eq_fintype_card, hH]
      have hcardC : (Fintype.card ↥H : ℂ) = 12 := by rw [hcardH]; norm_num
      haveI : Invertible (Fintype.card ↥H : ℂ) :=
        invertibleOfNonzero (by rw [hcardC]; norm_num)
      have horth := FDRep.char_orthonormal σ σ
      rw [if_pos ⟨CategoryTheory.Iso.refl σ⟩] at horth
      rw [Nat.card_eq_fintype_card] at horth
      have hSeq : (∑ g : ↥H, σ.character g * σ.character g⁻¹) = (Fintype.card ↥H : ℂ) := by
        have hne0 : (Fintype.card ↥H : ℂ) ≠ 0 := by rw [hcardC]; norm_num
        field_simp [hne0] at horth
        linear_combination horth
                                                                        
      have hnorm : ∀ g : ↥H,
          σ.character g * σ.character g⁻¹ = (Complex.normSq (σ.character g) : ℂ) := by
        intro g; rw [RepresentationTheory.Group.CharacterOperations.character_inv_eq_conj, Complex.mul_conj]
      have hbig : (∑ g : ↥H, (Complex.normSq (σ.character g) : ℂ)) = (12 : ℂ) := by
        rw [Finset.sum_congr rfl (fun g _ => (hnorm g).symm), hSeq, hcardC]
      have hsumR : (∑ g : ↥H, Complex.normSq (σ.character g)) = (12 : ℝ) := by
        rw [← Complex.ofReal_sum] at hbig; exact_mod_cast hbig
                                                                                            
      set S1 : Finset ↥H := univ.filter (fun g : ↥H => (g : Auxiliary.ambientType) ^ 2 = 1) with hS1
      have hS1card : S1.card = 4 := by
        have hcard4 : Fintype.card ↥(Auxiliary.subgroupOfCardTwelve H hH) = 4 := by
          rw [← Nat.card_eq_fintype_card]; exact natCard_subgroupOfCardTwelve_eq_four H hH
        have h1 : S1.card = Fintype.card {g : ↥H // (g : Auxiliary.ambientType) ^ 2 = 1} := by
          rw [hS1]; exact (Fintype.card_subtype _).symm
        have h2 : Fintype.card {g : ↥H // (g : Auxiliary.ambientType) ^ 2 = 1} = Fintype.card ↥(Auxiliary.subgroupOfCardTwelve H hH) :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
        rw [h1, h2, hcard4]
      have h1memS1 : (1 : ↥H) ∈ S1 := by
        rw [hS1, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [Subgroup.coe_one]; group⟩
                                                                      
      have hS1sum : (∑ g ∈ S1, Complex.normSq (σ.character g)) = 12 := by
        rw [← Finset.add_sum_erase _ _ h1memS1]
        have hid : Complex.normSq (σ.character (1 : ↥H)) = 9 := by
          rw [FDRep.char_one, hdim]; norm_num [Complex.normSq]
        have herase : ∀ g ∈ S1.erase 1, Complex.normSq (σ.character g) = 1 := by
          intro g hg
          rw [Finset.mem_erase, hS1, Finset.mem_filter] at hg
          obtain ⟨hgne, -, hg2⟩ := hg
          rw [Auxiliary.statement011923 H hH σ hdim g (by
            have hc : ((g ^ 2 : ↥H) : Auxiliary.ambientType) = 1 := by
              rw [show ((g ^ 2 : ↥H) : Auxiliary.ambientType) = (g : Auxiliary.ambientType) ^ 2 by push_cast; rfl, hg2]
            exact Subtype.ext (hc.trans (Subgroup.coe_one H).symm)) hgne]
          norm_num [Complex.normSq]
        rw [hid, Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem h1memS1,
          hS1card]
        norm_num
                                                                         
      have hcompl : (∑ g ∈ univ.filter (fun g : ↥H => ¬ (g : Auxiliary.ambientType) ^ 2 = 1),
          Complex.normSq (σ.character g)) = 0 := by
        have hsplit := Finset.sum_filter_add_sum_filter_not univ
          (fun g : ↥H => (g : Auxiliary.ambientType) ^ 2 = 1) (fun g => Complex.normSq (σ.character g))
        rw [← hS1] at hsplit
        rw [hsumR, hS1sum] at hsplit
        linarith [hsplit]
      have hhmem : h ∈ univ.filter (fun g : ↥H => ¬ (g : Auxiliary.ambientType) ^ 2 = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnsq⟩
      have hzero : Complex.normSq (σ.character h) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => Complex.normSq_nonneg _)).mp hcompl h hhmem
      rw [Complex.normSq_eq_zero.mp hzero]
      norm_num

                                                                                              
                                                             
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012027 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, -1, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012026 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g = ![15, 0, -1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012027 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                
                                                                                     
/-- The auxiliary construction applied to a simple rank-three representation of a subgroup of cardinality twelve is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_finrank_three_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 3) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [Auxiliary.statement012025 H hH σ (fun h => Auxiliary.statement011929 H hH σ hdim h) g,
    Auxiliary.statement012026 g]

                                   

                                                                                  
                                                                                           
                                                                                           
                                                                                      
                                                                                    
                                                                                            
                                                                   
                                                                      

set_option maxRecDepth 8000 in
                                                                              
set_option maxHeartbeats 4000000 in
                                                                                             
                                                                            
/-- An element whose fourth power is one has square one. -/
lemma sq_eq_one_of_pow_four_eq_one (x : Auxiliary.ambientType) (hx4 : x ^ 4 = 1) : x ^ 2 = 1 := by
  revert x; decide

set_option maxRecDepth 8000 in
                                                                           
set_option maxHeartbeats 4000000 in
                                                                                              
                             
/-- The numbers of conjugators carrying each indexed representative to representative two are given by the vector (0, 0, 4, 0, 0). -/
lemma card_conjugators_to_rep_two (j : Fin 5) :
    (univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2)).card
      = ![0, 0, 4, 0, 0] j := by
  fin_cases j <;> decide

                                                                                                 
                                                                                                
                                                                                     
/-- For a subgroup of cardinality four, the character of the auxiliary construction at an indexed representative is one quarter of the displayed linear combination of character values and their sum. -/
lemma auxiliary_construction_character_representative_card_four_formula (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)
      = (4 : ℂ)⁻¹ * (σ.character 1 * (![60, 0, 0, 0, 0] : Fin 5 → ℂ) j
          + ((∑ h : ↥H, σ.character h) - σ.character 1) * (![0, 0, 4, 0, 0] : Fin 5 → ℂ) j) := by
  classical
  rw [Auxiliary.statement012086]
  have hcard : (Fintype.card ↥H : ℂ) = 4 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
                                                                                        
  have hF : ∀ x : Auxiliary.ambientType,
      (if hm : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hm⟩ else 0)
        = ∑ h : ↥H, σ.character h * (if x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = (h : Auxiliary.ambientType) then (1 : ℂ) else 0) := by
    intro x
    by_cases hmem : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H
    · rw [dif_pos hmem, Finset.sum_eq_single (⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hmem⟩ : ↥H)]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb
        rw [if_neg (fun heq => hb (Subtype.ext heq.symm)), mul_zero]
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    · rw [dif_neg hmem]
      refine (Finset.sum_eq_zero (fun h _ => ?_)).symm
      rw [if_neg (fun heq => hmem (by rw [heq]; exact SetLike.coe_mem h)), mul_zero]
                                                                   
  have hsum : (∑ x : Auxiliary.ambientType,
        if hm : x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ ∈ H then σ.character ⟨x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹, hm⟩ else 0)
      = ∑ h : ↥H, σ.character h *
          ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = (h : Auxiliary.ambientType))).card : ℂ) := by
    rw [Finset.sum_congr rfl (fun x _ => hF x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_boole]
                                                                                                
  have hcnt : ∀ h : ↥H, σ.character h *
        ((univ.filter (fun x : Auxiliary.ambientType => x * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x⁻¹ = (h : Auxiliary.ambientType))).card : ℂ)
      = σ.character h * (if h = 1 then (![60, 0, 0, 0, 0] : Fin 5 → ℂ) j
          else (![0, 0, 4, 0, 0] : Fin 5 → ℂ) j) := by
    intro h
    congr 1
    by_cases hh : h = 1
    · subst hh
      rw [if_pos rfl, OneMemClass.coe_one, card_conjugators_to_one j]
      fin_cases j <;> norm_num
    · rw [if_neg hh]
      have hpc4 : (h : Auxiliary.ambientType) ^ 4 = 1 := by
        have h4 : h ^ 4 = 1 := by
          have := pow_card_eq_one' (G := ↥H) (x := h); rwa [hH] at this
        have := congrArg (fun t : ↥H => (t : Auxiliary.ambientType)) h4
        simpa using this
      have hpc2 : (h : Auxiliary.ambientType) ^ 2 = 1 := sq_eq_one_of_pow_four_eq_one _ hpc4
      have hne1 : (h : Auxiliary.ambientType) ≠ 1 := fun hc => hh (Subtype.ext (by simpa using hc))
      have hcl : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex (h : Auxiliary.ambientType) = 2 :=
        RepresentationTheory.FiniteGroupRepresentation.valueFormula_011000 (h : Auxiliary.ambientType) hpc2 hne1
      obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative (h : Auxiliary.ambientType)
      rw [hcl] at hc
      rw [card_conjugators_eq_of_targets_conjugate (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) (h : Auxiliary.ambientType) ⟨c, hc⟩, card_conjugators_to_rep_two j]
      fin_cases j <;> norm_num
  rw [hsum, Finset.sum_congr rfl (fun h _ => hcnt h), hcard]
                                                
  set A : ℂ := (![60, 0, 0, 0, 0] : Fin 5 → ℂ) j with hA
  set B : ℂ := (![0, 0, 4, 0, 0] : Fin 5 → ℂ) j with hB
  have hsplit : ∀ h : ↥H, σ.character h * (if h = 1 then A else B)
      = σ.character h * B + σ.character h * (if h = 1 then (A - B) else 0) := by
    intro h
    by_cases hh : h = 1
    · simp [hh]
      ring
    · simp [hh]
  have hsecond : (∑ h : ↥H, σ.character h * (if h = 1 then (A - B) else 0))
      = σ.character 1 * (A - B) := by
    rw [Finset.sum_eq_single (1 : ↥H)]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ (1 : ↥H)) hcon
  rw [Finset.sum_congr rfl (fun h _ => hsplit h), Finset.sum_add_distrib, ← Finset.sum_mul,
    hsecond]
  ring

                                                                                              
                      
/-- On indexed representatives, the character of the auxiliary construction applied to a constant-character-one representation of a subgroup of cardinality four has values (15, 0, 3, 0, 0). -/
lemma auxiliary_construction_character_representative_of_card_four_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, 3, 0, 0] j := by
  have h1 : σ.character 1 = 1 := htriv 1
  have hS : (∑ h : ↥H, σ.character h) = 4 := by
    rw [Finset.sum_congr rfl (fun h _ => htriv h), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card, hH]; norm_num
  rw [auxiliary_construction_character_representative_card_four_formula H hH σ j, h1, hS]
  fin_cases j <;> norm_num

                                                                               
/-- The character of the auxiliary construction applied to a representation with constant character one on a subgroup of cardinality four has class values (15, 0, 3, 0, 0). -/
lemma auxiliary_construction_character_of_card_four_character_one (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![15, 0, 3, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact auxiliary_construction_character_representative_of_card_four_character_one H hH σ htriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                      
/-- On indexed representatives, the displayed iterated biproduct has character vector (15, 0, 3, 0, 0). -/
lemma character_auxiliaryBiprod_card_four_representative (j : Fin 5) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, 3, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_zero, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  fin_cases j <;>
    norm_num [RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

                                                                              
/-- The displayed iterated biproduct has character values (15, 0, 3, 0, 0), selected by class index. -/
lemma character_auxiliaryBiprod_card_four (g : Auxiliary.ambientType) :
    (RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g = ![15, 0, 3, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact character_auxiliaryBiprod_card_four_representative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                      
                                                 
/-- The auxiliary construction applied to a simple representation with constant character one on a subgroup of cardinality four is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_character_one_card_four_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [auxiliary_construction_character_of_card_four_character_one H hH σ htriv g, character_auxiliaryBiprod_card_four g]

                                                                                                
                               
/-- The character sum of a simple representation whose character is not constantly one over a subgroup of cardinality four is zero. -/
lemma sum_character_eq_zero_of_simple_nontrivial_card_four (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    (∑ h : ↥H, σ.character h) = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : CommGroup ↥H := IsPGroup.commGroupOfCardEqPrimeSq (p := 2) (by rw [hH]; norm_num)
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule σ.ρ
                                                                    
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hmul : ∀ g h : ↥H, σ.character (g * h) = σ.character g * σ.character h := by
    intro g h
    have key : (σ.character (g * h) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character h : ℂ) • LinearMap.id := by
      rw [← hscalar (g * h), map_mul, hscalar g, hscalar h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
  obtain ⟨h₀, hh₀⟩ := hntriv
  have hreindex : (∑ h : ↥H, σ.character (h₀ * h)) = ∑ h : ↥H, σ.character h :=
    Fintype.sum_bijective (Equiv.mulLeft h₀) (Equiv.mulLeft h₀).bijective
      (fun h => σ.character (h₀ * h)) (fun h => σ.character h) (fun _ => rfl)
  have hmulsum : σ.character h₀ * (∑ h : ↥H, σ.character h) = ∑ h : ↥H, σ.character h := by
    rw [Finset.mul_sum, ← hreindex]
    exact Finset.sum_congr rfl (fun h _ => (hmul h₀ h).symm)
  have hzero : (σ.character h₀ - 1) * (∑ h : ↥H, σ.character h) = 0 := by
    rw [sub_mul, one_mul, hmulsum, sub_self]
  rcases mul_eq_zero.mp hzero with hc | hc
  · exact absurd (sub_eq_zero.mp hc) hh₀
  · exact hc

                                                                                                 
                                                               
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012039 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (Auxiliary.representationConstruction σ).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, -1, 0, 0] j := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : CommGroup ↥H := IsPGroup.commGroupOfCardEqPrimeSq (p := 2) (by rw [hH]; norm_num)
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule σ.ρ
  have h1 : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hS : (∑ h : ↥H, σ.character h) = 0 := sum_character_eq_zero_of_simple_nontrivial_card_four H hH σ hntriv
  rw [auxiliary_construction_character_representative_card_four_formula H hH σ j, h1, hS]
  fin_cases j <;> norm_num

                                                                                  
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012036 (H : Subgroup Auxiliary.ambientType) [DecidablePred (· ∈ H)] (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : Auxiliary.ambientType) :
    (Auxiliary.representationConstruction σ).character g = ![15, 0, -1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012039 H hH σ hntriv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                         
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012038 (j : Fin 5) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = ![15, 0, -1, 0, 0] j := by
  simp only [RepresentationTheory.FDRep.Biproduct.character_biprod, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationTwo, RepresentationTheory.TensorSquareSpectralDecomposition.character_auxiliaryRepresentationOne,
    RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_one, RepresentationTheory.AlternatingTensorSquare.character_auxiliaryRepresentation_row_two]
  have hs := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.AlternatingTensorSquare.integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
    ring

                                                                              
/-- An auxiliary statement whose displayed type is unavailable. -/
lemma Auxiliary.statement012037 (g : Auxiliary.ambientType) :
    (RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo).character g = ![15, 0, -1, 0, 0] (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact Auxiliary.statement012038 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

                                                                                            
                                                                      
/-- The auxiliary construction applied to a simple representation whose character is not constantly one on a subgroup of cardinality four is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Problem5.11.1" (role := supporting)]
theorem auxiliary_construction_simple_nontrivial_card_four_iso_auxiliaryBiprod (H : Subgroup Auxiliary.ambientType) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (Auxiliary.representationConstruction σ ≅ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationTwo ⊞ RepresentationTheory.TensorSquareSpectralDecomposition.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne ⊞ RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo) := by
  classical
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext g
  rw [Auxiliary.statement012036 H hH σ hntriv g, Auxiliary.statement012037 g]

end RepresentationTheory.FiniteGroupDegreeFiveCharacters
