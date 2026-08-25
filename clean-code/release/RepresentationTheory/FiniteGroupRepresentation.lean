/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Group.PermutationSubgroupData
import RepresentationTheory.Group.AlternatingGroupFin5Classification
import RepresentationTheory.SimpleRepresentationModules

   
                                                                          

                                                                                             
                                                                                           
                                                                                         
       

                                                                                   
              

                                                                                             
                    

                

                                                                                           
                                                                                               
                                                                                         
                                                                                             
                                                                                           
                                                                                         
                                                                 

                                                                                             
                                                                                            
                                                          
                                                                        
                                  

                                                                                         
                                                                                          
                                                                        

                                                                                           
                                                            
                                                                          
                                 
                                                                           
                                         

                                                                                        
                                                                                             
                                                                                           
               
  

noncomputable section

namespace RepresentationTheory.FiniteGroupRepresentation

                                                                     
/-- An auxiliary type whose internal description is not exposed by the displayed formal type. -/
abbrev AuxiliaryType010983 : Type := ↥(alternatingGroup (Fin 5))

                                                                                            
                                                                  
                                         
/-- The representation specified by the displayed formal signature. -/
def permutationRepresentation {G : Type*} [Group G] {n : ℕ} (act : G →* Equiv.Perm (Fin n)) :
    Representation ℂ G (Fin n → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (act g⁻¹)
  map_one' := by
    ext f i
    simp
  map_mul' g h := by
    ext f i
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_inv_rev, map_mul]

                                                                                           
                                        
/-- The representation specified by the displayed formal signature. -/
def restrictedCharacter {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) : ℂ :=
  LinearMap.trace ℂ S ((ρ g).restrict (hS g))

                                                                                
                                                                                            
       
/-- The representation specified by the displayed formal signature. -/
def IsIrreducibleSubmodule {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  S ≠ ⊥ ∧ ∀ T : Submodule ℂ (Fin n → ℂ),
    T ≤ S → (∀ g, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S

                                    

                                                                                          
                                                                                      
                                                                                            
                                                                                          
                                    

section Engine

                                                                                       
/-- A cardinality or dimension identity for the displayed finite object. -/
instance cardinalityFormula_011105 : NeZero (Nat.card AuxiliaryType010983 : ℂ) := by
  refine ⟨?_⟩
  have h : Nat.card AuxiliaryType010983 ≠ 0 := Nat.card_pos.ne'
  exact_mod_cast h

                                                                                  
                                                                                           
/-- Semisimplicity of the displayed representation module. -/
theorem semisimpleRepresentation_011109 {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)) :
    IsSemisimpleModule (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule :=
  inferInstance

                                                                                          
/-- The proposition given by the displayed formal type. -/
instance formalResult_011102 {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)) :
    Module.Finite (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule :=
  Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule

                                                                                
/-- A pointwise identity for the displayed group action. -/
lemma actionFormula_011127 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) (g : AuxiliaryType010983) :
    (permutationRepresentation act g) = (((act g⁻¹).permMatrix ℂ).toLin') := by
  apply LinearMap.ext; intro f; funext a
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
  rfl

                                                                                             
                                     
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011128 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) (g : AuxiliaryType010983) :
    LinearMap.trace ℂ (Fin n → ℂ) (permutationRepresentation act g)
      = ((Finset.univ.filter (fun i : Fin n => act g i = i)).card : ℂ) := by
  rw [actionFormula_011127, Matrix.trace_toLin'_eq, Matrix.trace_permutation]
  have hset : Function.fixedPoints (⇑(act g⁻¹ : Equiv.Perm (Fin n)))
      = (↑(Finset.univ.filter (fun i : Fin n => act g i = i)) : Set (Fin n)) := by
    ext a
    simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
      Finset.mem_univ, true_and, map_inv]
    constructor
    · intro h; exact ((Equiv.symm_apply_eq _).mp h).symm
    · intro h; exact (Equiv.symm_apply_eq _).mpr h.symm
  rw [hset, Set.ncard_coe_finset]

                                                                                             
                                                                            
/-- The equivalence of the two propositions displayed in the formal type. -/
lemma equivalence_011174 {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    {τ σ : Subrepresentation ρ} : τ ≤ σ ↔ τ.toSubmodule ≤ σ.toSubmodule := Iff.rfl

                                                                                     
                                                                         
/-- The equivalence of the two propositions displayed in the formal type. -/
lemma equivalence_011107 {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    IsIrreducibleSubmodule ρ σ.toSubmodule ↔ IsAtom σ := by
  constructor
  · rintro ⟨hne, hmax⟩
    refine ⟨fun h => hne (by rw [h]; rfl), fun τ hτ => ?_⟩
    have hle : τ.toSubmodule ≤ σ.toSubmodule := equivalence_011174.mp hτ.le
    rcases hmax τ.toSubmodule hle (fun g v hv => τ.apply_mem_toSubmodule g hv) with h1 | h2
    · exact Subrepresentation.toSubmodule_injective (by rw [h1]; rfl)
    · exact absurd (Subrepresentation.toSubmodule_injective h2) hτ.ne
  · rintro ⟨hne, hmax⟩
    refine ⟨fun h => hne (Subrepresentation.toSubmodule_injective (by rw [h]; rfl)), ?_⟩
    intro T hT hinv
    by_cases hTeq : T = σ.toSubmodule
    · exact Or.inr hTeq
    · refine Or.inl ?_
      have hτlt : (⟨T, hinv⟩ : Subrepresentation ρ) < σ :=
        lt_of_le_of_ne (equivalence_011174.mpr hT)
          (fun h => hTeq (congrArg Subrepresentation.toSubmodule h))
      have := hmax _ hτlt
      exact congrArg Subrepresentation.toSubmodule this |>.trans (by rfl)

                                                                                  
                                                                                          
/-- A simplicity statement for the displayed representation or module. -/
lemma simpleRepresentation_011108 {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    IsIrreducibleSubmodule ρ σ.toSubmodule ↔
      IsSimpleModule (MonoidAlgebra ℂ AuxiliaryType010983) σ.asSubmodule := by
  rw [equivalence_011107, isSimpleModule_iff_isAtom,
    ← Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff σ]
  rfl

                                                                                
                                                                                 
                                                                                   
                              
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011169 {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : AuxiliaryType010983) :
    restrictedCharacter ρ S hS g
      = (FDRep.of (⟨S, hS⟩ : Subrepresentation ρ).toRepresentation).character g :=
  rfl

                                                                                         
                                                                                          
                                                                                   
/-- Existence or properties of the displayed internal direct-sum decomposition. -/
theorem directSumDecomposition_011055 {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ)),
      (∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, ρ g v ∈ S k) ∧
      DirectSum.IsInternal S ∧ ∀ k, IsIrreducibleSubmodule ρ (S k) := by
  classical
  obtain ⟨s, hind, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule
  have simple' : ∀ N : ↥s, IsSimpleModule (MonoidAlgebra ℂ AuxiliaryType010983) ↥(N.1) := fun N => hsimple N.1 N.2
  haveI hfin : Finite ↥s := by
    apply WellFoundedGT.finite_of_iSupIndep ((sSupIndep_iff s).mp hind)
    intro N
    haveI := simple' N
    exact (N.1.nontrivial_iff_ne_bot).mp (IsSimpleModule.nontrivial (MonoidAlgebra ℂ AuxiliaryType010983) _)
  set e := Finite.equivFin ↥s with he
  set N : Fin (Nat.card ↥s) → Submodule (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule :=
    fun k => ((e.symm k : ↥s) : Submodule (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule) with hNdef
  have hiN : iSupIndep N := ((sSupIndep_iff s).mp hind).comp e.symm.injective
  have hsupN : (⨆ k, N k) = ⊤ := by
    calc (⨆ k, N k) = ⨆ x : ↥s, (x : Submodule (MonoidAlgebra ℂ AuxiliaryType010983) ρ.asModule) :=
            Equiv.iSup_comp e.symm
      _ = sSup s := (sSup_eq_iSup' s).symm
      _ = ⊤ := hsup
  have hInternalN : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hiN hsupN
  refine ⟨Nat.card ↥s, fun k => (Subrepresentation.ofSubmodule' (N k)).toSubmodule, ?_, ?_, ?_⟩
  · exact fun k g v hv => (Subrepresentation.ofSubmodule' (N k)).apply_mem_toSubmodule g hv
  · exact hInternalN
  · intro k
    set σ := Subrepresentation.ofSubmodule' (N k) with hσ
    have hsk : IsSimpleModule (MonoidAlgebra ℂ AuxiliaryType010983) σ.asSubmodule := simple' (e.symm k)
    exact (simpleRepresentation_011108 σ).mpr hsk

                                     

                                                                                           
                                                                                          
                                                                                        
                                                                                              
                                                                                           
                                                                                                
                                                           

open CategoryTheory


                                                                                          
/-- The construction specified by the displayed formal type. -/
noncomputable instance cardCastInvertible : Invertible (Fintype.card AuxiliaryType010983 : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

                                                                                                
                                       
/-- An equivalence statement for the displayed representations. -/
lemma representationEquivalence_011106 (a b : Fin 5) : Nonempty (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations a ≅ RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations b) ↔ a = b := by
  constructor
  · intro h; by_contra hne; exact RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations_pairwise_nonisomorphic a b hne h
  · rintro rfl; exact ⟨CategoryTheory.Iso.refl _⟩

                                                                                             
                                                                                                
                                                                                  
                                                                                                
               
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011086 {n m : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n))
    (S : Fin m → Submodule ℂ (Fin n → ℂ))
    (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k)
    (hInt : DirectSum.IsInternal S) (g : AuxiliaryType010983) :
    ((Finset.univ.filter (fun i : Fin n => act g i = i)).card : ℂ)
      = ∑ k, restrictedCharacter (permutationRepresentation act) (S k) (hS k) g := by
  have hmaps : ∀ k, Set.MapsTo (permutationRepresentation act g) (S k) (S k) := fun k v hv => hS k g v hv
  rw [← characterFormula_011128]
  exact LinearMap.trace_eq_sum_trace_restrict hInt hmaps

                                                                                             
                                                                                
                            
/-- The representation specified by the displayed formal signature. -/
def subrepresentationOfInvariant {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : FDRep ℂ AuxiliaryType010983 :=
  FDRep.of (⟨S, hS⟩ : Subrepresentation ρ).toRepresentation

                                                             
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011170 {n : ℕ} (ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : AuxiliaryType010983) :
    restrictedCharacter ρ S hS g = (subrepresentationOfInvariant ρ S hS).character g :=
  rfl

                                                                                                  
                                                                                                 
                                                                                                  
                                                                     
private def toRepAsModuleEquiv {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    (σ.toRepresentation).asModule ≃ₗ[MonoidAlgebra ℂ AuxiliaryType010983] σ.asSubmodule where
  toFun y := ⟨((σ.toRepresentation).asModuleEquiv y).1, ((σ.toRepresentation).asModuleEquiv y).2⟩
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by
    apply Subtype.ext
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c₁ c₂ h₁ h₂ =>
        simp only [add_smul, RingHom.id_apply] at h₁ h₂ ⊢
        rw [Submodule.coe_add, ← h₁, ← h₂]; rfl
    | single g t =>
        simp only [RingHom.id_apply, SetLike.val_smul]
        rw [Representation.single_smul, Representation.single_smul]; rfl
  invFun x := (σ.toRepresentation).asModuleEquiv.symm ⟨x.1, x.2⟩
  left_inv y := by simp
  right_inv x := by apply Subtype.ext; simp

                                                                                              
                                                                                                    
                                                                                          
/-- A simplicity statement for the displayed representation or module. -/
lemma simpleRepresentation_011173 {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (h : IsIrreducibleSubmodule ρ S) :
      CategoryTheory.Simple (subrepresentationOfInvariant ρ S hS) := by
  haveI hsimple : IsSimpleModule (MonoidAlgebra ℂ AuxiliaryType010983)
      (⟨S, hS⟩ : Subrepresentation ρ).asSubmodule :=
    (simpleRepresentation_011108 ⟨S, hS⟩).mp h
  haveI : IsSimpleModule (MonoidAlgebra ℂ AuxiliaryType010983)
      ((⟨S, hS⟩ : Subrepresentation ρ).toRepresentation).asModule :=
    IsSimpleModule.congr (toRepAsModuleEquiv ⟨S, hS⟩)
  exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule _

                                                                                       
                              
/-- An equivalence statement for the displayed representations. -/
lemma representationEquivalence_011060 {n : ℕ} {ρ : Representation ℂ AuxiliaryType010983 (Fin n → ℂ)}
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (h : IsIrreducibleSubmodule ρ S) :
    ∃ t : Fin 5, Nonempty (subrepresentationOfInvariant ρ S hS ≅ RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations t) := by
  haveI := simpleRepresentation_011173 S hS h
  exact RepresentationTheory.Group.AlternatingGroupFin5Classification.exists_iso_alternatingGroupFin5RepFamily (subrepresentationOfInvariant ρ S hS)

                                                                                  
                                                                                            
                                                         

                                                                                           
                                                            
                                                                       
                                                                                              

                                                                                          
                                                                            
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011061 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ))
      (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k)
      (type : Fin m → Fin 5),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrreducibleSubmodule (permutationRepresentation act) (S k)) ∧
      (∀ k g, restrictedCharacter (permutationRepresentation act) (S k) (hS k) g = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character g) ∧
      (∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k)) ∧
      ∀ i : Fin 5,
        ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
          = ⅟(Fintype.card AuxiliaryType010983 : ℂ) • ∑ g : AuxiliaryType010983,
              ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
                * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹ := by
  classical
  obtain ⟨m, S, hS, hInt, hIrr⟩ := directSumDecomposition_011055 (permutationRepresentation act)
  choose type hiso using fun k => representationEquivalence_011060 (S k) (hS k) (hIrr k)
                                                           
  have hchar : ∀ k g, restrictedCharacter (permutationRepresentation act) (S k) (hS k) g = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character g := by
    intro k g
    rw [characterFormula_011170]
    exact congrFun (FDRep.char_iso (hiso k).some) g
                                                     
  have hfr : ∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k) := by
    intro k
    have h1 : (subrepresentationOfInvariant (permutationRepresentation act) (S k) (hS k)).character 1
        = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character 1 := congrFun (FDRep.char_iso (hiso k).some) 1
    rw [FDRep.char_one, FDRep.char_one] at h1
    have h2 : Module.finrank ℂ (subrepresentationOfInvariant (permutationRepresentation act) (S k) (hS k))
        = Module.finrank ℂ (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)) := by exact_mod_cast h1
    rw [RepresentationTheory.TensorSquareSpectralDecomposition.finrank_indexedSimpleRepresentations] at h2
    exact h2
  refine ⟨m, S, hS, type, hInt, hIrr, hchar, hfr, ?_⟩
  intro i
                                                                                        
  have hperm : ∀ g : AuxiliaryType010983,
      ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
        = ∑ k, (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character g := by
    intro g
    rw [cardinalityFormula_011086 act S hS hInt g]
    exact Finset.sum_congr rfl fun k _ => hchar k g
                                                                       
  have hcard : ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
      = ∑ k : Fin m, ⅟(Fintype.card AuxiliaryType010983 : ℂ) • ∑ g : AuxiliaryType010983,
          (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character g * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹ := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := RepresentationTheory.TensorSquareSpectralDecomposition.simple_indexedSimpleRepresentations (type k)
    haveI := RepresentationTheory.TensorSquareSpectralDecomposition.simple_indexedSimpleRepresentations i
    rw [smul_eq_mul, invOf_eq_inv]
    rw [← Nat.card_eq_fintype_card]
    rw [FDRep.char_orthonormal (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)) (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i), representationEquivalence_011106]
    by_cases h : type k = i <;> simp [h]
  rw [hcard]
                                                                                   
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hperm g, Finset.sum_mul]

                                                                 
                                                                                                
                                                                                         
                                                                                                   
                                                                                                 
                                                                                
                                                                                            
                                                                                         
/-- A formula for the character or trace of the displayed representation. -/
theorem characterFormula_011056 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ))
      (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k)
      (type : Fin m → Fin 5),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrreducibleSubmodule (permutationRepresentation act) (S k)) ∧
      Monotone type ∧
      (∀ k g, restrictedCharacter (permutationRepresentation act) (S k) (hS k) g = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (type k)).character g) ∧
      (∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k)) ∧
      ∀ i : Fin 5,
        ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
          = ⅟(Fintype.card AuxiliaryType010983 : ℂ) • ∑ g : AuxiliaryType010983,
              ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
                * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹ := by
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hchar, hfr, hmult⟩ :=
    characterFormula_011061 act
  set e := Tuple.sort type with he
  refine ⟨m, S ∘ e, fun k => hS (e k), type ∘ e, ?_, fun k => hIrr (e k),
    Tuple.monotone_sort type, fun k g => hchar (e k) g, fun k => hfr (e k), ?_⟩
  ·                                                                         
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hInt ⊢
    obtain ⟨hind, hsup⟩ := hInt
    exact ⟨hind.comp e.injective, by rw [← hsup]; exact Equiv.iSup_comp e⟩
  ·                                                      
    intro i
    rw [← hmult i]
    congr 1
    rw [← Finset.card_image_of_injective (Finset.univ.filter (fun k => (type ∘ e) k = i))
      e.injective]
    congr 1
    ext j
    simp only [Function.comp_apply, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hk
    · intro hj; exact ⟨e.symm j, by simpa using hj, by simp⟩

end Engine

                                               

                                                                            
                                                                                               
                                                                                      
                                                                                                
                                                                                             
                                                               

section FixCount

open Finset

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {n : ℕ}

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

                                                                            
/-- A pointwise identity for the displayed group action. -/
lemma actionFormula_010985 (act : G →* Equiv.Perm (Fin n)) (g x : G) (i₀ : Fin n) :
    (act (x⁻¹ * g * x) i₀ = i₀) ↔ (act g (act x i₀) = act x i₀) := by
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  exact Equiv.symm_apply_eq (act x)

                                                                                            
                                         
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011116 (act : G →* Equiv.Perm (Fin n)) (i₀ i : Fin n) (xi : G)
    (hxi : act xi i₀ = i) :
    (univ.filter (fun x : G => act x i₀ = i)).card
      = (univ.filter (fun x : G => act x i₀ = i₀)).card := by
  apply Finset.card_nbij' (fun x => xi⁻¹ * x) (fun x => xi * x)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [map_mul, Equiv.Perm.mul_apply, map_inv, hx, ← hxi]; simp
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [map_mul, Equiv.Perm.mul_apply, hx, hxi]
  · intro x _; simp
  · intro x _; simp

                                                                                                
                                                                                       
                                        
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011095 (act : G →* Equiv.Perm (Fin n)) (g : G) (i₀ : Fin n)
    (htrans : ∀ j : Fin n, ∃ x : G, act x i₀ = j) :
    (univ.filter (fun i : Fin n => act g i = i)).card
        * (univ.filter (fun x : G => act x i₀ = i₀)).card
      = (univ.filter (fun x : G => act (x⁻¹ * g * x) i₀ = i₀)).card := by
  have key : (univ.filter (fun x : G => act (x⁻¹ * g * x) i₀ = i₀))
      = (univ.filter (fun x : G => act g (act x i₀) = act x i₀)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, actionFormula_010985]
  rw [key]
  symm
  rw [card_eq_sum_card_fiberwise (f := fun x : G => act x i₀)
      (t := (univ : Finset (Fin n))) (by intro x _; exact mem_univ _)]
  have hsum : ∀ i ∈ (univ : Finset (Fin n)),
      (univ.filter (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card
        = if act g i = i then (univ.filter (fun x : G => act x i₀ = i₀)).card else 0 := by
    intro i _
    by_cases hgi : act g i = i
    · rw [if_pos hgi]
      obtain ⟨xi, hxi⟩ := htrans i
      rw [← cardinalityFormula_011116 act i₀ i xi hxi]
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2; exact ⟨by rw [h2]; exact hgi, h2⟩
    · rw [if_neg hgi, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      rintro ⟨h1, h2⟩
      rw [h2] at h1; exact hgi h1
  have hrw : (fun i => (univ.filter (fun x : G => act g (act x i₀) = act x i₀)
        |>.filter (fun x => act x i₀ = i)).card)
      = (fun i => (univ.filter
          (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card) := by
    funext i; congr 1; rw [Finset.filter_filter]
  rw [show (∑ i : Fin n, (univ.filter (fun x : G => act g (act x i₀) = act x i₀)
        |>.filter (fun x => act x i₀ = i)).card)
      = ∑ i : Fin n, (univ.filter (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card
      from by rw [hrw]]
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_filter, Finset.sum_const_nat (fun _ _ => rfl)]

                                                                                             
                                                                                        
                 
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011001 (g c : G) (S T : Subgroup G)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : ∀ y : G, y ∈ T ↔ c⁻¹ * y * c ∈ S) :
    (univ.filter (fun x : G => x⁻¹ * g * x ∈ S)).card
      = (univ.filter (fun x : G => x⁻¹ * g * x ∈ T)).card := by
  apply Finset.card_nbij' (fun x => x * c⁻¹) (fun x => x * c)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [h]
    have : c⁻¹ * ((x * c⁻¹)⁻¹ * g * (x * c⁻¹)) * c = x⁻¹ * g * x := by group
    rw [this]; exact hx
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [h] at hx
    have : c⁻¹ * (x⁻¹ * g * x) * c = (x * c)⁻¹ * g * (x * c) := by group
    rw [this] at hx; exact hx
  · intro x _; simp [mul_assoc]
  · intro x _; simp [mul_assoc]

end FixCount

                                                        

                                                                                         
                                                                                   
                                                                                                
                                                                                                
                                                                                               
                                                                                            
                          

section A5FixCounts

open Finset
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable {N : ℕ}

                                                                
/-- The subgroup specified by the displayed formal signature. -/
def pointStabilizer (act : AuxiliaryType010983 →* Equiv.Perm (Fin N)) (i₀ : Fin N) : Subgroup AuxiliaryType010983 where
  carrier := {a | act a i₀ = i₀}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    rw [map_inv]; exact (Equiv.symm_apply_eq (act a)).mpr ha.symm

/-- A pointwise identity for the displayed group action. -/
@[simp] lemma actionFormula_011110 (act : AuxiliaryType010983 →* Equiv.Perm (Fin N)) (i₀ : Fin N) (a : AuxiliaryType010983) :
    a ∈ pointStabilizer act i₀ ↔ act a i₀ = i₀ := Iff.rfl

                   
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_010986 : Nat.card AuxiliaryType010983 = 60 := RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5

                                                                                             
                                                                   
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011099 [NeZero N] (act : AuxiliaryType010983 →* Equiv.Perm (Fin N)) (a g : AuxiliaryType010983)
    (htrans : ∀ i j : Fin N, ∃ x : AuxiliaryType010983, act x i = j) (c : AuxiliaryType010983)
    (hconj : ∀ y : AuxiliaryType010983, y ∈ Subgroup.zpowers a ↔ c⁻¹ * y * c ∈ pointStabilizer act 0) :
    (univ.filter (fun i : Fin N => act g i = i)).card
        * (univ.filter (fun x : AuxiliaryType010983 => act x 0 = 0)).card
      = (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * g * x ∈ Subgroup.zpowers a)).card := by
  haveI : DecidablePred (· ∈ pointStabilizer act 0) := Classical.decPred _
  haveI : DecidablePred (· ∈ Subgroup.zpowers a) := Classical.decPred _
  rw [cardinalityFormula_011095 act g 0 (fun j => htrans 0 j)]
  have hPeq : (univ.filter (fun x : AuxiliaryType010983 => act (x⁻¹ * g * x) 0 = 0)).card
      = (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * g * x ∈ pointStabilizer act 0)).card := by
    apply congrArg; ext x; simp only [mem_filter, mem_univ, true_and, actionFormula_011110]
  rw [hPeq]
  convert cardinalityFormula_011001 (S := pointStabilizer act 0) (T := Subgroup.zpowers a) g c hconj using 2
  exact Finset.filter_congr_decidable _ _ _

                                                                            
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011166 (act : AuxiliaryType010983 →* Equiv.Perm (Fin N)) (i₀ : Fin N) (p : ℕ)
    (hstab : Nat.card {x : AuxiliaryType010983 // act x i₀ = i₀} = p) :
    (univ.filter (fun x : AuxiliaryType010983 => act x i₀ = i₀)).card = p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hstab; exact hstab

                                                                                             
/-- An order identity for the group element appearing in the statement. -/
lemma orderFormula_011112 (a : AuxiliaryType010983) (m : ℕ) (h : orderOf a = m) (y : AuxiliaryType010983) :
    y ∈ Subgroup.zpowers a ↔ y ∈ (Finset.range m).image (a ^ ·) := by
  have hy := (isOfFinOrder_of_finite a).mem_zpowers_iff_mem_range_orderOf (y := y)
  rwa [h] at hy

                                                                                                
                                                                            
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011053 [NeZero N] {p : ℕ} [Fact p.Prime]
    (act : AuxiliaryType010983 →* Equiv.Perm (Fin N)) (a : AuxiliaryType010983)
    (hord : orderOf a = p) (hpfact : (Nat.card AuxiliaryType010983).factorization p = 1)
    (hstabc : Nat.card (pointStabilizer act 0) = p) :
    ∃ c : AuxiliaryType010983, ∀ y : AuxiliaryType010983, y ∈ Subgroup.zpowers a ↔ c⁻¹ * y * c ∈ pointStabilizer act 0 := by
  let P : Sylow p AuxiliaryType010983 := Sylow.ofCard (pointStabilizer act 0) (by rw [hstabc, hpfact, pow_one])
  have hQc : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  let Q : Sylow p AuxiliaryType010983 := Sylow.ofCard (Subgroup.zpowers a) (by rw [hQc, hpfact, pow_one])
  obtain ⟨cc, hcc⟩ := MulAction.exists_smul_eq AuxiliaryType010983 P Q
  refine ⟨cc, fun y => ?_⟩
  have hco : (Q : Subgroup AuxiliaryType010983) = MulAut.conj cc • (P : Subgroup AuxiliaryType010983) := by rw [← hcc]; rfl
  have hPc : (P : Subgroup AuxiliaryType010983) = pointStabilizer act 0 := Sylow.coe_ofCard _ _
  have hQcoe : (Q : Subgroup AuxiliaryType010983) = Subgroup.zpowers a := Sylow.coe_ofCard _ _
  rw [← hQcoe, ← hPc, hco, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]

                                                               
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011000 (s : AuxiliaryType010983) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 2 := by
  revert s; decide

                                                
/-- A relation involving the displayed subgroup, quotient, or coset construction. -/
lemma subgroupRelation_011010 (c t : AuxiliaryType010983) :
    MulAut.conj c • Subgroup.zpowers t = Subgroup.zpowers (c * t * c⁻¹) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [conj_zpow, hk]; group⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [conj_zpow] at hk; rw [← hk]; group⟩

                                                                                               
                                                                                               
                                                                                 
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011044 [NeZero N] (act : AuxiliaryType010983 →* Equiv.Perm (Fin N))
    (hstabc : Nat.card (pointStabilizer act 0) = 2) :
    ∃ c : AuxiliaryType010983, ∀ y : AuxiliaryType010983,
      y ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) ↔ c⁻¹ * y * c ∈ pointStabilizer act 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Nontrivial (pointStabilizer act 0) := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  obtain ⟨s, hs_mem, hs_ne⟩ := (pointStabilizer act 0).nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 2 := by
    rw [← hstabc]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : pointStabilizer act 0)
    rwa [Subgroup.orderOf_mk] at this
  have hord2 : orderOf s = 2 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs2 : s ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one s
  have hcl : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex s = 2 := valueFormula_011000 s hs2 hs_ne
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative s
  rw [hcl] at hc
  refine ⟨c⁻¹, fun y => ?_⟩
  have hzs : Subgroup.zpowers s = pointStabilizer act 0 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord2, hstabc]
  have hstabeq : (pointStabilizer act 0 : Subgroup AuxiliaryType010983)
      = MulAut.conj c • Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) := by
    rw [subgroupRelation_011010, hc, hzs]
  rw [hstabeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]
  constructor
  · intro hy; rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]; exact hy
  · intro hy; rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at hy; exact hy

                                                                            

/-- An order identity for the group element appearing in the statement. -/
lemma orderFormula_011120 : orderOf (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- An order identity for the group element appearing in the statement. -/
lemma orderFormula_011118 : orderOf (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- An order identity for the group element appearing in the statement. -/
lemma orderFormula_011119 : orderOf (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011084 : (Nat.card AuxiliaryType010983).factorization 5 = 1 := by
  rw [cardinalityFormula_010986, show (60 : ℕ) = 5 * 12 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011083 : (Nat.card AuxiliaryType010983).factorization 3 = 1 := by
  rw [cardinalityFormula_010986, show (60 : ℕ) = 3 * 20 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

                                              

                                                                                               
/-- An order identity for the group element appearing in the statement. -/
lemma orderFormula_011176 (a g : AuxiliaryType010983) (m : ℕ) (h : orderOf a = m) :
    (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * g * x ∈ Subgroup.zpowers a))
      = (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * g * x ∈ (Finset.range m).image (a ^ ·))) := by
  ext x; simp only [mem_filter, mem_univ, true_and]; exact orderFormula_011112 _ m h _

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011181 (j : Fin 5) :
    (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3))).card
      = ![60, 0, 0, 10, 10] j := by
  rw [orderFormula_011176 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 5 orderFormula_011120]
  fin_cases j <;> decide

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011180 (j : Fin 5) :
    (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1))).card
      = ![60, 6, 0, 0, 0] j := by
  rw [orderFormula_011176 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 3 orderFormula_011118]
  fin_cases j <;> decide

/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011179 (j : Fin 5) :
    (univ.filter (fun x : AuxiliaryType010983 => x⁻¹ * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * x ∈ Subgroup.zpowers (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2))).card
      = ![60, 0, 4, 0, 0] j := by
  rw [orderFormula_011176 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) 2 orderFormula_011119]
  fin_cases j <;> decide

                                                                                            
                                                                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011093 (act : AuxiliaryType010983 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : AuxiliaryType010983 // act g i = i} = 5) (j : Fin 5) :
    (univ.filter (fun i => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) i = i)).card = ![12, 0, 0, 2, 2] j := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hstabc : Nat.card (pointStabilizer act 0) = 5 := by
    change Nat.card {a : AuxiliaryType010983 // act a 0 = 0} = 5; exact hstab 0
  obtain ⟨c, hc⟩ := cardinalityFormula_011053 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) orderFormula_011120 cardinalityFormula_011084 hstabc
  have h := cardinalityFormula_011099 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) htrans c hc
  rw [cardinalityFormula_011166 act 0 5 (hstab 0), cardinalityFormula_011181] at h
  have hvec : ![60, 0, 0, 10, 10] j = 5 * ![12, 0, 0, 2, 2] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

                                                                                         
                                                                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011091 (act : AuxiliaryType010983 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : AuxiliaryType010983 // act g i = i} = 3) (j : Fin 5) :
    (univ.filter (fun i => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) i = i)).card = ![20, 2, 0, 0, 0] j := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hstabc : Nat.card (pointStabilizer act 0) = 3 := by
    change Nat.card {a : AuxiliaryType010983 // act a 0 = 0} = 3; exact hstab 0
  obtain ⟨c, hc⟩ := cardinalityFormula_011053 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) orderFormula_011118 cardinalityFormula_011083 hstabc
  have h := cardinalityFormula_011099 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 1) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) htrans c hc
  rw [cardinalityFormula_011166 act 0 3 (hstab 0), cardinalityFormula_011180] at h
  have hvec : ![60, 6, 0, 0, 0] j = 3 * ![20, 2, 0, 0, 0] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

                                                                                         
                                                                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011089 (act : AuxiliaryType010983 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : AuxiliaryType010983 // act g i = i} = 2) (j : Fin 5) :
    (univ.filter (fun i => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) i = i)).card = ![30, 0, 2, 0, 0] j := by
  have hstabc : Nat.card (pointStabilizer act 0) = 2 := by
    change Nat.card {a : AuxiliaryType010983 // act a 0 = 0} = 2; exact hstab 0
  obtain ⟨c, hc⟩ := cardinalityFormula_011044 act hstabc
  have h := cardinalityFormula_011099 act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 2) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) htrans c hc
  rw [cardinalityFormula_011166 act 0 2 (hstab 0), cardinalityFormula_011179] at h
  have hvec : ![60, 0, 4, 0, 0] j = 2 * ![30, 0, 2, 0, 0] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

end A5FixCounts

                                                                            

                                                                                             
                                                                                                
                                                                                              
                                                                                                
                                                         

open Finset


                                                                                             
                                                                              
                                                                                             
                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011085 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) (g : AuxiliaryType010983) :
    ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
      = ((univ.filter (fun p : Fin n =>
          act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) p = p)).card : ℂ) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  have key : permutationRepresentation act g
      = permutationRepresentation act c * permutationRepresentation act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) * permutationRepresentation act c⁻¹ := by
    conv_lhs => rw [← hc]
    rw [map_mul, map_mul]
  rw [← characterFormula_011128, ← characterFormula_011128, key,
    LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

                                                                                          
                                                                                           
                                                                                                
                                                                                               
                                                                                       
                                                                                              
                                            
/-- A formula for the character or trace of the displayed representation. -/
lemma characterFormula_011130 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) (i : Fin 5) :
    ∑ g : AuxiliaryType010983, ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
        * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹
      = ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ)
          * ((univ.filter (fun p : Fin n => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) p = p)).card : ℂ)
          * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j) := by
  classical
  have hclass : ∀ a b : AuxiliaryType010983, (∃ c, c * a * c⁻¹ = b) →
      (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character b = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character a := by
    rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
  have hterm : ∀ g : AuxiliaryType010983,
      ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ) * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹
        = ((univ.filter (fun p : Fin n => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) p = p)).card : ℂ)
          * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) := by
    intro g
    obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
    obtain ⟨d, hd⟩ := RepresentationTheory.Group.PermutationSubgroupData.classRepresentative_isConj_inv (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)
    have hginv : (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹
        = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) := by
      have step1 : (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹
          = (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g))⁻¹ := by
        refine hclass _ _ ⟨c, ?_⟩
        conv_rhs => rw [← hc]
        group
      rw [step1]; exact hclass _ _ ⟨d, hd⟩
    rw [hginv, cardinalityFormula_011085 act g, RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq]
  rw [Finset.sum_congr rfl (fun g _ => hterm g),
    show (∑ g : AuxiliaryType010983,
        ((univ.filter (fun p : Fin n => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) p = p)).card : ℂ)
          * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)))
      = ∑ j : Fin 5, ∑ _g ∈ univ.filter (fun g => RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g = j),
          ((univ.filter (fun p : Fin n => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) p = p)).card : ℂ)
            * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j)
      from (Finset.sum_fiberwise' univ RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex
        (fun j => ((univ.filter (fun p : Fin n => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) p = p)).card : ℂ)
          * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j))).symm]
  simp only [Finset.sum_const, RepresentationTheory.Group.PermutationSubgroupData.card_fiber_conjugacyClassIndex, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)

                                                                        

                                                                                             
                                                                                              
                                                                                                  
                                                                                   

section Multiplicity

open Finset CategoryTheory

set_option linter.unusedSectionVars false

                                                                                           
                                                                                           
/-- The equality displayed in the formal statement. -/
lemma valueFormula_011175 (F : AuxiliaryType010983 → ℂ) (hF : ∀ g c : AuxiliaryType010983, F (c * g * c⁻¹) = F g) :
    ∑ g : AuxiliaryType010983, F g
      = ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ) * F (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun g => RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g) F]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ g ∈ Finset.univ.filter (fun g => RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g = j),
      F g = F (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) := by
    intro g hg
    have hj : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g = j := (Finset.mem_filter.mp hg).2
    obtain ⟨c, hc⟩ := RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
    rw [← hc, hF, hj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, RepresentationTheory.Group.PermutationSubgroupData.card_fiber_conjugacyClassIndex j, nsmul_eq_mul]

                                                                                      
                                                                                                   
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011087 {n : ℕ} (act : AuxiliaryType010983 →* Equiv.Perm (Fin n)) (g c : AuxiliaryType010983) :
    (univ.filter (fun i : Fin n => act (c * g * c⁻¹) i = i)).card
      = (univ.filter (fun i : Fin n => act g i = i)).card := by
  apply Finset.card_nbij' (fun i => act c⁻¹ i) (fun i => act c i)
  · intro i hi
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    have h := actionFormula_010985 act g c⁻¹ i
    rw [inv_inv] at h
    exact h.mp hi
  · intro i hi
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    have h := actionFormula_010985 act g c⁻¹ (act c i)
    rw [inv_inv] at h
    rw [h, show act c⁻¹ (act c i) = i from by simp [map_inv]]
    exact hi
  · intro i _; simp [map_inv]
  · intro i _; simp [map_inv]

                                                                                                  
                                                                                                
                                                                                            
                       
/-- A cardinality or dimension identity for the displayed finite object. -/
lemma cardinalityFormula_011113 {m : ℕ} {P : Fin 5 → Prop} [DecidablePred P]
    (hP : ∀ ⦃a b : Fin 5⦄, a ≤ b → P b → P a)
    {t : Fin m → Fin 5} (hmono : Monotone t) (k : Fin m) :
    P (t k) ↔ (k : ℕ) < (univ.filter (fun j => P (t j))).card := by
  constructor
  · intro hpk
    have hsub : Finset.Iic k ⊆ univ.filter (fun j => P (t j)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      exact Finset.mem_filter.mpr ⟨mem_univ _, hP (hmono hj) hpk⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra hnp
    have hsub : univ.filter (fun j => P (t j)) ⊆ Finset.Iio k := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hjk
      rw [not_lt] at hjk
      exact hnp (hP (hmono hjk) hj.2)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

end Multiplicity

                                                                                            
                                                                                              
                                                                                        
                                                                                              
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011191
    (act : AuxiliaryType010983 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : AuxiliaryType010983 // act g i = i} = 5) :
    ∃ (S : Fin 4 → Submodule ℂ (Fin 12 → ℂ))
      (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrreducibleSubmodule (permutationRepresentation act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 5 ∧
      ∃ g : AuxiliaryType010983, restrictedCharacter (permutationRepresentation act) (S 1) (hS 1) g ≠ restrictedCharacter (permutationRepresentation act) (S 2) (hS 2) g := by
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    characterFormula_011056 act
                                                                  
  have hmultnat : ∀ i : Fin 5,
      (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 0, 1] i := by
    intro i
    have h := hmult i
    rw [characterFormula_011130 act i] at h
    simp only [cardinalityFormula_011093 act htrans hstab] at h
    have hcard : (Fintype.card AuxiliaryType010983 : ℂ) = 60 := by
      have : (Fintype.card AuxiliaryType010983 : ℕ) = 60 := by rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_010986
      rw [this]; norm_num
    have hsum : (∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ)
          * ((![12, 0, 0, 2, 2] j : ℕ) : ℂ) * RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j))
        = (Fintype.card AuxiliaryType010983 : ℂ) * ((![1, 1, 1, 0, 1] i : ℕ) : ℂ) := by
      rw [hcard]
      fin_cases i <;>
        norm_num [Fin.sum_univ_five, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
          Matrix.tail_cons, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
          RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im] <;>
        ring
    rw [hsum, smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul] at h
    exact_mod_cast h
                                                 
  have hpart : (univ : Finset (Fin m)).card
      = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (type k))
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hm4 : m = 4 := by rw [hpart]; simp only [hmultnat]; decide
  subst hm4
                                                                     
  have hle1 : ∀ v : Fin 5, (univ.filter (fun k => type k = v)).card ≤ 1 := by
    intro v; rw [hmultnat v]; fin_cases v <;> decide
  have hinj : Function.Injective type := by
    intro a b hab
    by_contra hne
    have hsub : ({a, b} : Finset (Fin 4)) ⊆ univ.filter (fun k => type k = type a) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp
      · simp [hab]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2
    exact absurd (h2.trans (hle1 (type a))) (by norm_num)
  have hstrict : StrictMono type := hmono.strictMono_of_injective hinj
                                                       
  have hne3 : ∀ k : Fin 4, type k ≠ 3 := by
    intro k hk
    have hmem : k ∈ univ.filter (fun k => type k = 3) := by simp [hk]
    have hpos := Finset.card_pos.mpr ⟨k, hmem⟩
    rw [hmultnat 3] at hpos
    simp at hpos
                                                                           
  have s01 : (type 0).val < (type 1).val := Fin.lt_def.mp (hstrict (by decide))
  have s12 : (type 1).val < (type 2).val := Fin.lt_def.mp (hstrict (by decide))
  have s23 : (type 2).val < (type 3).val := Fin.lt_def.mp (hstrict (by decide))
  have b0 : (type 0).val < 5 := (type 0).isLt
  have b1 : (type 1).val < 5 := (type 1).isLt
  have b2 : (type 2).val < 5 := (type 2).isLt
  have b3 : (type 3).val < 5 := (type 3).isLt
  have n0 : (type 0).val ≠ 3 := fun hh => hne3 0 (Fin.ext hh)
  have n1 : (type 1).val ≠ 3 := fun hh => hne3 1 (Fin.ext hh)
  have n2 : (type 2).val ≠ 3 := fun hh => hne3 2 (Fin.ext hh)
  have n3 : (type 3).val ≠ 3 := fun hh => hne3 3 (Fin.ext hh)
  have ht0 : type 0 = 0 := Fin.ext (by omega)
  have ht1 : type 1 = 1 := Fin.ext (by omega)
  have ht2 : type 2 = 2 := Fin.ext (by omega)
  have ht3 : type 3 = 4 := Fin.ext (by omega)
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hfr, ht0]
  · simp [hfr, ht1]
  · simp [hfr, ht2]
  · simp [hfr, ht3]
  · refine ⟨RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3, ?_⟩
    rw [hchar, hchar, ht1, ht2, RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations, RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq, RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im]
    intro hcontra
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination hcontra
    have hsq := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
    rw [hz] at hsq
    norm_num at hsq

open Finset CategoryTheory in
                                                                                          
                                                                                    
                                                                                            
                                                                                 
                  
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011071
    (act : AuxiliaryType010983 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : AuxiliaryType010983 // act g i = i} = 3) :
    ∃ (S : Fin 6 → Submodule ℂ (Fin 20 → ℂ))
      (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrreducibleSubmodule (permutationRepresentation act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      ∃ g : AuxiliaryType010983, restrictedCharacter (permutationRepresentation act) (S 1) (hS 1) g ≠ restrictedCharacter (permutationRepresentation act) (S 2) (hS 2) g := by
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    characterFormula_011056 act
                                                                  
  have hfix : ∀ j : Fin 5,
      ((univ.filter (fun p : Fin 20 => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) p = p)).card : ℂ)
        = ((![20, 2, 0, 0, 0] j : ℕ) : ℂ) := by
    intro j; rw [cardinalityFormula_011091 act htrans hstab j]
                                                                                    
  have hchar_inv : ∀ (i j : Fin 5),
      (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)⁻¹ = RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j) := by
    intro i j
    obtain ⟨d, hd⟩ := RepresentationTheory.Group.PermutationSubgroupData.classRepresentative_isConj_inv j
    rw [show (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)⁻¹ = d * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * d⁻¹ from hd.symm, FDRep.char_conj,
      RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq]
                        
  have hcard60 : (Fintype.card AuxiliaryType010983 : ℂ) = 60 := by
    rw [show Fintype.card AuxiliaryType010983 = 60 from by rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_010986]; norm_num
                                                       
  have hmulti : ∀ i : Fin 5, (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 2, 1] i := by
    intro i
    have hFconj : ∀ g c : AuxiliaryType010983,
        ((univ.filter (fun p : Fin 20 => act (c * g * c⁻¹) p = p)).card : ℂ)
              * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (c * g * c⁻¹)⁻¹
          = ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
              * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹ := by
      intro g c
      rw [cardinalityFormula_011087 act g c,
        show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ from by group, FDRep.char_conj]
    have hsum : (∑ g : AuxiliaryType010983, ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
          * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹)
        = (60 : ℂ) * ((![1, 1, 1, 2, 1] i : ℕ) : ℂ) := by
      rw [valueFormula_011175 (fun g => ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
          * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹) hFconj]
      simp only [hfix, hchar_inv]
      fin_cases i <;>
        · rw [Fin.sum_univ_five]
          norm_num [RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
            RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
            RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]
    have hC : ((univ.filter (fun k => type k = i)).card : ℂ) = ((![1, 1, 1, 2, 1] i : ℕ) : ℂ) := by
      rw [hmult i, smul_eq_mul, hsum, ← hcard60, ← mul_assoc, invOf_mul_self, one_mul]
    exact_mod_cast hC
                                                           
  have hm : m = 6 := by
    have hpart : (univ : Finset (Fin m)).card
        = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun k _ => mem_univ (type k))
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    rw [hpart]; simp only [hmulti]; decide
  subst hm
                                      
  have hp : ∀ i : Fin 5, (univ.filter (fun j => type j ≤ i)).card = ![1, 2, 3, 5, 6] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 6 => type j ≤ i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 6 => type j ≤ i)).filter (fun j => type j = b)).card
          = if b ≤ i then (![1, 1, 1, 2, 1] b) else 0 := by
      intro b
      by_cases hb : b ≤ i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  have hq : ∀ i : Fin 5, (univ.filter (fun j => type j < i)).card = ![0, 1, 2, 3, 5] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 6 => type j < i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 6 => type j < i)).filter (fun j => type j = b)).card
          = if b < i then (![1, 1, 1, 2, 1] b) else 0 := by
      intro b
      by_cases hb : b < i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
                                                                                
  have htype : ∀ k : Fin 6, type k = ![0, 1, 2, 3, 3, 4] k := by
    intro k
    have hle : ∀ v : Fin 5, (k : ℕ) < ![1, 2, 3, 5, 6] v → type k ≤ v := by
      intro v hv
      have h := cardinalityFormula_011113 (P := fun x => x ≤ v) (fun a b hab hb => le_trans hab hb) hmono k
      rw [hp v] at h; exact h.mpr hv
    have hgt : ∀ v : Fin 5, ![0, 1, 2, 3, 5] v ≤ (k : ℕ) → v ≤ type k := by
      intro v hv
      by_contra hlt
      rw [not_le] at hlt
      have h := cardinalityFormula_011113 (P := fun x => x < v)
        (fun a b hab hb => lt_of_le_of_lt hab hb) hmono k
      rw [hq v] at h
      have := h.mp hlt; omega
    fin_cases k <;> exact le_antisymm (hle _ (by decide)) (hgt _ (by decide))
                                                                                     
  have h1 : type 1 = 1 := by rw [htype 1]; rfl
  have h2 : type 2 = 2 := by rw [htype 2]; rfl
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr 0, htype 0]; rfl
  · rw [hfr 1, htype 1]; rfl
  · rw [hfr 2, htype 2]; rfl
  · rw [hfr 3, htype 3]; rfl
  · rw [hfr 4, htype 4]; rfl
  · rw [hfr 5, htype 5]; rfl
  · refine ⟨RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3, ?_⟩
    rw [hchar 1 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3), hchar 2 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3), h1, h2,
      RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations, RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq]
                                                                                  
    simp only [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
    rw [hz] at hsq; norm_num at hsq

open Finset CategoryTheory in
                                                                                          
                                                                                    
                                                                                   
                                                                                          
                           
/-- A cardinality or dimension identity for the displayed finite object. -/
theorem cardinalityFormula_011032
    (act : AuxiliaryType010983 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : AuxiliaryType010983, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : AuxiliaryType010983 // act g i = i} = 2) :
    ∃ (S : Fin 8 → Submodule ℂ (Fin 30 → ℂ))
      (hS : ∀ k, ∀ g : AuxiliaryType010983, ∀ v ∈ S k, permutationRepresentation act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrreducibleSubmodule (permutationRepresentation act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      Module.finrank ℂ (S 6) = 5 ∧ Module.finrank ℂ (S 7) = 5 ∧
      ∃ g : AuxiliaryType010983, restrictedCharacter (permutationRepresentation act) (S 1) (hS 1) g ≠ restrictedCharacter (permutationRepresentation act) (S 2) (hS 2) g := by
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    characterFormula_011056 act
                                                                  
  have hfix : ∀ j : Fin 5,
      ((univ.filter (fun p : Fin 30 => act (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) p = p)).card : ℂ)
        = ((![30, 0, 2, 0, 0] j : ℕ) : ℂ) := by
    intro j; rw [cardinalityFormula_011089 act htrans hstab j]
                                                                                    
  have hchar_inv : ∀ (i j : Fin 5),
      (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)⁻¹ = RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j) := by
    intro i j
    obtain ⟨d, hd⟩ := RepresentationTheory.Group.PermutationSubgroupData.classRepresentative_isConj_inv j
    rw [show (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)⁻¹ = d * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j * d⁻¹ from hd.symm, FDRep.char_conj,
      RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq]
                        
  have hcard60 : (Fintype.card AuxiliaryType010983 : ℂ) = 60 := by
    rw [show Fintype.card AuxiliaryType010983 = 60 from by rw [← Nat.card_eq_fintype_card]; exact cardinalityFormula_010986]; norm_num
                                                       
  have hmulti : ∀ i : Fin 5, (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 2, 3] i := by
    intro i
    have hFconj : ∀ g c : AuxiliaryType010983,
        ((univ.filter (fun p : Fin 30 => act (c * g * c⁻¹) p = p)).card : ℂ)
              * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (c * g * c⁻¹)⁻¹
          = ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
              * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹ := by
      intro g c
      rw [cardinalityFormula_011087 act g c,
        show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ from by group, FDRep.char_conj]
    have hsum : (∑ g : AuxiliaryType010983, ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
          * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹)
        = (60 : ℂ) * ((![1, 1, 1, 2, 3] i : ℕ) : ℂ) := by
      rw [valueFormula_011175 (fun g => ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
          * (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g⁻¹) hFconj]
      simp only [hfix, hchar_inv]
      fin_cases i <;>
        · rw [Fin.sum_univ_five]
          norm_num [RepresentationTheory.Group.PermutationSubgroupData.indexedTable, RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
            RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
            RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]
    have hC : ((univ.filter (fun k => type k = i)).card : ℂ) = ((![1, 1, 1, 2, 3] i : ℕ) : ℂ) := by
      rw [hmult i, smul_eq_mul, hsum, ← hcard60, ← mul_assoc, invOf_mul_self, one_mul]
    exact_mod_cast hC
                                                           
  have hm : m = 8 := by
    have hpart : (univ : Finset (Fin m)).card
        = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun k _ => mem_univ (type k))
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    rw [hpart]; simp only [hmulti]; decide
  subst hm
                                      
  have hp : ∀ i : Fin 5, (univ.filter (fun j => type j ≤ i)).card = ![1, 2, 3, 5, 8] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 8 => type j ≤ i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 8 => type j ≤ i)).filter (fun j => type j = b)).card
          = if b ≤ i then (![1, 1, 1, 2, 3] b) else 0 := by
      intro b
      by_cases hb : b ≤ i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  have hq : ∀ i : Fin 5, (univ.filter (fun j => type j < i)).card = ![0, 1, 2, 3, 5] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 8 => type j < i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 8 => type j < i)).filter (fun j => type j = b)).card
          = if b < i then (![1, 1, 1, 2, 3] b) else 0 := by
      intro b
      by_cases hb : b < i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
                                                                                    
  have htype : ∀ k : Fin 8, type k = ![0, 1, 2, 3, 3, 4, 4, 4] k := by
    intro k
    have hle : ∀ v : Fin 5, (k : ℕ) < ![1, 2, 3, 5, 8] v → type k ≤ v := by
      intro v hv
      have h := cardinalityFormula_011113 (P := fun x => x ≤ v) (fun a b hab hb => le_trans hab hb) hmono k
      rw [hp v] at h; exact h.mpr hv
    have hgt : ∀ v : Fin 5, ![0, 1, 2, 3, 5] v ≤ (k : ℕ) → v ≤ type k := by
      intro v hv
      by_contra hlt
      rw [not_le] at hlt
      have h := cardinalityFormula_011113 (P := fun x => x < v)
        (fun a b hab hb => lt_of_le_of_lt hab hb) hmono k
      rw [hq v] at h
      have := h.mp hlt; omega
    fin_cases k <;> exact le_antisymm (hle _ (by decide)) (hgt _ (by decide))
                                                                                     
  have h1 : type 1 = 1 := by rw [htype 1]; rfl
  have h2 : type 2 = 2 := by rw [htype 2]; rfl
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr 0, htype 0]; rfl
  · rw [hfr 1, htype 1]; rfl
  · rw [hfr 2, htype 2]; rfl
  · rw [hfr 3, htype 3]; rfl
  · rw [hfr 4, htype 4]; rfl
  · rw [hfr 5, htype 5]; rfl
  · rw [hfr 6, htype 6]; rfl
  · rw [hfr 7, htype 7]; rfl
  · refine ⟨RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3, ?_⟩
    rw [hchar 1 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3), hchar 2 (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative 3), h1, h2,
      RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations, RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations]
    simp only [RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq]
                                                                                  
    simp only [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, RepresentationTheory.Group.PermutationSubgroupData.indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
    rw [hz] at hsq; norm_num at hsq

end RepresentationTheory.FiniteGroupRepresentation
