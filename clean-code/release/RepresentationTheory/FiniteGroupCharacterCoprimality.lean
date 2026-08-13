/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Complex.RootsOfUnity.AverageIntegral
import RepresentationTheory.Alignment.Attribute

/-!
# Character coprimality for finite-group representations

This module relates coprimality between conjugacy-class size and representation dimension to
vanishing of a character value or scalar action.
-/

namespace RepresentationTheory.FiniteGroupCharacterCoprimality

   
                                                     

                                                                          
                                                                           
                                                    

                                                                     
                                                                

                         

                                                       

                

                                                         
                                                                                  
                                                                    
                                                                               
                                                                         
                                                                          
  

open CategoryTheory Finset

                                                

                                                                                
                                                                      
                                                                         
                                                                     

                      
                                                                             
                                                                         
                                                                        
  
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma character_eigenvalue_decomposition
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    ∃ (ε : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1) ∧
      V.character g = ∑ i, ε i ∧
      ((∀ i j, ε i = ε j) → ∃ (c : ℂ), V.ρ g = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj)) := by
  set n := Module.finrank ℂ V with hn_def
  set f := V.ρ g with hf_def
                                
  have hd_pos : 0 < orderOf g := orderOf_pos g
  have hf_pow : f ^ orderOf g = 1 := by
    change (V.ρ g) ^ orderOf g = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
                                   
  have hne : LinearMap.charpoly f ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hcard : (LinearMap.charpoly f).roots.card = n := by
    have hsplits := IsAlgClosed.splits (LinearMap.charpoly f)
    rw [← hsplits.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
                          
  have haeval : Polynomial.aeval f
      ((Polynomial.X : Polynomial ℂ) ^ orderOf g - 1) = 0 := by
    simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, hf_pow, sub_self]
                                                   
  have hroots_unity : ∀ μ ∈ (LinearMap.charpoly f).roots, μ ^ orderOf g = 1 := by
    intro μ hμ
    rw [Polynomial.mem_roots hne] at hμ
                              
    have heig : Module.End.HasEigenvalue f μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ
                                                   
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
                                                          
    have hpow_v : ∀ k : ℕ, (f ^ k) v = (μ ^ k) • v := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul,
          map_smul, ih, smul_smul, ← pow_succ']
    have h1 : v = (μ ^ orderOf g) • v := by
      rw [← hpow_v, hf_pow]; simp
                                                
    have h2 : (μ ^ orderOf g - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv.2
                                    
  set rl := (LinearMap.charpoly f).roots.toList with hrl_def
  have hlen : rl.length = n := by rw [hrl_def, Multiset.length_toList, hcard]
  have hlt (i : Fin n) : i.val < rl.length := by omega
  refine ⟨fun i => rl[i.val]'(hlt i), ?_, ?_, ?_⟩
                                        
  · intro i
    refine ⟨orderOf g, hd_pos, ?_⟩
    apply hroots_unity
    exact Multiset.mem_toList.mp (List.getElem_mem (hlt i))
                                
  ·                                                    
    change LinearMap.trace ℂ V f = _
                                               
    set b := Module.finBasis ℂ V
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
                                                                  
    have h1 : (LinearMap.toMatrix b b f).trace =
        (LinearMap.toMatrix b b f).charpoly.roots.sum :=
      Matrix.trace_eq_sum_roots_charpoly _
    simp only [LinearMap.charpoly_toMatrix] at h1
    rw [h1]
                                                     
    rw [← Multiset.sum_toList]
    change rl.sum = _
    have : rl = List.ofFn (fun i : Fin rl.length => rl[i.val]) := by
      rw [List.ofFn_getElem]
    conv_lhs => rw [this, List.sum_ofFn]
    exact Finset.sum_equiv (finCongr hlen) (by simp) (by intro i _; simp [finCongr])
                                                  
  · intro hall
                                                    
    have hn' : 0 < rl.length := by omega
    set c := rl[0]'hn' with hc_def
                                  
    have hall' : ∀ μ ∈ f.charpoly.roots, μ = c := by
      intro μ hμ
      have hμ_list : μ ∈ rl := Multiset.mem_toList.mpr hμ
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hμ_list
      exact hall ⟨i, hlen ▸ hi⟩ ⟨0, hn⟩
    refine ⟨c, ?_⟩
                                                                                         
                                                                          
                            
                                                             
    have hsep : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).Separable := by
      rw [Polynomial.X_pow_sub_one_separable_iff]
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd_pos)
                                      
    have hf_integral : IsIntegral ℂ f :=
      ⟨f.charpoly, LinearMap.charpoly_monic f, LinearMap.aeval_self_charpoly f⟩
    have hmin_dvd : minpoly ℂ f ∣ (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, hf_pow, sub_self]
                                                                    
    have hmin_sqfree : Squarefree (minpoly ℂ f) :=
      hsep.squarefree.squarefree_of_dvd hmin_dvd
                                                                          
    have hmin_roots : ∀ μ, (minpoly ℂ f).IsRoot μ → μ = c := by
      intro μ hμ_root
      apply hall'
      have hdvd := LinearMap.minpoly_dvd_charpoly f
      have hμ_mem : μ ∈ (minpoly ℂ f).roots :=
        (Polynomial.mem_roots (minpoly.ne_zero hf_integral)).mpr hμ_root
      exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd
        (LinearMap.charpoly_monic f).ne_zero hdvd) hμ_mem
                                                                           
                                                                   
    have hmin_eq : minpoly ℂ f = Polynomial.X - Polynomial.C c := by
      have hmin_ne := minpoly.ne_zero hf_integral
      have hmin_monic := minpoly.monic hf_integral
      have hmin_splits := IsAlgClosed.splits (minpoly ℂ f)
                                                         
      have hc_mem : c ∈ f.charpoly.roots := by
        rw [← Multiset.mem_toList]; exact List.getElem_mem hn'
                                                  
      have hc_eig : Module.End.HasEigenvalue f c :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly f c).mpr
          (Polynomial.isRoot_of_mem_roots hc_mem)
      have hc_min_root : (minpoly ℂ f).IsRoot c :=
        Module.End.hasEigenvalue_iff_isRoot.mp hc_eig
                                                                             
      have hroots_eq : (minpoly ℂ f).roots = {c} := by
        ext x
        by_cases hx : x = c
        · subst hx
          simp only [Multiset.count_singleton_self]
          have h1 : 0 < (minpoly ℂ f).roots.count c :=
            Multiset.count_pos.mpr ((Polynomial.mem_roots hmin_ne).mpr hc_min_root)
          have h2 : (minpoly ℂ f).roots.count c ≤ 1 :=
            Polynomial.count_roots_le_one
              (PerfectField.separable_iff_squarefree.mpr hmin_sqfree) c
          omega
        · simp only [Multiset.count_singleton, if_neg hx]
          exact Multiset.count_eq_zero.mpr
            (fun h => hx (hmin_roots x ((Polynomial.mem_roots hmin_ne).mp h)))
                                                    
      conv_lhs => rw [hmin_splits.eq_prod_roots_of_monic hmin_monic, hroots_eq]
      simp [Multiset.map_singleton, Multiset.prod_singleton]
                                                  
    have := minpoly.aeval ℂ f
    rw [hmin_eq] at this
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at this
    rw [sub_eq_zero] at this
    exact this

                                                                                 

                                                                               
                                                                     
                                                                                
                                               
  
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma class_sum_scalar_isIntegral
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    IsIntegral ℤ ((Fintype.card { h : G // IsConj g h } : ℂ) * V.character g /
      (Module.finrank ℂ V : ℂ)) := by
  set C := Fintype.card { h : G // IsConj g h }
  set d := Module.finrank ℂ V
                                                
  set σ := ∑ h : { h : G // IsConj g h }, V.ρ (h : G) with hσ_def
                                                                   
                                                                     
                                                                   
  have ⟨c, hc⟩ : ∃ c : ℂ, σ = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj) := by
                                                                           
    have hσ_comm : ∀ a : G, σ.comp (V.ρ a) = (V.ρ a).comp σ := by
      intro a
      ext v
      simp only [hσ_def, LinearMap.sum_apply, LinearMap.comp_apply]
                                                        
      rw [map_sum]
                                                        
                                                                                          
      simp_rw [← Module.End.mul_apply, ← map_mul]
                                                    
                                                                                          
      let e : { h : G // IsConj g h } ≃ { h : G // IsConj g h } :=
        { toFun := fun ⟨h, hh⟩ => ⟨a⁻¹ * h * a, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a⁻¹ * k, by group⟩⟩
          invFun := fun ⟨h, hh⟩ => ⟨a * h * a⁻¹, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a * k, by group⟩⟩
          left_inv := fun ⟨h, _⟩ => by ext; simp; group
          right_inv := fun ⟨h, _⟩ => by ext; simp; group }
      exact Fintype.sum_equiv e _ _ (fun x => by
        dsimp [e]; congr 1; group)
                                                               
                                                                                     
    have hrank : Module.finrank ℂ (V ⟶ V) = 1 := by
      rw [FDRep.finrank_hom_simple_simple V V, if_pos ⟨Iso.refl V⟩]
                     
    have hid_ne : (𝟙 V : V ⟶ V) ≠ 0 := by
      intro h
      apply id_nonzero V
      exact_mod_cast h
                              
    let σ_hom : V ⟶ V :=
      { hom := FGModuleCat.ofHom σ
        comm := fun g => by
          ext v
          exact congr_fun (congr_arg DFunLike.coe (hσ_comm g)) v }
                                                            
    obtain ⟨c, hc_eq⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 V) hid_ne).mp hrank σ_hom
    refine ⟨c, ?_⟩
                                                                 
    have h1 : σ_hom.hom = (c • 𝟙 V).hom := congr_arg Action.Hom.hom hc_eq.symm
                                                                              
    have h2 := congr_arg (fun f : V.V ⟶ V.V => InducedCategory.Hom.hom f |>.hom) h1
                                                    
                                                                                         
    apply LinearMap.ext
    intro v
    have := congr_arg (fun f : V.V.obj →ₗ[ℂ] V.V.obj => f v) h2
    exact this
                                                   
  have hc_val : c = (C : ℂ) * V.character g / (d : ℂ) := by
    have hdim_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
                                              
    have ht1 : LinearMap.trace ℂ V.V.obj σ = (C : ℂ) * V.character g := by
      simp only [hσ_def, map_sum]
                                                   
      have : ∀ h : { h : G // IsConj g h },
          (LinearMap.trace ℂ V.V.obj) (V.ρ (h : G)) = V.character g := by
        intro ⟨h, hh⟩
                                                                  
        change V.character h = V.character g
        obtain ⟨c, rfl⟩ := isConj_iff.mp hh
        exact V.char_conj g c
      simp_rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
                            
    rw [hc] at ht1
    simp only [map_smul, LinearMap.trace_id, smul_eq_mul] at ht1
                                                                 
                                          
    have hd_eq : (Module.finrank ℂ (V.V.obj) : ℂ) = (d : ℂ) := by rfl
    rw [hd_eq] at ht1
    exact eq_div_of_mul_eq hdim_ne ht1
                                 
                                                                                   
                                                                              
  rw [← hc_val]
                                  
  set e : MonoidAlgebra ℤ G := ∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h
                                                                     
  have he : IsIntegral ℤ e := IsIntegral.of_finite ℤ e
                                                                                    
                                                                              
                                                                               
  let φ : MonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℂ V.V.obj :=
    MonoidAlgebra.lift ℤ (Module.End ℂ V.V.obj) G V.ρ
                      
  have hφe : φ e = c • LinearMap.id := by
    have hφ_of : ∀ h : G, φ (MonoidAlgebra.of ℤ G h) = V.ρ h := by
      intro h; simp [φ]
    change φ (∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h) = c • LinearMap.id
    rw [map_sum]; simp_rw [hφ_of]; exact hc
                                                                                 
  have hφe_int : IsIntegral ℤ (φ e) := IsIntegral.map φ he
  rw [hφe] at hφe_int
                                                                     
  haveI : Nontrivial V.V.obj := Module.nontrivial_of_finrank_pos hn
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V.V.obj))
    (FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V.V.obj))).mp
                                                                                            
    (by convert hφe_int using 2; simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id])

                                                                              

                  
                                                                   
                                                                       
                                                                        
                             
                                                                
                                                                         
                                                                               
  
private lemma character_div_dim_isIntegral
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    IsIntegral ℤ (V.character g / (Module.finrank ℂ V : ℂ)) := by
                                           
  have hn : 0 < Module.finrank ℂ V := by
    by_contra h
    push Not at h
    have h0 : Module.finrank ℂ V = 0 := by omega
    haveI : Subsingleton V.V.obj := Module.finrank_zero_iff.1 h0
    apply id_nonzero V
    ext x
    exact Subsingleton.elim _ _
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  set C := Fintype.card { h : G // IsConj g h } with hC_def
  set d := Module.finrank ℂ V with hd_def
                                                                   
  obtain ⟨ε, hε_roots, hε_sum, _⟩ := character_eigenvalue_decomposition G V g hn
  have hchar_int : IsIntegral ℤ (V.character g) := by
    rw [hε_sum]
    apply IsIntegral.sum
    intro i _
    obtain ⟨m, hm_pos, hm⟩ := hε_roots i
    exact ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega),
      by simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, hm]⟩
                                                                       
                                                                            
                                                                                     
                                                                                   
  have hclass_int : IsIntegral ℤ ((C : ℂ) * V.character g / (d : ℂ)) := by
                                                                        
                                                                
                                            
                                                                                         
                                                   
                                                                        
    exact class_sum_scalar_isIntegral G V g hn
                                                                  
  have hbezout := Nat.gcd_eq_gcd_ab C d
  rw [h_coprime] at hbezout
  set a := Nat.gcdA C d
  set b := Nat.gcdB C d
                                        
                                                                       
  have h1 : (1 : ℂ) = (C : ℂ) * (a : ℂ) + (d : ℂ) * (b : ℂ) := by
    exact_mod_cast hbezout
  have hkey : V.character g / (d : ℂ) =
      (a : ℂ) * ((C : ℂ) * V.character g / (d : ℂ)) + (b : ℂ) * V.character g := by
    field_simp
    linear_combination V.character g * h1
  rw [hkey]
  exact (isIntegral_algebraMap (x := a).mul hclass_int).add
    (isIntegral_algebraMap (x := b).mul hchar_int)

open CategoryTheory in
                                                                                        
                                                                        
/-- For a simple finite-group representation, coprimality of the conjugacy-class size and dimension forces a zero character value or scalar action. -/
@[source_ref "Chapter5/Discussion_before_Lemma5.4.5" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.4.4" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.4.6" (role := primary),
  source_ref "Chapter5/Theorem5.4.4" (role := primary)]
theorem character_eq_zero_or_action_eq_smul_id_of_conjClassCard_coprime_finrank
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    V.character g = 0 ∨ ∃ (c : ℂ), V.ρ g = c • LinearMap.id := by
                                                      
  have hn : 0 < Module.finrank ℂ V := by
    by_contra h
    push Not at h
    have h0 : Module.finrank ℂ V = 0 := by omega
    haveI : Subsingleton V.V.obj := Module.finrank_zero_iff.1 h0
    apply id_nonzero V
    ext x
    exact Subsingleton.elim _ _
                                                                                      
  obtain ⟨ε, hε_roots, hε_sum, hε_scalar⟩ :=
    character_eigenvalue_decomposition G V g hn
                                                              
  have hint : IsIntegral ℤ ((∑ i, ε i) / (Module.finrank ℂ V : ℂ)) := by
    rw [← hε_sum]
    exact character_div_dim_isIntegral G V g h_coprime
                              
  rcases RepresentationTheory.Complex.RootsOfUnity.AverageIntegral.rootsOfUnity_all_eq_or_sum_eq_zero_of_average_integral
      (Module.finrank ℂ V) hn ε hε_roots hint with hall | hzero
  ·                                                
    exact Or.inr (hε_scalar hall)
  ·                                                  
    exact Or.inl (by rw [hε_sum, hzero])

end RepresentationTheory.FiniteGroupCharacterCoprimality

