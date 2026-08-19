/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Alignment.Attribute
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.Length

   
                                                                                       

                                                                               
                                                                                     
                                          

                                                                                   
                                                                                       
                                                                                  
                                          

                                                                            
                                                                                 
                                                                                      
              

                                                                                 
                                                                                          
                                                                                          
                                                                                
                                                                                           
                                                                          
                                                                                      
                                                                                          
                                                                                      
                                                                                      
                                                     
                                                                                        
                                                                                          
                               

                                                                                         
                                                                                         
                                                                                           
                                                                                        
                                                              

                             

                                                                                       
                                                                         
                                                                                         
                                                                                          
                                                                  
                                                                                        
                                                                  
                                            
  

open Module

open scoped DirectSum

namespace RepresentationTheory.Algebra.Module.IsotypicDecomposition

                                                                                 
                                                              
/-- A finite function module with values in a simple module is isotypic of that type. -/
@[source_ref "Chapter3/Proposition3.1.4/Derived4" (role := supporting)]
theorem isIsotypicOfType_fin_fun {A : Type*} [Ring A] {S : Type*} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (m : ℕ) : IsIsotypicOfType A (Fin m → S) S := by
  intro p _
                                                                            
  have hex : ∃ j, ((LinearMap.proj j) ∘ₗ p.subtype : ↥p →ₗ[A] S) ≠ 0 := by
    by_contra h
    push Not at h
    haveI : Nontrivial ↥p := IsSimpleModule.nontrivial A ↥p
    have : Subsingleton ↥p := by
      refine ⟨fun a b => ?_⟩
      have eq0 : ∀ c : ↥p, c = 0 := by
        intro c
        apply Subtype.ext
        funext j
        have := DFunLike.congr_fun (h j) c
        simpa using this
      rw [eq0 a, eq0 b]
    exact (not_subsingleton ↥p) this
  obtain ⟨j, hj⟩ := hex
  have hinj := LinearMap.injective_of_ne_zero hj
  exact ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hj)⟩

section

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)] [∀ i, Module.Finite A (V i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
                                                                                              
private theorem exists_iso_of_simple (n : ι → ℕ)
    (s : Submodule A (∀ k, Fin (n k) → V k)) [IsSimpleModule A ↥s] :
    ∃ i, Nonempty (↥s ≃ₗ[A] V i) := by
  have hex : ∃ i, ((LinearMap.proj i) ∘ₗ s.subtype : ↥s →ₗ[A] _) ≠ 0 := by
    by_contra h
    push Not at h
    haveI : Nontrivial ↥s := IsSimpleModule.nontrivial A ↥s
    have : Subsingleton ↥s := by
      refine ⟨fun a b => ?_⟩
      have eq0 : ∀ c : ↥s, c = 0 := by
        intro c
        apply Subtype.ext
        funext i
        have := DFunLike.congr_fun (h i) c
        simpa using this
      rw [eq0 a, eq0 b]
    exact (not_subsingleton ↥s) this
  obtain ⟨i, hi⟩ := hex
  have hinj := LinearMap.injective_of_ne_zero hi
  haveI : IsSimpleModule A ↥(LinearMap.range ((LinearMap.proj i) ∘ₗ s.subtype)) :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective _ hinj)).mp inferInstance
  refine ⟨i, ⟨(LinearEquiv.ofInjective _ hinj).trans
    (isIsotypicOfType_fin_fun (n i) (LinearMap.range ((LinearMap.proj i) ∘ₗ s.subtype))).some⟩⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
                                                                                         
                                                                              
private theorem coord_eq_zero_of_iso (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    {i j : ι} (hij : i ≠ j) {m : Submodule A (∀ k, Fin (n k) → V k)}
    (hm : Nonempty (↥m ≃ₗ[A] V i)) {x : ∀ k, Fin (n k) → V k} (hx : x ∈ m) :
    x j = 0 := by
  obtain ⟨em⟩ := hm
  haveI : IsSimpleModule A ↥m := (LinearEquiv.isSimpleModule_iff em).mpr inferInstance
  set f : ↥m →ₗ[A] (Fin (n j) → V j) := (LinearMap.proj j) ∘ₗ m.subtype with hf
  rcases eq_or_ne f 0 with h0 | h0
  · have : f ⟨x, hx⟩ = 0 := by rw [h0]; rfl
    simpa [hf] using this
  · exfalso
    have hinj := LinearMap.injective_of_ne_zero h0
    haveI : IsSimpleModule A ↥(LinearMap.range f) :=
      (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective f hinj)).mp inferInstance
    have e2 := (isIsotypicOfType_fin_fun (n j) (LinearMap.range f)).some
    exact hij (hd ⟨em.symm.trans ((LinearEquiv.ofInjective f hinj).trans e2)⟩)

omit [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
                                                                                            
                                                         
set_option linter.unusedFintypeInType false in
                                                                    
                                                                                    
                                                                                    
/-- A submodule of a displayed finite function module is equivalent to one with bounded multiplicities. -/
@[source_ref "Chapter3/Proposition3.1.4" (role := supporting), source_ref "Chapter3/Theorem3.2.2/Derived4" (role := supporting)]
theorem exists_equiv_pi_fin (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ∀ i, Fin (r i) → V i) := by
  classical
                                         
  set C : ι → Submodule A ↥W := fun i => isotypicComponent A (↥W) (V i) with hC
  have hCiso : ∀ i, IsIsotypicOfType A ↥(C i) (V i) := fun i => le_isotypicComponent_iff.mp le_rfl
                                                                   
  choose r hr using fun i => (hCiso i).linearEquiv_fun
  have e : ∀ i, ↥(C i) ≃ₗ[A] (Fin (r i) → V i) := fun i => (hr i).some
                                                      
  have length_fun : ∀ (m : ℕ) (j : ι), Module.length A (Fin m → V j) = (m : ℕ∞) := by
    intro m j
    rw [Module.length_pi_of_fintype]
    simp
                                                                     
  have iso_of_le : ∀ {k : ι} {t : Submodule A ↥W} (_ : IsSimpleModule A ↥t),
      t ≤ C k → Nonempty (↥t ≃ₗ[A] V k) := by
    intro k t hsimp hle
    haveI := hsimp
    have hit : IsIsotypicOfType A ↥t (V k) := le_isotypicComponent_iff.mp hle
                                                                       
    exact isIsotypicOfType_submodule_iff.mp hit t le_rfl
  have simple_mem : ∀ {s : Submodule A ↥W}, IsSimpleModule A ↥s → ∃ i, s ≤ C i := by
    intro s hs
    haveI := hs
                                                                        
    have es := Submodule.equivMapOfInjective W.subtype W.subtype_injective s
    haveI : IsSimpleModule A ↥(Submodule.map W.subtype s) :=
      (LinearEquiv.isSimpleModule_iff es).mp hs
    obtain ⟨i, ⟨ei⟩⟩ := exists_iso_of_simple n (Submodule.map W.subtype s)
    refine ⟨i, ?_⟩
    rw [hC, le_isotypicComponent_iff]
    exact (IsIsotypicOfType.of_isSimpleModule A ↥s).of_linearEquiv_type (es.trans ei)
                    
  have htop : ⨆ i, C i = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top A ↥W]
    apply sSup_le
    intro s hs
    obtain ⟨i, hi⟩ := simple_mem hs
    exact hi.trans (le_iSup C i)
                                  
  have hind : iSupIndep C := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
                                             
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (C i ⊓ ⨆ j, ⨆ (_ : j ≠ i), C j) with
      hbot | ⟨t, htle, _⟩
    · rw [hbot]
    · exfalso
      have ht_i : t ≤ C i := htle.trans inf_le_left
      have ht_sup : t ≤ ⨆ j, ⨆ (_ : j ≠ i), C j := htle.trans inf_le_right
                   
      obtain ⟨eti⟩ := iso_of_le ‹IsSimpleModule A ↥t› ht_i
                                                                           
      have hts : t ≤ sSup (C '' {j | j ≠ i}) := by
        rw [sSup_image]; exact ht_sup
      haveI : ∀ q : ↥(C '' {j | j ≠ i}), IsSemisimpleModule A ↥(q : Submodule A ↥W) :=
        fun q => inferInstance
      obtain ⟨q, hq, S, hSle, ⟨eS⟩⟩ :=
        Submodule.le_linearEquiv_of_le_sSup t (C '' {j | j ≠ i}) hts
      obtain ⟨j, hj, rfl⟩ := hq
      haveI : IsSimpleModule A ↥S := (LinearEquiv.isSimpleModule_iff eS).mp ‹_›
      obtain ⟨eSj⟩ := iso_of_le ‹IsSimpleModule A ↥S› hSle
      exact hj (hd ⟨(eti.symm.trans (eS.trans eSj)).symm⟩)
                                                                               
  have eqW : ↥W ≃ₗ[A] ∀ i, Fin (r i) → V i :=
    (hind.linearEquiv htop).symm.trans
      ((DirectSum.linearEquivFunOnFintype A ι (fun i => ↥(C i))).trans
        (LinearEquiv.piCongrRight fun i => e i))
  refine ⟨r, ?_, ⟨eqW⟩⟩
                                        
  intro i
                          
  have hlenC : Module.length A ↥(C i) = (r i : ℕ∞) := by
    rw [(e i).length_eq, length_fun]
                                          
  have eCi' := Submodule.equivMapOfInjective W.subtype W.subtype_injective (C i)
  have hCi'_le : Submodule.map W.subtype (C i) ≤
      isotypicComponent A (∀ k, Fin (n k) → V k) (V i) := by
    rw [le_isotypicComponent_iff]
    exact (LinearEquiv.isIsotypicOfType_iff eCi').mp (hCiso i)
                                                                                       
  have hisoComp_le : isotypicComponent A (∀ k, Fin (n k) → V k) (V i) ≤
      LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i) := by
    refine sSup_le ?_
    rintro m ⟨em⟩
    intro x hx
    refine ⟨x i, ?_⟩
    funext j
    rw [LinearMap.single_apply]
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hji]
      exact (coord_eq_zero_of_iso n hd (Ne.symm hji) ⟨em⟩ hx).symm
                                       
  have hlenSummand : Module.length A
      ↥(LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i)) = (n i : ℕ∞) := by
    have hsi : Function.Injective (LinearMap.single A (fun k => Fin (n k) → V k) i) := by
      intro a b hab
      have h2 := congrFun hab i
      simpa [LinearMap.single_apply] using h2
    rw [(LinearEquiv.ofInjective _ hsi).symm.length_eq, length_fun]
                                                 
  have hchain : (r i : ℕ∞) ≤ (n i : ℕ∞) := by
    rw [← hlenC, ← hlenSummand]
    calc Module.length A ↥(C i)
        = Module.length A ↥(Submodule.map W.subtype (C i)) := eCi'.length_eq
      _ ≤ Module.length A ↥(isotypicComponent A (∀ k, Fin (n k) → V k) (V i)) :=
          Module.length_le_of_injective (Submodule.inclusion hCi'_le)
            (Submodule.inclusion_injective hCi'_le)
      _ ≤ Module.length A ↥(LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i)) :=
          Module.length_le_of_injective (Submodule.inclusion hisoComp_le)
            (Submodule.inclusion_injective hisoComp_le)
  exact_mod_cast hchain

omit [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
                                                                                          
                                                                          
set_option linter.unusedFintypeInType false in
                          
                                                                                          
                                                                                          
                                               
/-- A submodule of a direct sum of pairwise inequivalent simple types is equivalent to a direct sum with bounded multiplicities. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting), source_ref "Chapter3/Proposition3.1.4" (role := primary)]
theorem exists_equiv_directSum_fin (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)) := by
  classical
                                                                                      
  set g := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (n i) → V i) with hg
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_pi_fin n hd (Submodule.map g.toLinearMap W)
  refine ⟨r, hr, ⟨?_⟩⟩
  exact (Submodule.equivMapOfInjective g.toLinearMap g.injective W).trans
    (e.trans (DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (r i) → V i)).symm)

end

section Matrix

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)]

omit [Fintype ι] [DecidableEq ι] in
                                                                                         
                                            
private theorem hom_eq_zero_of_ne
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    {i j : ι} (hij : i ≠ j) (f : V i →ₗ[A] V j) : f = 0 := by
  by_contra h
  exact hij (hd ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero h)⟩)

omit [DecidableEq ι] in
                                                                                              
                               
set_option linter.unusedFintypeInType false in
                                                                                  

                                                                                        
                                                                                     
                                                                          
                                                                                         
                                                                                     
                           
/--
A submodule of the displayed function module admits bounded multiplicities and linearly
independent coordinate data satisfying the stated expansion formula.
-/
@[source_ref "Chapter3/Corollary3.2.1/Derived2" (role := supporting), source_ref "Chapter3/Proposition3.1.4" (role := supporting)]
theorem exists_linearIndependent_coordinates_pi (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ (r : ι → ℕ) (X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)))
      (e : ↥W ≃ₗ[A] ∀ i, Fin (r i) → V i),
      (∀ i, r i ≤ n i) ∧
      (∀ i, LinearIndependent (Module.End A (V i))ᵐᵒᵖ (X i)) ∧
      ∀ (w : ↥W) (i : ι) (l : Fin (n i)),
        (w : ∀ k, Fin (n k) → V k) i l = ∑ a, X i a l (e w i a) := by
  classical
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_equiv_pi_fin n hd W
                                                                          
  set φ : (∀ k, Fin (r k) → V k) →ₗ[A] (∀ k, Fin (n k) → V k) :=
    W.subtype ∘ₗ (e.symm : (∀ k, Fin (r k) → V k) →ₗ[A] ↥W) with hφdef
  have hφinj : Function.Injective φ := W.subtype_injective.comp e.symm.injective
                            
  set Φ : ∀ i : ι, Fin (n i) → ((∀ k, Fin (r k) → V k) →ₗ[A] V i) := fun i l =>
    (LinearMap.proj l) ∘ₗ (LinearMap.proj i) ∘ₗ φ with hΦdef
                                                              
  set sr : ∀ k : ι, Fin (r k) → (V k →ₗ[A] (∀ k, Fin (r k) → V k)) := fun k a =>
    (LinearMap.single A (fun k => Fin (r k) → V k) k) ∘ₗ
      (LinearMap.single A (fun _ : Fin (r k) => V k) a) with hsrdef
                                                               
  set G : ∀ k : ι, Fin (r k) → ∀ i : ι, Fin (n i) → (V k →ₗ[A] V i) := fun k a i l =>
    (Φ i l) ∘ₗ (sr k a) with hGdef
  set X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)) := fun i a l =>
    G i a i l with hXdef
                                                                                    
  have hoff : ∀ (k i : ι), k ≠ i → ∀ (a : Fin (r k)) (l : Fin (n i)), G k a i l = 0 :=
    fun k i hki a l => hom_eq_zero_of_ne hd hki _
  have decompR : ∀ y : ∀ k, Fin (r k) → V k,
      (∑ k, LinearMap.single A (fun k => Fin (r k) → V k) k (y k)) = y := by
    intro y
    simpa [LinearMap.single_apply] using Finset.univ_sum_single y
  have decompr : ∀ (k : ι) (z : Fin (r k) → V k),
      (∑ a, LinearMap.single A (fun _ : Fin (r k) => V k) a (z a)) = z := by
    intro k z
    simpa [LinearMap.single_apply] using Finset.univ_sum_single z
                                                                 
  have key : ∀ (y : ∀ k, Fin (r k) → V k) (i : ι) (l : Fin (n i)),
      φ y i l = ∑ a, X i a l (y i a) := by
    intro y i l
    have h1 : Φ i l y = ∑ k, ∑ a, G k a i l (y k a) := by
      conv_lhs => rw [← decompR y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [← decompr k (y k)]
      simp only [map_sum, hGdef, hsrdef, LinearMap.comp_apply]
    have h2 : (∑ k, ∑ a, G k a i l (y k a)) = ∑ a, G i a i l (y i a) := by
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
      simp [hoff k i hk]
    calc φ y i l = Φ i l y := rfl
      _ = ∑ a, G i a i l (y i a) := by rw [h1, h2]
      _ = ∑ a, X i a l (y i a) := by simp [hXdef]
  refine ⟨r, X, e, hr, ?_, ?_⟩
  ·                                                                      
    intro i
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have hc' : ∀ (l : Fin (n i)) (v : V i), (∑ b, X i b l ((c b).unop v)) = 0 := by
      intro l v
      have h := congrFun hc l
      rw [Finset.sum_apply] at h
      have h2 : (∑ b, X i b l * (c b).unop) = 0 := h
      have := congrArg (fun f : Module.End A (V i) => f v) h2
      simpa [Module.End.mul_apply] using this
                                                                              
    have hz : ∀ v : V i, ∀ b : Fin (r i), (c b).unop v = 0 := by
      intro v
      set z : Fin (r i) → V i := fun b => (c b).unop v with hzdef
      set y : ∀ k, Fin (r k) → V k :=
        LinearMap.single A (fun k => Fin (r k) → V k) i z with hydef
      have h0 : φ y = 0 := by
        funext j
        funext l'
        rw [key y j l']
        rcases eq_or_ne j i with rfl | hji
        · have hyj : y j = z := by simp [hydef, LinearMap.single_apply]
          rw [hyj]
          simpa using hc' l' v
        · have hyj : y j = 0 := by
            simp [hydef, LinearMap.single_apply, Pi.single_eq_of_ne hji]
          simp [hyj]
      have hy0 : y = 0 := hφinj (by rw [h0, map_zero])
      intro b
      have := congrFun (congrFun hy0 i) b
      simpa [hydef, LinearMap.single_apply] using this
    have : (c a).unop = 0 := by
      ext v
      exact hz v a
    exact MulOpposite.unop_injective (by simpa using this)
  · intro w i l
    have hw : (w : ∀ k, Fin (n k) → V k) = φ (e w) := by
      simp [hφdef]
    rw [hw]
    exact key (e w) i l

omit [DecidableEq ι] in
                                                                                             
                                                             
set_option linter.unusedFintypeInType false in
                                                                                        
                                                                                        
                                  
/--
A submodule of the displayed direct sum admits bounded multiplicities and linearly independent
coordinate data satisfying the stated expansion formula.
-/
@[source_ref "Chapter3/Discussion_after_Lemma3.1.6/Derived4" (role := supporting), source_ref "Chapter3/Proposition3.1.4" (role := supporting)]
theorem exists_linearIndependent_coordinates_directSum (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ (r : ι → ℕ) (X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)))
      (e : ↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)),
      (∀ i, r i ≤ n i) ∧
      (∀ i, LinearIndependent (Module.End A (V i))ᵐᵒᵖ (X i)) ∧
      ∀ (w : ↥W) (i : ι) (l : Fin (n i)),
        (w : ⨁ k, (Fin (n k) → V k)) i l = ∑ a, X i a l (e w i a) := by
  classical
  set g := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (n i) → V i) with hg
  obtain ⟨r, X, e, hr, hli, hform⟩ :=
    exists_linearIndependent_coordinates_pi n hd (Submodule.map g.toLinearMap W)
  set g' := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (r i) → V i) with hg'
  set em := Submodule.equivMapOfInjective g.toLinearMap g.injective W with hem
  refine ⟨r, X, em.trans (e.trans g'.symm), hr, hli, ?_⟩
  intro w i l
  have h := hform (em w) i l
                                                                                            
                              
  have hcoe : ∀ (z : ⨁ k, (Fin (n k) → V k)) (j : ι), g z j = z j := fun _ _ => rfl
  have hcoe' : ∀ (z : ⨁ k, (Fin (r k) → V k)) (j : ι), g' z j = z j := fun _ _ => rfl
  have hleft : ((em w : ↥(Submodule.map g.toLinearMap W)) : ∀ k, Fin (n k) → V k) i
      = (w : ⨁ k, (Fin (n k) → V k)) i := by
    rw [hem, Submodule.coe_equivMapOfInjective_apply]
    exact hcoe _ i
  have hright : ∀ a, (e (em w)) i a = ((em.trans (e.trans g'.symm)) w) i a := by
    intro a
    have hz : ((em.trans (e.trans g'.symm)) w) i = (g' (g'.symm (e (em w)))) i :=
      (hcoe' (g'.symm (e (em w))) i).symm
    rw [hz, g'.apply_symm_apply]
  rw [← hleft, h]
  exact Finset.sum_congr rfl fun a _ => by rw [hright a]

end Matrix

end RepresentationTheory.Algebra.Module.IsotypicDecomposition
