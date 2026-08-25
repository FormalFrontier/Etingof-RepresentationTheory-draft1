/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.FiniteDecompositions
import RepresentationTheory.Alignment.Attribute

/-! # Equivalence transfers -/




















open scoped DirectSum

namespace RepresentationTheory.Algebra.Module.EquivalenceTransfers



/-- The displayed module property is preserved by a linear equivalence. -/
theorem _root_.RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.map {A V W : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A V) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W := by
  obtain ⟨hne, hsplit⟩ := hV
  refine ⟨?_, fun W₁ W₂ hC => ?_⟩
  · obtain ⟨a, b, hab⟩ := hne
    exact ⟨e a, e b, fun h => hab (e.injective h)⟩
  
  set g := (Submodule.orderIsoMapComap (e : V ≃ₗ[A] W)).symm with hg
  have hC' : IsCompl (g W₁) (g W₂) := g.isCompl_iff.mp hC
  have hbot : ∀ {U : Submodule A W}, g U = ⊥ → U = ⊥ := by
    intro U hU
    have : g U = g ⊥ := by rw [hU, OrderIso.map_bot]
    exact g.injective this
  rcases hsplit _ _ hC' with h1 | h2
  · exact Or.inl (hbot h1)
  · exact Or.inr (hbot h2)





/-- A linear equivalence transports a finite internal spanning family with the displayed submodule property. -/
theorem map_internalFamily {A V V' : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup V'] [Module A V']
    (e : V ≃ₗ[A] V') {p : ℕ} (D : Fin p → Submodule A V)
    (hindec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (D i))
    (hne : ∀ i, D i ≠ ⊥) (hsup : iSup D = ⊤) (hind : iSupIndep D) :
    (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A ((D i).map (e : V →ₗ[A] V'))) ∧
      (∀ i, (D i).map (e : V →ₗ[A] V') ≠ ⊥) ∧
      iSup (fun i => (D i).map (e : V →ₗ[A] V')) = ⊤ ∧
      iSupIndep (fun i => (D i).map (e : V →ₗ[A] V')) := by
  refine ⟨fun i => (hindec i).map
      (Submodule.equivMapOfInjective (e : V →ₗ[A] V') e.injective (D i)), fun i => ?_, ?_, ?_⟩
  · rw [Ne, Submodule.map_eq_bot_iff]
    exact hne i
  · rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearEquiv.range]
  · exact LinearMap.iSupIndep_map (e : V →ₗ[A] V') e.injective hind

set_option linter.unusedFintypeInType false in




private theorem exists_indexEquiv (k A M : Type*) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (D : ι → Submodule A M) (D' : ι' → Submodule A M)
    (hD_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (D i))
    (hD'_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (D' i))
    (hD_ne : ∀ i, D i ≠ ⊥) (hD'_ne : ∀ i, D' i ≠ ⊥)
    (hD_sup : iSup D = ⊤) (hD_ind : iSupIndep D)
    (hD'_sup : iSup D' = ⊤) (hD'_ind : iSupIndep D') :
    ∃ σ : ι ≃ ι', ∀ i, Nonempty (D i ≃ₗ[A] D' (σ i)) := by
  set a := Fintype.equivFin ι
  set b := Fintype.equivFin ι'
  obtain ⟨-, σ₀, hσ₀⟩ := RepresentationTheory.Algebra.Module.FiniteDecompositions.internal_family_unique_up_to_permutation k A M
    (D ∘ a.symm) (D' ∘ b.symm)
    (fun i => hD_indec _) (fun j => hD'_indec _)
    (fun i => hD_ne _) (fun j => hD'_ne _)
    (by rw [← hD_sup]; exact a.symm.iSup_comp) (hD_ind.comp a.symm.injective)
    (by rw [← hD'_sup]; exact b.symm.iSup_comp) (hD'_ind.comp b.symm.injective)
  refine ⟨a.trans (σ₀.trans b.symm), fun i => ?_⟩
  have h := hσ₀ (a i)
  simp only [Function.comp_apply] at h
  rw [show a.symm (a i) = i from a.symm_apply_apply i] at h
  exact h





private theorem iSupIndep_prod_of_families {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {κ ι : Type*} (s : κ → ι → α)
    (hblock : iSupIndep (fun k => ⨆ i, s k i))
    (hin : ∀ k, iSupIndep (s k)) :
    iSupIndep (fun ki : κ × ι => s ki.1 ki.2) := by
  rintro ⟨k, i⟩
  set B : κ → α := fun k => ⨆ i, s k i with hB
  set X : α := ⨆ (i') (_ : i' ≠ i), s k i' with hX_def
  set Y : α := ⨆ (k') (_ : k' ≠ k), B k' with hY_def
  have hsB : s k i ≤ B k := le_iSup (s k) i
  have hXB : X ≤ B k := iSup₂_le fun i' _ => le_iSup (s k) i'
  have hX : Disjoint (s k i) X := hin k i
  have hB' : Disjoint (B k) Y := hblock k
  
  have hcov : (⨆ (x : κ × ι) (_ : x ≠ (k, i)), s x.1 x.2) ≤ X ⊔ Y := by
    refine iSup₂_le fun x hx => ?_
    rcases eq_or_ne x.1 k with hk | hk
    · have hi : x.2 ≠ i := by
        intro hi; apply hx; ext <;> simp [hk, hi]
      calc s x.1 x.2 = s k x.2 := by rw [hk]
        _ ≤ X := le_iSup₂ (f := fun i' (_ : i' ≠ i) => s k i') x.2 hi
        _ ≤ X ⊔ Y := le_sup_left
    · calc s x.1 x.2 ≤ B x.1 := le_iSup (s x.1) x.2
        _ ≤ Y := le_iSup₂ (f := fun k' (_ : k' ≠ k) => B k') x.1 hk
        _ ≤ X ⊔ Y := le_sup_right
  refine Disjoint.mono_right hcov ?_
  
  rw [disjoint_iff]
  have hYBk : Y ⊓ B k = ⊥ := by rw [inf_comm]; exact disjoint_iff.mp hB'
  calc s k i ⊓ (X ⊔ Y)
      = s k i ⊓ (B k ⊓ (X ⊔ Y)) := by rw [← inf_assoc, inf_eq_left.mpr hsB]
    _ = s k i ⊓ ((X ⊔ Y) ⊓ B k) := by rw [inf_comm (B k)]
    _ = s k i ⊓ (X ⊔ Y ⊓ B k) := by rw [sup_inf_assoc_of_le _ hXB]
    _ = s k i ⊓ X := by rw [hYBk, sup_bot_eq]
    _ = ⊥ := disjoint_iff.mp hX





private theorem iSupIndep_sum_of_families {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {κ ι : Type*} (s : κ → α) (t : ι → α)
    (hdisj : Disjoint (⨆ a, s a) (⨆ b, t b))
    (hs : iSupIndep s) (ht : iSupIndep t) :
    iSupIndep (Sum.elim s t) := by
  set S : α := ⨆ a, s a with hS
  set T : α := ⨆ b, t b with hT
  rintro (a | b)
  · 
    set X : α := ⨆ (a') (_ : a' ≠ a), s a' with hX_def
    have hsS : s a ≤ S := le_iSup s a
    have hXS : X ≤ S := iSup₂_le fun a' _ => le_iSup s a'
    have hX : Disjoint (s a) X := hs a
    have hcov : (⨆ (x : κ ⊕ ι) (_ : x ≠ Sum.inl a), Sum.elim s t x) ≤ X ⊔ T := by
      refine iSup₂_le fun x hx => ?_
      rcases x with a' | b'
      · have : a' ≠ a := fun h => hx (by rw [h])
        calc Sum.elim s t (Sum.inl a') = s a' := rfl
          _ ≤ X := le_iSup₂ (f := fun a' (_ : a' ≠ a) => s a') a' this
          _ ≤ X ⊔ T := le_sup_left
      · calc Sum.elim s t (Sum.inr b') = t b' := rfl
          _ ≤ T := le_iSup t b'
          _ ≤ X ⊔ T := le_sup_right
    refine Disjoint.mono_right hcov ?_
    rw [disjoint_iff]
    have hTS : T ⊓ S = ⊥ := by rw [inf_comm]; exact disjoint_iff.mp hdisj
    calc s a ⊓ (X ⊔ T)
        = s a ⊓ (S ⊓ (X ⊔ T)) := by rw [← inf_assoc, inf_eq_left.mpr hsS]
      _ = s a ⊓ ((X ⊔ T) ⊓ S) := by rw [inf_comm S]
      _ = s a ⊓ (X ⊔ T ⊓ S) := by rw [sup_inf_assoc_of_le _ hXS]
      _ = s a ⊓ X := by rw [hTS, sup_bot_eq]
      _ = ⊥ := disjoint_iff.mp hX
  · 
    set X : α := ⨆ (b') (_ : b' ≠ b), t b' with hX_def
    have htT : t b ≤ T := le_iSup t b
    have hXT : X ≤ T := iSup₂_le fun b' _ => le_iSup t b'
    have hX : Disjoint (t b) X := ht b
    have hcov : (⨆ (x : κ ⊕ ι) (_ : x ≠ Sum.inr b), Sum.elim s t x) ≤ X ⊔ S := by
      refine iSup₂_le fun x hx => ?_
      rcases x with a' | b'
      · calc Sum.elim s t (Sum.inl a') = s a' := rfl
          _ ≤ S := le_iSup s a'
          _ ≤ X ⊔ S := le_sup_right
      · have : b' ≠ b := fun h => hx (by rw [h])
        calc Sum.elim s t (Sum.inr b') = t b' := rfl
          _ ≤ X := le_iSup₂ (f := fun b' (_ : b' ≠ b) => t b') b' this
          _ ≤ X ⊔ S := le_sup_left
    refine Disjoint.mono_right hcov ?_
    rw [disjoint_iff]
    have hST : S ⊓ T = ⊥ := disjoint_iff.mp hdisj
    calc t b ⊓ (X ⊔ S)
        = t b ⊓ (T ⊓ (X ⊔ S)) := by rw [← inf_assoc, inf_eq_left.mpr htT]
      _ = t b ⊓ ((X ⊔ S) ⊓ T) := by rw [inf_comm T]
      _ = t b ⊓ (X ⊔ S ⊓ T) := by rw [sup_inf_assoc_of_le _ hXT]
      _ = t b ⊓ X := by rw [hST, sup_bot_eq]
      _ = ⊥ := disjoint_iff.mp hX

open LinearMap in




private theorem finFunction_internalFamily {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    {n p : ℕ} (D : Fin p → Submodule A M)
    (hindec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (D i))
    (hne : ∀ i, D i ≠ ⊥) (hsup : iSup D = ⊤) (hind : iSupIndep D) :
    (∀ ci : Fin n × Fin p,
        RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A ((D ci.2).map (single A (fun _ : Fin n => M) ci.1))) ∧
      (∀ ci : Fin n × Fin p, (D ci.2).map (single A (fun _ : Fin n => M) ci.1) ≠ ⊥) ∧
      iSup (fun ci : Fin n × Fin p => (D ci.2).map (single A (fun _ : Fin n => M) ci.1)) = ⊤ ∧
      iSupIndep (fun ci : Fin n × Fin p => (D ci.2).map (single A (fun _ : Fin n => M) ci.1)) := by
  set φ : Fin n → Type _ := fun _ => M with hφ
  set sg : Fin n → (M →ₗ[A] (Fin n → M)) := fun c => single A φ c with hsg
  have hinj : ∀ c, Function.Injective (sg c) := fun c =>
    Function.LeftInverse.injective (g := (proj c : (Fin n → M) →ₗ[A] M)) (fun x => by
      have := LinearMap.congr_fun
        (show (proj c).comp (sg c) = LinearMap.id by rw [hsg]; exact proj_comp_single_same A φ c) x
      simpa using this)
  
  have hI : ∀ ci : Fin n × Fin p, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A ((D ci.2).map (sg ci.1)) :=
    fun ci => (hindec ci.2).map (Submodule.equivMapOfInjective _ (hinj ci.1) (D ci.2))
  
  have hN : ∀ ci : Fin n × Fin p, (D ci.2).map (sg ci.1) ≠ ⊥ := fun ci => by
    obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne ci.2)
    intro hbot
    have hmem : sg ci.1 x ∈ (D ci.2).map (sg ci.1) := Submodule.mem_map_of_mem hxmem
    rw [hbot, Submodule.mem_bot] at hmem
    exact hxne (hinj ci.1 (hmem.trans (map_zero (sg ci.1)).symm))
  
  have hblockeq : ∀ c, (⨆ i, (D i).map (sg c)) = range (sg c) := fun c => by
    rw [← Submodule.map_iSup, hsup, Submodule.map_top]
  
  have hS : iSup (fun ci : Fin n × Fin p => (D ci.2).map (sg ci.1)) = ⊤ := by
    rw [iSup_prod]
    simp_rw [hblockeq]
    simp only [hsg]; exact iSup_range_single A φ
  
  
  have haxes : iSupIndep (fun c : Fin n => range (sg c)) := by
    intro c
    have hle : (⨆ (c') (_ : c' ≠ c), range (sg c')) ≤ ker (proj c) :=
      iSup₂_le fun c' hc' => range_le_ker_iff.mpr
        (by rw [hsg]; exact proj_comp_single_ne A φ c c' (Ne.symm hc'))
    refine Disjoint.mono_right hle ?_
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨⟨v, rfl⟩, hx2⟩ := hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx2
    have hv : (LinearMap.proj (R := A) (φ := φ) c) (sg c v) = v := by
      have h := LinearMap.congr_fun (proj_comp_single_same A φ c) v
      simp only [hsg, LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h ⊢
      exact h
    rw [hv] at hx2
    simp [hx2]
  have hbl : iSupIndep (fun c : Fin n => ⨆ i, (D i).map (sg c)) := by
    simp_rw [hblockeq]; exact haxes
  have hin : ∀ c, iSupIndep (fun i => (D i).map (sg c)) :=
    fun c => LinearMap.iSupIndep_map (sg c) (hinj c) hind
  have hInd : iSupIndep (fun ci : Fin n × Fin p => (D ci.2).map (sg ci.1)) :=
    iSupIndep_prod_of_families (fun c i => (D i).map (sg c)) hbl hin
  exact ⟨hI, hN, hS, hInd⟩







private theorem exists_equiv_of_repeated_fibers {C : Type*} {p q n : ℕ} (hn : 0 < n)
    (f : Fin p → C) (g : Fin q → C)
    (σ : (Fin n × Fin p) ≃ (Fin n × Fin q))
    (hσ : ∀ x, g (σ x).2 = f x.2) :
    ∃ τ : Fin p ≃ Fin q, ∀ i, g (τ i) = f i := by
  classical
  
  have key : ∀ c : C, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := by
    intro c
    
    have e : {x : Fin n × Fin p // f x.2 = c} ≃ {y : Fin n × Fin q // g y.2 = c} :=
      { toFun := fun x => ⟨σ x.1, by rw [hσ]; exact x.2⟩
        invFun := fun y => ⟨σ.symm y.1, by
          have h := hσ (σ.symm y.1); rw [σ.apply_symm_apply] at h; rw [← h]; exact y.2⟩
        left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
    
    have eF : {x : Fin n × Fin p // f x.2 = c} ≃ Fin n × {i // f i = c} :=
      { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        left_inv := fun x => by rcases x with ⟨⟨a, b⟩, h⟩; rfl
        right_inv := fun y => by rcases y with ⟨a, b, h⟩; rfl }
    have eG : {y : Fin n × Fin q // g y.2 = c} ≃ Fin n × {j // g j = c} :=
      { toFun := fun y => (y.1.1, ⟨y.1.2, y.2⟩)
        invFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
        left_inv := fun y => by rcases y with ⟨⟨a, b⟩, h⟩; rfl
        right_inv := fun z => by rcases z with ⟨a, b, h⟩; rfl }
    have hFF : Fintype.card {x : Fin n × Fin p // f x.2 = c} = n * Fintype.card {i // f i = c} := by
      rw [Fintype.card_congr eF, Fintype.card_prod, Fintype.card_fin]
    have hGG : Fintype.card {y : Fin n × Fin q // g y.2 = c} = n * Fintype.card {j // g j = c} := by
      rw [Fintype.card_congr eG, Fintype.card_prod, Fintype.card_fin]
    have hEq : n * Fintype.card {i // f i = c} = n * Fintype.card {j // g j = c} := by
      rw [← hFF, ← hGG, Fintype.card_congr e]
    exact Nat.eq_of_mul_eq_mul_left hn hEq
  
  let eqv : ∀ c : C, {i // f i = c} ≃ {j // g j = c} := fun c => Fintype.equivOfCardEq (key c)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight eqv).trans (Equiv.sigmaFiberEquiv g)), fun i => ?_⟩
  exact (eqv (f i) ⟨i, rfl⟩).2

open LinearMap in

private theorem single_injective {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    {n : ℕ} (c : Fin n) : Function.Injective (single A (fun _ : Fin n => M) c) :=
  Function.LeftInverse.injective (g := LinearMap.proj (R := A) (φ := fun _ : Fin n => M) c)
    (fun x => by
      have h := LinearMap.congr_fun (proj_comp_single_same A (fun _ : Fin n => M) c) x
      simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h
      exact h)





private theorem map_internalFamily_aux {A V V' : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup V'] [Module A V']
    (e : V ≃ₗ[A] V') {ι : Type*} (D : ι → Submodule A V)
    (hindec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (D i))
    (hne : ∀ i, D i ≠ ⊥) (hsup : iSup D = ⊤) (hind : iSupIndep D) :
    (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A ((D i).map (e : V →ₗ[A] V'))) ∧
      (∀ i, (D i).map (e : V →ₗ[A] V') ≠ ⊥) ∧
      iSup (fun i => (D i).map (e : V →ₗ[A] V')) = ⊤ ∧
      iSupIndep (fun i => (D i).map (e : V →ₗ[A] V')) := by
  refine ⟨fun i => (hindec i).map
      (Submodule.equivMapOfInjective (e : V →ₗ[A] V') e.injective (D i)), fun i => ?_, ?_, ?_⟩
  · rw [Ne, Submodule.map_eq_bot_iff]
    exact hne i
  · rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearEquiv.range]
  · exact LinearMap.iSupIndep_map (e : V →ₗ[A] V') e.injective hind










/-- An equivalence between positive finite function modules yields an equivalence between their value modules. -/
@[source_ref "Chapter3/Problem3.8.4" (role := supporting)]
theorem exists_equiv_of_fin_fun_equiv (k A V W : Type*) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    {n : ℕ} (hn : 0 < n)
    (h : Nonempty ((Fin n → V) ≃ₗ[A] (Fin n → W))) :
    Nonempty (V ≃ₗ[A] W) := by
  classical
  
  obtain ⟨p, DV, hDV_indec, hDV_sup, hDV_ind⟩ := RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family k A V
  obtain ⟨q, DW, hDW_indec, hDW_sup, hDW_ind⟩ := RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family k A W
  have hDV_ne : ∀ i, DV i ≠ ⊥ := fun i => Submodule.nontrivial_iff_ne_bot.mp (hDV_indec i).1
  have hDW_ne : ∀ j, DW j ≠ ⊥ := fun j => Submodule.nontrivial_iff_ne_bot.mp (hDW_indec j).1
  set e : (Fin n → V) ≃ₗ[A] (Fin n → W) := h.some with he
  
  set sgV : Fin n → (V →ₗ[A] (Fin n → V)) :=
    fun c => LinearMap.single A (fun _ : Fin n => V) c with hsgV
  set sgW : Fin n → (W →ₗ[A] (Fin n → W)) :=
    fun c => LinearMap.single A (fun _ : Fin n => W) c with hsgW
  
  obtain ⟨hPV_indec, hPV_ne, hPV_sup, hPV_ind⟩ :=
    finFunction_internalFamily (n := n) DV hDV_indec hDV_ne hDV_sup hDV_ind
  obtain ⟨hPW_indec, hPW_ne, hPW_sup, hPW_ind⟩ :=
    finFunction_internalFamily (n := n) DW hDW_indec hDW_ne hDW_sup hDW_ind
  
  obtain ⟨hQW_indec, hQW_ne, hQW_sup, hQW_ind⟩ :=
    map_internalFamily_aux e.symm (fun cj : Fin n × Fin q => (DW cj.2).map (sgW cj.1))
      hPW_indec hPW_ne hPW_sup hPW_ind
  
  obtain ⟨σ, hσ⟩ := exists_indexEquiv k A (Fin n → V)
    (fun ci : Fin n × Fin p => (DV ci.2).map (sgV ci.1))
    (fun cj : Fin n × Fin q =>
      ((DW cj.2).map (sgW cj.1)).map (e.symm : (Fin n → W) →ₗ[A] (Fin n → V)))
    hPV_indec hQW_indec hPV_ne hQW_ne hPV_sup hPV_ind hQW_sup hQW_ind
  
  have isoPV : ∀ x : Fin n × Fin p, DV x.2 ≃ₗ[A] (DV x.2).map (sgV x.1) :=
    fun x => Submodule.equivMapOfInjective (sgV x.1) (single_injective _) (DV x.2)
  have isoPW : ∀ y : Fin n × Fin q, DW y.2 ≃ₗ[A] (DW y.2).map (sgW y.1) :=
    fun y => Submodule.equivMapOfInjective (sgW y.1) (single_injective _) (DW y.2)
  have isoQW : ∀ y : Fin n × Fin q, ((DW y.2).map (sgW y.1)) ≃ₗ[A]
      ((DW y.2).map (sgW y.1)).map (e.symm : (Fin n → W) →ₗ[A] (Fin n → V)) :=
    fun y => Submodule.equivMapOfInjective (e.symm : (Fin n → W) →ₗ[A] (Fin n → V))
      e.symm.injective _
  
  let rel : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → Prop := fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl i' => Nonempty (DV i ≃ₗ[A] DV i')
    | Sum.inl i, Sum.inr j => Nonempty (DV i ≃ₗ[A] DW j)
    | Sum.inr j, Sum.inl i => Nonempty (DW j ≃ₗ[A] DV i)
    | Sum.inr j, Sum.inr j' => Nonempty (DW j ≃ₗ[A] DW j')
  have hrefl : ∀ x, rel x x := by rintro (i | j) <;> exact ⟨LinearEquiv.refl A _⟩
  have hsymm : ∀ {x y}, rel x y → rel y x := by
    rintro (i | j) (i' | j') ⟨φ⟩ <;> exact ⟨φ.symm⟩
  have htrans : ∀ {x y z}, rel x y → rel y z → rel x z := by
    rintro (i | j) (i' | j') (i'' | j'') ⟨φ⟩ ⟨ψ⟩ <;> exact ⟨φ.trans ψ⟩
  letI S : Setoid (Fin p ⊕ Fin q) := ⟨rel, hrefl, hsymm, htrans⟩
  let fC : Fin p → Quotient S := fun i => ⟦Sum.inl i⟧
  let gC : Fin q → Quotient S := fun j => ⟦Sum.inr j⟧
  have hfg : ∀ i j, fC i = gC j ↔ Nonempty (DV i ≃ₗ[A] DW j) := fun i j => Quotient.eq
  
  have hfc : ∀ x : Fin n × Fin p, gC (σ x).2 = fC x.2 := by
    intro x
    rw [eq_comm, hfg x.2 (σ x).2]
    obtain ⟨φ⟩ := hσ x
    exact ⟨(isoPV x).trans (φ.trans ((isoPW (σ x)).trans (isoQW (σ x))).symm)⟩
  obtain ⟨τ, hτ⟩ := exists_equiv_of_repeated_fibers hn fC gC σ hfc
  have hiso : ∀ i, Nonempty (DV i ≃ₗ[A] DW (τ i)) := fun i => (hfg i (τ i)).mp (hτ i).symm
  
  have hIntV : DirectSum.IsInternal DV :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top DV).mpr ⟨hDV_ind, hDV_sup⟩
  have hIntWτ : DirectSum.IsInternal (fun i => DW (τ i)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (fun i => DW (τ i))).mpr
      ⟨hDW_ind.comp τ.injective, by rw [← hDW_sup]; exact τ.iSup_comp⟩
  let mid := DFinsupp.mapRange.linearEquiv (R := A) (fun i => (hiso i).some)
  exact ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap DV) hIntV).symm ≪≫ₗ mid ≪≫ₗ
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => DW (τ i))) hIntWτ⟩








private theorem exists_injective_of_repeated_fiber_embedding {C : Type*} {p q n r : ℕ} (hn : 0 < n)
    (f : Fin p → C) (g : Fin q → C) (d : Fin r → C)
    (σ : ((Fin n × Fin p) ⊕ Fin r) ≃ (Fin n × Fin q))
    (hσ : ∀ x, g (σ x).2 = Sum.elim (fun a : Fin n × Fin p => f a.2) d x) :
    ∃ φ : Fin p → Fin q, Function.Injective φ ∧ ∀ i, g (φ i) = f i := by
  classical
  
  have key : ∀ c : C, Fintype.card {i // f i = c} ≤ Fintype.card {j // g j = c} := by
    intro c
    
    have e : {x : (Fin n × Fin p) ⊕ Fin r // Sum.elim (fun a : Fin n × Fin p => f a.2) d x = c}
        ≃ {y : Fin n × Fin q // g y.2 = c} :=
      { toFun := fun x => ⟨σ x.1, by rw [hσ]; exact x.2⟩
        invFun := fun y => ⟨σ.symm y.1, by
          have h := hσ (σ.symm y.1); rw [σ.apply_symm_apply] at h; rw [← h]; exact y.2⟩
        left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
    
    have hinj : Fintype.card {a : Fin n × Fin p // f a.2 = c}
        ≤ Fintype.card {x : (Fin n × Fin p) ⊕ Fin r //
            Sum.elim (fun a : Fin n × Fin p => f a.2) d x = c} :=
      Fintype.card_le_of_injective (fun a => ⟨Sum.inl a.1, a.2⟩) (by
        intro a b h
        simp only [Subtype.mk.injEq, Sum.inl.injEq] at h
        exact Subtype.ext h)
    
    have eF : {a : Fin n × Fin p // f a.2 = c} ≃ Fin n × {i // f i = c} :=
      { toFun := fun a => (a.1.1, ⟨a.1.2, a.2⟩)
        invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        left_inv := fun a => by rcases a with ⟨⟨s, t⟩, h⟩; rfl
        right_inv := fun y => by rcases y with ⟨s, t, h⟩; rfl }
    have eG : {y : Fin n × Fin q // g y.2 = c} ≃ Fin n × {j // g j = c} :=
      { toFun := fun y => (y.1.1, ⟨y.1.2, y.2⟩)
        invFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
        left_inv := fun y => by rcases y with ⟨⟨s, t⟩, h⟩; rfl
        right_inv := fun z => by rcases z with ⟨s, t, h⟩; rfl }
    have hFF : Fintype.card {a : Fin n × Fin p // f a.2 = c} = n * Fintype.card {i // f i = c} := by
      rw [Fintype.card_congr eF, Fintype.card_prod, Fintype.card_fin]
    have hGG : Fintype.card {y : Fin n × Fin q // g y.2 = c} = n * Fintype.card {j // g j = c} := by
      rw [Fintype.card_congr eG, Fintype.card_prod, Fintype.card_fin]
    have hle : n * Fintype.card {i // f i = c} ≤ n * Fintype.card {j // g j = c} := by
      rw [← hFF, ← hGG, ← Fintype.card_congr e]; exact hinj
    exact Nat.le_of_mul_le_mul_left hle hn
  
  let emb : ∀ c : C, {i // f i = c} ↪ {j // g j = c} :=
    fun c => (Function.Embedding.nonempty_of_card_le (key c)).some
  let Φ : (Σ c, {i // f i = c}) ↪ (Σ c, {j // g j = c}) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl C) emb
  let ψ : Fin p ↪ Fin q :=
    (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans (Φ.trans (Equiv.sigmaFiberEquiv g).toEmbedding)
  exact ⟨ψ, ψ.injective, fun i => (emb (f i) ⟨i, rfl⟩).2⟩










private theorem exists_split_of_indexEmbedding {A V W : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    {p q : ℕ} (DV : Fin p → Submodule A V) (DW : Fin q → Submodule A W)
    (hIntV : DirectSum.IsInternal DV) (hIntW : DirectSum.IsInternal DW)
    {φ : Fin p → Fin q} (hφ : Function.Injective φ)
    (hiso : ∀ i, Nonempty ((DV i) ≃ₗ[A] (DW (φ i)))) :
    ∃ (ι : V →ₗ[A] W) (π : W →ₗ[A] V), π.comp ι = LinearMap.id := by
  classical
  let θ : ∀ i, (DV i) ≃ₗ[A] (DW (φ i)) := fun i => (hiso i).some
  let eV : V ≃ₗ[A] (⨁ i, (DV i)) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap DV) hIntV).symm
  let eW : (⨁ j, (DW j)) ≃ₗ[A] W := LinearEquiv.ofBijective (DirectSum.coeLinearMap DW) hIntW
  
  let ιS : (⨁ i, (DV i)) →ₗ[A] (⨁ j, (DW j)) :=
    DirectSum.toModule A (Fin p) _ (fun i =>
      (DirectSum.lof A (Fin q) (fun j => (DW j)) (φ i)).comp (θ i).toLinearMap)
  
  let πS : (⨁ j, (DW j)) →ₗ[A] (⨁ i, (DV i)) :=
    ∑ i : Fin p, (DirectSum.lof A (Fin p) (fun i => (DV i)) i).comp
      (((θ i).symm.toLinearMap).comp (DirectSum.component A (Fin q) (fun j => (DW j)) (φ i)))
  have hsplit : πS.comp ιS = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i₀
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    
    have hι : ιS (DirectSum.lof A (Fin p) (fun i => (DV i)) i₀ x)
        = DirectSum.lof A (Fin q) (fun j => (DW j)) (φ i₀) (θ i₀ x) := by
      simp only [ιS, DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hι]
    simp only [πS, LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Finset.sum_eq_single i₀]
    · rw [DirectSum.component.lof_self]
      simp only [LinearEquiv.symm_apply_apply]
    · intro b _ hb
      rw [DirectSum.component.of, dif_neg (fun h => hb (hφ h.symm))]
      simp only [map_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  refine ⟨(eW : (⨁ j, (DW j)) →ₗ[A] W).comp (ιS.comp (eV : V →ₗ[A] (⨁ i, (DV i)))),
      (eV.symm : (⨁ i, (DV i)) →ₗ[A] V).comp (πS.comp (eW.symm : W →ₗ[A] (⨁ j, (DW j)))), ?_⟩
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe]
  rw [eW.symm_apply_apply]
  have he : πS (ιS (eV v)) = eV v := LinearMap.congr_fun hsplit (eV v)
  rw [he, eV.symm_apply_apply]












/-- The displayed split-map existence statement follows from the same existence statement under the given hypotheses. -/
@[source_ref "Chapter3/Problem3.8.4/Derived6" (role := supporting)]
theorem exists_split_of_exists_split (k A V W : Type*) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    {n : ℕ} (hn : 0 < n)
    (h : ∃ (i : (Fin n → V) →ₗ[A] (Fin n → W)) (p : (Fin n → W) →ₗ[A] (Fin n → V)),
           p.comp i = LinearMap.id) :
    ∃ (i : V →ₗ[A] W) (p : W →ₗ[A] V), p.comp i = LinearMap.id := by
  classical
  obtain ⟨imap, pmap, hpi⟩ := h
  have hi_inj : Function.Injective imap :=
    Function.LeftInverse.injective (g := pmap) (fun x => LinearMap.congr_fun hpi x)
  
  set R : Submodule A (Fin n → W) := LinearMap.range imap with hR
  set iRange : (Fin n → V) ≃ₗ[A] R := LinearEquiv.ofInjective imap hi_inj with hiRange
  set f0 : (Fin n → W) →ₗ[A] R := iRange.toLinearMap.comp pmap with hf0def
  have hf0 : ∀ x : R, f0 x = x := by
    intro x
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp x.2
    apply Subtype.ext
    have hpv : pmap (x : Fin n → W) = v := by rw [← hv]; exact LinearMap.congr_fun hpi v
    have hfx : f0 (x : Fin n → W) = iRange v := by
      simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_coe, hpv]
    rw [hfx]
    change (imap v : Fin n → W) = (x : Fin n → W)
    exact hv
  have hCompl : IsCompl R (LinearMap.ker f0) := LinearMap.isCompl_of_proj hf0
  set Y' : Submodule A (Fin n → W) := LinearMap.ker f0 with hY'
  
  haveI : FiniteDimensional k (Y' : Submodule A (Fin n → W)) := by
    have hsub : Function.Injective ⇑(Y'.subtype.restrictScalars k) := Y'.injective_subtype
    exact FiniteDimensional.of_injective (Y'.subtype.restrictScalars k) hsub
  
  obtain ⟨p, DV, hDV_indec, hDV_sup, hDV_ind⟩ := RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family k A V
  obtain ⟨q, DW, hDW_indec, hDW_sup, hDW_ind⟩ := RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family k A W
  obtain ⟨r, DY, hDY_indec, hDY_sup, hDY_ind⟩ :=
    RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family k A (Y' : Submodule A (Fin n → W))
  have hDV_ne : ∀ i, DV i ≠ ⊥ := fun i => Submodule.nontrivial_iff_ne_bot.mp (hDV_indec i).1
  have hDW_ne : ∀ j, DW j ≠ ⊥ := fun j => Submodule.nontrivial_iff_ne_bot.mp (hDW_indec j).1
  have hDY_ne : ∀ j, DY j ≠ ⊥ := fun j => Submodule.nontrivial_iff_ne_bot.mp (hDY_indec j).1
  
  set sgV : Fin n → (V →ₗ[A] (Fin n → V)) :=
    fun c => LinearMap.single A (fun _ : Fin n => V) c with hsgV
  set sgW : Fin n → (W →ₗ[A] (Fin n → W)) :=
    fun c => LinearMap.single A (fun _ : Fin n => W) c with hsgW
  obtain ⟨hPV_indec, hPV_ne, hPV_sup, hPV_ind⟩ :=
    finFunction_internalFamily (n := n) DV hDV_indec hDV_ne hDV_sup hDV_ind
  obtain ⟨hPW_indec, hPW_ne, hPW_sup, hPW_ind⟩ :=
    finFunction_internalFamily (n := n) DW hDW_indec hDW_ne hDW_sup hDW_ind
  
  set D' : Fin n × Fin q → Submodule A (Fin n → W) := fun cj => (DW cj.2).map (sgW cj.1) with hD'
  
  set EL : Fin n × Fin p → Submodule A (Fin n → W) :=
    fun ci => ((DV ci.2).map (sgV ci.1)).map imap with hEL
  set ER : Fin r → Submodule A (Fin n → W) := fun jr => (DY jr).map Y'.subtype with hER
  let E : ((Fin n × Fin p) ⊕ Fin r) → Submodule A (Fin n → W) := Sum.elim EL ER
  have hEL_sup : iSup EL = R := by
    simp only [EL]; rw [← Submodule.map_iSup, hPV_sup, Submodule.map_top, hR]
  have hER_sup : iSup ER = Y' := by
    simp only [ER]; rw [← Submodule.map_iSup, hDY_sup, Submodule.map_top, Submodule.range_subtype]
  have hEL_indec : ∀ ci, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (EL ci) := fun ci =>
    (hPV_indec ci).map (Submodule.equivMapOfInjective imap hi_inj _)
  have hER_indec : ∀ jr, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (ER jr) := fun jr =>
    (hDY_indec jr).map (Submodule.equivMapOfInjective Y'.subtype Y'.injective_subtype _)
  have hEL_ne : ∀ ci, EL ci ≠ ⊥ := fun ci =>
    Submodule.nontrivial_iff_ne_bot.mp (hEL_indec ci).1
  have hER_ne : ∀ jr, ER jr ≠ ⊥ := fun jr =>
    Submodule.nontrivial_iff_ne_bot.mp (hER_indec jr).1
  have hEL_ind : iSupIndep EL := LinearMap.iSupIndep_map imap hi_inj hPV_ind
  have hER_ind : iSupIndep ER := LinearMap.iSupIndep_map Y'.subtype Y'.injective_subtype hDY_ind
  
  have hE_indec : ∀ x, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (E x) := by
    rintro (ci | jr)
    · exact hEL_indec ci
    · exact hER_indec jr
  have hE_ne : ∀ x, E x ≠ ⊥ := by
    rintro (ci | jr)
    · exact hEL_ne ci
    · exact hER_ne jr
  have hE_sup : iSup E = ⊤ := by
    change iSup (Sum.elim EL ER) = ⊤
    rw [iSup_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hEL_sup, hER_sup, hCompl.sup_eq_top]
  have hE_ind : iSupIndep E :=
    iSupIndep_sum_of_families EL ER (by rw [hEL_sup, hER_sup]; exact hCompl.disjoint) hEL_ind hER_ind
  
  obtain ⟨σ, hks⟩ := exists_indexEquiv k A (Fin n → W) E D'
    hE_indec hPW_indec hE_ne hPW_ne hE_sup hE_ind hPW_sup hPW_ind
  
  have isoV : ∀ ci : Fin n × Fin p, (DV ci.2) ≃ₗ[A] EL ci := fun ci =>
    (Submodule.equivMapOfInjective (sgV ci.1) (single_injective _) (DV ci.2)).trans
      (Submodule.equivMapOfInjective imap hi_inj _)
  have isoW : ∀ cj : Fin n × Fin q, (DW cj.2) ≃ₗ[A] D' cj := fun cj =>
    Submodule.equivMapOfInjective (sgW cj.1) (single_injective _) (DW cj.2)
  have isoY : ∀ jr : Fin r, (DY jr) ≃ₗ[A] ER jr := fun jr =>
    Submodule.equivMapOfInjective Y'.subtype Y'.injective_subtype (DY jr)
  
  let rel : (Fin p ⊕ Fin q ⊕ Fin r) → (Fin p ⊕ Fin q ⊕ Fin r) → Prop := fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl i' => Nonempty (DV i ≃ₗ[A] DV i')
    | Sum.inl i, Sum.inr (Sum.inl j) => Nonempty (DV i ≃ₗ[A] DW j)
    | Sum.inl i, Sum.inr (Sum.inr jr) => Nonempty (DV i ≃ₗ[A] DY jr)
    | Sum.inr (Sum.inl j), Sum.inl i => Nonempty (DW j ≃ₗ[A] DV i)
    | Sum.inr (Sum.inl j), Sum.inr (Sum.inl j') => Nonempty (DW j ≃ₗ[A] DW j')
    | Sum.inr (Sum.inl j), Sum.inr (Sum.inr jr) => Nonempty (DW j ≃ₗ[A] DY jr)
    | Sum.inr (Sum.inr jr), Sum.inl i => Nonempty (DY jr ≃ₗ[A] DV i)
    | Sum.inr (Sum.inr jr), Sum.inr (Sum.inl j) => Nonempty (DY jr ≃ₗ[A] DW j)
    | Sum.inr (Sum.inr jr), Sum.inr (Sum.inr jr') => Nonempty (DY jr ≃ₗ[A] DY jr')
  have hrefl : ∀ x, rel x x := by rintro (i | j | jr) <;> exact ⟨LinearEquiv.refl A _⟩
  have hsymm : ∀ {x y}, rel x y → rel y x := by
    rintro (i | j | jr) (i' | j' | jr') ⟨φ⟩ <;> exact ⟨φ.symm⟩
  have htrans : ∀ {x y z}, rel x y → rel y z → rel x z := by
    rintro (i | j | jr) (i' | j' | jr') (i'' | j'' | jr'') ⟨φ⟩ ⟨ψ⟩ <;> exact ⟨φ.trans ψ⟩
  letI S : Setoid (Fin p ⊕ Fin q ⊕ Fin r) := ⟨rel, hrefl, hsymm, htrans⟩
  let fC : Fin p → Quotient S := fun i => ⟦Sum.inl i⟧
  let gC : Fin q → Quotient S := fun j => ⟦Sum.inr (Sum.inl j)⟧
  let dC : Fin r → Quotient S := fun jr => ⟦Sum.inr (Sum.inr jr)⟧
  have hfg_vw : ∀ i j, fC i = gC j ↔ Nonempty (DV i ≃ₗ[A] DW j) := fun i j => Quotient.eq
  have hfg_yw : ∀ jr j, dC jr = gC j ↔ Nonempty (DY jr ≃ₗ[A] DW j) := fun jr j => Quotient.eq
  
  have hσ : ∀ x, gC (σ x).2 = Sum.elim (fun a : Fin n × Fin p => fC a.2) dC x := by
    intro x
    obtain ⟨χ⟩ := hks x
    rcases x with ci | jr
    · change gC (σ (Sum.inl ci)).2 = fC ci.2
      rw [eq_comm, hfg_vw ci.2 (σ (Sum.inl ci)).2]
      exact ⟨(isoV ci).trans (χ.trans (isoW (σ (Sum.inl ci))).symm)⟩
    · change gC (σ (Sum.inr jr)).2 = dC jr
      rw [eq_comm, hfg_yw jr (σ (Sum.inr jr)).2]
      exact ⟨(isoY jr).trans (χ.trans (isoW (σ (Sum.inr jr))).symm)⟩
  obtain ⟨φ, hφ_inj, hφ_lab⟩ := exists_injective_of_repeated_fiber_embedding hn fC gC dC σ hσ
  have hiso' : ∀ i, Nonempty (DV i ≃ₗ[A] DW (φ i)) := fun i =>
    (hfg_vw i (φ i)).mp (hφ_lab i).symm
  
  have hIntV : DirectSum.IsInternal DV :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top DV).mpr ⟨hDV_ind, hDV_sup⟩
  have hIntW : DirectSum.IsInternal DW :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top DW).mpr ⟨hDW_ind, hDW_sup⟩
  exact exists_split_of_indexEmbedding DV DW hIntV hIntW hφ_inj hiso'

end RepresentationTheory.Algebra.Module.EquivalenceTransfers
