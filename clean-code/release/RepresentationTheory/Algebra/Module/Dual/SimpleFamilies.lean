/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Trace
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity

namespace RepresentationTheory.Algebra.Module.Dual.SimpleFamilies

open _root_.Module in
/-- A dual element of an algebra associated with a finite free module over the base ring. -/
@[nolint unusedArguments]
noncomputable def moduleDualElement (k : Type*) (A : Type*) (V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Free k V] [Module.Finite k V] :
    Dual k A :=
  (LinearMap.trace k V).comp (Algebra.lsmul k k V : A →ₐ[k] End k V).toLinearMap

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := supporting)] moduleDualElement

open _root_.Module in
/-- The dual elements associated with a finite family of pairwise nonisomorphic simple modules are linearly independent. -/
theorem linearIndependent_moduleDualElement (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Finite ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => moduleDualElement k A (V i)) := by
  classical
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hga : ∀ a : A, ∑ j, g j * moduleDualElement k A (V j) a = 0 := by
    intro a
    have := LinearMap.congr_fun hg a
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    exact this
  have hsurj :=
    RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.family_algebra_smul_surjective
      k A ι V h_noniso
  haveI : Nontrivial (V i) := IsSimpleModule.nontrivial A (V i)
  let b := Module.Free.chooseBasis k (V i)
  have hne_idx : Nonempty (Module.Free.ChooseBasisIndex k (V i)) := by
    rw [← not_isEmpty_iff]
    intro h
    have : finrank k (V i) = 0 := by simp [finrank_eq_card_chooseBasisIndex, Fintype.card_eq_zero]
    have : 0 < finrank k (V i) := Module.finrank_pos
    omega
  let idx := hne_idx.some
  let target : ∀ j, Module.End k (V j) := fun j =>
    if h : j = i then h ▸ (dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx)) else 0
  obtain ⟨a, ha⟩ := hsurj target
  have h0 := hga a
  have hρ : ∀ j, (Algebra.lsmul k k (V j) : A →ₐ[k] Module.End k (V j)) a = target j := by
    intro j; exact congr_fun ha j
  simp only [moduleDualElement, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h0
  have htarget_ne : ∀ j, j ≠ i → target j = 0 := by
    intro j hj; simp [target, hj]
  have htarget_eq : target i = dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx) := by
    simp [target]
  have htr_target_i : LinearMap.trace k (V i) (target i) = 1 := by
    rw [htarget_eq, LinearMap.trace_eq_contract_apply]
    simp [contractLeft, Basis.coord]
  have htr_ne : ∀ j, j ≠ i → LinearMap.trace k (V j) (target j) = 0 := by
    intro j hj; rw [htarget_ne j hj, map_zero]
  have hsum : ∑ j, g j * LinearMap.trace k (V j) (target j) =
      g i * LinearMap.trace k (V i) (target i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_eq_zero (fun j hj => by rw [htr_ne j (Finset.ne_of_mem_erase hj), mul_zero])]
    ring
  have h0' : ∑ j, g j * LinearMap.trace k (V j) (target j) = 0 := by
    have : ∀ j, LinearMap.trace k (V j) ((Algebra.lsmul k k (V j) : A →ₐ[k] _) a) =
        LinearMap.trace k (V j) (target j) := fun j => congrArg _ (hρ j)
    simp only [this] at h0; exact h0
  rw [hsum, htr_target_i, mul_one] at h0'
  exact h0'

attribute [source_ref "Chapter3/Theorem3.6.2" (role := supporting)]
  linearIndependent_moduleDualElement
attribute [source_ref "Chapter3/Theorem3.7.1/Derived7" (role := primary)]
  linearIndependent_moduleDualElement

section helpers

open _root_.Module

private lemma tracial_of_end_eq_scalar_trace {k V : Type*}
    [Field k] [AddCommGroup V] [Module k V] [Free k V] [Module.Finite k V]
    (g : End k V →ₗ[k] k) (hg : ∀ x y : End k V, g (x * y) = g (y * x)) :
    ∃ c : k, g = c • LinearMap.trace k V := by
  classical
  let b := Module.Free.chooseBasis k V
  let ι := Module.Free.ChooseBasisIndex k V
  have end_mul : ∀ (i j p q : ι), b.end (i, j) * b.end (p, q) =
      if j = p then b.end (i, q) else 0 := by
    intro i j p q
    apply b.ext; intro m
    change b.end (i, j) (b.end (p, q) (b m)) = _
    simp only [Basis.end_apply_apply]
    split_ifs <;> simp_all [Basis.end_apply_apply]
  have end_trace : ∀ (i j : ι), LinearMap.trace k V (b.end (i, j)) =
      if i = j then 1 else 0 := by
    intro i j
    rw [Basis.end_apply, Matrix.trace_toLin_eq, Matrix.stdBasis_eq_single]
    split_ifs with hij
    · subst hij; simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne _ _ _ hij]
  by_cases hι : IsEmpty ι
  · refine ⟨0, ?_⟩
    apply b.end.ext; intro ⟨i, _⟩; exact hι.elim i
  · rw [not_isEmpty_iff] at hι
    obtain ⟨i₀⟩ := hι
    refine ⟨g (b.end (i₀, i₀)), ?_⟩
    apply b.end.ext; intro ⟨i, j⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have hdiag : g (b.end (i, i)) = g (b.end (i₀, i₀)) := by
        by_cases hp : i = i₀
        · exact hp ▸ rfl
        · have h1 : b.end (i, i₀) * b.end (i₀, i) = b.end (i, i) := by
            rw [end_mul]; simp
          have h2 : b.end (i₀, i) * b.end (i, i₀) = b.end (i₀, i₀) := by
            rw [end_mul]; simp
          rw [← h1, ← h2]; exact hg _ _
      rw [hdiag, end_trace, if_pos rfl, mul_one]
    · have h1 : b.end (i, j) * b.end (j, j) = b.end (i, j) := by
        rw [end_mul]; simp
      have h2 : b.end (j, j) * b.end (i, j) = 0 := by
        rw [end_mul]; simp [Ne.symm hij]
      have : g (b.end (i, j)) = 0 := by
        rw [← h1]; rw [hg]; rw [h2]; exact map_zero g
      rw [this, end_trace, if_neg hij, mul_zero]

private lemma rep_map_injective_of_semisimple.{v} {k : Type*} {A : Type v}
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*}
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_complete : ∀ (W : Type v) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    Function.Injective
      (fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] End k (V i)) a :
        A → ∀ i, End k (V i)) := by
  intro a₁ a₂ h
  by_contra hne
  have hb : a₁ - a₂ ≠ 0 := sub_ne_zero.mpr hne
  set b := a₁ - a₂ with hb_def
  have hb_act : ∀ i (v : V i), b • v = 0 := by
    intro i v
    have hi := congr_fun h i
    have hv := LinearMap.congr_fun hi v
    change (a₁ - a₂) • v = 0
    rw [sub_smul]
    exact sub_eq_zero.mpr hv
  suffices hb_zero : b = 0 from absurd hb_zero hb
  have hb_jac : b ∈ Ring.jacobson A := by
    change b ∈ Module.jacobson A A
    rw [Module.jacobson, Submodule.mem_sInf]
    intro m hm
    haveI : IsSimpleModule A (A ⧸ m) := isSimpleModule_iff_isCoatom.mpr hm
    have ⟨j, ⟨φ⟩⟩ := h_complete (A ⧸ m)
    rw [← Submodule.Quotient.mk_eq_zero]
    apply φ.injective
    simp only [map_zero]
    have hmk : (Submodule.Quotient.mk (p := m) b : A ⧸ m) =
        b • (Submodule.Quotient.mk (p := m) (1 : A) : A ⧸ m) := by
      change m.mkQ b = b • m.mkQ 1
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hmk, map_smul]
    exact hb_act j _
  rwa [IsSemisimpleRing.jacobson_eq_bot, Submodule.mem_bot] at hb_jac

end helpers

open _root_.Module in
/-- A linear functional invariant under exchanging the factors of a product belongs to the span of the dual elements associated with a complete family of pairwise nonisomorphic simple modules. -/
@[source_ref "Chapter3/Theorem3.6.2" (role := supporting),
  source_ref "Chapter3/Theorem3.6.2/Derived11" (role := supporting)]
theorem mem_span_moduleDualElement_of_commutes_mul.{v} (k : Type*) (A : Type v)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*} [Finite ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type v) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    ∀ f : Dual k A, (∀ a b : A, f (a * b) = f (b * a)) →
      f ∈ Submodule.span k (Set.range (fun i => moduleDualElement k A (V i))) := by
  intro f hf
  classical
  letI := Fintype.ofFinite ι
  have hρ_surj :=
    RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.family_algebra_smul_surjective
      k A ι V h_noniso
  have hρ_inj := rep_map_injective_of_semisimple V h_complete
  let ρ : A →ₗ[k] ∀ i, Module.End k (V i) :=
    { toFun := fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] _) a,
      map_add' := fun a b => funext fun i => map_add _ a b,
      map_smul' := fun c a => funext fun i => map_smul _ c a }
  let ρ_equiv : A ≃ₗ[k] (∀ i, Module.End k (V i)) := LinearEquiv.ofBijective ρ ⟨hρ_inj, hρ_surj⟩
  let g : (∀ i, Module.End k (V i)) →ₗ[k] k := f.comp ρ_equiv.symm.toLinearMap
  have hρ_mul : ∀ a b : A, ρ (a * b) = ρ a * ρ b :=
    fun a b => funext fun i => map_mul (Algebra.lsmul k k (V i) : A →ₐ[k] _) a b
  have hρ_symm_mul : ∀ x y, ρ_equiv.symm (x * y) = ρ_equiv.symm x * ρ_equiv.symm y := by
    intro x y
    apply ρ_equiv.injective
    rw [LinearEquiv.apply_symm_apply]
    change x * y = ρ_equiv (ρ_equiv.symm x * ρ_equiv.symm y)
    change x * y = ρ (ρ_equiv.symm x * ρ_equiv.symm y)
    rw [hρ_mul]
    change x * y = ρ_equiv (ρ_equiv.symm x) * ρ_equiv (ρ_equiv.symm y)
    simp [LinearEquiv.apply_symm_apply]
  have hg_tracial : ∀ (x y : ∀ i, Module.End k (V i)), g (x * y) = g (y * x) := by
    intro x y
    change f (ρ_equiv.symm (x * y)) = f (ρ_equiv.symm (y * x))
    rw [hρ_symm_mul, hρ_symm_mul, hf]
  let g_comp : ∀ i, Module.End k (V i) →ₗ[k] k := fun i =>
    g.comp (LinearMap.single (R := k) (fun i => Module.End k (V i)) i)
  have hg_comp_tr : ∀ i (x y : Module.End k (V i)),
      g_comp i (x * y) = g_comp i (y * x) := by
    intro i x y
    change g (Pi.single i (x * y)) = g (Pi.single i (y * x))
    have hpi_mul : ∀ (a b : Module.End k (V i)),
        (Pi.single i a : ∀ j, Module.End k (V j)) * Pi.single i b = Pi.single i (a * b) := by
      intro a b; ext j
      simp only [Pi.mul_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [← hpi_mul, ← hpi_mul, hg_tracial]
  choose c hc using fun i => tracial_of_end_eq_scalar_trace (g_comp i) (hg_comp_tr i)
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨c, ?_⟩
  ext a
  have hfa : f a = g (ρ a) := by
    change f a = f (ρ_equiv.symm (ρ_equiv a))
    simp
  have hg_sum : ∀ (e : ∀ i, Module.End k (V i)), g e = ∑ i, g_comp i (e i) := by
    intro e
    have : e = ∑ i : ι, Pi.single i (e i) := by
      ext j
      simp [Finset.sum_apply]
    conv_lhs => rw [this]
    simp [map_sum, g_comp]
  rw [hfa, hg_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [moduleDualElement, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [hc i]
  rfl

attribute [source_ref "Chapter4/Theorem4.2.1/Derived2" (role := supporting)]
  mem_span_moduleDualElement_of_commutes_mul

end RepresentationTheory.Algebra.Module.Dual.SimpleFamilies
