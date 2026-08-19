/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct

universe u v

namespace RepresentationTheory.CentralizerDecomposition

/-- A Noetherian semisimple module is linearly equivalent to the finitely supported sum of its isotypic components. -/
noncomputable def isotypicComponentsDFinsuppEquiv
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] [IsNoetherian R M]
    [DecidableEq (isotypicComponents R M)] :
    (Π₀ c : isotypicComponents R M, (c.1 : Submodule R M)) ≃ₗ[R] M :=
  let ind : iSupIndep fun c : isotypicComponents R M =>
      (c.1 : Submodule R M) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  have iSup_top :
      (⨆ c : isotypicComponents R M, (c.1 : Submodule R M)) = ⊤ := by
    rw [← sSup_eq_iSup']
    exact sSup_isotypicComponents R M
  ind.linearEquiv iSup_top

/-- For a finite simple module over an algebraically closed field, scalars are linearly equivalent to module endomorphisms. -/
noncomputable def scalarEquivModuleEnd
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V] :
    k ≃ₗ[k] (V →ₗ[A] V) :=
  LinearEquiv.ofBijective (Algebra.linearMap k (V →ₗ[A] V))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

/-- The scalar corresponding to a module endomorphism acts on every vector as that endomorphism. -/
lemma scalarEquivModuleEnd_symm_smul
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (φ : V →ₗ[A] V) (v : V) :
    (scalarEquivModuleEnd k A V).symm φ • v = φ v := by
  have hφ : scalarEquivModuleEnd k A V
      ((scalarEquivModuleEnd k A V).symm φ) = φ :=
    (scalarEquivModuleEnd k A V).apply_symm_apply φ

  have hφ' : (scalarEquivModuleEnd k A V).symm φ • (1 : V →ₗ[A] V) = φ := by
    have hrw : Algebra.linearMap k (V →ₗ[A] V)
        ((scalarEquivModuleEnd k A V).symm φ) = φ := hφ
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one] at hrw
    exact hrw
  have := LinearMap.congr_fun hφ' v
  simpa [LinearMap.smul_apply, Module.End.one_apply] using this

/-- An equivalence of codomains induces a linear equivalence between the corresponding spaces of module maps. -/
noncomputable def linearMapCodomainEquiv
    (k : Type*) [CommSemiring k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : M ≃ₗ[A] N) :
    (V →ₗ[A] M) ≃ₗ[k] (V →ₗ[A] N) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp
  map_smul' c f := by
    ext v
    simp [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- Module maps into a family of copies of a module are equivalent to families of module endomorphisms. -/
noncomputable def linearMapPiEquiv
    (k : Type*) [CommSemiring k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    (ι : Type*) :
    (V →ₗ[A] (ι → V)) ≃ₗ[k] (ι → V →ₗ[A] V) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext v i; rfl
  right_inv g := by funext i; ext v; rfl
  map_add' f g := by funext i; ext v; simp
  map_smul' c f := by funext i; ext v; simp

/-- Evaluation gives an equivalence from a simple module tensored with its map space onto an isotypic module. -/
noncomputable def tensorProductLinearMapEquiv
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M V) :
    V ⊗[k] (V →ₗ[A] M) ≃ₗ[k] M :=
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  let n : ℕ := h.linearEquiv_fun.choose
  let e : M ≃ₗ[A] (Fin n → V) := h.linearEquiv_fun.choose_spec.some

  let e1 : (V →ₗ[A] M) ≃ₗ[k] (V →ₗ[A] (Fin n → V)) :=
    linearMapCodomainEquiv k A V e
  let e2 : (V →ₗ[A] (Fin n → V)) ≃ₗ[k] (Fin n → V →ₗ[A] V) :=
    linearMapPiEquiv k A V (Fin n)
  let e3 : (Fin n → V →ₗ[A] V) ≃ₗ[k] (Fin n → k) :=
    LinearEquiv.piCongrRight (fun _ => (scalarEquivModuleEnd k A V).symm)
  let e4 : V ⊗[k] (Fin n → k) ≃ₗ[k] (Fin n → V) :=
    TensorProduct.piScalarRight k k V (Fin n)
  let e5 : (Fin n → V) ≃ₗ[k] M := e.symm.restrictScalars k
  (TensorProduct.congr (LinearEquiv.refl k V)
    (e1.trans (e2.trans e3))).trans (e4.trans e5)

/-- The tensor-product evaluation equivalence sends a pure tensor to evaluation of its linear-map factor. -/
lemma tensorProductLinearMapEquiv_apply_tmul
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M V) (v : V) (f : V →ₗ[A] M) :
    tensorProductLinearMapEquiv k A V M h (v ⊗ₜ[k] f) = f v := by
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V

  set n : ℕ := h.linearEquiv_fun.choose
  set e : M ≃ₗ[A] (Fin n → V) := h.linearEquiv_fun.choose_spec.some

  have step1 : tensorProductLinearMapEquiv k A V M h (v ⊗ₜ[k] f)
      = e.symm (fun j =>
          (scalarEquivModuleEnd k A V).symm
            ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v) := by
    rfl
  rw [step1]

  have hv : ∀ j, (scalarEquivModuleEnd k A V).symm
      ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v = (e (f v)) j := by
    intro j
    rw [scalarEquivModuleEnd_symm_smul]
    rfl
  have hfun : (fun j => (scalarEquivModuleEnd k A V).symm
      ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v) = e (f v) := by
    funext j; exact hv j
  rw [hfun]
  exact e.symm_apply_apply (f v)

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- A faithful semisimple subalgebra of endomorphisms equals its double centralizer. -/
@[source_ref "Chapter5/Theorem5.18.1" (role := supporting)]
theorem centralizer_centralizer_eq
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    Subalgebra.centralizer k
      (Subalgebra.centralizer k (A : Set (Module.End k E)) :
        Set (Module.End k E)) = A := by
  apply le_antisymm
  ·

    intro f hf
    rw [Subalgebra.mem_centralizer_iff] at hf

    haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule

    have hf_comm : ∀ (φ : Module.End A E) (e : E),
        f (φ e) = φ (f e) := by
      intro φ e
      have hφ_mem : (φ.restrictScalars k : Module.End k E) ∈
          Subalgebra.centralizer k
            (A : Set (Module.End k E)) := by
        rw [Subalgebra.mem_centralizer_iff]
        intro a ha
        ext e'
        change a (φ.restrictScalars k e') =
          φ.restrictScalars k (a e')
        change a (φ e') = φ (a e')
        exact (φ.map_smul ⟨a, ha⟩ e').symm
      have h := hf _ hφ_mem
      exact (LinearMap.congr_fun h e).symm

    let f' : Module.End (Module.End A E) E :=
      { f with
        map_smul' := fun φ e => by
          simp only [Module.End.smul_def, RingHom.id_apply]
          exact hf_comm φ e }

    have ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := E)

    obtain ⟨a, ha⟩ := jacobson_density f' s

    have heq : f = (a : Module.End k E) := by
      ext e
      induction hs.ge (Submodule.mem_top (x := e)) using
          Submodule.span_induction with
      | mem m hm =>
        have h := ha m hm

        have : f' m = f m := rfl
        rw [this] at h
        exact h
      | zero => simp [map_zero]
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | smul c x _ hx =>
        simp only [map_smul]
        rw [hx]
    rw [heq]
    exact a.2
  ·
    exact Subalgebra.le_centralizer_centralizer k

/-- The centralizer of a faithful semisimple algebra action on a finite-dimensional space is semisimple. -/
@[source_ref "Chapter5/Theorem5.18.1" (role := supporting)]
theorem isSemisimpleRing_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    IsSemisimpleRing
      (Subalgebra.centralizer k
        (A : Set (Module.End k E))) := by

  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule

  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E

  haveI : IsSemisimpleRing (Module.End A E) := IsSemisimpleRing.moduleEnd A E

  let toEnd : (Subalgebra.centralizer k (A : Set (Module.End k E))) →+* Module.End A E :=
    { toFun := fun ⟨f, hf⟩ =>
        { f with
          map_smul' := fun (a : A) e => by
            rw [Subalgebra.mem_centralizer_iff] at hf
            have h := hf a.1 a.2
            exact (LinearMap.congr_fun h e).symm }
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let fromEnd : Module.End A E →+* (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    { toFun := fun g =>
        ⟨g.restrictScalars k, by
          rw [Subalgebra.mem_centralizer_iff]
          intro a ha
          ext e
          have := g.map_smul (⟨a, ha⟩ : A) e
          exact this.symm⟩
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let e : (Subalgebra.centralizer k (A : Set (Module.End k E))) ≃+* Module.End A E :=
    RingEquiv.ofRingHom toEnd fromEnd (by ext; rfl) (by ext; rfl)
  exact e.symm.isSemisimpleRing

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

/--
The finite module with its faithful semisimple algebra action is linearly equivalent to a direct
sum of tensor products.
-/
theorem exists_directSum_tensorProduct_equiv
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Type v) (W : ι → Type u)
      (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module k (V i))
      (_ : ∀ i, Module A (V i))
      (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i, AddCommGroup (W i))
      (_ : ∀ i, Module k (W i)),
      Nonempty
        (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] W i)) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E

  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A E

  exact ⟨Fin n, inferInstance, inferInstance,
    fun i => ↥(S i), fun _ => k,
    inferInstance, inferInstance,
    inferInstance, hS,
    inferInstance, inferInstance,
    ⟨(e.restrictScalars k).trans
      (DFinsupp.mapRange.linearEquiv (fun i => (TensorProduct.rid k ↥(S i)).symm))⟩⟩

/--
The ring homomorphism sending a centralizing endomorphism to its module-linear action on the
ambient module.
-/
noncomputable def centralizerToModuleEnd
    (A : Subalgebra k (Module.End k E)) :
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) →+*
      Module.End A E where
  toFun b :=
    { toFun := b.val
      map_add' := b.val.map_add
      map_smul' := fun a e => by
        have hb := b.property
        rw [Subalgebra.mem_centralizer_iff] at hb
        have h := hb a.val a.property

        have happ := LinearMap.congr_fun h e

        exact happ.symm }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

set_option synthInstance.maxHeartbeats 400000 in

/-- The centralizer-module structure on linear maps from an algebra module into the ambient module. -/
noncomputable instance centralizerModuleHom
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) where
  smul b f := (centralizerToModuleEnd k E A b).comp f
  one_smul f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A 1) (f v) = f v
    rw [map_one]; rfl
  mul_smul b₁ b₂ f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A (b₁ * b₂)) (f v) =
      (centralizerToModuleEnd k E A b₁)
        ((centralizerToModuleEnd k E A b₂) (f v))
    rw [map_mul]; rfl
  smul_zero b := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A b) ((0 : V →ₗ[A] E) v) = 0
    simp
  smul_add b f g := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A b) ((f + g) v) =
      (centralizerToModuleEnd k E A b) (f v) + (centralizerToModuleEnd k E A b) (g v)
    simp
  add_smul b₁ b₂ f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A (b₁ + b₂)) (f v) =
      (centralizerToModuleEnd k E A b₁) (f v) + (centralizerToModuleEnd k E A b₂) (f v)
    rw [map_add]; rfl
  zero_smul f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToModuleEnd k E A 0) (f v) = 0
    rw [map_zero]; rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 320000 in

/-- Centralizer scalar multiplication on the linear-map space commutes with scalar multiplication by the base field. -/
instance centralizerSMulCommClass
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    SMulCommClass (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) k
      (V →ₗ[A] E) where
  smul_comm b c f := by
    refine LinearMap.ext fun v => ?_

    change b.val ((c • f) v) = c • b.val (f v)
    rw [LinearMap.smul_apply, map_smul]

set_option synthInstance.maxHeartbeats 400000 in

/--
The centralizer acts by base-field-linear endomorphisms on the space of module maps into the
ambient module.
-/
noncomputable def centralizerActionMonoidHom
    (A : Subalgebra k (Module.End k E))
    (V : Type*) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) →*
      Module.End k (V →ₗ[A] E) where
  toFun b :=
    { toFun := fun l => (centralizerToModuleEnd k E A b).comp l
      map_add' := fun l₁ l₂ => by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
      map_smul' := fun c l => by
        ext v
        simp only [LinearMap.smul_apply, RingHom.id_apply,
          LinearMap.comp_apply, LinearMap.map_smul_of_tower] }
  map_one' := by
    ext l v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.End.one_apply]
    change (centralizerToModuleEnd k E A 1) (l v) = l v
    rw [map_one]; rfl
  map_mul' b₁ b₂ := by
    ext l v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.End.mul_apply]
    change (centralizerToModuleEnd k E A (b₁ * b₂)) (l v) = _
    rw [map_mul]; rfl

omit [Module.Finite k E] in

/-- The centralizer action on a module map is pointwise application of the centralizing endomorphism. -/
@[simp]
theorem centralizerActionMonoidHom_apply
    (A : Subalgebra k (Module.End k E))
    (V : Type*) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V]
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
    (l : V →ₗ[A] E) (v : V) :
    centralizerActionMonoidHom k E A V b l v = b.val (l v) := rfl

/-- The ring structure on the carrier of a subalgebra of linear endomorphisms. -/
noncomputable local instance (priority := high) subalgebraCarrierRing
    (A : Subalgebra k (Module.End k E)) : Ring A := A.toRing

/-- The centralizer-module structure on maps from a submodule into the ambient module. -/
noncomputable local instance (priority := high) centralizerModuleSubmoduleHom
    (A : Subalgebra k (Module.End k E)) (V : Submodule A E) :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥V →ₗ[A] E) := centralizerModuleHom k E (A := A) (V := ↥V)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
omit [Module.Finite k E] in

/-- The range of a map from a simple submodule lies in its isotypic component. -/
theorem range_le_isotypicComponent
    {A : Subalgebra k (Module.End k E)}
    (V : Submodule A E) [IsSimpleModule A V]
    (f : V →ₗ[A] E) :
    LinearMap.range f ≤ isotypicComponent A E V := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  ·

    have hker : LinearMap.ker f = ⊥ := by
      rcases eq_bot_or_eq_top (LinearMap.ker f) with h | h
      · exact h
      · exfalso; apply hf
        ext v
        have hv : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa [LinearMap.mem_ker] using hv
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have e : V ≃ₗ[A] LinearMap.range f := LinearEquiv.ofInjective f hinj
    have heq : isotypicComponent A E (LinearMap.range f) = isotypicComponent A E V :=
      e.symm.isotypicComponent_eq
    calc LinearMap.range f
        ≤ isotypicComponent A E (LinearMap.range f) :=
          Submodule.le_isotypicComponent _
      _ = isotypicComponent A E V := heq

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

/-- Identifying a submodule with an isotypic component gives an equivalence between maps into it and maps into the ambient module. -/
noncomputable def linearMapSubtypeCodomainEquiv
    (A : Subalgebra k (Module.End k E))
    (V : Submodule A E) [IsSimpleModule A V]
    (c : Submodule A E)
    (hc_eq : c = isotypicComponent A E V) :
    (V →ₗ[A] c) ≃ₗ[k] (V →ₗ[A] E) where
  toFun f := c.subtype.comp f
  invFun g := g.codRestrict c (fun v => by
    have hrange : LinearMap.range g ≤ c := by
      rw [hc_eq]
      exact range_le_isotypicComponent (k := k) (E := E) (V := V) g
    exact hrange (LinearMap.mem_range_self g v))
  left_inv f := by ext v; rfl
  right_inv g := by ext v; rfl
  map_add' f g := by ext v; simp
  map_smul' r f := by ext v; rfl

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 800000 in
omit [Module.Finite k E] in

/-- Maps from a simple submodule into a semisimple module form a simple module over the centralizer. -/
theorem isSimpleModule_linearMap
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleModule A E]
    (V : Submodule A E) [IsSimpleModule A V] :
    IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥V →ₗ[A] E) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, ?_⟩
  ·
    refine ⟨V.subtype, 0, fun h => ?_⟩

    have hV : Nontrivial (↥V) := IsSimpleModule.nontrivial A (↥V)
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥V)
    have : (V.subtype v : E) = 0 := by
      have := LinearMap.congr_fun h v
      simpa using this
    apply hv
    exact Subtype.ext this
  ·
    intro f hf

    have hker : LinearMap.ker f = ⊥ := by
      rcases eq_bot_or_eq_top (LinearMap.ker f) with h | h
      · exact h
      · exfalso; apply hf
        ext v
        have hv : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa [LinearMap.mem_ker] using hv
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker

    intro g
    obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property f hinj g

    have hcent : LinearMap.restrictScalars k h ∈
        Subalgebra.centralizer k (A : Set (Module.End k E)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro a ha
      ext e

      have hsmul : h (a e) = a (h e) := h.map_smul (⟨a, ha⟩ : ↥A) e
      exact hsmul.symm

    refine ⟨⟨LinearMap.restrictScalars k h, hcent⟩, ?_⟩

    ext v
    simp only [LinearMap.toSpanSingleton_apply]

    change h (f v) = g v
    exact LinearMap.congr_fun hh v

set_option maxHeartbeats 3200000 in

set_option synthInstance.maxHeartbeats 1000000 in

/-- Provides auxiliary indexed data and a linear equivalence with a direct sum of tensor products. -/
theorem exists_auxiliary_tensor_decomposition
    [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Type v) (_ : ∀ i, AddCommGroup (V i))
      (_ : ∀ i, Module k (V i)) (_ : ∀ i, Module A (V i))
      (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i j, Nonempty (V i ≃ₗ[A] V j) → i = j)
      (_ : ∀ i, Module.Finite k (V i))
      (L : ι → Type v) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module
            (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
            (L i))
      (_ : ∀ i, SMulCommClass
            (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
            k (L i))
      (_ : ∀ i, Module.Finite k (L i)),
      Nonempty (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] L i)) := by
  classical
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : IsNoetherian A E := inferInstance
  haveI : Finite (isotypicComponents A E) := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  set m := Fintype.card (isotypicComponents A E) with hm
  let φ : isotypicComponents A E ≃ Fin m := Fintype.equivFin _

  let V' : isotypicComponents A E → Submodule A E := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose
  have V'_le : ∀ c, V' c ≤ c.1 := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.1
  have V'_simple : ∀ c, IsSimpleModule A (V' c) := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.2
  have V'_spec : ∀ c, (c.1 : Submodule A E) = isotypicComponent A E (V' c) := by
    intro c
    haveI := V'_simple c
    exact eq_isotypicComponent_of_le c.2 (V'_le c)
  haveI : ∀ c : isotypicComponents A E, Module.Finite k ↥(V' c) := fun c =>
    Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
      Subtype.val_injective
  haveI : ∀ c : isotypicComponents A E,
      Module.Finite k ((↥(V' c) : Type v) →ₗ[A] E) := fun c => by

    haveI : Module.Finite k ((↥(V' c) : Type v) →ₗ[k] E) := inferInstance
    exact Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (↥(V' c)) E k)
      (LinearMap.restrictScalars_injective _)
  refine ⟨Fin m, inferInstance, inferInstance,
    fun i => ↥(V' (φ.symm i)),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun i => V'_simple (φ.symm i),
    ?_,
    fun _ => inferInstance,
    fun i => (↥(V' (φ.symm i)) →ₗ[A] E),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun i => centralizerSMulCommClass k E (A := A) (V := ↥(V' (φ.symm i))),
    fun _ => inferInstance,
    ?_⟩
  ·
    intro i j ⟨e⟩
    have h_eq : isotypicComponent A E (V' (φ.symm i)) =
                isotypicComponent A E (V' (φ.symm j)) :=
      e.isotypicComponent_eq
    have h_c_eq : (φ.symm i).1 = (φ.symm j).1 := by
      rw [V'_spec (φ.symm i), V'_spec (φ.symm j)]; exact h_eq
    exact φ.symm.injective (Subtype.ext h_c_eq)
  ·

    let e1 : E ≃ₗ[A] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
      (isotypicComponentsDFinsuppEquiv A E).symm

    let e2 : E ≃ₗ[k] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
      e1.restrictScalars k

    haveI : IsNoetherian k E := inferInstance
    let perComp : ∀ c : isotypicComponents A E,
        (↥c.1 : Type v) ≃ₗ[k]
          ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E) := fun c => by
      haveI := V'_simple c

      haveI : Module.Finite k (↥(V' c) : Type v) :=
        Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
          Subtype.val_injective
      haveI : Module.Finite k (↥c.1 : Type v) :=
        Module.Finite.of_injective (c.1.subtype.restrictScalars k)
          Subtype.val_injective

      have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
        LinearEquiv.ofEq _ _ (V'_spec c)
      haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
        IsIsotypicOfType.isotypicComponent A E _
      haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
        e_submod.isIsotypicOfType_iff.mpr h_iso'

      let sE := tensorProductLinearMapEquiv k A (↥(V' c)) (↥c.1) h_iso

      let br := linearMapSubtypeCodomainEquiv k E A (V' c) c.1 (V'_spec c)

      exact sE.symm.trans (TensorProduct.congr (LinearEquiv.refl k _) br)

    let e3 : (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) ≃ₗ[k]
             (Π₀ c : isotypicComponents A E,
               ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) :=
      DFinsupp.mapRange.linearEquiv perComp

    let e4 : (Π₀ c : isotypicComponents A E,
              ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) ≃ₗ[k]
             DirectSum (Fin m) (fun i =>
               ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
      DirectSum.lequivCongrLeft k φ
    exact ⟨e2.trans (e3.trans e4)⟩

set_option maxHeartbeats 4000000 in

set_option synthInstance.maxHeartbeats 1500000 in

/-- Provides auxiliary indexed submodules and an equivalence whose inverse evaluates pure tensors. -/
@[source_ref "Chapter5/Theorem5.18.1" (role := supporting)]
theorem exists_auxiliary_evaluation_equiv
    [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Submodule A E) (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i j, Nonempty (↥(V i) ≃ₗ[A] ↥(V j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(V i))
      (_ : ∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
        (↥(V i) →ₗ[A] E)),
      ∃ (e : E ≃ₗ[k] DirectSum ι
          (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E))),
        ∀ (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E),
          e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v := by
  classical
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : IsNoetherian A E := inferInstance
  haveI : Finite (isotypicComponents A E) := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  haveI : IsNoetherian k E := inferInstance
  set m := Fintype.card (isotypicComponents A E) with hm
  let φ : isotypicComponents A E ≃ Fin m := Fintype.equivFin _
  let V' : isotypicComponents A E → Submodule A E := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose
  have V'_le : ∀ c, V' c ≤ c.1 := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.1
  have V'_simple : ∀ c, IsSimpleModule A (V' c) := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.2
  have V'_spec : ∀ c, (c.1 : Submodule A E) = isotypicComponent A E (V' c) := by
    intro c
    haveI := V'_simple c
    exact eq_isotypicComponent_of_le c.2 (V'_le c)

  haveI hV'_fin : ∀ c : isotypicComponents A E,
      Module.Finite k ((↥(V' c) : Type v)) := fun c =>
    Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
      Subtype.val_injective

  let perComp : ∀ c : isotypicComponents A E,
      (↥c.1 : Type v) ≃ₗ[k]
        ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E) := fun c => by
    haveI := V'_simple c
    haveI : Module.Finite k (↥c.1 : Type v) :=
      Module.Finite.of_injective (c.1.subtype.restrictScalars k)
        Subtype.val_injective
    have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
      LinearEquiv.ofEq _ _ (V'_spec c)
    haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
      IsIsotypicOfType.isotypicComponent A E _
    haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
      e_submod.isIsotypicOfType_iff.mpr h_iso'
    let sE := tensorProductLinearMapEquiv k A (↥(V' c)) (↥c.1) h_iso
    let br := linearMapSubtypeCodomainEquiv k E A (V' c) c.1 (V'_spec c)
    exact sE.symm.trans (TensorProduct.congr (LinearEquiv.refl k _) br)

  have perComp_symm_tmul : ∀ (c : isotypicComponents A E)
      (v : ↥(V' c)) (l : ↥(V' c) →ₗ[A] E),
      (((perComp c).symm (v ⊗ₜ[k] l) : ↥c.1) : E) = l v := by
    intro c v l
    haveI := V'_simple c
    haveI : Module.Finite k (↥c.1 : Type v) :=
      Module.Finite.of_injective (c.1.subtype.restrictScalars k)
        Subtype.val_injective
    have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
      LinearEquiv.ofEq _ _ (V'_spec c)
    haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
      IsIsotypicOfType.isotypicComponent A E _
    haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
      e_submod.isIsotypicOfType_iff.mpr h_iso'

    change ((((tensorProductLinearMapEquiv k A (↥(V' c)) (↥c.1) h_iso).symm).trans
            (TensorProduct.congr (LinearEquiv.refl k _)
              (linearMapSubtypeCodomainEquiv k E A (V' c) c.1 (V'_spec c)))).symm
          (v ⊗ₜ[k] l) : ↥c.1).val = l v
    rw [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
        TensorProduct.congr_symm, LinearEquiv.refl_symm, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, tensorProductLinearMapEquiv_apply_tmul]

    rfl

  let e2 : E ≃ₗ[k] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
    (isotypicComponentsDFinsuppEquiv A E).symm.restrictScalars k
  let e3 : (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) ≃ₗ[k]
           (Π₀ c : isotypicComponents A E,
             ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) :=
    DFinsupp.mapRange.linearEquiv perComp
  let e4 : (Π₀ c : isotypicComponents A E,
            ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) ≃ₗ[k]
           DirectSum (Fin m) (fun i =>
             ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
    DirectSum.lequivCongrLeft k φ
  let etotal : E ≃ₗ[k] DirectSum (Fin m)
    (fun i => ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
    e2.trans (e3.trans e4)

  have hL_simp : ∀ i, IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥(V' (φ.symm i)) →ₗ[A] E) := fun i => by
    haveI : IsSimpleModule (↥A) ↥(V' (φ.symm i)) := V'_simple (φ.symm i)
    exact isSimpleModule_linearMap (k := k) (E := E) A (V' (φ.symm i))
  refine ⟨Fin m, inferInstance, inferInstance,
    fun i => V' (φ.symm i),
    fun i => V'_simple (φ.symm i),
    ?_, fun i => hV'_fin (φ.symm i), hL_simp,
    etotal, ?_⟩
  ·
    intro i j ⟨eqv⟩
    have h_eq : isotypicComponent A E (V' (φ.symm i)) =
                isotypicComponent A E (V' (φ.symm j)) :=
      eqv.isotypicComponent_eq
    have h_c_eq : (φ.symm i).1 = (φ.symm j).1 := by
      rw [V'_spec (φ.symm i), V'_spec (φ.symm j)]; exact h_eq
    exact φ.symm.injective (Subtype.ext h_c_eq)
  ·
    intro i

    change ∀ (v : ↥(V' (φ.symm i))) (l : ↥(V' (φ.symm i)) →ₗ[A] E),
      etotal.symm (DirectSum.of
        (fun j : Fin m => ↥(V' (φ.symm j)) ⊗[k] (↥(V' (φ.symm j)) →ₗ[A] E))
        i (v ⊗ₜ[k] l)) = l v
    intro v l

    rw [LinearEquiv.symm_apply_eq]

    haveI := V'_simple (φ.symm i)

    have hrange : l v ∈ ((φ.symm i).1 : Submodule A E) := by
      have hr := range_le_isotypicComponent (k := k) (E := E)
        (V := V' (φ.symm i)) (A := A) l (LinearMap.mem_range_self l v)
      rw [← V'_spec (φ.symm i)] at hr
      exact hr

    have step_fwd_1 : (isotypicComponentsDFinsuppEquiv A E).symm (l v) =
        DFinsupp.single (φ.symm i) (⟨l v, hrange⟩ : ↥((φ.symm i).1)) :=
      iSupIndep.linearEquiv_symm_apply
        (ind := (sSupIndep_iff _).mp (sSupIndep_isotypicComponents A E))
        (iSup_top := by
          rw [← sSup_eq_iSup']
          exact sSup_isotypicComponents A E) (i := φ.symm i)
        (x := l v) hrange

    have step_fwd_2 : (perComp (φ.symm i)) ⟨l v, hrange⟩ =
        (v ⊗ₜ[k] l : ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) := by
      apply (perComp (φ.symm i)).symm.injective
      rw [(perComp (φ.symm i)).symm_apply_apply]
      apply Subtype.ext
      symm
      exact perComp_symm_tmul (φ.symm i) v l

    change (DirectSum.of
        (fun i : Fin m => ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E))
        i (v ⊗ₜ[k] l)) =
      e4 (e3 (e2 (l v)))

    have he2 : e2 (l v) = DFinsupp.single (φ.symm i)
        (⟨l v, hrange⟩ : ↥((φ.symm i).1)) := step_fwd_1
    rw [he2]

    have he3 : e3 (DFinsupp.single (φ.symm i)
        (⟨l v, hrange⟩ : ↥((φ.symm i).1))) =
        DFinsupp.single (φ.symm i) ((perComp (φ.symm i)) ⟨l v, hrange⟩) :=
      DFinsupp.mapRange_single (hf := fun c => (perComp c).map_zero)
    rw [he3, step_fwd_2]

    refine DFinsupp.ext (fun k' => ?_)
    change (DirectSum.of
          (fun j : Fin m => ↥(V' (φ.symm j)) ⊗[k] (↥(V' (φ.symm j)) →ₗ[A] E))
          i (v ⊗ₜ[k] l)) k' =
      ((DirectSum.lequivCongrLeft k φ)
        (DFinsupp.single
          (β := fun c : isotypicComponents A E =>
            ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E))
          (φ.symm i)
          (v ⊗ₜ[k] l))) k'
    rw [DirectSum.lequivCongrLeft_apply]
    by_cases hk : k' = i
    · subst hk
      rw [DirectSum.of_eq_same, DFinsupp.single_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hk]
      have hne : φ.symm k' ≠ φ.symm i := fun h => hk (φ.symm.injective h)
      rw [DFinsupp.single_eq_of_ne hne]

/-- The algebra action on a direct sum of tensors, acting on the submodule factor. -/
noncomputable def algebraActionOnTensorDirectSum
    {ι : Type*} {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E) (a : A) :
    DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)) →ₗ[k]
      DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)) :=
  DirectSum.lmap fun i => TensorProduct.map
    (Algebra.lsmul k k (↥(V i)) a) LinearMap.id

/-- The centralizer action on a direct sum of tensors, acting on the linear-map factor. -/
noncomputable def centralizerActionOnTensorDirectSum
    {ι : Type*} {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E)
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :
    DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)) →ₗ[k]
      DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)) :=
  DirectSum.lmap fun i => TensorProduct.map LinearMap.id
    (centralizerActionMonoidHom k E A (↥(V i)) b)

omit [Module.Finite k E] in
/-- The algebra action on a pure tensor acts on its first factor. -/
@[simp]
theorem algebraActionOnTensorDirectSum_apply_tmul
    {ι : Type*} [DecidableEq ι] {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E) (a : A) (i : ι) (v : ↥(V i))
    (l : ↥(V i) →ₗ[A] E) :
    algebraActionOnTensorDirectSum (k := k) (E := E) V a
        (DirectSum.of (fun j => ↥(V j) ⊗[k] (↥(V j) →ₗ[A] E))
          i (v ⊗ₜ[k] l)) =
      DirectSum.of (fun j => ↥(V j) ⊗[k] (↥(V j) →ₗ[A] E))
        i ((a • v) ⊗ₜ[k] l) := by
  rw [algebraActionOnTensorDirectSum, DirectSum.lmap_of,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

omit [Module.Finite k E] in
/-- The centralizer action on a pure tensor composes its linear-map factor with the commuting endomorphism. -/
@[simp]
theorem centralizerActionOnTensorDirectSum_apply_tmul
    {ι : Type*} [DecidableEq ι] {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E)
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
    (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E) :
    centralizerActionOnTensorDirectSum (k := k) (E := E) V b
        (DirectSum.of (fun j => ↥(V j) ⊗[k] (↥(V j) →ₗ[A] E))
          i (v ⊗ₜ[k] l)) =
      DirectSum.of (fun j => ↥(V j) ⊗[k] (↥(V j) →ₗ[A] E)) i
        (v ⊗ₜ[k] ((centralizerToModuleEnd k E A b).comp l)) := by
  rw [centralizerActionOnTensorDirectSum, DirectSum.lmap_of,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

/-- Auxiliary decomposition data attached to a family of submodules of an ambient module. -/
structure AuxiliaryDecompositionData
    {ι : Type*} {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E) where
  /-- The linear equivalence from the representation to the direct sum of tensor products carried by the data. -/
  equiv : E ≃ₗ[k]
    DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E))
  /-- The associated equivalence intertwines the original algebra action with its action on the tensor direct sum. -/
  equiv_apply_algebra : ∀ (a : A) (x : E),
    equiv (a.val x) =
      algebraActionOnTensorDirectSum (k := k) (E := E) (A := A) V a (equiv x)
  /-- The associated equivalence intertwines the centralizer action with its action on the tensor direct sum. -/
  equiv_apply_centralizer :
    ∀ (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) (x : E),
      equiv (b.val x) =
        centralizerActionOnTensorDirectSum (k := k) (E := E) (A := A)
          V b (equiv x)

set_option maxHeartbeats 4000000 in

set_option synthInstance.maxHeartbeats 1500000 in

/-- Constructs auxiliary decomposition data from an equivalence whose inverse sends pure tensors to evaluation. -/
@[source_ref "Chapter5/Theorem5.18.1" (role := supporting)]
noncomputable def AuxiliaryDecompositionData.ofEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Subalgebra k (Module.End k E)}
    (V : ι → Submodule A E)
    (e : E ≃ₗ[k] DirectSum ι (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)))
    (he : ∀ (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v) :
    AuxiliaryDecompositionData (k := k) (E := E) (A := A) V := by
  classical
  refine ⟨e, ?_, ?_⟩
  · intro a x
    have h_inv : ∀ y : DirectSum ι
        (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)),
        e.symm (algebraActionOnTensorDirectSum (k := k) (E := E) (A := A)
          V a y) = a.val (e.symm y) := by
      intro y
      induction y using DirectSum.induction_on with
      | zero => simp [algebraActionOnTensorDirectSum]
      | add y z hy hz => simp only [map_add, hy, hz]
      | of i t =>
        induction t using TensorProduct.induction_on with
        | zero => simp [algebraActionOnTensorDirectSum]
        | add t s ht hs => simp only [map_add, ht, hs]
        | tmul v l =>
          rw [algebraActionOnTensorDirectSum_apply_tmul]
          change e.symm (DirectSum.of _ i ((a • v) ⊗ₜ[k] l)) =
            a.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))
          rw [he, he, LinearMap.map_smul]
          rfl
    apply e.symm.injective
    rw [e.symm_apply_apply, h_inv, e.symm_apply_apply]
  · intro b x
    have h_inv : ∀ y : DirectSum ι
        (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)),
        e.symm (centralizerActionOnTensorDirectSum
          (k := k) (E := E) (A := A) V b y) =
          b.val (e.symm y) := by
      intro y
      induction y using DirectSum.induction_on with
      | zero => simp [centralizerActionOnTensorDirectSum]
      | add y z hy hz => simp only [map_add, hy, hz]
      | of i t =>
        induction t using TensorProduct.induction_on with
        | zero => simp [centralizerActionOnTensorDirectSum]
        | add t s ht hs => simp only [map_add, ht, hs]
        | tmul v l =>
          rw [centralizerActionOnTensorDirectSum_apply_tmul]
          change e.symm (DirectSum.of _ i
            (v ⊗ₜ[k] ((centralizerToModuleEnd k E A b).comp l))) =
              b.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))
          rw [he, he]
          rfl
    apply e.symm.injective
    rw [e.symm_apply_apply, h_inv, e.symm_apply_apply]

set_option maxHeartbeats 4000000 in

set_option synthInstance.maxHeartbeats 1500000 in

/-- Provides auxiliary indexed submodules and decomposition data satisfying the pure-tensor evaluation formula. -/
@[source_ref "Chapter5/Theorem5.18.1" (role := supporting)]
theorem exists_auxiliary_decomposition_data
    [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Submodule A E) (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i j, Nonempty (↥(V i) ≃ₗ[A] ↥(V j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(V i))
      (_ : ∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
        (↥(V i) →ₗ[A] E)),
      ∃ e : AuxiliaryDecompositionData (k := k) (E := E) (A := A) V,
        ∀ (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E),
          e.equiv.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v := by
  obtain ⟨ι, hι, hιDec, V, hVSimple, hVDistinct, hVFinite, hLSimple, e, he⟩ :=
    exists_auxiliary_evaluation_equiv k E A
  exact ⟨ι, hι, hιDec, V, hVSimple, hVDistinct, hVFinite, hLSimple,
    AuxiliaryDecompositionData.ofEquiv (k := k) (E := E) (A := A) V e he, he⟩

end RepresentationTheory.CentralizerDecomposition

/--
The linear equivalence from the ambient module to the direct sum of tensor products carried by
the data.
-/
add_decl_doc _root_.RepresentationTheory.CentralizerDecomposition.AuxiliaryDecompositionData.equiv
