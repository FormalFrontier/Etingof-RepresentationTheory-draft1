/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.RingAuxiliary
import RepresentationTheory.FieldAlgebraProperties
import RepresentationTheory.RingTheory.Idempotent
import RepresentationTheory.RingTheory.ElementProperties
import RepresentationTheory.ModuleCat.Equivalence.Finite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Algebra.Opposite

import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Morita equivalence

Structural results for equivalences of module categories and associated algebras.
-/


set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

namespace RepresentationTheory.MoritaEquivalence

/-- An internal finite direct-sum decomposition induces an isomorphism from the ambient module to the biproduct of its summands. -/
noncomputable def moduleCatIsoBiproductOfIsInternal
    {A : Type u} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Submodule A A)
    (h : DirectSum.IsInternal N) :
    ModuleCat.of A A ≅ ⨁ (fun i => ModuleCat.of A (↥(N i))) := by

  let e₁ := (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) h)

  let e₂ := DirectSum.linearEquivFunOnFintype A ι (fun i => ↥(N i))

  let e₃ := ModuleCat.biproductIsoPi (fun i => ModuleCat.of A (↥(N i)))

  exact e₁.symm.toModuleIso ≪≫ e₂.toModuleIso ≪≫ e₃.symm

/-- An equivalence between categories with zero morphisms sends a simple object to a simple object. -/
theorem simple_equivalence_obj {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ≌ D) (X : C) [Simple X] :
    Simple (F.functor.obj X) := by
  constructor
  intro Y g hMono

  let g' : F.inverse.obj Y ⟶ X := F.inverse.map g ≫ (F.unitIso.app X).inv

  haveI : Mono (F.inverse.map g) := by
    haveI : F.inverse.PreservesMonomorphisms :=
      CategoryTheory.Functor.preservesMonomorphisms_of_adjunction F.toAdjunction
    exact F.inverse.map_mono g
  haveI : Mono g' := mono_comp (F.inverse.map g) (F.unitIso.app X).inv

  have hSimp := Simple.mono_isIso_iff_nonzero g'
  constructor
  ·
    intro hIso h0

    have hg'_zero : g' = 0 := by
      simp only [g', h0, Functor.map_zero, zero_comp]

    have := hSimp.mp

    haveI : IsIso (F.inverse.map g) := by
      haveI := hIso
      exact Functor.map_isIso F.inverse g
    haveI : IsIso g' := IsIso.comp_isIso
    exact absurd hg'_zero (hSimp.mp ‹IsIso g'›)
  ·
    intro hne

    have hg'_ne : g' ≠ 0 := by
      intro h0
      apply hne

      have h_inv_zero := congr_arg (· ≫ (F.unitIso.app X).hom) h0

      simp only [g', Category.assoc, Iso.inv_hom_id, Category.comp_id,
        zero_comp] at h_inv_zero

      exact F.inverse.map_injective (by rw [h_inv_zero, Functor.map_zero])

    haveI : IsIso g' := hSimp.mpr hg'_ne

    have : F.inverse.map g = g' ≫ (F.unitIso.app X).hom := by

      simp only [g', Category.assoc, Iso.inv_hom_id, Category.comp_id]
    haveI : IsIso (F.inverse.map g) := by rw [this]; exact IsIso.comp_isIso

    exact isIso_of_reflects_iso g F.inverse

/-- The ring relation is symmetric. -/
lemma _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.ring_relation_symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : RepresentationTheory.RingAuxiliary.RingAuxiliary A B) : RepresentationTheory.RingAuxiliary.RingAuxiliary B A :=
  h.map CategoryTheory.Equivalence.symm

/-- The ring relation is transitive. -/
lemma _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.ring_relation_trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : RepresentationTheory.RingAuxiliary.RingAuxiliary A B) (h₂ : RepresentationTheory.RingAuxiliary.RingAuxiliary B C) :
    RepresentationTheory.RingAuxiliary.RingAuxiliary A C := by
  obtain ⟨e₁⟩ := h₁; obtain ⟨e₂⟩ := h₂; exact ⟨e₁.trans e₂⟩

/-- An idempotent is one when its complement is nilpotent. -/
theorem idempotent_eq_one_of_one_sub_nilpotent
    {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) (hnil : IsNilpotent (1 - e)) : e = 1 := by

  have h_unit : IsUnit e := by
    have h := hnil.isUnit_one_sub
    rwa [sub_sub_cancel] at h

  obtain ⟨u, rfl⟩ := h_unit
  have h_mul : (↑u : R) * (↑u - 1) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]

  have key : (↑u : R) - 1 = 0 := by
    have h1 : (↑u⁻¹ : R) * ↑u = 1 := u.inv_mul
    calc (↑u : R) - 1
        = 1 * (↑u - 1) := (one_mul _).symm
      _ = ↑u⁻¹ * ↑u * (↑u - 1) := by rw [h1]
      _ = ↑u⁻¹ * (↑u * (↑u - 1)) := by rw [mul_assoc]
      _ = ↑u⁻¹ * 0 := by rw [h_mul]
      _ = 0 := mul_zero _
  exact sub_eq_zero.mp key

variable {k : Type u} [Field k]

private noncomputable def iso_of_surjection_with_trivial_kernel_head
    {B₂ : Type u} [Ring B₂] [IsArtinianRing B₂]
    (P : ModuleCat.{u} B₂)
    (f : P →ₗ[B₂] B₂) (hf_surj : Function.Surjective f)
    (hker : LinearMap.ker f ≤ Ring.jacobson B₂ • (LinearMap.ker f)) :
    P ≅ ModuleCat.of B₂ B₂ := by

  have heq : LinearMap.ker f = Ring.jacobson B₂ • LinearMap.ker f :=
    le_antisymm hker Submodule.smul_le_right

  have hker_bot : LinearMap.ker f = ⊥ := by
    obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson B₂))

    have hstep : ∀ k, Ring.jacobson B₂ ^ k • LinearMap.ker f =
        Ring.jacobson B₂ ^ (k + 1) • LinearMap.ker f := fun k => by
      conv_lhs => rw [heq]
      rw [← Submodule.mul_smul, ← Submodule.pow_succ]

    suffices h : ∀ k, LinearMap.ker f = Ring.jacobson B₂ ^ k • LinearMap.ker f by
      have h1 := h n
      rw [eq_bot_iff, h1]
      have : (Ring.jacobson B₂ ^ n : Ideal B₂) = ⊥ := by rwa [Ideal.zero_eq_bot] at hn
      rw [this, Submodule.bot_smul]
    intro k; induction k with
    | zero => rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih => rw [← hstep, ← ih]

  have hf_inj : Function.Injective f :=
    LinearMap.ker_eq_bot.mp hker_bot

  exact (LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).toModuleIso

private theorem module_finite_equiv_image
    (k : Type u) [Field k]
    {B₁ : Type u} [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    {B₂ : Type u} [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) :
    Module.Finite B₂ (F.functor.obj (ModuleCat.of B₁ B₁)) := by
  haveI : IsArtinianRing B₁ := IsArtinianRing.of_finite k B₁
  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂
  exact RepresentationTheory.ModuleCat.Equivalence.Finite.ModuleCat.Equivalence.finite_image_regular F

private noncomputable instance equiv_image_projective
    {R : Type u} [Ring R] {S : Type u} [Ring S]
    (F : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Projective S (F.functor.obj (ModuleCat.of R R)) := by

  haveI : Module.Projective R R := Module.Projective.of_free
  haveI : CategoryTheory.Projective (ModuleCat.of R R) :=
    (ModuleCat.of R R).projective_of_categoryTheory_projective
  haveI : CategoryTheory.Projective (F.functor.obj (ModuleCat.of R R)) :=
    (F.map_projective_iff _).mpr ‹CategoryTheory.Projective (ModuleCat.of R R)›
  exact (F.functor.obj (ModuleCat.of R R)).projective_of_module_projective

private theorem projective_lift_surjective
    {B₂ : Type u} [Ring B₂] [IsSemiprimaryRing B₂]
    {P : Type u} [AddCommGroup P] [Module B₂ P]
    {f : P →ₗ[B₂] B₂}
    {g : P →ₗ[B₂] B₂ ⧸ (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂)}
    (hg_surj : Function.Surjective g)
    (hf : (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂).mkQ ∘ₗ f = g) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  let π := (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂).mkQ

  have h_range_sup : LinearMap.range f ⊔ (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨p, hp⟩ := hg_surj (π b)
    have hπfp : π (f p) = π b := by rw [← LinearMap.comp_apply, hf, hp]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hπfp
    exact Submodule.mem_sup.mpr ⟨f p, LinearMap.mem_range.mpr ⟨p, rfl⟩, b - f p,
      neg_sub (f p) b ▸ Submodule.neg_mem _ hπfp, add_sub_cancel (f p) b⟩

  obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson B₂))
  suffices h : ∀ k, LinearMap.range f ⊔ Ring.jacobson B₂ ^ k • ⊤ = ⊤ by
    have h1 := h n
    have : (Ring.jacobson B₂ ^ n : Ideal B₂) = ⊥ := by rwa [Ideal.zero_eq_bot] at hn
    rw [this, Submodule.bot_smul, sup_bot_eq] at h1
    exact h1
  intro k; induction k with
  | zero =>
    simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
  | succ k ih =>

    have hstep : Ring.jacobson B₂ ^ k • (⊤ : Submodule B₂ B₂) ≤
        LinearMap.range f ⊔ Ring.jacobson B₂ ^ (k + 1) • ⊤ := by
      calc Ring.jacobson B₂ ^ k • ⊤
          = Ring.jacobson B₂ ^ k • (LinearMap.range f ⊔ Ring.jacobson B₂ • ⊤) := by
            rw [h_range_sup]
        _ = Ring.jacobson B₂ ^ k • LinearMap.range f ⊔
            Ring.jacobson B₂ ^ k • (Ring.jacobson B₂ • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ LinearMap.range f ⊔ Ring.jacobson B₂ ^ (k + 1) • ⊤ := by
            apply sup_le_sup
            · exact Submodule.smul_le_right
            · rw [← Submodule.mul_smul, ← Submodule.pow_succ]
    exact le_antisymm le_top (ih.symm.le.trans
      ((sup_le_sup_left hstep _).trans (by rw [← sup_assoc, sup_idem])))

private theorem jacobson_smul_eq_bot_of_semisimple
    {B₂ : Type u} [Ring B₂]
    {M : Type u} [AddCommGroup M] [Module B₂ M] [IsSemisimpleModule B₂ M] :
    Ring.jacobson B₂ • (⊤ : Submodule B₂ M) = ⊥ :=
  le_bot_iff.mp ((Ring.jacobson_smul_top_le B₂ M).trans
    (le_of_eq (IsSemisimpleModule.jacobson_eq_bot B₂ M)))

private theorem module_jacobson_eq_smul_of_artinian
    {B₂ : Type u} [Ring B₂] [IsArtinianRing B₂]
    {M : Type u} [AddCommGroup M] [Module B₂ M] :
    Module.jacobson B₂ M = Ring.jacobson B₂ • (⊤ : Submodule B₂ M) := by
  apply le_antisymm
  ·

    set N := Ring.jacobson B₂ • (⊤ : Submodule B₂ M) with hN
    have h_tors := Module.isTorsionBySet_quotient_ideal_smul M (Ring.jacobson B₂)

    haveI : IsSemisimpleModule B₂ (M ⧸ N) := h_tors.isSemisimpleModule_iff.mp inferInstance
    have h_le := Module.le_comap_jacobson (f := N.mkQ)
    rw [IsSemisimpleModule.jacobson_eq_bot B₂ (M ⧸ N), Submodule.comap_bot,
      Submodule.ker_mkQ] at h_le
    exact h_le
  · exact Ring.jacobson_smul_top_le B₂ M

private theorem equiv_hom_to_simple_nonzero
    {B₁ : Type u} [Ring B₁]
    {B₂ : Type u} [Ring B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    (S : ModuleCat.{u} B₂) [hS : Simple S] :
    ∃ (f : F.functor.obj (ModuleCat.of B₁ B₁) ⟶ S), f ≠ 0 := by

  haveI : Simple (F.inverse.obj S) := simple_equivalence_obj F.symm S

  have hGS_nt : Nontrivial (F.inverse.obj S) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact Simple.not_isZero (F.inverse.obj S) (ModuleCat.isZero_of_subsingleton _)

  obtain ⟨m, hm⟩ := exists_ne (0 : F.inverse.obj S)

  let φ_m : ModuleCat.of B₁ B₁ ⟶ F.inverse.obj S :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton B₁ (F.inverse.obj S) m)

  have hφ_ne : φ_m ≠ 0 := by
    intro h
    apply hm
    have h1 : φ_m.hom = (0 : ModuleCat.of B₁ B₁ ⟶ F.inverse.obj S).hom :=
      congrArg ModuleCat.Hom.hom h
    have h2 : φ_m.hom (1 : B₁) = 0 := by rw [h1]; rfl
    simpa [φ_m, LinearMap.toSpanSingleton_apply] using h2

  let f : F.functor.obj (ModuleCat.of B₁ B₁) ⟶ S :=
    (F.toAdjunction.homEquiv _ _).symm φ_m
  refine ⟨f, ?_⟩
  intro hf
  apply hφ_ne
  have h2 : φ_m = (F.toAdjunction.homEquiv _ _) f := by
    rw [Equiv.apply_symm_apply]
  rw [h2, hf, Adjunction.homEquiv_apply, F.inverse.map_zero, comp_zero]

private noncomputable instance equiv_inverse_linear
    {k : Type*} [CommSemiring k]
    {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
    {D : Type u} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D]
    (F : C ≌ D) [F.functor.Linear k] : F.inverse.Linear k where
  map_smul {X Y} f c := by

    apply F.functor.map_injective
    rw [F.functor.map_smul]

    set ε := F.counitIso.hom
    have nat_f := ε.naturality f
    have nat_cf := ε.naturality (c • f)

    have hε : IsIso (ε.app Y) := (F.counitIso.app Y).isIso_hom
    simp only [Functor.comp_map, Functor.id_map] at nat_cf nat_f

    rw [CategoryTheory.Linear.comp_smul, ← nat_f, ← CategoryTheory.Linear.smul_comp] at nat_cf

    exact (cancel_mono (ε.app Y)).mp nat_cf

private theorem adj_homEquiv_smul
    {k : Type*} [Field k]
    {B₁ : Type u} [Ring B₁] [Algebra k B₁]
    {B₂ : Type u} [Ring B₂] [Algebra k B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) [F.functor.Linear k]
    (X : ModuleCat.{u} B₁) (Y : ModuleCat.{u} B₂)
    (c : k) (f : F.functor.obj X ⟶ Y) :
    F.toAdjunction.homEquiv X Y (c • f) =
    c • F.toAdjunction.homEquiv X Y f := by
  haveI := equiv_inverse_linear F (k := k)
  simp only [Adjunction.homEquiv_unit]
  rw [F.inverse.map_smul, CategoryTheory.Linear.comp_smul]

private noncomputable instance equiv_functor_additive
    {R : Type u} [Ring R] {S : Type u} [Ring S]
    (F : ModuleCat.{u} R ≌ ModuleCat.{u} S) : F.functor.Additive :=
  Functor.additive_of_preserves_binary_products F.functor

private theorem simple_of_equiv_inverse
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u} [Category.{v} D] [Preadditive D]
    (F : C ≌ D) (Y : D) [Simple Y] : Simple (F.inverse.obj Y) := by

  haveI : Simple ((𝟭 D).obj Y) := ‹Simple Y›
  haveI : Simple (F.functor.obj (F.inverse.obj Y)) :=
    Simple.of_iso (F.counitIso.app Y)

  constructor; intro Z f _; constructor
  ·
    intro hi hf
    apply Simple.not_isZero (F.functor.obj (F.inverse.obj Y))
    rw [IsZero.iff_id_eq_zero, ← F.functor.map_id,
      show 𝟙 (F.inverse.obj Y) = inv f ≫ f from (IsIso.inv_hom_id f).symm]
    simp only [hf, comp_zero, F.functor.map_zero]
  ·
    intro hne
    have hFf_ne : F.functor.map f ≠ 0 := by
      intro h; apply hne; rw [← F.functor.map_zero] at h
      exact F.functor.map_injective h
    haveI : Mono (F.functor.map f) := inferInstance
    haveI : IsIso (F.functor.map f) := isIso_of_mono_of_nonzero hFf_ne
    exact isIso_of_reflects_iso f F.functor

private theorem semisimple_iso_aux
    {k : Type*} [Field k] [IsAlgClosed k]
    {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
    [IsSemiprimaryRing R]
    (d : ℕ)
    (M N : Type u) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N]
    [Module.Finite R M] [Module.Finite R N]
    [Module.Finite k M] [Module.Finite k N]
    (hd : Module.finrank k M ≤ d)
    (hM_tors : Module.IsTorsionBySet R M (Ring.jacobson R))
    (hN_tors : Module.IsTorsionBySet R N (Ring.jacobson R))
    (hhom : ∀ (S : Type u) [AddCommGroup S] [Module R S] [Module k S] [IsScalarTower k R S]
      [IsSimpleModule R S] [Module.Finite k S],
      Module.finrank k (M →ₗ[R] S) = Module.finrank k (N →ₗ[R] S)) :
    Nonempty (M ≃ₗ[R] N) := by
  induction d generalizing M N with
  | zero =>

    haveI : Subsingleton M := by
      haveI : Module.Free k M := inferInstance
      exact (Module.finrank_zero_iff (R := k)).mp (Nat.le_zero.mp hd)

    haveI : Subsingleton N := by
      by_contra hN; rw [not_subsingleton_iff_nontrivial] at hN
      obtain ⟨S₀, hS₀⟩ := IsSemisimpleModule.exists_simple_submodule (R := R) (M := N)
      haveI := hS₀; haveI : Nontrivial ↥S₀ := IsSimpleModule.nontrivial R ↥S₀
      obtain ⟨Q₀, hc⟩ := exists_isCompl S₀
      haveI : Module.Finite k ↥S₀ :=
        Module.Finite.of_injective (S₀.restrictScalars k).subtype Subtype.val_injective

      have hne : S₀.projectionOnto Q₀ hc ≠ 0 := by
        intro h; obtain ⟨s₀, hs₀⟩ := exists_ne (0 : ↥S₀)
        have := Submodule.projectionOnto_apply_left hc s₀
        rw [h, LinearMap.zero_apply] at this; exact hs₀ this.symm

      have h0 : Module.finrank k (N →ₗ[R] ↥S₀) = 0 := by
        rw [← hhom]; exact Module.finrank_zero_of_subsingleton

      haveI : Module.Finite k (N →ₗ[R] ↥S₀) :=
        Module.Finite.of_injective
          (LinearMap.restrictScalarsₗ (S := R) (M := N) (N := ↥S₀) (R := k) (R₁ := k))
          (LinearMap.restrictScalars_injective k)

      have : Subsingleton (N →ₗ[R] ↥S₀) :=
        (Module.finrank_zero_iff (R := k)).mp h0
      exact hne (Subsingleton.elim _ 0)
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  | succ d ih =>
    by_cases htriv : Subsingleton M
    ·
      haveI : Subsingleton N := by
        by_contra hN; rw [not_subsingleton_iff_nontrivial] at hN
        obtain ⟨S₀, hS₀⟩ := IsSemisimpleModule.exists_simple_submodule (R := R) (M := N)
        haveI := hS₀; haveI : Nontrivial ↥S₀ := IsSimpleModule.nontrivial R ↥S₀
        obtain ⟨Q₀, hc⟩ := exists_isCompl S₀
        haveI : Module.Finite k ↥S₀ :=
          Module.Finite.of_injective (S₀.restrictScalars k).subtype Subtype.val_injective
        have hne : S₀.projectionOnto Q₀ hc ≠ 0 := by
          intro h; obtain ⟨s₀, hs₀⟩ := exists_ne (0 : ↥S₀)
          have := Submodule.projectionOnto_apply_left hc s₀
          rw [h, LinearMap.zero_apply] at this; exact hs₀ this.symm
        have h0 : Module.finrank k (N →ₗ[R] ↥S₀) = 0 := by
          rw [← hhom]; exact Module.finrank_zero_of_subsingleton
        haveI : Module.Finite k (N →ₗ[R] ↥S₀) :=
          Module.Finite.of_injective
            (LinearMap.restrictScalarsₗ (S := R) (M := N) (N := ↥S₀) (R := k) (R₁ := k))
            (LinearMap.restrictScalars_injective k)
        have : Subsingleton (N →ₗ[R] ↥S₀) :=
          (Module.finrank_zero_iff (R := k)).mp h0
        exact hne (Subsingleton.elim _ 0)
      exact ⟨LinearEquiv.ofSubsingleton M N⟩
    ·
      haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp htriv
      obtain ⟨S₀, hS₀⟩ := IsSemisimpleModule.exists_simple_submodule (R := R) (M := M)
      haveI := hS₀
      obtain ⟨Q, hMc⟩ := exists_isCompl S₀

      haveI : Nontrivial ↥S₀ := IsSimpleModule.nontrivial R ↥S₀
      haveI : Module.Finite k ↥S₀ :=
        Module.Finite.of_injective (S₀.restrictScalars k).subtype Subtype.val_injective
      obtain ⟨f, hf_ne, hf_surj⟩ :
          ∃ f : N →ₗ[R] ↥S₀, f ≠ 0 ∧ Function.Surjective f := by

        obtain ⟨Q', hMc'⟩ := exists_isCompl S₀
        have hproj_ne : S₀.projectionOnto Q' hMc' ≠ 0 := by
          intro h; obtain ⟨s₀, hs₀⟩ := exists_ne (0 : ↥S₀)
          have := Submodule.projectionOnto_apply_left hMc' s₀
          rw [h, LinearMap.zero_apply] at this; exact hs₀ this.symm

        haveI : Module.Finite k (M →ₗ[R] ↥S₀) :=
          Module.Finite.of_injective
            (LinearMap.restrictScalarsₗ (S := R) (M := M) (N := ↥S₀) (R := k) (R₁ := k))
            (LinearMap.restrictScalars_injective k)
        have hM_pos : 0 < Module.finrank k (M →ₗ[R] ↥S₀) := by
          rw [Module.finrank_pos_iff (R := k)]
          exact ⟨_, _, hproj_ne⟩

        have hN_pos : 0 < Module.finrank k (N →ₗ[R] ↥S₀) := by
          rw [hhom] at hM_pos; exact hM_pos
        haveI : Module.Finite k (N →ₗ[R] ↥S₀) :=
          Module.Finite.of_injective
            (LinearMap.restrictScalarsₗ (S := R) (M := N) (N := ↥S₀) (R := k) (R₁ := k))
            (LinearMap.restrictScalars_injective k)
        rw [Module.finrank_pos_iff (R := k)] at hN_pos
        obtain ⟨f, g, hfg⟩ := hN_pos
        by_cases hf : f = 0
        · exact ⟨g, (fun h => hfg (hf.trans h.symm)),
            LinearMap.surjective_of_ne_zero (fun h => hfg (hf.trans h.symm))⟩
        · exact ⟨f, hf, LinearMap.surjective_of_ne_zero hf⟩

      obtain ⟨T₀, hNc⟩ := exists_isCompl (LinearMap.ker f)
      have eT₀S₀ : ↥T₀ ≃ₗ[R] ↥S₀ := by
        apply LinearEquiv.ofBijective (f.domRestrict T₀)
        refine ⟨?_, ?_⟩
        ·
          intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ hfxy
          ext
          have hfeq : f x₁ = f x₂ := by
            have := congrArg Subtype.val hfxy
            simp only [LinearMap.domRestrict_apply] at this
            exact Subtype.ext this
          have hdiff : x₁ - x₂ ∈ T₀ ⊓ LinearMap.ker f :=
            ⟨T₀.sub_mem hx₁ hx₂,
             LinearMap.mem_ker.mpr (by rw [map_sub, sub_eq_zero]; exact hfeq)⟩
          rw [hNc.symm.inf_eq_bot] at hdiff
          exact eq_of_sub_eq_zero (Submodule.mem_bot R |>.mp hdiff)
        ·
          intro ⟨s, hs⟩
          obtain ⟨n, hn⟩ := hf_surj ⟨s, hs⟩
          have hmem : (n : N) ∈ (LinearMap.ker f ⊔ T₀ : Submodule R N) :=
            hNc.sup_eq_top ▸ Submodule.mem_top
          obtain ⟨k_val, hk, t_val, ht, hsum⟩ := Submodule.mem_sup.mp hmem
          exact ⟨⟨t_val, ht⟩, Subtype.ext (by
            simp only [LinearMap.domRestrict_apply]
            have : f t_val = f n := by
              rw [show n = k_val + t_val from hsum.symm]
              simp [map_add, LinearMap.mem_ker.mp hk]
            rw [this, hn])⟩

      haveI : Module.Finite k ↥S₀ :=
        Module.Finite.of_injective (S₀.restrictScalars k).subtype Subtype.val_injective
      haveI : Module.Finite k ↥Q :=
        Module.Finite.of_injective (Q.restrictScalars k).subtype Subtype.val_injective
      haveI : Module.Finite k ↥(LinearMap.ker f) :=
        Module.Finite.of_injective ((LinearMap.ker f).restrictScalars k).subtype
          Subtype.val_injective

      have hQ_finrank : Module.finrank k ↥Q ≤ d := by
        have hdecomp : Module.finrank k M =
            Module.finrank k ↥S₀ + Module.finrank k ↥Q := by
          rw [← Module.finrank_prod,
            ((Submodule.prodEquivOfIsCompl S₀ Q hMc).restrictScalars k).finrank_eq]
        haveI : Nontrivial ↥S₀ := IsSimpleModule.nontrivial R ↥S₀
        have hS₀_pos : 0 < Module.finrank k ↥S₀ := Module.finrank_pos (R := k)
        omega

      have hQ_tors : Module.IsTorsionBySet R ↥Q ↑(Ring.jacobson R) :=
        fun {x} {a} => Subtype.ext (@hM_tors x.val a)
      have hKer_tors : Module.IsTorsionBySet R ↥(LinearMap.ker f) ↑(Ring.jacobson R) :=
        fun {x} {a} => Subtype.ext (@hN_tors x.val a)

      have hhom_QK : ∀ (S : Type u) [AddCommGroup S] [Module R S] [Module k S]
          [IsScalarTower k R S] [IsSimpleModule R S] [Module.Finite k S],
          Module.finrank k (↥Q →ₗ[R] S) =
          Module.finrank k (↥(LinearMap.ker f) →ₗ[R] S) := by
        intro S _ _ _ _ _ _

        have precomp_equiv {A B : Type u} [AddCommGroup A] [Module R A]
            [Module k A] [IsScalarTower k R A]
            [AddCommGroup B] [Module R B] [Module k B] [IsScalarTower k R B]
            (e : A ≃ₗ[R] B) :
            (B →ₗ[R] S) ≃ₗ[k] (A →ₗ[R] S) :=
          { toFun := fun g => g.comp e.toLinearMap
            invFun := fun g => g.comp e.symm.toLinearMap
            left_inv := fun g => by ext; simp
            right_inv := fun g => by ext; simp
            map_add' := fun g₁ g₂ => by ext; simp
            map_smul' := fun c g => by ext; simp }

        have eM : (M →ₗ[R] S) ≃ₗ[k]
            ((↥S₀ →ₗ[R] S) × (↥Q →ₗ[R] S)) :=
          (precomp_equiv (Submodule.prodEquivOfIsCompl S₀ Q hMc)).trans
            (LinearMap.coprodEquiv k).symm
        have eN : (N →ₗ[R] S) ≃ₗ[k]
            ((↥T₀ →ₗ[R] S) × (↥(LinearMap.ker f) →ₗ[R] S)) :=
          (precomp_equiv (Submodule.prodEquivOfIsCompl T₀ (LinearMap.ker f) hNc.symm)).trans
            (LinearMap.coprodEquiv k).symm
        have eTS : (↥T₀ →ₗ[R] S) ≃ₗ[k] (↥S₀ →ₗ[R] S) :=
          precomp_equiv eT₀S₀.symm

        haveI : Module.Finite k (M →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.restrictScalarsₗ (S := R) (M := M) (N := S) (R := k) (R₁ := k))
            (LinearMap.restrictScalars_injective k)
        haveI : Module.Finite k ((↥S₀ →ₗ[R] S) × (↥Q →ₗ[R] S)) :=
          Module.Finite.equiv eM
        haveI : Module.Finite k (↥S₀ →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.inl k (↥S₀ →ₗ[R] S) (↥Q →ₗ[R] S)) LinearMap.inl_injective
        haveI : Module.Finite k (↥Q →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.inr k (↥S₀ →ₗ[R] S) (↥Q →ₗ[R] S)) LinearMap.inr_injective
        haveI : Module.Finite k (N →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.restrictScalarsₗ (S := R) (M := N) (N := S) (R := k) (R₁ := k))
            (LinearMap.restrictScalars_injective k)
        haveI : Module.Finite k ((↥T₀ →ₗ[R] S) × (↥(LinearMap.ker f) →ₗ[R] S)) :=
          Module.Finite.equiv eN
        haveI : Module.Finite k (↥T₀ →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.inl k (↥T₀ →ₗ[R] S) (↥(LinearMap.ker f) →ₗ[R] S))
            LinearMap.inl_injective
        haveI : Module.Finite k (↥(LinearMap.ker f) →ₗ[R] S) :=
          Module.Finite.of_injective
            (LinearMap.inr k (↥T₀ →ₗ[R] S) (↥(LinearMap.ker f) →ₗ[R] S))
            LinearMap.inr_injective

        have hM_decomp : Module.finrank k (M →ₗ[R] S) =
            Module.finrank k (↥S₀ →ₗ[R] S) + Module.finrank k (↥Q →ₗ[R] S) := by
          rw [eM.finrank_eq, Module.finrank_prod]
        have hN_decomp : Module.finrank k (N →ₗ[R] S) =
            Module.finrank k (↥T₀ →ₗ[R] S) +
            Module.finrank k (↥(LinearMap.ker f) →ₗ[R] S) := by
          rw [eN.finrank_eq, Module.finrank_prod]
        have hT₀S₀ : Module.finrank k (↥T₀ →ₗ[R] S) =
            Module.finrank k (↥S₀ →ₗ[R] S) :=
          eTS.finrank_eq
        linarith [hhom S]

      obtain ⟨eQK⟩ := ih ↥Q ↥(LinearMap.ker f) hQ_finrank hQ_tors hKer_tors hhom_QK

      exact ⟨(Submodule.prodEquivOfIsCompl S₀ Q hMc).symm.trans
        ((LinearEquiv.prodCongr eT₀S₀.symm eQK).trans
          (Submodule.prodEquivOfIsCompl T₀ (LinearMap.ker f) hNc.symm))⟩

private theorem semisimple_iso_of_finrank_hom_eq
    {k : Type*} [Field k] [IsAlgClosed k]
    {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
    [IsSemiprimaryRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N]
    [Module.Finite R M] [Module.Finite R N]
    [Module.Finite k M] [Module.Finite k N]
    (hM_tors : Module.IsTorsionBySet R M (Ring.jacobson R))
    (hN_tors : Module.IsTorsionBySet R N (Ring.jacobson R))
    (hhom : ∀ (S : Type u) [AddCommGroup S] [Module R S] [Module k S] [IsScalarTower k R S]
      [IsSimpleModule R S] [Module.Finite k S],
      Module.finrank k (M →ₗ[R] S) = Module.finrank k (N →ₗ[R] S)) :
    Nonempty (M ≃ₗ[R] N) :=
  semisimple_iso_aux (Module.finrank k M) M N le_rfl hM_tors hN_tors hhom

private noncomputable def head_isomorphism [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₁) (_hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₂)
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) [F.functor.Linear k] :
    let Pt := (F.functor.obj (ModuleCat.of B₁ B₁) : Type u)
    let J₂ := Ring.jacobson B₂
    (Pt ⧸ (J₂ • ⊤ : Submodule B₂ Pt)) ≃ₗ[B₂]
    (B₂ ⧸ (J₂ • ⊤ : Submodule B₂ B₂)) := by
  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂
  haveI : IsArtinianRing B₁ := IsArtinianRing.of_finite k B₁
  set Pt : Type u := ↑(F.functor.obj (ModuleCat.of B₁ B₁))
  set J₂ := Ring.jacobson B₂
  set JP := (J₂ • ⊤ : Submodule B₂ Pt)
  set JB := (J₂ • ⊤ : Submodule B₂ B₂)

  have h_tors_P := Module.isTorsionBySet_quotient_ideal_smul Pt (Ring.jacobson B₂)
  haveI : IsSemisimpleModule B₂ (Pt ⧸ JP) := h_tors_P.isSemisimpleModule_iff.mp inferInstance
  have h_tors_B := Module.isTorsionBySet_quotient_ideal_smul B₂ (Ring.jacobson B₂)
  haveI : IsSemisimpleModule B₂ (B₂ ⧸ JB) := h_tors_B.isSemisimpleModule_iff.mp inferInstance
  haveI : Module.Finite B₂ Pt := RepresentationTheory.ModuleCat.Equivalence.Finite.ModuleCat.Equivalence.finite_image_regular F
  haveI : Module.Finite B₂ (Pt ⧸ JP) := inferInstance
  haveI : Module.Finite B₂ (B₂ ⧸ JB) := inferInstance
  haveI : Module.Finite k Pt := Module.Finite.trans B₂ Pt
  haveI : Module.Finite k (Pt ⧸ JP) := Module.Finite.quotient k JP
  haveI : Module.Finite k (B₂ ⧸ JB) := Module.Finite.quotient k JB
  haveI := equiv_inverse_linear F (k := k)
  haveI : IsSemiprimaryRing B₂ := inferInstance

  exact (semisimple_iso_of_finrank_hom_eq (k := k) (R := B₂) (Pt ⧸ JP) (B₂ ⧸ JB)
    h_tors_P h_tors_B (fun S _ _ _ _ _ _ => by

    have hS_ann : Ring.jacobson B₂ ≤ Module.annihilator B₂ S :=
      IsSemisimpleModule.jacobson_le_annihilator (R := B₂) (M := S)

    have hkill : ∀ {M : Type u} [AddCommGroup M] [Module B₂ M]
        (g : M →ₗ[B₂] S) (N : Submodule B₂ M),
        (Ring.jacobson B₂ • ⊤ : Submodule B₂ M) ≤ LinearMap.ker g := by
      intro M _ _ g _
      intro x hx
      rw [LinearMap.mem_ker]
      exact Submodule.smul_induction_on hx
        (fun j hj m _ => by rw [g.map_smul]; exact Module.mem_annihilator.mp (hS_ann hj) _)
        (fun a b ha hb => by rw [map_add, ha, hb, add_zero])

    have hom_equiv_mkQ : ∀ {M : Type u} [AddCommGroup M] [Module B₂ M]
        [Module k M] [IsScalarTower k B₂ M]
        (N : Submodule B₂ M) (hN : N = Ring.jacobson B₂ • ⊤),
        Module.finrank k (M ⧸ N →ₗ[B₂] S) = Module.finrank k (M →ₗ[B₂] S) := by
      intro M _ _ _ _ N hN
      apply LinearEquiv.finrank_eq
      exact {
        toFun := fun f => f.comp N.mkQ
        invFun := fun g => N.liftQ g (hN ▸ hkill g N)
        left_inv := fun f => LinearMap.ext fun x =>
          Submodule.Quotient.induction_on _ x (fun m => rfl)
        right_inv := fun g => LinearMap.ext fun x => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
      }

    have eval_B₂ : Module.finrank k (B₂ →ₗ[B₂] S) = Module.finrank k S :=
      (LinearMap.ringLmapEquivSelf B₂ k S).finrank_eq

    have hS_dim : Module.finrank k S = 1 := _hB₂ S

    have rhs : Module.finrank k ((B₂ ⧸ JB) →ₗ[B₂] S) = 1 := by
      rw [hom_equiv_mkQ JB rfl, eval_B₂, hS_dim]

    have lhs : Module.finrank k ((Pt ⧸ JP) →ₗ[B₂] S) = 1 := by
      rw [hom_equiv_mkQ JP rfl]

      set X := ModuleCat.of B₁ B₁
      set Y := ModuleCat.of B₂ S
      set GS := F.inverse.obj Y

      have hfull : Module.finrank k (Pt →ₗ[B₂] S) = Module.finrank k (↥GS) := by
        apply LinearEquiv.finrank_eq
        haveI : F.inverse.Additive := Equivalence.inverse_additive F

        let e1 : (Pt →ₗ[B₂] ↥Y) ≃ₗ[k] (F.functor.obj X ⟶ Y) :=
          (ModuleCat.homLinearEquiv (S := k)).symm

        let e2 : (F.functor.obj X ⟶ Y) ≃ₗ[k] (X ⟶ GS) := {
          toFun := F.toAdjunction.homEquiv X Y
          invFun := (F.toAdjunction.homEquiv X Y).symm
          left_inv := (F.toAdjunction.homEquiv X Y).left_inv
          right_inv := (F.toAdjunction.homEquiv X Y).right_inv
          map_add' := fun f g => by
            simp only [Adjunction.homEquiv_unit, F.inverse.map_add, Preadditive.comp_add]
          map_smul' := fun c f => by
            simp only [RingHom.id_apply]

            convert adj_homEquiv_smul F X Y c f using 1
            all_goals (congr 1; ext x; exact (algebraMap_smul B₂ c (f.hom x)).symm)
        }

        let e3 : (X ⟶ GS) ≃ₗ[k] (↥X →ₗ[B₁] ↥GS) :=
          ModuleCat.homLinearEquiv (S := k)

        let e4 : (↥X →ₗ[B₁] ↥GS) ≃ₗ[k] ↥GS :=
          LinearMap.ringLmapEquivSelf B₁ k ↥GS
        exact e1.trans (e2.trans (e3.trans e4))

      have hGS_dim : Module.finrank k (↥GS) = 1 := by
        haveI : Simple GS := simple_of_equiv_inverse F Y
        haveI : IsSimpleModule B₁ ↥GS := inferInstance
        exact _hB₁ ↥GS
      rw [hfull, hGS_dim]
    rw [lhs, rhs])).some

private noncomputable def exists_surjection_with_trivial_kernel_head [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₁) (_hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₂)
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) [F.functor.Linear k] :
    Σ' (f : (F.functor.obj (ModuleCat.of B₁ B₁)) →ₗ[B₂] B₂),
      Function.Surjective f ∧
      LinearMap.ker f ≤ Ring.jacobson B₂ • (LinearMap.ker f) := by
  haveI := equiv_image_projective F
  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂

  set Pt : Type u := ↑(F.functor.obj (ModuleCat.of B₁ B₁))
  set P := F.functor.obj (ModuleCat.of B₁ B₁) with hP_def
  set J₂ := Ring.jacobson B₂
  set JP := (J₂ • ⊤ : Submodule B₂ Pt) with hJP_def
  set JB := (J₂ • ⊤ : Submodule B₂ B₂) with hJB_def

  have head_iso : (Pt ⧸ JP) ≃ₗ[B₂] (B₂ ⧸ JB) :=
    head_isomorphism (k := k) B₁ B₂ _hB₁ _hB₂ F
  let g : Pt →ₗ[B₂] B₂ ⧸ JB := head_iso.toLinearMap.comp JP.mkQ
  have hg_surj : Function.Surjective g :=
    head_iso.surjective.comp (Submodule.mkQ_surjective JP)
  have hg_ker : LinearMap.ker g = JP := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply]
    exact (head_iso.map_eq_zero_iff).trans (Submodule.Quotient.mk_eq_zero JP)

  have hex_f := Module.projective_lifting_property JB.mkQ g (Submodule.mkQ_surjective _)
  let f : ↑P →ₗ[B₂] B₂ := hex_f.choose
  have hf : JB.mkQ ∘ₗ f = g := hex_f.choose_spec

  have hf_surj : Function.Surjective f := projective_lift_surjective hg_surj hf

  have hex_s := LinearMap.exists_rightInverse_of_surjective f
    (LinearMap.range_eq_top.mpr hf_surj)
  let s : B₂ →ₗ[B₂] ↑P := hex_s.choose
  have hs : f ∘ₗ s = LinearMap.id := hex_s.choose_spec

  have hker_le_JP : LinearMap.ker f ≤ JP := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hgx : g x = 0 := by rw [← hf, LinearMap.comp_apply, hx, map_zero]
    rw [← hg_ker]
    exact LinearMap.mem_ker.mpr hgx

  let proj : ↑P →ₗ[B₂] ↑P := LinearMap.id - s.comp f
  have hproj_ker : ∀ p : ↑P, proj p ∈ LinearMap.ker f := fun p => by
    rw [LinearMap.mem_ker]
    change f (proj p) = 0
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]

    have : (f ∘ₗ s) (f p) = f p := by rw [hs, LinearMap.id_apply]
    simp only [LinearMap.comp_apply] at this
    rw [this, sub_self]
  have hproj_id : ∀ x ∈ LinearMap.ker f, proj x = x := fun x hx => by
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hx, map_zero, sub_zero]
  have hker : LinearMap.ker f ≤ J₂ • LinearMap.ker f := by
    intro x hx

    rw [← hproj_id x hx]
    exact Submodule.smul_induction_on (hker_le_JP hx)
      (fun j hj p _ => by
        change proj (j • p) ∈ J₂ • LinearMap.ker f
        rw [proj.map_smul]
        exact Submodule.smul_mem_smul hj (hproj_ker p))
      (fun a b ha hb => by
        change proj (a + b) ∈ J₂ • LinearMap.ker f
        rw [map_add]
        exact Submodule.add_mem _ ha hb)
  exact ⟨f, hf_surj, hker⟩

private noncomputable def basic_morita_regular_module_iso [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₁) (_hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k B₂)
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) [F.functor.Linear k] :
    F.functor.obj (ModuleCat.of B₁ B₁) ≅ ModuleCat.of B₂ B₂ := by

  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂

  let ⟨f, hf_surj, hker⟩ :=
    exists_surjection_with_trivial_kernel_head B₁ B₂ _hB₁ _hB₂ F
  exact iso_of_surjection_with_trivial_kernel_head _ f hf_surj hker

private noncomputable instance equivFunctorAdditive
    {R : Type u} [Ring R] {S : Type u} [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) : E.functor.Additive := by
  haveI : E.functor.IsEquivalence := E.isEquivalence_functor
  exact Functor.additive_of_preserves_binary_products E.functor

private noncomputable def equivEndAlgEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    [F.functor.Additive] [F.functor.Linear k]
    (α : F.functor.obj (ModuleCat.of B₁ B₁) ≅ ModuleCat.of B₂ B₂) :
    Module.End B₁ B₁ ≃ₐ[k] Module.End B₂ B₂ := by
  let X := ModuleCat.of B₁ B₁
  let Y := ModuleCat.of B₂ B₂

  let fRing : End X ≃+* End (F.functor.obj X) := {
    F.fullyFaithfulFunctor.mulEquivEnd X with
    map_add' := fun _ _ => F.functor.map_add
  }

  let αRing : End (F.functor.obj X) ≃+* End Y := {
    α.conj with
    map_add' := fun f g => by
      change α.inv ≫ (f + g) ≫ α.hom =
        (α.inv ≫ f ≫ α.hom) + (α.inv ≫ g ≫ α.hom)
      rw [Preadditive.add_comp, Preadditive.comp_add]
  }

  let eB₁ := ModuleCat.endRingEquiv X
  let eB₂ := ModuleCat.endRingEquiv Y
  let re : Module.End B₁ B₁ ≃+* Module.End B₂ B₂ :=
    eB₁.symm.trans (fRing.trans (αRing.trans eB₂))

  exact AlgEquiv.ofRingEquiv (f := re) (fun c => by

    change re (algebraMap k (Module.End B₁ B₁) c) =
      algebraMap k (Module.End B₂ B₂) c
    simp only [Algebra.algebraMap_eq_smul_one]
    change eB₂ (αRing (fRing (eB₁.symm (c • 1)))) = c • 1

    have h1 : eB₁.symm (c • (1 : Module.End B₁ B₁)) =
        (c • (𝟙 X : X ⟶ X) : X ⟶ X) :=
      ModuleCat.hom_ext rfl

    change eB₂ (αRing (F.functor.map (eB₁.symm (c • (1 : Module.End B₁ B₁))))) = c • 1
    rw [h1]

    apply LinearMap.ext; intro x

    simp only [LinearMap.smul_apply]

    change (re (c • (1 : Module.End B₁ B₁))).toFun x = c • x

    change (αRing (fRing (eB₁.symm (c • (1 : Module.End B₁ B₁))))).hom x = c • x

    change (α.inv ≫ (fRing (eB₁.symm (c • (1 : Module.End B₁ B₁)))) ≫ α.hom).hom x = c • x
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]

    change α.hom.hom ((F.functor.map (eB₁.symm (c • (1 : Module.End B₁ B₁)))).hom
      (α.inv.hom x)) = c • x

    rw [h1]

    have hF := congrArg ModuleCat.Hom.hom
      (Functor.Linear.map_smul (F := F.functor) (R := k) (𝟙 X) c)

    simp only [F.functor.map_id, ModuleCat.hom_smul] at hF

    have key := Functor.Linear.map_smul (F := F.functor) (R := k) (𝟙 X) c
    simp only [F.functor.map_id] at key

    have smul_eq : (c • 𝟙 X : X ⟶ X) = @HSMul.hSMul k (X ⟶ X) (X ⟶ X)
        (@instHSMul k (X ⟶ X) (Linear.homModule X X).toSMul) c (𝟙 X) := by
      apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.id_apply]

      conv_lhs => rw [Algebra.smul_def]
      rfl

    have h_Fmap : ∀ y, (F.functor.map (c • 𝟙 X)).hom y = c • y := by
      intro y
      have h := congrArg F.functor.map smul_eq

      have := congrArg ModuleCat.Hom.hom (h.trans key)

      simp only [ModuleCat.hom_smul] at this
      exact LinearMap.congr_fun this y
    rw [h_Fmap]

    conv_lhs => rw [show c • α.inv.hom x = algebraMap k B₂ c • α.inv.hom x from by
      simp only [algebraMap_smul]]
    rw [map_smul]

    conv_rhs => rw [show c • x = algebraMap k B₂ c • x from by
      simp only [Algebra.smul_def, algebraMap_smul]]
    congr 1
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom α.inv_hom_id) x)

private lemma basic_morita_algEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B₁)
    (_hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B₂)
    (h : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k B₁ B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  obtain ⟨F, hlin⟩ := h
  haveI : F.functor.Additive :=
    letI : F.functor.IsEquivalence := F.isEquivalence_functor
    Functor.additive_of_preserves_binary_products F.functor
  haveI := hlin

  have hα := basic_morita_regular_module_iso B₁ B₂ _hB₁ _hB₂ F

  have hEnd := equivEndAlgEquiv (k := k) B₁ B₂ F hα

  have hB1op : B₁ᵐᵒᵖ ≃ₐ[k] Module.End B₁ B₁ :=
    AlgEquiv.moduleEndSelf (A := B₁) k
  have hB2op : B₂ᵐᵒᵖ ≃ₐ[k] Module.End B₂ B₂ :=
    AlgEquiv.moduleEndSelf (A := B₂) k

  have hOp : B₁ᵐᵒᵖ ≃ₐ[k] B₂ᵐᵒᵖ := hB1op.trans (hEnd.trans hB2op.symm)

  exact ⟨AlgEquiv.unop hOp⟩

/-- Under the stated hypotheses, the second algebra is algebra equivalent to a subtype of the first determined by an element. -/
theorem exists_algEquiv_subtype_associated_to_element [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (_hB : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B)
    (h : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty (@AlgEquiv k B (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) _ _
        (RepresentationTheory.RingTheory.Idempotent.submodule.ring he).toSemiring
        _ (@RepresentationTheory.RingTheory.Idempotent.submodule.algebra k _ A _ _ e he)) := by

  obtain ⟨e, he_full, hbasic_corner, _⟩ := RepresentationTheory.RingTheory.ElementProperties.exists_element_with_membership_subtype_conditions k A
  refine ⟨e, he_full.1, ?_⟩

  have hKLinCorner := RepresentationTheory.RingTheory.ElementProperties.membershipSubtype_has_indexed_condition_of_ringElementCondition (k := k) he_full

  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he_full.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he_full.1
  letI : Module.Finite k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.moduleFinite
  have hKLinBC : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k B (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
    h.symm.trans hKLinCorner

  have hbasic_corner' : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{_, _, u} k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
    fun M _ _ _ _ _ => hbasic_corner M
  exact basic_morita_algEquiv B (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) _hB hbasic_corner' hKLinBC

/-- The finrank of the module subtype associated to an element is at most the finrank of the ambient algebra. -/
theorem _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.finrank_associated_subtype_le
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (e : A) :
    Module.finrank k (RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e) ≤ Module.finrank k A :=
  RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule_finrank_le e

/-- The functor of an equivalence of module categories preserves the specified module predicate. -/
lemma module_predicate_equivalence_obj
    {B₁ : Type u} [Ring B₁] {B₂ : Type u} [Ring B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    {M : ModuleCat.{u} B₁}
    (hM : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate B₁ M) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate B₂ (F.functor.obj M) := by
  obtain ⟨hnt, hind⟩ := hM
  refine ⟨?_, ?_⟩
  ·
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h

    have hzFM : IsZero (F.functor.obj M) := ModuleCat.isZero_of_subsingleton _
    have hzM : IsZero M := by
      rw [IsZero.iff_id_eq_zero]
      apply F.functor.map_injective
      rw [F.functor.map_id, F.functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp hzFM
    exact (not_subsingleton_iff_nontrivial.mpr hnt) (ModuleCat.subsingleton_of_isZero hzM)
  ·
    intro W₁ W₂ hc

    let proj := Submodule.projectionOnto W₁ W₂ hc
    let p : (F.functor.obj M) →ₗ[B₂] (F.functor.obj M) :=
      W₁.subtype.comp proj
    have hp_idem : p.comp p = p := by
      ext x
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply]
      congr 1
      exact Submodule.projectionOnto_apply_left hc (proj x)

    let p_cat : F.functor.obj M ⟶ F.functor.obj M := ModuleCat.ofHom p

    let q_cat : M ⟶ M := F.functor.preimage p_cat

    have hq_map : F.functor.map q_cat = p_cat := F.functor.map_preimage p_cat
    have hp_idem_cat : p_cat ≫ p_cat = p_cat := by
      ext x; exact LinearMap.congr_fun hp_idem x
    have hq_idem_cat : q_cat ≫ q_cat = q_cat := by
      apply F.functor.map_injective
      simp only [F.functor.map_comp, hq_map, hp_idem_cat]

    let q : M →ₗ[B₁] M := q_cat.hom
    have hq_idem : IsIdempotentElem q := by
      ext x; exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hq_idem_cat) x

    have hcompl_q : IsCompl (LinearMap.range q) (LinearMap.ker q) :=
      open LinearMap in IsIdempotentElem.isCompl hq_idem
    rcases hind (LinearMap.range q) (LinearMap.ker q) hcompl_q with hrange | hker
    ·
      left
      have hq_zero : q = 0 := LinearMap.range_eq_bot.mp hrange
      have hp_zero : p = 0 := by
        have hp_cat_zero : p_cat = 0 := by
          rw [← hq_map]
          have : q_cat = 0 := ModuleCat.hom_ext_iff.mpr hq_zero
          rw [this, F.functor.map_zero]
        exact ModuleCat.hom_ext_iff.mp hp_cat_zero

      rw [eq_bot_iff]
      intro x hx
      have hp_x : p x = 0 := LinearMap.congr_fun hp_zero x

      have hproj := Submodule.projectionOnto_apply_left hc ⟨x, hx⟩

      have : p x = x := by
        change (W₁.subtype (proj x)) = x
        rw [hproj]; rfl
      rw [this] at hp_x
      exact hp_x
    ·
      right
      have hq_id : q = LinearMap.id := by
        ext x
        have hqx_mem : q x - x ∈ LinearMap.ker q := by
          rw [LinearMap.mem_ker, map_sub]
          have : q (q x) = q x := LinearMap.congr_fun (show q.comp q = q from hq_idem) x
          rw [this, sub_self]
        rw [hker, Submodule.mem_bot, sub_eq_zero] at hqx_mem
        rw [hqx_mem, LinearMap.id_apply]
      have hp_id : p = LinearMap.id := by
        have hp_cat_id : p_cat = 𝟙 _ := by
          rw [← hq_map, ← F.functor.map_id]
          congr 1
          exact ModuleCat.hom_ext_iff.mpr hq_id
        exact ModuleCat.hom_ext_iff.mp hp_cat_id

      have hW1_top : W₁ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hpx : p x = x := LinearMap.congr_fun hp_id x
        have : W₁.subtype (proj x) = x := hpx
        rw [Submodule.subtype_apply] at this
        have hmem := (proj x).2
        rwa [this] at hmem
      exact eq_bot_of_isCompl_top (hW1_top ▸ hc.symm)

end RepresentationTheory.MoritaEquivalence
