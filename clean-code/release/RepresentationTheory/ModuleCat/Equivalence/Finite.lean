import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki

universe u

open CategoryTheory

namespace RepresentationTheory.ModuleCat.Equivalence.Finite

/-- An equivalence between module categories over Artinian rings sends the regular module to a
finite module. -/
theorem ModuleCat.Equivalence.finite_image_regular
    {B₁ : Type u} [Ring B₁] [IsArtinianRing B₁]
    {B₂ : Type u} [Ring B₂] [IsArtinianRing B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) :
    Module.Finite B₂ (F.functor.obj (ModuleCat.of B₁ B₁)) := by
  set P := F.functor.obj (ModuleCat.of B₁ B₁)
  set η := F.unitIso.app (ModuleCat.of B₁ B₁) with hη_def
  let Φ : Submodule B₂ ↑P → Submodule B₁ B₁ := fun N =>
    Submodule.comap η.hom.hom (LinearMap.range (F.inverse.map (ModuleCat.ofHom N.subtype)).hom)
  have hΦ_mono : Monotone Φ := by
    intro N₁ N₂ h
    apply Submodule.comap_mono
    have h_factor : ModuleCat.ofHom N₁.subtype =
        ModuleCat.ofHom (Submodule.inclusion h) ≫ ModuleCat.ofHom N₂.subtype := by
      ext x; rfl
    rw [h_factor, Functor.map_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  have hΦ_inj : Function.Injective Φ := by
    intro N₁ N₂ hΦ
    have hη_surj : Function.Surjective η.hom.hom :=
      (ModuleCat.epi_iff_surjective η.hom).mp inferInstance
    have h_range_eq : LinearMap.range (F.inverse.map (ModuleCat.ofHom N₁.subtype)).hom =
        LinearMap.range (F.inverse.map (ModuleCat.ofHom N₂.subtype)).hom :=
      Submodule.comap_injective_of_surjective hη_surj hΦ
    suffices h_le : ∀ (A B : Submodule B₂ ↑P),
        LinearMap.range (F.inverse.map (ModuleCat.ofHom A.subtype)).hom =
        LinearMap.range (F.inverse.map (ModuleCat.ofHom B.subtype)).hom →
        A ≤ B from
      le_antisymm (h_le N₁ N₂ h_range_eq) (h_le N₂ N₁ h_range_eq.symm)
    intro A B h_rng x hx
    have h_inj_B : Function.Injective (F.inverse.map (ModuleCat.ofHom B.subtype)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    set GιA := (F.inverse.map (ModuleCat.ofHom A.subtype)).hom
    set GιB := (F.inverse.map (ModuleCat.ofHom B.subtype)).hom
    let σ_hom : (F.inverse.obj (ModuleCat.of B₂ ↑A) : Type u) →ₗ[B₁]
        (F.inverse.obj (ModuleCat.of B₂ ↑B) : Type u) :=
      (LinearEquiv.ofInjective GιB h_inj_B).symm.toLinearMap.comp
        (GιA.codRestrict (LinearMap.range GιB) (fun a => h_rng ▸ LinearMap.mem_range_self GιA a))
    have h_σ_comm : ∀ a, GιB (σ_hom a) = GιA a := by
      intro a
      change GιB ((LinearEquiv.ofInjective GιB h_inj_B).symm
        ⟨GιA a, h_rng ▸ LinearMap.mem_range_self GιA a⟩) = GιA a
      have := (LinearEquiv.ofInjective GιB h_inj_B).apply_symm_apply
        ⟨GιA a, h_rng ▸ LinearMap.mem_range_self GιA a⟩
      exact congr_arg Subtype.val this
    let τ : ModuleCat.of B₂ ↑A ⟶ ModuleCat.of B₂ ↑B :=
      F.fullyFaithfulInverse.preimage (ModuleCat.ofHom σ_hom)
    have h_G_τ : F.inverse.map τ = ModuleCat.ofHom σ_hom :=
      F.fullyFaithfulInverse.map_preimage (ModuleCat.ofHom σ_hom)
    have h_G_eq : F.inverse.map (τ ≫ ModuleCat.ofHom B.subtype) =
        F.inverse.map (ModuleCat.ofHom A.subtype) := by
      simp only [Functor.map_comp, h_G_τ]
      ext a
      exact h_σ_comm a
    have h_eq : τ ≫ ModuleCat.ofHom B.subtype = ModuleCat.ofHom A.subtype :=
      F.inverse.map_injective h_G_eq
    have h_val : (τ.hom ⟨x, hx⟩ : ↑P) = x := by
      have h1 : (τ ≫ ModuleCat.ofHom B.subtype).hom ⟨x, hx⟩ =
          (ModuleCat.ofHom A.subtype).hom ⟨x, hx⟩ := by rw [h_eq]
      simpa using h1
    rw [← h_val]; exact (τ.hom ⟨x, hx⟩).2
  have hΦ_strict : StrictMono Φ :=
    hΦ_mono.strictMono_of_injective hΦ_inj
  haveI : IsArtinian B₂ ↑P := hΦ_strict.wellFoundedLT
  haveI : IsNoetherian B₂ ↑P := IsSemiprimaryRing.isNoetherian_iff_isArtinian.mpr ‹_›
  exact inferInstance

end RepresentationTheory.ModuleCat.Equivalence.Finite
