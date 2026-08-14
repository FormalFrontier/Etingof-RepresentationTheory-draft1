import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Order.KrullDimension

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.NoetherianObjects

variable {C : Type u} [Category.{v} C]

/-- An object is Noetherian when its poset of subobjects has finite dimension. -/
theorem isNoetherianObject_of_finiteDimensionalOrder_subobject (X : C)
    [FiniteDimensionalOrder (Subobject X)] : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  have h1 : Order.krullDim ℕ ≤ Order.krullDim (Subobject X) :=
    Order.krullDim_le_of_strictMono f hf
  rw [Order.krullDim_nat] at h1
  exact Order.krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp h1)

end RepresentationTheory.CategoryTheory.NoetherianObjects

namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  {P : C}

/-- For each object, there are a parameter and a morphism that is an epimorphism. -/
theorem IsProjectiveEpiSigmaDesc.exists_epi
    (h : IsProjectiveEpiSigmaDesc P) (X : C) :
    ∃ (n : ℕ) (φ : (⨁ fun _ : Fin n => P) ⟶ X), Epi φ := by
  haveI : IsNoetherianObject X :=
    NoetherianObjects.isNoetherianObject_of_finiteDimensionalOrder_subobject X
  let S : Set (Subobject X) :=
    fun Y => ∃ (n : ℕ) (v : Fin n → (P ⟶ X)), imageSubobject (biproduct.desc v) = Y
  have hSne : S.Nonempty :=
    ⟨imageSubobject (biproduct.desc (finZeroElim : Fin 0 → (P ⟶ X))), 0, finZeroElim, rfl⟩
  obtain ⟨m, ⟨n₀, v₀, hm⟩, hmax⟩ := wellFounded_gt.has_min S hSne
  by_cases hmtop : m = ⊤
  · refine ⟨n₀, biproduct.desc v₀, ?_⟩
    have htop : imageSubobject (biproduct.desc v₀) = ⊤ := hm.trans hmtop
    haveI : IsIso (imageSubobject (biproduct.desc v₀)).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]; exact htop
    have hfac := imageSubobject_arrow_comp (biproduct.desc v₀)
    rw [← hfac]
    exact epi_comp _ _
  · exfalso
    let π : X ⟶ cokernel m.arrow := cokernel.π m.arrow
    have hcoker_ne : ¬ IsZero (cokernel m.arrow) := by
      intro hz
      have hπ0 : cokernel.π m.arrow = 0 := hz.eq_of_tgt _ _
      haveI : Epi m.arrow := Abelian.epi_of_cokernel_π_eq_zero _ hπ0
      haveI : IsIso m.arrow := isIso_of_mono_of_epi m.arrow
      exact hmtop (Subobject.eq_top_of_isIso_arrow m)
    have hsep : IsSeparator P := h.2
    obtain ⟨g, hg⟩ : ∃ g : P ⟶ cokernel m.arrow, g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hcoker_ne
      rw [Preadditive.isSeparator_iff] at hsep
      have hid : 𝟙 (cokernel m.arrow) = 0 :=
        hsep _ (fun hh => by rw [Category.comp_id, hcon hh])
      exact (IsZero.iff_id_eq_zero _).mpr hid
    haveI : Projective P := h.1
    let glift : P ⟶ X := Projective.factorThru g π
    have hlift : glift ≫ π = g := Projective.factorThru_comp g π
    let v₁ : Fin (n₀ + 1) → (P ⟶ X) := Fin.cons glift v₀
    let φ₁ := biproduct.desc v₁
    have hmemφ₁ : imageSubobject φ₁ ∈ S := ⟨n₀ + 1, v₁, rfl⟩
    let incl : (⨁ fun _ : Fin n₀ => P) ⟶ (⨁ fun _ : Fin (n₀ + 1) => P) :=
      biproduct.desc (fun i => biproduct.ι (fun _ : Fin (n₀ + 1) => P) i.succ)
    have hfac : biproduct.desc v₀ = incl ≫ φ₁ := by
      refine biproduct.hom_ext' _ _ (fun i => ?_)
      simp only [incl, φ₁, v₁, biproduct.ι_desc, biproduct.ι_desc_assoc, Fin.cons_succ]
    have hle : m ≤ imageSubobject φ₁ := by
      rw [← hm, hfac]
      exact imageSubobject_comp_le incl φ₁
    have hne : m ≠ imageSubobject φ₁ := by
      intro heq
      have hφ₁le : imageSubobject φ₁ ≤ m := heq.ge
      have hgliftfac : biproduct.ι (fun _ : Fin (n₀ + 1) => P) 0 ≫ φ₁ = glift := by
        simp only [φ₁, v₁, biproduct.ι_desc, Fin.cons_zero]
      have hgliftle : imageSubobject glift ≤ m := by
        calc imageSubobject glift
            = imageSubobject (biproduct.ι (fun _ : Fin (n₀ + 1) => P) 0 ≫ φ₁) := by rw [hgliftfac]
          _ ≤ imageSubobject φ₁ := imageSubobject_comp_le _ _
          _ ≤ m := hφ₁le
      let k : P ⟶ (m : C) := factorThruImageSubobject glift ≫ Subobject.ofLE _ _ hgliftle
      have hk : k ≫ m.arrow = glift := by
        simp only [k, Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
      have : g = 0 := by
        rw [← hlift, ← hk, Category.assoc]
        rw [show m.arrow ≫ π = 0 from cokernel.condition m.arrow, comp_zero]
      exact hg this
    exact hmax (imageSubobject φ₁) hmemφ₁ (lt_of_le_of_ne hle hne)

/-- The hypothesis on P implies the target property. -/
theorem IsProjectiveEpiSigmaDesc.implies_property (h : IsProjectiveEpiSigmaDesc P) :
    HasProjectiveEpiWitnesses P :=
  { toProjective := h.1
    exists_epi := fun X => by
      obtain ⟨n, φ, hφ⟩ := h.exists_epi X
      exact ⟨n, inferInstance, φ, hφ⟩ }

end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
