/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.RingAuxiliary
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Span

universe u

open CategoryTheory Limits

namespace RepresentationTheory.ModuleCat.FiniteUnderEquivalence

/-- A ring regarded as its regular module is a separator in its module category. -/
lemma isSeparator_regularModule (R : Type u) [Ring R] :
    IsSeparator (ModuleCat.of.{u} R R) := fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff,
    ModuleCat.hom_comp, LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply,
    forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)) 1

/-- An additive functor sends a finite biproduct to a finite module when each component image is finite. -/
lemma moduleFinite_obj_biproduct {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {n : ℕ} (f : Fin n → ModuleCat.{u} R)
    (h : ∀ i, Module.Finite S (F.obj (f i))) :
    Module.Finite S (F.obj (⨁ f)) := by
  haveI : ∀ i, Module.Finite S ((F.obj ∘ f) i) := h
  let e : F.obj (⨁ f) ≅ ModuleCat.of S (∀ i, (F.obj ∘ f) i) :=
    (F.mapBiproduct f).trans (ModuleCat.biproductIsoPi _)
  haveI : Module.Finite S (∀ i, (F.obj ∘ f) i) := inferInstance
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- The inverse image of the regular module under an equivalence of module categories is finite. -/
lemma moduleFinite_equivalence_inverse_obj_regular {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Finite R (E.inverse.obj (ModuleCat.of.{u} S S)) := by
  haveI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI : E.inverse.Additive := Equivalence.inverse_additive E
  haveI : Functor.PreservesEpimorphisms E.inverse :=
    Functor.preservesEpimorphisms_of_adjunction E.symm.toAdjunction
  set G := E.functor.obj (ModuleCat.of.{u} R R) with hG
  have hsep : IsSeparator G := (isSeparator_regularModule R).of_equivalence E
  set N : Submodule S (ModuleCat.of.{u} S S) :=
    ⨆ (φ : G ⟶ ModuleCat.of.{u} S S), LinearMap.range φ.hom with hN
  have hNtop : N = ⊤ := by
    have hmkQ : ModuleCat.ofHom N.mkQ = (0 : ModuleCat.of.{u} S S ⟶ ModuleCat.of S (_ ⧸ N)) := by
      refine hsep _ _ (fun G' hG' hh => ?_)
      obtain rfl := (ObjectProperty.singleton_iff G G').mp hG'
      apply ModuleCat.hom_ext
      ext x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      refine (Submodule.Quotient.mk_eq_zero N).mpr ?_
      exact le_iSup (fun φ : G ⟶ ModuleCat.of.{u} S S => LinearMap.range φ.hom) hh
        (LinearMap.mem_range_self hh.hom x)
    have hzero : N.mkQ = 0 := by
      have := congrArg ModuleCat.Hom.hom hmkQ
      simpa using this
    refine Submodule.eq_top_iff'.mpr (fun s => ?_)
    have : N.mkQ s = 0 := by rw [hzero]; rfl
    exact (Submodule.Quotient.mk_eq_zero N).mp this
  have h1 : (1 : (ModuleCat.of.{u} S S : Type u)) ∈ N := hNtop ▸ Submodule.mem_top
  rw [hN] at h1
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.mp h1
  obtain ⟨μ, hμ⟩ :=
    (Submodule.mem_iSup_finset_iff_exists_sum
      (fun φ : G ⟶ ModuleCat.of.{u} S S => LinearMap.range φ.hom) 1).mp ht
  set n := t.card with hn
  let e := (t.equivFin)
  let g : Fin n → (G ⟶ ModuleCat.of.{u} S S) := fun i => ((e.symm i : {x // x ∈ t}) : G ⟶ _)
  have hx : ∀ i : Fin n, ∃ y : (G : Type u),
      (g i).hom y = (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u)) :=
    fun i => LinearMap.mem_range.mp (μ (g i)).2
  choose x hx using hx
  have hsum1 : (∑ i : Fin n, ((μ (g i)).1 : (ModuleCat.of.{u} S S : Type u))) = 1 := by
    have hre : (∑ i : Fin n, ((μ (g i)).1 : (ModuleCat.of.{u} S S : Type u)))
        = ∑ φ : {x // x ∈ t}, ((μ (↑φ : G ⟶ ModuleCat.of.{u} S S)).1 : (ModuleCat.of.{u} S S : Type u)) :=
      Fintype.sum_equiv e.symm _ _ (fun i => rfl)
    rw [hre, Finset.sum_coe_sort t (fun φ => ((μ φ).1 : (ModuleCat.of.{u} S S : Type u)))]
    exact hμ
  let Φ : (⨁ fun _ : Fin n => G) ⟶ ModuleCat.of.{u} S S := biproduct.desc g
  let z := ∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i)
  have hΦz : Φ.hom z = 1 := by
    have hstep : ∀ i : Fin n,
        Φ.hom ((biproduct.ι (fun _ : Fin n => G) i).hom (x i))
          = (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u)) := by
      intro i
      have hid : biproduct.ι (fun _ : Fin n => G) i ≫ Φ = g i := biproduct.ι_desc g i
      have := congrArg (fun m : G ⟶ ModuleCat.of.{u} S S => m.hom (x i)) hid
      simpa [ModuleCat.hom_comp] using this.trans (hx i)
    change Φ.hom (∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i)) = 1
    calc Φ.hom (∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i))
        = ∑ i : Fin n, Φ.hom ((biproduct.ι (fun _ : Fin n => G) i).hom (x i)) := by
          rw [map_sum]
      _ = ∑ i : Fin n, (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u) ) :=
          Finset.sum_congr rfl (fun i _ => hstep i)
      _ = 1 := hsum1
  have hsurj : Function.Surjective Φ.hom := by
    intro s
    exact ⟨s • z, by rw [map_smul, hΦz, smul_eq_mul, mul_one]⟩
  haveI hepi : Epi Φ := (ModuleCat.epi_iff_surjective Φ).mpr hsurj
  haveI : Epi (E.inverse.map Φ) := inferInstance
  haveI hdom : Module.Finite R (E.inverse.obj (⨁ fun _ : Fin n => G)) := by
    apply moduleFinite_obj_biproduct E.inverse (fun _ : Fin n => G)
    intro i
    have hiso : ModuleCat.of.{u} R R ≅ E.inverse.obj G := E.unitIso.app (ModuleCat.of.{u} R R)
    exact Module.Finite.equiv hiso.toLinearEquiv
  have hsurj2 : Function.Surjective (E.inverse.map Φ).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (E.inverse.map Φ).hom hsurj2

/-- An additive epimorphism-preserving functor sends every finite module to a finite module if it does so for the regular module. -/
lemma moduleFinite_obj_of_moduleFinite_obj_regular {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [Functor.PreservesEpimorphisms F]
    (hreg : Module.Finite S (F.obj (ModuleCat.of.{u} R R)))
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S (F.obj M) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let p : (⨁ fun _ : Fin n => ModuleCat.of.{u} R R) ⟶ M :=
    biproduct.desc (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R M (s i)))
  have hptop : LinearMap.range p.hom = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hid : biproduct.ι (fun _ : Fin n => ModuleCat.of.{u} R R) i ≫ p
        = ModuleCat.ofHom (LinearMap.toSpanSingleton R M (s i)) := biproduct.ι_desc _ i
    refine ⟨(biproduct.ι (fun _ : Fin n => ModuleCat.of.{u} R R) i).hom 1, ?_⟩
    have hcongr := congrArg (fun m : ModuleCat.of.{u} R R ⟶ M => m.hom 1) hid
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul] at hcongr
    exact hcongr
  haveI hepi : Epi p := (ModuleCat.epi_iff_range_eq_top p).mpr hptop
  haveI : Epi (F.map p) := inferInstance
  haveI : Module.Finite S (F.obj (⨁ fun _ : Fin n => ModuleCat.of.{u} R R)) := by
    apply moduleFinite_obj_biproduct F (fun _ : Fin n => ModuleCat.of.{u} R R)
    intro _; exact hreg
  have hsurj : Function.Surjective (F.map p).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (F.map p).hom hsurj

/-- The image of the regular module under an equivalence of module categories is finite. -/
lemma moduleFinite_equivalence_functor_obj_regular {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Finite S (E.functor.obj (ModuleCat.of.{u} R R)) := by
  exact moduleFinite_equivalence_inverse_obj_regular E.symm

/-- A module is finite exactly when its image under an equivalence of module categories is finite. -/
lemma moduleFinite_equivalence_functor_obj_iff {A B : Type u} [Ring A] [Ring B]
    (E : ModuleCat.{u} A ≌ ModuleCat.{u} B) (M : ModuleCat.{u} A) :
    Module.Finite B (E.functor.obj M) ↔ Module.Finite A M := by
  haveI hFadd : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI hIadd : E.inverse.Additive := Equivalence.inverse_additive E
  haveI : Functor.PreservesEpimorphisms E.functor :=
    Functor.preservesEpimorphisms_of_adjunction E.toAdjunction
  haveI : Functor.PreservesEpimorphisms E.inverse :=
    Functor.preservesEpimorphisms_of_adjunction E.symm.toAdjunction
  constructor
  · intro hEM
    haveI : Module.Finite B (E.functor.obj M) := hEM
    haveI hfin : Module.Finite A ((E.functor ⋙ E.inverse).obj M) :=
      moduleFinite_obj_of_moduleFinite_obj_regular E.inverse
        (moduleFinite_equivalence_inverse_obj_regular E) (E.functor.obj M)
    exact Module.Finite.equiv (E.unitIso.app M).symm.toLinearEquiv
  · intro hM
    haveI : Module.Finite A M := hM
    exact moduleFinite_obj_of_moduleFinite_obj_regular E.functor
      (moduleFinite_equivalence_functor_obj_regular E) M

/-- The property of being a finitely generated module is closed under isomorphisms. -/
instance isFG_isClosedUnderIsomorphisms (R : Type u) [Ring R] :
    (ModuleCat.isFG.{u} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    haveI : Module.Finite R X := hX
    exact Module.Finite.equiv e.toLinearEquiv

end RepresentationTheory.ModuleCat.FiniteUnderEquivalence

namespace RepresentationTheory.RingAuxiliary

/-- The designated relation between two rings yields an equivalence of their finitely generated module categories. -/
theorem RingAuxiliary.exists_fgModuleCatEquivalence {A B : Type u} [Ring A] [Ring B]
    (h : RingAuxiliary A B) :
    Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} B) := by
  obtain ⟨E⟩ := h
  have hobj : (ModuleCat.isFG.{u} B).inverseImage E.functor = ModuleCat.isFG.{u} A := by
    funext M
    apply propext
    exact RepresentationTheory.ModuleCat.FiniteUnderEquivalence.moduleFinite_equivalence_functor_obj_iff E M
  exact ⟨E.congrFullSubcategory hobj⟩

/-- The designated relation between two rings implies the auxiliary ring property. -/
theorem RingAuxiliary.toAuxiliaryRingProperty {A B : Type u} [Ring A] [Ring B]
    (h : RingAuxiliary A B) : RingAuxiliary' A B :=
  RingAuxiliary.exists_fgModuleCatEquivalence h

/-- The designated relation between two algebras implies the auxiliary algebra relation. -/
theorem AlgebraAuxiliary.toAuxiliaryAlgebraProperty {k : Type u} [Field k]
    {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary k A B) : AlgebraAuxiliary' k A B := by
  obtain ⟨E, hlin⟩ := h
  haveI := hlin
  have hobj : (ModuleCat.isFG.{u} B).inverseImage E.functor = ModuleCat.isFG.{u} A := by
    funext M; exact propext
      (RepresentationTheory.ModuleCat.FiniteUnderEquivalence.moduleFinite_equivalence_functor_obj_iff E M)
  refine ⟨E.congrFullSubcategory hobj, ⟨fun {X Y} f r => ?_⟩⟩
  apply (ModuleCat.isFG.{u} B).ι.map_injective
  change E.functor.map ((ModuleCat.isFG.{u} A).ι.map (r • f))
      = (ModuleCat.isFG.{u} B).ι.map (r • (E.congrFullSubcategory hobj).functor.map f)
  simp only [Functor.Linear.map_smul]
  rfl

end RepresentationTheory.RingAuxiliary
