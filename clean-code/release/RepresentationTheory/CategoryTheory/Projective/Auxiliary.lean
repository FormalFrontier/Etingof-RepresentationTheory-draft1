/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import RepresentationTheory.CategoryTheory.Abelian.SubobjectLength
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary results for projective objects

This module relates epimorphisms from finite biproducts of a projective object to nonzero
morphisms from that object to simple objects. It also constructs an object carrying the resulting
epimorphism-witness property.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Projective.Auxiliary

variable {C : Type u} [Category.{v} C]

/-- A biproduct of projective objects is projective. -/
theorem projective_biproduct {β : Type*} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g]
    [∀ b, Projective (g b)] : Projective (biproduct g) where
  factors f e _ :=
    ⟨biproduct.desc fun b => Projective.factorThru (biproduct.ι g b ≫ f) e, by
      refine biproduct.hom_ext' _ _ (fun b => ?_)
      simp [Projective.factorThru_comp]⟩

/-- A projective object admits epimorphisms under nonzero-morphism hypotheses for all simple
objects. -/
theorem projective_exists_epi_of_forall_simple_exists_ne_zero
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
    (P : C) [Projective P] (hHom : ∀ (L : C), Simple L → ∃ f : P ⟶ L, f ≠ 0) (X : C) :
    ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
      (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f := by
  haveI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  suffices key : ∀ n, ∀ X : C,
      RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X = n →
      ∃ (m : ℕ) (_ : HasBiproduct (fun _ : Fin m => P))
        (f : biproduct (fun _ : Fin m => P) ⟶ X), Epi f by
    exact key (RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X) X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro X hX
    by_cases hz : IsZero X
    · refine ⟨0, inferInstance, 0, ⟨fun g h _ => hz.eq_of_src g h⟩⟩
    · haveI : IsArtinianObject X :=
        isArtinianObject.is_of_prop
          (RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.subobject_wellFoundedLT
            (X := X))
      set S : C := simpleSubobject hz with hSdef
      set i : S ⟶ X := simpleSubobjectArrow hz with hidef
      haveI : Simple S := inferInstance
      haveI : Mono i := inferInstance
      set q : X ⟶ cokernel i := cokernel.π i with hqdef
      have hSE : (ShortComplex.cokernelSequence i).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
          (inferInstanceAs (Mono i)) (inferInstanceAs (Epi (cokernel.π i)))
      have hadd :
          RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X =
            RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength S +
              RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength
                (cokernel i) := by
        simpa using
          RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_shortExact hSE
      have hS1 :
          RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength S = 1 :=
        RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_eq_one_of_simple
          inferInstance
      have hnpos : 0 < n := hX ▸
        RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_pos_of_not_isZero
          hz
      have hQlt :
          RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength (cokernel i) <
            n := by
        rw [hS1] at hadd; omega
      obtain ⟨m, hbpm, πQ, hπQ⟩ := IH _ hQlt (cokernel i) rfl
      haveI : HasBiproduct (fun _ : Fin m => P) := hbpm
      haveI : ∀ b : Fin m, Projective ((fun _ : Fin m => P) b) := fun _ => inferInstance
      haveI : Projective (biproduct (fun _ : Fin m => P)) := projective_biproduct _
      haveI : Epi πQ := hπQ
      set a : biproduct (fun _ : Fin m => P) ⟶ X := Projective.factorThru πQ q with hadef
      have ha_comp : a ≫ q = πQ := Projective.factorThru_comp πQ q
      obtain ⟨g, hg⟩ := hHom S inferInstance
      haveI : Epi g := epi_of_nonzero_to_simple hg
      set b : P ⟶ X := g ≫ i with hbdef
      set p : Fin (m + 1) → (P ⟶ X) :=
        Fin.lastCases b (fun k => biproduct.ι (fun _ : Fin m => P) k ≫ a) with hpdef
      refine ⟨m + 1, inferInstance, biproduct.desc p, ?_⟩
      apply Abelian.epi_of_cokernel_π_eq_zero
      set π₀ : X ⟶ cokernel (biproduct.desc p) := cokernel.π (biproduct.desc p) with hπ₀def
      have hcπ : biproduct.desc p ≫ π₀ = 0 := cokernel.condition _
      have hb : b ≫ π₀ = 0 := by
        have h1 :
            biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫ biproduct.desc p = b := by
          simp [hpdef]
        calc
          b ≫ π₀ =
              (biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫ biproduct.desc p) ≫
                π₀ := by rw [h1]
          _ = biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫
              (biproduct.desc p ≫ π₀) := by rw [Category.assoc]
          _ = 0 := by rw [hcπ, comp_zero]
      have hi : i ≫ π₀ = 0 := by
        have hgi : g ≫ (i ≫ π₀) = 0 := by rw [← Category.assoc]; exact hb
        exact (cancel_epi g).1 (by rw [hgi, comp_zero])
      have ha : a ≫ π₀ = 0 := by
        refine biproduct.hom_ext' _ _ (fun k => ?_)
        have h2 :
            biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫ biproduct.desc p =
              biproduct.ι (fun _ : Fin m => P) k ≫ a := by
          simp [hpdef]
        calc
          biproduct.ι (fun _ : Fin m => P) k ≫ (a ≫ π₀) =
              (biproduct.ι (fun _ : Fin m => P) k ≫ a) ≫ π₀ := by rw [Category.assoc]
          _ = (biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫ biproduct.desc p) ≫
              π₀ := by rw [h2]
          _ = biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫
              (biproduct.desc p ≫ π₀) := by rw [Category.assoc]
          _ = biproduct.ι (fun _ : Fin m => P) k ≫ 0 := by
            rw [hcπ, comp_zero, comp_zero]
      set π' : cokernel i ⟶ cokernel (biproduct.desc p) := cokernel.desc i π₀ hi with hπ'def
      have hfact : q ≫ π' = π₀ := cokernel.π_desc i π₀ hi
      have hπQ' : πQ ≫ π' = 0 := by
        have : a ≫ (q ≫ π') = 0 := by rw [hfact]; exact ha
        rwa [← Category.assoc, ha_comp] at this
      have hπ'zero : π' = 0 := (cancel_epi πQ).1 (by rw [hπQ', comp_zero])
      rw [← hfact, hπ'zero, comp_zero]

/-- For a projective object, nonemptiness of its auxiliary type is equivalent to the existence of
a nonzero morphism for every simple object. -/
@[source_ref "Chapter9/Exercise9.6.3" (role := supporting)]
theorem nonempty_auxiliary_iff_forall_simple_exists_ne_zero
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
    (P : C) [Projective P] :
    Nonempty
        (RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) ↔
      ∀ (L : C), Simple L → ∃ f : P ⟶ L, f ≠ 0 := by
  constructor
  · rintro ⟨hpg⟩ L hL
    haveI : Simple L := hL
    obtain ⟨n, hbp, f, hf⟩ := hpg.exists_epi L
    haveI : HasBiproduct (fun _ : Fin n => P) := hbp
    haveI : Epi f := hf
    have hfne : f ≠ 0 := by
      rintro rfl
      have : 𝟙 L = 0 := (cancel_epi (0 : biproduct (fun _ : Fin n => P) ⟶ L)).1 (by simp)
      exact id_nonzero L this
    have : ∃ k, biproduct.ι (fun _ : Fin n => P) k ≫ f ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hfne (biproduct.hom_ext' _ _ (fun k => by rw [hc k, comp_zero]))
    obtain ⟨k, hk⟩ := this
    exact ⟨_, hk⟩
  · intro hHom
    exact
      ⟨{ toProjective := inferInstance
         exists_epi := fun X =>
           projective_exists_epi_of_forall_simple_exists_ne_zero P hHom X }⟩

/-- There exists an object whose associated auxiliary type is nonempty. -/
@[source_ref "Chapter9/Exercise9.6.3" (role := supporting)]
theorem exists_object_with_nonempty_auxiliary (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] :
    ∃ P : C,
      Nonempty
        (RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) := by
  haveI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  haveI : Fintype
      (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary C) :=
    RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.fintype
  set Pi :
      RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary C →
        C :=
    fun i =>
      Projective.over
        (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object i) with
    hPidef
  haveI : HasBiproduct Pi := inferInstance
  haveI : ∀ b, Projective (Pi b) := fun _ => inferInstance
  haveI : Projective (biproduct Pi) := projective_biproduct _
  refine ⟨biproduct Pi, ?_⟩
  rw [nonempty_auxiliary_iff_forall_simple_exists_ne_zero]
  intro L hL
  haveI : Simple L := hL
  obtain ⟨j, ⟨e⟩⟩ :=
    RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.simple_iso_auxiliaryObject
      L hL
  refine
    ⟨biproduct.π Pi j ≫
        Projective.π
          (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object j) ≫
      e.inv, ?_⟩
  intro hzero
  have hj :
      Projective.π
            (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object j) ≫
          e.inv =
        0 := by
    have := congrArg (fun t => biproduct.ι Pi j ≫ t) hzero
    simpa [hPidef, biproduct.ι_π_self_assoc] using this
  haveI : Epi
      (Projective.π
          (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object j) ≫
        e.inv) :=
    epi_comp _ _
  have : 𝟙 L = 0 :=
    (cancel_epi
      (Projective.π
          (RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object j) ≫
        e.inv)).1 (by rw [hj]; simp)
  exact id_nonzero L this

end RepresentationTheory.CategoryTheory.Projective.Auxiliary
