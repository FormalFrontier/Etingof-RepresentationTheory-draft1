/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import RepresentationTheory.CategoryTheory.Limits.BiproductDecomposition
import RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

set_option backward.isDefEq.respectTransparency false

universe u v w

/-!
# Projective decompositions by positive multiplicities

This module constructs multiplicity-indexed finite biproducts and classifies projective
epimorphism witnesses by positive multiplicities of a complete family of indecomposable
projectives.
-/

open CategoryTheory CategoryTheory.Limits
open RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
open RepresentationTheory.CategoryTheory.Limits.BiproductDecomposition
open RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable

namespace RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition

variable {C : Type u} [Category.{v} C]

section MultBiproduct

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- Forms the finite biproduct obtained by repeating each member of a family according to a natural-number multiplicity. -/
noncomputable def biproductOfMultiplicities {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ) : C :=
  ⨁ (fun p : Σ i, Fin (n i) => P p.1)

/-- An internal helper definition associated with the enclosing multiplicity-indexed biproduct construction. -/
noncomputable def biproductOfMultiplicities.aux' {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ)
    (p : Σ i, Fin (n i)) : biproductOfMultiplicities P n ⟶ P p.1 :=
  biproduct.π (fun p : Σ i, Fin (n i) => P p.1) p

/-- An internal helper definition associated with the enclosing multiplicity-indexed biproduct construction. -/
noncomputable def biproductOfMultiplicities.aux {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ)
    (p : Σ i, Fin (n i)) : P p.1 ⟶ biproductOfMultiplicities P n :=
  biproduct.ι (fun p : Σ i, Fin (n i) => P p.1) p

end MultBiproduct

end RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition

namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Transfers the enclosing property across an isomorphism. -/
theorem ofIso {Q R : C} (e : Q ≅ R) [hR : HasProjectiveEpiWitnesses R] :
    HasProjectiveEpiWitnesses Q where
  toProjective := Projective.of_iso e.symm hR.toProjective
  exists_epi X := by
    obtain ⟨m, hbp, π, hπ⟩ := hR.exists_epi X
    haveI : HasBiproduct (fun _ : Fin m => R) := hbp
    haveI : HasBiproduct (fun _ : Fin m => Q) := inferInstance
    exact ⟨m, inferInstance,
      (biproduct.mapIso (fun _ : Fin m => e)).hom ≫ π, epi_comp _ _⟩

end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses

namespace RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition

variable {C : Type u} [Category.{v} C]

section Backward

variable [Preadditive C] [HasFiniteBiproducts C]

/-- Shows that the displayed property is preserved after each projective summand is assigned a positive multiplicity. -/
theorem ofPositiveMultiplicities {ι : Type v} [Fintype ι] (P : ι → C)
    [∀ i, Projective (P i)] [hgen : HasProjectiveEpiWitnesses (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    HasProjectiveEpiWitnesses (biproductOfMultiplicities P n) := by
  classical
  let e : ι → Σ i, Fin (n i) := fun i => ⟨i, ⟨0, hn i⟩⟩
  have he : Function.Injective e := fun i j h => congrArg Sigma.fst h
  let s : (⨁ P) ⟶ biproductOfMultiplicities P n :=
    biproduct.desc (fun i => biproductOfMultiplicities.aux P n (e i))
  let r : biproductOfMultiplicities P n ⟶ (⨁ P) :=
    biproduct.lift (fun i => biproductOfMultiplicities.aux' P n (e i))
  have key : s ≫ r = 𝟙 (⨁ P) := by
    apply biproduct.hom_ext'
    intro i
    rw [Category.comp_id, ← Category.assoc,
      show biproduct.ι P i ≫ s = biproductOfMultiplicities.aux P n (e i) from biproduct.ι_desc _ i]
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc,
      show r ≫ biproduct.π P j = biproductOfMultiplicities.aux' P n (e j) from biproduct.lift_π _ j]
    unfold biproductOfMultiplicities.aux biproductOfMultiplicities.aux'
    rw [biproduct.ι_π, biproduct.ι_π]
    by_cases h : i = j
    · subst h; rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg (fun he' => h (he he')), dif_neg h]
  haveI : IsSplitEpi r := ⟨⟨s, key⟩⟩
  haveI : Projective (biproductOfMultiplicities P n) :=
    inferInstanceAs (Projective (⨁ fun p : Σ i, Fin (n i) => P p.1))
  refine { toProjective := inferInstance, exists_epi := fun X => ?_ }
  obtain ⟨m, hbp, π, hπ⟩ := hgen.exists_epi X
  haveI : HasBiproduct (fun _ : Fin m => (⨁ P)) := hbp
  haveI : Epi r := inferInstance
  refine ⟨m, inferInstance, biproduct.map (fun _ : Fin m => r) ≫ π, ?_⟩
  exact epi_comp _ _

end Backward

section Classification

variable [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [HasFiniteBiproducts C]

/-- Produces positive multiplicities and an isomorphism to the associated biproduct for an object with the displayed property. -/
theorem existsPositiveMultiplicities {ι : Type v} [Fintype ι] (P : ι → C)
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, CategoryTheory.Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → CategoryTheory.Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    (hgen : HasProjectiveEpiWitnesses (⨁ P)) (Q : C) (hQ : HasProjectiveEpiWitnesses Q) :
    ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (Q ≅ biproductOfMultiplicities P n) := by
  classical
  obtain ⟨κ, instκ, f, hf, ⟨e⟩⟩ :=
    exists_iso_biproduct_of_projective_indec hQ.toProjective
  haveI := instκ
  choose g hg using fun k => hcomplete (f k) (hf k).1 (hf k).2
  let fiso : ∀ k, f k ≅ P (g k) := fun k => (hg k).some
  set n : ι → ℕ := fun i => Fintype.card {k // g k = i} with hn
  let σ : (Σ i, Fin (n i)) ≃ κ :=
    (Equiv.sigmaCongrRight fun i => (Fintype.equivFin {k // g k = i}).symm).trans
      (Equiv.sigmaFiberEquiv g)
  have hgσ : ∀ p : Σ i, Fin (n i), g (σ p) = p.1 := by
    rintro ⟨i, a⟩
    exact ((Fintype.equivFin {k // g k = i}).symm a).2
  have hpos : ∀ i, 1 ≤ n i := by
    intro i
    haveI : Projective (P i) := hproj i
    obtain ⟨m, hbp, π, hπ⟩ := hQ.exists_epi (P i)
    haveI := hbp
    haveI := hπ
    let t : P i ⟶ (⨁ fun _ : Fin m => Q) := Projective.factorThru (𝟙 (P i)) π
    have ht : t ≫ π = 𝟙 (P i) := Projective.factorThru_comp _ _
    let E1 : (⨁ fun _ : Fin m => Q) ≅ ⨁ (fun p : Σ _ : Fin m, κ => f p.2) :=
      biproduct.mapIso (fun _ : Fin m => e) ≪≫
        biproductBiproductIso (fun _ : Fin m => κ) (fun _ : Fin m => f)
    let F : (Σ _ : Fin m, κ) → C := fun p => f p.2
    have hF : ∀ p, CategoryTheory.Indecomposable (F p) := fun p => (hf p.2).2
    have hsr : (t ≫ E1.hom) ≫ (E1.inv ≫ π) = 𝟙 (P i) := by
      rw [Category.assoc, ← Category.assoc E1.hom, E1.hom_inv_id, Category.id_comp, ht]
    obtain ⟨p, ⟨iso⟩⟩ :=
      indecomposable_iso_biproduct_summand_of_retract F hF (hindec i)
        (t ≫ E1.hom) (E1.inv ≫ π) hsr
    have : i = g p.2 := hdistinct i (g p.2) ⟨iso ≪≫ fiso p.2⟩
    exact Fintype.card_pos_iff.mpr ⟨⟨p.2, this.symm⟩⟩
  refine ⟨n, hpos, ⟨?_⟩⟩
  let w : ∀ p : Σ i, Fin (n i), f (σ p) ≅ P p.1 :=
    fun p => fiso (σ p) ≪≫ eqToIso (congrArg P (hgσ p))
  exact e ≪≫ (biproduct.whiskerEquiv σ w).symm

/-- Under the stated hypotheses, characterizes the displayed property by positive multiplicities and an isomorphism to the associated biproduct. -/
theorem iffExistsPositiveMultiplicities {ι : Type v} [Fintype ι] (P : ι → C)
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, CategoryTheory.Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → CategoryTheory.Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [hgen : HasProjectiveEpiWitnesses (⨁ P)] (Q : C) :
    HasProjectiveEpiWitnesses Q ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (Q ≅ biproductOfMultiplicities P n) := by
  haveI : ∀ i, Projective (P i) := hproj
  constructor
  · intro hQ
    exact existsPositiveMultiplicities P hproj hindec hdistinct hcomplete hgen Q hQ
  · rintro ⟨n, hn, ⟨e⟩⟩
    haveI := ofPositiveMultiplicities P n hn
    exact HasProjectiveEpiWitnesses.ofIso e

end Classification

end RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition
