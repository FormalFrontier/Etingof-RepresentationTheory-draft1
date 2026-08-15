/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import RepresentationTheory.RingAuxiliary
import RepresentationTheory.ModuleEnd.OppositeRing
import RepresentationTheory.FGModuleCat.Projectivity
import RepresentationTheory.ModuleCat.FiniteFreeRetractEndomorphisms
import RepresentationTheory.ModuleCat.FiniteUnderEquivalence
import RepresentationTheory.FGModuleCat.ProjectiveSeparators
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Ring.Equiv

universe w u u' v

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.Algebra.Category.ModuleCat.EndomorphismEquivalences

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}

set_option backward.isDefEq.respectTransparency false in

/-- Conjugation by an isomorphism gives a ring equivalence between the endomorphism rings of its source and target. -/

def endRingEquiv (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := fun f g =>
      show e.inv ≫ (f + g) ≫ e.hom = e.inv ≫ f ≫ e.hom + e.inv ≫ g ≫ e.hom by
        rw [Preadditive.add_comp, Preadditive.comp_add] }

/-- The endomorphism ring equivalence induced by an isomorphism sends a morphism to its conjugate by that isomorphism. -/
@[simp]
theorem endRingEquiv_apply (e : X ≅ Y) (f : End X) :
    e.endRingEquiv f = e.inv ≫ f ≫ e.hom := rfl

end CategoryTheory.Iso

variable {C : Type u} [Category.{v} C]

/-- A finitely generated module object associated to a ring. -/

noncomputable def fgModuleOfRing (A : Type u) [Ring A] : FGModuleCat.{u} A :=
  FGModuleCat.of A A

/-- The finitely generated module associated to a ring satisfies the auxiliary object property. -/

theorem fgModuleOfRingAuxiliary (A : Type u) [Ring A] :
    _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (fgModuleOfRing A) := by
  letI : HasFiniteBiproducts (FGModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let R := fgModuleOfRing A
  have hproj : Projective R :=
    _root_.RepresentationTheory.FGModuleCat.Projectivity.projective_of_toModuleCat_projective
      (inferInstanceAs (Projective (ModuleCat.of A A)))
  refine { toProjective := hproj, exists_epi := fun X => ?_ }
  obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' (R := A) (M := X)
  let F : Fin n → FGModuleCat.{u} A := fun _ => R
  letI : PreservesBiproduct F (_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A) :=
    preservesBiproduct_of_preservesCoproduct (_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A)
  let free : FGModuleCat.{u} A := FGModuleCat.of A (Fin n → A)
  let eUnder : (_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A).obj free ≅
      (_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A).obj (⨁ F) :=
    (ModuleCat.biproductIsoPi (fun _ : Fin n => ModuleCat.of A A)).symm.trans
      ((_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A).mapBiproduct F).symm
  let e : free ≅ ⨁ F := (ModuleCat.isFG A).isoMk eUnder
  let f : (⨁ F) ⟶ X := e.inv ≫ FGModuleCat.ofHom l
  refine ⟨n, inferInstance, f, ?_⟩
  apply _root_.RepresentationTheory.FGModuleCat.Projectivity.epi_of_toModuleCat_map_epi f
  rw [Functor.map_comp]
  haveI : Epi ((_root_.RepresentationTheory.FGModuleCat.Projectivity.toModuleCat A).map (FGModuleCat.ofHom l)) :=
    (ModuleCat.epi_iff_surjective _).mpr hl
  exact epi_comp _ _

/-- The auxiliary property is transported along an equivalence of preadditive categories with finite biproducts. -/

theorem _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.mapEquivalence
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (E : C ≌ D) (P : C) (hP : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) :
    _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (E.functor.obj P) := by
  letI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  letI : Functor.PreservesEpimorphisms E.functor :=
    Functor.preservesEpimorphisms_of_adjunction E.toAdjunction
  have hproj : Projective (E.functor.obj P) :=
    (E.map_projective_iff P).mpr hP.toProjective
  refine { toProjective := hproj, exists_epi := fun X => ?_ }
  obtain ⟨n, hbp, f, hf⟩ := hP.exists_epi (E.inverse.obj X)
  let F : Fin n → C := fun _ => P
  haveI : HasBiproduct F := hbp
  let g : (⨁ fun _ : Fin n => E.functor.obj P) ⟶ X :=
    (E.functor.mapBiproduct F).inv ≫ E.functor.map f ≫ (E.counitIso.app X).hom
  refine ⟨n, inferInstance, g, ?_⟩
  haveI : Epi f := hf
  haveI : Epi (E.functor.map f) := inferInstance
  have htail : Epi (E.functor.map f ≫ (E.counitIso.app X).hom) := epi_comp _ _
  haveI := htail
  exact epi_comp _ _

/-- The categorical endomorphism ring of the finitely generated module associated to a ring is equivalent to its ring of module endomorphisms. -/

noncomputable def fgModuleOfRingEndRingEquivModuleEnd (A : Type u) [Ring A] :
    End (fgModuleOfRing A) ≃+* Module.End A A where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv f := by apply FGModuleCat.hom_ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The categorical endomorphism algebra of the finitely generated module associated to a ring is equivalent to its algebra of linear endomorphisms. -/

noncomputable def fgModuleOfRingEndAlgEquivModuleEnd
    (k : Type w) (A : Type u) [Field k] [Ring A] [Algebra k A] :
    End (fgModuleOfRing A) ≃ₐ[k] Module.End A A :=
  AlgEquiv.ofRingEquiv (f := fgModuleOfRingEndRingEquivModuleEnd A) (fun c => by
    apply LinearMap.ext
    intro x
    simp only [fgModuleOfRingEndRingEquivModuleEnd, Algebra.algebraMap_eq_smul_one]
    change algebraMap k A c * x = c • x
    rw [Algebra.smul_def])

/-- A ring is equivalent to the opposite endomorphism ring of its associated finitely generated module. -/

noncomputable def fgModuleOfRingRingEquivOppositeEnd (A : Type u) [Ring A] :
    A ≃+* (End (fgModuleOfRing A))ᵐᵒᵖ :=
  (((RingEquiv.op ((fgModuleOfRingEndRingEquivModuleEnd A).trans (_root_.RepresentationTheory.ModuleEnd.OppositeRing.regularEndRingEquivOpposite A))).trans
    (RingEquiv.opOp A).symm)).symm

/-- The given algebra is equivalent to the opposite endomorphism algebra of the finitely generated module associated to its underlying ring. -/

noncomputable def fgModuleOfRingAlgEquivOppositeEnd
    (k : Type w) (A : Type u) [Field k] [Ring A] [Algebra k A] :
    A ≃ₐ[k] (End (fgModuleOfRing A))ᵐᵒᵖ :=
  (AlgEquiv.opOp k A).trans <|
    (AlgEquiv.op (AlgEquiv.moduleEndSelf k (A := A))).trans <|
      AlgEquiv.op (fgModuleOfRingEndAlgEquivModuleEnd k A).symm

/-- An equivalence of preadditive categories induces a ring equivalence between the endomorphism rings of an object and its image. -/

noncomputable def CategoryTheory.Equivalence.endRingEquiv
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (E : C ≌ D) (X : C) : End X ≃+* End (E.functor.obj X) := by
  letI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  exact { E.fullyFaithfulFunctor.mulEquivEnd X with
    map_add' := fun _ _ => E.functor.map_add }

/-- A linear equivalence of preadditive categories induces an algebra equivalence between the endomorphism algebras of an object and its image. -/

noncomputable def CategoryTheory.Equivalence.endAlgEquiv
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
    [HasFiniteBiproducts C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D]
    [HasFiniteBiproducts D]
    (E : C ≌ D) [E.functor.Linear k] (X : C) : End X ≃ₐ[k] End (E.functor.obj X) :=
  { CategoryTheory.Equivalence.endRingEquiv E X with
    commutes' := fun r => by
      change E.functor.map (r • 𝟙 X) = r • 𝟙 (E.functor.obj X)
      rw [Functor.Linear.map_smul, E.functor.map_id] }

/-- An equivalence between categories of finitely generated modules yields an auxiliary object whose opposite endomorphism ring is equivalent to the source ring. -/

theorem existsAuxiliaryObjectRingEquivOfFGModuleCatEquivalence {A B : Type u}
    [Ring A] [Ring B] (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) :
    ∃ P : FGModuleCat.{u} B,
      _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P ∧ Nonempty (A ≃+* (End P)ᵐᵒᵖ) := by
  letI : HasFiniteBiproducts (FGModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : HasFiniteBiproducts (FGModuleCat.{u} B) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let R := fgModuleOfRing A
  let P := E.functor.obj R
  have hR : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses R := fgModuleOfRingAuxiliary A
  have hP : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hR.mapEquivalence E
  let endEquiv : End R ≃+* End P := CategoryTheory.Equivalence.endRingEquiv E R
  let ringEquiv : A ≃+* (End P)ᵐᵒᵖ :=
    (fgModuleOfRingRingEquivOppositeEnd A).trans (RingEquiv.op endEquiv)
  exact ⟨P, hP, ⟨ringEquiv⟩⟩

/-- A linear equivalence between categories of finitely generated modules yields an auxiliary object whose opposite endomorphism algebra is equivalent to the source algebra. -/

theorem existsAuxiliaryObjectAlgEquivOfLinearFGModuleCatEquivalence
    {k : Type w} [Field k] {A B : Type u}
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) [E.functor.Linear k] :
    ∃ P : FGModuleCat.{u} B,
      _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P ∧ Nonempty (A ≃ₐ[k] (End P)ᵐᵒᵖ) := by
  letI : HasFiniteBiproducts (FGModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : HasFiniteBiproducts (FGModuleCat.{u} B) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let R := fgModuleOfRing A
  let P := E.functor.obj R
  have hR : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses R := fgModuleOfRingAuxiliary A
  have hP : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hR.mapEquivalence E
  let endEquiv : End R ≃ₐ[k] End P := CategoryTheory.Equivalence.endAlgEquiv E R
  let algEquiv : A ≃ₐ[k] (End P)ᵐᵒᵖ :=
    (fgModuleOfRingAlgEquivOppositeEnd k A).trans (AlgEquiv.op endEquiv)
  exact ⟨P, hP, ⟨algEquiv⟩⟩

/-- The image of the regular finitely generated module under an equivalence satisfies two auxiliary properties and has the expected opposite endomorphism ring. -/

theorem auxiliaryPropertiesOfFGModuleCatEquivalence {A B : Type u}
    [Ring A] [IsNoetherianRing A] [Ring B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) :
    let P := E.functor.obj (FGModuleCat.of.{u} A A)
    _root_.RepresentationTheory.FGModuleCat.ProjectiveSeparators.IsProjectiveSeparator P ∧ _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P ∧
      Nonempty (A ≃+* (End P)ᵐᵒᵖ) := by
  letI : HasFiniteBiproducts (FGModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : HasFiniteBiproducts (FGModuleCat.{u} B) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let R := fgModuleOfRing A
  let P := E.functor.obj R
  have hR : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses R := fgModuleOfRingAuxiliary A
  have hP : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hR.mapEquivalence E
  let endEquiv : End R ≃+* End P := CategoryTheory.Equivalence.endRingEquiv E R
  let ringEquiv : A ≃+* (End P)ᵐᵒᵖ :=
    (fgModuleOfRingRingEquivOppositeEnd A).trans (RingEquiv.op endEquiv)
  exact ⟨_root_.RepresentationTheory.FGModuleCat.ProjectiveSeparators.isProjectiveSeparator_equivalence_obj_regular E, hP, ⟨ringEquiv⟩⟩

/-- An auxiliary ring hypothesis produces an object with the auxiliary property whose opposite endomorphism ring is equivalent to the given ring. -/

theorem _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.existsObjectRingEquivOppositeEnd {A B : Type u}
    [Ring A] [Ring B] (h : _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary' A B) :
    ∃ P : FGModuleCat.{u} B,
      _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P ∧ Nonempty (A ≃+* (End P)ᵐᵒᵖ) := by
  obtain ⟨E⟩ := h
  exact existsAuxiliaryObjectRingEquivOfFGModuleCatEquivalence E

/-- An auxiliary hypothesis produces an object with the auxiliary property whose opposite endomorphism algebra is equivalent to the given algebra. -/

theorem _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.existsObjectAlgEquivOppositeEnd
    {k : Type w} [Field k] {A B : Type u}
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (h : _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary' k A B) :
    ∃ P : FGModuleCat.{u} B,
      _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P ∧ Nonempty (A ≃ₐ[k] (End P)ᵐᵒᵖ) := by
  obtain ⟨E, hlin⟩ := h
  letI := hlin
  exact existsAuxiliaryObjectAlgEquivOfLinearFGModuleCatEquivalence E

/-- Given the stated module-category equivalences for auxiliary objects, an auxiliary ring relation yields another auxiliary relation. -/

theorem _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.ofModuleCatEquivalence
    {A B : Type u} [Ring A] [Ring B] (h : _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary' A B)
    (reconstruct : ∀ (P : FGModuleCat.{u} B), _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P →
      Nonempty (ModuleCat.{u} B ≌ ModuleCat.{u} (End P)ᵐᵒᵖ)) :
    _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary A B := by
  obtain ⟨P, hP, ⟨e⟩⟩ := h.existsObjectRingEquivOppositeEnd
  obtain ⟨EP⟩ := reconstruct P hP
  let changeRings : ModuleCat.{u} A ≌ ModuleCat.{u} (End P)ᵐᵒᵖ :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm
  exact ⟨changeRings.trans EP.symm⟩

/-- An auxiliary relation between rings implies an auxiliary relation between their algebra structures. -/

theorem _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.toAlgebra
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (h : _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary' A B) : _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary A B :=
  h.ofModuleCatEquivalence
    (fun P hP => hP.exists_moduleCatEquivalenceEnd (k := k) P)

/-- When both algebras are finitely generated as modules over the field, one auxiliary relation implies the other. -/

theorem _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.ofModuleFinite
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [Module.Finite k A] [Module.Finite k B]
    (h : _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary' k A B) : _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B := by
  obtain ⟨P, hP, ⟨e⟩⟩ := h.existsObjectAlgEquivOppositeEnd
  let change := MoritaEquivalence.ofAlgEquiv e
  have hChange : _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A (End P)ᵐᵒᵖ :=
    ⟨change.eqv, change.linear⟩
  exact hChange.trans (hP.toAuxiliaryAlgebraRelation (k := k) P).symm

/-- For algebras over a field, the two auxiliary relations are equivalent. -/

theorem auxiliaryAlgebraIffRing
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
    _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary A B ↔ _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary' A B :=
  ⟨_root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.toAuxiliaryRingProperty, _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.toAlgebra (k := k)⟩

/-- When both algebras are finitely generated as modules over the field, the two auxiliary relations are equivalent. -/

theorem auxiliaryModuleFiniteIff
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [Module.Finite k A] [Module.Finite k B] :
    _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B ↔ _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary' k A B :=
  ⟨_root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary.toAuxiliaryAlgebraProperty,
    _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.ofModuleFinite (k := k)⟩

/-- An auxiliary type family attached to a finite family of objects and a family of natural-number multiplicities. -/

noncomputable abbrev auxiliaryTypeFamily [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ) : Type v :=
  (End (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n))ᵐᵒᵖ

variable [_root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [HasFiniteBiproducts C]
  {ι : Type v} [Fintype ι] (P : ι → C)

/-- Under the stated auxiliary and projectivity assumptions, the category is equivalent to finitely generated modules over the auxiliary type determined by positive multiplicities. -/

theorem equivalenceFGModuleCatAuxiliaryType
    (hproj : ∀ i, Projective (P i)) [_root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) [IsNoetherianRing (auxiliaryTypeFamily P n)] :
    Nonempty (C ≌ FGModuleCat.{v} (auxiliaryTypeFamily P n)) := by
  haveI : ∀ i, Projective (P i) := hproj
  haveI : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n) := _root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.ofPositiveMultiplicities P n hn
  exact _root_.RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.nonempty_fgModuleEquivalence_of_noetherian C (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n)

/-- Under the stated projective and indecomposable classification assumptions, an opposite endomorphism-ring presentation is equivalent to a presentation by an auxiliary type with positive multiplicities. -/

theorem existsAuxiliaryObjectRingEquivIffExistsAuxiliaryTypeRingEquiv
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [_root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)] (A : Type v) [Ring A] :
    (∃ Q : C, _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q ∧ Nonempty (A ≃+* (End Q)ᵐᵒᵖ)) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* auxiliaryTypeFamily P n) := by
  haveI : ∀ i, Projective (P i) := hproj
  constructor
  · rintro ⟨Q, hQ, ⟨φ⟩⟩
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.iffExistsPositiveMultiplicities P hproj hindec hdistinct hcomplete Q).mp hQ
    exact ⟨n, hn, ⟨φ.trans (RingEquiv.op e.endRingEquiv)⟩⟩
  · rintro ⟨n, hn, ⟨φ⟩⟩
    haveI : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n) := _root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.ofPositiveMultiplicities P n hn
    exact ⟨_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n, inferInstance, ⟨φ⟩⟩

/-- Under the stated projective and indecomposable classification assumptions, an equivalence from finitely generated modules is characterized by a ring equivalence to an auxiliary type with positive multiplicities. -/

theorem fgModuleCatEquivalenceIffExistsAuxiliaryRingEquiv
    {k : Type w} [Field k] [Linear k C] [_root_.RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [_root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)] (A : Type v) [Ring A] :
    Nonempty (FGModuleCat.{v} A ≌ C) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* auxiliaryTypeFamily P n) := by
  letI : HasFiniteBiproducts (FGModuleCat.{v} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  constructor
  · rintro ⟨E⟩
    let R := fgModuleOfRing A
    let Q := E.functor.obj R
    have hR : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses R := fgModuleOfRingAuxiliary A
    have hQ : _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q := hR.mapEquivalence E
    let endEquiv : End R ≃+* End Q := CategoryTheory.Equivalence.endRingEquiv E R
    let ringEquiv : A ≃+* (End Q)ᵐᵒᵖ :=
      (fgModuleOfRingRingEquivOppositeEnd A).trans (RingEquiv.op endEquiv)
    exact (existsAuxiliaryObjectRingEquivIffExistsAuxiliaryTypeRingEquiv P hproj hindec hdistinct hcomplete A).mp
      ⟨Q, hQ, ⟨ringEquiv⟩⟩
  · rintro ⟨n, hn, ⟨e⟩⟩
    haveI : IsNoetherianRing (auxiliaryTypeFamily P n) :=
      _root_.RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.opEnd_isNoetherian (k := k) (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n)
    let full : ModuleCat.{v} A ≌ ModuleCat.{v} (auxiliaryTypeFamily P n) :=
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm
    obtain ⟨fg⟩ :=
      _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.exists_fgModuleCatEquivalence (⟨full⟩ : _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary A (auxiliaryTypeFamily P n))
    obtain ⟨eC⟩ := equivalenceFGModuleCatAuxiliaryType P hproj n hn
    exact ⟨fg.trans eC.symm⟩

/-- Under the stated projective and indecomposable hypotheses, an auxiliary ring relation is characterized by positive multiplicities and a ring equivalence to the associated auxiliary type. -/

theorem auxiliaryRingClassification
    {k : Type w} [Field k] [Linear k C] [_root_.RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [_root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)] (A : Type v) [Ring A]
    (n₀ : ι → ℕ) (hn₀ : ∀ i, 1 ≤ n₀ i) :
    _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary' A (auxiliaryTypeFamily P n₀) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* auxiliaryTypeFamily P n) := by
  haveI : IsNoetherianRing (auxiliaryTypeFamily P n₀) :=
    _root_.RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.opEnd_isNoetherian (k := k) (_root_.RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities P n₀)
  obtain ⟨eC⟩ := equivalenceFGModuleCatAuxiliaryType P hproj n₀ hn₀
  rw [_root_.RepresentationTheory.RingAuxiliary.RingAuxiliary']
  constructor
  · rintro ⟨e⟩
    exact (fgModuleCatEquivalenceIffExistsAuxiliaryRingEquiv (k := k) P hproj hindec hdistinct
      hcomplete A).mp ⟨e.trans eC.symm⟩
  · intro h
    obtain ⟨e⟩ := (fgModuleCatEquivalenceIffExistsAuxiliaryRingEquiv (k := k) P hproj hindec
      hdistinct hcomplete A).mpr h
    exact ⟨e.trans eC⟩

/-- Auxiliary types arising from two positive multiplicity families have equivalent categories of finitely generated modules under the stated hypotheses. -/

theorem fgModuleCatAuxiliaryTypesEquivalent
    (hproj : ∀ i, Projective (P i)) [_root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)]
    (n n' : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (hn' : ∀ i, 1 ≤ n' i)
    [IsNoetherianRing (auxiliaryTypeFamily P n)] [IsNoetherianRing (auxiliaryTypeFamily P n')] :
    Nonempty (FGModuleCat.{v} (auxiliaryTypeFamily P n) ≌ FGModuleCat.{v} (auxiliaryTypeFamily P n')) := by
  obtain ⟨e⟩ := equivalenceFGModuleCatAuxiliaryType P hproj n hn
  obtain ⟨e'⟩ := equivalenceFGModuleCatAuxiliaryType P hproj n' hn'
  exact ⟨e.symm.trans e'⟩

end RepresentationTheory.Algebra.Category.ModuleCat.EndomorphismEquivalences
