/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.EndomorphismDecomposition
import RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable
import RepresentationTheory.RingTheory.Artinian.ModuleIdempotents
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import RepresentationTheory.Algebra.QuotientMatrixDecomposition
import RepresentationTheory.FGModuleCat.SimpleModules
import RepresentationTheory.FGModuleCat.Projectivity
import RepresentationTheory.Algebra.Module.Simple
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Projection

/-! # Indecomposable objects -/

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Indecomposable

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

section Equivalence

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
variable {D : Type u'} [Category.{v'} D] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional D]

/-- The functor of the given equivalence sends an indecomposable object to an indecomposable object. -/
theorem indecomposable_map_of_equivalence (E : C ≌ D) {X : C}
    (hX : Indecomposable X) : Indecomposable (E.functor.obj X) := by
  letI : E.inverse.IsEquivalence := E.isEquivalence_inverse
  letI : E.inverse.Additive :=
    Functor.additive_of_preserves_binary_products E.inverse
  letI : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.inverse
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hX.1
    rw [IsZero.iff_id_eq_zero]
    apply E.functor.map_injective
    rw [E.functor.map_id, E.functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp hzero
  · intro Y Z e
    let e' : X ≅ E.inverse.obj Y ⊞ E.inverse.obj Z :=
      E.unitIso.app X ≪≫ E.inverse.mapIso e ≪≫ E.inverse.mapBiprod Y Z
    rcases hX.2 _ _ e' with hY | hZ
    · left
      have hEY : IsZero (E.functor.obj (E.inverse.obj Y)) := by
        rw [IsZero.iff_id_eq_zero, ← E.functor.map_id]
        rw [hY.eq_of_src (𝟙 (E.inverse.obj Y)) 0, E.functor.map_zero]
      exact hEY.of_iso (E.counitIso.app Y).symm
    · right
      have hEZ : IsZero (E.functor.obj (E.inverse.obj Z)) := by
        rw [IsZero.iff_id_eq_zero, ← E.functor.map_id]
        rw [hZ.eq_of_src (𝟙 (E.inverse.obj Z)) 0, E.functor.map_zero]
      exact hEZ.of_iso (E.counitIso.app Z).symm

end Equivalence

section SimpleEquivalence

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- The functor of an equivalence carries a simple object to a simple object. -/
theorem simple_map_of_equivalence (E : A ≌ D) (X : A) [Simple X] :
    Simple (E.functor.obj X) := by
  haveI : Simple ((Functor.id A).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) :=
    Simple.of_iso (E.unitIso.app X).symm
  exact
    { mono_isIso_iff_nonzero := fun {Y} f _ => by
        constructor
        · intro _ h
          haveI : IsIso (E.inverse.map f) := Functor.map_isIso E.inverse f
          exact (Simple.mono_isIso_iff_nonzero (E.inverse.map f)).mp inferInstance
            (by rw [h]; simp)
        · intro hne
          haveI : Mono (E.inverse.map f) := inferInstance
          haveI : IsIso (E.inverse.map f) :=
            (Simple.mono_isIso_iff_nonzero (E.inverse.map f)).mpr
              (fun h => hne (E.inverse.map_injective (by rwa [E.inverse.map_zero])))
          exact isIso_of_fully_faithful E.inverse f }

end SimpleEquivalence

section ModuleBridge

variable {R : Type u} [Ring R]

/-- Recovers the stated module-side property from indecomposability of its associated ModuleCat object. -/
theorem module_property_of_moduleCat_indecomposable
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : Indecomposable (ModuleCat.of R M)) : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R M := by
  constructor
  · rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    letI : Subsingleton M := hsub
    exact hM.1 (ModuleCat.isZero_of_subsingleton _)
  · intro W₁ W₂ hcompl
    let e : ModuleCat.of R M ≅
        (ModuleCat.of R W₁) ⊞ (ModuleCat.of R W₂) :=
      (W₁.prodEquivOfIsCompl W₂ hcompl).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of R W₁) (ModuleCat.of R W₂)).symm
    rcases hM.2 _ _ e with hW₁ | hW₂
    · left
      have hsub : Subsingleton W₁ := ModuleCat.subsingleton_of_isZero hW₁
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : W₁) = 0 := @Subsingleton.elim W₁ hsub _ _
      exact congrArg Subtype.val this
    · right
      have hsub : Subsingleton W₂ := ModuleCat.subsingleton_of_isZero hW₂
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : W₂) = 0 := @Subsingleton.elim W₂ hsub _ _
      exact congrArg Subtype.val this

/-- Turns the stated module-side property into indecomposability of the associated ModuleCat object. -/
theorem moduleCat_indecomposable_of_module_property
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R M) : Indecomposable (ModuleCat.of R M) := by
  constructor
  · intro hzero
    exact (not_subsingleton_iff_nontrivial.mpr hM.1)
      (ModuleCat.subsingleton_of_isZero hzero)
  · intro Y Z e
    let p : ModuleCat.of R M ⟶ ModuleCat.of R M :=
      e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    have hp : IsIdempotentElem p.hom := by
      ext x
      change (p ≫ p).hom x = p.hom x
      congr 1
      dsimp only [p]
      simp
    rcases hM.2 (LinearMap.range p.hom) (LinearMap.ker p.hom)
        (open LinearMap in IsIdempotentElem.isCompl hp) with hrange | hker
    · left
      have hp0 : p = 0 := by
        apply ModuleCat.hom_ext
        exact LinearMap.range_eq_bot.mp hrange
      rw [IsZero.iff_id_eq_zero]
      calc
        𝟙 Y = biprod.inl ≫ e.inv ≫ p ≫ e.hom ≫ biprod.fst := by
          dsimp only [p]
          simp
        _ = 0 := by rw [hp0]; simp
    · right
      have hp_inj : Function.Injective p.hom := LinearMap.ker_eq_bot.mp hker
      have hp1 : p = 𝟙 _ := by
        ext x
        apply hp_inj
        exact LinearMap.congr_fun hp x
      rw [IsZero.iff_id_eq_zero]
      calc
        𝟙 Z = biprod.inr ≫ e.inv ≫ p ≫ e.hom ≫ biprod.snd := by
          rw [hp1]
          simp
        _ = 0 := by
          dsimp only [p]
          simp

end ModuleBridge

section FullyFaithfulReflection

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]

/-- Reflects indecomposability along a full and faithful functor preserving the stated zero and biproduct structure. -/
theorem indecomposable_of_map_of_full_faithful (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    {X : C} (hX : Indecomposable (F.obj X)) : Indecomposable X := by
  constructor
  · intro hzero
    apply hX.1
    rw [IsZero.iff_id_eq_zero, ← F.map_id]
    rw [hzero.eq_of_src (𝟙 X) 0, F.map_zero]
  · intro Y Z e
    let e' : F.obj X ≅ F.obj Y ⊞ F.obj Z := F.mapIso e ≪≫ F.mapBiprod Y Z
    rcases hX.2 _ _ e' with hY | hZ
    · left
      rw [IsZero.iff_id_eq_zero]
      apply F.map_injective
      rw [F.map_id, F.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp hY
    · right
      rw [IsZero.iff_id_eq_zero]
      apply F.map_injective
      rw [F.map_id, F.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp hZ

end FullyFaithfulReflection

section IndecomposableEquivalence

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]

/-- An equivalence between the displayed preadditive categories with binary biproducts preserves indecomposable objects. -/
theorem indecomposable_map_of_preadditive_equivalence (E : A ≌ D) {X : A}
    (hX : Indecomposable X) : Indecomposable (E.functor.obj X) := by
  letI : E.inverse.Additive := Functor.additive_of_preserves_binary_products E.inverse
  letI : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.inverse
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hX.1
    rw [IsZero.iff_id_eq_zero]
    apply E.functor.map_injective
    rw [E.functor.map_id, E.functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp hzero
  · intro Y Z e
    let e' : X ≅ E.inverse.obj Y ⊞ E.inverse.obj Z :=
      E.unitIso.app X ≪≫ E.inverse.mapIso e ≪≫ E.inverse.mapBiprod Y Z
    rcases hX.2 _ _ e' with hY | hZ
    · left
      have hEY : IsZero (E.functor.obj (E.inverse.obj Y)) := by
        rw [IsZero.iff_id_eq_zero, ← E.functor.map_id]
        rw [hY.eq_of_src (𝟙 (E.inverse.obj Y)) 0, E.functor.map_zero]
      exact hEY.of_iso (E.counitIso.app Y).symm
    · right
      have hEZ : IsZero (E.functor.obj (E.inverse.obj Z)) := by
        rw [IsZero.iff_id_eq_zero, ← E.functor.map_id]
        rw [hZ.eq_of_src (𝟙 (E.inverse.obj Z)) 0, E.functor.map_zero]
      exact hEZ.of_iso (E.counitIso.app Z).symm

end IndecomposableEquivalence

section Uniqueness

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]

/-- Two indecomposable projective objects with nonzero morphisms to the same simple object are isomorphic. -/
theorem projective_iso_of_nonzero_hom_to_simple
    {P P' S : C} (hP : Indecomposable P) (hP' : Indecomposable P')
    (hproj : Projective P) (hproj' : Projective P') [Simple S]
    (φ : P ⟶ S) (hφ : φ ≠ 0) (ψ : P' ⟶ S) (hψ : ψ ≠ 0) :
    Nonempty (P ≅ P') := by
  haveI : Projective P := hproj
  haveI : Projective P' := hproj'
  haveI : Epi φ := epi_of_nonzero_to_simple hφ
  haveI : Epi ψ := epi_of_nonzero_to_simple hψ
  let f : P ⟶ P' := Projective.factorThru φ ψ
  let g : P' ⟶ P := Projective.factorThru ψ φ
  have hf : f ≫ ψ = φ := Projective.factorThru_comp φ ψ
  have hg : g ≫ φ = ψ := Projective.factorThru_comp ψ φ
  let a : End P := f ≫ g
  let b : End P' := g ≫ f
  have ha_fix : (a : P ⟶ P) ≫ φ = φ := by dsimp [a]; rw [Category.assoc, hg, hf]
  have hb_fix : (b : P' ⟶ P') ≫ ψ = ψ := by dsimp [b]; rw [Category.assoc, hf, hg]
  have hpow_fg : ∀ n : ℕ, ((a ^ n : End P) : P ⟶ P) ≫ φ = φ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, End.mul_def]
      rw [Category.assoc, ih, ha_fix]
  have hpow_gf : ∀ n : ℕ, ((b ^ n : End P') : P' ⟶ P') ≫ ψ = ψ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, End.mul_def]
      rw [Category.assoc, ih, hb_fix]
  haveI hfg_iso : IsIso (f ≫ g) := by
    rcases RepresentationTheory.CategoryTheory.EndomorphismDecomposition.indecomposableEndIsNilpotentOrIsIso hP a with hnil | hiso
    · obtain ⟨n, hn⟩ := hnil
      exfalso
      apply hφ
      have h := hpow_fg n
      rw [hn] at h
      change (0 : P ⟶ P) ≫ φ = φ at h
      simpa only [zero_comp] using h.symm
    · change IsIso (a : P ⟶ P)
      exact hiso
  haveI hgf_iso : IsIso (g ≫ f) := by
    rcases RepresentationTheory.CategoryTheory.EndomorphismDecomposition.indecomposableEndIsNilpotentOrIsIso hP' b with hnil | hiso
    · obtain ⟨n, hn⟩ := hnil
      exfalso
      apply hψ
      have h := hpow_gf n
      rw [hn] at h
      change (0 : P' ⟶ P') ≫ ψ = ψ at h
      simpa only [zero_comp] using h.symm
    · change IsIso (b : P' ⟶ P')
      exact hiso
  let r : P' ⟶ P := g ≫ inv (f ≫ g)
  let l : P' ⟶ P := inv (g ≫ f) ≫ g
  have hfr : f ≫ r = 𝟙 P := by
    dsimp [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hlf : l ≫ f = 𝟙 P' := by
    dsimp [l]
    rw [Category.assoc, IsIso.inv_hom_id]
  have hlr : l = r := by
    calc
      l = l ≫ 𝟙 P := (Category.comp_id _).symm
      _ = l ≫ (f ≫ r) := by rw [hfr]
      _ = (l ≫ f) ≫ r := (Category.assoc _ _ _).symm
      _ = r := by rw [hlf, Category.id_comp]
  haveI : IsIso f := ⟨⟨r, hfr, by rw [← hlr, hlf]⟩⟩
  exact ⟨asIso f⟩

end Uniqueness

section FamilyCompleteness

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
variable {ι : Type v} [Finite ι]

/-- Under the stated hypotheses, an indecomposable projective object is isomorphic to an object in the given finite family. -/
theorem indecomposable_projective_iso_family_object
    (P : ι → C) (hindec : ∀ i, Indecomposable (P i)) [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)]
    (R : C) (hRproj : Projective R) (hRindec : Indecomposable R) :
    ∃ i, Nonempty (R ≅ P i) := by
  classical
  letI := Fintype.ofFinite ι
  haveI : Projective R := hRproj
  obtain ⟨m, hbp, π, hπ⟩ :=
    (inferInstance : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)).exists_epi R
  haveI := hbp
  haveI := hπ
  let t : R ⟶ (⨁ fun _ : Fin m => ⨁ P) := Projective.factorThru (𝟙 R) π
  have ht : t ≫ π = 𝟙 R := Projective.factorThru_comp _ _
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let σ : (Fin m × Fin (Fintype.card ι)) ≃ (Σ _ : Fin m, ι) :=
    { toFun := fun p => ⟨p.1, eι p.2⟩
      invFun := fun p => (p.1, eι.symm p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  let F : (Fin m × Fin (Fintype.card ι)) → C := fun p => P (eι p.2)
  let E₀ : (⨁ fun _ : Fin m => ⨁ P) ≅
      ⨁ (fun p : Σ _ : Fin m, ι => P p.2) :=
    biproductBiproductIso (fun _ : Fin m => ι) (fun _ : Fin m => P)
  let E₁ : (⨁ F) ≅ ⨁ (fun p : Σ _ : Fin m, ι => P p.2) :=
    biproduct.whiskerEquiv (f := F) (g := fun p : Σ _ : Fin m, ι => P p.2)
      σ (fun _ => Iso.refl _)
  let E : (⨁ fun _ : Fin m => ⨁ P) ≅ ⨁ F := E₀ ≪≫ E₁.symm
  have hF : ∀ p, Indecomposable (F p) := fun p => hindec (eι p.2)
  let s : R ⟶ ⨁ F := t ≫ E.hom
  let r : ⨁ F ⟶ R := E.inv ≫ π
  have hsplit : s ≫ r = 𝟙 R := by
    dsimp only [s, r]
    rw [Category.assoc, ← Category.assoc E.hom, E.hom_inv_id, Category.id_comp, ht]
  obtain ⟨p, hp⟩ :=
    RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable.indecomposable_iso_biproduct_summand_of_retract (C := C)
      (κ := Fin m × Fin (Fintype.card ι))
      (X := R) F hF hRindec s r hsplit
  exact ⟨eι p.2, hp⟩

end FamilyCompleteness

section IrredundantSimples

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]

/-- Provides a family containing exactly one representative, up to isomorphism, of every simple object. -/
theorem exists_simple_representatives :
    ∃ (κ : Type) (_ : Fintype κ) (S : κ → C),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i)) := by
  classical
  let I := RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary (C := C)
  letI : Fintype I := RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.fintype
  let S₀ : I → C := RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object
  let r : Setoid I :=
    { r := fun i j => Nonempty (S₀ i ≅ S₀ j)
      iseqv := ⟨fun _ => ⟨Iso.refl _⟩,
        fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩ }
  let κ := Quotient r
  letI : Fintype κ := Fintype.ofSurjective (Quotient.mk r) Quotient.mk_surjective
  let S : κ → C := fun q => S₀ q.out
  refine ⟨κ, inferInstance, S, fun q => ?_, ?_, ?_⟩
  · dsimp only [S, S₀]
    exact RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.simple_object q.out
  · intro q q' h
    calc
      q = ⟦q.out⟧ := (Quotient.out_eq q).symm
      _ = ⟦q'.out⟧ := Quotient.sound h
      _ = q' := Quotient.out_eq q'
  · intro X hX
    obtain ⟨i, ⟨e⟩⟩ := RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.simple_iso_auxiliaryObject X hX
    let q : κ := ⟦i⟧
    have hrel : r q.out i := Quotient.exact (Quotient.out_eq q)
    exact ⟨q, ⟨e ≪≫ hrel.some.symm⟩⟩

end IrredundantSimples

section LinearEquivalence

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]

/-- Constructs the linear equivalence between hom spaces induced by the given linear additive equivalence. -/
noncomputable def equivalence_hom_linear_equiv (E : C ≌ D) [E.functor.Additive]
    [E.functor.Linear k] (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (E.functor.obj X ⟶ E.functor.obj Y) :=
  LinearEquiv.ofBijective (E.functor.mapLinearMap k)
    ⟨E.functor.map_injective, E.functor.map_surjective⟩

/-- A linear additive equivalence gives equal finrank values for corresponding morphism spaces. -/
theorem equivalence_finrank_hom (E : C ≌ D) [E.functor.Additive]
    [E.functor.Linear k] (X Y : C) :
    Module.finrank k (X ⟶ Y) = Module.finrank k (E.functor.obj X ⟶ E.functor.obj Y) :=
  (equivalence_hom_linear_equiv E X Y).finrank_eq

end LinearEquivalence

section DeltaFamily

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
variable {ι : Type v} [Finite ι] [DecidableEq ι]

/-- Produces simple representatives whose hom spaces from the supplied projective objects have finrank one at matching indices and zero otherwise. -/
theorem exists_simple_family_with_finrank_hom (P : ι → C)
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P)] :
    ∃ S : ι → C,
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i)) ∧
      (∀ i j, Module.finrank k (P i ⟶ S j) = if i = j then 1 else 0) := by
  classical
  letI := Fintype.ofFinite ι
  let Q : C := ⨁ P
  let B := (End Q)ᵐᵒᵖ
  haveI : ∀ i, Projective (P i) := hproj
  letI : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q := inferInstanceAs (RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses (⨁ P))
  haveI : FiniteDimensional k B := RepresentationTheory.Algebra.QuotientMatrixDecomposition.finiteDimensional_op_end Q
  haveI : IsNoetherianRing B := RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.opEnd_isNoetherian (k := k) Q
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI := RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.fgModuleFunctor_isEquivalence (k := k) (P := Q)
  let E : C ≌ FGModuleCat.{v} B :=
    RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.fgModuleFunctor.asEquivalence
  obtain ⟨κ, hκ, T, hTsimple, hTdistinct, hTcomplete⟩ :=
    exists_simple_representatives (C := C)
  letI : Fintype κ := hκ
  let M : κ → Type v := fun a => Q ⟶ T a
  let η : ∀ a, FGModuleCat.of B (M a) ≅ E.functor.obj (T a) := fun a => by
    dsimp [M, E, Functor.asEquivalence, RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.fgModuleFunctor]
    exact Iso.refl _
  haveI : ∀ a, Module.Finite B (M a) := fun a => by
    dsimp only [M]
    exact (inferInstance : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q).hom_finite (T a)
  haveI : ∀ a, IsSimpleModule B (M a) := by
    intro a
    haveI : Simple (T a) := hTsimple a
    haveI : Simple (E.functor.obj (T a)) := simple_map_of_equivalence E (T a)
    haveI : Simple (FGModuleCat.of B (M a)) := Simple.of_iso (η a)
    exact RepresentationTheory.FGModuleCat.SimpleModules.isSimpleModule_carrier_of_simple (FGModuleCat.of B (M a))
  haveI : ∀ a, IsScalarTower k B (M a) := fun a => by
    dsimp [M, E]
    set_option backward.isDefEq.respectTransparency false in
      constructor
      intro c b f
      change ((c • b).unop ≫ f) = c • (b.unop ≫ f)
      rw [Algebra.smul_def, MulOpposite.unop_mul, End.mul_def]
      change (((c • 𝟙 Q) ≫ b.unop) ≫ f) = c • (b.unop ≫ f)
      simp
  haveI : ∀ a, SMulCommClass B k (M a) := fun _ => inferInstance
  have hMdistinct : ∀ a b, Nonempty (M a ≃ₗ[B] M b) → a = b := by
    intro a b hab
    apply hTdistinct a b
    obtain ⟨e⟩ := hab
    let eE : E.functor.obj (T a) ≅ E.functor.obj (T b) :=
      (η a).symm ≪≫ e.toFGModuleCatIso ≪≫ η b
    exact ⟨E.unitIso.app (T a) ≪≫ E.inverse.mapIso eE ≪≫
      (E.unitIso.app (T b)).symm⟩
  have hMcomplete : ∀ (W : Type v) [AddCommGroup W] [Module B W]
      [IsSimpleModule B W], ∃ a, Nonempty (W ≃ₗ[B] M a) := by
    intro W _ _ _
    letI : Module.Finite B W := RepresentationTheory.Algebra.Module.Simple.IsSimpleModule.finite
    let X : FGModuleCat.{v} B := FGModuleCat.of B W
    haveI : Simple X := RepresentationTheory.FGModuleCat.SimpleModules.simple_of_isSimpleModule W
    haveI : Simple (E.inverse.obj X) := simple_map_of_equivalence E.symm X
    obtain ⟨a, ⟨e⟩⟩ := hTcomplete (E.inverse.obj X) inferInstance
    exact ⟨a, ⟨FGModuleCat.isoToLinearEquiv
      ((E.counitIso.app X).symm ≪≫ E.functor.mapIso e ≪≫ (η a).symm)⟩⟩
  obtain ⟨Cover, hCoverAdd, hCoverModule, hCoverKModule, hCoverTower, hCoverComm,
      hCoverProjective, hCoverFinite, hCoverIndec, hCoverDelta, hCoverUnique⟩ :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_projective_family_with_finrank_hom (k := k) M hMdistinct hMcomplete
  letI : ∀ a, AddCommGroup (Cover a) := hCoverAdd
  letI : ∀ a, Module B (Cover a) := hCoverModule
  letI : ∀ a, Module k (Cover a) := hCoverKModule
  letI : ∀ a, IsScalarTower k B (Cover a) := hCoverTower
  letI : ∀ a, SMulCommClass B k (Cover a) := hCoverComm
  letI : ∀ a, Module.Projective B (Cover a) := hCoverProjective
  letI : ∀ a, Module.Finite B (Cover a) := hCoverFinite
  let CoverFG : κ → FGModuleCat.{v} B := fun a => FGModuleCat.of B (Cover a)
  have hCoverFGProjective : ∀ a, Projective (CoverFG a) := by
    intro a
    apply RepresentationTheory.FGModuleCat.Projectivity.projective_of_toModuleCat_projective
    exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of B (Cover a))
  have hCoverFGIndec : ∀ a, Indecomposable (CoverFG a) := by
    intro a
    letI : PreservesBinaryBiproducts (RepresentationTheory.FGModuleCat.Projectivity.toModuleCat B) :=
      preservesBinaryBiproducts_of_preservesBinaryProducts (RepresentationTheory.FGModuleCat.Projectivity.toModuleCat B)
    apply indecomposable_of_map_of_full_faithful (RepresentationTheory.FGModuleCat.Projectivity.toModuleCat B)
    exact moduleCat_indecomposable_of_module_property
      (Cover a) (hCoverIndec a)
  let R : κ → C := fun a => E.inverse.obj (CoverFG a)
  have hRprojective : ∀ a, Projective (R a) := by
    intro a
    exact (E.symm.map_projective_iff (CoverFG a)).mpr (hCoverFGProjective a)
  have hRindec : ∀ a, Indecomposable (R a) := fun a =>
    indecomposable_map_of_preadditive_equivalence E.symm (hCoverFGIndec a)
  choose g hg using fun a =>
    indecomposable_projective_iso_family_object
      P hindec (R a) (hRprojective a) (hRindec a)
  have hCoverIndex_of_iso : ∀ a b, Nonempty (CoverFG a ≅ CoverFG b) → a = b := by
    intro a b hab
    obtain ⟨eFG⟩ := hab
    let e : Cover a ≃ₗ[B] Cover b := FGModuleCat.isoToLinearEquiv eFG
    haveI : Module.Finite k (Cover a) := Module.Finite.trans B (Cover a)
    haveI : Module.Finite k (Cover b) := Module.Finite.trans B (Cover b)
    haveI : Module.Finite k (M a) := Module.Finite.trans B (M a)
    haveI : Module.Finite k (Cover a →ₗ[B] M a) :=
      Module.Finite.of_injective
        (LinearMap.restrictScalarsₗ k B (Cover a) (M a) k)
        (LinearMap.restrictScalars_injective k)
    haveI : Module.Finite k (Cover b →ₗ[B] M a) :=
      Module.Finite.of_injective
        (LinearMap.restrictScalarsₗ k B (Cover b) (M a) k)
        (LinearMap.restrictScalars_injective k)
    have hdiag : Module.finrank k (Cover a →ₗ[B] M a) = 1 := by
      simpa using hCoverDelta a a
    obtain ⟨f, hf⟩ : ∃ f : Cover a →ₗ[B] M a, f ≠ 0 := by
      by_contra h
      have hall : ∀ f : Cover a →ₗ[B] M a, f = 0 := by
        intro f
        exact not_ne_iff.mp (not_exists.mp h f)
      exact Nat.one_ne_zero (hdiag.symm.trans (finrank_zero_iff_forall_zero.mpr hall))
    have hcomp : f.comp e.symm.toLinearMap ≠ 0 := by
      intro hzero
      apply hf
      apply LinearMap.ext
      intro x
      have hx := LinearMap.congr_fun hzero (e x)
      simpa using hx
    by_contra habne
    have hoff : Module.finrank k (Cover b →ₗ[B] M a) = 0 := by
      simpa [Ne.symm habne] using hCoverDelta b a
    exact hcomp (finrank_zero_iff_forall_zero.mp hoff _)
  have hg_injective : Function.Injective g := by
    intro a b hab
    apply hCoverIndex_of_iso a b
    obtain ⟨ea⟩ := hg a
    obtain ⟨eb⟩ := hg b
    let eR : R a ≅ R b := ea ≪≫ eqToIso (congrArg P hab) ≪≫ eb.symm
    exact ⟨(E.counitIso.app (CoverFG a)).symm ≪≫ E.functor.mapIso eR ≪≫
      E.counitIso.app (CoverFG b)⟩
  have hPtoSimple : ∀ i, ∃ a, ∃ f : P i ⟶ T a, f ≠ 0 := by
    intro i
    let N : Type v := Q ⟶ P i
    let ηP : FGModuleCat.of B N ≅ E.functor.obj (P i) := by
      dsimp [N, E, Functor.asEquivalence, RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.fgModuleFunctor]
      exact Iso.refl _
    haveI : Module.Finite B N := by
      dsimp only [N]
      exact (inferInstance : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q).hom_finite (P i)
    haveI : Nontrivial N := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      letI : Subsingleton N := hsub
      have hz : IsZero (FGModuleCat.of B N) := by
        rw [IsZero.iff_id_eq_zero]
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      have hzE : IsZero (E.functor.obj (P i)) := hz.of_iso ηP
      exact (indecomposable_map_of_preadditive_equivalence E (hindec i)).1 hzE
    obtain ⟨a, φ, hφ⟩ :=
      RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_index_and_nonzero_map M hMcomplete (Q := N)
    let φFG : FGModuleCat.of B N ⟶ FGModuleCat.of B (M a) :=
      InducedCategory.homMk (ModuleCat.ofHom φ)
    let m : E.functor.obj (P i) ⟶ E.functor.obj (T a) :=
      ηP.inv ≫ φFG ≫ (η a).hom
    let f : P i ⟶ T a := E.functor.preimage m
    refine ⟨a, f, ?_⟩
    intro hf
    have hm0 : m = 0 := by
      have hmap : E.functor.map f = m := E.functor.map_preimage m
      rw [hf, E.functor.map_zero] at hmap
      exact hmap.symm
    have hleft : ηP.inv ≫ φFG = 0 := by
      apply (cancel_mono (η a).hom).mp
      rw [Category.assoc]
      simpa only [m, zero_comp] using hm0
    have hφFG : φFG = 0 := by
      apply (cancel_epi ηP.inv).mp
      simpa only [comp_zero] using hleft
    apply hφ
    exact ModuleCat.hom_ext_iff.mp (congrArg InducedCategory.Hom.hom hφFG)
  choose r fr hfr using hPtoSimple
  have hr_injective : Function.Injective r := by
    intro i j hij
    apply hdistinct i j
    exact projective_iso_of_nonzero_hom_to_simple
      (hindec i) (hindec j) (hproj i) (hproj j)
      (fr i) (hfr i) (fr j ≫ eqToHom (congrArg T hij).symm) (by
        intro hzero
        apply hfr j
        apply (cancel_mono (eqToHom (congrArg T hij).symm)).mp
        simpa only [zero_comp] using hzero)
  have hcard : Fintype.card κ = Fintype.card ι := by
    apply Nat.le_antisymm
    · exact Fintype.card_le_of_injective g hg_injective
    · exact Fintype.card_le_of_injective r hr_injective
  have hg_surjective : Function.Surjective g :=
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_injective, hcard⟩).2
  let σ : κ ≃ ι := Equiv.ofBijective g ⟨hg_injective, hg_surjective⟩
  let S : ι → C := fun i => T (σ.symm i)
  refine ⟨S, fun i => ?_, ?_, ?_, ?_⟩
  · dsimp only [S]
    exact hTsimple (σ.symm i)
  · intro i j hij
    apply σ.symm.injective
    exact hTdistinct _ _ hij
  · intro X hX
    obtain ⟨a, ⟨e⟩⟩ := hTcomplete X hX
    refine ⟨σ a, ⟨e ≪≫ eqToIso ?_⟩⟩
    exact congrArg T (σ.symm_apply_apply a).symm
  · intro i j
    let a : κ := σ.symm i
    let b : κ := σ.symm j
    obtain ⟨ea⟩ := hg a
    have hga : g a = i := by
      change σ a = i
      exact σ.apply_symm_apply i
    let ePiR : P i ≅ R a :=
      eqToIso (congrArg P hga.symm) ≪≫ ea.symm
    let eSource : E.functor.obj (P i) ≅ CoverFG a :=
      E.functor.mapIso ePiR ≪≫ E.counitIso.app (CoverFG a)
    let eMorita : (P i ⟶ T b) ≃ₗ[k] ((Q ⟶ P i) →ₗ[B] M b) :=
      { toFun := fun f => (E.functor.map f).hom.hom
        invFun := fun f => E.functor.preimage
          (InducedCategory.homMk (ModuleCat.ofHom f))
        left_inv := fun f => by
          apply E.functor.map_injective
          rw [E.functor.map_preimage]
          rfl
        right_inv := fun f => by
          have h := E.functor.map_preimage
            (InducedCategory.homMk (ModuleCat.ofHom f))
          exact ModuleCat.hom_ext_iff.mp (congrArg InducedCategory.Hom.hom h)
        map_add' := fun f g => by
          apply LinearMap.ext
          intro x
          change x ≫ (f + g) = x ≫ f + x ≫ g
          simp
        map_smul' := fun r f => by
          apply LinearMap.ext
          intro x
          change x ≫ (r • f) = r • (x ≫ f)
          simp }
    let ηPi : FGModuleCat.of B (Q ⟶ P i) ≅ E.functor.obj (P i) := by
      dsimp [E, Functor.asEquivalence, RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.fgModuleFunctor]
      exact Iso.refl _
    let eN : (Q ⟶ P i) ≃ₗ[B] Cover a :=
      FGModuleCat.isoToLinearEquiv (ηPi ≪≫ eSource)
    let ePrecomp : ((Q ⟶ P i) →ₗ[B] M b) ≃ₗ[k] (Cover a →ₗ[B] M b) :=
      { toFun := fun f => f.comp eN.symm.toLinearMap
        invFun := fun f => f.comp eN.toLinearMap
        left_inv := fun f => by ext x; simp
        right_inv := fun f => by ext x; simp
        map_add' := fun f g => by ext x; rfl
        map_smul' := fun r f => by ext x; rfl }
    change Module.finrank k (P i ⟶ T b) = if i = j then 1 else 0
    calc
      Module.finrank k (P i ⟶ T b) =
          Module.finrank k ((Q ⟶ P i) →ₗ[B] M b) := eMorita.finrank_eq
      _ = Module.finrank k (Cover a →ₗ[B] M b) := ePrecomp.finrank_eq
      _ = if a = b then 1 else 0 := hCoverDelta a b
      _ = if i = j then 1 else 0 := by
        simp only [a, b, σ.symm.injective.eq_iff]

end DeltaFamily

end RepresentationTheory.CategoryTheory.Indecomposable
