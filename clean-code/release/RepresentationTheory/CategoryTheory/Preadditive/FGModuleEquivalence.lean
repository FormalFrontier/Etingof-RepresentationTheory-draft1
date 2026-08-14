/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import RepresentationTheory.RingAuxiliary
import RepresentationTheory.CategoryTheory.Abelian.FiniteLength
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Abelian.Yoneda
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finitely generated module equivalences

This module provides conditions under which the preadditive coyoneda functor to finitely generated
modules over an opposite endomorphism ring is an equivalence.
-/

universe u v w


open CategoryTheory CategoryTheory.Limits
open RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
open RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
open RepresentationTheory.CategoryTheory.Abelian.FiniteLength

namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

/-- The given object is a separator. -/
theorem HasProjectiveEpiWitnesses.isSeparator {C : Type u} [Category.{v} C]
    [Preadditive C] {P : C} [hp : HasProjectiveEpiWitnesses P] : IsSeparator P := by
  rw [Preadditive.isSeparator_iff]
  intro X Y f hf
  obtain ⟨n, hbp, π, hπ⟩ := hp.exists_epi X
  have : π ≫ f = 0 := by
    apply @biproduct.hom_ext' _ _ _ _ (fun _ : Fin n => P) hbp
    intro i
    simp only [comp_zero]
    rw [← Category.assoc]
    exact hf _
  exact (cancel_epi π).mp (by rw [this, comp_zero])

/-- The given object satisfies the additional displayed property. -/
theorem HasProjectiveEpiWitnesses.hasAssociatedProperty {C : Type u} [Category.{v} C]
    [Preadditive C] {P : C} [hp : HasProjectiveEpiWitnesses P] :
    IsProjectiveEpiSigmaDesc P :=
  ⟨hp.toProjective, HasProjectiveEpiWitnesses.isSeparator⟩

/-- The preadditive coyoneda functor at the given object is faithful. -/
instance HasProjectiveEpiWitnesses.preadditiveCoyonedaObj_faithful
    {C : Type u} [Category.{v} C] [Preadditive C]
    {P : C} [HasProjectiveEpiWitnesses P] :
    (preadditiveCoyonedaObj P).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj P).mp
    HasProjectiveEpiWitnesses.isSeparator

set_option synthInstance.maxHeartbeats 40000 in
-- Required for the fullness proof.
/-- The preadditive coyoneda functor at the given object is full. -/
instance HasProjectiveEpiWitnesses.preadditiveCoyonedaObj_full
    {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C]
    {P : C} [hp : HasProjectiveEpiWitnesses P] :
    (preadditiveCoyonedaObj P).Full := by
  haveI : Projective P := hp.toProjective
  constructor
  intro X Y f
  obtain ⟨n, hbp, π, hπ⟩ := hp.exists_epi X
  haveI : HasBiproduct (fun _ : Fin n => P) := hbp
  let F := fun _ : Fin n => P
  have hlin : ∀ (s : P ⟶ P) (g : P ⟶ X),
      (f : (P ⟶ X) → (P ⟶ Y)) (s ≫ g) = s ≫ (f : (P ⟶ X) → (P ⟶ Y)) g := by
    intro s g
    have := f.hom.map_smul (MulOpposite.op s) g
    exact this
  let h : ⨁ F ⟶ Y :=
    biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π))
  have h_kernel : kernel.ι π ≫ h = 0 := by
    have hSep := HasProjectiveEpiWitnesses.isSeparator (P := P)
    rw [Preadditive.isSeparator_iff] at hSep
    apply hSep
    intro φ
    rw [← Category.assoc]
    show (φ ≫ kernel.ι π) ≫ h = 0
    change (φ ≫ kernel.ι π) ≫
      biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π)) = 0
    rw [biproduct.desc_eq, Preadditive.comp_sum]
    simp_rw [← Category.assoc _ (biproduct.π _ _), ← hlin]
    refine (map_sum (ConcreteCategory.hom f) _ Finset.univ).symm.trans ?_
    have key : (∑ x, ((φ ≫ kernel.ι π) ≫ biproduct.π (fun _ : Fin n => P) x) ≫
        (biproduct.ι F x ≫ π) : P ⟶ X) = 0 := by
      simp_rw [Category.assoc, ← Preadditive.comp_sum]
      have : ∑ j : Fin n, biproduct.π F j ≫ biproduct.ι F j ≫ π = π := by
        simp_rw [← Category.assoc]
        rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
      rw [this, kernel.condition, comp_zero]
    exact (congrArg (ConcreteCategory.hom f) key).trans (map_zero _)
  refine ⟨Abelian.epiDesc π h h_kernel, ?_⟩
  have hcomp : π ≫ Abelian.epiDesc π h h_kernel = h := Abelian.comp_epiDesc π h h_kernel
  ext α
  have hβ : Projective.factorThru α π ≫ π = α := Projective.factorThru_comp α π
  change α ≫ Abelian.epiDesc π h h_kernel =
    (f : (P ⟶ X) → (P ⟶ Y)) α
  rw [← hβ, Category.assoc, hcomp]
  change Projective.factorThru α π ≫
    biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π)) = _
  rw [biproduct.desc_eq, Preadditive.comp_sum]
  simp_rw [← Category.assoc _ (biproduct.π _ _), ← hlin]
  refine (map_sum (ConcreteCategory.hom f) _ Finset.univ).symm.trans ?_
  have key : (∑ j, (Projective.factorThru α π ≫ biproduct.π (fun _ : Fin n => P) j) ≫
      (biproduct.ι F j ≫ π) : P ⟶ X) = Projective.factorThru α π ≫ π := by
    simp_rw [Category.assoc, ← Preadditive.comp_sum]
    have : ∑ j : Fin n, biproduct.π F j ≫ biproduct.ι F j ≫ π = π := by
      simp_rw [← Category.assoc]
      rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
    rw [this]
  exact congrArg (ConcreteCategory.hom f) key

/-- Morphisms out of the given object form a finite module over its opposite endomorphism ring. -/
instance HasProjectiveEpiWitnesses.hom_finite
    {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C]
    {P : C} [hp : HasProjectiveEpiWitnesses P] (X : C) :
    Module.Finite (End P)ᵐᵒᵖ (P ⟶ X) := by
  obtain ⟨n, hbp, π, hπ⟩ := hp.exists_epi X
  haveI : HasBiproduct (fun _ : Fin n => P) := hbp
  haveI : Projective P := hp.toProjective
  let φ : (P ⟶ biproduct (fun _ : Fin n => P)) →ₗ[(End P)ᵐᵒᵖ] (P ⟶ X) :=
    ((preadditiveCoyonedaObj P).map π).hom
  have hφ_surj : Function.Surjective φ := by
    intro f
    exact ⟨Projective.factorThru f π, Projective.factorThru_comp f π⟩
  haveI : Module.Finite (End P)ᵐᵒᵖ (P ⟶ biproduct (fun _ : Fin n => P)) := by
    let F := fun _ : Fin n => P
    haveI : Module.Finite (End P)ᵐᵒᵖ (End P) := by
      constructor
      refine ⟨{𝟙 P}, ?_⟩
      rw [Submodule.eq_top_iff']
      intro f
      have hmem : 𝟙 P ∈ Submodule.span (End P)ᵐᵒᵖ
          (↑({𝟙 P} : Finset _) : Set _) :=
        Submodule.subset_span (by simp)
      have hsmul : MulOpposite.op f • (𝟙 P : End P) = f := by
        change f ≫ 𝟙 P = f; simp
      rw [← hsmul]
      exact Submodule.smul_mem _ _ hmem
    haveI : Module.Finite (End P)ᵐᵒᵖ (Fin n → End P) := Module.Finite.pi
    exact Module.Finite.of_surjective
      ({ toFun := fun f => biproduct.lift (fun i => f i)
         map_add' := fun f g => by
           apply biproduct.hom_ext; intro i
           set_option backward.isDefEq.respectTransparency false in
           simp only [Preadditive.add_comp, biproduct.lift_π, Pi.add_apply]
         map_smul' := fun s f => by
           apply biproduct.hom_ext; intro i
           simp only [RingHom.id_apply, biproduct.lift_π]
           change s.unop ≫ f i =
             (s.unop ≫ biproduct.lift fun j => f j) ≫ biproduct.π F i
           rw [Category.assoc, biproduct.lift_π] } :
        (Fin n → End P) →ₗ[(End P)ᵐᵒᵖ] (P ⟶ biproduct F))
      (fun g => ⟨fun i => g ≫ biproduct.π F i, by
        apply @biproduct.hom_ext _ _ _ _ F hbp; intro i
        change (biproduct.lift fun j => g ≫ biproduct.π F j) ≫ biproduct.π F i =
             g ≫ biproduct.π F i
        exact biproduct.lift_π _ _⟩)
  exact Module.Finite.of_surjective φ hφ_surj

/--
A functor from the given category to finitely generated modules over the opposite endomorphism
ring of the given object. -/
noncomputable def HasProjectiveEpiWitnesses.fgModuleFunctor
    {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C]
    {P : C} [hp : HasProjectiveEpiWitnesses P] :
    C ⥤ FGModuleCat.{v} (End P)ᵐᵒᵖ where
  obj X := ⟨(preadditiveCoyonedaObj P).obj X, hp.hom_finite X⟩
  map f := InducedCategory.homMk ((preadditiveCoyonedaObj P).map f)
  map_id X := by
    apply InducedCategory.hom_ext
    change (preadditiveCoyonedaObj P).map (𝟙 X) = 𝟙 _
    exact (preadditiveCoyonedaObj P).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    change (preadditiveCoyonedaObj P).map (f ≫ g) =
      (preadditiveCoyonedaObj P).map f ≫ (preadditiveCoyonedaObj P).map g
    exact (preadditiveCoyonedaObj P).map_comp f g

end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

namespace RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional

set_option linter.dupNamespace false in
/-- The displayed categorical assumption entails finite biproducts. -/
noncomputable instance SubobjectFiniteDimensional.hasFiniteBiproducts
    {C : Type u} [Category.{v} C] [h : SubobjectFiniteDimensional C] :
    HasFiniteBiproducts C := Abelian.hasFiniteBiproducts

end RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional

private lemma unop_mul_eq_comp {C : Type u} [Category.{v} C] {P : C}
    (s r : (End P)ᵐᵒᵖ) : (s * r).unop = s.unop ≫ r.unop := by
  rw [MulOpposite.unop_mul]; rfl

private noncomputable def freeModuleIsoHom
    {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => P)] :
    (Fin n → (End P)ᵐᵒᵖ) ≃ₗ[(End P)ᵐᵒᵖ] (P ⟶ ⨁ (fun _ : Fin n => P)) where
  toFun v := biproduct.lift (fun i => (v i).unop)
  invFun g := fun i => MulOpposite.op (g ≫ biproduct.π _ i)
  left_inv v := by ext i; simp [biproduct.lift_π]
  right_inv g := by apply biproduct.hom_ext; intro i; simp [biproduct.lift_π]
  map_add' a b := by
    apply biproduct.hom_ext; intro i
    set_option backward.isDefEq.respectTransparency false in
    simp only [biproduct.lift_π, MulOpposite.unop_add, Preadditive.add_comp, Pi.add_apply]
  map_smul' s v := by
    apply biproduct.hom_ext; intro i
    simp only [biproduct.lift_π, RingHom.id_apply]
    change (s * v i).unop = (s.unop ≫ biproduct.lift fun j => (v j).unop) ≫ biproduct.π _ i
    rw [Category.assoc, biproduct.lift_π, unop_mul_eq_comp]

namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

set_option maxHeartbeats 400000 in
-- Required for the essential-surjectivity proof.
/--
With a noetherian opposite endomorphism ring, the associated module functor is essentially
surjective. -/
instance HasProjectiveEpiWitnesses.fgModuleFunctor_essentiallySurjective
    {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C]
    {P : C} [hp : HasProjectiveEpiWitnesses P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
    hp.fgModuleFunctor.EssSurj := by
  constructor
  intro M
  let R := (End P)ᵐᵒᵖ
  haveI : Projective P := hp.toProjective
  haveI : Module.Finite R ↑M.obj := M.property
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R ↑M.obj
  haveI : Module.Finite R (LinearMap.ker φ) :=
    IsNoetherian.noetherian (LinearMap.ker φ) |>.choose_spec ▸ inferInstance
  obtain ⟨m, ψ, hψ⟩ := Module.Finite.exists_fin' R (LinearMap.ker φ)
  let α : (Fin m → R) →ₗ[R] (Fin n → R) := (LinearMap.ker φ).subtype.comp ψ
  let Fm := fun _ : Fin m => P
  let Fn := fun _ : Fin n => P
  let βm := freeModuleIsoHom P m
  let βn := freeModuleIsoHom P n
  let α' : (P ⟶ ⨁ Fm) →ₗ[R] (P ⟶ ⨁ Fn) :=
    βn.toLinearMap.comp (α.comp βm.symm.toLinearMap)
  have hFull := HasProjectiveEpiWitnesses.preadditiveCoyonedaObj_full (P := P)
  obtain ⟨f, hf⟩ := hFull.map_surjective
    (ModuleCat.ofHom α' : (preadditiveCoyonedaObj P).obj (⨁ Fm) ⟶
      (preadditiveCoyonedaObj P).obj (⨁ Fn))
  let X := cokernel f
  let ε : (P ⟶ ⨁ Fn) →ₗ[R] ↑M.obj := φ.comp βn.symm.toLinearMap
  have hε_surj : Function.Surjective ε := by
    intro x; obtain ⟨y, hy⟩ := hφ x
    exact ⟨βn y, by change φ (βn.symm (βn y)) = x; rw [LinearEquiv.symm_apply_apply]; exact hy⟩
  let π_star : (P ⟶ ⨁ Fn) →ₗ[R] (P ⟶ X) :=
    ((preadditiveCoyonedaObj P).map (cokernel.π f)).hom
  have hπ_surj : Function.Surjective π_star := by
    intro g; exact ⟨Projective.factorThru g (cokernel.π f),
      Projective.factorThru_comp g (cokernel.π f)⟩
  have hker_eq : LinearMap.ker ε = LinearMap.ker π_star := by
    ext g
    constructor
    · -- ker ε ⊆ ker π_star: if ε(g) = 0 then g ∈ Im(α') so g ≫ cokernel.π = 0
      intro hg
      simp only [LinearMap.mem_ker] at hg ⊢
      have hg_ker : βn.symm g ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]; simp only [FGModuleCat.obj_carrier] at hg; exact hg
      obtain ⟨w, hw⟩ := hψ ⟨βn.symm g, hg_ker⟩
      have hα'_eq : ∀ k, α' k = k ≫ f := by
        intro k
        change α' k = ((preadditiveCoyonedaObj P).map f).hom k
        conv_rhs => rw [hf]; simp [ModuleCat.hom_ofHom]
        rfl
      have hg_eq : g = α' (βm w) := by
        change g = βn (α (βm.symm (βm w)))
        simp only [LinearEquiv.symm_apply_apply]
        change g = βn ((LinearMap.ker φ).subtype (ψ w))
        rw [hw]; simp [LinearEquiv.apply_symm_apply]
      rw [hg_eq, hα'_eq]
      change (βm w ≫ f) ≫ cokernel.π f = 0
      rw [Category.assoc, cokernel.condition, comp_zero]
    · -- ker π_star ⊆ ker ε: if g ≫ cokernel.π = 0 then g factors through f
      intro hg
      simp only [LinearMap.mem_ker] at hg ⊢
      have hg_zero : g ≫ cokernel.π f = 0 := hg
      let g_lift := kernel.lift (cokernel.π f) g hg_zero
      let img_iso := Abelian.imageIsoImage f
      let h := Projective.factorThru g_lift (Abelian.factorThruImage f)
      have hh : h ≫ f = g := by
        have h1 := Projective.factorThru_comp g_lift (Abelian.factorThruImage f)
        have h2 := Abelian.image.fac f
        calc h ≫ f = h ≫ (Abelian.factorThruImage f ≫ Abelian.image.ι f) := by rw [h2]
          _ = (h ≫ Abelian.factorThruImage f) ≫ Abelian.image.ι f := by rw [Category.assoc]
          _ = g_lift ≫ Abelian.image.ι f := by rw [h1]
          _ = g_lift ≫ kernel.ι (cokernel.π f) := rfl
          _ = g := kernel.lift_ι (cokernel.π f) g hg_zero
      rw [← hh]
      change φ (βn.symm (h ≫ f)) = 0
      have hα'_eq : ∀ k, α' k = k ≫ f := by
        intro k
        change α' k = ((preadditiveCoyonedaObj P).map f).hom k
        conv_rhs => rw [hf]; simp [ModuleCat.hom_ofHom]
        rfl
      rw [← hα'_eq]
      change φ (βn.symm (βn (α (βm.symm h)))) = 0
      rw [LinearEquiv.symm_apply_apply]
      exact LinearMap.mem_ker.mp (ψ (βm.symm h)).property
  let iso1 := ε.quotKerEquivOfSurjective hε_surj
  let iso2 := Submodule.quotEquivOfEq _ _ hker_eq
  let iso3 := π_star.quotKerEquivOfSurjective hπ_surj
  let full_iso : (P ⟶ X) ≃ₗ[R] ↑M.obj := iso3.symm.trans (iso2.symm.trans iso1)
  exact ⟨cokernel f, ⟨{
    hom := InducedCategory.homMk (ModuleCat.ofHom full_iso.toLinearMap)
    inv := InducedCategory.homMk (ModuleCat.ofHom full_iso.symm.toLinearMap)
    hom_inv_id := by apply InducedCategory.hom_ext; ext x; exact full_iso.left_inv x
    inv_hom_id := by apply InducedCategory.hom_ext; ext x; exact full_iso.right_inv x
  }⟩⟩

end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

namespace RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence

/-- Under the displayed field-linear hypotheses, the opposite endomorphism ring is noetherian. -/
theorem opEnd_isNoetherian
    {k : Type w} [Field k] {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] [Linear k C]
    [SchurFiniteLengthCategory k C] (P : C) :
    IsNoetherianRing (End P)ᵐᵒᵖ := by
  haveI : FiniteDimensional k (End P) :=
    SchurFiniteLengthCategory.finiteDimensional_hom P P
  haveI : IsNoetherian k (End P)ᵐᵒᵖ := inferInstance
  exact isNoetherian_of_tower k inferInstance

/-- The module functor is an equivalence when the opposite endomorphism ring is noetherian. -/
theorem fgModuleFunctor_isEquivalence_of_noetherian
    {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C]
    {P : C} [hp : HasProjectiveEpiWitnesses P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
    hp.fgModuleFunctor.IsEquivalence where
  essSurj := hp.fgModuleFunctor_essentiallySurjective
  faithful :=
    { map_injective := fun {X Y f g} h => by
        have hF := HasProjectiveEpiWitnesses.preadditiveCoyonedaObj_faithful (P := P)
        apply hF.map_injective
        have : (hp.fgModuleFunctor.map f).hom =
               (hp.fgModuleFunctor.map g).hom := congrArg InducedCategory.Hom.hom h
        exact this }
  full :=
    { map_surjective := fun {X Y} f => by
        have hF := HasProjectiveEpiWitnesses.preadditiveCoyonedaObj_full (P := P)
        obtain ⟨g, hg⟩ := hF.map_surjective f.hom
        exact ⟨g, InducedCategory.hom_ext hg⟩ }

/-- Under the displayed field-linear hypotheses, the module functor is an equivalence. -/
theorem fgModuleFunctor_isEquivalence
    {k : Type w} [Field k] {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] [Linear k C]
    [SchurFiniteLengthCategory k C]
    {P : C} [hp : HasProjectiveEpiWitnesses P] :
    hp.fgModuleFunctor.IsEquivalence :=
  haveI : IsNoetherianRing (End P)ᵐᵒᵖ :=
    opEnd_isNoetherian (k := k) P
  fgModuleFunctor_isEquivalence_of_noetherian

/--
A noetherian opposite endomorphism ring gives an equivalence with its finitely generated
modules. -/
theorem nonempty_fgModuleEquivalence_of_noetherian
    (C : Type u) [Category.{v} C]
    [SubobjectFiniteDimensional C]
    (P : C) [hp : HasProjectiveEpiWitnesses P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
    Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) := by
  haveI := fgModuleFunctor_isEquivalence_of_noetherian (P := P)
  exact ⟨hp.fgModuleFunctor.asEquivalence⟩

/--
Under the displayed field-linear hypotheses, an equivalence with finitely generated modules
over the opposite endomorphism ring exists. -/
theorem nonempty_fgModuleEquivalence
    {k : Type w} [Field k] (C : Type u) [Category.{v} C]
    [SubobjectFiniteDimensional C] [Linear k C]
    [SchurFiniteLengthCategory k C]
    (P : C) [hp : HasProjectiveEpiWitnesses P] :
    Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) :=
  haveI : IsNoetherianRing (End P)ᵐᵒᵖ :=
    opEnd_isNoetherian (k := k) P
  nonempty_fgModuleEquivalence_of_noetherian C P

end RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
