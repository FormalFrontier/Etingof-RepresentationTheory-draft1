import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Fitting
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Projection

universe u v u' v' w

/-!
# Categorical infrastructure for projective-cover delta-Hom families

This file records the equivalence-invariant facts needed to transport the module-theoretic
projective covers of Theorem 9.2.1 across the Morita equivalence of Theorem 9.6.4.

The main point is the categorical uniqueness statement
`projective_indecomposable_iso_of_hom_to_simple`: two indecomposable projective objects admitting
nonzero maps to the same simple object are isomorphic.  Its proof is the abstract finite-length
version of the Fitting-lemma argument already used for modules in `Theorem9_2_1.lean`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

section Equivalence

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]
variable {D : Type u'} [Category.{v'} D] [IsFiniteAbelianCategory D]

/-- An equivalence between finite abelian categories preserves indecomposable objects. -/
theorem indecomposable_map_equivalence (E : C ≌ D) {X : C}
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

section ModuleBridge

variable {R : Type u} [Ring R]

/-- Categorical indecomposability of a module implies the complemented-submodule formulation
`Etingof.IsIndecomposable` used by Theorem 9.2.1. -/
theorem isIndecomposable_of_categoryTheory_moduleCat
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : Indecomposable (ModuleCat.of R M)) : IsIndecomposable R M := by
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

end ModuleBridge

section Uniqueness

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

/-- Two indecomposable projective objects with nonzero maps to the same simple object are
isomorphic.

Projectivity lifts the two maps through each other.  The resulting endomorphisms fix the maps to
the simple object, so they cannot be nilpotent.  Fitting's dichotomy for an indecomposable object
therefore makes both composites isomorphisms, hence the original comparison is an isomorphism. -/
theorem projective_indecomposable_iso_of_hom_to_simple
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
    rcases isNilpotent_or_isIso_of_indecomposable hP a with hnil | hiso
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
    rcases isNilpotent_or_isIso_of_indecomposable hP' b with hnil | hiso
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

section LinearEquivalence

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]

/-- A `k`-linear categorical equivalence induces a linear equivalence on every Hom space. -/
noncomputable def equivalenceHomLinearEquiv (E : C ≌ D) [E.functor.Additive]
    [E.functor.Linear k] (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (E.functor.obj X ⟶ E.functor.obj Y) :=
  LinearEquiv.ofBijective (E.functor.mapLinearMap k)
    ⟨E.functor.map_injective, E.functor.map_surjective⟩

/-- A `k`-linear categorical equivalence preserves the dimension of Hom spaces. -/
theorem finrank_hom_eq_of_linear_equivalence (E : C ≌ D) [E.functor.Additive]
    [E.functor.Linear k] (X Y : C) :
    Module.finrank k (X ⟶ Y) = Module.finrank k (E.functor.obj X ⟶ E.functor.obj Y) :=
  (equivalenceHomLinearEquiv E X Y).finrank_eq

end LinearEquivalence

end Etingof
