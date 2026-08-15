/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Projective module objects under scalar restriction and extension

This module transfers projectivity, projective-dimension bounds, and subsingleton Ext properties
across the extension-restriction adjunction for module categories.
-/

set_option linter.dupNamespace false

universe u

open CategoryTheory Limits
open _root_.ModuleCat

namespace RepresentationTheory.Algebra.Category.ModuleCat.Projective

namespace ModuleCat

section PreservesEpimorphisms

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars preserves epimorphisms of module objects. -/
instance restrictScalars_preservesEpimorphisms :
    (restrictScalars f).PreservesEpimorphisms where
  preserves {X Y} g hg := by
    rw [ModuleCat.epi_iff_surjective] at hg ⊢
    exact hg

/-- Extension of scalars preserves projective module objects. -/
instance extendScalars_preservesProjectiveObjects :
    (extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (extendRestrictScalarsAdj.{u} f)

end PreservesEpimorphisms

section HasProjectiveDimensionLT

open Abelian

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars preserves a strict projective-dimension bound. -/
theorem hasProjectiveDimensionLT_restrictScalars
    [(restrictScalars.{u} f).PreservesProjectiveObjects]
    [(restrictScalars.{u} f).PreservesHomology]
    (X : ModuleCat.{u} S) :
    ∀ (n : ℕ), HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT ((restrictScalars f).obj X) n := by
  intro n
  induction n generalizing X with
  | zero =>
    intro h
    have hX := isZero_of_hasProjectiveDimensionLT_zero X
    exact ((restrictScalars f).map_isZero hX).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr h
      have : Projective ((restrictScalars f).obj X) :=
        Functor.PreservesProjectiveObjects.projective_obj hproj
      exact projective_iff_hasProjectiveDimensionLT_one.mp this
    | succ k =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation X
      let SC := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (k + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (k + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (k + 1) (by omega))
          h
      have hGK := ih (kernel pp.f) hK
      have hGSE : (SC.map (restrictScalars f)).ShortExact :=
        hSE.map_of_exact (restrictScalars f)
      have hGP_proj : Projective ((restrictScalars f).obj pp.p) :=
        Functor.PreservesProjectiveObjects.projective_obj pp.projective
      exact hGSE.hasProjectiveDimensionLT_X₃ (k + 1) hGK
        (hasProjectiveDimensionLT_of_ge ((restrictScalars f).obj pp.p) 1 (k + 2)
          (by omega))

/-- A retract of the restriction of its scalar extension inherits any strict projective-dimension
bound held by that extension. -/
theorem hasProjectiveDimensionLT_of_retract_restrictScalars_extendScalars
    [Small.{u} R] [Small.{u} S]
    [(restrictScalars.{u} f).PreservesProjectiveObjects]
    [(restrictScalars.{u} f).PreservesHomology]
    (M : ModuleCat.{u} R) (n : ℕ)
    (retraction : Retract M ((restrictScalars f).obj ((extendScalars f).obj M)))
    (h : HasProjectiveDimensionLT ((extendScalars f).obj M) n) :
    HasProjectiveDimensionLT M n := by
  have hG := hasProjectiveDimensionLT_restrictScalars f
    ((extendScalars f).obj M) n h
  exact retraction.hasProjectiveDimensionLT n

end HasProjectiveDimensionLT

section ExtSubsingleton

open Abelian

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The adjunction homEquiv commutes with precomposition by the functor map.
This is the naturality of `adj.homEquiv` in the first variable. -/
private lemma adj_homEquiv_naturality_left
    {X X' : ModuleCat.{u} R} {Y : ModuleCat.{u} S} (d : X' ⟶ X)
    (g : (extendScalars.{u, u, u} f).obj X ⟶ Y) :
    (extendRestrictScalarsAdj.{u} f).homEquiv X' Y
      ((extendScalars.{u, u, u} f).map d ≫ g) =
    d ≫ (extendRestrictScalarsAdj.{u} f).homEquiv X Y g := by
  simp [Adjunction.homEquiv_naturality_left]

/-- A subsingleton Ext type from an extended module yields the corresponding subsingleton Ext type
into a restricted module. -/
theorem subsingleton_ext_restrictScalars_of_subsingleton_ext_extendScalars
    [Small.{u} R] [Small.{u} S]
    [(extendScalars.{u, u, u} f).PreservesHomology]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (i : ℕ)
    (h : Subsingleton (Ext.{u} ((extendScalars.{u, u, u} f).obj M) N i)) :
    Subsingleton (Ext.{u} M ((restrictScalars.{u} f).obj N) i) := by
  set F := extendScalars.{u, u, u} f
  set G := restrictScalars.{u} f
  set adj := extendRestrictScalarsAdj.{u} f
  letI : EnoughProjectives (ModuleCat.{u} R) := ModuleCat.enoughProjectives.{u}
  letI : EnoughProjectives (ModuleCat.{u} S) := ModuleCat.enoughProjectives.{u}
  letI : F.Additive := Adjunction.left_adjoint_additive adj
  have ⟨P⟩ : Nonempty (ProjectiveResolution M) :=
    (inferInstance : HasProjectiveResolution M).out
  let FP : ProjectiveResolution (F.obj M) := F.mapProjectiveResolution P
  constructor
  intro e₁ e₂
  match i with
  | 0 =>
    apply Ext.addEquiv₀.injective
    have hHomS : Subsingleton (F.obj M ⟶ N) := by
      constructor; intro a b
      exact Ext.addEquiv₀.symm.injective (h.elim _ _)
    have : Subsingleton (M ⟶ G.obj N) := by
      constructor; intro a b
      exact (adj.homEquiv M N).symm.injective (Subsingleton.elim _ _)
    exact Subsingleton.elim _ _
  | n + 1 =>
    have hsub : e₁ - e₂ = 0 := by
      obtain ⟨g, hg, hge⟩ := P.extMk_surjective (e₁ - e₂) (n + 2) rfl
      set g' : FP.complex.X (n + 1) ⟶ N :=
        (adj.homEquiv (P.complex.X (n + 1)) N).symm g with hg'_def
      have hg'_cocycle : FP.complex.d (n + 2) (n + 1) ≫ g' = 0 := by
        rw [hg'_def]
        have : FP.complex.d (n + 2) (n + 1) =
            F.map (P.complex.d (n + 2) (n + 1)) := rfl
        rw [this]
        change (extendScalars f).map (P.complex.d (n + 2) (n + 1)) ≫
          (adj.homEquiv (P.complex.X (n + 1)) N).symm g = 0
        rw [← adj.homEquiv_naturality_left_symm (P.complex.d (n + 2) (n + 1)) g]
        simp [hg]
      have he' : FP.extMk g' (n + 2) rfl hg'_cocycle = 0 := h.elim _ _
      rw [FP.extMk_eq_zero_iff g' (n + 2) rfl hg'_cocycle n rfl] at he'
      obtain ⟨φ', hφ'⟩ := he'
      set φ := (adj.homEquiv (P.complex.X n) N) φ' with hφ_def
      have hcoboundary : P.complex.d (n + 1) n ≫ φ = g := by
        rw [hφ_def, ← adj_homEquiv_naturality_left f (P.complex.d (n + 1) n) φ']
        have : F.map (P.complex.d (n + 1) n) = FP.complex.d (n + 1) n := rfl
        rw [this]
        change (adj.homEquiv (P.complex.X (n + 1)) N)
          (FP.complex.d (n + 1) n ≫ φ') = g
        exact (congrArg (adj.homEquiv (P.complex.X (n + 1)) N) hφ').trans
          (by rw [hg'_def, Equiv.apply_symm_apply])
      rw [← hge, P.extMk_eq_zero_iff g (n + 2) rfl hg n rfl]
      exact ⟨φ, hcoboundary⟩
    exact sub_eq_zero.mp hsub

end ExtSubsingleton

end ModuleCat

end RepresentationTheory.Algebra.Category.ModuleCat.Projective
