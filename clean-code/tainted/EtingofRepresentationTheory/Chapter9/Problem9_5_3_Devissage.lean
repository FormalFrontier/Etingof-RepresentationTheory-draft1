import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.FiniteLength
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_CompositionFactor

/-!
# Problem 9.5.3(ii), step 2: the finite-length dévissage

This is **step 2** of the block dévissage for Etingof Problem 9.5.3(ii). The base case
(`Etingof.ext_subsingleton_of_not_areLinked`, step 1) says that two *simple* modules `S`, `T`
that are not linked have subsingleton `Ext¹(S, T)`. Here we generalize from simple modules to
**finite-length** modules:

> if every Jordan–Hölder composition factor `U` of `X` and `V` of `Y` are unlinked, then
> `Ext¹(X, Y)` is subsingleton.

The argument is a double dévissage on the `IsFiniteLength` structure. Fixing a simple `S` in
the first slot and inducting on `Y` gives `ext_simple_subsingleton_of_factors_unlinked`
(second-variable dévissage, using the covariant Ext long exact sequence). Feeding that in as
the "quotient" term, an induction on `X` in the first slot gives the general statement
(first-variable dévissage, using the contravariant Ext long exact sequence). Each inductive
step squeezes the middle `Ext¹` between two subsingleton flanking terms of a three-term exact
piece of the appropriate long exact sequence.

## Mathlib correspondence

Ext long exact sequences: `Abelian.Ext.covariant_sequence_exact₂`,
`Abelian.Ext.contravariant_sequence_exact₂`
(`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {R : Type u} [Ring R] [Small.{v} R]

/-- `Ext` out of a zero object vanishes: `Ext(Z, Y, n)` is subsingleton when `Z` is a zero
object. -/
theorem subsingleton_ext_of_isZero_left {Z Y : ModuleCat.{v} R} (hZ : IsZero Z) (n : ℕ) :
    Subsingleton (Abelian.Ext Z Y n) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Abelian.Ext Z Y n, x = 0 := by
    intro x
    rw [← Abelian.Ext.mk₀_id_comp x, hZ.eq_of_src (𝟙 Z) 0]
    simp
  rw [key a, key b]

/-- `Ext` into a zero object vanishes: `Ext(X, Z, n)` is subsingleton when `Z` is a zero
object. -/
theorem subsingleton_ext_of_isZero_right {X Z : ModuleCat.{v} R} (hZ : IsZero Z) (n : ℕ) :
    Subsingleton (Abelian.Ext X Z n) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Abelian.Ext X Z n, x = 0 := by
    intro x
    rw [← Abelian.Ext.comp_mk₀_id x, hZ.eq_of_src (𝟙 Z) 0]
    simp
  rw [key a, key b]

omit [Small.{v} R] in
/-- A simple module is a composition factor of itself. -/
theorem isCompositionFactor_self {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    IsCompositionFactor R S S :=
  isCompositionFactor_iff.mpr ⟨hS, ⊤, Submodule.topEquiv.toLinearMap, Submodule.topEquiv.surjective⟩

/-- The short exact sequence `0 → ↥N → Y → Y ⧸ N → 0` in `ModuleCat R` attached to a
submodule `N`. -/
private def submoduleSES {Y : Type v} [AddCommGroup Y] [Module R Y] (N : Submodule R Y) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by ext x; simp)

omit [Small.{v} R] in
private theorem submoduleSES_shortExact {Y : Type v} [AddCommGroup Y] [Module R Y]
    (N : Submodule R Y) : (submoduleSES N).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective

/-- **Second-variable dévissage.** For a *simple* module `S` and a finite-length module `Y`
all of whose composition factors are unlinked to `S`, the group `Ext¹(S, Y)` is subsingleton.
Induct on the finite length of `Y`, using the covariant Ext long exact sequence for the short
exact sequence `0 → N → Y → Y ⧸ N → 0`. -/
theorem ext_simple_subsingleton_of_factors_unlinked
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∀ {Y : Type v} [AddCommGroup Y] [Module R Y], IsFiniteLength R Y →
      (∀ V : ModuleCat.{v} R, IsCompositionFactor R (ModuleCat.of R Y) V → ¬ AreLinked R S V) →
      Subsingleton (Abelian.Ext S (ModuleCat.of R Y) 1) := by
  intro Y _ _ hY
  induction hY with
  | @of_subsingleton Y _ _ _ =>
      intro _
      exact subsingleton_ext_of_isZero_right
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R Y)) 1
  | @of_simple_quotient Y _ _ N _ hN ih =>
      intro h
      -- `T = Y ⧸ N` is a simple quotient, hence a composition factor of `Y`.
      set T : ModuleCat.{v} R := ModuleCat.of R (Y ⧸ N) with hT_def
      have hT : IsSimpleModule R T := ‹IsSimpleModule R (Y ⧸ N)›
      have hcfT : IsCompositionFactor R (ModuleCat.of R Y) T :=
        IsCompositionFactor.of_surjective N.mkQ N.mkQ_surjective (isCompositionFactor_self hT)
      -- Flanking subsingleton terms.
      have hExtN : Subsingleton (Abelian.Ext S (ModuleCat.of R N) 1) :=
        ih (fun V hcf => h V (IsCompositionFactor.of_submodule N hcf))
      have hExtT : Subsingleton (Abelian.Ext S T 1) := by
        rw [← not_nontrivial_iff_subsingleton]
        intro hnt
        exact h T hcfT (areLinked_of_extAdjacent R hS hT (Or.inl hnt))
      -- Squeeze `Ext¹(S, Y)` between them via the covariant long exact sequence.
      have hSE := submoduleSES_shortExact N
      haveI : Subsingleton (Abelian.Ext S (submoduleSES N).X₁ 1) := hExtN
      haveI : Subsingleton (Abelian.Ext S (submoduleSES N).X₃ 1) := hExtT
      have hX₂ : Subsingleton (Abelian.Ext S (submoduleSES N).X₂ 1) := by
        refine ⟨fun a b => ?_⟩
        suffices key : ∀ x : Abelian.Ext S (submoduleSES N).X₂ 1, x = 0 by rw [key a, key b]
        intro x
        obtain ⟨x₁, hx₁⟩ :=
          Abelian.Ext.covariant_sequence_exact₂ S hSE x (Subsingleton.elim _ _)
        rw [← hx₁, Subsingleton.elim x₁ 0, Abelian.Ext.zero_comp]
      exact hX₂

/-- **The finite-length dévissage (Problem 9.5.3(ii), step 2).** If `X` and `Y` are
finite-length modules such that every composition factor `U` of `X` and `V` of `Y` are
unlinked, then `Ext¹(X, Y)` is subsingleton. -/
theorem ext_subsingleton_of_factors_unlinked
    {Y : ModuleCat.{v} R} (hY : IsFiniteLength R Y) :
    ∀ {X : Type v} [AddCommGroup X] [Module R X], IsFiniteLength R X →
      (∀ U V : ModuleCat.{v} R, IsCompositionFactor R (ModuleCat.of R X) U →
        IsCompositionFactor R Y V → ¬ AreLinked R U V) →
      Subsingleton (Abelian.Ext (ModuleCat.of R X) Y 1) := by
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
      intro _
      exact subsingleton_ext_of_isZero_left
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R X)) 1
  | @of_simple_quotient X _ _ N _ hN ih =>
      intro h
      set S₀ : ModuleCat.{v} R := ModuleCat.of R (X ⧸ N) with hS₀_def
      have hS₀ : IsSimpleModule R S₀ := ‹IsSimpleModule R (X ⧸ N)›
      have hcfS₀ : IsCompositionFactor R (ModuleCat.of R X) S₀ :=
        IsCompositionFactor.of_surjective N.mkQ N.mkQ_surjective (isCompositionFactor_self hS₀)
      -- Flanking subsingleton terms.
      have hExtN : Subsingleton (Abelian.Ext (ModuleCat.of R N) Y 1) :=
        ih (fun U V hU hV => h U V (IsCompositionFactor.of_submodule N hU) hV)
      have hExtS₀ : Subsingleton (Abelian.Ext S₀ Y 1) :=
        ext_simple_subsingleton_of_factors_unlinked hS₀ hY
          (fun V hcfV => h S₀ V hcfS₀ hcfV)
      -- Squeeze `Ext¹(X, Y)` between them via the contravariant long exact sequence.
      have hSE := submoduleSES_shortExact N
      haveI : Subsingleton (Abelian.Ext (submoduleSES N).X₁ Y 1) := hExtN
      haveI : Subsingleton (Abelian.Ext (submoduleSES N).X₃ Y 1) := hExtS₀
      have hX₂ : Subsingleton (Abelian.Ext (submoduleSES N).X₂ Y 1) := by
        refine ⟨fun a b => ?_⟩
        suffices key : ∀ x : Abelian.Ext (submoduleSES N).X₂ Y 1, x = 0 by rw [key a, key b]
        intro x
        obtain ⟨x₁, hx₁⟩ :=
          Abelian.Ext.contravariant_sequence_exact₂ hSE Y x (Subsingleton.elim _ _)
        rw [← hx₁, Subsingleton.elim x₁ 0, Abelian.Ext.comp_zero]
      exact hX₂

/-- Object-level restatement of `ext_subsingleton_of_factors_unlinked` matching the
`ModuleCat`-object phrasing used downstream (Problem 9.5.3(ii)). -/
theorem ext_subsingleton_of_compositionFactors_unlinked
    {X Y : ModuleCat.{v} R} (hX : IsFiniteLength R X) (hY : IsFiniteLength R Y)
    (h : ∀ U V : ModuleCat.{v} R, IsCompositionFactor R X U → IsCompositionFactor R Y V →
      ¬ AreLinked R U V) :
    Subsingleton (Abelian.Ext X Y 1) :=
  ext_subsingleton_of_factors_unlinked hY hX h

end Etingof
