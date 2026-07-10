import EtingofRepresentationTheory.Chapter8.Horseshoe
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Homology.ExactSequence

/-!
# The six-term exact sequence of a left derived functor

Given an additive functor `F : C ⥤ D` between abelian categories, with `C` having enough
projectives, and a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in `C`, the left derived
functors `F.leftDerived n` fit into a long exact sequence.  This file proves the six-term window

`Lₙ₁(X₁) → Lₙ₁(X₂) → Lₙ₁(X₃) →[δ] Lₙ₀(X₁) → Lₙ₀(X₂) → Lₙ₀(X₃)`  (for `n₀ + 1 = n₁`)

as `Etingof.Functor.leftDerived_sixTerm_exact`.

The proof runs through the horseshoe lemma (`Etingof.horseshoe`): choose projective resolutions
`P₁, P₃` of `X₁, X₃`, obtain a projective resolution `P₂` of `X₂` sitting in a short exact
sequence of complexes `0 → P₁ → P₂ → P₃ → 0` lifting `S`.  This sequence is *degreewise split*
(each degree is `0 → P₁ᵢ → P₁ᵢ ⊞ P₃ᵢ → P₃ᵢ → 0`, and `P₃ᵢ` is projective), so the additive
functor `F` preserves its short exactness.  Applying the homology long exact sequence
(`HomologicalComplex.HomologySequence`) to the image complexes and transporting along
`ProjectiveResolution.isoLeftDerivedObj` (whose naturality uses exactly the augmentation squares
the horseshoe provides) yields the six-term exact window.

This lemma is the reusable crux for the `Tor` long exact sequence in the first argument
(`Problem_8_2_6_v_tor`) and the corresponding `Ext` half.
-/

universe v u v' u'

open CategoryTheory Category Limits ComposableArrows

namespace Etingof

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]

omit [EnoughProjectives C] in
/-- An additive functor preserves a short exact sequence of chain complexes whose right-hand
complex is degreewise projective: each degree is a short exact sequence with projective right-hand
term, hence splits, and an additive functor preserves splittings. -/
lemma shortExact_map_of_degreewise_projective {ι : Type*} {c : ComplexShape ι}
    {SC : ShortComplex (HomologicalComplex C c)} (hSC : SC.ShortExact)
    (hproj : ∀ i, Projective (SC.X₃.X i)) :
    (SC.map (F.mapHomologicalComplex c)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hi : (SC.map (HomologicalComplex.eval C c i)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact SC).mp hSC i
  haveI : Projective ((SC.map (HomologicalComplex.eval C c i)).X₃) := hproj i
  have split : (SC.map (HomologicalComplex.eval C c i)).Splitting :=
    hi.splittingOfProjective
  exact (split.map F).shortExact

/-- **The six-term exact sequence of a left derived functor.** A short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` in `C` induces, for `n₀ + 1 = n₁`, a connecting map
`δ : Lₙ₁(X₃) → Lₙ₀(X₁)` making the six-term window of left derived functors exact. -/
theorem Functor.leftDerived_sixTerm_exact
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (F.leftDerived n₁).obj S.X₃ ⟶ (F.leftDerived n₀).obj S.X₁,
      (ComposableArrows.mk₅
        ((F.leftDerived n₁).map S.f) ((F.leftDerived n₁).map S.g)
        δ
        ((F.leftDerived n₀).map S.f) ((F.leftDerived n₀).map S.g)).Exact := by
  -- Chosen projective resolutions and the horseshoe.
  set P₁ : ProjectiveResolution S.X₁ := projectiveResolution S.X₁ with hP₁
  set P₃ : ProjectiveResolution S.X₃ := projectiveResolution S.X₃ with hP₃
  obtain ⟨P₂, α, β, w, hSE, aug₁, aug₂⟩ := horseshoe hS P₁ P₃
  -- The horseshoe short exact sequence of complexes and its image under `F`.
  set SC : ShortComplex (ChainComplex C ℕ) := ShortComplex.mk α β w with hSCdef
  have hT : (SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact :=
    shortExact_map_of_degreewise_projective F hSE (fun i => P₃.projective i)
  set T := SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ)) with hTdef
  -- The relevant complex-shape relation and the connecting map.
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]; omega
  set δ' := hT.δ n₁ n₀ hij with hδ'
  -- The connecting map on left derived functors, transported through `isoLeftDerivedObj`.
  refine ⟨(P₃.isoLeftDerivedObj F n₁).hom ≫ δ' ≫ (P₁.isoLeftDerivedObj F n₀).inv, ?_⟩
  -- The homology six-term window of `T`.
  set Hrow : ComposableArrows D 5 := ComposableArrows.mk₅
    (HomologicalComplex.homologyMap T.f n₁) (HomologicalComplex.homologyMap T.g n₁)
    δ'
    (HomologicalComplex.homologyMap T.f n₀) (HomologicalComplex.homologyMap T.g n₀) with hHrow
  -- `Hrow` is exact: this is the homology long exact sequence.
  have hHrowExact : Hrow.Exact := by
    rw [hHrow]
    refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_))
    · exact (hT.homology_exact₂ n₁).exact_toComposableArrows
    · exact (hT.homology_exact₃ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₁ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₂ n₀).exact_toComposableArrows
  -- An isomorphism between the left-derived window and the homology window.
  have e : ComposableArrows.mk₅
      ((F.leftDerived n₁).map S.f) ((F.leftDerived n₁).map S.g)
      ((P₃.isoLeftDerivedObj F n₁).hom ≫ δ' ≫ (P₁.isoLeftDerivedObj F n₀).inv)
      ((F.leftDerived n₀).map S.f) ((F.leftDerived n₀).map S.g) ≅ Hrow := by
    refine ComposableArrows.isoMk₅
      (P₁.isoLeftDerivedObj F n₁) (P₂.isoLeftDerivedObj F n₁) (P₃.isoLeftDerivedObj F n₁)
      (P₁.isoLeftDerivedObj F n₀) (P₂.isoLeftDerivedObj F n₀) (P₃.isoLeftDerivedObj F n₀)
      ?_ ?_ ?_ ?_ ?_
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ P₂ α aug₁ F n₁
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g P₂ P₃ β aug₂ F n₁
    · change ((P₃.isoLeftDerivedObj F n₁).hom ≫ δ' ≫ (P₁.isoLeftDerivedObj F n₀).inv) ≫
          (P₁.isoLeftDerivedObj F n₀).hom = (P₃.isoLeftDerivedObj F n₁).hom ≫ δ'
      simp
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ P₂ α aug₁ F n₀
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g P₂ P₃ β aug₂ F n₀
  exact (ComposableArrows.exact_iff_of_iso e).mpr hHrowExact

end Etingof
