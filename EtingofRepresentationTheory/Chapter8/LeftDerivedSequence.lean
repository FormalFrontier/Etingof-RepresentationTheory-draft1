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

This lemma is the reusable key ingredient for the `Tor` long exact sequence in the first argument
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

/-- **The six-term exact sequence for a short exact sequence of additive functors, in the varying
functor.** Given additive functors `F₁ F₂ F₃ : C ⥤ D` with natural transformations
`τ₁ : F₁ ⟶ F₂`, `τ₂ : F₂ ⟶ F₃` such that `τ₁ ≫ τ₂ = 0` and, on every projective object `Y`, the
short complex `0 → F₁(Y) → F₂(Y) → F₃(Y) → 0` is short exact, then for `n₀ + 1 = n₁` and any
object `X` there is a connecting map `δ : (F₃.leftDerived n₁).obj X → (F₁.leftDerived n₀).obj X`
making the six-term window of left derived functors exact.

This is the "functor-varies" dual of `Functor.leftDerived_sixTerm_exact` (where the short exact
sequence is in the object being resolved and the functor is fixed).  The proof resolves the fixed
object `X` once by `P := projectiveResolution X`, applies `τ₁, τ₂` degreewise to `P.complex`
(getting a short complex of chain complexes that is short exact because `P.complex` is degreewise
projective and `τ₁/τ₂` are short exact on projectives), takes the homology long exact sequence,
and transports it to the left derived functors via `ProjectiveResolution.leftDerived_app_eq`.

It is the reusable key ingredient for the `Tor` long exact sequence in the *second* argument
(`Etingof.Problem_8_2_6_iii_tor`). -/
theorem NatTrans.leftDerived_sixTerm_exact
    {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (w : τ₁ ≫ τ₂ = 0)
    (hSE : ∀ (Y : C) [Projective Y],
      (ShortComplex.mk (τ₁.app Y) (τ₂.app Y)
        (by rw [← NatTrans.comp_app, w]; rfl)).ShortExact)
    (X : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (F₃.leftDerived n₁).obj X ⟶ (F₁.leftDerived n₀).obj X,
      (ComposableArrows.mk₅
        ((NatTrans.leftDerived τ₁ n₁).app X) ((NatTrans.leftDerived τ₂ n₁).app X)
        δ
        ((NatTrans.leftDerived τ₁ n₀).app X) ((NatTrans.leftDerived τ₂ n₀).app X)).Exact := by
  -- Resolve `X` once; apply `τ₁, τ₂` degreewise to the resolution.
  set P : ProjectiveResolution X := projectiveResolution X with hP
  -- The two chain maps between the image complexes.
  have w' : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  set SC : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) w' with hSCdef
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by simp only [ComplexShape.down_Rel]; omega
  -- `SC` is short exact: degreewise it is `τ₁/τ₂` evaluated at a projective object.
  have hT : SC.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hSE (P.complex.X i)
  set δ' := hT.δ n₁ n₀ hij with hδ'
  refine ⟨(P.isoLeftDerivedObj F₃ n₁).hom ≫ δ' ≫ (P.isoLeftDerivedObj F₁ n₀).inv, ?_⟩
  -- The homology six-term window of `SC`.
  set Hrow : ComposableArrows D 5 := ComposableArrows.mk₅
    (HomologicalComplex.homologyMap SC.f n₁) (HomologicalComplex.homologyMap SC.g n₁)
    δ'
    (HomologicalComplex.homologyMap SC.f n₀) (HomologicalComplex.homologyMap SC.g n₀) with hHrow
  have hHrowExact : Hrow.Exact := by
    rw [hHrow]
    refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_))
    · exact (hT.homology_exact₂ n₁).exact_toComposableArrows
    · exact (hT.homology_exact₃ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₁ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₂ n₀).exact_toComposableArrows
  -- Transport the homology window to the left derived window, one column per functor.
  have e : ComposableArrows.mk₅
      ((NatTrans.leftDerived τ₁ n₁).app X) ((NatTrans.leftDerived τ₂ n₁).app X)
      ((P.isoLeftDerivedObj F₃ n₁).hom ≫ δ' ≫ (P.isoLeftDerivedObj F₁ n₀).inv)
      ((NatTrans.leftDerived τ₁ n₀).app X) ((NatTrans.leftDerived τ₂ n₀).app X) ≅ Hrow := by
    refine ComposableArrows.isoMk₅
      (P.isoLeftDerivedObj F₁ n₁) (P.isoLeftDerivedObj F₂ n₁) (P.isoLeftDerivedObj F₃ n₁)
      (P.isoLeftDerivedObj F₁ n₀) (P.isoLeftDerivedObj F₂ n₀) (P.isoLeftDerivedObj F₃ n₀)
      ?_ ?_ ?_ ?_ ?_
    · change (NatTrans.leftDerived τ₁ n₁).app X ≫ (P.isoLeftDerivedObj F₂ n₁).hom =
        (P.isoLeftDerivedObj F₁ n₁).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex) n₁
      rw [ProjectiveResolution.leftDerived_app_eq τ₁ P n₁]; simp
    · change (NatTrans.leftDerived τ₂ n₁).app X ≫ (P.isoLeftDerivedObj F₃ n₁).hom =
        (P.isoLeftDerivedObj F₂ n₁).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) n₁
      rw [ProjectiveResolution.leftDerived_app_eq τ₂ P n₁]; simp
    · change ((P.isoLeftDerivedObj F₃ n₁).hom ≫ δ' ≫ (P.isoLeftDerivedObj F₁ n₀).inv) ≫
          (P.isoLeftDerivedObj F₁ n₀).hom = (P.isoLeftDerivedObj F₃ n₁).hom ≫ δ'
      simp
    · change (NatTrans.leftDerived τ₁ n₀).app X ≫ (P.isoLeftDerivedObj F₂ n₀).hom =
        (P.isoLeftDerivedObj F₁ n₀).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex) n₀
      rw [ProjectiveResolution.leftDerived_app_eq τ₁ P n₀]; simp
    · change (NatTrans.leftDerived τ₂ n₀).app X ≫ (P.isoLeftDerivedObj F₃ n₀).hom =
        (P.isoLeftDerivedObj F₂ n₀).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) n₀
      rw [ProjectiveResolution.leftDerived_app_eq τ₂ P n₀]; simp
  exact (ComposableArrows.exact_iff_of_iso e).mpr hHrowExact

end Etingof
