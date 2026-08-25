import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_RightExact
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_LeftExact
import EtingofRepresentationTheory.Chapter8.Problem8_2_6_Core
import EtingofRepresentationTheory.Chapter8.TensorProjectiveExact
import EtingofRepresentationTheory.Chapter8.TensorRightProjectiveExact
import EtingofRepresentationTheory.Chapter8.LeftDerivedSequence
import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import EtingofRepresentationTheory.Chapter8.BarResolution
import EtingofRepresentationTheory.Chapter8.Problem8_2_6_ii_Crux
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Problem 8.2.6: basic properties of `Tor` and `Ext`

* (i) `Tor₀(M, N) = M ⊗_A N` and `Ext⁰(M, N) = Hom_A(M, N)`.
* (ii) `Ext¹(M, N)` is canonically isomorphic to the group `Ext¹` defined in Problem 3.9.1.
* (iii) A short exact sequence `0 → N₁ → N₂ → N₃ → 0` of left `A`-modules induces long exact
  sequences of `Ext`-groups and of `Tor`-groups (in the second argument).
* (iv) `Torᵢᴬ(M, N)` may be computed from a projective resolution of `N`, tensored with `M`
  (the balancing theorem).
* (v) A short exact sequence `0 → M₁ → M₂ → M₃ → 0` induces long exact sequences of `Ext`- and
  `Tor`-groups (in the first argument).

## What is formalized here

All parts (i)–(v) are stated below, for both the `Ext` and `Tor` sides.

* (i) uses `Etingof.Tor` / `Etingof.tensorOver` (Definition 8.2.3) for the `Tor₀` half and
  `Etingof.Ext` (Definition 8.2.4) with `Abelian.Ext.addEquiv₀` for the `Ext⁰` half.
* (ii) relates `Etingof.Ext` in degree `1` to `Etingof.Problem3_9_1.Ext1`, the cocycle/coboundary
  description of extensions.
* The local `Ext` and `Tor` windows of (iii) and (v) are proved here.  The companion file
  `Problem8_2_6_LongExact.lean` packages them into globally indexed connecting families,
  proves every adjacent window exact, and supplies the zero-ended `Ext⁰` mono and `Tor₀` epi
  endpoints through the canonical `Ext⁰ ≃ Hom` and `Tor₀ ≅ tensor` comparisons.
* The horizontal `Tor` maps are the first-argument functoriality of `Etingof.TorFunctor`
  (for (v)) and the second-argument functoriality `torSndMap` built below (for (iii)).
* The balancing theorem (iv) is stated as a canonical isomorphism between `Etingof.Tor` (left
  derived of `- ⊗_A N` in `M`) and the left derived functor of `M ⊗_A -` in `N`
  (`tensorLeftFunctor A M`).

To phrase (iii) and (iv) we build second-argument infrastructure: `tensorSndMap`,
`tensorRightNatTrans`, `torSndMap`, and `tensorLeftFunctor`. Definition 8.2.3 originally left-derives `- ⊗_A N` only in its first argument
`M`; a left `A`-module map `g : N → N'` induces a natural transformation of the tensor functors,
and `NatTrans.leftDerived` supplies the missing second-argument functoriality of `Tor`.

The balancing theorem (iv) is proved by an elementary dimension shift
(strong induction on the homological degree via projective presentations of the right module),
using the two six-term windows (`Problem_8_2_6_v_tor` / `torBalancing_sixTerm`), the vanishing of
higher `Tor` on projectives, and the naturality of the degree-`0` balancing isomorphism
(`balancing_zero_naturality`).
-/

namespace Etingof

open CategoryTheory TensorProduct CochainComplex.HomComplex

universe u

/-! ### Part (i) -/

/-- **Problem 8.2.6(i), `Tor₀`.** `Tor₀ᴬ(M, N)` is canonically isomorphic to `M ⊗_A N`. In the
derived-functor formulation of Definition 8.2.3 this is the statement that the zeroth left
derived functor of `- ⊗_A N` recovers `- ⊗_A N` itself. -/
theorem Problem_8_2_6_i_tor
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Nonempty (Etingof.Tor A N M 0 ≅ AddCommGrpCat.of (Etingof.tensorOver A N M)) :=
  ⟨((tensorRightFunctor A N).leftDerivedZeroIsoSelf).app M⟩

/-- **Problem 8.2.6(i), `Ext⁰`.** `Ext⁰_A(M, N)` is canonically isomorphic (as an abelian group)
to `Hom_A(M, N)`. -/
theorem Problem_8_2_6_i_ext
    (A : Type u) [Ring A] (M N : ModuleCat.{u} A) :
    Nonempty (Etingof.Ext M N 0 ≃+ (M ⟶ N)) :=
  ⟨CategoryTheory.Abelian.Ext.addEquiv₀⟩

/-! ### Part (ii) -/

/-- The canonical additive equivalence from categorical `Ext¹_A(W, V)` to the explicit
cocycle-modulo-coboundary model of Problem 3.9.1. -/
noncomputable def extOneAddEquivProblem3Ext1
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    Etingof.Ext (ModuleCat.of A W) (ModuleCat.of A V) 1
      ≃+ Etingof.Problem3_9_1.Ext1 k A V W :=
  ((Etingof.barResolution k A W).extAddEquivCohomologyClass
      (Y := ModuleCat.of A V) (n := 1)).trans
    (Etingof.cohomologyClassEquivExt1 k A W V)

/-- The canonical comparison factors through degree-one cohomology of the bar resolution. -/
@[simp]
theorem extOneAddEquivProblem3Ext1_apply
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (x : Etingof.Ext (ModuleCat.of A W) (ModuleCat.of A V) 1) :
    extOneAddEquivProblem3Ext1 k A V W x =
      cohomologyClassEquivExt1 k A W V
        ((barResolution k A W).extAddEquivCohomologyClass x) :=
  rfl

/-- The bar cocycle represented by a degree-one chain map used in `ProjectiveResolution.extMk`. -/
noncomputable def barExtCocycle
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (f : (barResolution k A W).complex.X 1 ⟶ ModuleCat.of A V)
    (hf : (barResolution k A W).complex.d 2 1 ≫ f = 0) :
    Cocycle (barCochainComplex k A W) (singleV A V) 1 :=
  Cocycle.toSingleMk
    (((barResolution k A W).cochainComplexXIso (-(1 : ℕ)) 1 rfl).hom ≫ f) (by simp)
    (-(2 : ℕ)) (by lia)
    (by
      rw [ProjectiveResolution.cochainComplex_d (barResolution k A W)
        (-(2 : ℕ)) (-(1 : ℕ)) 2 1 (by norm_num) (by norm_num)]
      simp [Category.assoc, hf])

/-- On the standard `extMk` generators, the canonical comparison is the quotient class of the
corresponding bar cocycle.  Together with `barCocycleEquivProblem3Cocycle_apply`, this computes
the representative by the tensor–hom formula `z (1 ⊗ (a ⊗ w))`. -/
@[simp]
theorem extOneAddEquivProblem3Ext1_extMk
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (f : (barResolution k A W).complex.X 1 ⟶ ModuleCat.of A V)
    (hf : (barResolution k A W).complex.d 2 1 ≫ f = 0) :
    extOneAddEquivProblem3Ext1 k A V W
        ((barResolution k A W).extMk f 2 rfl hf) =
      cohomologyClassEquivExt1 k A W V
        (CohomologyClass.mk (barExtCocycle k A V W f hf)) := by
  unfold extOneAddEquivProblem3Ext1
  rw [AddEquiv.trans_apply,
    ProjectiveResolution.extAddEquivCohomologyClass_apply,
    ProjectiveResolution.extEquivCohomologyClass_extMk]
  rfl

/-- **Problem 8.2.6(ii).** For representations `V`, `W` of a `k`-algebra `A`, the group
`Ext¹_A(W, V)` of Definition 8.2.4 is canonically isomorphic to the group `Ext¹(W, V)` of
Problem 3.9.1, defined as 1-cocycles modulo coboundaries. (Both classify extensions
`0 → V → U → W → 0`.) -/
theorem Problem_8_2_6_ii
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    Nonempty (Etingof.Ext (ModuleCat.of A W) (ModuleCat.of A V) 1
      ≃+ Etingof.Problem3_9_1.Ext1 k A V W) :=
  ⟨extOneAddEquivProblem3Ext1 k A V W⟩

/-! ### Part (iii): long exact sequence in the second argument (`Ext` half) -/

/-- **Problem 8.2.6(iii), `Ext`.** A short exact sequence `S : 0 → N₁ → N₂ → N₃ → 0` of left
`A`-modules induces, for each object `M` and each `n₀ + 1 = n₁`, the covariant long exact
sequence
`Ext M N₁ n₀ → Ext M N₂ n₀ → Ext M N₃ n₀ → Ext M N₁ n₁ → Ext M N₂ n₁ → Ext M N₃ n₁`.
Its objects are the `Etingof.Ext` groups of Definition 8.2.4. -/
theorem Problem_8_2_6_iii_ext
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (Abelian.Ext.covariantSequence (X := M) hS n₀ n₁ h).Exact :=
  Abelian.Ext.covariantSequence_exact M hS n₀ n₁ h

set_option backward.isDefEq.respectTransparency false in
/-- The tensor natural transformations induced by the two arrows of a short complex compose to
zero.  Exposing this relation lets the explicit varying-functor connecting map be reused without
reconstructing its witness. -/
lemma tensorRightNatTrans_comp_zero
    (A : Type u) [Ring A] {S : ShortComplex (ModuleCat.{u} A)} :
    tensorRightNatTrans A S.f.hom ≫ tensorRightNatTrans A S.g.hom = 0 := by
  have hcomp : ∀ (n : S.X₁), S.g.hom (S.f.hom n) = 0 := by
    intro n
    have h0 : (S.f ≫ S.g).hom n = 0 := by rw [S.zero]; rfl
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
  ext Y x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  induction y with
  | zero => simp
  | tmul m n =>
    change tensorSndMap A S.g.hom Y (tensorSndMap A S.f.hom Y
      (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n))) = 0
    rw [tensorSndMap_mk, tensorSndMap_mk, hcomp n, tmul_zero]
    rfl
  | add a b ha hb =>
    rw [show ((a + b : TensorProduct ℤ Y ↑S.X₁) : Etingof.tensorOver A ↑S.X₁ Y)
          = (a : Etingof.tensorOver A ↑S.X₁ Y) + b from
        map_add (QuotientAddGroup.mk' (Etingof.balancedSubgroup A ↑S.X₁ Y)) a b,
      map_add, map_add, ha, hb]

/-- **Problem 8.2.6(iii), `Tor`.** A short exact sequence `S : 0 → N₁ → N₂ → N₃ → 0` of left
`A`-modules induces, for each right `A`-module `M` and each `n₀ + 1 = n₁`, a connecting
homomorphism `δ : Torₙ₁(M, N₃) → Torₙ₀(M, N₁)` making the six-term homology window
`Torₙ₁(M,N₁) → Torₙ₁(M,N₂) → Torₙ₁(M,N₃) →[δ] Torₙ₀(M,N₁) → Torₙ₀(M,N₂) → Torₙ₀(M,N₃)`
exact. The horizontal maps are the second-argument functoriality `torSndMap` of `Etingof.Tor`;
splicing these windows over all `n` gives the book's long exact `Tor` sequence in the second
argument (ending in `M ⊗_A N₁ → M ⊗_A N₂ → M ⊗_A N₃ → 0`). Existence of `δ` is part of the
claim. -/
theorem Problem_8_2_6_iii_tor
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : Etingof.Tor A S.X₃ M n₁ ⟶ Etingof.Tor A S.X₁ M n₀,
      (ComposableArrows.mk₅
        (torSndMap A S.f.hom n₁ M) (torSndMap A S.g.hom n₁ M)
        δ
        (torSndMap A S.f.hom n₀ M) (torSndMap A S.g.hom n₀ M)).Exact := by
  -- Apply the varying-functor six-term exact sequence; on projective `Y` the tensor sequence
  -- `Y ⊗_A N₁ → Y ⊗_A N₂ → Y ⊗_A N₃` is short exact by flatness of projectives.
  exact NatTrans.leftDerived_sixTerm_exact
    (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom)
    (tensorRightNatTrans_comp_zero A)
    (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS) M n₀ n₁ h

/-! ### Part (iv): the balancing theorem -/

/-- **Balancing in degree 0** (the base case of the dimension-shift proof of Problem 8.2.6(iv)).
Both `Tor₀ᴬ(M, N)` and the zeroth left derived functor of `M ⊗_A -` evaluated at `N` are
canonically the group `M ⊗_A N`: both `Etingof.Tor A N M 0` (i.e.
`(leftDerived (tensorRightFunctor A N) 0).obj M`) and
`(leftDerived (tensorLeftFunctor A M) 0).obj N`
reduce, via `leftDerivedZeroIsoSelf`, to the common object
`AddCommGrpCat.of (tensorOver A N M) = M ⊗_A N`. Composing the two zeroth-derived identifications
gives the balancing isomorphism in degree `0`. -/
noncomputable def balancingIsoZero
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Etingof.Tor A N M 0 ≅
      (Functor.leftDerived (tensorLeftFunctor A M) 0).obj (ModuleCat.of A N) :=
  ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app M) ≪≫
    ((tensorLeftFunctor A M).leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Balancing-side six-term window.** The mirror of `Problem_8_2_6_iii_tor` for the
balancing-side derived functor: a short exact sequence `S : 0 → M₁ → M₂ → M₃ → 0` of *right*
`A`-modules induces, for a fixed left module `N` and each `n₀ + 1 = n₁`, a connecting homomorphism
making the six-term homology window of the left derived functors of `M ↦ M ⊗_A N`
(`tensorLeftFunctor A M`, varying in `M`) exact. This is the second six-term long exact sequence the
elementary dimension-shift proof of the balancing theorem (Problem 8.2.6(iv)) needs, alongside the
`Etingof.Tor`-side window `Problem_8_2_6_iii_tor`. -/
theorem torBalancing_sixTerm
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (Functor.leftDerived (tensorLeftFunctor A S.X₃) n₁).obj (ModuleCat.of A N) ⟶
          (Functor.leftDerived (tensorLeftFunctor A S.X₁) n₀).obj (ModuleCat.of A N),
      (ComposableArrows.mk₅
        ((NatTrans.leftDerived (tensorLeftNatTrans A S.f) n₁).app (ModuleCat.of A N))
        ((NatTrans.leftDerived (tensorLeftNatTrans A S.g) n₁).app (ModuleCat.of A N))
        δ
        ((NatTrans.leftDerived (tensorLeftNatTrans A S.f) n₀).app (ModuleCat.of A N))
        ((NatTrans.leftDerived (tensorLeftNatTrans A S.g) n₀).app (ModuleCat.of A N))).Exact := by
  -- The composite `S.g.hom ∘ S.f.hom` vanishes since `S.f ≫ S.g = 0`.
  have hcomp : ∀ (m : S.X₁), S.g.hom (S.f.hom m) = 0 := by
    intro m
    have h0 : (S.f ≫ S.g).hom m = 0 := by rw [S.zero]; rfl
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
  -- The induced natural transformations `- ⊗_A N` compose to zero (via the `tensorBifunctor`
  -- functoriality: `S.f ≫ S.g = 0`).
  have w : tensorLeftNatTrans A S.f ≫ tensorLeftNatTrans A S.g = 0 := by
    ext N' x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
      change (QuotientAddGroup.mk (S.g.hom (S.f.hom m) ⊗ₜ[ℤ] n)
          : Etingof.tensorOver A N' S.X₃) = 0
      rw [hcomp m, zero_tmul]
      rfl
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ S.X₁ N') : Etingof.tensorOver A N' S.X₁)
            = (a : Etingof.tensorOver A N' S.X₁) + b from
          map_add (QuotientAddGroup.mk' (Etingof.balancedSubgroup A N' S.X₁)) a b,
        map_add, map_add, ha, hb]
  -- Apply the varying-functor six-term exact sequence; on a projective left module `Y` the tensor
  -- sequence `M₁ ⊗_A Y → M₂ ⊗_A Y → M₃ ⊗_A Y` is short exact by flatness of projectives.
  exact NatTrans.leftDerived_sixTerm_exact
    (tensorLeftNatTrans A S.f) (tensorLeftNatTrans A S.g) w
    (fun Y _ => tensorRightFunctor_map_shortExact A Y hS) (ModuleCat.of A N) n₀ n₁ h

/-! ### Infrastructure for the dimension-shift proof of the balancing theorem (iv) -/

section BalancingIV

open CategoryTheory.Limits

universe v₁ u₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `fromLeftDerivedZero` in the functor variable.** For a natural transformation
`α : F ⟶ G` of additive functors between abelian categories (`C` with enough projectives), the
degree-`0` comparison maps `L₀F ⟶ F` and `L₀G ⟶ G` intertwine `NatTrans.leftDerived α 0` with `α`.
This is the key input to the naturality of the degree-`0` balancing isomorphism
(`balancing_zero_naturality`), which the `n = 1` base of the dimension-shift proof needs. -/
lemma fromLeftDerivedZero_natTrans_app
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
    {D : Type*} [Category D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X
      = F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P : ProjectiveResolution X := projectiveResolution X
  rw [ProjectiveResolution.leftDerived_app_eq α P 0,
    ProjectiveResolution.fromLeftDerivedZero_eq P G,
    ProjectiveResolution.fromLeftDerivedZero_eq P F]
  simp only [HomologicalComplex.homologyFunctor_map, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.cancel_iso_hom_left, ← Iso.inv_comp_eq,
    ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id_assoc]
  refine (cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) 0)).1 ?_
  rw [← Category.assoc, HomologicalComplex.p_opcyclesMap, Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  simp only [NatTrans.mapHomologicalComplex_app_f]
  exact (α.naturality (P.π.f 0)).symm

set_option backward.isDefEq.respectTransparency false in
/-- In a six-term exact window with the two neighbours `obj 1` and `obj 4` of the central map
`obj 2 ⟶ obj 3` both zero, that central map is an isomorphism, giving `obj 2 ≅ obj 3`. Used to
collapse each six-term window `Tₙ(K) → Tₙ(P) → Tₙ(M) → Tₙ₋₁(K) → Tₙ₋₁(P) → Tₙ₋₁(M)` to
`Tₙ(M) ≅ Tₙ₋₁(K)` when the projective terms vanish (degrees `≥ 2`). -/
noncomputable def iso_of_sixTerm_exact
    {D : Type*} [Category D] [Abelian D] {W : ComposableArrows D 5}
    (hW : W.Exact) (h1 : IsZero (W.obj 1)) (h4 : IsZero (W.obj 4)) :
    W.obj 2 ≅ W.obj 3 := by
  let g : W.obj 2 ⟶ W.obj 3 := W.map' 2 3
  haveI : Mono g := (hW.exact' 1 2 3).mono_g (h1.eq_of_src _ _)
  haveI : Epi g := (hW.exact' 2 3 4).epi_f (h4.eq_of_tgt _ _)
  haveI : IsIso g := isIso_of_mono_of_epi _
  exact asIso g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the degree-0 balancing isomorphism** in the right module. For a map
`f : M ⟶ M'` of right `A`-modules, the square relating `balancingIsoZero A N M` and
`balancingIsoZero A N M'` commutes: the `Tor`-side functoriality `(TorFunctor A N 0).map f` and
the balancing-side functoriality `NatTrans.leftDerived (tensorLeftNatTrans A f) 0` agree under
`balancingIsoZero`. This lets the `n = 1` base of the dimension shift identify the two kernels. -/
lemma balancing_zero_naturality
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (TorFunctor A N 0).map f ≫ (balancingIsoZero A N M').hom
      = (balancingIsoZero A N M).hom
        ≫ (NatTrans.leftDerived (tensorLeftNatTrans A f) 0).app (ModuleCat.of A N) := by
  have hmap : (tensorLeftNatTrans A f).app (ModuleCat.of A N)
      = (tensorRightFunctor A N).map f := rfl
  have hnat := fromLeftDerivedZero_natTrans_app (tensorLeftNatTrans A f) (ModuleCat.of A N)
  rw [hmap] at hnat
  have hα : (TorFunctor A N 0).map f
        ≫ ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app M').hom
      = ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app M).hom
        ≫ (tensorRightFunctor A N).map f :=
    (tensorRightFunctor A N).leftDerivedZeroIsoSelf.hom.naturality f
  have hβ : (tensorRightFunctor A N).map f
        ≫ ((tensorLeftFunctor A M').leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).inv
      = ((tensorLeftFunctor A M).leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).inv
        ≫ (NatTrans.leftDerived (tensorLeftNatTrans A f) 0).app (ModuleCat.of A N) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hnat.symm
  simp only [balancingIsoZero, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hα, Category.assoc, hβ]

end BalancingIV

/-- **Problem 8.2.6(iv), balancing.** `Torₙᴬ(M, N)` may be computed from a projective resolution
of `N` tensored with `M`: the `n`-th left derived functor of `- ⊗_A N` evaluated at `M`
(the definition `Etingof.Tor`) is canonically isomorphic to the `n`-th left derived functor of
`M ⊗_A -` (the functor `tensorLeftFunctor A M`) evaluated at `N`. Equivalently, `Tor` is
symmetric: it can be computed by resolving either argument. -/
theorem Problem_8_2_6_iv
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    Nonempty (Etingof.Tor A N M n ≅
      (Functor.leftDerived (tensorLeftFunctor A M) n).obj (ModuleCat.of A N)) := by
  induction n generalizing M with
  | zero => exact ⟨balancingIsoZero A N M⟩
  | succ k IH =>
    obtain ⟨pp⟩ := CategoryTheory.EnoughProjectives.presentation M
    set SC : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
      ShortComplex.mk (Limits.kernel.ι pp.f) pp.f (by simp) with hSC
    have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
    haveI : CategoryTheory.Projective SC.X₂ := pp.projective
    obtain ⟨δT, hT⟩ :=
      Etingof.Functor.leftDerived_sixTerm_exact (tensorRightFunctor A N) hSE k (k + 1) rfl
    obtain ⟨δB, hB⟩ := torBalancing_sixTerm A N hSE k (k + 1) rfl
    obtain _ | j := k
    · -- `n = 1`: the dimension shift bottoms out at a kernel comparison
      set a := (TorFunctor A N 0).map SC.f with ha
      set b := (NatTrans.leftDerived (tensorLeftNatTrans A SC.f) 0).app (ModuleCat.of A N) with hb
      have hcompT : δT ≫ a = 0 := hT.toIsComplex.zero' 2 3 4
      have hcompB : δB ≫ b = 0 := hB.toIsComplex.zero' 2 3 4
      haveI hmonoT : Mono δT := (hT.exact' 1 2 3).mono_g
        ((Functor.isZero_leftDerived_obj_projective_succ
          (tensorRightFunctor A N) 0 SC.X₂).eq_of_src _ _)
      haveI hmonoB : Mono δB := (hB.exact' 1 2 3).mono_g
        ((Etingof.isZero_tensorLeftFunctor_leftDerived_succ A SC.X₂ N 0).eq_of_src _ _)
      let ST : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk δT a hcompT
      let SB : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk δB b hcompB
      have hExT : ST.Exact := hT.exact' 2 3 4
      have hExB : SB.Exact := hB.exact' 2 3 4
      haveI : Mono ST.f := hmonoT
      haveI : Mono SB.f := hmonoB
      have isoTor := Limits.IsLimit.conePointUniqueUpToIso hExT.fIsKernel (Limits.kernelIsKernel a)
      have isoB := Limits.IsLimit.conePointUniqueUpToIso hExB.fIsKernel (Limits.kernelIsKernel b)
      have hsq : a ≫ (balancingIsoZero A N SC.X₂).hom
          = (balancingIsoZero A N SC.X₁).hom ≫ b := balancing_zero_naturality A N SC.f
      exact ⟨isoTor.trans ((Limits.kernel.mapIso a b (balancingIsoZero A N SC.X₁)
        (balancingIsoZero A N SC.X₂) hsq).trans isoB.symm)⟩
    · -- `n ≥ 2`: both windows collapse to `Tₙ(M) ≅ Tₙ₋₁(K)`; compose with the induction hypothesis
      exact ⟨(iso_of_sixTerm_exact hT
          (Functor.isZero_leftDerived_obj_projective_succ (tensorRightFunctor A N) (j + 1) SC.X₂)
          (Functor.isZero_leftDerived_obj_projective_succ (tensorRightFunctor A N) j SC.X₂)).trans
        (((IH SC.X₁).some).trans
          (iso_of_sixTerm_exact hB
            (Etingof.isZero_tensorLeftFunctor_leftDerived_succ A SC.X₂ N (j + 1))
            (Etingof.isZero_tensorLeftFunctor_leftDerived_succ A SC.X₂ N j)).symm)⟩

/-! ### Part (v): long exact sequence in the first argument (`Ext` half) -/

/-- **Problem 8.2.6(v), `Ext`.** A short exact sequence `S : 0 → M₁ → M₂ → M₃ → 0` of left
`A`-modules induces, for each object `N` and each `1 + n₀ = n₁`, the contravariant long exact
sequence
`Ext M₃ N n₀ → Ext M₂ N n₀ → Ext M₁ N n₀ → Ext M₃ N n₁ → Ext M₂ N n₁ → Ext M₁ N n₁`.
Its objects are the `Etingof.Ext` groups of Definition 8.2.4. -/
theorem Problem_8_2_6_v_ext
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Abelian.Ext.contravariantSequence hS N n₀ n₁ h).Exact :=
  Abelian.Ext.contravariantSequence_exact hS N n₀ n₁ h

/-- **Problem 8.2.6(v), `Tor`.** A short exact sequence `S : 0 → M₁ → M₂ → M₃ → 0` of right
`A`-modules (objects of `ModuleCat Aᵐᵒᵖ`) induces, for each left `A`-module `N` and each
`n₀ + 1 = n₁`, a connecting homomorphism `δ : Torₙ₁(M₃, N) → Torₙ₀(M₁, N)` making the six-term
homology window
`Torₙ₁(M₁,N) → Torₙ₁(M₂,N) → Torₙ₁(M₃,N) →[δ] Torₙ₀(M₁,N) → Torₙ₀(M₂,N) → Torₙ₀(M₃,N)`
exact. The horizontal maps are the first-argument functoriality of `Etingof.TorFunctor`
(the `n`-th left derived functor of `- ⊗_A N`); splicing these windows over all `n` gives the
book's long exact `Tor` sequence in the first argument. Existence of `δ` is part of the claim. -/
theorem Problem_8_2_6_v_tor
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (Etingof.TorFunctor A N n₁).obj S.X₃ ⟶ (Etingof.TorFunctor A N n₀).obj S.X₁,
      (ComposableArrows.mk₅
        ((Etingof.TorFunctor A N n₁).map S.f) ((Etingof.TorFunctor A N n₁).map S.g)
        δ
        ((Etingof.TorFunctor A N n₀).map S.f) ((Etingof.TorFunctor A N n₀).map S.g)).Exact := by
  exact Etingof.Functor.leftDerived_sixTerm_exact (Etingof.tensorRightFunctor A N) hS n₀ n₁ h

end Etingof
