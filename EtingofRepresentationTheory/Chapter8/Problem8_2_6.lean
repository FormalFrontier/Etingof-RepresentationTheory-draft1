import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_RightExact
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_LeftExact
import EtingofRepresentationTheory.Chapter8.Problem8_2_6_Core
import EtingofRepresentationTheory.Chapter8.TensorProjectiveExact
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
* The `Ext` long exact sequences of (iii) and (v) are `Abelian.Ext.covariantSequence` and
  `Abelian.Ext.contravariantSequence` from Mathlib, whose objects are exactly the
  `Etingof.Ext` groups.
* The `Tor` long exact sequences of (iii) and (v) are stated as six-term homology windows
  (`ComposableArrows _ 5`) with an existentially quantified connecting homomorphism `δ`,
  mirroring the shape of the `Ext` sequences. The horizontal maps are the first-argument
  functoriality of `Etingof.TorFunctor` (for (v)) and the second-argument functoriality
  `torSndMap` built below (for (iii)).
* The balancing theorem (iv) is stated as a canonical isomorphism between `Etingof.Tor` (left
  derived of `- ⊗_A N` in `M`) and the left derived functor of `M ⊗_A -` in `N`
  (`tensorLeftFunctor A M`).

To phrase (iii) and (iv) we build genuine second-argument infrastructure: `tensorSndMap`,
`tensorRightNatTrans`, `torSndMap`, and `tensorLeftFunctor` (all real constructions, no sorried
`def` bodies). Definition 8.2.3 originally left-derives `- ⊗_A N` only in its first argument
`M`; a left `A`-module map `g : N → N'` induces a natural transformation of the tensor functors,
and `NatTrans.leftDerived` supplies the missing second-argument functoriality of `Tor`.

These are statement-level formalizations (spec-first): the proofs are deferred (`sorry`).
-/

namespace Etingof

open CategoryTheory TensorProduct

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
  -- Step 1 (this reduction, sorry-free): the relative bar resolution `Etingof.barResolution`
  -- computes `Ext¹` as the degree-1 cohomology of the Hom-into-`V` cochain complex, via
  -- `ProjectiveResolution.extAddEquivCohomologyClass`.
  -- Step 1: the relative bar resolution `Etingof.barResolution` computes `Ext¹` as the degree-1
  -- cohomology of the Hom-into-`V` cochain complex (`extAddEquivCohomologyClass`).
  -- Step 2 (crux): identify that cohomology group with `Problem3_9_1.Ext1` via
  -- `Etingof.cohomologyClassEquivExt1`.
  ⟨((Etingof.barResolution k A W).extAddEquivCohomologyClass
      (Y := ModuleCat.of A V) (n := 1)).trans
    (Etingof.cohomologyClassEquivExt1 k A W V)⟩

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
  -- The composite `S.g.hom ∘ S.f.hom` vanishes since `S.f ≫ S.g = 0`.
  have hcomp : ∀ (n : S.X₁), S.g.hom (S.f.hom n) = 0 := by
    intro n
    have h0 : (S.f ≫ S.g).hom n = 0 := by rw [S.zero]; rfl
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
  -- The induced natural transformations `- ⊗_A Nᵢ` compose to zero.
  have w : tensorRightNatTrans A S.f.hom ≫ tensorRightNatTrans A S.g.hom = 0 := by
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
  -- Apply the varying-functor six-term exact sequence; on projective `Y` the tensor sequence
  -- `Y ⊗_A N₁ → Y ⊗_A N₂ → Y ⊗_A N₃` is short exact by flatness of projectives (#6587).
  exact NatTrans.leftDerived_sixTerm_exact
    (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom) w
    (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS) M n₀ n₁ h

/-! ### Part (iv): the balancing theorem -/

/-- **Balancing in degree 0** (the base case of the dimension-shift proof of Problem 8.2.6(iv)).
Both `Tor₀ᴬ(M, N)` and the zeroth left derived functor of `M ⊗_A -` evaluated at `N` are
canonically the group `M ⊗_A N`: `Etingof.Tor A N M 0 = (leftDerived (tensorRightFunctor A N) 0).obj M`
and `(leftDerived (tensorLeftFunctor A M) 0).obj N` both reduce, via `leftDerivedZeroIsoSelf`, to the
common object `AddCommGrpCat.of (tensorOver A N M) = M ⊗_A N`. Composing the two zeroth-derived
identifications gives the balancing isomorphism in degree `0`. -/
noncomputable def balancingIsoZero
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Etingof.Tor A N M 0 ≅
      (Functor.leftDerived (tensorLeftFunctor A M) 0).obj (ModuleCat.of A N) :=
  ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app M) ≪≫
    ((tensorLeftFunctor A M).leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).symm

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
  sorry

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
