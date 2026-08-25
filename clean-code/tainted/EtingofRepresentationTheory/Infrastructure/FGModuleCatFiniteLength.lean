import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import EtingofRepresentationTheory.Infrastructure.SimpleModuleFamily
import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives

/-!
# Objects of `FGModuleCat A` have finite length (the inductive `Etingof.HasFiniteLength`)

For a left-Noetherian ring `A` that is also Artinian (in particular a finite-dimensional
`k`-algebra), every object `X : FGModuleCat A` satisfies the categorical finite-length predicate
`Etingof.HasFiniteLength X` of `Chapter9/Introduction_9_6.lean`: `X` is built from simple objects
(and the zero object) by finitely many extensions.

This supplies the `finiteLength` field required by
`Etingof.IsFiniteAbelianCategoryOverField k (FGModuleCat A)` (issue #7424, sub-issue #7639).

## Strategy

The underlying `A`-module of `X` has finite length in the module sense
(`IsFiniteLength A X`, from `IsNoetherian A X ∧ IsArtinian A X`). We turn a module-level finite
length into the categorical predicate by induction on Mathlib's `IsFiniteLength` inductive:

* the `of_subsingleton` base case gives a zero object (`HasFiniteLength.of_isZero`);
* the `of_simple_quotient` step provides a submodule `N ≤ M` with simple quotient `M ⧸ N`;
  the categorical short exact sequence `0 → N → M → M ⧸ N → 0` in `FGModuleCat A`
  (`Etingof.submoduleSES`) feeds `HasFiniteLength.of_shortExact`, with the simple quotient handled
  by `Etingof.simple_fgModuleCat_of_isSimpleModule` (`SimpleModuleFamily.lean`) and the submodule
  by the induction hypothesis.

Short-exactness of the categorical sequence is checked through the fully faithful,
homology-preserving inclusion `forget₂ (FGModuleCat A) (ModuleCat A)`
(`ShortComplex.exact_map_iff_of_faithful`), which reflects exactness; monomorphy and epimorphy are
reflected because the inclusion is faithful and (over a Noetherian ring) preserves finite colimits.
-/

open CategoryTheory Limits

namespace Etingof

universe u

noncomputable section

variable {A : Type u} [Ring A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- A subsingleton finitely generated module is a zero object of `FGModuleCat A`. -/
lemma isZero_fgModuleCat_of_subsingleton (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Subsingleton M] : IsZero (FGModuleCat.of A M) := by
  rw [IsZero.iff_id_eq_zero]
  apply FGModuleCat.hom_ext
  ext x
  exact Subsingleton.elim _ _

/-- The categorical short exact sequence `0 → N → M → M ⧸ N → 0` in `FGModuleCat A` coming from a
submodule `N ≤ M`. -/
def submoduleSES {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) [Module.Finite A ↥N] : ShortComplex (FGModuleCat.{u} A) where
  X₁ := FGModuleCat.of A ↥N
  X₂ := FGModuleCat.of A M
  X₃ := FGModuleCat.of A (M ⧸ N)
  f := FGModuleCat.ofHom N.subtype
  g := FGModuleCat.ofHom N.mkQ
  zero := by
    apply FGModuleCat.hom_ext
    ext x
    change N.mkQ (N.subtype x) = 0
    simp

/-- The submodule short exact sequence is short exact in `FGModuleCat A`. -/
theorem submoduleSES_shortExact {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) [Module.Finite A ↥N] : (submoduleSES N).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · have hmap : ((submoduleSES N).map (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))).Exact := by
      apply ModuleCat.shortComplex_exact
      exact LinearMap.exact_subtype_mkQ N
    exact (ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))).mp hmap
  · apply (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).mono_of_mono_map
      (f := (submoduleSES N).f)
    rw [ModuleCat.mono_iff_injective]
    exact N.injective_subtype
  · apply FGModuleCat.epi_of_forget₂_epi (submoduleSES N).g
    rw [ModuleCat.epi_iff_surjective]
    exact N.mkQ_surjective

/-- **Objects of `FGModuleCat A` built from a finite-length module have finite length.** For a
finitely generated module `M` of finite length over a left-Noetherian ring, the object
`FGModuleCat.of A M` satisfies the categorical finite-length predicate. -/
theorem hasFiniteLength_fgModuleCat_of_isFiniteLength
    {M : Type u} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module.Finite A M], HasFiniteLength (FGModuleCat.of A M) := by
  induction hM with
  | of_subsingleton =>
      intro _
      exact HasFiniteLength.of_isZero (isZero_fgModuleCat_of_subsingleton _)
  | @of_simple_quotient M _ _ N _ _hN ih =>
      intro _
      haveI : Module.Finite A ↥N := inferInstance
      haveI : Module.Finite A (M ⧸ N) := inferInstance
      exact HasFiniteLength.of_shortExact (submoduleSES_shortExact N) ih
        (HasFiniteLength.of_simple (simple_fgModuleCat_of_isSimpleModule (M ⧸ N)))

/-- **Every object of `FGModuleCat A` has finite length**, for `A` a left-Noetherian *and* Artinian
ring (in particular a finite-dimensional `k`-algebra). This is the categorical finite-length
standing assumption of Etingof §9.6, supplying the `finiteLength` field of
`Etingof.IsFiniteAbelianCategoryOverField k (FGModuleCat A)`. -/
theorem hasFiniteLength_fgModuleCat [IsArtinianRing A] (X : FGModuleCat.{u} A) :
    HasFiniteLength X := by
  haveI : IsFiniteLength A X :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have h := hasFiniteLength_fgModuleCat_of_isFiniteLength (A := A) (M := X) this
  exact h

end

end Etingof
