import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Definition 7.8.2: Short Exact Sequence

A **short exact sequence** is an exact sequence of the form:
0 → X → Y → Z → 0

This holds iff X → Y is injective, Y → Z is surjective, and the induced map
Y/X → Z is an isomorphism. Short exact sequences correspond to extensions of Z by X.

## Mathlib correspondence

Exact match: `CategoryTheory.ShortComplex` bundled with the defining predicate
`CategoryTheory.ShortComplex.ShortExact`. The latter records that `S.f` is a
mono (injectivity of `X → Y`), `S.g` is an epi (surjectivity of `Y → Z`), and
`S` is exact at `Y` (equivalently the induced `Y/X → Z` is an isomorphism).
-/

/-- A short exact sequence `0 → X → Y → Z → 0` in an abelian category, in the
sense of Etingof Definition 7.8.2. It is a `CategoryTheory.ShortComplex`
together with a proof that it is `ShortComplex.ShortExact`: `X → Y` injective,
`Y → Z` surjective, and exact at `Y`. Bundling the `ShortExact` predicate is
what distinguishes a short *exact* sequence from a bare short complex (which the
zero complex would also satisfy). -/
def Etingof.ShortExactSequence (C : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] :=
  {S : CategoryTheory.ShortComplex C // S.ShortExact}

/-- An extension of `Z` by `X` is a short exact sequence equipped with
identifications of its left and right endpoints with `X` and `Z`.  We use
isomorphisms, rather than literal equalities, so that the definition respects
the usual categorical notion of sameness. -/
structure Etingof.Extension (C : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (Z X : C) where
  sequence : Etingof.ShortExactSequence C
  leftIso : sequence.1.X₁ ≅ X
  rightIso : sequence.1.X₃ ≅ Z

/-- Every short exact sequence is canonically an extension of its right
endpoint by its left endpoint. -/
def Etingof.ShortExactSequence.asExtension {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (S : Etingof.ShortExactSequence C) :
    Etingof.Extension C S.1.X₃ S.1.X₁ where
  sequence := S
  leftIso := CategoryTheory.Iso.refl _
  rightIso := CategoryTheory.Iso.refl _

/-- Forgetting the chosen endpoint identifications of an extension leaves its
underlying short exact sequence. -/
def Etingof.Extension.toShortExactSequence {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {Z X : C} (E : Etingof.Extension C Z X) :
    Etingof.ShortExactSequence C :=
  E.sequence

/-- Etingof's characterization of a short exact sequence: the first arrow is
injective, the second arrow is surjective, and the map from the cokernel of the
first arrow to the target of the second is an isomorphism.  In an abelian
category, mono and epi are the categorical versions of injective and
surjective, while the cokernel is the quotient `Y/X`. -/
theorem Etingof.shortExact_iff {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (S : CategoryTheory.ShortComplex C) :
    S.ShortExact ↔
      CategoryTheory.Mono S.f ∧ CategoryTheory.Epi S.g ∧
        CategoryTheory.IsIso
          (CategoryTheory.Limits.cokernel.desc S.f S.g S.zero) := by
  open CategoryTheory CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Mono S.f := h.mono_f
    haveI : Epi S.g := h.epi_g
    haveI : Mono (cokernel.desc S.f S.g S.zero) := h.exact.mono_cokernelDesc
    haveI : Epi (cokernel.desc S.f S.g S.zero) :=
      epi_of_epi_fac (cokernel.π_desc S.f S.g S.zero)
    exact ⟨inferInstance, inferInstance, isIso_of_mono_of_epi _⟩
  · rintro ⟨hf, hg, hq⟩
    haveI : Mono S.f := hf
    haveI : Epi S.g := hg
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := hq
    exact ShortComplex.ShortExact.mk'
      (S.exact_iff_mono_cokernel_desc.mpr inferInstance) hf hg
