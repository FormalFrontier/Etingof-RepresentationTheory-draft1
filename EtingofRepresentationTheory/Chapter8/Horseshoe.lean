import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The horseshoe lemma

Given a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in an abelian category with enough
projectives, and projective resolutions `P₁` of `X₁` and `P₃` of `X₃`, the **horseshoe lemma**
produces a projective resolution `P₂` of `X₂` whose terms are the biproducts
`P₂.X n = P₁.X n ⊞ P₃.X n`, together with a short exact sequence of chain complexes

`0 → P₁.complex →ᵅ P₂.complex →ᵝ P₃.complex → 0`

that is *degreewise split* (each degree is the split biproduct sequence
`0 → P₁ₙ → P₁ₙ ⊞ P₃ₙ → P₃ₙ → 0`) and lifts `S`, in the sense that the augmentations satisfy the
two compatibility squares
`α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f` and `β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g`.

This is the book's construction `P²ᵢ := P¹ᵢ ⊕ P³ᵢ` (Problem 8.2.6(v),
`blobs/Chapter8/Problem8.2.6.md`), whose degreewise lifting step is `Exercise_8_1_4`
(`Chapter8/Exercise8_1_4.lean`). It is the crux the first-argument `Tor`/`Ext` long exact
sequences of Problem 8.2.6 rely on: because the sequence of complexes is degreewise split, it is
preserved by any additive functor (in particular `- ⊗_A N`), so applying such a functor and
taking homology yields the six-term homology window via
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁/₂/₃`, with the objects identified with
left-derived functors through `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj`.

## Construction (the standard horseshoe)

The augmentation compatibility squares in the conclusion are exactly the hypotheses required by
`ProjectiveResolution.isoLeftDerivedObj_hom_naturality` downstream, so they are stated as part of
the deliverable.

Write `S.f : X₁ ⟶ X₂`, `S.g : X₂ ⟶ X₃`, `ε₁ := P₁.π.f 0`, `ε₃ := P₃.π.f 0`,
`d¹ := P₁.complex.d`, `d³ := P₃.complex.d`.

* Terms: `P₂.X n := P₁.X n ⊞ P₃.X n`, with `α` degreewise `biprod.inl` and `β` degreewise
  `biprod.snd`. The degreewise sequence `0 → P₁ₙ → P₁ₙ ⊞ P₃ₙ → P₃ₙ → 0` is the split biproduct
  short exact sequence (`ShortComplex.Splitting`, hence `ShortExact`).
* Augmentation: choose a lift `h₀ : P₃₀ ⟶ X₂` of `ε₃` through the epi `S.g` (projectivity of
  `P₃₀`; `g ∘ h₀ = ε₃`). Set `ε₂ := biprod.desc (ε₁ ≫ S.f) h₀ : P₁₀ ⊞ P₃₀ ⟶ X₂`; it is epi and
  satisfies `α.f 0 ≫ ε₂ = ε₁ ≫ S.f` and `β.f 0 ≫ S.g ∘ ... = ...` giving the two squares.
* Differentials `d²ₙ = ⟪⟪d¹ₙ, sₙ⟫, ⟪0, d³ₙ⟫⟫` (lower triangular biproduct matrix) with
  off-diagonal lift `sₙ : P₃ₙ ⟶ P₁_{n-1}` built by induction: projectivity of `P₃ₙ` against the
  epi `d¹_{n-1} : P₁ₙ ↠ ker …` (equivalently `Exercise_8_1_4`) produces `sₙ` making
  `d¹_{n-1} ≫ sₙ = - sₙ₋₁ ≫ d³ₙ` and `ε₂`-compatibility hold; this uses the exactness of the
  *given* resolutions `P₁`, `P₃`, not of the complex being built.
* `P₂` is a resolution: the sequence of complexes is short exact, `P₁`, `P₃` are exact off
  degree `0` and resolve `X₁`, `X₃`, so the homology long exact sequence (together with `hS`
  in degree `0`) forces `P₂.complex` exact off degree `0` with `H₀ = X₂`; each `P₂.X n` is
  projective as a biproduct of projectives.

## Status

Spec-first: the statement is recorded and the construction/proof is deferred (`sorry`). The
resolution *data* (the twisted differential threading the inductive lift, the augmentation, and
the chain maps `α`, `β`) is the substantial remaining work; see the route above. Once built, only
`Prop`-level obligations (`d ≫ d = 0`, chain-map laws, `QuasiIso`, `ShortExact`) remain, and the
theorem should become sorry-free.
-/

universe v u

open CategoryTheory Category Limits

namespace Etingof

section Augmentation

variable {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)

/-- The degree-`0` augmentation of the horseshoe resolution of `S.X₂`, on the biproduct
`P₁.complex.X 0 ⊞ P₃.complex.X 0`. On the `P₁` summand it is `P₁.π.f 0 ≫ S.f`; on the `P₃`
summand it is a lift of `P₃.π.f 0` through the epimorphism `S.g` (which exists because
`P₃.complex.X 0` is projective). This is the base case of the horseshoe augmentation; the two
compatibility squares of the horseshoe lemma reduce to `horseshoeπZero_inl` and
`horseshoeπZero_comp_g` in degree `0`. -/
noncomputable def horseshoeπZero :
    P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ S.X₂ :=
  haveI := hS.epi_g
  biprod.desc (P₁.π.f 0 ≫ S.f) (Projective.factorThru (P₃.π.f 0) S.g)

@[reassoc (attr := simp)]
lemma horseshoeπZero_inl :
    biprod.inl ≫ horseshoeπZero hS P₁ P₃ = P₁.π.f 0 ≫ S.f := by
  simp [horseshoeπZero]

/-- The `P₃`-summand of the horseshoe augmentation covers `P₃.π.f 0` after `S.g`. -/
@[reassoc (attr := simp)]
lemma horseshoeπZero_inr_comp_g :
    haveI := hS.epi_g
    (biprod.inr ≫ horseshoeπZero hS P₁ P₃) ≫ S.g = P₃.π.f 0 := by
  haveI := hS.epi_g
  simp [horseshoeπZero, Projective.factorThru_comp]

/-- The second augmentation-compatibility square in degree `0`:
`biprod.snd ≫ P₃.π.f 0 = horseshoeπZero ≫ S.g` (with `β.f 0 = biprod.snd`,
`P₂.π.f 0 = horseshoeπZero`). Uses `S.f ≫ S.g = 0` to kill the `P₁` summand. -/
@[reassoc]
lemma horseshoeπZero_comp_g :
    horseshoeπZero hS P₁ P₃ ≫ S.g = biprod.snd ≫ P₃.π.f 0 := by
  haveI := hS.epi_g
  ext
  · simp [horseshoeπZero]
  · simp [horseshoeπZero, Projective.factorThru_comp]

end Augmentation

/-- **The horseshoe lemma.** A short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in an abelian
category with enough projectives, together with projective resolutions `P₁` of `X₁` and `P₃` of
`X₃`, gives a projective resolution `P₂` of `X₂` and chain maps
`α : P₁.complex ⟶ P₂.complex`, `β : P₂.complex ⟶ P₃.complex` forming a short exact sequence of
complexes lifting `S`: the augmentation squares `α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f` and
`β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g` commute. (In the intended construction `P₂` has terms
`P₁.X n ⊞ P₃.X n` and the sequence of complexes is degreewise split, hence preserved by any
additive functor.) -/
theorem horseshoe {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    ∃ (P₂ : ProjectiveResolution S.X₂)
      (α : P₁.complex ⟶ P₂.complex) (β : P₂.complex ⟶ P₃.complex)
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
      α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f ∧
      β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g := by
  sorry

end Etingof
