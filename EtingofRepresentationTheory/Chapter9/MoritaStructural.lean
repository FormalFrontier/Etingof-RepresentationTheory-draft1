import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Simple
import Mathlib.FieldTheory.IsAlgClosed.Basic

universe u v w

/-!
# Morita structural theorem

The **Morita structural theorem** asserts that if two algebras `A` and `B` are
Morita equivalent (i.e., `ModuleCat A ≌ ModuleCat B`), then `B` is isomorphic
to a corner ring `eAe` for some idempotent `e ∈ A`.

This file also states that categorical equivalences preserve simple objects,
which is needed for the uniqueness of basic algebras (Corollary 9.7.3).

## Main results

* `Etingof.simple_of_equivalence`: An equivalence of categories preserves
  simple objects.
* `Etingof.MoritaStructural`: If `MoritaEquivalent A B`, then `B ≅ eAe`
  for some idempotent `e : A`.

## Implementation notes

The full proofs require substantial infrastructure connecting categorical Morita
equivalence (Theorem 9.6.4) with the concrete algebra-level isomorphism `B ≅ eAe`.
The key steps are:
1. An equivalence `F : ModuleCat A ≌ ModuleCat B` sends the free module `A` to a
   progenerator `P` of `ModuleCat B`.
2. `B ≅ End_B(P)ᵒᵖ` (Morita I).
3. `End_B(P)ᵒᵖ ≅ eAe` where `e` is the idempotent corresponding to the
   projection onto the image of `A` under `F`.

These steps are sorry'd pending formalization of the progenerator-to-algebra
correspondence.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

/-! ## Simple module preservation under equivalence -/

/-- An equivalence of categories preserves simple objects: if `F : C ≌ D` is
an equivalence and `X : C` is simple, then `F.functor.obj X` is simple.

Proof: `Simple` is characterized by `IsSimpleOrder (Subobject X)`. The
equivalence induces an order isomorphism on subobjects (via `MonoOver.mapIso`
composed with the essential surjectivity), preserving the simple order property.
Alternatively, use that the equivalence is fully faithful: it preserves and
reflects monomorphisms and zero morphisms, so the condition
`IsIso f ↔ f ≠ 0` for monos transfers. -/
theorem simple_of_equivalence {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ≌ D) (X : C) [Simple X] :
    Simple (F.functor.obj X) := by
  constructor
  intro Y g hMono
  -- Build a mono into X by applying F.inverse and composing with the unit
  let g' : F.inverse.obj Y ⟶ X := F.inverse.map g ≫ (F.unitIso.app X).inv
  -- g' is mono: F.inverse.map g is mono (right adjoint preserves mono),
  -- and (F.unitIso.app X).inv is iso hence mono
  haveI : Mono (F.inverse.map g) := by
    haveI : F.inverse.PreservesMonomorphisms :=
      CategoryTheory.Functor.preservesMonomorphisms_of_adjunction F.toAdjunction
    exact F.inverse.map_mono g
  haveI : Mono g' := mono_comp (F.inverse.map g) (F.unitIso.app X).inv
  -- By simplicity of X: IsIso g' ↔ g' ≠ 0
  have hSimp := Simple.mono_isIso_iff_nonzero g'
  constructor
  · -- IsIso g → g ≠ 0
    intro hIso h0
    -- g' = F.inverse.map 0 ≫ _ = 0 ≫ _ = 0
    have hg'_zero : g' = 0 := by
      simp only [g', h0, Functor.map_zero, zero_comp]
    -- g' = 0 implies ¬ IsIso g'
    have := hSimp.mp
    -- But g' is also iso (F.inverse preserves iso, and unit is iso)
    haveI : IsIso (F.inverse.map g) := by
      haveI := hIso
      exact Functor.map_isIso F.inverse g
    haveI : IsIso g' := IsIso.comp_isIso
    exact absurd hg'_zero (hSimp.mp ‹IsIso g'›)
  · -- g ≠ 0 → IsIso g
    intro hne
    -- g' ≠ 0 (because F.inverse is faithful, g ≠ 0 implies F.inverse.map g ≠ 0)
    have hg'_ne : g' ≠ 0 := by
      intro h0
      apply hne
      -- g' = F.inverse.map g ≫ unit.inv = 0
      -- So F.inverse.map g = 0 (compose with unit.hom on right)
      have h_inv_zero := congr_arg (· ≫ (F.unitIso.app X).hom) h0
      simp [g', Category.assoc] at h_inv_zero
      -- F.inverse.map g = 0 implies g = 0 by faithfulness
      exact F.inverse.map_injective (by rw [h_inv_zero, Functor.map_zero])
    -- By simplicity, g' is iso
    haveI : IsIso g' := hSimp.mpr hg'_ne
    -- F.inverse.map g = g' ≫ unit.hom, which is iso
    have : F.inverse.map g = g' ≫ (F.unitIso.app X).hom := by
      simp [g', Category.assoc]
    haveI : IsIso (F.inverse.map g) := by rw [this]; exact IsIso.comp_isIso
    -- F reflects isos (it's an equivalence), so g is iso
    exact isIso_of_reflects_iso g F.inverse

/-! ## Morita structural theorem -/

variable {k : Type u} [Field k]

/-! ### Helper lemmas for the structural theorem

The proof decomposes into two independently provable steps:

1. **Existence of a basic corner ring**: For any finite-dimensional algebra `A`
   over an algebraically closed field, there exists an idempotent `e ∈ A` such
   that the corner ring `eAe` is basic and Morita equivalent to `A`. This uses
   Wedderburn-Artin decomposition of `A/rad(A)`, idempotent lifting (Corollary
   9.1.3), and the corner functor `M ↦ eM`.

2. **Uniqueness of basic algebras**: Two basic finite-dimensional algebras over
   an algebraically closed field that are Morita equivalent must be isomorphic.
   This follows from the equivalence preserving endomorphism rings and the fact
   that a basic algebra is determined by its progenerator. -/

/-- There exists an idempotent `e ∈ A` such that `CornerRing e` is basic and
Morita equivalent to `A`.

This combines the Wedderburn-Artin decomposition (to extract one primitive
idempotent per simple module iso-class), idempotent lifting from `A/rad(A)` to
`A` (Corollary 9.1.3), and the corner functor equivalence `M ↦ eM` for full
idempotents.

The sorry's in this lemma correspond to those in
`Infrastructure.BasicAlgebraExistence` (`exists_full_idempotent_basic_corner`
and `morita_equiv_of_full_idempotent`). -/
private lemma exists_basic_corner_ring [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (e : A) (he : IsIdempotentElem e),
      @IsBasicAlgebra.{u, u, u} k _ (CornerRing (k := k) e)
        (CornerRing.instRing he) (CornerRing.instAlgebra he) ∧
      @MoritaEquivalent A _ (CornerRing (k := k) e) (CornerRing.instRing he) := by
  sorry

/-- Two basic finite-dimensional algebras over an algebraically closed field
that are Morita equivalent are isomorphic as `k`-algebras.

**Proof sketch**: Given `F : ModuleCat B₁ ≌ ModuleCat B₂`:
1. `F` sends `B₁` (as left `B₁`-module) to a progenerator `F(B₁)` of
   `ModuleCat B₂`.
2. Since `B₁` is basic, `B₁ ≅ ⊕ᵢ Pᵢ` with one copy of each indecomposable
   projective (Theorem 9.2.1(ii) with `dim Mᵢ = 1`).
3. `F` preserves indecomposable projectives (equivalences preserve
   indecomposability and projectivity).
4. `F(B₁) ≅ ⊕ᵢ F(Pᵢ)`, giving one copy of each indecomposable projective
   `B₂`-module. Since `B₂` is also basic, `F(B₁) ≅ B₂`.
5. `End_{B₁}(B₁) ≅ B₁ᵒᵖ` and `End_{B₂}(B₂) ≅ B₂ᵒᵖ`
   (`RingEquiv.moduleEndSelf`).
6. The equivalence preserves endomorphism rings: `End_{B₁}(B₁) ≅ End_{B₂}(F(B₁))`.
7. Composing: `B₁ᵒᵖ ≅ B₂ᵒᵖ`, hence `B₁ ≅ B₂` as `k`-algebras. -/
private lemma basic_morita_equiv_algEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (h : MoritaEquivalent B₁ B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  sorry

/-- **Morita structural theorem**: If `A` is a finite-dimensional `k`-algebra
over an algebraically closed field and `B` is a basic finite-dimensional
`k`-algebra that is Morita equivalent to `A`, then there exists an idempotent
`e : A` such that `B` is isomorphic (as a `k`-algebra) to the corner ring `eAe`.

The `IsBasicAlgebra k B` hypothesis is essential: without it the statement is
false. For example, `k` and `Mₙ(k)` are Morita equivalent, but `Mₙ(k)` cannot
be realized as `eke` for any `e ∈ k`. The basic algebra is always the smallest
representative in a Morita equivalence class, so it embeds as a corner ring of
any other representative.

This is the concrete algebraic content of Morita's theorem beyond the categorical
equivalence proved in Theorem 9.6.4.
(Etingof, discussion after Definition 9.7.1)

## Proof

1. By `exists_basic_corner_ring`, obtain an idempotent `e ∈ A` such that
   `CornerRing e` is basic and Morita equivalent to `A`.
2. Since `B` is also basic and Morita equivalent to `A`, we have
   `MoritaEquivalent B (CornerRing e)` by transitivity.
3. By `basic_morita_equiv_algEquiv`, `B ≅ CornerRing e` as `k`-algebras. -/
theorem MoritaStructural [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (_hB : IsBasicAlgebra k B)
    (h : MoritaEquivalent A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty (@AlgEquiv k B (CornerRing (k := k) e) _ _
        (CornerRing.instRing he).toSemiring
        _ (@CornerRing.instAlgebra k _ A _ _ e he)) := by
  -- Step 1: Get a basic corner ring of A
  obtain ⟨e, he, hbasic, hMor_corner⟩ := exists_basic_corner_ring (k := k) A
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he
  -- Step 2: B and CornerRing e are both basic and Morita equivalent
  -- h : MoritaEquivalent A B, hMor_corner : MoritaEquivalent A (CornerRing e)
  -- Need: MoritaEquivalent B (CornerRing e), i.e., h⁻¹ ∘ hMor_corner
  have hMor_BC : MoritaEquivalent B (CornerRing (k := k) e) := by
    obtain ⟨F⟩ := h
    obtain ⟨G⟩ := hMor_corner
    exact ⟨F.symm.trans G⟩
  -- Step 3: Two basic Morita-equivalent algebras are isomorphic
  obtain ⟨φ⟩ := basic_morita_equiv_algEquiv B (CornerRing (k := k) e) _hB hbasic hMor_BC
  exact ⟨e, he, ⟨φ⟩⟩

/-- **Dimension bound from Morita equivalence**: If `A` and `B` are Morita
equivalent, then `dim B ≤ dim A` (when `B` is the basic algebra).
This follows from `B ≅ eAe` and `dim(eAe) ≤ dim(A)`. -/
theorem MoritaEquivalent.finrank_cornerRing_le
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (e : A) :
    Module.finrank k (cornerSubmodule (k := k) e) ≤ Module.finrank k A :=
  finrank_cornerSubmodule_le e

end Etingof
