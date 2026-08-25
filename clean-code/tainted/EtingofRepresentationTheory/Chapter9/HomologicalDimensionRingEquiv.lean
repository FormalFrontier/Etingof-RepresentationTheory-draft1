import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import EtingofRepresentationTheory.Chapter9.Definition9_4_3

/-!
# Homological dimension is invariant under a ring equivalence

This file proves that `Etingof.homologicalDimension` (Definition 9.4.3) is invariant under a
ring isomorphism `e : R ≃+* S`:

* `Etingof.hasHomologicalDimensionLE_congr`: `HasHomologicalDimensionLE R d`
  iff `HasHomologicalDimensionLE S d`;
* `Etingof.homologicalDimension_congr`: `homologicalDimension R = homologicalDimension S`.

## Strategy

A ring equivalence `e : R ≃+* S` induces an additive equivalence of module categories
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv e : ModuleCat S ≌ ModuleCat R`. Since
`HasProjectiveDimensionLE X n := HasProjectiveDimensionLT X (n + 1)` is defined by the vanishing
of `Ext` groups, and Mathlib has no ready lemma transferring it across an equivalence, we prove the
transfer directly: for an additive equivalence `e : C ≌ D` of abelian categories with enough
projectives, projective dimension `< n` is preserved by `e.functor`
(`hasProjectiveDimensionLT_map`). The proof is a strong induction on `n` using the standard
dimension-shifting short exact sequence coming from a projective presentation, mapped across `e`
(`e.functor` preserves projectives, short exact sequences and zero objects because it is an
equivalence). The iff form (`hasProjectiveDimensionLT_map_iff`) follows by also applying the
statement to `e.symm`.

The lemmas are stated for two rings in the same universe, which is all the free-algebra
corollary of Problem 9.4.6 (i) (`homologicalDimension_freeAlgebra_eq_one`) needs, since
`FreeAlgebra k (Fin n)` and the one-vertex path algebra are both `Type u`.
-/

universe u v

open CategoryTheory Limits CategoryTheory.Limits

namespace Etingof

section Equivalence

variable {C : Type*} {D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- An additive equivalence `e : C ≌ D` of abelian categories (with `C` having enough projectives)
maps objects of projective dimension `< n` to objects of projective dimension `< n`.

Strong induction on `n`. The base cases are `n = 0` (`e.functor` preserves zero objects) and
`n = 1` (`e.functor` preserves projectives, being an equivalence). For `n + 2` one takes a
projective presentation `0 → K → P → X → 0`, shifts `X`'s dimension down to `K`
(`hasProjectiveDimensionLT_X₁`), applies the induction hypothesis to `K`, and shifts back up along
the image short exact sequence `0 → e K → e P → e X → 0` (`hasProjectiveDimensionLT_X₃`). -/
theorem hasProjectiveDimensionLT_map (e : C ≌ D) [e.functor.Additive] [EnoughProjectives C] :
    ∀ (n : ℕ) (X : C), HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT (e.functor.obj X) n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    match n, IH with
    | 0, _ =>
        intro X hX
        rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
        exact e.functor.map_isZero hX
    | 1, _ =>
        intro X hX
        haveI : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr hX
        exact projective_iff_hasProjectiveDimensionLT_one.mp
          (inferInstance : Projective (e.functor.obj X))
    | (m + 2), IH =>
        intro X hX
        -- A projective presentation `0 → K → P → X → 0`.
        obtain ⟨P⟩ : Nonempty (ProjectivePresentation X) := EnoughProjectives.presentation X
        let S : ShortComplex C := ShortComplex.mk _ _ (kernel.condition P.f)
        have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
        -- `P.p` is projective, so has projective dimension `< 1`, hence `< m + 1`.
        haveI hP1 : HasProjectiveDimensionLT P.p 1 :=
          projective_iff_hasProjectiveDimensionLT_one.mp P.projective
        have hPm1 : HasProjectiveDimensionLT S.X₂ (m + 1) :=
          hasProjectiveDimensionLT_of_ge P.p 1 (m + 1) (by omega)
        -- Dimension shift: `pd X < m + 2` gives `pd K < m + 1`.
        have hK : HasProjectiveDimensionLT S.X₁ (m + 1) :=
          hSE.hasProjectiveDimensionLT_X₁ (m + 1) hPm1 hX
        -- Induction hypothesis on the syzygy `K`.
        have hFK : HasProjectiveDimensionLT (e.functor.obj S.X₁) (m + 1) :=
          IH (m + 1) (by omega) S.X₁ hK
        -- Map the short exact sequence across the (exact) equivalence.
        have hSEF : (S.map e.functor).ShortExact := hSE.map_of_exact e.functor
        -- `e P` is projective, so has projective dimension `< m + 2`.
        haveI : Projective (S.map e.functor).X₂ := by
          change Projective (e.functor.obj P.p); infer_instance
        have hFP : HasProjectiveDimensionLT (S.map e.functor).X₂ (m + 2) := by
          have h1 : HasProjectiveDimensionLT (S.map e.functor).X₂ 1 :=
            projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
          exact hasProjectiveDimensionLT_of_ge (S.map e.functor).X₂ 1 (m + 2) (by omega)
        -- Dimension shift back up along the image short exact sequence.
        have : HasProjectiveDimensionLT (S.map e.functor).X₃ (m + 2) :=
          hSEF.hasProjectiveDimensionLT_X₃ (m + 1) hFK hFP
        exact this

/-- Projective dimension `< n` is preserved and reflected by an additive equivalence: it holds for
`e.functor.obj X` iff it holds for `X`. The forward direction is `hasProjectiveDimensionLT_map`
applied to `e.symm` composed with the unit isomorphism; the backward direction is a direct
application of `hasProjectiveDimensionLT_map`. -/
theorem hasProjectiveDimensionLT_map_iff (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [EnoughProjectives C] [EnoughProjectives D]
    (n : ℕ) (X : C) :
    HasProjectiveDimensionLT (e.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  constructor
  · intro h
    haveI : e.symm.functor.Additive := (inferInstance : e.inverse.Additive)
    haveI key : HasProjectiveDimensionLT (e.inverse.obj (e.functor.obj X)) n :=
      hasProjectiveDimensionLT_map e.symm n (e.functor.obj X) h
    have iso : e.inverse.obj (e.functor.obj X) ≅ X := (e.unitIso.app X).symm
    exact hasProjectiveDimensionLT_of_iso iso n
  · exact hasProjectiveDimensionLT_map e n X

end Equivalence

/-- **Ring-equivalence invariance of homological dimension (predicate form).** If `R ≃+* S`, then
`R` has homological dimension `≤ d` iff `S` does. Both rings live in the same universe. -/
theorem hasHomologicalDimensionLE_congr {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (d : ℕ) :
    HasHomologicalDimensionLE R d ↔ HasHomologicalDimensionLE S d := by
  -- `F : ModuleCat S ≌ ModuleCat R`, an additive equivalence of abelian categories.
  let F : ModuleCat.{u} S ≌ ModuleCat.{u} R := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  constructor
  · intro hR M
    -- `HasProjectiveDimensionLE M d = HasProjectiveDimensionLT M (d + 1)`.
    exact (hasProjectiveDimensionLT_map_iff F (d + 1) M).mp (hR (F.functor.obj M))
  · intro hS N
    haveI h2 : HasProjectiveDimensionLT (F.functor.obj (F.inverse.obj N)) (d + 1) :=
      (hasProjectiveDimensionLT_map_iff F (d + 1) (F.inverse.obj N)).mpr (hS (F.inverse.obj N))
    have iso : F.functor.obj (F.inverse.obj N) ≅ N := F.counitIso.app N
    exact hasProjectiveDimensionLT_of_iso iso (d + 1)

/-- **Ring-equivalence invariance of homological dimension.** Isomorphic rings (in the same
universe) have equal homological dimension. -/
theorem homologicalDimension_congr {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    homologicalDimension R = homologicalDimension S := by
  unfold homologicalDimension
  refine iInf_congr fun d => ?_
  by_cases h : HasHomologicalDimensionLE R d
  · rw [iInf_pos h, iInf_pos ((hasHomologicalDimensionLE_congr e d).mp h)]
  · rw [iInf_neg h, iInf_neg (fun hs => h ((hasHomologicalDimensionLE_congr e d).mpr hs))]

/-- **Left/right agreement for commutative rings (predicate form).** A commutative ring is
isomorphic to its opposite (`RingEquiv.toOpposite`), so its right homological-dimension bound
coincides with its left one. -/
theorem hasRightHomologicalDimensionLE_iff_left {R : Type u} [CommRing R] (d : ℕ) :
    HasRightHomologicalDimensionLE R d ↔ HasLeftHomologicalDimensionLE R d := by
  rw [hasRightHomologicalDimensionLE_iff_op]
  exact (hasHomologicalDimensionLE_congr (RingEquiv.toOpposite R) d).symm

/-- **Left/right agreement for commutative rings.** A commutative ring is isomorphic to its
opposite (`RingEquiv.toOpposite`), so its right and left homological dimensions coincide. -/
theorem rightHomologicalDimension_eq_left {R : Type u} [CommRing R] :
    rightHomologicalDimension R = leftHomologicalDimension R := by
  rw [rightHomologicalDimension_eq_left_op]
  exact (homologicalDimension_congr (RingEquiv.toOpposite R)).symm

end Etingof
