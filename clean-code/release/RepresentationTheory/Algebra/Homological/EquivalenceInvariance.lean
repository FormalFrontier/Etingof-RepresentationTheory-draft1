/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import RepresentationTheory.Auxiliary.RingData

/-!
# Invariance under equivalences

This module records invariance results for projective-dimension bounds and related ring data under
categorical and ring equivalences.
-/

universe u v

open CategoryTheory Limits CategoryTheory.Limits

namespace RepresentationTheory.Algebra.Homological.EquivalenceInvariance

section Equivalence

variable {C : Type*} {D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- An equivalence sends objects of bounded projective dimension to objects with the same bound. -/
theorem hasProjectiveDimensionLT_of_equivalence (e : C ≌ D) [e.functor.Additive]
    [EnoughProjectives C] :
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
        obtain ⟨P⟩ : Nonempty (ProjectivePresentation X) := EnoughProjectives.presentation X
        let S : ShortComplex C := ShortComplex.mk _ _ (kernel.condition P.f)
        have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
        haveI hP1 : HasProjectiveDimensionLT P.p 1 :=
          projective_iff_hasProjectiveDimensionLT_one.mp P.projective
        have hPm1 : HasProjectiveDimensionLT S.X₂ (m + 1) :=
          hasProjectiveDimensionLT_of_ge P.p 1 (m + 1) (by omega)
        have hK : HasProjectiveDimensionLT S.X₁ (m + 1) :=
          hSE.hasProjectiveDimensionLT_X₁ (m + 1) hPm1 hX
        have hFK : HasProjectiveDimensionLT (e.functor.obj S.X₁) (m + 1) :=
          IH (m + 1) (by omega) S.X₁ hK
        have hSEF : (S.map e.functor).ShortExact := hSE.map_of_exact e.functor
        haveI : Projective (S.map e.functor).X₂ := by
          change Projective (e.functor.obj P.p); infer_instance
        have hFP : HasProjectiveDimensionLT (S.map e.functor).X₂ (m + 2) := by
          have h1 : HasProjectiveDimensionLT (S.map e.functor).X₂ 1 :=
            projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
          exact hasProjectiveDimensionLT_of_ge (S.map e.functor).X₂ 1 (m + 2) (by omega)
        have : HasProjectiveDimensionLT (S.map e.functor).X₃ (m + 2) :=
          hSEF.hasProjectiveDimensionLT_X₃ (m + 1) hFK hFP
        exact this

/-- A categorical equivalence preserves and reflects bounded projective dimension. -/
theorem hasProjectiveDimensionLT_iff_of_equivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [EnoughProjectives C] [EnoughProjectives D]
    (n : ℕ) (X : C) :
    HasProjectiveDimensionLT (e.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  constructor
  · intro h
    haveI : e.symm.functor.Additive := (inferInstance : e.inverse.Additive)
    haveI key : HasProjectiveDimensionLT (e.inverse.obj (e.functor.obj X)) n :=
      hasProjectiveDimensionLT_of_equivalence e.symm n (e.functor.obj X) h
    have iso : e.inverse.obj (e.functor.obj X) ≅ X := (e.unitIso.app X).symm
    exact hasProjectiveDimensionLT_of_iso iso n
  · exact hasProjectiveDimensionLT_of_equivalence e n X

end Equivalence

/-- A degree-indexed property of rings is invariant under ring equivalences. -/
theorem ringProperty_iff_of_ringEquiv {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    (d : ℕ) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d ↔
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty S d := by
  let F : ModuleCat.{u} S ≌ ModuleCat.{u} R := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  constructor
  · intro hR M
    exact (hasProjectiveDimensionLT_iff_of_equivalence F (d + 1) M).mp
      (hR (F.functor.obj M))
  · intro hS N
    haveI h2 : HasProjectiveDimensionLT (F.functor.obj (F.inverse.obj N)) (d + 1) :=
      (hasProjectiveDimensionLT_iff_of_equivalence F (d + 1) (F.inverse.obj N)).mpr
        (hS (F.inverse.obj N))
    have iso : F.functor.obj (F.inverse.obj N) ≅ N := F.counitIso.app N
    exact hasProjectiveDimensionLT_of_iso iso (d + 1)

/-- Ring equivalences leave the displayed ring-indexed construction unchanged. -/
theorem ringConstruction_eq_of_ringEquiv {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R =
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant S := by
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  refine iInf_congr fun d => ?_
  by_cases h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d
  · rw [iInf_pos h, iInf_pos ((ringProperty_iff_of_ringEquiv e d).mp h)]
  · rw [iInf_neg h, iInf_neg (fun hs => h ((ringProperty_iff_of_ringEquiv e d).mpr hs))]

/-- The two displayed degree-indexed properties agree for every commutative ring. -/
theorem firstRingProperty_iff_secondRingProperty {R : Type u} [CommRing R] (d : ℕ) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyThird R d ↔
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyAux R d := by
  rw [RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyThird_opposite_iff]
  exact (ringProperty_iff_of_ringEquiv (RingEquiv.toOpposite R) d).symm

/-- The two displayed constructions agree for all commutative rings. -/
theorem firstRingConstruction_eq_secondRingConstruction {R : Type u} [CommRing R] :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantThird R =
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantAux R := by
  rw [RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantThird_opposite]
  exact (ringConstruction_eq_of_ringEquiv (RingEquiv.toOpposite R)).symm

end RepresentationTheory.Algebra.Homological.EquivalenceInvariance
