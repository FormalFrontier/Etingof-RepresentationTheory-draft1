/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Ring.ULift
import RepresentationTheory.Algebra.Homological.EquivalenceInvariance

/-!
# Auxiliary dimension transfer

This module records reflection of projective-dimension bounds along suitable functors and a
comparison with universe lifts.
-/

universe v u

open CategoryTheory Limits CategoryTheory.Limits

namespace RepresentationTheory.Algebra.Homological.AuxiliaryDimensionTransfer

section Reflect

variable {C : Type*} {D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- A full and faithful additive functor reflects a strict bound on projective dimension under
the stated preservation hypotheses. -/
theorem hasProjectiveDimensionLT_of_fully_faithful (F : C ⥤ D) [F.Additive] [F.Full]
    [F.Faithful] [F.PreservesEpimorphisms] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F] [F.PreservesProjectiveObjects] [EnoughProjectives C] :
    ∀ (n : ℕ) (X : C), HasProjectiveDimensionLT (F.obj X) n → HasProjectiveDimensionLT X n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    match n, IH with
    | 0, _ =>
        intro X hX
        rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
        rw [IsZero.iff_id_eq_zero] at hX ⊢
        apply F.map_injective
        rw [F.map_id, F.map_zero]
        exact hX
    | 1, _ =>
        intro X hX
        haveI : Projective (F.obj X) := projective_iff_hasProjectiveDimensionLT_one.mpr hX
        exact projective_iff_hasProjectiveDimensionLT_one.mp (F.projective_of_map_projective ‹_›)
    | (m + 2), IH =>
        intro X hX
        obtain ⟨P⟩ : Nonempty (ProjectivePresentation X) := EnoughProjectives.presentation X
        let S : ShortComplex C := ShortComplex.mk _ _ (kernel.condition P.f)
        have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
        have hSEF : (S.map F).ShortExact := hSE.map_of_exact F
        haveI : Projective (S.map F).X₂ := by
          change Projective (F.obj P.p); infer_instance
        have hFP1 : HasProjectiveDimensionLT (S.map F).X₂ (m + 1) :=
          hasProjectiveDimensionLT_of_ge (S.map F).X₂ 1 (m + 1) (by omega)
        have hFK : HasProjectiveDimensionLT (S.map F).X₁ (m + 1) :=
          hSEF.hasProjectiveDimensionLT_X₁ (m + 1) hFP1 hX
        have hK : HasProjectiveDimensionLT S.X₁ (m + 1) := by
          have : HasProjectiveDimensionLT (F.obj S.X₁) (m + 1) := hFK
          exact IH (m + 1) (by omega) S.X₁ this
        haveI hP1 : HasProjectiveDimensionLT P.p 1 :=
          projective_iff_hasProjectiveDimensionLT_one.mp P.projective
        have hP2 : HasProjectiveDimensionLT S.X₂ (m + 2) :=
          hasProjectiveDimensionLT_of_ge P.p 1 (m + 2) (by omega)
        exact hSE.hasProjectiveDimensionLT_X₃ (m + 1) hK hP2

end Reflect

/-- Transfers the auxiliary ring-indexed datum from a lifted universe to the original ring. -/
theorem auxiliary_ulift_down {R : Type u} [Ring R] {d : ℕ}
    (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty (ULift.{v} R) d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d := by
  let E : ModuleCat.{max u v} R ≌ ModuleCat.{max u v} (ULift.{v} R) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv (R := R))
  have hbig : ∀ N : ModuleCat.{max u v} R, HasProjectiveDimensionLE N d := by
    intro N
    exact
      (RepresentationTheory.Algebra.Homological.EquivalenceInvariance.hasProjectiveDimensionLT_iff_of_equivalence
        E (d + 1) N).mp
        (h (E.functor.obj N))
  intro M
  have := hbig ((ModuleCat.uliftFunctor.{v, u} R).obj M)
  exact hasProjectiveDimensionLT_of_fully_faithful
    (ModuleCat.uliftFunctor.{v, u} R) (d + 1) M this

/-- Places an auxiliary ring-indexed quantity below its value after a universe lift. -/
theorem auxiliary_le_ulift {R : Type u} [Ring R] :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R ≤
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant (ULift.{v} R) := by
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  exact le_iInf₂ fun d hd => iInf₂_le d (auxiliary_ulift_down hd)

end RepresentationTheory.Algebra.Homological.AuxiliaryDimensionTransfer
