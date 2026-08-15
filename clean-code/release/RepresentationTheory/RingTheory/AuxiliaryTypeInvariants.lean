/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Algebra.TensorProduct.MatrixProductEquivalence

open CategoryTheory

open scoped TensorProduct

namespace RepresentationTheory.RingTheory.AuxiliaryTypeInvariants

universe u

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- An equivalence of module categories induces an equivalence of auxiliary types. -/
noncomputable def auxiliaryType_equiv_of_moduleCat_equivalence {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} R ≃ RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} S :=
  RepresentationTheory.CategoryTheory.IsomorphismClasses.Equivalence.isomorphismClassesEquiv
    (Equivalence.congrFullSubcategory E
      (P := RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} R)) (Q := RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} S))
      (funext fun X => propext (RepresentationTheory.SimpleRepresentationModules.simple_map_iff_of_equivalence E X)))

/-- A ring equivalence induces an equivalence of auxiliary types. -/
noncomputable def auxiliaryType_equiv_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (f : R ≃+* S) : RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} R ≃ RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} S :=
  auxiliaryType_equiv_of_moduleCat_equivalence (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm)

/-- A positive-size square matrix ring has an auxiliary type equivalent to that of its coefficient ring. -/
noncomputable def matrix_auxiliaryType_equiv {R : Type u} [Ring R] (m : ℕ) [NeZero m] :
    RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin m) (Fin m) R) ≃ RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} R :=
  (auxiliaryType_equiv_of_moduleCat_equivalence
    (ModuleCat.matrixEquivalence R (⟨0, Nat.pos_of_neZero m⟩ : Fin m))).symm

/-- A nontrivial finite-dimensional algebra has a nonempty auxiliary type. -/
theorem nonempty_auxiliaryType (k : Type u) {B : Type u} [Field k] [Ring B]
    [Nontrivial B] [Algebra k B] [Module.Finite k B] :
    Nonempty (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} B) := by
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  haveI : IsAtomic (Submodule B B) := isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨m, hm⟩ : ∃ m : Submodule B B, IsSimpleModule B m := by
    simpa only [isSimpleModule_iff_isAtom] using IsAtomic.exists_atom (Submodule B B)
  haveI := hm
  haveI : Simple (ModuleCat.of B (m : Type u)) := inferInstance
  exact ⟨Quotient.mk _ ⟨ModuleCat.of B (m : Type u), this⟩⟩

/-- The auxiliary type of a division ring is subsingleton. -/
theorem subsingleton_auxiliaryType_of_divisionRing (D : Type u) [DivisionRing D] :
    Subsingleton (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} D) := by

  have key : ∀ (M : Type u) [AddCommGroup M] [Module D M] [IsSimpleModule D M],
      Nonempty (M ≃ₗ[D] (D ⧸ (⊥ : Ideal D))) := by
    intro M _ _ _
    obtain ⟨I, hmax, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := D) (M := M)).mp ‹_›
    have hI : I = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top I).resolve_right hmax.ne_top
    exact ⟨hI ▸ e⟩
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
  induction b using Quotient.inductionOn with
  | _ Q =>
  haveI : Simple P.obj := P.property
  haveI : Simple Q.obj := Q.property
  haveI : IsSimpleModule D (P.obj : ModuleCat.{u} D) := inferInstance
  haveI : IsSimpleModule D (Q.obj : ModuleCat.{u} D) := inferInstance
  obtain ⟨eP⟩ := key (P.obj : ModuleCat.{u} D)
  obtain ⟨eQ⟩ := key (Q.obj : ModuleCat.{u} D)
  exact Quotient.sound
    ⟨(RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} D)).fullyFaithfulι.preimageIso (eP.trans eQ.symm).toModuleIso⟩

section Pi

variable {n : ℕ} (R : Fin n → Type u) [∀ i, Ring (R i)]

private def idModuleIso {S : Type*} [Ring S] {M : Type u} [AddCommGroup M]
    (i₁ i₂ : Module S M) (h : ∀ (s : S) (x : M), (letI := i₁; s • x) = (letI := i₂; s • x)) :
    (letI := i₁; ModuleCat.of S M) ≅ (letI := i₂; ModuleCat.of S M) :=
  @LinearEquiv.toModuleIso S _ M M _ _ i₁ i₂
    (@AddEquiv.toLinearEquiv S M M _ _ _ i₁ i₂ (AddEquiv.refl M) h)

private noncomputable def inflatePiObj (i : Fin n)
    (P : (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (R i))).FullSubcategory) :
    (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (∀ j, R j))).FullSubcategory := by
  haveI : Simple P.obj := P.property
  haveI hsP : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
  letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
    Module.compHom _ (Pi.evalRingHom R i)
  haveI : RingHomSurjective (Pi.evalRingHom R i) := ⟨fun x => ⟨Pi.single i x, by simp⟩⟩
  haveI : IsSimpleModule (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
    (LinearMap.isSimpleModule_iff_of_bijective
      ({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        (P.obj : ModuleCat.{u} (R i)) →ₛₗ[Pi.evalRingHom R i]
          (P.obj : ModuleCat.{u} (R i))) Function.bijective_id).mpr hsP
  exact ⟨ModuleCat.of (∀ j, R j) (P.obj : ModuleCat.{u} (R i)), simple_of_isSimpleModule⟩

private noncomputable def inflatePiClass (i : Fin n) :
    RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (R i) → RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (∀ j, R j) :=
  Quotient.map (inflatePiObj R i) (by
    rintro P P' ⟨iso⟩
    haveI : Simple P.obj := P.property
    haveI : Simple P'.obj := P'.property
    haveI : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
    haveI : IsSimpleModule (R i) (P'.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
    have eR : (P.obj : ModuleCat.{u} (R i)) ≃ₗ[R i] (P'.obj : ModuleCat.{u} (R i)) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
      Module.compHom _ (Pi.evalRingHom R i)
    letI : Module (∀ j, R j) (P'.obj : ModuleCat.{u} (R i)) :=
      Module.compHom _ (Pi.evalRingHom R i)
    refine ⟨(RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (∀ j, R j))).fullyFaithfulι.preimageIso
      (LinearEquiv.toModuleIso
        { toFun := eR, invFun := eR.symm, left_inv := eR.left_inv, right_inv := eR.right_inv,
          map_add' := eR.map_add,
          map_smul' := fun s x => eR.map_smul (Pi.evalRingHom R i s) x })⟩)

private noncomputable def sigmaToPi :
    (Σ i, RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (R i)) → RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (∀ j, R j) :=
  fun p => inflatePiClass R p.1 p.2

private theorem exists_support_index (M : Type u) [AddCommGroup M] [Module (∀ j, R j) M]
    [IsSimpleModule (∀ j, R j) M] :
    ∃ i, ∀ m : M, (Pi.single i (1 : R i) : ∀ j, R j) • m = m := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (∀ j, R j) M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hsum : ∑ i, (Pi.single i (1 : R i) : ∀ j, R j) = 1 := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j
      (fun b _ hbj => by simp [hbj]) (fun hj => absurd (Finset.mem_univ j) hj)]
    simp
  have hne : ∃ i, (Pi.single i (1 : R i) : ∀ j, R j) • m₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    apply hm₀
    calc m₀ = (1 : ∀ j, R j) • m₀ := (one_smul _ _).symm
      _ = (∑ i, (Pi.single i (1 : R i) : ∀ j, R j)) • m₀ := by rw [hsum]
      _ = ∑ i, (Pi.single i (1 : R i) : ∀ j, R j) • m₀ := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ?_⟩
  set e : (∀ j, R j) := Pi.single i (1 : R i) with he
  have hcentral : ∀ s : ∀ j, R j, e * s = s * e := by
    intro s; funext j
    rcases eq_or_ne i j with h | h
    · subst h; simp [he, Pi.single_eq_same]
    · simp [he, Pi.single_eq_of_ne (Ne.symm h)]
  have hidem : e * e = e := by
    funext j
    rcases eq_or_ne i j with h | h
    · subst h; simp [he, Pi.single_eq_same]
    · simp [he, Pi.single_eq_of_ne (Ne.symm h)]
  let g : M →ₗ[∀ j, R j] M :=
    { toFun := fun m => e • m
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s m => by
        simp only [RingHom.id_apply]
        rw [← mul_smul, ← mul_smul, hcentral s] }
  have hg : ∀ m, g m = e • m := fun _ => rfl
  have hrange : LinearMap.range g = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range g) with h | h
    · exfalso
      apply hi
      have hmem : g m₀ ∈ LinearMap.range g := ⟨m₀, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hmem
    · exact h
  intro m
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hrange m
  rw [hg] at hx
  rw [← hx, ← mul_smul, hidem]

private theorem sigmaToPi_injective : Function.Injective (sigmaToPi R) := by
  rintro ⟨i, c⟩ ⟨i', c'⟩ hEq
  induction c using Quotient.inductionOn with | _ P => ?_
  induction c' using Quotient.inductionOn with | _ P' => ?_
  have hEq' : (Quotient.mk _ (inflatePiObj R i P) : RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (∀ j, R j))
      = Quotient.mk _ (inflatePiObj R i' P') := hEq
  obtain ⟨iso⟩ := Quotient.exact hEq'
  haveI : Simple P.obj := P.property
  haveI : Simple P'.obj := P'.property
  haveI hsP : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
  haveI hsP' : IsSimpleModule (R i') (P'.obj : ModuleCat.{u} (R i')) := isSimpleModule_of_simple _
  letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) := Module.compHom _ (Pi.evalRingHom R i)
  letI : Module (∀ j, R j) (P'.obj : ModuleCat.{u} (R i')) :=
    Module.compHom _ (Pi.evalRingHom R i')
  have φ : (P.obj : ModuleCat.{u} (R i)) ≃ₗ[∀ j, R j] (P'.obj : ModuleCat.{u} (R i')) :=
    ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
  have hii : i = i' := by
    by_contra hne
    have hsrc : ∀ p : (P.obj : ModuleCat.{u} (R i)),
        (Pi.single i (1 : R i) : ∀ j, R j) • p = p := by
      intro p
      change (Pi.single i (1 : R i)) i • p = p
      rw [Pi.single_eq_same, one_smul]
    have htgt : ∀ q : (P'.obj : ModuleCat.{u} (R i')),
        (Pi.single i (1 : R i) : ∀ j, R j) • q = 0 := by
      intro q
      change (Pi.single i (1 : R i)) i' • q = 0
      rw [Pi.single_eq_of_ne (Ne.symm hne), zero_smul]
    haveI : Nontrivial (P.obj : ModuleCat.{u} (R i)) := IsSimpleModule.nontrivial (R i) _
    obtain ⟨p, hp⟩ := exists_ne (0 : (P.obj : ModuleCat.{u} (R i)))
    have hz : φ p = 0 := by
      have hmap := φ.map_smul (Pi.single i (1 : R i)) p
      rw [hsrc p] at hmap
      rw [htgt (φ p)] at hmap
      exact hmap
    exact hp (φ.injective (hz.trans (map_zero φ).symm))
  subst hii
  refine congrArg (Sigma.mk i) (Quotient.sound ?_)
  refine ⟨(RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (R i))).fullyFaithfulι.preimageIso (LinearEquiv.toModuleIso
    { toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
      map_add' := φ.map_add,
      map_smul' := fun r p => by
        simp only [RingHom.id_apply]
        have h1 : (r : R i) • (p : (P.obj : ModuleCat.{u} (R i)))
            = (Pi.single i r : ∀ j, R j) • p := by
          change r • p = (Pi.single i r) i • p
          rw [Pi.single_eq_same]
        have h2 : (r : R i) • (φ p : (P'.obj : ModuleCat.{u} (R i)))
            = (Pi.single i r : ∀ j, R j) • φ p := by
          change r • φ p = (Pi.single i r) i • φ p
          rw [Pi.single_eq_same]
        rw [h1, h2, φ.map_smul] })⟩

private theorem sigmaToPi_surjective : Function.Surjective (sigmaToPi R) := by
  intro c
  induction c using Quotient.inductionOn with | _ M => ?_
  haveI : Simple M.obj := M.property
  haveI hsM : IsSimpleModule (∀ j, R j) (M.obj : ModuleCat.{u} (∀ j, R j)) :=
    isSimpleModule_of_simple _
  obtain ⟨i, hsupp⟩ := exists_support_index R (M.obj : ModuleCat.{u} (∀ j, R j))
  letI factor : Module (R i) (M.obj : ModuleCat.{u} (∀ j, R j)) :=
    { smul := fun r m => (Pi.single i r : ∀ j, R j) • m
      one_smul := fun m => hsupp m
      mul_smul := fun r r' m => by
        change (Pi.single i (r * r') : ∀ j, R j) • m
            = (Pi.single i r : ∀ j, R j) • ((Pi.single i r' : ∀ j, R j) • m)
        rw [← mul_smul]
        congr 1
        funext j
        rcases eq_or_ne i j with h | h
        · subst h; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne (Ne.symm h)]
      smul_zero := fun r => smul_zero _
      smul_add := fun r a b => smul_add _ _ _
      add_smul := fun r r' m => by
        change (Pi.single i (r + r') : ∀ j, R j) • m
            = (Pi.single i r : ∀ j, R j) • m + (Pi.single i r' : ∀ j, R j) • m
        rw [Pi.single_add, add_smul]
      zero_smul := fun m => by
        change (Pi.single i (0 : R i) : ∀ j, R j) • m = 0
        rw [Pi.single_zero, zero_smul] }
  have hrecover : ∀ (s : ∀ j, R j) (m : (M.obj : ModuleCat.{u} (∀ j, R j))),
      (Pi.single i (s i) : ∀ j, R j) • m = s • m := by
    intro s m
    have hs : (Pi.single i (s i) : ∀ j, R j) = s * Pi.single i (1 : R i) := by
      funext j
      rcases eq_or_ne i j with h | h
      · subst h; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne (Ne.symm h)]
    rw [hs, mul_smul, hsupp m]
  haveI hsFactor : letI := factor; IsSimpleModule (R i) (M.obj : ModuleCat.{u} (∀ j, R j)) := by
    letI := factor
    haveI : RingHomSurjective (Pi.evalRingHom R i) := ⟨fun x => ⟨Pi.single i x, by simp⟩⟩

    exact (LinearMap.isSimpleModule_iff_of_bijective
      (σ := Pi.evalRingHom R i)
      ({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun s m => (hrecover s m).symm } :
        (M.obj : ModuleCat.{u} (∀ j, R j)) →ₛₗ[Pi.evalRingHom R i]
          (M.obj : ModuleCat.{u} (∀ j, R j))) Function.bijective_id).mp hsM
  let P₀ : (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (R i))).FullSubcategory :=
    ⟨letI := factor; ModuleCat.of (R i) (M.obj : ModuleCat.{u} (∀ j, R j)),
     letI := factor; letI := hsFactor; simple_of_isSimpleModule⟩
  refine ⟨⟨i, Quotient.mk _ P₀⟩, ?_⟩
  have hiso := idModuleIso
    (Module.compHom (M.obj : ModuleCat.{u} (∀ j, R j)) (Pi.evalRingHom R i))
    M.obj.isModule
    (fun s m => by
      change (Pi.single i (s i) : ∀ j, R j) • m = s • m
      exact hrecover s m)
  exact Quotient.sound
    ⟨(RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (∀ j, R j))).fullyFaithfulι.preimageIso hiso⟩

private noncomputable def simpleModuleClassesPiEquiv :
    (Σ i, RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (R i)) ≃ RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (∀ j, R j) :=
  Equiv.ofBijective (sigmaToPi R) ⟨sigmaToPi_injective R, sigmaToPi_surjective R⟩

end Pi

/-- The auxiliary cardinality of a finite product equals the sum of the component cardinalities. -/
theorem auxiliaryCard_pi_eq_sum {n : ℕ} (R : Fin n → Type u) [∀ i, Ring (R i)]
    [∀ i, Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (R i))] :
    Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (∀ i, R i))
      = ∑ i, Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (R i)) := by
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (simpleModuleClassesPiEquiv R)).symm

/-- Scalar extension by a field does not decrease the cardinality of the auxiliary type. -/
theorem auxiliaryCard_le_tensorProduct_auxiliaryCard
    (k K : Type u) {A : Type u} [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A] :
    Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} A)
      ≤ Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (K ⊗[k] A)) := by
  classical
  obtain ⟨n, D, d, _, _, hDfin, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)

  have hDone : ∀ i, Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (D i)) = 1 := by
    intro i
    haveI := hDfin i
    have hne : Nonempty (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (D i)) := nonempty_auxiliaryType k
    have hss : Subsingleton (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (D i)) :=
      subsingleton_auxiliaryType_of_divisionRing (D i)
    exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩

  have hL : Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} A) = n := by
    haveI : ∀ i, Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
      intro i
      haveI : NeZero (d i) := hd i
      haveI : Subsingleton (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (D i)) :=
        subsingleton_auxiliaryType_of_divisionRing (D i)
      exact Finite.of_equiv _ (matrix_auxiliaryType_equiv (R := D i) (d i)).symm
    rw [Nat.card_congr (auxiliaryType_equiv_of_ringEquiv (e.toRingEquiv)),
      auxiliaryCard_pi_eq_sum]
    have : ∀ i, Nat.card
        (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin (d i)) (Fin (d i)) (D i))) = 1 := by
      intro i
      haveI : NeZero (d i) := hd i
      rw [Nat.card_congr (matrix_auxiliaryType_equiv (R := D i) (d i)), hDone i]
    simp [this]

  obtain ⟨f⟩ := RepresentationTheory.Algebra.TensorProduct.MatrixProductEquivalence.nonempty_tensorProduct_algEquiv_pi_matrix k K D d e
  haveI : ∀ i, Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
    intro i
    haveI : NeZero (d i) := hd i
    haveI := hDfin i
    haveI : Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (K ⊗[k] D i)) := RepresentationTheory.SimpleRepresentationModules.finite_auxiliaryRingType_of_module_finite K
    exact Finite.of_equiv _ (matrix_auxiliaryType_equiv (R := K ⊗[k] D i) (d i)).symm
  rw [Nat.card_congr (auxiliaryType_equiv_of_ringEquiv (f.toRingEquiv)),
    auxiliaryCard_pi_eq_sum, hL]

  have key : ∀ i, 1 ≤ Nat.card
      (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
    intro i
    haveI : NeZero (d i) := hd i
    haveI := hDfin i
    haveI : Module.Finite K (K ⊗[k] D i) := inferInstance
    rw [Nat.card_congr (matrix_auxiliaryType_equiv (R := K ⊗[k] D i) (d i))]
    have hne : Nonempty (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (K ⊗[k] D i)) :=
      nonempty_auxiliaryType K
    haveI : Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (K ⊗[k] D i)) :=
      RepresentationTheory.SimpleRepresentationModules.finite_auxiliaryRingType_of_module_finite K
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩)
  have hsum : ∑ _i : Fin n, 1 ≤ ∑ i, Nat.card
      (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) :=
    Finset.sum_le_sum fun i _ => key i
  simpa using hsum

end RepresentationTheory.RingTheory.AuxiliaryTypeInvariants
