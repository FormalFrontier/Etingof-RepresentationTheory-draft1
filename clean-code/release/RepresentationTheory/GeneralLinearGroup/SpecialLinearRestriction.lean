/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryModuleData
import RepresentationTheory.GeneralLinearGroup.ExteriorPower
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.AuxiliaryRepresentationParameters
import RepresentationTheory.AsModuleEquivalences
import RepresentationTheory.Alignment.Attribute

/-! # Restricting general linear representations to the special linear group -/

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false


namespace RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex

variable {n : ℕ}

/-- Shift every component by the given integer constant. -/
def constShift (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c : ℤ) : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n :=
  ⟨fun i => lam.val i + c, fun _ _ h => by dsimp only; have := lam.property h; omega⟩

/-- A constant shift adds the constant to each component. -/
@[simp] lemma constShift_apply (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c : ℤ) (i : Fin n) :
    (lam.constShift c).val i = lam.val i + c := rfl

/-- Shifting by zero leaves an element unchanged. -/
@[simp] lemma constShift_zero (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) : lam.constShift 0 = lam := by
  apply Subtype.ext; funext i; simp

/-- Successive constant shifts combine by addition. -/
lemma constShift_add (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c d : ℤ) :
    (lam.constShift c).constShift d = lam.constShift (c + d) := by
  apply Subtype.ext; funext i; simp [add_assoc]

/-- The integer total associated to an element. -/
def total (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) : ℤ := ∑ i, lam.val i

/-- A constant shift changes the total by the rank times the shift. -/
@[simp] lemma total_constShift (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c : ℤ) :
    (lam.constShift c).total = lam.total + n * c := by
  simp only [total, constShift_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The relation between two elements that differ by a constant shift. -/
def ShiftEquiv (lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) : Prop := ∃ c : ℤ, mu = lam.constShift c

/-- The setoid whose equivalence classes identify constant shifts. -/
def shiftSetoid (n : ℕ) : Setoid (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) where
  r := ShiftEquiv
  iseqv :=
    { refl := fun lam => ⟨0, (lam.constShift_zero).symm⟩
      symm := fun {lam mu} ⟨c, hc⟩ => ⟨-c, by
        apply Subtype.ext; funext i; subst hc; simp⟩
      trans := fun {lam mu nu} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by
        subst hc; subst hd; rw [constShift_add]⟩ }

/-- Two elements are related exactly when one is a constant shift of the other. -/
@[simp] lemma shiftSetoid_rel (lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    (shiftSetoid n).r lam mu ↔ ∃ c : ℤ, mu = lam.constShift c := Iff.rfl

end RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex

namespace RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction

/-- An auxiliary type family indexed by a natural number. -/
abbrev AuxiliaryType (n : ℕ) := Quotient (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.shiftSetoid n)

/-- The determinant of the underlying matrix of a special linear matrix is one. -/
lemma SpecialLinearGroup.det_coe {n : ℕ} {k : Type*} [CommRing k]
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (g : Matrix (Fin n) (Fin n) k).det = 1 :=
  g.property

private lemma toNatWeight_cast {n : ℕ} (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (i : Fin n) :
    (lam.toNatAt i : ℤ) = lam.val i + (lam.toNat : ℤ) := by
  have hnonneg : (0 : ℤ) ≤ lam.val i + (lam.toNat : ℤ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
    have hlast : lam.val (Fin.last m) ≤ lam.val i := lam.property (Fin.le_last i)
    change (0 : ℤ) ≤ lam.val i + (((-(lam.val (Fin.last m))).toNat : ℕ) : ℤ)
    omega
  change (((lam.val i + (lam.toNat : ℤ)).toNat : ℕ) : ℤ) = lam.val i + (lam.toNat : ℤ)
  rw [Int.toNat_of_nonneg hnonneg]

private lemma toNatWeight_antitone {n : ℕ} (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    Antitone lam.toNatAt := by
  intro i j hij
  simp only [RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.toNatAt]
  exact Int.toNat_le_toNat (by have := lam.property hij; omega)

private lemma finrank_schurModuleSubmodule_succ {N : ℕ} {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (μ : Fin N → ℕ) (hμ : Antitone μ) :
    Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N (fun i => μ i + 1))
      = Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N μ) := by
  obtain ⟨e⟩ := RepresentationTheory.GeneralLinearGroup.ExteriorPower.shiftedAuxiliarySubtypeRepresentationIsoNonempty k N μ hμ
  exact (FDRep.isoToLinearEquiv e).finrank_eq

private lemma finrank_schurModuleSubmodule_add_const {N : ℕ} {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (μ : Fin N → ℕ) (hμ : Antitone μ) (m : ℕ) :
    Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N (fun i => μ i + m))
      = Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N (fun i => μ i + (m + 1)))
        = Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N (fun i => μ i + m)) := by
      have hidx : (fun i => μ i + (m + 1)) = (fun i => (μ i + m) + 1) := by
        funext i; omega
      rw [hidx]
      exact finrank_schurModuleSubmodule_succ (fun j => μ j + m)
        (fun a b h => Nat.add_le_add_right (hμ h) m)
    rw [key, ih]

/-- Constant shifts preserve the finrank of the associated space. -/
theorem finrank_constShift
    {n : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c : ℤ) :
    Module.finrank k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n (lam.constShift c) k)
      = Module.finrank k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) := by
  change Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n (lam.constShift c).toNatAt)
    = Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt)
  have ha_anti : Antitone lam.toNatAt := toNatWeight_antitone lam
  have hb_anti : Antitone (lam.constShift c).toNatAt := toNatWeight_antitone (lam.constShift c)
  set Δ : ℤ := c + ((lam.constShift c).toNat : ℤ) - (lam.toNat : ℤ) with hΔdef
  have hrel : ∀ i, ((lam.constShift c).toNatAt i : ℤ) = (lam.toNatAt i : ℤ) + Δ := by
    intro i
    rw [toNatWeight_cast (lam.constShift c) i, toNatWeight_cast lam i,
      RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.constShift_apply, hΔdef]
    ring
  rcases le_total 0 Δ with hΔ | hΔ
  · have hbrw : (lam.constShift c).toNatAt = (fun i => lam.toNatAt i + Δ.toNat) := by
      funext i; have := hrel i; omega
    rw [hbrw]
    exact finrank_schurModuleSubmodule_add_const lam.toNatAt ha_anti Δ.toNat
  · have harw : lam.toNatAt = (fun i => (lam.constShift c).toNatAt i + (-Δ).toNat) := by
      funext i; have := hrel i; omega
    rw [harw]
    exact (finrank_schurModuleSubmodule_add_const (lam.constShift c).toNatAt hb_anti
      (-Δ).toNat).symm


section SLRestriction

variable {n : ℕ} {k : Type*} [CommRing k] {V : Type*} [AddCommMonoid V] [Module k V]

/-- Restrict a general linear group representation to the special linear group. -/
def Representation.restrictToSpecialLinear (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k) V :=
  MonoidHom.comp ρ Matrix.SpecialLinearGroup.toGL

/-- Restriction acts through the inclusion of the special linear group into the general linear group. -/
@[simp] lemma Representation.restrictToSpecialLinear_apply (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (g : Matrix.SpecialLinearGroup (Fin n) k) (v : V) :
    Representation.restrictToSpecialLinear ρ g v = ρ (Matrix.SpecialLinearGroup.toGL g) v := rfl

/-- The determinant character is one on a special linear matrix. -/
@[simp] lemma detCharacter_specialLinear (g : Matrix.SpecialLinearGroup (Fin n) k) :
    RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n (Matrix.SpecialLinearGroup.toGL g) = 1 :=
  Units.ext (by simp [RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits, Matrix.GeneralLinearGroup.det])

/-- Twisting by an integer power of the determinant character does not change the restricted representation. -/
lemma restrictToSpecialLinear_detCharacter_zpow (c : ℤ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V) :
    Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ c) ρ) = Representation.restrictToSpecialLinear ρ := by
  ext g v
  simp [MonoidHom.zpow_apply]

end SLRestriction

/-- Convert an isomorphism of finite-dimensional representations into an equivalence of representations. -/
noncomputable def FDRep.isoToRepresentationEquiv {K : Type} [Field K] {G : Type*} [Monoid G]
    {V W : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (α : FDRep.of ρ ≅ FDRep.of σ) : Representation.Equiv ρ σ :=
  Representation.Equiv.mk (FDRep.isoToLinearEquiv α) fun g => by
    have h := FDRep.Iso.conj_ρ α g
    rw [FDRep.of_ρ', FDRep.of_ρ'] at h
    rw [h, LinearEquiv.conj_apply]
    refine LinearMap.ext fun v => ?_
    simp

/-- Restrict an equivalence of general linear representations to the special linear group. -/
def Representation.Equiv.restrictToSpecialLinear {n : ℕ} {k : Type*} [CommRing k] {V W : Type*}
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V}
    {σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) W}
    (E : Representation.Equiv ρ σ) :
    Representation.Equiv (Representation.restrictToSpecialLinear ρ) (Representation.restrictToSpecialLinear σ) :=
  Representation.Equiv.mk E.toLinearEquiv fun g =>
    E.isIntertwining' (Matrix.SpecialLinearGroup.toGL g)


section SLEquiv

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

omit [IsAlgClosed k] [CharZero k] in
/-- Identifies an auxiliary representation with an associated determinant-character construction. -/
lemma auxiliaryRepresentation_eq (N : ℕ) (lam : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.ExteriorPower.auxiliarySubtypeRepresentation k N lam = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam) := rfl

omit [IsAlgClosed k] [CharZero k] in
/-- The restrictions of the two auxiliary associated representations are equal. -/
lemma restrictToSpecialLinear_auxiliary_eq (N : ℕ) (lam : Fin N → ℕ) :
    Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.ExteriorPower.auxiliarySubtypeRepresentation k N lam) = Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam) := by
  rw [auxiliaryRepresentation_eq, ← zpow_one (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N)]
  exact restrictToSpecialLinear_detCharacter_zpow 1 _

/-- Adding one to an antitone weight yields an equivalent restricted representation. -/
theorem restrictToSpecialLinear_succShift_equiv (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (Representation.Equiv (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N (fun i => lam i + 1)))
      (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam))) := by
  obtain ⟨e⟩ := RepresentationTheory.GeneralLinearGroup.ExteriorPower.shiftedAuxiliarySubtypeRepresentationIsoNonempty k N lam hlam
  refine ⟨?_⟩
  have E := Representation.Equiv.restrictToSpecialLinear (FDRep.isoToRepresentationEquiv _ _ e)
  rwa [restrictToSpecialLinear_auxiliary_eq N lam] at E

omit [IsAlgClosed k] [CharZero k] in
/-- Equal weights yield equivalent restricted representations. -/
theorem restrictToSpecialLinear_equiv_of_eq (N : ℕ) {lam mu : Fin N → ℕ} (h : lam = mu) :
    Nonempty (Representation.Equiv (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam))
      (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N mu))) := by
  subst h; exact ⟨Representation.Equiv.refl _⟩

/-- Adding a natural constant to an antitone weight yields an equivalent restricted representation. -/
theorem restrictToSpecialLinear_natShift_equiv (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (m : ℕ) :
    Nonempty (Representation.Equiv (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N (fun i => lam i + m)))
      (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam))) := by
  induction m with
  | zero =>
    exact restrictToSpecialLinear_equiv_of_eq (k := k) N
      (show (fun i => lam i + 0) = lam by funext i; omega)
  | succ m ih =>
    obtain ⟨E⟩ := ih
    obtain ⟨F⟩ := restrictToSpecialLinear_succShift_equiv (k := k) N (fun i => lam i + m)
      (fun a b h => Nat.add_le_add_right (hlam h) m)
    obtain ⟨G⟩ := restrictToSpecialLinear_equiv_of_eq (k := k) N
      (show (fun i => lam i + (m + 1)) = (fun i => (lam i + m) + 1) by funext i; omega)
    exact ⟨(G.trans F).trans E⟩

omit [CharZero k] in
/-- The restricted representation agrees with that associated to the natural weight. -/
lemma restrictToSpecialLinear_eq_natWeight {n : ℕ} (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) = Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lam.toNatAt) :=
  restrictToSpecialLinear_detCharacter_zpow _ _

/-- Constant shifts yield equivalent restricted representations. -/
@[source_ref "Chapter5/Remark5.23.3" (role := primary)]
theorem restrictToSpecialLinear_constShift_equiv {n : ℕ} (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (c : ℤ) :
    Nonempty (Representation.Equiv (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n (lam.constShift c) k))
      (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k))) := by
  rw [restrictToSpecialLinear_eq_natWeight, restrictToSpecialLinear_eq_natWeight]
  have ha_anti : Antitone lam.toNatAt := toNatWeight_antitone lam
  have hb_anti : Antitone (lam.constShift c).toNatAt := toNatWeight_antitone (lam.constShift c)
  set Δ : ℤ := c + ((lam.constShift c).toNat : ℤ) - (lam.toNat : ℤ) with hΔdef
  have hrel : ∀ i, ((lam.constShift c).toNatAt i : ℤ) = (lam.toNatAt i : ℤ) + Δ := by
    intro i
    rw [toNatWeight_cast (lam.constShift c) i, toNatWeight_cast lam i,
      RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.constShift_apply, hΔdef]
    ring
  rcases le_total 0 Δ with hΔ | hΔ
  · obtain ⟨G⟩ := restrictToSpecialLinear_equiv_of_eq (k := k) n
      (show (lam.constShift c).toNatAt = (fun i => lam.toNatAt i + Δ.toNat) by
        funext i; have := hrel i; omega)
    obtain ⟨E⟩ := restrictToSpecialLinear_natShift_equiv (k := k) n lam.toNatAt ha_anti Δ.toNat
    exact ⟨G.trans E⟩
  · obtain ⟨G⟩ := restrictToSpecialLinear_equiv_of_eq (k := k) n
      (show lam.toNatAt = (fun i => (lam.constShift c).toNatAt i + (-Δ).toNat) by
        funext i; have := hrel i; omega)
    obtain ⟨E⟩ := restrictToSpecialLinear_natShift_equiv (k := k) n (lam.constShift c).toNatAt hb_anti
      (-Δ).toNat
    exact ⟨(G.trans E).symm⟩

end SLEquiv


section SLParam

variable (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- The setoid on indexed elements induced by the associated representations. -/
def representationSetoid : Setoid (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) where
  r lam mu := Nonempty (Representation.Equiv (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k))
    (Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k)))
  iseqv :=
    { refl := fun _ => ⟨Representation.Equiv.refl _⟩
      symm := fun ⟨E⟩ => ⟨E.symm⟩
      trans := fun ⟨E⟩ ⟨F⟩ => ⟨E.trans F⟩ }

variable {n k}

/-- Constant-shift equivalence implies equivalence in the representation setoid. -/
theorem representationRelated_of_shiftEquiv {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n}
    (h : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.ShiftEquiv lam mu) : (representationSetoid n k).r lam mu := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨(restrictToSpecialLinear_constShift_equiv (k := k) lam c).some.symm⟩

variable (n k)

/-- The auxiliary map into the quotient by representation equivalence. -/
def auxiliaryQuotientMap : AuxiliaryType n → Quotient (representationSetoid n k) :=
  Quotient.map' id fun _ _ h => representationRelated_of_shiftEquiv h

/-- The auxiliary quotient map sends a shift class to its representation-equivalence class. -/
@[simp] lemma auxiliaryQuotientMap_mk (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    auxiliaryQuotientMap n k (Quotient.mk _ lam) = Quotient.mk _ lam := rfl

/-- The auxiliary quotient map is surjective. -/
theorem auxiliaryQuotientMap_surjective : Function.Surjective (auxiliaryQuotientMap n k) := by
  intro q
  induction q using Quotient.inductionOn with
  | h lam => exact ⟨Quotient.mk _ lam, rfl⟩

end SLParam


section Scalars

variable (k : Type*) [Field k] (n : ℕ)

/-- The invertible scalar matrix of a given rank. -/
def scalarMatrix (s : kˣ) : Matrix.GeneralLinearGroup (Fin n) k where
  val := (s : k) • (1 : Matrix (Fin n) (Fin n) k)
  inv := ((s⁻¹ : kˣ) : k) • (1 : Matrix (Fin n) (Fin n) k)
  val_inv := by simp [smul_smul]
  inv_val := by simp [smul_smul]

variable {k n}

/-- The underlying matrix of a scalar matrix is the scalar multiple of the identity. -/
@[simp] lemma coe_scalarMatrix (s : kˣ) :
    ((scalarMatrix k n s : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (s : k) • 1 := rfl

/-- The determinant character of a scalar matrix is the scalar raised to the rank. -/
@[simp] lemma detCharacter_scalarMatrix (s : kˣ) : RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n (scalarMatrix k n s) = s ^ n := by
  apply Units.ext
  change Matrix.det (scalarMatrix k n s).val = ((s ^ n : kˣ) : k)
  simp

/-- The determinant of a scalar matrix is the scalar raised to the rank. -/
lemma det_scalarMatrix (s : kˣ) :
    Matrix.GeneralLinearGroup.det (scalarMatrix k n s) = s ^ n := detCharacter_scalarMatrix s

/-- A scalar matrix whose rank-th power is one, regarded as a special linear matrix. -/
def scalarSpecialLinear (s : kˣ) (hs : (s : k) ^ n = 1) : Matrix.SpecialLinearGroup (Fin n) k :=
  ⟨(s : k) • 1, by simp [hs]⟩

/-- The general linear matrix underlying a scalar special linear matrix is the corresponding scalar matrix. -/
@[simp] lemma scalarSpecialLinear_toGL (s : kˣ) (hs : (s : k) ^ n = 1) :
    Matrix.SpecialLinearGroup.toGL (scalarSpecialLinear s hs) = scalarMatrix k n s := Units.ext rfl

/-- Every nonzero-rank general linear matrix over an algebraically closed field is a scalar matrix times a special linear matrix. -/
lemma exists_scalarMatrix_mul_specialLinear [IsAlgClosed k] (hn : n ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∃ (s : kˣ) (h : Matrix.SpecialLinearGroup (Fin n) k),
      g = scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
    ((g : Matrix (Fin n) (Fin n) k).det) (Nat.pos_of_ne_zero hn)
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn] at hx
    exact (Matrix.GeneralLinearGroup.det g).ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, ⟨((scalarMatrix k n (Units.mk0 x hx0))⁻¹ * g).val, ?_⟩, ?_⟩
  · -- The leftover factor has determinant `det g / s^N = 1`.
    have hdet : Matrix.GeneralLinearGroup.det ((scalarMatrix k n (Units.mk0 x hx0))⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, det_scalarMatrix, inv_mul_eq_one]
      exact Units.ext (by simpa using hx)
    exact congrArg Units.val hdet
  · apply Units.ext
    change (g : Matrix (Fin n) (Fin n) k)
        = (scalarMatrix k n (Units.mk0 x hx0)).val * ((scalarMatrix k n (Units.mk0 x hx0))⁻¹ * g).val
    rw [← Units.val_mul, mul_inv_cancel_left]

end Scalars

section ScalarAction

variable {k : Type*} [Field k] {n : ℕ}

/-- A scalar matrix acts on a homogeneous element by the corresponding power of the scalar. -/
lemma scalarMatrix_action_homogeneous (m : ℕ) (s : kˣ) (x : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin n → k) m) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k n m (scalarMatrix k n s) x = ((s : k) ^ m) • x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    change RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k n m (scalarMatrix k n s) (a • PiTensorProduct.tprod k v) = _
    rw [map_smul]
    change a • PiTensorProduct.map (fun _ : Fin m => Matrix.mulVecLin (scalarMatrix k n s).val)
      (PiTensorProduct.tprod k v) = _
    rw [PiTensorProduct.map_tprod]
    have hmv : ∀ i : Fin m,
        Matrix.mulVecLin (R := k) (scalarMatrix k n s).val (v i) = (s : k) • v i := by
      intro i
      change ((s : k) • (1 : Matrix (Fin n) (Fin n) k)).mulVec (v i) = (s : k) • v i
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [funext hmv, (PiTensorProduct.tprod k).map_smul_univ (fun _ : Fin m => (s : k)) v]
    simp [smul_smul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/--
A scalar matrix acts on the auxiliary subtype by the scalar raised to the sum of the indexed
weights.
-/
lemma scalarMatrix_action_auxiliarySubtype (a : Fin n → ℕ) (s : kˣ) (v : RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n a) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n a (scalarMatrix k n s) v = ((s : k) ^ (∑ i, a i)) • v := by
  apply Subtype.ext
  change RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k n (∑ i, a i) (scalarMatrix k n s) (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin n → k) (∑ i, a i))
    = ((s : k) ^ (∑ i, a i)) • (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin n → k) (∑ i, a i))
  exact scalarMatrix_action_homogeneous _ s _

variable [IsAlgClosed k]

private lemma sum_toNatWeight (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    ((∑ i, lam.toNatAt i : ℕ) : ℤ) = lam.total + n * (lam.toNat : ℤ) := by
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => toNatWeight_cast lam i)]
  simp only [RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.total, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- A scalar matrix acts by its scalar raised to the total. -/
lemma scalarMatrix_action (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (s : kˣ) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (scalarMatrix k n s) v = ((s ^ lam.total : kˣ) : k) • v := by
  have key : ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ))) (scalarMatrix k n s))
      * (s ^ (∑ i, lam.toNatAt i) : kˣ) = s ^ lam.total := by
    rw [MonoidHom.zpow_apply, detCharacter_scalarMatrix, ← zpow_natCast s (∑ i, lam.toNatAt i),
      ← zpow_natCast s n, ← zpow_mul, ← zpow_add]
    congr 1
    rw [sum_toNatWeight lam]
    ring
  change ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ))) (scalarMatrix k n s) : k) •
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lam.toNatAt (scalarMatrix k n s)
        (v : RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt)
      = ((s ^ lam.total : kˣ) : k) • (v : RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt)
  rw [scalarMatrix_action_auxiliarySubtype, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, key]

end ScalarAction

section SLNonIso

variable {n : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- The family at rank zero is a subsingleton. -/
instance rankZero_subsingleton : Subsingleton (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex 0) :=
  ⟨fun _ _ => Subtype.ext (funext fun i => i.elim0)⟩

omit [IsAlgClosed k] [CharZero k] in
private lemma equiv_apply_rho {G : Type*} [Monoid G] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (E : Representation.Equiv ρ σ)
    (g : G) (v : V) : E.toLinearEquiv (ρ g v) = σ g (E.toLinearEquiv v) :=
  LinearMap.ext_iff.mp (E.isIntertwining' g) v

/-- Related elements have totals whose difference is divisible by the rank. -/
theorem rank_dvd_total_sub_of_related {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n}
    (h : (representationSetoid n k).r lam mu) : (n : ℤ) ∣ mu.total - lam.total := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- No coordinates: both totals are the empty sum.
    simp [RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.total]
  obtain ⟨E⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  haveI : NeZero n := ⟨hn0⟩
  haveI : NeZero ((n : ℕ) : k) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  obtain ⟨u, huζ⟩ : ∃ u : kˣ, (u : k) = ζ := ⟨(hζ.isUnit hn0).unit, IsUnit.unit_spec _⟩
  have hζu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp (by rw [huζ]; exact hζ)
  have hun : (u : k) ^ n = 1 := by rw [huζ]; exact hζ.pow_eq_one
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp
    (RepresentationTheory.AuxiliaryModuleData.auxiliary_ne_bot_of_antitone (k := k) n lam.toNatAt lam.toNatWeight_antitone)
  have hvne : (⟨w, hwmem⟩ : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ≠ 0 :=
    fun hcon => hw0 (congrArg Subtype.val hcon)
  have hEne : E.toLinearEquiv (⟨w, hwmem⟩ : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ≠ 0 :=
    fun hcon => hvne (E.toLinearEquiv.map_eq_zero_iff.mp hcon)
  have hint := equiv_apply_rho E (scalarSpecialLinear u hun) (⟨w, hwmem⟩ : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
  simp only [Representation.restrictToSpecialLinear_apply, scalarSpecialLinear_toGL, scalarMatrix_action, map_smul] at hint
  have hscal : ((u ^ lam.total : kˣ) : k) = ((u ^ mu.total : kˣ) : k) := by
    by_contra hne
    apply hEne
    have hz := sub_eq_zero_of_eq hint
    rw [← sub_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero_of_ne hne)
  refine (hζu.zpow_eq_one_iff_dvd (mu.total - lam.total)).mp ?_
  rw [zpow_sub, show u ^ mu.total = u ^ lam.total from Units.ext hscal.symm, mul_inv_cancel]

omit [CharZero k] in
/-- A linear equivalence preserving equal totals and intertwining the special linear actions also intertwines the general linear actions. -/
theorem generalLinear_equivariant_of_specialLinear_equivariant {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n} (hn : n ≠ 0)
    (htot : lam.total = mu.total) (f : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n mu k)
    (hf : ∀ (h : Matrix.SpecialLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      f (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (Matrix.SpecialLinearGroup.toGL h) v)
        = RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k (Matrix.SpecialLinearGroup.toGL h) (f v))
    (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    f (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k g (f v) := by
  obtain ⟨s, h, rfl⟩ := exists_scalarMatrix_mul_specialLinear hn g
  rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply,
    scalarMatrix_action, map_smul, scalarMatrix_action, htot]
  exact congrArg _ (hf h v)

/-- Equivalence in the representation setoid implies constant-shift equivalence. -/
@[source_ref "Chapter5/Remark5.23.3" (role := supporting)]
theorem shiftEquiv_of_representationRelated {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n}
    (h : (representationSetoid n k).r lam mu) : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.ShiftEquiv lam mu := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨c, hc⟩ := rank_dvd_total_sub_of_related h
  refine ⟨c, ?_⟩
  set lam' : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n := lam.constShift c with hlam'
  have htot : lam'.total = mu.total := by
    rw [hlam', RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.total_constShift]; omega
  have hslam' : (representationSetoid n k).r lam' mu :=
    (representationSetoid n k).trans ((representationSetoid n k).symm (representationRelated_of_shiftEquiv ⟨c, rfl⟩)) h
  obtain ⟨E⟩ := hslam'
  have hiso : Nonempty ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam' k).asModule ≃ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)] (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k).asModule) :=
    ⟨RepresentationTheory.AsModuleEquivalences.linearEquivAsModule E.toLinearEquiv
      (generalLinear_equivariant_of_specialLinear_equivariant hn.ne' htot E.toLinearEquiv
        (fun g x => equiv_apply_rho E g x))⟩
  exact ((RepresentationTheory.AuxiliaryRepresentationParameters.auxiliaryRepresentation_linearEquiv_iff_parameters_eq n k).mp hiso).symm

variable (n k)

/-- The auxiliary quotient map is injective. -/
theorem auxiliaryQuotientMap_injective : Function.Injective (auxiliaryQuotientMap n k) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | h lam =>
    induction q using Quotient.inductionOn with
    | h mu =>
      exact Quotient.sound (shiftEquiv_of_representationRelated (k := k) (Quotient.exact hpq))

/-- The auxiliary quotient map is bijective. -/
theorem auxiliaryQuotientMap_bijective : Function.Bijective (auxiliaryQuotientMap n k) :=
  ⟨auxiliaryQuotientMap_injective n k, auxiliaryQuotientMap_surjective n k⟩

/-- An auxiliary equivalence with the quotient by representation equivalence. -/
@[source_ref "Chapter5/Remark5.23.3" (role := supporting)]
noncomputable def auxiliaryQuotientEquiv : AuxiliaryType n ≃ Quotient (representationSetoid n k) :=
  Equiv.ofBijective _ (auxiliaryQuotientMap_bijective n k)

/-- The auxiliary quotient equivalence sends a shift class to its representation-equivalence class. -/
@[simp] lemma auxiliaryQuotientEquiv_mk (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    auxiliaryQuotientEquiv n k (Quotient.mk _ lam) = Quotient.mk _ lam := rfl

end SLNonIso

end RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction
