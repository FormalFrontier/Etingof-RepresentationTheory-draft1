/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
import RepresentationTheory.MatrixPolynomialHomogeneity

noncomputable section

open MvPolynomial
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open scoped MonoidAlgebra

namespace RepresentationTheory.Submodules

section SimpleSubmodule

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A nonzero submodule that is finite-dimensional over the field contains a simple submodule. -/
theorem exists_isSimpleModule_submodule_le_of_finite (ρ : Representation k G V)
    (W : Submodule (MonoidAlgebra k G) ρ.asModule) [Module.Finite k W] (hW : W ≠ ⊥) :
    ∃ S : Submodule (MonoidAlgebra k G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra k G) S ∧ S ≤ W := by
  haveI : IsArtinian k W := inferInstance
  haveI : IsArtinian (MonoidAlgebra k G) W := isArtinian_of_tower k inferInstance
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  haveI : Nontrivial (Submodule (MonoidAlgebra k G) W) :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mpr inferInstance
  haveI : IsAtomic (Submodule (MonoidAlgebra k G) W) :=
    isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨b, hb⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra k G) W)
  haveI : IsSimpleModule (MonoidAlgebra k G) b := isSimpleModule_iff_isAtom.mpr hb
  refine ⟨b.map W.subtype, ?_, Submodule.map_subtype_le W b⟩
  exact IsSimpleModule.congr (M := ↥(b.map W.subtype)) (N := ↥b)
    (Submodule.equivMapOfInjective W.subtype Subtype.val_injective b).symm

end SimpleSubmodule

section Bridge

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The module of a subrepresentation's associated representation is linearly equivalent to its
underlying submodule. -/
def Subrepresentation.toRepresentationLinearEquivAsSubmodule
    (σ : Subrepresentation ρ) :
    (σ.toRepresentation).asModule ≃ₗ[MonoidAlgebra k G] σ.asSubmodule where
  toFun y := ⟨((σ.toRepresentation).asModuleEquiv y).1,
    ((σ.toRepresentation).asModuleEquiv y).2⟩
  map_add' y z := by
    apply Subtype.ext
    exact congrArg Subtype.val ((σ.toRepresentation).asModuleEquiv.map_add y z)
  map_smul' c y := by
    apply Subtype.ext
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
        change (0 : V) = 0
        rfl
    | add c₁ c₂ h₁ h₂ =>
        simp only [add_smul, RingHom.id_apply] at h₁ h₂ ⊢
        rw [Submodule.coe_add, ← h₁, ← h₂]; rfl
    | single g t =>
        simp only [RingHom.id_apply, SetLike.val_smul]
        rw [Representation.single_smul, Representation.single_smul]
        rfl
  invFun x := (σ.toRepresentation).asModuleEquiv.symm ⟨x.1, x.2⟩
  left_inv y := by simp
  right_inv x := by apply Subtype.ext; simp

/-- Simplicity of a subrepresentation as a submodule implies simplicity of its associated
representation module. -/
theorem isSimpleModule_toRepresentation_of_asSubmodule
    (σ : Subrepresentation ρ)
    (h : IsSimpleModule (MonoidAlgebra k G) σ.asSubmodule) :
    IsSimpleModule (MonoidAlgebra k G) (σ.toRepresentation).asModule :=
  IsSimpleModule.congr
    (Subrepresentation.toRepresentationLinearEquivAsSubmodule σ)

end Bridge

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.MatrixPolynomialHomogeneity

variable {k : Type*} [Field k] {N : ℕ}

/-- For every general-linear-group index, the displayed map carries each polynomial in the
total-degree-restricted collection to another member of that collection. -/
theorem generalLinearGroupIndexedMap_preserves_restrictTotalDegree
    (g : Matrix.GeneralLinearGroup (Fin N) k) (D : ℕ)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D) :
    generalLinearGroupMvPolynomialRightMul k N g f ∈
      MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D := by
  rw [MvPolynomial.mem_restrictTotalDegree] at hf
  have hsplit : generalLinearGroupMvPolynomialRightMul k N g f =
      ∑ d ∈ Finset.range (f.totalDegree + 1),
        generalLinearGroupMvPolynomialRightMul k N g
          (homogeneousComponent d f) := by
    rw [← map_sum]; congr 1; exact
      (MvPolynomial.sum_homogeneousComponent f).symm
  rw [hsplit]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.mem_restrictTotalDegree]
  refine le_trans
    (generalLinearAction_preserves_isHomogeneous g
      (MvPolynomial.homogeneousComponent_isHomogeneous d f)).totalDegree_le ?_
  simp only [Finset.mem_range] at hd
  omega

/-- A nonzero submodule satisfying the displayed closure condition contains the image of an
injective map from a simple module that intertwines the indicated group-indexed maps. -/
theorem exists_isSimpleModule_embedding_of_nonzero_submodule
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    {W : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸
      matrixIndexedPolynomialSubmodule k N)}
    (hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W, matrixPolynomialQuotientRepresentation k N g w ∈ W)
    (hW : W ≠ ⊥) :
    ∃ (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (φ : L →ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸
        matrixIndexedPolynomialSubmodule k N)),
      IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule L.ρ) ∧
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        φ (L.ρ g v) = matrixPolynomialQuotientRepresentation k N g (φ v)) ∧
      Set.range φ ⊆ (W : Set _) := by
  classical
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  set D := p.totalDegree with hD
  set Bsub : Submodule k (MvPolynomial (Fin N × Fin N) k) :=
    MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D with hBsub
  set Bq : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸
      matrixIndexedPolynomialSubmodule k N) :=
    Bsub.map (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)) with hBq
  have hBq_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Bq, matrixPolynomialQuotientRepresentation k N g x ∈ Bq := by
    rintro g _ ⟨f, hf, rfl⟩
    exact ⟨generalLinearGroupMvPolynomialRightMul k N g f,
      generalLinearGroupIndexedMap_preserves_restrictTotalDegree g D hf, by
        simp [matrixPolynomialQuotientRepresentation_apply_mk]⟩
  let Wr : Subrepresentation (matrixPolynomialQuotientRepresentation k N) :=
    ⟨W, fun g _ hx => hW_inv g _ hx⟩
  let Bqr : Subrepresentation (matrixPolynomialQuotientRepresentation k N) :=
    ⟨Bq, fun g _ hx => hBq_inv g _ hx⟩
  set M₀ : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (matrixPolynomialQuotientRepresentation k N).asModule :=
    (Wr ⊓ Bqr).asSubmodule with hM₀
  have hwBq : (Submodule.Quotient.mk p :
      MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) ∈
      Bq :=
    ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin N × Fin N) D p).mpr
      (le_of_eq hD.symm), rfl⟩
  have hwM₀ : (Submodule.Quotient.mk p :
      (matrixPolynomialQuotientRepresentation k N).asModule) ∈ M₀ :=
    ⟨hwW, hwBq⟩
  haveI : Module.Finite k (Wr ⊓ Bqr).toSubmodule := by
    rw [Subrepresentation.toSubmodule_inf]
    exact Module.Finite.of_injective
      (Submodule.inclusion
        (inf_le_right : Wr.toSubmodule ⊓ Bqr.toSubmodule ≤ Bqr.toSubmodule))
      (Submodule.inclusion_injective _)
  haveI : Module.Finite k M₀ :=
    Module.Finite.equiv
      ((Subrepresentation.toRepresentationLinearEquivAsSubmodule
        (Wr ⊓ Bqr)).restrictScalars k)
  have hM₀ne : M₀ ≠ ⊥ := by
    intro h
    apply hw0
    rw [h] at hwM₀
    change (Submodule.Quotient.mk p :
      (matrixPolynomialQuotientRepresentation k N).asModule) = 0 at hwM₀
    exact hwM₀
  obtain ⟨S, hSsimple, hSle⟩ :=
    exists_isSimpleModule_submodule_le_of_finite
      (matrixPolynomialQuotientRepresentation k N) M₀ hM₀ne
  set Sr : Subrepresentation (matrixPolynomialQuotientRepresentation k N) :=
    Subrepresentation.ofSubmodule' S with hSr
  have hSrAsSub : Sr.asSubmodule = S := rfl
  have hScarrier : ∀ x ∈ Sr.toSubmodule, x ∈ W := fun x hx => (hSle hx).1
  haveI : Module.Finite k Sr.toSubmodule := by
    have hle : Sr.toSubmodule ≤ (Wr ⊓ Bqr).toSubmodule := fun x hx => hSle hx
    exact Module.Finite.of_injective
      (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  refine ⟨FDRep.of Sr.toRepresentation, Sr.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · have hsimp : IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        Sr.asSubmodule := by
      rw [hSrAsSub]; exact hSsimple
    exact isSimpleModule_toRepresentation_of_asSubmodule Sr hsimp
  · exact Subtype.val_injective
  · intro g v; rfl
  · rintro _ ⟨v, rfl⟩
    exact hScarrier _ v.2

end RepresentationTheory.Submodules

end
