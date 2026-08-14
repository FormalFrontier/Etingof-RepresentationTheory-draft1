/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Centralizer.LinearMaps
import RepresentationTheory.TensorPower

open scoped TensorProduct

universe u

namespace RepresentationTheory.LinearAlgebra.EndomorphismCentralizer

open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.Centralizer.LinearMaps
open RepresentationTheory.CentralizerDecomposition
open RepresentationTheory.TensorPower

variable {k : Type u} [Field k]

noncomputable local instance (priority := high) subalgebraCarrierRing
    {E : Type u} [AddCommGroup E] [Module k E]
    (A : Subalgebra k (Module.End k E)) : Ring A :=
  A.toRing

noncomputable local instance (priority := high) centralizerModuleSubmoduleHom
    {E : Type u} [AddCommGroup E] [Module k E] [Module.Finite k E]
    (A : Subalgebra k (Module.End k E)) (V : Submodule A E) :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) (↥V →ₗ[A] E) :=
  centralizerModuleHom k E (A := A) (V := ↥V)

noncomputable local instance (priority := high) permutationSubmoduleAddCommGroup
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (S : Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n)) :
    AddCommGroup S :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := S.addCommMonoid }

section

variable {V : Type u} [AddCommGroup V] [Module k V]

set_option synthInstance.maxHeartbeats 400000 in
-- Heartbeats increased because centralizer membership requires extended instance synthesis.
/-- Associates an invertible module endomorphism and a natural number with an element of the
relevant centralizer. -/
noncomputable def unitEndomorphismCentralizerElement [Module.Finite k V]
    (g : (Module.End k V)ˣ) (n : ℕ) :
    ↥(Subalgebra.centralizer k
      (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n)))) :=
  ⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
    auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra k V n
      (Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩)⟩

set_option maxHeartbeats 6400000 in
-- Heartbeats increased because centralizer actions require extended elaboration.
set_option synthInstance.maxHeartbeats 3200000 in
/-- An equivalence of linear-map spaces that is equivariant for invertible endomorphisms preserves
scalar multiplication by centralizer elements. -/
theorem LinearEquiv.map_smul_of_unit_equivariant
    [Module.Finite k V] [Infinite k] [CharZero k] {n : ℕ}
    {S W : Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n)}
    (ψ : (↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) ≃ₗ[k]
        (↥W →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n))
    (h_int : ∀ (g : (Module.End k V)ˣ)
        (l : ↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
        ψ (unitEndomorphismCentralizerElement g n • l) =
          unitEndomorphismCentralizerElement g n • ψ l)
    (c : ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n)))))
    (l : ↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :
    ψ (c • l) = c • ψ l := by
  classical
  obtain ⟨cval, hcmem⟩ := c
  set C := Subalgebra.centralizer k
    (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n))) with hC
  haveI hstS : IsScalarTower k (↥C)
      (↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :=
    ⟨fun a c f => by
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)⟩
  haveI hstW : IsScalarTower k (↥C)
      (↥W →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :=
    ⟨fun a c f => by
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)⟩
  have hCeq : C = Algebra.adjoin k (Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
    rw [hC, centralizer_permutationActionAlgebra k V n,
      ← adjoin_piTensorProductMaps_eq_auxiliary k (V := V) n]
  have hgen : cval ∈ Algebra.adjoin k
      (Set.range fun (g : (Module.End k V)ˣ) =>
        PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
    rw [← hCeq]; exact hcmem
  refine Algebra.adjoin_induction
    (s := Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)))
    (p := fun x _ => ∀ (hx : x ∈ C)
        (l : ↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
        ψ ((⟨x, hx⟩ : ↥C) • l) = (⟨x, hx⟩ : ↥C) • ψ l)
    ?_ ?_ ?_ ?_ hgen hcmem l
  · rintro x ⟨g, rfl⟩ hx l
    exact h_int g l
  · intro r hx l
    have e1 : (⟨algebraMap k (Module.End k (auxiliarySpace k V n)) r, hx⟩ : ↥C) • l =
        r • l := by
      rw [show (⟨algebraMap k (Module.End k (auxiliarySpace k V n)) r, hx⟩ : ↥C) =
          algebraMap k (↥C) r from rfl,
        Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    have e2 : (⟨algebraMap k (Module.End k (auxiliarySpace k V n)) r, hx⟩ : ↥C) • ψ l =
        r • ψ l := by
      rw [show (⟨algebraMap k (Module.End k (auxiliarySpace k V n)) r, hx⟩ : ↥C) =
          algebraMap k (↥C) r from rfl,
        Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [e1, e2, map_smul]
  · rintro x y hx_adj hy_adj ihx ihy hxy l
    have hxC : x ∈ C := hCeq ▸ hx_adj
    have hyC : y ∈ C := hCeq ▸ hy_adj
    rw [show (⟨x + y, hxy⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) + (⟨y, hyC⟩ : ↥C) from rfl,
      add_smul, map_add, ihx hxC l, ihy hyC l, add_smul]
  · rintro x y hx_adj hy_adj ihx ihy hxy l
    have hxC : x ∈ C := hCeq ▸ hx_adj
    have hyC : y ∈ C := hCeq ▸ hy_adj
    rw [show (⟨x * y, hxy⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) * (⟨y, hyC⟩ : ↥C) from rfl,
      mul_smul, ihx hxC ((⟨y, hyC⟩ : ↥C) • l), ihy hyC l, mul_smul]

set_option maxHeartbeats 6400000 in
-- Heartbeats increased because packaging the centralizer equivalence requires extended elaboration.
set_option synthInstance.maxHeartbeats 3200000 in
/-- Reinterprets an equivalence of linear-map spaces that commutes with invertible endomorphisms as
an equivalence linear over the centralizer. -/
noncomputable def LinearEquiv.restrictScalarsToCentralizer
    [Module.Finite k V] [Infinite k] [CharZero k] {n : ℕ}
    {S W : Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n)}
    (ψ : (↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) ≃ₗ[k]
        (↥W →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n))
    (h_int : ∀ (g : (Module.End k V)ˣ)
        (l : ↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
        ψ (unitEndomorphismCentralizerElement g n • l) =
          unitEndomorphismCentralizerElement g n • ψ l) :
    (↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) ≃ₗ[
      ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n))))]
      (↥W →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) where
  toFun := ψ
  invFun := ψ.symm
  map_add' := ψ.map_add
  map_smul' c l := LinearEquiv.map_smul_of_unit_equivariant ψ h_int c l
  left_inv := ψ.left_inv
  right_inv := ψ.right_inv

set_option maxHeartbeats 6400000 in
-- Heartbeats increased because resolving the centralizer action requires extended elaboration.
set_option synthInstance.maxHeartbeats 3200000 in
/-- The action of the centralizer element supplied for an invertible endomorphism equals
composition with the linear map obtained from that element. -/
theorem unitEndomorphismCentralizerElement_smul_eq_comp
    [Module.Finite k V] {n : ℕ}
    {S : Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n)}
    (g : (Module.End k V)ˣ)
    (f : ↥S →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :
    unitEndomorphismCentralizerElement g n • f =
      (centralizerToModuleEnd k (auxiliarySpace k V n) (permutationActionAlgebra k V n)
        (unitEndomorphismCentralizerElement g n)).comp f := rfl

end

section

variable [IsAlgClosed k] [CharZero k]

omit [IsAlgClosed k] [CharZero k] in
/-- Every invertible endomorphism of a finite coordinate space is induced by multiplication by an
invertible matrix. -/
theorem exists_matrixUnit_mulVecLin_eq {N : ℕ}
    (g : (Module.End k (Fin N → k))ˣ) :
    ∃ h : Matrix.GeneralLinearGroup (Fin N) k,
      Matrix.mulVecLin (R := k) (h : Matrix (Fin N) (Fin N) k) =
        (g : Module.End k (Fin N → k)) := by
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩
  rw [← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]

set_option maxHeartbeats 6400000 in
-- Heartbeats increased because the representation and centralizer instance chains are deep.
set_option synthInstance.maxHeartbeats 3200000 in
/-- Representations identified equivariantly with pairwise inequivalent indexed simple submodules
are pairwise nonisomorphic. -/
theorem pairwise_not_iso_of_submodule_equiv
    (N n : ℕ)
    {ι : Type}
    (S' : ι → Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    (hS'_simp : ∀ i, IsSimpleModule (permutationActionAlgebra k (Fin N → k) n) (S' i))
    (hS'_dist : ∀ i j,
      Nonempty (↥(S' i) ≃ₗ[permutationActionAlgebra k (Fin N → k) n] ↥(S' j)) → i = j)
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
      (↥(S' i) →ₗ[permutationActionAlgebra k (Fin N → k) n]
        auxiliarySpace k (Fin N → k) n))
    (h_act : ∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k)
        (l : (L i : Type u)) (v : ↥(S' i)),
        (L_carrier i ((L i).ρ g l)) v =
          PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
            ((L_carrier i l) v)) :
    Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))) := by
  classical
  haveI : FaithfulSMul (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n) :=
    faithfulSMul_permutationActionAlgebra_auxiliarySpace k (Fin N → k) n
  intro i j hij
  rintro ⟨f⟩
  apply hij
  set φ : (L i : Type u) ≃ₗ[k] (L j : Type u) := FDRep.isoToLinearEquiv f with hφdef
  have hφ : ∀ (h : Matrix.GeneralLinearGroup (Fin N) k) (x : (L i : Type u)),
      φ ((L i).ρ h x) = (L j).ρ h (φ x) := by
    intro h x
    have hc := FDRep.Iso.conj_ρ f h
    have hconj : (FDRep.isoToLinearEquiv f).conj ((L i).ρ h) (φ x) =
        φ ((L i).ρ h x) := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      change φ (((L i).ρ h) (φ.symm (φ x))) = φ (((L i).ρ h) x)
      rw [φ.symm_apply_apply]
    rw [← hconj, hc]
  set ψ : (↥(S' i) →ₗ[permutationActionAlgebra k (Fin N → k) n]
      auxiliarySpace k (Fin N → k) n) ≃ₗ[k]
      (↥(S' j) →ₗ[permutationActionAlgebra k (Fin N → k) n]
        auxiliarySpace k (Fin N → k) n) :=
    (L_carrier i).symm.trans (φ.trans (L_carrier j)) with hψdef
  refine hS'_dist i j (@Subalgebra.centralizer.linearMapEquiv_implies_linearEquiv k _
    (auxiliarySpace k (Fin N → k) n) _ _ _
    (permutationActionAlgebra k (Fin N → k) n) _ _ _ (S' i) (S' j)
    (hS'_simp i) (hS'_simp j) ⟨LinearEquiv.restrictScalarsToCentralizer ψ ?_⟩)
  intro g l
  obtain ⟨h, hgh⟩ := exists_matrixUnit_mulVecLin_eq g
  have hrel : ∀ (m : ι) (y : (L m : Type u)),
      (centralizerToModuleEnd k (auxiliarySpace k (Fin N → k) n)
          (permutationActionAlgebra k (Fin N → k) n)
          (unitEndomorphismCentralizerElement g n)).comp (L_carrier m y) =
        L_carrier m ((L m).ρ h y) := by
    intro m y
    refine LinearMap.ext fun v => ?_
    rw [h_act m h y v]
    change PiTensorProduct.map (R := k)
          (fun _ : Fin n => (g : Module.End k (Fin N → k))) ((L_carrier m y) v) =
        PiTensorProduct.map (R := k)
          (fun _ : Fin n => Matrix.mulVecLin (R := k) (h : Matrix (Fin N) (Fin N) k))
          ((L_carrier m y) v)
    rw [show (fun _ : Fin n => Matrix.mulVecLin (R := k)
        (h : Matrix (Fin N) (Fin N) k)) =
        (fun _ : Fin n => (g : Module.End k (Fin N → k))) from funext fun _ => hgh]
  simp only [unitEndomorphismCentralizerElement_smul_eq_comp, hψdef,
    LinearEquiv.trans_apply]
  have e1 : (L_carrier i).symm
        ((centralizerToModuleEnd k (auxiliarySpace k (Fin N → k) n)
            (permutationActionAlgebra k (Fin N → k) n)
            (unitEndomorphismCentralizerElement g n)).comp l) =
      (L i).ρ h ((L_carrier i).symm l) := by
    apply (L_carrier i).injective
    rw [LinearEquiv.apply_symm_apply, ← hrel i ((L_carrier i).symm l),
      LinearEquiv.apply_symm_apply]
  rw [e1, hφ h ((L_carrier i).symm l), ← hrel j (φ ((L_carrier i).symm l))]

end

end RepresentationTheory.LinearAlgebra.EndomorphismCentralizer
