/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.Alignment.Attribute

/-!
# Submodules associated with partitions
-/

namespace RepresentationTheory.SymmetricGroup.PartitionSubmodules

/-- Associates a submodule of the ambient module to each partition of a natural number. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
noncomputable def partitionSubmodule (n : ℕ) (la : Nat.Partition n) :
    Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      (RepresentationTheory.PartitionAuxiliary.natIndexedType n) :=
  Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    {RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la}

/-- For every partition, there is a function compatible with the action of each finite
permutation. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem exists_equivariantMap (n : ℕ) (la : Nat.Partition n) :
    ∃ e : ↥(partitionSubmodule n la) ≃ₗ[ℂ]
        ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la),
      ∀ (g : Equiv.Perm (Fin n)) (x : ↥(partitionSubmodule n la)),
        e ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • x) =
          (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • e x := by
  classical
  obtain ⟨α, hα⟩ :=
    RepresentationTheory.Partitions.SquareScalar.exists_mul_self_eq_smul n la
  obtain ⟨ℓ, hℓ⟩ :=
    RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_fixed_sign_sandwich_eq_smul_mul
      n la
  have hsq := RepresentationTheory.PartitionAuxiliary.self_mul_ne_zero n la
  set a :=
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB
      n la with ha_def
  set b :=
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA
      n la with hb_def
  have hY :
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC
        n la = b * a := rfl
  rw [hY] at hα hsq
  have hα_ne : α ≠ 0 := fun h => hsq (by rw [hα, h, zero_smul])
  have hbne : b * a ≠ 0 := fun h => hsq (by rw [h, mul_zero])
  have hd2 : (a * b) * (a * b) = ℓ (b * a) • (a * b) := by
    have h := hℓ (b * a)
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = ℓ (b * a) • (a * b) := h
  have hβα : ℓ (b * a) = α := by
    have cube1 : b * ((a * b) * (a * b)) * a = (α * α) • (b * a) := by
      have e : b * ((a * b) * (a * b)) * a = ((b * a) * (b * a)) * (b * a) := by
        simp only [mul_assoc]
      rw [e, hα, smul_mul_assoc, hα, smul_smul]
    have cube2 : b * ((a * b) * (a * b)) * a = (ℓ (b * a) * α) • (b * a) := by
      rw [hd2, mul_smul_comm, smul_mul_assoc]
      have e2 : b * (a * b) * a = (b * a) * (b * a) := by simp only [mul_assoc]
      rw [e2, hα, smul_smul]
    have hαβ : (α * α) • (b * a) = (ℓ (b * a) * α) • (b * a) := by
      rw [← cube1, cube2]
    have hzero :
        (α * α - ℓ (b * a) * α) • (b * a) =
          (0 : RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
      rw [sub_smul, hαβ, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact (mul_right_cancel₀ hα_ne (sub_eq_zero.mp h)).symm
    · exact absurd h hbne
  rw [hβα] at hd2
  have hRC : partitionSubmodule n la =
      Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {a * b} := by
    simp only [partitionSubmodule, ← ha_def, ← hb_def]
  have hSM : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la =
      Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {b * a} := by
    simp only [RepresentationTheory.PartitionAuxiliary.partitionSubmodule, hY]
  let Fa : RepresentationTheory.PartitionAuxiliary.natIndexedType n
      →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
    { toFun := fun x => x * a
      map_add' := fun x y => add_mul x y a
      map_smul' := fun s x => by simp only [RingHom.id_apply, smul_eq_mul, mul_assoc] }
  let Gb : RepresentationTheory.PartitionAuxiliary.natIndexedType n
      →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
    { toFun := fun x => x * b
      map_add' := fun x y => add_mul x y b
      map_smul' := fun s x => by simp only [RingHom.id_apply, smul_eq_mul, mul_assoc] }
  have hFa_maps : ∀ x ∈ partitionSubmodule n la,
      Fa x ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la := by
    intro x hx
    rw [hRC, Submodule.mem_span_singleton] at hx
    obtain ⟨r, hr⟩ := hx
    rw [hSM, Submodule.mem_span_singleton]
    refine ⟨r * a, ?_⟩
    change (r * a) • (b * a) = x * a
    rw [← hr]; simp only [smul_eq_mul, mul_assoc]
  have hGb_maps : ∀ y ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la,
      Gb y ∈ partitionSubmodule n la := by
    intro y hy
    rw [hSM, Submodule.mem_span_singleton] at hy
    obtain ⟨s, hs⟩ := hy
    rw [hRC, Submodule.mem_span_singleton]
    refine ⟨s * b, ?_⟩
    change (s * b) • (a * b) = y * b
    rw [← hs]; simp only [smul_eq_mul, mul_assoc]
  let F : ↥(partitionSubmodule n la)
      →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
    Fa.restrict hFa_maps
  let G : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)
      →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(partitionSubmodule n la) :=
    Gb.restrict hGb_maps
  have hGF : ∀ x : ↥(partitionSubmodule n la), G (F x) = α • x := by
    intro x
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    change (x.val * a) * b = α • x.val
    have hx : (x : RepresentationTheory.PartitionAuxiliary.natIndexedType n) ∈
        Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {a * b} := by
      rw [← hRC]; exact x.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hr]; simp only [smul_eq_mul]
    rw [show (r * (a * b)) * a * b = r * ((a * b) * (a * b)) by simp only [mul_assoc],
      hd2, mul_smul_comm]
  have hFG : ∀ y : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la),
      F (G y) = α • y := by
    intro y
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    change (y.val * b) * a = α • y.val
    have hy : (y : RepresentationTheory.PartitionAuxiliary.natIndexedType n) ∈
        Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {b * a} := by
      rw [← hSM]; exact y.property
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
    rw [← hs]; simp only [smul_eq_mul]
    rw [show (s * (b * a)) * b * a = s * ((b * a) * (b * a)) by simp only [mul_assoc],
      hα, mul_smul_comm]
  let Fℂ : ↥(partitionSubmodule n la) →ₗ[ℂ]
      ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
    F.restrictScalars ℂ
  have hinj : Function.Injective Fℂ := by
    intro x y hxy
    have h1 : G (F x) = G (F y) := by rw [show F x = F y from hxy]
    rw [hGF, hGF] at h1
    have h2 : α⁻¹ • (α • x) = α⁻¹ • (α • y) := by rw [h1]
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ hα_ne, one_smul, one_smul] at h2
  have hsurj : Function.Surjective Fℂ := by
    intro y
    refine ⟨α⁻¹ • G y, ?_⟩
    have h1 : Fℂ (α⁻¹ • G y) = α⁻¹ • (α • y) := by
      rw [map_smul, show Fℂ (G y) = α • y from hFG y]
    rw [h1, smul_smul, inv_mul_cancel₀ hα_ne, one_smul]
  refine ⟨LinearEquiv.ofBijective Fℂ ⟨hinj, hsurj⟩, ?_⟩
  intro g x
  exact F.map_smul (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) x

end RepresentationTheory.SymmetricGroup.PartitionSubmodules
