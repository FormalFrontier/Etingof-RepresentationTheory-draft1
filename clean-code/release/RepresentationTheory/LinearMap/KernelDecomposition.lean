/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.BigradedComponents
import RepresentationTheory.Alignment.Attribute

/-! # Kernel decomposition -/

namespace RepresentationTheory.LinearMap.KernelDecomposition

section Kernel

variable {k : Type*} [Field k]

/-- Every auxiliary-family element is mapped to zero. -/
theorem map_auxFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m) = 0 :=
  _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_eq_zero_of_forall_bracket_eq_zero
    h3
    (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracket_auxiliaryCentralFamily_eq_zero
      h2 h3 h5 m)

/-- The span of the auxiliary family is contained in the kernel. -/
theorem auxFamilySpan_le_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    Submodule.span k
      (Set.range
        (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k)) ≤
      LinearMap.ker
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) := by
  rw [Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact LinearMap.mem_ker.2 (map_auxFamily_eq_zero h2 h3 h5 m)

/-- The span of the displayed generator family is disjoint from the kernel of the linear map. -/
theorem generatorSpan_disjoint_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    Disjoint
      (Submodule.span k
        (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)))
      (LinearMap.ker
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) :=
  Submodule.range_ker_disjoint
    (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.linearIndependent_realizationMap_indexedFamily
      h2 h3)

/-- An element lying in both the generator span and the kernel is zero. -/
theorem eq_zero_of_mem_generatorSpan_and_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hspan : u ∈ Submodule.span k
      (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)))
    (hker : u ∈ LinearMap.ker
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) : u = 0 :=
  Submodule.disjoint_def.1 (generatorSpan_disjoint_ker h2 h3) u hspan hker

/-- The two displayed family spans together generate the whole space. -/
theorem generatorSpan_sup_auxFamilySpan_eq_top (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) :
    Submodule.span k
        (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)) ⊔
      Submodule.span k
        (Set.range
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k)) = ⊤ := by
  rw [← Submodule.span_union]
  exact
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.span_auxiliarySpanningSet_eq_top
      h2 h3 h5

/-- Identifies the kernel with the span of the auxiliary family. -/
theorem ker_eq_auxFamily_span (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    LinearMap.ker
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) =
      Submodule.span k
        (Set.range
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k)) := by
  refine le_antisymm (fun u hu => ?_) (auxFamilySpan_le_ker h2 h3 h5)
  have hdec : u ∈ Submodule.span k
        (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)) ⊔
      Submodule.span k
        (Set.range
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k)) := by
    rw [generatorSpan_sup_auxFamilySpan_eq_top h2 h3 h5]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hdec
  have hbker : b ∈ LinearMap.ker
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) :=
    auxFamilySpan_le_ker h2 h3 h5 hb
  have haker : a ∈ LinearMap.ker
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) := by
    rw [LinearMap.mem_ker] at hu hbker ⊢
    rw [map_add, hbker, add_zero] at hu
    exact hu
  rw [eq_zero_of_mem_generatorSpan_and_ker h2 h3 ha haker, zero_add]
  exact hb

/-- The linear map is injective exactly when every element of the auxiliary family vanishes. -/
theorem injective_iff_auxFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) :
    Function.Injective
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) ↔
      ∀ m : ℕ,
        _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0 := by
  refine
    ⟨_root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryFamily_eq_zero
      h2 h3 h5, fun hgap => ?_⟩
  rw [← LinearMap.ker_eq_bot, ker_eq_auxFamily_span h2 h3 h5, Submodule.span_eq_bot]
  rintro _ ⟨m, rfl⟩
  exact hgap m

/-- An element in the kernel has zero bracket with every element. -/
theorem mem_ker_implies_bracket_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hu : u ∈ LinearMap.ker
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k))
    (v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    ⁅v, u⁆ = 0 := by
  rw [ker_eq_auxFamily_span h2 h3 h5] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact
        _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracket_auxiliaryCentralFamily_eq_zero
          h2 h3 h5 m v
  | zero => exact _root_.lie_zero v
  | add x y _ _ hx hy => rw [lie_add, hx, hy, add_zero]
  | smul c x _ hx => rw [lie_smul, hx, smul_zero]

/-- The kernel intersects the specified indexed component only in bottom under the displayed index condition. -/
theorem ker_inf_component_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    (hp : ∀ m : ℕ, p ≠ (2 * m + 2, 4 * m + 4)) :
    LinearMap.ker
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) ⊓
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p = ⊥ := by
  refine le_antisymm (fun u hu => ?_) bot_le
  obtain ⟨hker, hdeg⟩ := Submodule.mem_inf.1 hu
  refine (Submodule.mem_bot k).2 ?_
  by_cases hI : ∃ I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex,
      I.bideg = p
  · obtain ⟨I, rfl⟩ := hI
    have hle :=
      _root_.RepresentationTheory.LieAlgebra.BigradedComponents.component_le_span_singleton
        h2 h3 h5 I fun m => Ne.symm (hp m)
    have hsub :
        ({_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I} :
          Set (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4)) ⊆
          Set.range
            (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k) :=
      Set.singleton_subset_iff.2 ⟨I, rfl⟩
    exact eq_zero_of_mem_generatorSpan_and_ker h2 h3
      (Submodule.span_mono hsub (hle hdeg)) hker
  · have hbot :
        _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p = ⊥ :=
      _root_.RepresentationTheory.LieAlgebra.BigradedComponents.component_eq_bot_of_unclassified_bidegree
        h2 h3 h5 p (fun I hIp => hI ⟨I, hIp⟩) fun m hm => hp m hm.symm
    rw [hbot] at hdeg
    exact (Submodule.mem_bot k).1 hdeg

end Kernel

end RepresentationTheory.LinearMap.KernelDecomposition
