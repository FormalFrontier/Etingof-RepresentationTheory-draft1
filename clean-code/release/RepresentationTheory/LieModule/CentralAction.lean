/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.FiniteDimensionalModules
import RepresentationTheory.Alignment.Attribute


/-! # Central actions on Lie modules -/

open RepresentationTheory.LieAlgebra.FiniteDimensionalModules
  RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices
  RepresentationTheory.LieAlgebra.Sl2Representations

namespace RepresentationTheory.LieModule.CentralAction

section Casimir

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]


/-- The distinguished complex-linear endomorphism of the module. -/
noncomputable def centralEndomorphism (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M] : Module.End ℂ M :=
  LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement
    + LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement
    + (2⁻¹ : ℂ) • (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement)


/-- Evaluates the distinguished endomorphism as the displayed combination of iterated actions. -/
theorem centralEndomorphism_apply (x : M) :
    centralEndomorphism M x = ⁅raisingElement, ⁅loweringElement, x⁆⁆ + ⁅loweringElement, ⁅raisingElement, x⁆⁆
      + (2⁻¹ : ℂ) • ⁅weightElement, ⁅weightElement, x⁆⁆ := by
  simp only [centralEndomorphism, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LieModule.toEnd_apply_apply]


/-- Computes the distinguished endomorphism on a vector satisfying the first pair of eigenvector conditions. -/
theorem centralEndomorphism_apply_eq_smul_of_firstEigenvector (μ : ℂ) (x : M) (hE : ⁅raisingElement, x⁆ = 0)
    (hH : ⁅weightElement, x⁆ = μ • x) :
    centralEndomorphism M x = ((μ * (μ + 2)) / 2) • x := by

  have hEF : ⁅raisingElement, ⁅loweringElement, x⁆⁆ = μ • x := by
    rw [leibniz_lie raisingElement loweringElement x, bracket_raising_lowering, hH, hE, lie_zero, add_zero]

  have hFE : ⁅loweringElement, ⁅raisingElement, x⁆⁆ = 0 := by rw [hE, lie_zero]

  have hHH : ⁅weightElement, ⁅weightElement, x⁆⁆ = (μ * μ) • x := by rw [hH, lie_smul, hH, smul_smul]
  rw [centralEndomorphism_apply, hEF, hFE, hHH, add_zero, smul_smul, ← add_smul]
  congr 1
  ring


/-- Computes the distinguished endomorphism on a vector satisfying the second pair of eigenvector conditions. -/
theorem centralEndomorphism_apply_eq_smul_of_secondEigenvector (μ : ℂ) (x : M) (hF : ⁅loweringElement, x⁆ = 0)
    (hH : ⁅weightElement, x⁆ = μ • x) :
    centralEndomorphism M x = ((μ * (μ - 2)) / 2) • x := by

  have hEF : ⁅raisingElement, ⁅loweringElement, x⁆⁆ = 0 := by rw [hF, lie_zero]

  have hFE : ⁅loweringElement, ⁅raisingElement, x⁆⁆ = -(μ • x) := by
    have h := leibniz_lie raisingElement loweringElement x
    rw [bracket_raising_lowering, hH, hEF] at h
    exact eq_neg_of_add_eq_zero_right h.symm

  have hHH : ⁅weightElement, ⁅weightElement, x⁆⁆ = (μ * μ) • x := by rw [hH, lie_smul, hH, smul_smul]
  rw [centralEndomorphism_apply, hEF, hFE, hHH, zero_add, smul_smul, ← neg_smul, ← add_smul]
  congr 1
  ring

end Casimir

section Central

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]


attribute [local instance 100] LieRing.ofAssociativeRing

omit [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M] in


private theorem lie_mul' (a b c : Module.End ℂ M) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by
  simp only [Ring.lie_def]; noncomm_ring


private theorem lie_e_casimir : ⁅LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement, centralEndomorphism M⁆ = 0 := by
  rw [centralEndomorphism]
  set E := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement with hE
  set F := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement with hF
  set H := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement with hH
  have bEF : ⁅E, F⁆ = H := by rw [hE, hF, hH, ← LieHom.map_lie, bracket_raising_lowering]
  have bHE : ⁅H, E⁆ = 2 • E := by rw [hH, hE, ← LieHom.map_lie, bracket_weight_raising, map_nsmul]
  have bEH : ⁅E, H⁆ = -(2 • E) := by rw [(lie_skew E H).symm, bHE]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bEF, bEH, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module


private theorem lie_f_casimir : ⁅LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement, centralEndomorphism M⁆ = 0 := by
  rw [centralEndomorphism]
  set E := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement with hE
  set F := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement with hF
  set H := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement with hH
  have bFE : ⁅F, E⁆ = -H := by
    rw [(lie_skew F E).symm, hF, hE, hH, ← LieHom.map_lie, bracket_raising_lowering]
  have bHF : ⁅H, F⁆ = -(2 • F) := by
    rw [hH, hF, ← LieHom.map_lie, bracket_weight_lowering, map_neg, map_nsmul]
  have bFH : ⁅F, H⁆ = 2 • F := by rw [(lie_skew F H).symm, bHF, neg_neg]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bFE, bFH, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module


private theorem lie_h_casimir : ⁅LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement, centralEndomorphism M⁆ = 0 := by
  rw [centralEndomorphism]
  set E := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement with hE
  set F := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement with hF
  set H := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement with hH
  have bHE : ⁅H, E⁆ = 2 • E := by rw [hH, hE, ← LieHom.map_lie, bracket_weight_raising, map_nsmul]
  have bHF : ⁅H, F⁆ = -(2 • F) := by
    rw [hH, hF, ← LieHom.map_lie, bracket_weight_lowering, map_neg, map_nsmul]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bHE, bHF, zero_mul, mul_zero, add_zero,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module


/-- Expresses an element of the displayed Lie subobject in terms of three designated generators. -/
theorem eq_linearCombination_generators (x : complexTwoByTwoMatrixLieSubalgebra) :
    x = (x.val 0 1) • raisingElement + (x.val 1 0) • loweringElement + (x.val 0 0) • weightElement := by
  apply Subtype.ext
  push_cast
  simp only [raisingElement, loweringElement, weightElement,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.single, entry_one_one_eq_neg_entry_zero_zero x]


/-- The commutator of a represented Lie element with the distinguished endomorphism is zero. -/
theorem centralEndomorphism_bracket_eq_zero (x : complexTwoByTwoMatrixLieSubalgebra) :
    ⁅LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x, centralEndomorphism M⁆ = 0 := by
  rw [eq_linearCombination_generators x, map_add, map_add, map_smul, map_smul, map_smul,
    add_lie, add_lie, smul_lie, smul_lie, smul_lie,
    lie_e_casimir, lie_f_casimir, lie_h_casimir, smul_zero, smul_zero, smul_zero,
    add_zero, add_zero]


/-- The distinguished endomorphism commutes with every Lie action. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem centralEndomorphism_commutes_action (x : complexTwoByTwoMatrixLieSubalgebra) (m : M) :
    ⁅x, centralEndomorphism M m⁆ = centralEndomorphism M ⁅x, m⁆ := by
  have hcomm : LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x * centralEndomorphism M
      = centralEndomorphism M * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x := by
    have h := centralEndomorphism_bracket_eq_zero (M := M) x
    rwa [Ring.lie_def, sub_eq_zero] at h
  calc ⁅x, centralEndomorphism M m⁆
      = LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x (centralEndomorphism M m) := (LieModule.toEnd_apply_apply ..).symm
    _ = (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x * centralEndomorphism M) m := (Module.End.mul_apply ..).symm
    _ = (centralEndomorphism M * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x) m := by rw [hcomm]
    _ = centralEndomorphism M (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x m) := Module.End.mul_apply ..
    _ = centralEndomorphism M ⁅x, m⁆ := by rw [LieModule.toEnd_apply_apply]

end Central

section GenEigenspaceDecomp

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]


/-- The distinguished endomorphism commutes with each represented Lie element. -/
theorem centralEndomorphism_commute_lieAction (x : complexTwoByTwoMatrixLieSubalgebra) :
    Commute (centralEndomorphism M) (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x) := by
  change centralEndomorphism M * LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x = LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x * centralEndomorphism M
  apply LinearMap.ext
  intro m
  simp only [Module.End.mul_apply, LieModule.toEnd_apply_apply]
  exact (centralEndomorphism_commutes_action x m).symm


/-- The Lie submodule attached to each complex generalized eigenvalue. -/
noncomputable def centralGeneralizedEigenspace (a : ℂ) : LieSubmodule ℂ complexTwoByTwoMatrixLieSubalgebra M where
  toSubmodule := (centralEndomorphism M).maxGenEigenspace a
  lie_mem := by
    intro x m hm
    have hmap := Module.End.mapsTo_maxGenEigenspace_of_comm
      (centralEndomorphism_commute_lieAction (M := M) x) a
    rw [show ⁅x, m⁆ = LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M x m from (LieModule.toEnd_apply_apply ..).symm]
    exact hmap hm


/-- Identifies the underlying submodule with the maximal generalized eigenspace of the distinguished endomorphism. -/
@[simp] theorem centralGeneralizedEigenspace_toSubmodule_eq_maxGenEigenspace (a : ℂ) :
    (centralGeneralizedEigenspace (M := M) a : Submodule ℂ M) = (centralEndomorphism M).maxGenEigenspace a :=
  rfl


/-- The family of these generalized eigenspaces is independent under supremum. -/
theorem centralGeneralizedEigenspace_iSupIndep : iSupIndep (centralGeneralizedEigenspace (M := M)) := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  simpa only [centralGeneralizedEigenspace_toSubmodule_eq_maxGenEigenspace] using
    Module.End.independent_maxGenEigenspace (centralEndomorphism M)

variable [FiniteDimensional ℂ M]


/-- For a finite-dimensional module, these generalized eigenspaces span the whole module. -/
theorem iSup_centralGeneralizedEigenspace_eq_top :
    ⨆ a, centralGeneralizedEigenspace (M := M) a = ⊤ := by
  rw [← LieSubmodule.iSup_toSubmodule_eq_top]
  simpa only [centralGeneralizedEigenspace_toSubmodule_eq_maxGenEigenspace] using
    Module.End.iSup_maxGenEigenspace_eq_top (centralEndomorphism M)


/-- For a finite-dimensional module, the generalized eigenspaces form an internal direct sum. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem centralGeneralizedEigenspace_isInternal :
    DirectSum.IsInternal (fun a => (centralGeneralizedEigenspace (M := M) a : Submodule ℂ M)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((LieSubmodule.iSupIndep_toSubmodule).mpr centralGeneralizedEigenspace_iSupIndep)
    ((LieSubmodule.iSup_toSubmodule_eq_top).mpr iSup_centralGeneralizedEigenspace_eq_top)

end GenEigenspaceDecomp

section Indecomposable

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]


/-- A predicate on a complex Lie module. -/
def AuxiliaryModulePredicate (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] : Prop :=
  Nontrivial M ∧ ∀ N N' : LieSubmodule ℂ complexTwoByTwoMatrixLieSubalgebra M, IsCompl N N' → N = ⊥ ∨ N' = ⊥

variable [FiniteDimensional ℂ M]


/-- The predicate yields a complex parameter whose generalized eigenspace is the entire finite-dimensional module. -/
theorem exists_centralGeneralizedEigenspace_eq_top_of_auxiliaryPredicate (hM : AuxiliaryModulePredicate M) :
    ∃ a : ℂ, centralGeneralizedEigenspace (M := M) a = ⊤ := by
  obtain ⟨hnt, hindec⟩ := hM
  haveI : Nontrivial M := hnt

  have hexists : ∃ a, centralGeneralizedEigenspace (M := M) a ≠ ⊥ := by
    by_contra h
    push Not at h
    have hbot : (⨆ a, centralGeneralizedEigenspace (M := M) a) = ⊥ := by simp only [h, iSup_bot]
    rw [iSup_centralGeneralizedEigenspace_eq_top] at hbot
    exact bot_ne_top hbot.symm
  obtain ⟨a₀, ha₀⟩ := hexists
  refine ⟨a₀, ?_⟩

  have hdisj : Disjoint (centralGeneralizedEigenspace (M := M) a₀)
      (⨆ (a) (_ : a ≠ a₀), centralGeneralizedEigenspace (M := M) a) :=
    centralGeneralizedEigenspace_iSupIndep a₀
  have hsup : centralGeneralizedEigenspace (M := M) a₀
      ⊔ (⨆ (a) (_ : a ≠ a₀), centralGeneralizedEigenspace (M := M) a) = ⊤ := by
    rw [← iSup_split_single (centralGeneralizedEigenspace (M := M)) a₀,
      iSup_centralGeneralizedEigenspace_eq_top]
  have hcompl : IsCompl (centralGeneralizedEigenspace (M := M) a₀)
      (⨆ (a) (_ : a ≠ a₀), centralGeneralizedEigenspace (M := M) a) :=
    ⟨hdisj, codisjoint_iff.mpr hsup⟩


  rcases hindec _ _ hcompl with h | h
  · exact absurd h ha₀
  · rw [h, sup_bot_eq] at hsup
    exact hsup

omit [FiniteDimensional ℂ M] in


/-- Two complex parameters whose generalized eigenspaces are both top are equal on a nontrivial module. -/
theorem centralGeneralizedEigenspace_eq_top_unique [Nontrivial M] {a b : ℂ}
    (ha : centralGeneralizedEigenspace (M := M) a = ⊤)
    (hb : centralGeneralizedEigenspace (M := M) b = ⊤) : a = b := by
  by_contra hab

  have hdisj := centralGeneralizedEigenspace_iSupIndep (M := M) a
  rw [ha] at hdisj
  have hYbot : (⨆ (j) (_ : j ≠ a), centralGeneralizedEigenspace (M := M) j) = ⊥ :=
    disjoint_top.mp hdisj.symm
  have hble : centralGeneralizedEigenspace (M := M) b
      ≤ ⨆ (j) (_ : j ≠ a), centralGeneralizedEigenspace (M := M) j :=
    le_iSup₂ (f := fun j (_ : j ≠ a) => centralGeneralizedEigenspace (M := M) j) b fun h => hab h.symm
  rw [hYbot, le_bot_iff, hb] at hble
  exact bot_ne_top hble.symm

end Indecomposable


section CompleteReducibility

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]


/-- Every Lie submodule of a finite-dimensional module has a complementary Lie submodule. -/
@[source_ref "Chapter2/Problem2.15.1/Derived10" (role := supporting),
  source_ref "Chapter2/Problem2.15.1/Derived11" (role := supporting),
  source_ref "Chapter2/Problem2.15.1/Derived12" (role := supporting)]
theorem exists_lieSubmodule_isCompl (N : LieSubmodule ℂ complexTwoByTwoMatrixLieSubalgebra M) :
    ∃ N' : LieSubmodule ℂ complexTwoByTwoMatrixLieSubalgebra M, IsCompl N N' :=
  haveI : ComplementedLattice (LieSubmodule ℂ complexTwoByTwoMatrixLieSubalgebra M) := lieSubmodule_complementedLattice M
  exists_isCompl N


/-- A finite-dimensional module satisfying the predicate is irreducible. -/
theorem isIrreducible_of_auxiliaryPredicate (hM : AuxiliaryModulePredicate M) :
    LieModule.IsIrreducible ℂ complexTwoByTwoMatrixLieSubalgebra M := by
  letI : Nontrivial M := hM.1
  apply LieModule.IsIrreducible.mk
  intro N hN
  obtain ⟨N', hcompl⟩ := exists_lieSubmodule_isCompl N
  rcases hM.2 N N' hcompl with h | h
  · exact (hN h).elim
  · simpa [h] using hcompl.sup_eq_top


/-- The predicate provides a natural-number parameter whose displayed generalized eigenspace is top. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem exists_integral_centralGeneralizedEigenspace_eq_top_of_auxiliaryPredicate (hM : AuxiliaryModulePredicate M) :
    ∃ lam : ℕ, centralGeneralizedEigenspace (M := M)
      (((lam : ℂ) * ((lam : ℂ) + 2)) / 2) = ⊤ := by
  letI : Nontrivial M := hM.1
  have hirr : LieModule.IsIrreducible ℂ complexTwoByTwoMatrixLieSubalgebra M := isIrreducible_of_auxiliaryPredicate hM
  let lam := Module.finrank ℂ M - 1
  have hdim : Module.finrank ℂ M = lam + 1 := by
    dsimp [lam]
    have := Module.finrank_pos (R := ℂ) (M := M)
    omega
  obtain ⟨Phi⟩ := nonempty_lieModuleEquiv_finFunction_of_irreducible lam hdim hirr
  let c : ℂ := ((lam : ℂ) * ((lam : ℂ) + 2)) / 2
  have hmap (x : complexTwoByTwoMatrixLieSubalgebra) (m : M) : Phi ⁅x, m⁆ = ⁅x, Phi m⁆ :=
    Phi.toLieModuleHom.map_lie x m
  have hcasimir_map (m : M) :
      Phi (centralEndomorphism M m) = centralEndomorphism (Fin (lam + 1) → ℂ) (Phi m) := by
    simp only [centralEndomorphism_apply, map_add, map_smul]
    simp_rw [hmap]
  have hstandard (w : Fin (lam + 1) → ℂ) :
      centralEndomorphism (Fin (lam + 1) → ℂ) w = c • w := by
    have h := LinearMap.congr_fun (quadraticGeneratorCombination_succ_eq_smul_id lam) w
    simpa only [centralEndomorphism_apply, bracket_eq_representation_apply, LinearMap.add_apply,
      Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, c] using h
  have hscalar (m : M) : centralEndomorphism M m = c • m := by
    apply Phi.injective
    rw [hcasimir_map, hstandard, map_smul]
  refine ⟨lam, ?_⟩
  apply top_unique
  intro m _
  change m ∈ (centralEndomorphism M).maxGenEigenspace c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, hscalar, LinearMap.smul_apply,
    Module.End.one_apply, c, sub_self]

end CompleteReducibility

end RepresentationTheory.LieModule.CentralAction
