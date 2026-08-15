/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearMap.KernelDecomposition
import Mathlib.LinearAlgebra.Dual.Lemmas
import RepresentationTheory.Alignment.Attribute

/-! # Bigraded cocycle lifts -/

namespace RepresentationTheory.LieAlgebra.BigradedCocycleLifts

attribute [local instance] LieRing.ofAssociativeRing

section Jacobi

variable {L : Type*} [LieRing L]

/-- The cyclic sum `[[a,b],d] + [[b,d],a] + [[d,a],b]` vanishes in any Lie ring. -/
theorem cyclic_bracket_bracket (a b d : L) : ⁅⁅a, b⁆, d⁆ + ⁅⁅b, d⁆, a⁆ + ⁅⁅d, a⁆, b⁆ = 0 := by
  rw [← lie_skew ⁅a, b⁆ d, ← lie_skew ⁅b, d⁆ a, ← lie_skew ⁅d, a⁆ b, ← neg_add, ← neg_add,
    lie_jacobi, neg_zero]

end Jacobi

section Cochain

variable (k : Type*) {L M N : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The explicit conditions that a module-valued binary map be additive and linear in both variables, alternating, and satisfy the cyclic bracket identity. -/
structure IsAlternatingLieCocycle (c : L → L → M) : Prop where
  /-- An alternating Lie cocycle is additive in its first argument. -/
  add_left : ∀ a b d : L, c (a + b) d = c a d + c b d
  /-- An alternating Lie cocycle commutes with scalar multiplication in its first argument. -/
  smul_left : ∀ (r : k) (a b : L), c (r • a) b = r • c a b
  /-- An alternating Lie cocycle is additive in its second argument. -/
  add_right : ∀ a b d : L, c a (b + d) = c a b + c a d
  /-- An alternating Lie cocycle commutes with scalar multiplication in its second argument. -/
  smul_right : ∀ (r : k) (a b : L), c a (r • b) = r • c a b
  /-- An alternating Lie cocycle vanishes when both arguments are equal. -/
  self_eq_zero : ∀ a : L, c a a = 0
  /-- The cyclic sum of an alternating Lie cocycle evaluated on brackets is zero. -/
  cyclic_bracket : ∀ a b d : L, c ⁅a, b⁆ d + c ⁅b, d⁆ a + c ⁅d, a⁆ b = 0

/-- A predicate on binary maps from a Lie algebra to a module expressing the binary cocycle condition. -/
def IsBinaryLieCocycle (c : L → L → M) : Prop :=
  ∃ f : L →ₗ[k] M, ∀ a b : L, c a b = f ⁅a, b⁆

/-- A binary Lie cocycle satisfies the explicit alternating Lie-cocycle conditions. -/
theorem IsBinaryLieCocycle.toIsAlternatingLieCocycle {c : L → L → M} (h : IsBinaryLieCocycle k c) :
    IsAlternatingLieCocycle k c := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun a b d => ?_, fun r a b => ?_, fun a b d => ?_, fun r a b => ?_, fun a => ?_,
    fun a b d => ?_⟩
  · rw [hf, hf, hf, add_lie, map_add]
  · rw [hf, hf, smul_lie, map_smul]
  · rw [hf, hf, hf, lie_add, map_add]
  · rw [hf, hf, lie_smul, map_smul]
  · rw [hf, lie_self, map_zero]
  · rw [hf, hf, hf, ← map_add, ← map_add, cyclic_bracket_bracket, map_zero]

/-- Postcomposition with a linear map preserves the alternating Lie-cocycle conditions. -/
theorem IsAlternatingLieCocycle.map {c : L → L → M} (hc : IsAlternatingLieCocycle k c) (φ : M →ₗ[k] N) :
    IsAlternatingLieCocycle k fun a b => φ (c a b) where
  add_left a b d := by rw [hc.add_left, map_add]
  smul_left r a b := by rw [hc.smul_left, map_smul]
  add_right a b d := by rw [hc.add_right, map_add]
  smul_right r a b := by rw [hc.smul_right, map_smul]
  self_eq_zero a := by rw [hc.self_eq_zero, map_zero]
  cyclic_bracket a b d := by rw [← map_add, ← map_add, hc.cyclic_bracket, map_zero]

end Cochain

section Grading

variable {k : Type*} [Field k]

/-- The pair of natural numbers giving the bidegree of an index. -/
def _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bidegree (J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : ℕ × ℕ := (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J).bideg

/-- The distinguished index has bidegree `(0, 1)`. -/
@[simp] theorem distinguishedIndex_bidegree : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.base.bidegree = (0, 1) := rfl

/-- The bidegree of the five-member indexed family is `(2m + 1, 4m + i.rev)`. -/
@[simp] theorem fiveFamilyIndex_bidegree (m : ℕ) (i : Fin 5) :
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.odd m i).bidegree = (2 * m + 1, 4 * m + (i.rev : ℕ)) := rfl

/-- The bidegree of the three-member indexed family is `(2m + 2, 4m + 3 + i.rev)`. -/
@[simp] theorem threeFamilyIndex_bidegree (m : ℕ) (i : Fin 3) :
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m i).bidegree = (2 * m + 2, 4 * m + 3 + (i.rev : ℕ)) := rfl

/-- The index associated with `I` has the same bidegree as `I`. -/
theorem associatedIndex_bidegree (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution I).bidegree = I.bideg := by
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bidegree, _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution_involutive I]

/-- The bidegree projection on indices is injective. -/
theorem bidegree_injective : Function.Injective _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bidegree :=
  _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg_injective.comp _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution_injective

/-- The submodule of the distinguished Lie subspace associated with a pair of natural-number degrees. -/
noncomputable def bidegreeComponent (k : Type*) [Field k] (p : ℕ × ℕ) : Submodule k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :=
  Submodule.span k {v | ∃ J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex, J.bidegree = p ∧ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J = v}

/-- Each indexed subspace element belongs to the component specified by the bidegree of its index. -/
theorem indexedElement_mem_bidegreeComponent (J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J ∈ bidegreeComponent k J.bidegree :=
  Submodule.subset_span ⟨J, rfl, rfl⟩

end Grading

section Section

variable {k : Type*} [Field k]

/-- A characteristic-dependent linear lift from the distinguished Lie subspace to the ambient Lie algebra at parameter four. -/
noncomputable def liftFromDistinguishedSubspace (h2 : (2 : k) ≠ 0) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4 :=
  (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2 k h2).constr k fun J => (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexedCoefficient k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J))⁻¹ • _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J)

/-- The lift of an indexed subspace element is the corresponding ambient indexed element scaled by the inverse of its designated coefficient. -/
theorem liftFromDistinguishedSubspace_indexedElement (h2 : (2 : k) ≠ 0) (J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    liftFromDistinguishedSubspace h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) = (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexedCoefficient k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J))⁻¹ • _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J) := by
  rw [liftFromDistinguishedSubspace, ← _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux6 k h2 J, Module.Basis.constr_basis]

/-- The lift of an indexed subspace element belongs to the ambient component determined by its bidegree. -/
theorem liftFromDistinguishedSubspace_indexedElement_mem (h2 : (2 : k) ≠ 0) (J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    liftFromDistinguishedSubspace h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 J.bidegree := by
  rw [liftFromDistinguishedSubspace_indexedElement]
  exact Submodule.smul_mem _ _ (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.indexedElement_mem_component k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution J))

/-- The lift sends a subspace bidegree component into the matching ambient bidegree component. -/
theorem liftFromDistinguishedSubspace_mem_bidegreeComponent (h2 : (2 : k) ≠ 0) (p : ℕ × ℕ) {v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k} (hv : v ∈ bidegreeComponent k p) :
    liftFromDistinguishedSubspace h2 v ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p := by
  have key : ∀ w ∈ bidegreeComponent k p, liftFromDistinguishedSubspace h2 w ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨J, hJ, rfl⟩ := hz
        exact hJ ▸ liftFromDistinguishedSubspace_indexedElement_mem h2 J
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  exact key v hv

/-- The ambient map applied to a lifted subspace element is its underlying value. -/
theorem ambientMap_comp_lift (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (liftFromDistinguishedSubspace h2 v) = (v : Matrix (Fin 3) (Fin 3) (Polynomial k)) := by
  have key : (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k).comp (liftFromDistinguishedSubspace h2) = (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k).toSubmodule.subtype := by
    refine (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2 k h2).ext fun J => ?_
    rw [LinearMap.comp_apply, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux6, liftFromDistinguishedSubspace_indexedElement, map_smul, _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.realizationMap_indexedFamily,
      _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution_involutive J, smul_smul, inv_mul_cancel₀ (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexedCoefficient_ne_zero h2 h3 _), one_smul]
    rfl
  exact congrArg (fun f : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] Matrix (Fin 3) (Fin 3) (Polynomial k) => f v) key

/-- A linear map from the ambient Lie algebra at parameter four to the distinguished Lie subspace. -/
noncomputable def projectToDistinguishedSubspace (k : Type*) [Field k] : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4 →ₗ[k] _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k where
  toFun u := ⟨_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_mem u⟩
  map_add' u v := Subtype.ext (map_add (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) u v)
  map_smul' r u := Subtype.ext (map_smul (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) r u)

/-- The underlying value of the subspace-valued projection agrees with the corresponding ambient linear map. -/
@[simp] theorem projectedSubtypeMap_val (u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    (projectToDistinguishedSubspace k u : Matrix (Fin 3) (Fin 3) (Polynomial k)) = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u := rfl

/-- Projection to the distinguished subspace preserves Lie brackets. -/
theorem projectToDistinguishedSubspace_bracket (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) : projectToDistinguishedSubspace k ⁅u, v⁆ = ⁅projectToDistinguishedSubspace k u, projectToDistinguishedSubspace k v⁆ :=
  Subtype.ext <| by rw [projectedSubtypeMap_val, LieSubalgebra.coe_bracket, projectedSubtypeMap_val, projectedSubtypeMap_val, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket]

/-- Under the stated characteristic restrictions, projecting a lifted subspace element returns that element. -/
theorem projectToDistinguishedSubspace_comp_lift (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :
    projectToDistinguishedSubspace k (liftFromDistinguishedSubspace h2 v) = v :=
  Subtype.ext (ambientMap_comp_lift h2 h3 v)

/-- Under the stated characteristic restrictions, projection annihilates every member of the specified natural-number-indexed family. -/
theorem projectToDistinguishedSubspace_specialFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m) = 0 :=
  Subtype.ext <| by rw [projectedSubtypeMap_val, _root_.RepresentationTheory.LinearMap.KernelDecomposition.map_auxFamily_eq_zero h2 h3 h5]; rfl

/-- Under the stated characteristic restrictions, projection sends each ambient bidegree component into the corresponding subspace component. -/
theorem projectToDistinguishedSubspace_mem_bidegreeComponent (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} (hu : u ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p) : projectToDistinguishedSubspace k u ∈ bidegreeComponent k p := by
  set T : Set (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) := {w | (∃ I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex, I.bideg = p ∧ _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I = w) ∨
    ∃ m : ℕ, (2 * m + 2, 4 * m + 4) = p ∧ _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = w} with hT
  have hle : _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p ≤ Submodule.span k T :=
    _root_.RepresentationTheory.LieAlgebra.BigradedComponents.component_le_span_of_generators h2 h3 h5 p T (fun I hI => Submodule.subset_span (Or.inl ⟨I, hI, rfl⟩))
      (fun m hm => Submodule.subset_span (Or.inr ⟨m, hm, rfl⟩))
  have key : ∀ w ∈ Submodule.span k T, projectToDistinguishedSubspace k w ∈ bidegreeComponent k p := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨I, hI, rfl⟩ | ⟨m, hm, rfl⟩
        · have himg : projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I) = _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexedCoefficient k I • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution I) :=
            Subtype.ext <| by rw [projectedSubtypeMap_val, _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.realizationMap_indexedFamily]; rfl
          rw [himg]
          refine Submodule.smul_mem _ _ ?_
          exact (associatedIndex_bidegree I).trans hI ▸ indexedElement_mem_bidegreeComponent (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution I)
        · rw [projectToDistinguishedSubspace_specialFamily_eq_zero h2 h3 h5]
          exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  exact key u (hle hu)

/-- The bracket of two indexed subspace elements belongs to the component whose bidegree is the sum of their bidegrees. -/
theorem bracket_indexedElement_mem_bidegreeComponent_add (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J⁆ ∈ bidegreeComponent k (I.bidegree + J.bidegree) := by
  have hrw : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J⁆
      = projectToDistinguishedSubspace k ⁅liftFromDistinguishedSubspace h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I), liftFromDistinguishedSubspace h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J)⁆ := by
    rw [projectToDistinguishedSubspace_bracket, projectToDistinguishedSubspace_comp_lift h2 h3, projectToDistinguishedSubspace_comp_lift h2 h3]
  rw [hrw]
  exact projectToDistinguishedSubspace_mem_bidegreeComponent h2 h3 h5 _
    (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k (liftFromDistinguishedSubspace_indexedElement_mem h2 I) (liftFromDistinguishedSubspace_indexedElement_mem h2 J))

end Section

section Cocycle

variable {k : Type*} [Field k]

/-- The ambient-valued correction term comparing brackets of lifted subspace elements with lifts of their bracket. -/
noncomputable def bracketCorrection (h2 : (2 : k) ≠ 0) (a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4 :=
  ⁅liftFromDistinguishedSubspace h2 a, liftFromDistinguishedSubspace h2 b⁆ - liftFromDistinguishedSubspace h2 ⁅a, b⁆

/-- The bracket of two lifted elements is the lift of their bracket plus the bracket-correction term. -/
theorem bracket_lift_eq_lift_bracket_add_correction (h2 : (2 : k) ≠ 0) (a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :
    ⁅liftFromDistinguishedSubspace h2 a, liftFromDistinguishedSubspace h2 b⁆ = liftFromDistinguishedSubspace h2 ⁅a, b⁆ + bracketCorrection h2 a b := by
  rw [bracketCorrection]; abel

/-- The bracket-correction term lies in the kernel of the ambient linear map. -/
theorem bracketCorrection_mem_ambientMap_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :
    bracketCorrection h2 a b ∈ LinearMap.ker (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) := by
  rw [LinearMap.mem_ker, bracketCorrection, map_sub, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket, ambientMap_comp_lift h2 h3,
    ambientMap_comp_lift h2 h3, ambientMap_comp_lift h2 h3, LieSubalgebra.coe_bracket, sub_self]

/-- Under the stated characteristic restrictions, an element in the kernel of the ambient map brackets to zero with every ambient element. -/
theorem mem_ambientMap_ker_bracket_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    {w : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} (hw : w ∈ LinearMap.ker (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) (u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) : ⁅w, u⁆ = 0 := by
  have h := _root_.RepresentationTheory.LinearMap.KernelDecomposition.mem_ker_implies_bracket_eq_zero h2 h3 h5 hw u
  rw [← lie_skew u w] at h
  exact neg_eq_zero.1 h

/-- Under the stated characteristic restrictions, the bracket-correction term is an alternating Lie cocycle. -/
theorem bracketCorrection_isAlternatingLieCocycle (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    IsAlternatingLieCocycle k (bracketCorrection h2) where
  add_left a b d := by
    simp only [bracketCorrection, map_add, add_lie]
    abel
  smul_left r a b := by
    simp only [bracketCorrection, map_smul, smul_lie, smul_sub]
  add_right a b d := by
    simp only [bracketCorrection, map_add, lie_add]
    abel
  smul_right r a b := by
    simp only [bracketCorrection, map_smul, lie_smul, smul_sub]
  self_eq_zero a := by
    rw [bracketCorrection, lie_self, lie_self, map_zero, sub_self]
  cyclic_bracket a b d := by
    have key : ∀ x y z : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k, ⁅⁅liftFromDistinguishedSubspace h2 x, liftFromDistinguishedSubspace h2 y⁆, liftFromDistinguishedSubspace h2 z⁆
        = liftFromDistinguishedSubspace h2 ⁅⁅x, y⁆, z⁆ + bracketCorrection h2 ⁅x, y⁆ z := by
      intro x y z
      rw [bracket_lift_eq_lift_bracket_add_correction h2 x y, add_lie,
        mem_ambientMap_ker_bracket_eq_zero h2 h3 h5 (bracketCorrection_mem_ambientMap_ker h2 h3 x y) _, add_zero,
        bracket_lift_eq_lift_bracket_add_correction h2 ⁅x, y⁆ z]
    have h0 := cyclic_bracket_bracket (liftFromDistinguishedSubspace h2 a) (liftFromDistinguishedSubspace h2 b) (liftFromDistinguishedSubspace h2 d)
    rw [key a b d, key b d a, key d a b] at h0
    have hL : liftFromDistinguishedSubspace h2 ⁅⁅a, b⁆, d⁆ + liftFromDistinguishedSubspace h2 ⁅⁅b, d⁆, a⁆ + liftFromDistinguishedSubspace h2 ⁅⁅d, a⁆, b⁆ = 0 := by
      rw [← map_add, ← map_add, cyclic_bracket_bracket, map_zero]
    have e : bracketCorrection h2 ⁅a, b⁆ d + bracketCorrection h2 ⁅b, d⁆ a + bracketCorrection h2 ⁅d, a⁆ b
        = ((liftFromDistinguishedSubspace h2 ⁅⁅a, b⁆, d⁆ + bracketCorrection h2 ⁅a, b⁆ d)
            + (liftFromDistinguishedSubspace h2 ⁅⁅b, d⁆, a⁆ + bracketCorrection h2 ⁅b, d⁆ a)
            + (liftFromDistinguishedSubspace h2 ⁅⁅d, a⁆, b⁆ + bracketCorrection h2 ⁅d, a⁆ b))
          - (liftFromDistinguishedSubspace h2 ⁅⁅a, b⁆, d⁆ + liftFromDistinguishedSubspace h2 ⁅⁅b, d⁆, a⁆ + liftFromDistinguishedSubspace h2 ⁅⁅d, a⁆, b⁆) := by
      abel
    rw [e, h0, hL, sub_zero]

/-- The correction term on indexed elements vanishes when the sum of their bidegrees avoids every pair `(2m + 2, 4m + 4)`. -/
theorem bracketCorrection_indexed_eq_zero_of_bidegree_ne (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) (hIJ : ∀ m : ℕ, I.bidegree + J.bidegree ≠ (2 * m + 2, 4 * m + 4)) :
    bracketCorrection h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) = 0 := by
  have hker := bracketCorrection_mem_ambientMap_ker h2 h3 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J)
  have hdeg : bracketCorrection h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (I.bidegree + J.bidegree) := by
    refine sub_mem (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k (liftFromDistinguishedSubspace_indexedElement_mem h2 I) (liftFromDistinguishedSubspace_indexedElement_mem h2 J)) ?_
    exact liftFromDistinguishedSubspace_mem_bidegreeComponent h2 _ (bracket_indexedElement_mem_bidegreeComponent_add h2 h3 h5 I J)
  have hbot := _root_.RepresentationTheory.LinearMap.KernelDecomposition.ker_inf_component_eq_bot h2 h3 h5 (I.bidegree + J.bidegree) hIJ
  rw [Submodule.eq_bot_iff] at hbot
  exact hbot _ (Submodule.mem_inf.2 ⟨hker, hdeg⟩)

/-- A distinguished condition on scalar-valued binary functions on the specified Lie subspace. -/
def SpecialBinaryFormCondition (c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k) : Prop :=
  ∀ I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex, (∀ m : ℕ, I.bidegree + J.bidegree ≠ (2 * m + 2, 4 * m + 4)) →
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) = 0

/-- The bidegrees `(2, 1)` and `(1, 5)` are distinct from every pair `(2m + 2, 4m + 4)`. -/
theorem exceptionalBidegrees_ne_family :
    (∀ m : ℕ, ((2, 1) : ℕ × ℕ) ≠ (2 * m + 2, 4 * m + 4)) ∧
      ∀ m : ℕ, ((1, 5) : ℕ × ℕ) ≠ (2 * m + 2, 4 * m + 4) := by
  refine ⟨fun m h => ?_, fun m h => ?_⟩ <;> rw [Prod.mk.injEq] at h <;> omega

/-- A binary form satisfying the distinguished condition vanishes on the displayed pair of indexed subspace elements. -/
theorem specialBinaryFormCondition_apply_distinguished_eq_zero {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k}
    (hc : SpecialBinaryFormCondition c) : c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd 0 0)) = 0 := by
  refine hc _ _ fun m h => ?_
  rw [distinguishedIndex_bidegree, fiveFamilyIndex_bidegree, Prod.mk_add_mk, Prod.mk.injEq] at h
  have hrev : ((0 : Fin 5).rev : ℕ) = 4 := rfl
  rw [hrev] at h
  omega

/-- Composing the bracket-correction term with any linear functional produces a binary form satisfying the distinguished condition. -/
theorem linearFunctional_comp_bracketCorrection_specialCondition (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (φ : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4 →ₗ[k] k) : SpecialBinaryFormCondition fun a b => φ (bracketCorrection h2 a b) := by
  intro I J hIJ
  change φ (bracketCorrection h2 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J)) = 0
  rw [bracketCorrection_indexed_eq_zero_of_bidegree_ne h2 h3 h5 I J hIJ, map_zero]

end Cocycle

section Reduction

variable {k : Type*} [Field k]

/-- Under the stated characteristic restrictions, the bracket of two ambient elements equals the bracket of the lifts of their projections. -/
theorem bracket_eq_bracket_lift_project (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) : ⁅u, v⁆ = ⁅liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k u), liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k v)⁆ := by
  have hu : u - liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k u) ∈ LinearMap.ker (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) := by
    rw [LinearMap.mem_ker, map_sub, ambientMap_comp_lift h2 h3, projectedSubtypeMap_val, sub_self]
  have hv : v - liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k v) ∈ LinearMap.ker (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) := by
    rw [LinearMap.mem_ker, map_sub, ambientMap_comp_lift h2 h3, projectedSubtypeMap_val, sub_self]
  have e : ⁅u, v⁆ - ⁅liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k u), liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k v)⁆
      = ⁅u - liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k u), v⁆
        + ⁅liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k u), v - liftFromDistinguishedSubspace h2 (projectToDistinguishedSubspace k v)⁆ := by
    rw [sub_lie, lie_sub]; abel
  rw [← sub_eq_zero, e, mem_ambientMap_ker_bracket_eq_zero h2 h3 h5 hu v,
    _root_.RepresentationTheory.LinearMap.KernelDecomposition.mem_ker_implies_bracket_eq_zero h2 h3 h5 hv _, add_zero]

/-- Under the cocycle-extension hypothesis and the stated characteristic restrictions, every element of the specified natural-number-indexed family is zero. -/
theorem specialFamily_eq_zero_of_cocycle_extension (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (H : ∀ c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k,
      IsAlternatingLieCocycle k c → SpecialBinaryFormCondition c → IsBinaryLieCocycle k c)
    (m : ℕ) : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m)]
  intro φ
  obtain ⟨f, hf⟩ := H (fun a b => φ (bracketCorrection h2 a b))
    ((bracketCorrection_isAlternatingLieCocycle h2 h3 h5).map k φ) (linearFunctional_comp_bracketCorrection_specialCondition h2 h3 h5 φ)
  have hf' : ∀ a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k, φ (bracketCorrection h2 a b) = f ⁅a, b⁆ := hf
  set ψ : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] k := φ.comp (liftFromDistinguishedSubspace h2) + f with hψ
  have hbr : ∀ u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4, φ ⁅u, v⁆ = ψ ⁅projectToDistinguishedSubspace k u, projectToDistinguishedSubspace k v⁆ := by
    intro u v
    rw [bracket_eq_bracket_lift_project h2 h3 h5 u v, bracket_lift_eq_lift_bracket_add_correction h2 (projectToDistinguishedSubspace k u) (projectToDistinguishedSubspace k v), map_add,
      hf' (projectToDistinguishedSubspace k u) (projectToDistinguishedSubspace k v), hψ]
    simp [LinearMap.comp_apply]
  have hz : ⁅projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 4), projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m)⁆
      - (2 : k) • ⁅projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux8 k 4), projectToDistinguishedSubspace k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ = 0 := by
    rw [← projectToDistinguishedSubspace_bracket, ← projectToDistinguishedSubspace_bracket, ← map_smul, ← map_sub, ← _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one, ← _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily]
    exact projectToDistinguishedSubspace_specialFamily_eq_zero h2 h3 h5 m
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one, map_sub, map_smul, hbr, hbr, ← map_smul ψ, ← map_sub ψ, hz, map_zero]

/-- The ambient linear map is injective when every explicit alternating cocycle satisfying the distinguished condition also satisfies the binary cocycle predicate. -/
theorem ambientMap_injective_of_cocycle_extension (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (H : ∀ c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k,
      IsAlternatingLieCocycle k c → SpecialBinaryFormCondition c → IsBinaryLieCocycle k c) :
    Function.Injective (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) :=
  (_root_.RepresentationTheory.LinearMap.KernelDecomposition.injective_iff_auxFamily_eq_zero h2 h3 h5).2
    (specialFamily_eq_zero_of_cocycle_extension h2 h3 h5 H)

/-- Under the cocycle-extension hypothesis and the stated characteristic restrictions, the indexed ambient elements span the whole ambient space. -/
theorem indexedElements_span_eq_top_of_cocycle_extension (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (H : ∀ c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k,
      IsAlternatingLieCocycle k c → SpecialBinaryFormCondition c → IsBinaryLieCocycle k c) :
    Submodule.span k (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)) = ⊤ :=
  _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.span_range_auxiliaryFamily_eq_top h2 h3 h5
    (ambientMap_injective_of_cocycle_extension h2 h3 h5 H)

end Reduction

end RepresentationTheory.LieAlgebra.BigradedCocycleLifts
attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsBinaryLieCocycle
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bidegree
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bidegreeComponent
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.liftFromDistinguishedSubspace
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bracketCorrection
  RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition
