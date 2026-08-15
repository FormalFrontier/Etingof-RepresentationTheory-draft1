/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.IndexedPermutationFinsetAction








namespace RepresentationTheory.AlternatingTensorSquare

open RepresentationTheory.QuaternionGroupTwo.AuxiliaryType



open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false











open scoped TensorProduct


/-- An auxiliary complex submodule of functions on five coordinates. -/
abbrev auxiliaryCoordinateSubmodule : Submodule ℂ (Fin 5 → ℂ) := (RepresentationTheory.PermutationActionRepresentations.auxiliarySubrepresentation (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5)).toSubmodule


/-- A complex representation on the auxiliary five-coordinate submodule. -/
def coordinateRepresentation : Representation ℂ RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 auxiliaryCoordinateSubmodule := (RepresentationTheory.PermutationActionRepresentations.auxiliarySubrepresentation (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5)).toRepresentation

/-- The trace of each coordinate representation operator equals the character of the displayed finite-dimensional representation. -/
lemma trace_coordinateRepresentation (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) : LinearMap.trace ℂ auxiliaryCoordinateSubmodule (coordinateRepresentation g) = RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character g := by
  rw [RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne, RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation, FDRep.character, FDRep.of_ρ', coordinateRepresentation]


private lemma trace_eq_sum_repr_diagW
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ M f = ∑ i, b.repr (f (b i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]




private lemma trace_comm_comp_mapW
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (A B : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W ⊗[ℂ] W)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B)
      = LinearMap.trace ℂ W (A ∘ₗ B) := by
  classical
  set b := Module.finBasis ℂ W with hb
  rw [trace_eq_sum_repr_diagW (b.tensorProduct b)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B),
      Fintype.sum_prod_type]
  have hLHS : ∀ i j, (b.tensorProduct b).repr
        ((((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B))
          ((b.tensorProduct b) (i, j))) (i, j)
        = b.repr (A (b i)) j * b.repr (B (b j)) i := by
    intro i j
    rw [Module.Basis.tensorProduct_apply]
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  simp_rw [hLHS]
  rw [trace_eq_sum_repr_diagW b (A ∘ₗ B)]
  have hRHS : ∀ i, b.repr ((A ∘ₗ B) (b i)) i
      = ∑ j, b.repr (A (b j)) i * b.repr (B (b i)) j := by
    intro i
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← Module.Basis.sum_repr b (B (b i))]
    rw [map_sum, map_sum, Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hRHS]
  rw [Finset.sum_comm]


/-- A complex-linear endomorphism of the tensor square that commutes with the group action. -/
def equivariantInvolution : Module.End ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := (TensorProduct.comm ℂ auxiliaryCoordinateSubmodule auxiliaryCoordinateSubmodule).toLinearMap


/-- A complex-linear endomorphism of the tensor square of the auxiliary coordinate submodule. -/
def equivariantIdempotent : Module.End ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := (2⁻¹ : ℂ) • (1 - equivariantInvolution)

/-- The square of the equivariant tensor endomorphism is the identity. -/
lemma equivariantInvolution_sq : equivariantInvolution * equivariantInvolution = 1 := by
  rw [Module.End.mul_eq_comp, equivariantInvolution, TensorProduct.comm_comp_comm]; rfl

/-- The equivariant tensor-square endomorphism is idempotent. -/
lemma isIdempotentElem_equivariantIdempotent : IsIdempotentElem equivariantIdempotent := by
  have hbb : (1 - equivariantInvolution) * (1 - equivariantInvolution) = 1 - equivariantInvolution - equivariantInvolution + equivariantInvolution * equivariantInvolution := by
    rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel
  rw [IsIdempotentElem, equivariantIdempotent, smul_mul_smul_comm, hbb, equivariantInvolution_sq]
  rw [show (1 : Module.End ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule)) - equivariantInvolution - equivariantInvolution + 1 = (2 : ℂ) • (1 - equivariantInvolution) by module]
  rw [smul_smul, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]


/-- The tensor-square involution commutes with every representation operator. -/
lemma equivariantInvolution_commutes (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    equivariantInvolution * (coordinateRepresentation.tprod coordinateRepresentation) g = (coordinateRepresentation.tprod coordinateRepresentation) g * equivariantInvolution := by
  rw [Representation.tprod_apply, equivariantInvolution]
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul]


/-- The endomorphism commutes with every operator of the tensor-product representation. -/
lemma equivariantIdempotent_commutes (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    equivariantIdempotent * (coordinateRepresentation.tprod coordinateRepresentation) g = (coordinateRepresentation.tprod coordinateRepresentation) g * equivariantIdempotent := by
  rw [equivariantIdempotent, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, equivariantInvolution_commutes]


/-- An auxiliary subrepresentation of the tensor square of the coordinate representation. -/
def auxiliaryTensorSquareSubrepresentation : Subrepresentation (coordinateRepresentation.tprod coordinateRepresentation) where
  toSubmodule := LinearMap.range equivariantIdempotent
  apply_mem_toSubmodule g := by
    intro v hv
    rw [LinearMap.IsIdempotentElem.mem_range_iff isIdempotentElem_equivariantIdempotent] at hv ⊢
    calc equivariantIdempotent ((coordinateRepresentation.tprod coordinateRepresentation) g v)
        = (equivariantIdempotent * (coordinateRepresentation.tprod coordinateRepresentation) g) v := rfl
      _ = ((coordinateRepresentation.tprod coordinateRepresentation) g * equivariantIdempotent) v := by rw [equivariantIdempotent_commutes]
      _ = (coordinateRepresentation.tprod coordinateRepresentation) g (equivariantIdempotent v) := rfl
      _ = (coordinateRepresentation.tprod coordinateRepresentation) g v := by rw [hv]


/-- A finite-dimensional complex representation with the alternating-square character formula. -/
def alternatingSquareRepresentation : FDRep ℂ RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 := FDRep.of auxiliaryTensorSquareSubrepresentation.toRepresentation


/-- The alternating-square character is one half of the difference between the squared character and its value at the square. -/
lemma character_alternatingSquareRepresentation (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    alternatingSquareRepresentation.character g = (2⁻¹ : ℂ) * (RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character g ^ 2 - RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character (g * g)) := by
  classical

  set T := (coordinateRepresentation.tprod coordinateRepresentation) g with hT
  set N : Fin 2 → Submodule ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := ![LinearMap.range equivariantIdempotent, LinearMap.ker equivariantIdempotent] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr
      (LinearMap.IsIdempotentElem.isCompl isIdempotentElem_equivariantIdempotent)

  have hbeta_range : ∀ x ∈ LinearMap.range equivariantIdempotent, equivariantInvolution x = -x := by
    intro x hx
    rw [LinearMap.IsIdempotentElem.mem_range_iff isIdempotentElem_equivariantIdempotent, equivariantIdempotent, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.one_apply] at hx

    have h2 : x - equivariantInvolution x = (2 : ℂ) • x := by
      have h := congrArg (fun z : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule => (2 : ℂ) • z) hx
      simp only [smul_smul] at h
      rwa [show (2 : ℂ) * 2⁻¹ = 1 by norm_num, one_smul] at h
    have hb : equivariantInvolution x = x - (2 : ℂ) • x := by rw [eq_sub_iff_add_eq, ← h2]; abel
    rw [hb]; module
  have hbeta_ker : ∀ x ∈ LinearMap.ker equivariantIdempotent, equivariantInvolution x = x := by
    intro x hx
    rw [LinearMap.mem_ker, equivariantIdempotent, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply] at hx

    rw [smul_eq_zero] at hx
    rcases hx with h | h
    · norm_num at h
    · rw [sub_eq_zero] at h; exact h.symm

  have hfT : ∀ i, Set.MapsTo T (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · exact fun x hx => auxiliaryTensorSquareSubrepresentation.apply_mem_toSubmodule g hx
    · intro x hx
      have hxk : equivariantIdempotent x = 0 := (LinearMap.mem_ker (f := equivariantIdempotent)).mp hx
      have hzero : equivariantIdempotent (T x) = 0 := by
        rw [hT]
        calc equivariantIdempotent ((coordinateRepresentation.tprod coordinateRepresentation) g x)
              = (equivariantIdempotent * (coordinateRepresentation.tprod coordinateRepresentation) g) x := rfl
            _ = ((coordinateRepresentation.tprod coordinateRepresentation) g * equivariantIdempotent) x := by rw [equivariantIdempotent_commutes]
            _ = (coordinateRepresentation.tprod coordinateRepresentation) g (equivariantIdempotent x) := rfl
            _ = 0 := by rw [hxk, map_zero]
      exact (LinearMap.mem_ker (f := equivariantIdempotent)).mpr hzero
  have hbetaT : (TensorProduct.comm ℂ auxiliaryCoordinateSubmodule auxiliaryCoordinateSubmodule).toLinearMap ∘ₗ TensorProduct.map (coordinateRepresentation g) (coordinateRepresentation g)
      = equivariantInvolution ∘ₗ T := by rw [equivariantInvolution, hT, Representation.tprod_apply]
  have hfbT : ∀ i, Set.MapsTo (equivariantInvolution ∘ₗ T) (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro x hx
      have hbx : (equivariantInvolution ∘ₗ T) x = -(T x) := by
        rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
      rw [SetLike.mem_coe, hbx]
      exact neg_mem (hfT 0 hx)
    · intro x hx
      have hbx : (equivariantInvolution ∘ₗ T) x = T x := by
        rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
      rw [SetLike.mem_coe, hbx]
      exact hfT 1 hx

  have htrT := LinearMap.trace_eq_sum_trace_restrict hInternal hfT
  have htrbT := LinearMap.trace_eq_sum_trace_restrict hInternal hfbT
  rw [Fin.sum_univ_two] at htrT htrbT

  have hres0 : (equivariantInvolution ∘ₗ T).restrict (hfbT 0) = -(T.restrict (hfT 0)) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) ∈ N 0 := x.2
    change (equivariantInvolution ∘ₗ T) (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) = -(T (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule))
    rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
  have hres1 : (equivariantInvolution ∘ₗ T).restrict (hfbT 1) = T.restrict (hfT 1) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) ∈ N 1 := x.2
    change (equivariantInvolution ∘ₗ T) (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) = T (x : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule)
    rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
  have htr_b0 : LinearMap.trace ℂ ↥(N 0) ((equivariantInvolution ∘ₗ T).restrict (hfbT 0))
      = -(LinearMap.trace ℂ ↥(N 0) (T.restrict (hfT 0))) := by
    rw [hres0]; exact map_neg (LinearMap.trace ℂ ↥(N 0)) (T.restrict (hfT 0))
  have htr_b1 : LinearMap.trace ℂ ↥(N 1) ((equivariantInvolution ∘ₗ T).restrict (hfbT 1))
      = LinearMap.trace ℂ ↥(N 1) (T.restrict (hfT 1)) := by rw [hres1]
  rw [htr_b0, htr_b1] at htrbT

  have hTtrace : LinearMap.trace ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) T = RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character g ^ 2 := by
    rw [hT, Representation.tprod_apply, LinearMap.trace_tensorProduct', trace_coordinateRepresentation, sq]
  have hbTtrace : LinearMap.trace ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) (equivariantInvolution ∘ₗ T) = RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character (g * g) := by
    rw [← hbetaT, trace_comm_comp_mapW, ← Module.End.mul_eq_comp, ← map_mul, trace_coordinateRepresentation]

  have hlam2 : alternatingSquareRepresentation.character g = LinearMap.trace ℂ (N 0) (T.restrict (hfT 0)) := rfl

  rw [hTtrace] at htrT
  rw [hbTtrace] at htrbT
  rw [hlam2]

  linear_combination (-2⁻¹ : ℂ) * htrT + (2⁻¹ : ℂ) * htrbT




/-- An auxiliary statement whose formal type was unavailable. -/
lemma auxiliaryUnavailableStatement (j : Fin 5) :
    alternatingSquareRepresentation.character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = (![6, 0, -2, 1, 1] j : ℂ) := by
  have hf : ∀ k, RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative k) = ![5, 2, 1, 0, 0] k := by decide
  have hsq : ∀ k, RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative k * RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative k)
      = ![5, 2, 5, 0, 0] k := by decide
  rw [character_alternatingSquareRepresentation, RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne, RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne, hf j, hsq j]
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in














/-- The endomorphism space of the alternating-square representation has complex dimension two. -/
lemma finrank_end_alternatingSquareRepresentation : Module.finrank ℂ (alternatingSquareRepresentation ⟶ alternatingSquareRepresentation) = 2 := by
  haveI : Invertible (Fintype.card RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 : ℂ) := by
    have h60 : Fintype.card RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 = 60 := by rw [← Nat.card_eq_fintype_card, RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5]
    rw [h60]; exact invertibleOfNonzero (by norm_num)
  have key := FDRep.scalar_product_char_eq_finrank_equivariant alternatingSquareRepresentation alternatingSquareRepresentation

  have hterm : ∀ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5, alternatingSquareRepresentation.character g * alternatingSquareRepresentation.character g⁻¹
      = (4⁻¹ : ℂ) * ((((((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) g : ℤ) - 1) ^ 2
          - ((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2 : ℤ) : ℂ)) := by
    intro g
    rw [character_alternatingSquareRepresentation, character_alternatingSquareRepresentation]
    simp only [RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne, RepresentationTheory.PermutationActionRepresentations.fixedPointCount_inv]
    rw [show g⁻¹ * g⁻¹ = (g * g)⁻¹ from by group, RepresentationTheory.PermutationActionRepresentations.fixedPointCount_inv]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.mul_sum, ← Int.cast_sum] at key
  have hZ : ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5, ((((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) g : ℤ) - 1) ^ 2
      - ((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2) = 480 := by decide
  rw [hZ] at key
  have h60 : Fintype.card RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 = 60 := by rw [← Nat.card_eq_fintype_card, RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5]

  rw [RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5] at key
  have hval : ((60 : ℕ) : ℂ)⁻¹ * ((4⁻¹ : ℂ) * ((480 : ℤ) : ℂ)) = (2 : ℂ) := by
    push_cast; norm_num
  rw [hval] at key
  exact_mod_cast key.symm









/-- A three-by-five table of integer character values. -/
def integerCharacterTable : Fin 3 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![4,  1,  0, -1, -1],
    ![5, -1,  1,  0,  0]]



/-- A map selecting three character-table rows from a five-valued row index. -/
def selectedCharacterRowIndex : Fin 3 → Fin 5 := ![0, 3, 4]

/-- At each indexed group element, the displayed representation's character equals the integer-table entry in row zero. -/
lemma character_auxiliaryRepresentation_row_zero (j : Fin 5) : RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation.character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = (integerCharacterTable 0 j : ℂ) := by
  rw [RepresentationTheory.IndexedPermutationFinsetAction.character_trivialRepresentation]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- At each indexed group element, the displayed representation's character equals the integer-table entry in row one. -/
lemma character_auxiliaryRepresentation_row_one (j : Fin 5) : RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne.character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = (integerCharacterTable 1 j : ℂ) := by
  have hf : ∀ k, RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative k) = ![5, 2, 1, 0, 0] k := by decide
  rw [RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne, hf j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- At each indexed group element, the displayed representation's character equals the integer-table entry in row two. -/
lemma character_auxiliaryRepresentation_row_two (j : Fin 5) : RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo.character (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) = (integerCharacterTable 2 j : ℂ) := by
  have hf : ∀ k, RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 6) (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative k) = ![6, 0, 2, 1, 1] k := by decide
  rw [RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationTwo, hf j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]




/-- The selected entries of the displayed complex table are integer casts of the corresponding integer-table entries. -/
lemma complexTable_selectedRows_eq_intCast (i : Fin 3) (j : Fin 5) :
    RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable (selectedCharacterRowIndex i) j) = (integerCharacterTable i j : ℂ) := by
  have him : (RepresentationTheory.Group.PermutationSubgroupData.indexedTable (selectedCharacterRowIndex i) j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (RepresentationTheory.Group.PermutationSubgroupData.indexedTable (selectedCharacterRowIndex i) j).re = ((integerCharacterTable i j : ℤ) : ℚ) := by
    fin_cases i <;> fin_cases j <;> decide
  rw [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, him, hre]; push_cast; ring


end



end RepresentationTheory.AlternatingTensorSquare
