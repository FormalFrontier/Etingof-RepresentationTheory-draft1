/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryFiniteFieldRepresentations
import RepresentationTheory.FiniteFieldMatrixCharacterValues
import RepresentationTheory.FDRep.Biproduct
import RepresentationTheory.Alignment.Attribute



open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace RepresentationTheory.FiniteFieldMatrixCharacterFormulas

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

/-- A decidable equality instance for the finite Galois field. -/
local instance (priority := low) galoisFieldDecidableEq : DecidableEq (GaloisField p n) := Classical.decEq _
/-- A decidability choice for arbitrary propositions. -/
local instance (priority := low) propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

private abbrev GL2 (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)


-- ============================================================
-- The coset form of the principal-series character
-- ============================================================

/-- The complex-linear map from the auxiliary subtype to functions on optional field parameters. -/
def functionModelLinearMap (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) where
  toFun f i := (f : GL2 p n → ℂ) (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i)
  map_add' _ _ := funext fun _ => rfl
  map_smul' _ _ := funext fun _ => rfl

/-- The function-model linear map is bijective. -/
lemma functionModelLinearMap_bijective (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Function.Bijective (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearMap p n chi1 chi2) := by
  constructor
  · intro f g hfg
    have h : f - g = 0 :=
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmodule_ext p n chi1 chi2 (f - g) fun i => by
        have := congr_fun hfg i
        simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearMap, LinearMap.coe_mk, AddHom.coe_mk] at this
        simpa using sub_eq_zero.mpr this
    exact sub_eq_zero.mp h
  · intro c
    exact ⟨⟨RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup p n chi1 chi2 c,
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩,
      funext fun i => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c i⟩

/-- A complex-linear equivalence from the auxiliary subtype to functions on optional field parameters. -/
def functionModelLinearEquiv (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmodule p n chi1 chi2) ≃ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
  LinearEquiv.ofBijective _ (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearMap_bijective p n chi1 chi2)

/-- The value underlying the inverse function-model equivalence equals the specified function. -/
lemma functionModelLinearEquiv_symm_apply (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2).symm c : GL2 p n → ℂ) =
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup p n chi1 chi2 c := by
  have h : (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2).symm c =
      ⟨RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup p n chi1 chi2 c,
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩ := by
    apply (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (funext fun i => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c i).symm
  rw [h]

/-- Writes the two-parameter auxiliary representation character as a sum over optional field parameters. -/
theorem character_auxTwoParameter_eq_sum [Fintype (GaloisField p n)]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n chi1 chi2).character g =
      ∑ i : Option (GaloisField p n),
        if RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) = i then
          RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2
            (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g))
        else 0 := by
  change LinearMap.trace ℂ ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmodule p n chi1 chi2)
      (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmoduleRepresentation p n chi1 chi2 g) = _
  rw [← LinearMap.trace_conj' (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmoduleRepresentation p n chi1 chi2 g)
      (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2),
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Option (GaloisField p n)))]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    LinearEquiv.conj_apply]
  have hval : ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2)
      (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubmoduleRepresentation p n chi1 chi2 g
        ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2).symm (Pi.single i 1)))) i =
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup p n chi1 chi2 (Pi.single i 1)
        (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) := by
    rw [show (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2) = fun f => RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearMap p n chi1 chi2 f from
      rfl]
    simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    change ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv p n chi1 chi2).symm (Pi.single i 1) : GL2 p n → ℂ)
      (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) = _
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.functionModelLinearEquiv_symm_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hval ⊢
  rw [hval, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryFunctionOnGroup, Pi.single_apply]
  by_cases h : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) = i <;> simp [h]

-- ============================================================
-- The bijection `G ≃ B × P¹` and the order of `B`
-- ============================================================

/-- An equivalence between the finite-field matrix group and the product of the distinguished subtype with an optional field parameter. -/
def matrixGroupEquivSubtypeProd :
    GL2 p n ≃ ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) × Option (GaloisField p n) where
  toFun x := (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n x, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n x)
  invFun bi := bi.1.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n bi.2
  left_inv x := (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap_decomposition p n x).symm
  right_inv := by
    rintro ⟨b, i⟩
    have h1 : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (b.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i) = i := by
      rw [RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap_mul, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap_auxiliaryElement]
    have h2 : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (b.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i) = b := by
      rw [RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap_mul, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap_auxiliaryElement]
      exact Subtype.ext (by simp)
    exact Prod.ext h2 h1

/-- An equivalence from the distinguished subtype to two unit parameters and one field parameter. -/
def subtypeEquivUnitsProd :
    ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) ≃
      (GaloisField p n)ˣ × (GaloisField p n)ˣ × GaloisField p n where
  toFun b :=
    (Units.mk0 _ (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_eval_zero_zero_ne_zero p n b),
     Units.mk0 _ (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_eval_one_one_ne_zero p n b),
     (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1)
  invFun adc :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(adc.1 : GaloisField p n), adc.2.2; 0, (adc.2.1 : GaloisField p n)]
        (by simp [Matrix.det_fin_two]),
      by
        change ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(adc.1 : GaloisField p n), adc.2.2; 0, (adc.2.1 : GaloisField p n)]
          (by simp [Matrix.det_fin_two])).val :
            Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible]⟩
  left_inv b := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, hb10]
  right_inv adc := by
    obtain ⟨a, d, c⟩ := adc
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_) <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible]

/-- The distinguished subtype has cardinality equal to the field cardinality times the square of one less than it. -/
theorem card_distinguishedSubtype [Fintype (GaloisField p n)]
    [Fintype ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)] :
    Fintype.card ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) =
      (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n) := by
  rw [Fintype.card_congr (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.subtypeEquivUnitsProd p n), Fintype.card_prod,
    Fintype.card_prod, Fintype.card_units]
  ring

-- ============================================================
-- Deliverable 1 : the character of the principal series is `charVα₁`
-- ============================================================

/-- The auxiliary character on the distinguished subtype is invariant under internal conjugation. -/
lemma auxCharacter_conj (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b y : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)) :
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 (b * y * b⁻¹) =
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 y := by
  have hmul : ∀ u v : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n),
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 (u * v) =
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 u *
          RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 v := fun u v =>
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction_mul p n chi1 chi2 u v
  have hone : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 1 = 1 :=
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction_one p n chi1 chi2
  have hinv : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b *
      RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel, hone]
  rw [hmul, hmul]
  calc RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b *
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 y *
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b⁻¹
      = (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b *
          RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 b⁻¹) *
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 y := by ring
    _ = RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 y := by rw [hinv, one_mul]

/-- The complex-valued auxiliary function on the finite-field matrix group associated with two unit characters. -/
def auxCharacterExtension (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (y : GL2 p n) : ℂ :=
  if h : y ∈ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n then
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2 ⟨y, h⟩
  else 0

/-- The auxiliary character extension is invariant under conjugation by an element of the distinguished subtype. -/
lemma auxCharacterExtension_conj_mem (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)) (y : GL2 p n) :
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2 (b.val * y * b.val⁻¹) =
      RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2 y := by
  simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension]
  by_cases hy : y ∈ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n
  · have hc : b.val * y * b.val⁻¹ ∈ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n :=
      (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).mul_mem
        ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).mul_mem b.prop hy)
        ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).inv_mem b.prop)
    rw [dif_pos hc, dif_pos hy]
    have := RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacter_conj p n chi1 chi2 b ⟨y, hy⟩
    rw [← this]
    congr 1
  · have hc : b.val * y * b.val⁻¹ ∉ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n := by
      intro hmem
      apply hy
      have : y = b.val⁻¹ * (b.val * y * b.val⁻¹) * b.val := by group
      rw [this]
      exact (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).mul_mem
        ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).mul_mem
          ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n).inv_mem b.prop) hmem) b.prop
    rw [dif_neg hc, dif_neg hy]

/-- Evaluates the auxiliary character extension after conjugation by the group element associated with an optional field parameter. -/
lemma auxCharacterExtension_conj_parameterElement (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (i : Option (GaloisField p n)) :
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2
        (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g * (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i)⁻¹) =
      if RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) = i then
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2
          (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g))
      else 0 := by
  set r := RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i with hr
  have hdecomp := RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap_decomposition p n (r * g)
  by_cases h : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (r * g) = i
  · rw [if_pos h]
    have hrg : r * g = (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (r * g)).val * r := by
      conv_lhs => rw [hdecomp]
      rw [h]
    have hb : r * g * r⁻¹ = (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (r * g)).val := by
      conv_lhs => rw [hrg]
      rw [mul_inv_cancel_right]
    have hmem : r * g * r⁻¹ ∈ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n := by
      rw [hb]; exact (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (r * g)).prop
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension, dif_pos hmem]
    congr 1
    exact Subtype.ext hb
  · rw [if_neg h, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension, dif_neg]
    intro hmem
    apply h
    have h1 := RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap_mul p n
      (⟨r * g * r⁻¹, hmem⟩ : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)) r
    simp only [inv_mul_cancel_right] at h1
    rw [h1, hr, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap_auxiliaryElement]

/-- The sum of all conjugates of the auxiliary character extension equals the subtype cardinality times the associated representation character. -/
theorem sum_conjugates_auxCharacterExtension
    [Fintype (GL2 p n)]
    [Fintype ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    ∑ x : GL2 p n, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2 (x * g * x⁻¹) =
      (Fintype.card ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) : ℂ) *
        (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n chi1 chi2).character g := by
  rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxTwoParameter_eq_sum]
  rw [← Equiv.sum_comp (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.matrixGroupEquivSubtypeProd p n).symm
    (fun x => RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2 (x * g * x⁻¹))]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ (b : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)) (i : Option (GaloisField p n)),
      RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n chi1 chi2
        ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.matrixGroupEquivSubtypeProd p n).symm (b, i) * g *
          ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.matrixGroupEquivSubtypeProd p n).symm (b, i))⁻¹) =
      if RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g) = i then
        RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n chi1 chi2
          (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroupMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g))
      else 0 := by
    intro b i
    have hx : (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.matrixGroupEquivSubtypeProd p n).symm (b, i) =
        b.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i := rfl
    rw [hx]
    have hrw : b.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g *
        (b.val * RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i)⁻¹ =
        b.val * (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i * g * (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n i)⁻¹) * b.val⁻¹ := by
      group
    rw [hrw, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension_conj_mem, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension_conj_parameterElement]
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Identifies the character of the two-parameter auxiliary representation with trivial second parameter. -/
@[source_ref "Chapter5/Discussion_5.25.3" (role := primary)]
theorem character_auxTwoParameter_rightOne
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n alpha 1).character g =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction p n alpha g := by
  classical
  -- The summand of `charVα₁` is the Borel character extended by zero.
  have hsummand : ∀ x : GL2 p n,
      (if ((x⁻¹ * g * x : GL2 p n).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then
        (if h : ((x⁻¹ * g * x : GL2 p n).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0
          then (alpha (Units.mk0 _ h) : ℂ) else 0)
      else 0) = RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n alpha 1 (x⁻¹ * g * x) := by
    intro x
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension]
    by_cases hx : (x⁻¹ * g * x : GL2 p n) ∈ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n
    · have hx' : ((x⁻¹ * g * x : GL2 p n).val :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := hx
      have h00 := RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_eval_zero_zero_ne_zero p n ⟨_, hx⟩
      rw [dif_pos hx, if_pos hx', dif_pos h00, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction]
      simp
    · have hx' : ¬ ((x⁻¹ * g * x : GL2 p n).val :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := hx
      rw [dif_neg hx, if_neg hx']
  -- Move from `x⁻¹ g x` to `x g x⁻¹` and apply the Frobenius formula.
  have hsum : ∑ x : GL2 p n, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacterExtension p n alpha 1 (x⁻¹ * g * x) =
      (Fintype.card ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) : ℂ) *
        (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n alpha 1).character g := by
    rw [← RepresentationTheory.FiniteFieldMatrixCharacterFormulas.sum_conjugates_auxCharacterExtension p n alpha 1 g]
    exact Fintype.sum_equiv (Equiv.inv (GL2 p n)) _ _ fun x => by simp
  rw [RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction]
  simp only [hsummand, hsum]
  have hcard : ((((Fintype.card (GaloisField p n) - 1) ^ 2 *
      Fintype.card (GaloisField p n) : ℕ) : ℂ)) =
      (Fintype.card ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n) : ℂ) := by
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.card_distinguishedSubtype]
  rw [hcard, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_pos (α := ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n))).ne'

-- ============================================================
-- Deliverable 2 : the character of `W₁` is `charW₁`
-- ============================================================

/-- The auxiliary character attached to two trivial unit characters has constant value one. -/
lemma auxCharacter_one_one (b : ↥(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliarySubgroup p n)) :
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction p n 1 1 b = 1 := by
  simp [RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryComplexFunction]

/-- Evaluates an auxiliary representation character by applying the unit character to the matrix determinant. -/
lemma character_auxDeterminantFamily (mu : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).character g =
      ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  change LinearMap.trace ℂ ℂ
    (((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- Expresses the character of the one-parameter auxiliary representation as a difference of two representation characters. -/
lemma character_auxFamily_eq_sub (mu : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n mu).character g =
      (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n mu mu).character g -
        (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).character g := by
  obtain ⟨iso⟩ := RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_iso_biprod p n mu
  have h := congrFun (FDRep.char_iso iso) g
  rw [RepresentationTheory.FDRep.Biproduct.character_biprod] at h
  rw [h]; ring

/-- The `none` optional parameter is fixed exactly when the entry at indices (1, 0) vanishes. -/
lemma fixedParameter_none_iff (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n none * g) = none) ↔
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
  have hr : RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n none = 1 := rfl
  rw [hr, one_mul, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap]
  split_ifs with h <;> simp [h]

/-- Computes the entries at indices (1, 0) and (1, 1) after left multiplication by the element associated with a field parameter. -/
lemma parameterElement_mul_entries (t : GaloisField p n) (g : GL2 p n) :
    (((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n (some t) * g).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 =
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 +
        t * (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0) ∧
    (((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n (some t) * g).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 =
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1 +
        t * (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1) := by
  constructor <;>
    · simp [RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, Units.val_mul,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- A field-valued optional parameter is fixed exactly when the displayed quadratic expression in the matrix entries vanishes. -/
lemma fixedParameter_some_iff (t : GaloisField p n) (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap p n (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n (some t) * g) = some t) ↔
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 * t ^ 2 +
          ((g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 -
            (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1) * t -
          (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1 = 0 := by
  have hdet : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 *
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 -
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1 *
      (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 := by
    have h : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0 :=
      IsUnit.ne_zero ((Units.isUnit g).map Matrix.detMonoidHom)
    rwa [Matrix.det_fin_two] at h
  obtain ⟨h10, h11⟩ := RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterElement_mul_entries p n t g
  rw [RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOptionMap]
  by_cases hu : ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryElement p n (some t) * g).val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
  · rw [dif_pos hu]
    rw [h10] at hu
    constructor
    · intro hcon; exact absurd hcon (by simp)
    · intro hroot
      exact absurd (by
        linear_combination ((g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 -
          (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 * t) * hu +
          (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 * hroot) hdet
  · rw [dif_neg hu, h10, h11]
    rw [h10] at hu
    rw [Option.some_inj, div_eq_iff hu]
    constructor <;> intro h <;> linear_combination -h

/-- The auxiliary self-map of the optional finite-field parameter space. -/
def parameterInvolution : Option (GaloisField p n) → Option (GaloisField p n)
  | none => some 0
  | some t => if t = 0 then none else some (-t⁻¹)

/-- The auxiliary self-map on optional field parameters is involutive. -/
lemma parameterInvolution_involutive : Function.Involutive (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution p n) := by
  rintro (_ | t)
  · simp [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution]
  · by_cases ht : t = 0
    · simp [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution, ht]
    · have h1 : -t⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht)
      simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution, if_neg ht, if_neg h1]
      rw [inv_neg, inv_inv, neg_neg]

/-- An equivalence of the type of optional field parameters. -/
def optionFieldEquiv : Option (GaloisField p n) ≃ Option (GaloisField p n) :=
  Function.Involutive.toPerm _ (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution_involutive p n)

/-- A complex-valued function of three field arguments and one optional field argument. -/
def parameterFunction [DecidableEq (GaloisField p n)] (a b c : GaloisField p n) :
    Option (GaloisField p n) → ℂ
  | none => if a = 0 then 1 else 0
  | some t => if a * t ^ 2 + b * t - c = 0 then 1 else 0

/-- Applying the parameter involution while exchanging the first and third field arguments preserves the parameter function. -/
lemma parameterFunction_involution [DecidableEq (GaloisField p n)]
    (a b c : GaloisField p n) (i : Option (GaloisField p n)) :
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n c b a (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution p n i) =
      RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n a b c i := by
  rcases i with _ | t
  · simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction]
    simp [neg_eq_zero]
  · by_cases ht : t = 0
    · subst ht
      simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction]
      simp [neg_eq_zero]
    · simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterInvolution, if_neg ht, RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction]
      have hexp : c * (-t⁻¹) ^ 2 + b * (-t⁻¹) - a = -(a * t ^ 2 + b * t - c) / t ^ 2 := by
        field_simp
        ring
      have hiff : (c * (-t⁻¹) ^ 2 + b * (-t⁻¹) - a = 0) ↔ (a * t ^ 2 + b * t - c = 0) := by
        rw [hexp, div_eq_zero_iff, neg_eq_zero]
        simp [pow_ne_zero 2 ht]
      simp only [hiff]

/-- The sum of the parameter function is unchanged when the first and third field arguments are exchanged. -/
lemma sum_parameterFunction_swap [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (a b c : GaloisField p n) :
    ∑ i : Option (GaloisField p n), RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n a b c i =
      ∑ i : Option (GaloisField p n), RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n c b a i := by
  rw [← Equiv.sum_comp (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.optionFieldEquiv p n) (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n c b a)]
  exact Finset.sum_congr rfl fun i _ =>
    (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction_involution p n a b c i).symm

/-- Identifies the character of the auxiliary representation at the trivial unit character with a specified complex-valued function. -/
@[source_ref "Chapter5/Discussion_5.25.3" (role := primary)]
theorem character_auxFamily_one [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n 1).character g =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction p n g := by
  classical
  -- `charW₁` in the shape produced below: an affine root count plus the point at infinity.
  have hW : RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction p n g =
      (if (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1 = 0 then (1 : ℂ) else 0) +
        ((Finset.univ.filter fun t : GaloisField p n =>
            (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1 * t ^ 2 +
              ((g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 -
                (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1) * t -
              (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0).card : ℂ) - 1 := by
    simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction]
    split_ifs with h <;> push_cast <;> ring
  set M := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) with hM
  -- The character of `V(1,1)` counts the points of `P¹` fixed by `g`.
  have hchar : (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n 1 1).character g =
      ∑ i : Option (GaloisField p n),
        RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction p n (M 1 0) (M 0 0 - M 1 1) (M 0 1) i := by
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxTwoParameter_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.auxCharacter_one_one]
    rcases i with _ | t
    · rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction]
      by_cases h : M 1 0 = 0
      · rw [if_pos ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.fixedParameter_none_iff p n g).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.fixedParameter_none_iff p n g).mp hc)),
          if_neg h]
    · rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction]
      by_cases h : M 1 0 * t ^ 2 + (M 0 0 - M 1 1) * t - M 0 1 = 0
      · rw [if_pos ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.fixedParameter_some_iff p n t g).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((RepresentationTheory.FiniteFieldMatrixCharacterFormulas.fixedParameter_some_iff p n t g).mp hc)),
          if_neg h]
  rw [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxFamily_eq_sub, hchar,
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.sum_parameterFunction_swap p n (M 1 0) (M 0 0 - M 1 1) (M 0 1),
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxDeterminantFamily, Fintype.sum_option, hW]
  simp only [RepresentationTheory.FiniteFieldMatrixCharacterFormulas.parameterFunction, Finset.sum_boole, MonoidHom.one_apply, Units.val_one]

/-- The complex dimension of the auxiliary representation at the trivial unit character equals the field cardinality. -/
theorem finrank_auxFamily_one [Fintype (GaloisField p n)] :
    Module.finrank ℂ (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n 1).V = Fintype.card (GaloisField p n) := by
  classical
  have hscalar : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) 1 := by
    rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [(by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)]
  have h := (RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxFamily_one p n (1 : GL2 p n)).symm
  rw [RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction_eq_card_of_auxiliaryProperty
    p n 1 hscalar, FDRep.char_one] at h
  exact_mod_cast h.symm

end RepresentationTheory.FiniteFieldMatrixCharacterFormulas

end
