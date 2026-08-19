/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.RingQuot
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

/-! # Representations of a rank-one quantum algebra -/

namespace RepresentationTheory.QuantumGroup.SL2Representations

/-- An auxiliary type indexing the generators of the free algebra used in the presentation. -/
abbrev Generator := Fin 4

/-- A third auxiliary element of the free algebra on the generator type. -/
noncomputable abbrev auxiliaryFreeAlgebraElementThree : FreeAlgebra ℂ Generator := FreeAlgebra.ι ℂ (0 : Fin 4)

/-- A fourth auxiliary element of the free algebra on the generator type. -/
noncomputable abbrev auxiliaryFreeAlgebraElementFour : FreeAlgebra ℂ Generator := FreeAlgebra.ι ℂ (1 : Fin 4)

/-- An auxiliary element of the free algebra on the generator type. -/
noncomputable abbrev auxiliaryFreeAlgebraElementOne : FreeAlgebra ℂ Generator := FreeAlgebra.ι ℂ (2 : Fin 4)

/-- A second auxiliary element of the free algebra on the generator type. -/
noncomputable abbrev auxiliaryFreeAlgebraElementTwo : FreeAlgebra ℂ Generator := FreeAlgebra.ι ℂ (3 : Fin 4)

/-- The parameter-dependent relations on pairs of elements of the free algebra. -/
inductive Relations (q : ℂˣ) : FreeAlgebra ℂ Generator → FreeAlgebra ℂ Generator → Prop
  /-- The product of the first auxiliary element and the second is related to one. -/
  | weight_inverse : Relations q (auxiliaryFreeAlgebraElementOne * auxiliaryFreeAlgebraElementTwo) 1
  /-- The product of the second auxiliary element and the first is related to one. -/
  | inverse_weight : Relations q (auxiliaryFreeAlgebraElementTwo * auxiliaryFreeAlgebraElementOne) 1
  /-- Moving the first auxiliary element past the third introduces the squared parameter. -/
  | weight_raising : Relations q (auxiliaryFreeAlgebraElementOne * auxiliaryFreeAlgebraElementThree) (((q : ℂ) ^ 2) • (auxiliaryFreeAlgebraElementThree * auxiliaryFreeAlgebraElementOne))
  /-- Moving the first auxiliary element past the fourth introduces the inverse squared parameter. -/
  | weight_lowering : Relations q (auxiliaryFreeAlgebraElementOne * auxiliaryFreeAlgebraElementFour) (((q : ℂ) ^ 2)⁻¹ • (auxiliaryFreeAlgebraElementFour * auxiliaryFreeAlgebraElementOne))
  /-- The scaled commutator of the third and fourth auxiliary elements is related to the
  difference of the first two. -/
  | raising_lowering : Relations q (((q : ℂ) - (q : ℂ)⁻¹) • (auxiliaryFreeAlgebraElementThree * auxiliaryFreeAlgebraElementFour - auxiliaryFreeAlgebraElementFour * auxiliaryFreeAlgebraElementThree)) (auxiliaryFreeAlgebraElementOne - auxiliaryFreeAlgebraElementTwo)

/-- The complex algebra determined by the displayed parameter-dependent rank-one relations. -/
noncomputable abbrev QuantumSL2 (q : ℂˣ) : Type := RingQuot (Relations q)

/-- A complex algebra homomorphism from the free algebra to the parameterized algebra. -/
noncomputable def freeAlgebraMap (q : ℂˣ) : FreeAlgebra ℂ Generator →ₐ[ℂ] QuantumSL2 q := RingQuot.mkAlgHom ℂ (Relations q)

/-- The raising element of the parameterized algebra. -/
noncomputable def raisingElement (q : ℂˣ) : QuantumSL2 q := freeAlgebraMap q auxiliaryFreeAlgebraElementThree

/-- The lowering element of the parameterized algebra. -/
noncomputable def loweringElement (q : ℂˣ) : QuantumSL2 q := freeAlgebraMap q auxiliaryFreeAlgebraElementFour

/-- The weight element of the parameterized algebra. -/
noncomputable def weightElement (q : ℂˣ) : QuantumSL2 q := freeAlgebraMap q auxiliaryFreeAlgebraElementOne

/-- The inverse weight element of the parameterized algebra. -/
noncomputable def inverseWeightElement (q : ℂˣ) : QuantumSL2 q := freeAlgebraMap q auxiliaryFreeAlgebraElementTwo

/-- The weight element multiplied by its inverse element is one. -/
@[simp] lemma weightElement_mul_inverseWeightElement (q : ℂˣ) : weightElement q * inverseWeightElement q = 1 := by
  have h := RingQuot.mkAlgHom_rel ℂ (Relations.weight_inverse (q := q)); simp only [map_mul, map_one] at h; exact h

/-- The inverse weight element multiplied by the weight element is one. -/
@[simp] lemma inverseWeightElement_mul_weightElement (q : ℂˣ) : inverseWeightElement q * weightElement q = 1 := by
  have h := RingQuot.mkAlgHom_rel ℂ (Relations.inverse_weight (q := q)); simp only [map_mul, map_one] at h; exact h

/-- Moving the weight element past the raising element introduces the square of the parameter. -/
@[simp] lemma weightElement_mul_raisingElement (q : ℂˣ) : weightElement q * raisingElement q = ((q : ℂ) ^ 2) • (raisingElement q * weightElement q) := by
  have h := RingQuot.mkAlgHom_rel ℂ (Relations.weight_raising (q := q)); simp only [map_mul, map_smul] at h; exact h

/-- Moving the weight element past the lowering element introduces the inverse square of the parameter. -/
@[simp] lemma weightElement_mul_loweringElement (q : ℂˣ) : weightElement q * loweringElement q = ((q : ℂ) ^ 2)⁻¹ • (loweringElement q * weightElement q) := by
  have h := RingQuot.mkAlgHom_rel ℂ (Relations.weight_lowering (q := q)); simp only [map_mul, map_smul] at h; exact h

/-- Scaling the raising-lowering commutator by the difference of the parameter and its inverse gives the difference of the weight elements. -/
@[simp] lemma parameterDifference_smul_commutator (q : ℂˣ) :
    ((q : ℂ) - (q : ℂ)⁻¹) • (raisingElement q * loweringElement q - loweringElement q * raisingElement q) = weightElement q - inverseWeightElement q := by
  have h := RingQuot.mkAlgHom_rel ℂ (Relations.raising_lowering (q := q))
  simp only [map_smul, map_sub, map_mul] at h; exact h

private noncomputable def complexCharacterOnGenerator : Generator → ℂ := ![0, 0, 1, 1]

private noncomputable def complexCharacterFree : FreeAlgebra ℂ Generator →ₐ[ℂ] ℂ :=
  FreeAlgebra.lift ℂ complexCharacterOnGenerator

private theorem complexCharacterFree_respectsRelations (q : ℂˣ) :
    ∀ ⦃a b⦄, Relations q a b → complexCharacterFree a = complexCharacterFree b := by
  rintro _ _ h
  cases h <;> simp [complexCharacterFree, complexCharacterOnGenerator]

/-- A complex algebra homomorphism from the parameterized algebra to the complex numbers. -/
noncomputable def complexCharacter (q : ℂˣ) : QuantumSL2 q →ₐ[ℂ] ℂ :=
  RingQuot.liftAlgHom ℂ ⟨complexCharacterFree, complexCharacterFree_respectsRelations q⟩

/-- The distinguished complex-valued algebra homomorphism is surjective. -/
theorem complexCharacter_surjective (q : ℂˣ) : Function.Surjective (complexCharacter q) := by
  intro z
  refine ⟨algebraMap ℂ (QuantumSL2 q) z, ?_⟩
  exact (complexCharacter q).commutes z

/-- The parameterized algebra is nontrivial. -/
noncomputable instance quantumSL2_nontrivial (q : ℂˣ) : Nontrivial (QuantumSL2 q) :=
  (complexCharacter_surjective q).nontrivial

/-- For a parameter of infinite order and a nonzero scalar, multiplication by successive even powers of the parameter is injective in the exponent. -/
lemma injective_evenPower_mul_of_infiniteOrder (q : ℂˣ) (hq : ¬ IsOfFinOrder q) (μ₀ : ℂ) (hμ₀ : μ₀ ≠ 0) :
    Function.Injective (fun n : ℕ => (q : ℂ) ^ (2 * n) * μ₀) := by
  intro a b hab
  simp only at hab
  have h : (q : ℂ) ^ (2 * a) = (q : ℂ) ^ (2 * b) := mul_right_cancel₀ hμ₀ hab
  have hu : q ^ (2 * a) = q ^ (2 * b) := by
    apply Units.ext; push_cast; simpa using h
  have hinj : Function.Injective (fun n : ℕ => q ^ n) :=
    injective_pow_iff_not_isOfFinOrder.mpr hq
  have : 2 * a = 2 * b := hinj hu
  omega

section HighestWeight

variable (q : ℂˣ)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
  [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V]

/-- The complex-linear endomorphism induced by the action of the weight element. -/
noncomputable def weightActionEnd : Module.End ℂ V where
  toFun v := weightElement q • v
  map_add' := by intro x y; simp [smul_add]
  map_smul' := by intro c v; exact smul_comm (weightElement q) c v

omit [FiniteDimensional ℂ V] in

/-- The weight-action endomorphism evaluates as scalar action by the weight element. -/
@[simp] lemma weightActionEnd_apply (v : V) : weightActionEnd q V v = weightElement q • v := rfl

omit [FiniteDimensional ℂ V] in

/-- Applying the raising element to a weight eigenvector multiplies its eigenvalue by the square of the parameter. -/
lemma weightActionEnd_smul_raisingElement (μ : ℂ) (w : V) (hw : weightActionEnd q V w = μ • w) :
    weightActionEnd q V (raisingElement q • w) = ((q : ℂ) ^ 2 * μ) • (raisingElement q • w) := by
  simp only [weightActionEnd_apply] at hw ⊢
  have h1 : weightElement q • (raisingElement q • w) = (weightElement q * raisingElement q) • w := by rw [mul_smul]
  rw [h1, weightElement_mul_raisingElement, smul_assoc, mul_smul, hw, smul_comm (raisingElement q) μ w, smul_smul]

omit [FiniteDimensional ℂ V] in

/-- Applying the lowering element to a weight eigenvector multiplies its eigenvalue by the inverse square of the parameter. -/
lemma weightActionEnd_smul_loweringElement (μ : ℂ) (w : V) (hw : weightActionEnd q V w = μ • w) :
    weightActionEnd q V (loweringElement q • w) = (((q : ℂ) ^ 2)⁻¹ * μ) • (loweringElement q • w) := by
  simp only [weightActionEnd_apply] at hw ⊢
  have h1 : weightElement q • (loweringElement q • w) = (weightElement q * loweringElement q) • w := by rw [mul_smul]
  rw [h1, weightElement_mul_loweringElement, smul_assoc, mul_smul, hw, smul_comm (loweringElement q) μ w, smul_smul]

omit [FiniteDimensional ℂ V] in

/-- Every eigenvalue of the weight-action endomorphism is nonzero. -/
lemma weightActionEnd_eigenvalue_ne_zero (μ : ℂ) (hμ : (weightActionEnd q V).HasEigenvalue μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hKv : weightElement q • v = 0 := by
    have := Module.End.mem_eigenspace_iff.mp hv; simpa using this
  have : v = 0 := by
    have h := congrArg (fun x => inverseWeightElement q • x) hKv
    simp only [smul_zero] at h
    rw [← mul_smul, inverseWeightElement_mul_weightElement, one_smul] at h
    exact h
  exact hv0 this

/-- A nontrivial finite-dimensional module at an infinite-order parameter has a weight eigenvalue whose shift by the squared parameter is not an eigenvalue. -/
lemma exists_weightEigenvalue_not_shifted_of_infiniteOrder (hq : ¬ IsOfFinOrder q) [Nontrivial V] :
    ∃ μ : ℂ, (weightActionEnd q V).HasEigenvalue μ ∧ ¬ (weightActionEnd q V).HasEigenvalue ((q : ℂ) ^ 2 * μ) := by
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (weightActionEnd q V)
  by_contra hcon
  have h_all : ∀ μ : ℂ, (weightActionEnd q V).HasEigenvalue μ → (weightActionEnd q V).HasEigenvalue ((q : ℂ) ^ 2 * μ) := by
    intro μ hμ; by_contra hne; exact hcon ⟨μ, hμ, hne⟩
  have h_chain : ∀ n : ℕ, (weightActionEnd q V).HasEigenvalue ((q : ℂ) ^ (2 * n) * μ₀) := by
    intro n; induction n with
    | zero => simpa using hμ₀
    | succ n ih =>
        have hh := h_all _ ih
        have heq : (q : ℂ) ^ (2 * (n + 1)) * μ₀ = (q : ℂ) ^ 2 * ((q : ℂ) ^ (2 * n) * μ₀) := by ring
        rw [heq]; exact hh
  have h_inj := injective_evenPower_mul_of_infiniteOrder q hq μ₀ (weightActionEnd_eigenvalue_ne_zero q V μ₀ hμ₀)
  have h_li := Module.End.eigenvectors_linearIndependent' (weightActionEnd q V)
    (fun n : ℕ => (q : ℂ) ^ (2 * n) * μ₀) h_inj
    (fun n => (h_chain n).exists_hasEigenvector.choose)
    (fun n => (h_chain n).exists_hasEigenvector.choose_spec)
  exact Module.Finite.not_linearIndependent_of_infinite _ h_li

/-- A nontrivial finite-dimensional module at an infinite-order parameter has a nonzero weight eigenvector annihilated by the raising element. -/
theorem exists_ne_zero_raising_annihilated_weightEigenvector (hq : ¬ IsOfFinOrder q) [Nontrivial V] :
    ∃ (v : V) (lam : ℂ), v ≠ 0 ∧ raisingElement q • v = 0 ∧ weightElement q • v = lam • v := by
  obtain ⟨μ, hμ, hμ2⟩ := exists_weightEigenvalue_not_shifted_of_infiniteOrder q V hq
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨v, μ, hv.2, ?_, ?_⟩
  · 
    by_contra he
    apply hμ2
    have hmem : weightActionEnd q V (raisingElement q • v) = ((q : ℂ) ^ 2 * μ) • (raisingElement q • v) :=
      weightActionEnd_smul_raisingElement q V μ v (Module.End.mem_eigenspace_iff.mp hv.1)
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hmem, he⟩
  · have := Module.End.mem_eigenspace_iff.mp hv.1
    simpa using this

end HighestWeight

/-- No positive power of an infinite-order complex unit is one. -/
lemma pow_ne_one_of_infiniteOrder (q : ℂˣ) (hq : ¬ IsOfFinOrder q) {n : ℕ} (hn : 0 < n) : (q : ℂ) ^ n ≠ 1 := by
  intro h
  refine hq (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩)
  apply Units.ext
  push_cast
  simpa using h

/-- The square of an infinite-order complex unit is not one. -/
lemma sq_ne_one_of_infiniteOrder (q : ℂˣ) (hq : ¬ IsOfFinOrder q) : (q : ℂ) ^ 2 ≠ 1 :=
  pow_ne_one_of_infiniteOrder q hq (by norm_num)

/-- An infinite-order complex unit differs from its inverse. -/
lemma sub_inv_ne_zero_of_infiniteOrder (q : ℂˣ) (hq : ¬ IsOfFinOrder q) : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := by
  intro h
  have h2 : (q : ℂ) = (q : ℂ)⁻¹ := sub_eq_zero.mp h
  have : (q : ℂ) ^ 2 = 1 := by
    rw [sq]; nth_rewrite 2 [h2]; exact mul_inv_cancel₀ q.ne_zero
  exact sq_ne_one_of_infiniteOrder q hq this

section Ladder

variable (q : ℂˣ)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
  [IsScalarTower ℂ (QuantumSL2 q) V]

/-- The sequence obtained by iterating the action of the lowering element on a vector. -/
noncomputable def loweringIterate (v : V) (i : ℕ) : V := (loweringElement q) ^ i • v

/-- The sequence of weight eigenvalues associated with successive lowering iterates. -/
noncomputable def loweringWeight (lam : ℂ) (i : ℕ) : ℂ := lam * (((q : ℂ) ^ 2)⁻¹) ^ i

omit [Module ℂ V] [IsScalarTower ℂ (QuantumSL2 q) V] in

/-- The zeroth lowering iterate is the original vector. -/
@[simp] lemma loweringIterate_zero (v : V) : loweringIterate q V v 0 = v := by simp [loweringIterate]

omit [Module ℂ V] [IsScalarTower ℂ (QuantumSL2 q) V] in

/-- The next lowering iterate is obtained by applying the lowering element. -/
lemma loweringIterate_succ (v : V) (i : ℕ) : loweringIterate q V v (i + 1) = loweringElement q • loweringIterate q V v i := by
  simp only [loweringIterate, pow_succ', mul_smul]

/-- The zeroth lowering weight is the initial scalar. -/
@[simp] lemma loweringWeight_zero (lam : ℂ) : loweringWeight q lam 0 = lam := by simp [loweringWeight]

/-- Every term of the lowering-weight sequence from a nonzero initial scalar is nonzero. -/
lemma loweringWeight_ne_zero (lam : ℂ) (hlam : lam ≠ 0) (i : ℕ) : loweringWeight q lam i ≠ 0 := by
  apply mul_ne_zero hlam
  exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ q.ne_zero))

/-- The weight element acts on each lowering iterate with the corresponding shifted eigenvalue. -/
lemma weightElement_smul_loweringIterate (v : V) (lam : ℂ) (hKv : weightElement q • v = lam • v) (i : ℕ) :
    weightElement q • loweringIterate q V v i = loweringWeight q lam i • loweringIterate q V v i := by
  induction i with
  | zero => simpa [loweringWeight] using hKv
  | succ n ih =>
    rw [loweringIterate_succ, ← mul_smul, weightElement_mul_loweringElement, smul_assoc, mul_smul, ih,
      smul_comm (loweringElement q) (loweringWeight q lam n), smul_smul]
    congr 1
    simp only [loweringWeight, pow_succ]
    ring

/-- The inverse weight element acts on each lowering iterate by the inverse shifted eigenvalue. -/
lemma inverseWeightElement_smul_loweringIterate (v : V) (lam : ℂ) (hlam : lam ≠ 0) (hKv : weightElement q • v = lam • v) (i : ℕ) :
    inverseWeightElement q • loweringIterate q V v i = (loweringWeight q lam i)⁻¹ • loweringIterate q V v i := by
  have hK := weightElement_smul_loweringIterate q V v lam hKv i
  have hmu := loweringWeight_ne_zero q lam hlam i
  have h1 : inverseWeightElement q • (weightElement q • loweringIterate q V v i) = loweringIterate q V v i := by
    rw [← mul_smul, inverseWeightElement_mul_weightElement, one_smul]
  rw [hK, smul_comm (inverseWeightElement q) (loweringWeight q lam i)] at h1
  
  have := congrArg (fun x => (loweringWeight q lam i)⁻¹ • x) h1
  simp only [smul_smul, inv_mul_cancel₀ hmu, one_smul] at this
  exact this

/-- On a simultaneous weight and inverse-weight eigenvector, raising after lowering equals lowering after raising plus the indicated scalar action. -/
lemma raisingElement_smul_loweringElement_smul (hne : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (x : V) (a : ℂ)
    (hK : weightElement q • x = a • x) (hL : inverseWeightElement q • x = a⁻¹ • x) :
    raisingElement q • (loweringElement q • x) = loweringElement q • (raisingElement q • x) + (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (a - a⁻¹)) • x := by
  have expand : (weightElement q - inverseWeightElement q) • x = (a - a⁻¹) • x := by rw [sub_smul, sub_smul, hK, hL]
  have expand2 : (raisingElement q * loweringElement q - loweringElement q * raisingElement q) • x = raisingElement q • (loweringElement q • x) - loweringElement q • (raisingElement q • x) := by
    rw [sub_smul, mul_smul, mul_smul]
  have hrel := parameterDifference_smul_commutator q
  have h3 : ((q : ℂ) - (q : ℂ)⁻¹) • (raisingElement q • (loweringElement q • x) - loweringElement q • (raisingElement q • x)) = (a - a⁻¹) • x := by
    rw [← expand2, ← smul_assoc, hrel, expand]
  have hDiff : raisingElement q • (loweringElement q • x) - loweringElement q • (raisingElement q • x)
      = ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ • ((a - a⁻¹) • x) := by
    rw [← h3, inv_smul_smul₀ hne]
  rw [mul_smul, ← hDiff]
  abel

/-- The scalar coefficient governing the raising action on successive lowering iterates. -/
noncomputable def raisingOnLoweringPowerCoeff (lam : ℂ) (i : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (i + 1), ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (loweringWeight q lam j - (loweringWeight q lam j)⁻¹)

/-- On a vector killed by the raising element, raising the next lowering iterate yields the specified coefficient times the preceding iterate. -/
lemma raisingElement_smul_loweringIterate_succ (hne : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (v : V) (lam : ℂ) (hlam : lam ≠ 0)
    (he : raisingElement q • v = 0) (hKv : weightElement q • v = lam • v) (i : ℕ) :
    raisingElement q • loweringIterate q V v (i + 1) = raisingOnLoweringPowerCoeff q lam i • loweringIterate q V v i := by
  induction i with
  | zero =>
    rw [loweringIterate_succ,
      raisingElement_smul_loweringElement_smul q V hne (loweringIterate q V v 0) (loweringWeight q lam 0)
        (weightElement_smul_loweringIterate q V v lam hKv 0) (inverseWeightElement_smul_loweringIterate q V v lam hlam hKv 0)]
    have hev : raisingElement q • loweringIterate q V v 0 = 0 := by simpa using he
    rw [hev, smul_zero, zero_add, raisingOnLoweringPowerCoeff, Finset.sum_range_one]
  | succ n ih =>
    rw [loweringIterate_succ,
      raisingElement_smul_loweringElement_smul q V hne (loweringIterate q V v (n + 1)) (loweringWeight q lam (n + 1))
        (weightElement_smul_loweringIterate q V v lam hKv (n + 1)) (inverseWeightElement_smul_loweringIterate q V v lam hlam hKv (n + 1)),
      ih, smul_comm (loweringElement q) (raisingOnLoweringPowerCoeff q lam n), ← loweringIterate_succ, ← add_smul]
    congr 1
    have hstep : raisingOnLoweringPowerCoeff q lam (n + 1) = raisingOnLoweringPowerCoeff q lam n
        + ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (loweringWeight q lam (n + 1) - (loweringWeight q lam (n + 1))⁻¹) := by
      simp only [raisingOnLoweringPowerCoeff, Finset.sum_range_succ]
    rw [hstep]

/-- For a nonzero initial scalar and an infinite-order parameter, the lowering-weight sequence is injective. -/
lemma loweringWeight_injective_of_infiniteOrder (hq : ¬ IsOfFinOrder q) (lam : ℂ) (hlam : lam ≠ 0) :
    Function.Injective (loweringWeight q lam) := by
  intro a b hab
  simp only [loweringWeight] at hab
  have h : (((q : ℂ) ^ 2)⁻¹) ^ a = (((q : ℂ) ^ 2)⁻¹) ^ b := mul_left_cancel₀ hlam hab
  have hu_inf : ¬ IsOfFinOrder ((q ^ 2)⁻¹ : ℂˣ) := by
    rw [isOfFinOrder_inv_iff]
    intro hfin
    apply hq
    rw [isOfFinOrder_iff_pow_eq_one] at hfin ⊢
    obtain ⟨m, hm, hpow⟩ := hfin
    exact ⟨2 * m, by omega, by rw [pow_mul]; exact hpow⟩
  have hinj : Function.Injective (fun n : ℕ => ((q ^ 2)⁻¹ : ℂˣ) ^ n) :=
    injective_pow_iff_not_isOfFinOrder.mpr hu_inf
  have hu : ((q ^ 2)⁻¹ : ℂˣ) ^ a = ((q ^ 2)⁻¹ : ℂˣ) ^ b := by
    have hcast : (((q ^ 2)⁻¹ : ℂˣ) ^ a : ℂ) = (((q ^ 2)⁻¹ : ℂˣ) ^ b : ℂ) := by
      push_cast; exact h
    exact_mod_cast hcast
  exact hinj hu

end Ladder

/-- At an infinite-order parameter, vanishing of the raising-on-lowering coefficient forces the square of the eigenvalue to equal the indicated even power of the parameter. -/
lemma sq_eq_evenPower_of_raisingOnLoweringPowerCoeff_eq_zero (q : ℂˣ) (hq : ¬ IsOfFinOrder q) (lam : ℂ) (hlam : lam ≠ 0) (N : ℕ)
    (h : raisingOnLoweringPowerCoeff q lam N = 0) : lam ^ 2 = (q : ℂ) ^ (2 * N) := by
  have hqne : (q : ℂ) ≠ 0 := q.ne_zero
  have htne : (q : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hqne
  have hc : ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero (sub_inv_ne_zero_of_infiniteOrder q hq)
  rw [raisingOnLoweringPowerCoeff, ← Finset.mul_sum] at h
  have hS : ∑ j ∈ Finset.range (N + 1), (loweringWeight q lam j - (loweringWeight q lam j)⁻¹) = 0 :=
    (mul_eq_zero.mp h).resolve_left hc
  have hSexpand : ∑ j ∈ Finset.range (N + 1), (loweringWeight q lam j - (loweringWeight q lam j)⁻¹)
      = lam * (∑ j ∈ Finset.range (N + 1), (((q : ℂ) ^ 2)⁻¹) ^ j)
        - lam⁻¹ * (∑ j ∈ Finset.range (N + 1), ((q : ℂ) ^ 2) ^ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [loweringWeight, mul_inv, inv_pow, inv_inv]
  rw [hSexpand] at hS
  set SA : ℂ := ∑ j ∈ Finset.range (N + 1), (((q : ℂ) ^ 2)⁻¹) ^ j with hSA
  set SB : ℂ := ∑ j ∈ Finset.range (N + 1), ((q : ℂ) ^ 2) ^ j with hSB
  have hSB_ne : SB ≠ 0 := by
    intro h0
    have hgeom : SB * ((q : ℂ) ^ 2 - 1) = ((q : ℂ) ^ 2) ^ (N + 1) - 1 := by
      rw [hSB]; exact geom_sum_mul _ _
    rw [h0, zero_mul] at hgeom
    have hX : ((q : ℂ) ^ 2) ^ (N + 1) = 1 := sub_eq_zero.mp hgeom.symm
    exact pow_ne_one_of_infiniteOrder q hq (n := 2 * (N + 1)) (by omega) (by rw [pow_mul]; exact hX)
  have hkey : SA * ((q : ℂ) ^ 2) ^ N = SB := by
    rw [hSA, hSB, Finset.sum_mul,
      ← Finset.sum_range_reflect (fun j => ((q : ℂ) ^ 2) ^ j) (N + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjN : j ≤ N := by omega
    rw [inv_pow, show (N + 1) - 1 - j = N - j by omega, pow_sub₀ _ htne hjN]
    exact mul_comm _ _
  have hSA_ne : SA ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hkey; exact hSB_ne hkey.symm
  rw [← hkey] at hS
  have hfact : SA * (lam - lam⁻¹ * ((q : ℂ) ^ 2) ^ N) = 0 := by linear_combination hS
  have hlin : lam - lam⁻¹ * ((q : ℂ) ^ 2) ^ N = 0 :=
    (mul_eq_zero.mp hfact).resolve_left hSA_ne
  have h2 := sub_eq_zero.mp hlin
  have hlam2 : lam ^ 2 = ((q : ℂ) ^ 2) ^ N := by
    rw [sq]
    nth_rewrite 2 [h2]
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  rw [pow_mul]; exact hlam2

/-- A complex submodule stable under the raising, lowering, weight, and inverse-weight elements is stable under every algebra element. -/
lemma smul_mem_of_stable_generators (q : ℂˣ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (QuantumSL2 q) V] [IsScalarTower ℂ (QuantumSL2 q) V] (W : Submodule ℂ V)
    (hclE : ∀ x ∈ W, raisingElement q • x ∈ W) (hclF : ∀ x ∈ W, loweringElement q • x ∈ W)
    (hclK : ∀ x ∈ W, weightElement q • x ∈ W) (hclL : ∀ x ∈ W, inverseWeightElement q • x ∈ W)
    (a : QuantumSL2 q) (x : V) (hx : x ∈ W) : a • x ∈ W := by
  suffices H : ∀ p : FreeAlgebra ℂ Generator, ∀ y ∈ W, freeAlgebraMap q p • y ∈ W by
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (Relations q) a
    exact H p x hx
  intro p
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    intro y hy
    rw [show freeAlgebraMap q (algebraMap ℂ (FreeAlgebra ℂ Generator) r) = algebraMap ℂ (QuantumSL2 q) r from
      AlgHom.commutes (freeAlgebraMap q) r, algebraMap_smul]
    exact W.smul_mem r hy
  | grade1 g =>
    intro y hy
    fin_cases g
    · exact hclE y hy
    · exact hclF y hy
    · exact hclK y hy
    · exact hclL y hy
  | mul a b ha hb =>
    intro y hy
    rw [map_mul, mul_smul]
    exact ha _ (hb y hy)
  | add a b ha hb =>
    intro y hy
    rw [map_add, add_smul]
    exact W.add_mem (ha y hy) (hb y hy)

/-- A finite-dimensional simple module at an infinite-order parameter has a nonzero vector killed by the raising element whose weight eigenvalue is a sign times the indicated parameter power. -/
theorem exists_highestWeightVector_eigenvalue_eq_sign_mul_pow (q : ℂˣ) (hq : ¬ IsOfFinOrder q)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    ∃ (v : V) (ε : ℂ), v ≠ 0 ∧ raisingElement q • v = 0 ∧ ε ^ 2 = 1 ∧
      weightElement q • v = (ε * (q : ℂ) ^ (Module.finrank ℂ V - 1)) • v := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  have hqinv : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_infiniteOrder q hq
  obtain ⟨v, lam, hv0, he, hKv⟩ := exists_ne_zero_raising_annihilated_weightEigenvector q V hq
  
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hKv
    apply hv0
    have h := congrArg (fun x => inverseWeightElement q • x) hKv
    simp only [smul_zero] at h
    rw [← mul_smul, inverseWeightElement_mul_weightElement, one_smul] at h
    exact h
  
  have hex : ∃ i, loweringIterate q V v i = 0 := by
    by_contra hcon
    push Not at hcon
    have hLI : LinearIndependent ℂ (loweringIterate q V v) :=
      Module.End.eigenvectors_linearIndependent' (weightActionEnd q V) (loweringWeight q lam)
        (loweringWeight_injective_of_infiniteOrder q hq lam hlam) (loweringIterate q V v)
        (fun i => ⟨Module.End.mem_eigenspace_iff.mpr
          (by rw [weightActionEnd_apply]; exact weightElement_smul_loweringIterate q V v lam hKv i), hcon i⟩)
    exact Module.Finite.not_linearIndependent_of_infinite _ hLI
  haveI : DecidablePred (fun i => loweringIterate q V v i = 0) := Classical.decPred _
  set M0 := Nat.find hex with hM0def
  have hM0_spec : loweringIterate q V v M0 = 0 := Nat.find_spec hex
  have hM0_ne : M0 ≠ 0 := by
    intro h0; rw [h0, loweringIterate_zero] at hM0_spec; exact hv0 hM0_spec
  obtain ⟨N, hNsucc⟩ : ∃ N, M0 = N + 1 := ⟨M0 - 1, by omega⟩
  have hzero_succ : loweringIterate q V v (N + 1) = 0 := by rw [← hNsucc]; exact hM0_spec
  have hne_le : ∀ i, i ≤ N → loweringIterate q V v i ≠ 0 := fun i hi => Nat.find_min hex (by omega)
  have hzero_ge : ∀ k, loweringIterate q V v (N + 1 + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using hzero_succ
    | succ j ih => rw [show N + 1 + (j + 1) = (N + 1 + j) + 1 by omega, loweringIterate_succ, ih, smul_zero]
  
  set b : Fin (N + 1) → V := fun i => loweringIterate q V v ↑i with hb
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hW
  have hiW : ∀ i, loweringIterate q V v i ∈ W := by
    intro i
    by_cases hiN : i ≤ N
    · exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨i, by omega⟩, rfl⟩)
    · have hle' : N + 1 ≤ i := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle'
      rw [hzero_ge k]; exact W.zero_mem
  
  have heW : ∀ i, raisingElement q • loweringIterate q V v i ∈ W := by
    intro i
    cases i with
    | zero => rw [loweringIterate_zero, he]; exact W.zero_mem
    | succ j => rw [raisingElement_smul_loweringIterate_succ q V hqinv v lam hlam he hKv j]; exact W.smul_mem _ (hiW j)
  have hfW : ∀ i, loweringElement q • loweringIterate q V v i ∈ W := fun i => by
    rw [← loweringIterate_succ]; exact hiW (i + 1)
  have hKW : ∀ i, weightElement q • loweringIterate q V v i ∈ W := fun i => by
    rw [weightElement_smul_loweringIterate q V v lam hKv i]; exact W.smul_mem _ (hiW i)
  have hLW : ∀ i, inverseWeightElement q • loweringIterate q V v i ∈ W := fun i => by
    rw [inverseWeightElement_smul_loweringIterate q V v lam hlam hKv i]; exact W.smul_mem _ (hiW i)
  have clOf : ∀ (a : QuantumSL2 q), (∀ i, a • loweringIterate q V v i ∈ W) → ∀ x ∈ W, a • x ∈ W := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ha ↑i
    | zero => rw [smul_zero]; exact W.zero_mem
    | add p r _ _ hp hr => rw [smul_add]; exact W.add_mem hp hr
    | smul c p _ hp => rw [smul_comm]; exact W.smul_mem c hp
  
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (W : Set V)
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      smul_mem' := fun a x hx => smul_mem_of_stable_generators q V W (clOf (raisingElement q) heW)
        (clOf (loweringElement q) hfW) (clOf (weightElement q) hKW) (clOf (inverseWeightElement q) hLW) a x hx }
  have hv_mem : v ∈ W' := by
    change v ∈ W
    have := hiW 0; rwa [loweringIterate_zero] at this
  have hne : W' ≠ ⊥ := by
    intro hbot
    apply hv0
    have : v ∈ (⊥ : Submodule (QuantumSL2 q) V) := hbot ▸ hv_mem
    exact (Submodule.mem_bot (QuantumSL2 q)).mp this
  have hW'top : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne
  have hWtop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxW' : x ∈ W' := by rw [hW'top]; exact Submodule.mem_top
    exact hxW'
  
  have hbne : ∀ i : Fin (N + 1), b i ≠ 0 := fun i => hne_le ↑i (Nat.lt_succ_iff.mp i.isLt)
  have hLIb : LinearIndependent ℂ b :=
    Module.End.eigenvectors_linearIndependent' (weightActionEnd q V) (fun i : Fin (N + 1) => loweringWeight q lam ↑i)
      ((loweringWeight_injective_of_infiniteOrder q hq lam hlam).comp Fin.val_injective) b
      (fun i => ⟨Module.End.mem_eigenspace_iff.mpr
        (by rw [weightActionEnd_apply]; exact weightElement_smul_loweringIterate q V v lam hKv ↑i), hbne i⟩)
  have hge : N + 1 ≤ Module.finrank ℂ V := by
    have := hLIb.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  have hle : Module.finrank ℂ V ≤ N + 1 := by
    have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range b)) ≤ N + 1 := by
      have := finrank_range_le_card (R := ℂ) b
      rwa [Set.finrank, Fintype.card_fin] at this
    rw [← hW, hWtop, finrank_top] at hspan
    exact hspan
  have hfinrank : Module.finrank ℂ V = N + 1 := le_antisymm hle hge
  have hfinrank_sub : Module.finrank ℂ V - 1 = N := by omega
  
  have hdcoef : raisingOnLoweringPowerCoeff q lam N = 0 := by
    have h1 : raisingElement q • loweringIterate q V v (N + 1) = raisingOnLoweringPowerCoeff q lam N • loweringIterate q V v N :=
      raisingElement_smul_loweringIterate_succ q V hqinv v lam hlam he hKv N
    rw [hzero_succ, smul_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right (hne_le N le_rfl)
  have hlam2 : lam ^ 2 = (q : ℂ) ^ (2 * N) := sq_eq_evenPower_of_raisingOnLoweringPowerCoeff_eq_zero q hq lam hlam N hdcoef
  
  refine ⟨v, lam * ((q : ℂ) ^ N)⁻¹, hv0, he, ?_, ?_⟩
  · have hqN : (q : ℂ) ^ N ≠ 0 := pow_ne_zero _ q.ne_zero
    rw [mul_pow, hlam2, inv_pow, ← pow_mul, show N * 2 = 2 * N by ring,
      mul_inv_cancel₀ (pow_ne_zero _ q.ne_zero)]
  · rw [hKv]
    congr 1
    rw [hfinrank_sub, mul_assoc, inv_mul_cancel₀ (pow_ne_zero N q.ne_zero), mul_one]

/-- Moving a power of the weight element past the raising element introduces the corresponding power of the squared parameter. -/
lemma weightElement_pow_mul_raisingElement (q : ℂˣ) (n : ℕ) :
    weightElement q ^ n * raisingElement q = (((q : ℂ) ^ 2) ^ n) • (raisingElement q * weightElement q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (weightElement q), mul_assoc, weightElement_mul_raisingElement, mul_smul_comm, ← mul_assoc, ih,
        smul_mul_assoc, smul_smul, mul_assoc (raisingElement q), ← pow_succ (weightElement q),
        mul_comm ((q : ℂ) ^ 2), ← pow_succ]

/-- Moving a power of the weight element past the lowering element introduces the corresponding power of the inverse squared parameter. -/
lemma weightElement_pow_mul_loweringElement (q : ℂˣ) (n : ℕ) :
    weightElement q ^ n * loweringElement q = ((((q : ℂ) ^ 2)⁻¹) ^ n) • (loweringElement q * weightElement q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (weightElement q), mul_assoc, weightElement_mul_loweringElement, mul_smul_comm, ← mul_assoc, ih,
        smul_mul_assoc, smul_smul, mul_assoc (loweringElement q), ← pow_succ (weightElement q),
        mul_comm (((q : ℂ) ^ 2)⁻¹), ← pow_succ]

/-- The parameter square raised to the order of the parameter is one. -/
lemma sq_pow_orderOf (q : ℂˣ) : ((q : ℂ) ^ 2) ^ orderOf q = 1 := by
  have hq1 : (q : ℂ) ^ orderOf q = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  rw [← pow_mul, mul_comm, pow_mul, hq1, one_pow]

/-- The order-th power of the weight element commutes with the raising element. -/
lemma weightElement_order_pow_commutes_raisingElement (q : ℂˣ) :
    weightElement q ^ orderOf q * raisingElement q = raisingElement q * weightElement q ^ orderOf q := by
  rw [weightElement_pow_mul_raisingElement, sq_pow_orderOf, one_smul]

/-- The order-th power of the weight element commutes with the lowering element. -/
lemma weightElement_order_pow_commutes_loweringElement (q : ℂˣ) :
    weightElement q ^ orderOf q * loweringElement q = loweringElement q * weightElement q ^ orderOf q := by
  rw [weightElement_pow_mul_loweringElement, inv_pow, sq_pow_orderOf, inv_one, one_smul]

/-- The order-th power of the weight element commutes with every algebra element. -/
lemma weightElement_order_pow_commutes (q : ℂˣ) (a : QuantumSL2 q) :
    weightElement q ^ orderOf q * a = a * weightElement q ^ orderOf q := by
  suffices H : ∀ p : FreeAlgebra ℂ Generator,
      weightElement q ^ orderOf q * freeAlgebraMap q p = freeAlgebraMap q p * weightElement q ^ orderOf q by
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (Relations q) a
    exact H p
  intro p
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      rw [show freeAlgebraMap q (algebraMap ℂ (FreeAlgebra ℂ Generator) r) = algebraMap ℂ (QuantumSL2 q) r from
        AlgHom.commutes (freeAlgebraMap q) r, Algebra.commutes]
  | grade1 g =>
      fin_cases g
      · change weightElement q ^ orderOf q * raisingElement q = raisingElement q * weightElement q ^ orderOf q
        exact weightElement_order_pow_commutes_raisingElement q
      · change weightElement q ^ orderOf q * loweringElement q = loweringElement q * weightElement q ^ orderOf q
        exact weightElement_order_pow_commutes_loweringElement q
      · change weightElement q ^ orderOf q * weightElement q = weightElement q * weightElement q ^ orderOf q
        rw [← pow_succ, ← pow_succ']
      · change weightElement q ^ orderOf q * inverseWeightElement q = inverseWeightElement q * weightElement q ^ orderOf q
        have hc : Commute (weightElement q) (inverseWeightElement q) := by
          change weightElement q * inverseWeightElement q = inverseWeightElement q * weightElement q; rw [weightElement_mul_inverseWeightElement, inverseWeightElement_mul_weightElement]
        exact (hc.pow_left (orderOf q)).eq
  | mul x y hx hy =>
      rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy =>
      rw [map_add, mul_add, add_mul, hx, hy]

/-- A power of the weight-action endomorphism acts by the corresponding power of the weight element. -/
lemma weightActionEnd_pow_apply (q : ℂˣ) (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] (n : ℕ) (v : V) :
    (weightActionEnd q V ^ n) v = weightElement q ^ n • v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, weightActionEnd_apply, ih, ← mul_smul, ← pow_succ]

/-- On a finite-dimensional simple module at a finite-order parameter, the order-th power of the weight element acts by a nonzero scalar. -/
theorem weightElement_order_pow_smul_eq_scalar (q : ℂˣ) (_hq : IsOfFinOrder q)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    ∃ α : ℂ, α ≠ 0 ∧ ∀ v : V, weightElement q ^ orderOf q • v = α • v := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (weightActionEnd q V ^ orderOf q)
  
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (Module.End.eigenspace (weightActionEnd q V ^ orderOf q) α : Set V)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro a x hx
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, weightActionEnd_pow_apply] at hx
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, weightActionEnd_pow_apply,
          ← mul_smul, weightElement_order_pow_commutes, mul_smul, hx, smul_comm] }
  
  have hne : W' ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
    intro hbot
    apply hv0
    have hmem : v ∈ W' := hv
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have htop : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne
  refine ⟨α, ?_, ?_⟩
  · 
    obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
    intro hα0
    apply hv0
    have hKv : weightElement q ^ orderOf q • v = 0 := by
      have hmem := Module.End.mem_eigenspace_iff.mp hv
      rw [weightActionEnd_pow_apply, hα0, zero_smul] at hmem
      exact hmem
    have hLK : inverseWeightElement q ^ orderOf q * weightElement q ^ orderOf q = 1 := by
      have hc : Commute (inverseWeightElement q) (weightElement q) := by
        change inverseWeightElement q * weightElement q = weightElement q * inverseWeightElement q; rw [inverseWeightElement_mul_weightElement, weightElement_mul_inverseWeightElement]
      rw [← hc.mul_pow, inverseWeightElement_mul_weightElement, one_pow]
    have h := congrArg (fun x => inverseWeightElement q ^ orderOf q • x) hKv
    simp only [smul_zero] at h
    rw [← mul_smul, hLK, one_smul] at h
    exact h
  · intro v
    have hv_mem : v ∈ W' := by rw [htop]; exact Submodule.mem_top
    have hmem : v ∈ Module.End.eigenspace (weightActionEnd q V ^ orderOf q) α := hv_mem
    rw [Module.End.mem_eigenspace_iff, weightActionEnd_pow_apply] at hmem
    exact hmem

/-- On a finite-dimensional simple module at a finite-order parameter, the weight-action endomorphism is semisimple, its eigenspaces span, and a common positive power of its eigenvalues is fixed. -/
theorem weightActionEnd_structure_of_finiteOrder (q : ℂˣ) (hq : IsOfFinOrder q)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    (weightActionEnd q V).IsSemisimple ∧
      (⨆ μ : ℂ, Module.End.eigenspace (weightActionEnd q V) μ) = ⊤ ∧
      ∃ α : ℂ, α ≠ 0 ∧ ∀ μ : ℂ, (weightActionEnd q V).HasEigenvalue μ → μ ^ orderOf q = α := by
  obtain ⟨α, hα0, hα⟩ := weightElement_order_pow_smul_eq_scalar q hq V
  have hℓ : 0 < orderOf q := hq.orderOf_pos
  
  have hpow : weightActionEnd q V ^ orderOf q = α • (1 : Module.End ℂ V) := by
    ext v; rw [weightActionEnd_pow_apply, hα v, LinearMap.smul_apply, Module.End.one_apply]
  
  have hss : (weightActionEnd q V).IsSemisimple := by
    have hsqf : Squarefree (Polynomial.X ^ orderOf q - Polynomial.C α : Polynomial ℂ) :=
      (Polynomial.separable_X_pow_sub_C α (Nat.cast_ne_zero.mpr hℓ.ne') hα0).squarefree
    have haeval : Polynomial.aeval (weightActionEnd q V) (Polynomial.X ^ orderOf q - Polynomial.C α) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hpow,
        Algebra.algebraMap_eq_smul_one, sub_self]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsqf haeval
  refine ⟨hss, hss.iSup_eigenspace_eq_top, α, hα0, ?_⟩
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hve : weightActionEnd q V v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  
  have hpm : ∀ n : ℕ, (weightActionEnd q V ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hve, map_smul, ih, smul_smul, ← pow_succ']
  have h1 : μ ^ orderOf q • v = α • v := by
    rw [← hpm, hpow, LinearMap.smul_apply, Module.End.one_apply]
  have h2 : (μ ^ orderOf q - α) • v = 0 := by rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_right hv0 |> sub_eq_zero.mp

/-- A complex unit whose square is not one differs from its inverse. -/
lemma sub_inv_ne_zero_of_sq_ne_one (q : ℂˣ) (hq2 : (q : ℂ) ^ 2 ≠ 1) : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := by
  intro h
  have h2 : (q : ℂ) = (q : ℂ)⁻¹ := sub_eq_zero.mp h
  have : (q : ℂ) ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h2]; exact mul_inv_cancel₀ q.ne_zero
  exact hq2 this

/-- Moving the inverse weight element past the raising element introduces the inverse square of the parameter. -/
@[simp] lemma inverseWeightElement_mul_raisingElement (q : ℂˣ) : inverseWeightElement q * raisingElement q = ((q : ℂ) ^ 2)⁻¹ • (raisingElement q * inverseWeightElement q) := by
  have hq2 : ((q : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ q.ne_zero
  have key : raisingElement q * inverseWeightElement q = ((q : ℂ) ^ 2) • (inverseWeightElement q * raisingElement q) := by
    have h : inverseWeightElement q * (weightElement q * raisingElement q) * inverseWeightElement q = inverseWeightElement q * (((q : ℂ) ^ 2) • (raisingElement q * weightElement q)) * inverseWeightElement q := by
      rw [weightElement_mul_raisingElement]
    rw [mul_smul_comm, smul_mul_assoc] at h
    rw [show inverseWeightElement q * (weightElement q * raisingElement q) * inverseWeightElement q = raisingElement q * inverseWeightElement q by
          rw [← mul_assoc (inverseWeightElement q) (weightElement q) (raisingElement q), inverseWeightElement_mul_weightElement, one_mul]] at h
    rw [show inverseWeightElement q * (raisingElement q * weightElement q) * inverseWeightElement q = inverseWeightElement q * raisingElement q by
          rw [mul_assoc (inverseWeightElement q) (raisingElement q * weightElement q) (inverseWeightElement q), mul_assoc (raisingElement q) (weightElement q) (inverseWeightElement q), weightElement_mul_inverseWeightElement, mul_one]] at h
    exact h
  rw [key, smul_smul, inv_mul_cancel₀ hq2, one_smul]

/-- Moving the inverse weight element past the lowering element introduces the square of the parameter. -/
@[simp] lemma inverseWeightElement_mul_loweringElement (q : ℂˣ) : inverseWeightElement q * loweringElement q = ((q : ℂ) ^ 2) • (loweringElement q * inverseWeightElement q) := by
  have key : loweringElement q * inverseWeightElement q = ((q : ℂ) ^ 2)⁻¹ • (inverseWeightElement q * loweringElement q) := by
    have h : inverseWeightElement q * (weightElement q * loweringElement q) * inverseWeightElement q = inverseWeightElement q * (((q : ℂ) ^ 2)⁻¹ • (loweringElement q * weightElement q)) * inverseWeightElement q := by
      rw [weightElement_mul_loweringElement]
    rw [mul_smul_comm, smul_mul_assoc] at h
    rw [show inverseWeightElement q * (weightElement q * loweringElement q) * inverseWeightElement q = loweringElement q * inverseWeightElement q by
          rw [← mul_assoc (inverseWeightElement q) (weightElement q) (loweringElement q), inverseWeightElement_mul_weightElement, one_mul]] at h
    rw [show inverseWeightElement q * (loweringElement q * weightElement q) * inverseWeightElement q = inverseWeightElement q * loweringElement q by
          rw [mul_assoc (inverseWeightElement q) (loweringElement q * weightElement q) (inverseWeightElement q), mul_assoc (loweringElement q) (weightElement q) (inverseWeightElement q), weightElement_mul_inverseWeightElement, mul_one]] at h
    exact h
  have hq2 : ((q : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ q.ne_zero
  rw [key, smul_smul, mul_inv_cancel₀ hq2, one_smul]

/-- The product of the raising and lowering elements is their reverse product plus the normalized difference of the weight elements. -/
lemma raisingElement_mul_loweringElement (q : ℂˣ) (hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) :
    raisingElement q * loweringElement q = loweringElement q * raisingElement q + (((q : ℂ) - (q : ℂ)⁻¹)⁻¹) • (weightElement q - inverseWeightElement q) := by
  have h := parameterDifference_smul_commutator q
  have hd : raisingElement q * loweringElement q - loweringElement q * raisingElement q = (((q : ℂ) - (q : ℂ)⁻¹)⁻¹) • (weightElement q - inverseWeightElement q) := by
    rw [← h, inv_smul_smul₀ hq']
  rw [← hd]; abel

/-- Moving the weight element past a power of the raising element introduces the indicated even power of the parameter. -/
lemma weightElement_mul_raisingElement_pow (q : ℂˣ) (n : ℕ) :
    weightElement q * raisingElement q ^ n = (((q : ℂ) ^ 2) ^ n) • (raisingElement q ^ n * weightElement q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (raisingElement q) n, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (raisingElement q ^ n) (weightElement q) (raisingElement q),
        weightElement_mul_raisingElement, mul_smul_comm, smul_smul, ← mul_assoc (raisingElement q ^ n) (raisingElement q) (weightElement q),
        ← pow_succ ((q : ℂ) ^ 2) n]

/-- Moving the inverse weight element past a power of the raising element introduces the corresponding power of the inverse squared parameter. -/
lemma inverseWeightElement_mul_raisingElement_pow (q : ℂˣ) (n : ℕ) :
    inverseWeightElement q * raisingElement q ^ n = ((((q : ℂ) ^ 2)⁻¹) ^ n) • (raisingElement q ^ n * inverseWeightElement q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (raisingElement q) n, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (raisingElement q ^ n) (inverseWeightElement q) (raisingElement q),
        inverseWeightElement_mul_raisingElement, mul_smul_comm, smul_smul, ← mul_assoc (raisingElement q ^ n) (raisingElement q) (inverseWeightElement q),
        ← pow_succ (((q : ℂ) ^ 2)⁻¹) n]

/-- Moving the weight element past a power of the lowering element introduces the inverse of the indicated even power of the parameter. -/
lemma weightElement_mul_loweringElement_pow (q : ℂˣ) (n : ℕ) :
    weightElement q * loweringElement q ^ n = ((((q : ℂ) ^ 2)⁻¹) ^ n) • (loweringElement q ^ n * weightElement q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (loweringElement q) n, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (loweringElement q ^ n) (weightElement q) (loweringElement q),
        weightElement_mul_loweringElement, mul_smul_comm, smul_smul, ← mul_assoc (loweringElement q ^ n) (loweringElement q) (weightElement q),
        ← pow_succ (((q : ℂ) ^ 2)⁻¹) n]

/-- Moving the inverse weight element past a power of the lowering element introduces the corresponding power of the squared parameter. -/
lemma inverseWeightElement_mul_loweringElement_pow (q : ℂˣ) (n : ℕ) :
    inverseWeightElement q * loweringElement q ^ n = (((q : ℂ) ^ 2) ^ n) • (loweringElement q ^ n * inverseWeightElement q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (loweringElement q) n, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (loweringElement q ^ n) (inverseWeightElement q) (loweringElement q),
        inverseWeightElement_mul_loweringElement, mul_smul_comm, smul_smul, ← mul_assoc (loweringElement q ^ n) (loweringElement q) (inverseWeightElement q),
        ← pow_succ ((q : ℂ) ^ 2) n]

/-- A successor power of the raising element multiplied by the lowering element satisfies the displayed commutation expansion. -/
lemma raisingElement_succ_pow_mul_loweringElement (q : ℂˣ) (hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (n : ℕ) :
    raisingElement q ^ (n + 1) * loweringElement q
      = loweringElement q * raisingElement q ^ (n + 1)
        + (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ 2) ^ k)
            • (raisingElement q ^ n * weightElement q)
        - (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * ∑ k ∈ Finset.range (n + 1), (((q : ℂ) ^ 2)⁻¹) ^ k)
            • (raisingElement q ^ n * inverseWeightElement q) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, one_mul, mul_one, Finset.range_one,
      Finset.sum_singleton]
    rw [raisingElement_mul_loweringElement q hq', smul_sub]
    abel
  | succ n ih =>
    have hAK : raisingElement q * (raisingElement q ^ n * weightElement q) = raisingElement q ^ (n + 1) * weightElement q := by
      rw [← mul_assoc, ← pow_succ' (raisingElement q) n]
    have hAL : raisingElement q * (raisingElement q ^ n * inverseWeightElement q) = raisingElement q ^ (n + 1) * inverseWeightElement q := by
      rw [← mul_assoc, ← pow_succ' (raisingElement q) n]
    have key : raisingElement q * (loweringElement q * raisingElement q ^ (n + 1))
        = loweringElement q * raisingElement q ^ (n + 1 + 1)
          + ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ • (weightElement q * raisingElement q ^ (n + 1))
          - ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ • (inverseWeightElement q * raisingElement q ^ (n + 1)) := by
      rw [← mul_assoc, raisingElement_mul_loweringElement q hq', add_mul, smul_mul_assoc, sub_mul, smul_sub,
        mul_assoc (loweringElement q) (raisingElement q) (raisingElement q ^ (n + 1)), ← pow_succ' (raisingElement q) (n + 1)]
      abel
    rw [Finset.sum_range_succ (fun k => ((q : ℂ) ^ 2) ^ k) (n + 1),
        Finset.sum_range_succ (fun k => (((q : ℂ) ^ 2)⁻¹) ^ k) (n + 1)]
    conv_lhs =>
      rw [pow_succ' (raisingElement q) (n + 1), mul_assoc (raisingElement q) (raisingElement q ^ (n + 1)) (loweringElement q), ih,
        mul_sub, mul_add, mul_smul_comm, mul_smul_comm, key, hAK, hAL,
        weightElement_mul_raisingElement_pow q (n + 1), inverseWeightElement_mul_raisingElement_pow q (n + 1)]
    module

/-- If the squared parameter is not one, the order-th power of the raising element commutes with the lowering element. -/
lemma raisingElement_order_pow_commutes_loweringElement (q : ℂˣ) (hq2 : (q : ℂ) ^ 2 ≠ 1) :
    raisingElement q ^ orderOf q * loweringElement q = loweringElement q * raisingElement q ^ orderOf q := by
  have hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one q hq2
  rcases Nat.eq_zero_or_pos (orderOf q) with h0 | hpos
  · rw [h0, pow_zero, one_mul, mul_one]
  · obtain ⟨m, hm⟩ : ∃ m, orderOf q = m + 1 := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm]
    have h1 : ((q : ℂ) ^ 2) ^ (m + 1) = 1 := by rw [← hm]; exact sq_pow_orderOf q
    have hSA : (∑ k ∈ Finset.range (m + 1), ((q : ℂ) ^ 2) ^ k) = 0 := by
      have hgeom : (∑ k ∈ Finset.range (m + 1), ((q : ℂ) ^ 2) ^ k) * ((q : ℂ) ^ 2 - 1)
          = ((q : ℂ) ^ 2) ^ (m + 1) - 1 := geom_sum_mul _ _
      rw [h1, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hq2)
    have hSB : (∑ k ∈ Finset.range (m + 1), (((q : ℂ) ^ 2)⁻¹) ^ k) = 0 := by
      have h1' : (((q : ℂ) ^ 2)⁻¹) ^ (m + 1) = 1 := by rw [inv_pow, h1, inv_one]
      have hgeom : (∑ k ∈ Finset.range (m + 1), (((q : ℂ) ^ 2)⁻¹) ^ k) * (((q : ℂ) ^ 2)⁻¹ - 1)
          = (((q : ℂ) ^ 2)⁻¹) ^ (m + 1) - 1 := geom_sum_mul _ _
      rw [h1', sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right
        (sub_ne_zero.mpr (fun h => hq2 (inv_eq_one.mp h)))
    rw [raisingElement_succ_pow_mul_loweringElement q hq' m, hSA, hSB]
    simp

/-- The order-th power of the raising element commutes with the weight element. -/
lemma raisingElement_order_pow_commutes_weightElement (q : ℂˣ) : raisingElement q ^ orderOf q * weightElement q = weightElement q * raisingElement q ^ orderOf q := by
  rw [weightElement_mul_raisingElement_pow q (orderOf q), sq_pow_orderOf, one_smul]

/-- The order-th power of the raising element commutes with the inverse weight element. -/
lemma raisingElement_order_pow_commutes_inverseWeightElement (q : ℂˣ) : raisingElement q ^ orderOf q * inverseWeightElement q = inverseWeightElement q * raisingElement q ^ orderOf q := by
  rw [inverseWeightElement_mul_raisingElement_pow q (orderOf q), inv_pow, sq_pow_orderOf, inv_one, one_smul]

/-- The order-th power of the raising element commutes with the raising element. -/
lemma raisingElement_order_pow_commutes_raisingElement (q : ℂˣ) : raisingElement q ^ orderOf q * raisingElement q = raisingElement q * raisingElement q ^ orderOf q := by
  rw [← pow_succ, ← pow_succ']

/-- If the squared parameter is not one, the order-th power of the raising element commutes with every algebra element. -/
lemma raisingElement_order_pow_commutes (q : ℂˣ) (hq2 : (q : ℂ) ^ 2 ≠ 1) (a : QuantumSL2 q) :
    raisingElement q ^ orderOf q * a = a * raisingElement q ^ orderOf q := by
  suffices H : ∀ p : FreeAlgebra ℂ Generator,
      raisingElement q ^ orderOf q * freeAlgebraMap q p = freeAlgebraMap q p * raisingElement q ^ orderOf q by
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (Relations q) a
    exact H p
  intro p
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      rw [show freeAlgebraMap q (algebraMap ℂ (FreeAlgebra ℂ Generator) r) = algebraMap ℂ (QuantumSL2 q) r from
        AlgHom.commutes (freeAlgebraMap q) r, Algebra.commutes]
  | grade1 g =>
      fin_cases g
      · change raisingElement q ^ orderOf q * raisingElement q = raisingElement q * raisingElement q ^ orderOf q
        exact raisingElement_order_pow_commutes_raisingElement q
      · change raisingElement q ^ orderOf q * loweringElement q = loweringElement q * raisingElement q ^ orderOf q
        exact raisingElement_order_pow_commutes_loweringElement q hq2
      · change raisingElement q ^ orderOf q * weightElement q = weightElement q * raisingElement q ^ orderOf q
        exact raisingElement_order_pow_commutes_weightElement q
      · change raisingElement q ^ orderOf q * inverseWeightElement q = inverseWeightElement q * raisingElement q ^ orderOf q
        exact raisingElement_order_pow_commutes_inverseWeightElement q
  | mul x y hx hy =>
      rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy =>
      rw [map_add, mul_add, add_mul, hx, hy]

/-- The product of the lowering and raising elements is their reverse product minus the normalized difference of the weight elements. -/
lemma loweringElement_mul_raisingElement (q : ℂˣ) (hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) :
    loweringElement q * raisingElement q = raisingElement q * loweringElement q - (((q : ℂ) - (q : ℂ)⁻¹)⁻¹) • (weightElement q - inverseWeightElement q) := by
  have h := raisingElement_mul_loweringElement q hq'
  rw [h]; abel

/-- A successor power of the lowering element multiplied by the raising element satisfies the displayed commutation expansion. -/
lemma loweringElement_succ_pow_mul_raisingElement (q : ℂˣ) (hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (n : ℕ) :
    loweringElement q ^ (n + 1) * raisingElement q
      = raisingElement q * loweringElement q ^ (n + 1)
        - (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * ∑ k ∈ Finset.range (n + 1), (((q : ℂ) ^ 2)⁻¹) ^ k)
            • (loweringElement q ^ n * weightElement q)
        + (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ 2) ^ k)
            • (loweringElement q ^ n * inverseWeightElement q) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, one_mul, mul_one, Finset.range_one,
      Finset.sum_singleton]
    rw [loweringElement_mul_raisingElement q hq', smul_sub]
    abel
  | succ n ih =>
    have hAK : loweringElement q * (loweringElement q ^ n * weightElement q) = loweringElement q ^ (n + 1) * weightElement q := by
      rw [← mul_assoc, ← pow_succ' (loweringElement q) n]
    have hAL : loweringElement q * (loweringElement q ^ n * inverseWeightElement q) = loweringElement q ^ (n + 1) * inverseWeightElement q := by
      rw [← mul_assoc, ← pow_succ' (loweringElement q) n]
    have key : loweringElement q * (raisingElement q * loweringElement q ^ (n + 1))
        = raisingElement q * loweringElement q ^ (n + 1 + 1)
          - ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ • (weightElement q * loweringElement q ^ (n + 1))
          + ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ • (inverseWeightElement q * loweringElement q ^ (n + 1)) := by
      rw [← mul_assoc, loweringElement_mul_raisingElement q hq', sub_mul, smul_mul_assoc, sub_mul, smul_sub,
        mul_assoc (raisingElement q) (loweringElement q) (loweringElement q ^ (n + 1)), ← pow_succ' (loweringElement q) (n + 1)]
      abel
    rw [Finset.sum_range_succ (fun k => (((q : ℂ) ^ 2)⁻¹) ^ k) (n + 1),
        Finset.sum_range_succ (fun k => ((q : ℂ) ^ 2) ^ k) (n + 1)]
    conv_lhs =>
      rw [pow_succ' (loweringElement q) (n + 1), mul_assoc (loweringElement q) (loweringElement q ^ (n + 1)) (raisingElement q), ih,
        mul_add, mul_sub, mul_smul_comm, mul_smul_comm, key, hAK, hAL,
        weightElement_mul_loweringElement_pow q (n + 1), inverseWeightElement_mul_loweringElement_pow q (n + 1)]
    module

/-- If the squared parameter is not one, the order-th power of the lowering element commutes with the raising element. -/
lemma loweringElement_order_pow_commutes_raisingElement (q : ℂˣ) (hq2 : (q : ℂ) ^ 2 ≠ 1) :
    loweringElement q ^ orderOf q * raisingElement q = raisingElement q * loweringElement q ^ orderOf q := by
  have hq' : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one q hq2
  rcases Nat.eq_zero_or_pos (orderOf q) with h0 | hpos
  · rw [h0, pow_zero, one_mul, mul_one]
  · obtain ⟨m, hm⟩ : ∃ m, orderOf q = m + 1 := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm]
    have h1 : ((q : ℂ) ^ 2) ^ (m + 1) = 1 := by rw [← hm]; exact sq_pow_orderOf q
    have hSA : (∑ k ∈ Finset.range (m + 1), ((q : ℂ) ^ 2) ^ k) = 0 := by
      have hgeom : (∑ k ∈ Finset.range (m + 1), ((q : ℂ) ^ 2) ^ k) * ((q : ℂ) ^ 2 - 1)
          = ((q : ℂ) ^ 2) ^ (m + 1) - 1 := geom_sum_mul _ _
      rw [h1, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hq2)
    have hSB : (∑ k ∈ Finset.range (m + 1), (((q : ℂ) ^ 2)⁻¹) ^ k) = 0 := by
      have h1' : (((q : ℂ) ^ 2)⁻¹) ^ (m + 1) = 1 := by rw [inv_pow, h1, inv_one]
      have hgeom : (∑ k ∈ Finset.range (m + 1), (((q : ℂ) ^ 2)⁻¹) ^ k) * (((q : ℂ) ^ 2)⁻¹ - 1)
          = (((q : ℂ) ^ 2)⁻¹) ^ (m + 1) - 1 := geom_sum_mul _ _
      rw [h1', sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right
        (sub_ne_zero.mpr (fun h => hq2 (inv_eq_one.mp h)))
    rw [loweringElement_succ_pow_mul_raisingElement q hq' m, hSA, hSB]
    simp

/-- The order-th power of the lowering element commutes with the weight element. -/
lemma loweringElement_order_pow_commutes_weightElement (q : ℂˣ) : loweringElement q ^ orderOf q * weightElement q = weightElement q * loweringElement q ^ orderOf q := by
  rw [weightElement_mul_loweringElement_pow q (orderOf q), inv_pow, sq_pow_orderOf, inv_one, one_smul]

/-- The order-th power of the lowering element commutes with the inverse weight element. -/
lemma loweringElement_order_pow_commutes_inverseWeightElement (q : ℂˣ) : loweringElement q ^ orderOf q * inverseWeightElement q = inverseWeightElement q * loweringElement q ^ orderOf q := by
  rw [inverseWeightElement_mul_loweringElement_pow q (orderOf q), sq_pow_orderOf, one_smul]

/-- The order-th power of the lowering element commutes with the lowering element. -/
lemma loweringElement_order_pow_commutes_loweringElement (q : ℂˣ) : loweringElement q ^ orderOf q * loweringElement q = loweringElement q * loweringElement q ^ orderOf q := by
  rw [← pow_succ, ← pow_succ']

/-- If the squared parameter is not one, the order-th power of the lowering element commutes with every algebra element. -/
lemma loweringElement_order_pow_commutes (q : ℂˣ) (hq2 : (q : ℂ) ^ 2 ≠ 1) (a : QuantumSL2 q) :
    loweringElement q ^ orderOf q * a = a * loweringElement q ^ orderOf q := by
  suffices H : ∀ p : FreeAlgebra ℂ Generator,
      loweringElement q ^ orderOf q * freeAlgebraMap q p = freeAlgebraMap q p * loweringElement q ^ orderOf q by
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (Relations q) a
    exact H p
  intro p
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      rw [show freeAlgebraMap q (algebraMap ℂ (FreeAlgebra ℂ Generator) r) = algebraMap ℂ (QuantumSL2 q) r from
        AlgHom.commutes (freeAlgebraMap q) r, Algebra.commutes]
  | grade1 g =>
      fin_cases g
      · change loweringElement q ^ orderOf q * raisingElement q = raisingElement q * loweringElement q ^ orderOf q
        exact loweringElement_order_pow_commutes_raisingElement q hq2
      · change loweringElement q ^ orderOf q * loweringElement q = loweringElement q * loweringElement q ^ orderOf q
        exact loweringElement_order_pow_commutes_loweringElement q
      · change loweringElement q ^ orderOf q * weightElement q = weightElement q * loweringElement q ^ orderOf q
        exact loweringElement_order_pow_commutes_weightElement q
      · change loweringElement q ^ orderOf q * inverseWeightElement q = inverseWeightElement q * loweringElement q ^ orderOf q
        exact loweringElement_order_pow_commutes_inverseWeightElement q
  | mul x y hx hy =>
      rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy =>
      rw [map_add, mul_add, add_mul, hx, hy]

section CentralScalar

variable (q : ℂˣ)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
  [IsScalarTower ℂ (QuantumSL2 q) V]

/-- The complex-linear endomorphism induced by the action of an algebra element. -/
noncomputable def algebraActionEnd (x : QuantumSL2 q) : Module.End ℂ V where
  toFun v := x • v
  map_add' := by intro a b; rw [smul_add]
  map_smul' := by intro c v; exact smul_comm x c v

/-- The algebra-action endomorphism evaluates as scalar action by its algebra element. -/
@[simp] lemma algebraActionEnd_apply (x : QuantumSL2 q) (v : V) : algebraActionEnd q V x v = x • v := rfl

/-- A central element acts by a scalar on every finite-dimensional simple module. -/
theorem exists_scalar_smul_eq_of_central (x : QuantumSL2 q) (hx : ∀ a : QuantumSL2 q, x * a = a * x)
    [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    ∃ α : ℂ, ∀ v : V, x • v = α • v := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (algebraActionEnd q V x)
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (Module.End.eigenspace (algebraActionEnd q V x) α : Set V)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro a v hv
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, algebraActionEnd_apply] at hv
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, algebraActionEnd_apply,
          ← mul_smul, hx, mul_smul, hv, smul_comm] }
  have hne : W' ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
    intro hbot
    apply hv0
    have hmem : v ∈ W' := hv
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have htop : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne
  refine ⟨α, fun v => ?_⟩
  have hv_mem : v ∈ W' := by rw [htop]; exact Submodule.mem_top
  have hmem : v ∈ Module.End.eigenspace (algebraActionEnd q V x) α := hv_mem
  rw [Module.End.mem_eigenspace_iff, algebraActionEnd_apply] at hmem
  exact hmem

/-- On a finite-dimensional simple module, the order-th power of the raising element acts by a scalar when the squared parameter is not one. -/
theorem raisingElement_order_pow_smul_eq_scalar (hq2 : (q : ℂ) ^ 2 ≠ 1)
    [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    ∃ α : ℂ, ∀ v : V, raisingElement q ^ orderOf q • v = α • v :=
  exists_scalar_smul_eq_of_central q V (raisingElement q ^ orderOf q) (raisingElement_order_pow_commutes q hq2)

/-- On a finite-dimensional simple module, the order-th power of the lowering element acts by a scalar when the squared parameter is not one. -/
theorem loweringElement_order_pow_smul_eq_scalar (hq2 : (q : ℂ) ^ 2 ≠ 1)
    [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    ∃ α : ℂ, ∀ v : V, loweringElement q ^ orderOf q • v = α • v :=
  exists_scalar_smul_eq_of_central q V (loweringElement q ^ orderOf q) (loweringElement_order_pow_commutes q hq2)

end CentralScalar

section LowerLadder

variable (q : ℂˣ)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
  [IsScalarTower ℂ (QuantumSL2 q) V]

/-- The sequence obtained by iterating the action of the raising element on a vector. -/
noncomputable def raisingIterate (w : V) (i : ℕ) : V := (raisingElement q) ^ i • w

/-- The sequence of weight eigenvalues associated with successive raising iterates. -/
noncomputable def raisingWeight (lam : ℂ) (i : ℕ) : ℂ := lam * ((q : ℂ) ^ 2) ^ i

omit [Module ℂ V] [IsScalarTower ℂ (QuantumSL2 q) V] in

/-- The zeroth raising iterate is the original vector. -/
@[simp] lemma raisingIterate_zero (w : V) : raisingIterate q V w 0 = w := by simp [raisingIterate]

omit [Module ℂ V] [IsScalarTower ℂ (QuantumSL2 q) V] in

/-- The next raising iterate is obtained by applying the raising element. -/
lemma raisingIterate_succ (w : V) (i : ℕ) : raisingIterate q V w (i + 1) = raisingElement q • raisingIterate q V w i := by
  simp only [raisingIterate, pow_succ', mul_smul]

/-- The zeroth raising weight is the initial scalar. -/
@[simp] lemma raisingWeight_zero (lam : ℂ) : raisingWeight q lam 0 = lam := by simp [raisingWeight]

/-- Every term of the raising-weight sequence from a nonzero initial scalar is nonzero. -/
lemma raisingWeight_ne_zero (lam : ℂ) (hlam : lam ≠ 0) (i : ℕ) : raisingWeight q lam i ≠ 0 := by
  apply mul_ne_zero hlam
  exact pow_ne_zero _ (pow_ne_zero _ q.ne_zero)

/-- The weight element acts on each raising iterate with the corresponding shifted eigenvalue. -/
lemma weightElement_smul_raisingIterate (w : V) (lam : ℂ) (hKw : weightElement q • w = lam • w) (i : ℕ) :
    weightElement q • raisingIterate q V w i = raisingWeight q lam i • raisingIterate q V w i := by
  induction i with
  | zero => simpa [raisingWeight] using hKw
  | succ n ih =>
    rw [raisingIterate_succ, ← mul_smul, weightElement_mul_raisingElement, smul_assoc, mul_smul, ih,
      smul_comm (raisingElement q) (raisingWeight q lam n), smul_smul]
    congr 1
    simp only [raisingWeight, pow_succ]
    ring

/-- The inverse weight element acts on each raising iterate by the inverse shifted eigenvalue. -/
lemma inverseWeightElement_smul_raisingIterate (w : V) (lam : ℂ) (hlam : lam ≠ 0) (hKw : weightElement q • w = lam • w) (i : ℕ) :
    inverseWeightElement q • raisingIterate q V w i = (raisingWeight q lam i)⁻¹ • raisingIterate q V w i := by
  have hK := weightElement_smul_raisingIterate q V w lam hKw i
  have hnu := raisingWeight_ne_zero q lam hlam i
  have h1 : inverseWeightElement q • (weightElement q • raisingIterate q V w i) = raisingIterate q V w i := by
    rw [← mul_smul, inverseWeightElement_mul_weightElement, one_smul]
  rw [hK, smul_comm (inverseWeightElement q) (raisingWeight q lam i)] at h1
  have := congrArg (fun x => (raisingWeight q lam i)⁻¹ • x) h1
  simp only [smul_smul, inv_mul_cancel₀ hnu, one_smul] at this
  exact this

/-- On a simultaneous weight and inverse-weight eigenvector, lowering after raising equals raising after lowering minus the indicated scalar action. -/
lemma loweringElement_smul_raisingElement_smul (hne : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (x : V) (a : ℂ)
    (hK : weightElement q • x = a • x) (hL : inverseWeightElement q • x = a⁻¹ • x) :
    loweringElement q • (raisingElement q • x) = raisingElement q • (loweringElement q • x) - (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (a - a⁻¹)) • x := by
  have h := raisingElement_smul_loweringElement_smul q V hne x a hK hL
  rw [h]
  abel

/-- The scalar coefficient governing the lowering action on successive raising iterates. -/
noncomputable def loweringOnRaisingPowerCoeff (lam : ℂ) (i : ℕ) : ℂ :=
  -∑ j ∈ Finset.range (i + 1), ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (raisingWeight q lam j - (raisingWeight q lam j)⁻¹)

/-- On a vector killed by the lowering element, lowering the next raising iterate yields the specified coefficient times the preceding iterate. -/
lemma loweringElement_smul_raisingIterate_succ (hne : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0) (w : V) (lam : ℂ) (hlam : lam ≠ 0)
    (hf : loweringElement q • w = 0) (hKw : weightElement q • w = lam • w) (i : ℕ) :
    loweringElement q • raisingIterate q V w (i + 1) = loweringOnRaisingPowerCoeff q lam i • raisingIterate q V w i := by
  induction i with
  | zero =>
    rw [raisingIterate_succ,
      loweringElement_smul_raisingElement_smul q V hne (raisingIterate q V w 0) (raisingWeight q lam 0)
        (weightElement_smul_raisingIterate q V w lam hKw 0) (inverseWeightElement_smul_raisingIterate q V w lam hlam hKw 0)]
    have hfw : loweringElement q • raisingIterate q V w 0 = 0 := by simpa using hf
    rw [hfw, smul_zero, zero_sub, loweringOnRaisingPowerCoeff, Finset.sum_range_one, neg_smul]
  | succ n ih =>
    rw [raisingIterate_succ,
      loweringElement_smul_raisingElement_smul q V hne (raisingIterate q V w (n + 1)) (raisingWeight q lam (n + 1))
        (weightElement_smul_raisingIterate q V w lam hKw (n + 1)) (inverseWeightElement_smul_raisingIterate q V w lam hlam hKw (n + 1)),
      ih, smul_comm (raisingElement q) (loweringOnRaisingPowerCoeff q lam n), ← raisingIterate_succ, ← sub_smul]
    congr 1
    have hstep : loweringOnRaisingPowerCoeff q lam (n + 1) = loweringOnRaisingPowerCoeff q lam n
        - ((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (raisingWeight q lam (n + 1) - (raisingWeight q lam (n + 1))⁻¹) := by
      simp only [loweringOnRaisingPowerCoeff, Finset.sum_range_succ]
      ring
    rw [hstep]

end LowerLadder

/-- If the order-th power of the raising element annihilates a finite-dimensional simple module, then its finrank is at most the parameter order. -/
theorem finrank_le_orderOf_of_raising_pow_smul_eq_zero (q : ℂˣ) (hq : IsOfFinOrder q) (hq2 : (q : ℂ) ^ 2 ≠ 1)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V]
    (he0 : ∀ w : V, raisingElement q ^ orderOf q • w = 0) :
    Module.finrank ℂ V ≤ orderOf q := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  have hℓpos : 0 < orderOf q := hq.orderOf_pos
  have hqinv : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one q hq2
  classical
  
  have key : ∃ (v : V) (lam : ℂ),
      v ≠ 0 ∧ raisingElement q • v = 0 ∧ weightElement q • v = lam • v ∧ lam ≠ 0 := by
    obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (weightActionEnd q V)
    obtain ⟨w₀, hw₀mem, hw₀0⟩ := hμ₀.exists_hasEigenvector
    have hμ₀0 : μ₀ ≠ 0 := weightActionEnd_eigenvalue_ne_zero q V μ₀ hμ₀
    have hKw₀ : weightActionEnd q V w₀ = μ₀ • w₀ := Module.End.mem_eigenspace_iff.mp hw₀mem
    
    have hchain : ∀ j : ℕ,
        weightActionEnd q V (raisingElement q ^ j • w₀) = (((q : ℂ) ^ 2) ^ j * μ₀) • (raisingElement q ^ j • w₀) := by
      intro j
      induction j with
      | zero => simpa using hKw₀
      | succ n ih =>
        have hsplit : raisingElement q ^ (n + 1) • w₀ = raisingElement q • (raisingElement q ^ n • w₀) := by rw [pow_succ', mul_smul]
        rw [hsplit, weightActionEnd_smul_raisingElement q V _ _ ih]
        congr 1
        ring
    have hex : ∃ k, raisingElement q ^ k • w₀ = 0 := ⟨orderOf q, he0 w₀⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have hs := Nat.find_spec hex
      rw [h, pow_zero, one_smul] at hs
      exact hw₀0 hs
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    refine ⟨raisingElement q ^ m • w₀, ((q : ℂ) ^ 2) ^ m * μ₀, Nat.find_min hex (by omega), ?_, ?_, ?_⟩
    · have hs := Nat.find_spec hex
      rw [hm] at hs
      rw [← mul_smul, ← pow_succ']
      exact hs
    · have h := hchain m
      rw [weightActionEnd_apply] at h
      exact h
    · exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ q.ne_zero)) hμ₀0
  obtain ⟨v, lam, hv0, he, hKv, hlam⟩ := key
  
  obtain ⟨fb, hfb⟩ := loweringElement_order_pow_smul_eq_scalar q V hq2
  have hladder_ℓ : loweringIterate q V v (orderOf q) = fb • v := hfb v
  
  set b : Fin (orderOf q) → V := fun i => loweringIterate q V v ↑i with hb
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hW
  have hb_mem : ∀ (n : ℕ), n < orderOf q → loweringIterate q V v n ∈ W :=
    fun n hn => Submodule.subset_span (Set.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩)
  have hvW : v ∈ W := by
    have h0 := hb_mem 0 hℓpos
    rwa [loweringIterate_zero] at h0
  
  have heW : ∀ i : Fin (orderOf q), raisingElement q • b i ∈ W := by
    intro i
    change raisingElement q • loweringIterate q V v ↑i ∈ W
    rcases Nat.eq_zero_or_pos (↑i : ℕ) with hi0 | hipos
    · rw [hi0, loweringIterate_zero, he]; exact W.zero_mem
    · obtain ⟨j, hj⟩ : ∃ j, (↑i : ℕ) = j + 1 := ⟨↑i - 1, by omega⟩
      have hi := i.isLt
      rw [hj, raisingElement_smul_loweringIterate_succ q V hqinv v lam hlam he hKv j]
      exact W.smul_mem _ (hb_mem j (by omega))
  have hfW : ∀ i : Fin (orderOf q), loweringElement q • b i ∈ W := by
    intro i
    change loweringElement q • loweringIterate q V v ↑i ∈ W
    rw [← loweringIterate_succ q V v ↑i]
    rcases eq_or_lt_of_le (show (↑i : ℕ) + 1 ≤ orderOf q from i.isLt) with heq | hlt
    · rw [heq, hladder_ℓ]; exact W.smul_mem _ hvW
    · exact hb_mem (↑i + 1) hlt
  have hKW : ∀ i : Fin (orderOf q), weightElement q • b i ∈ W := by
    intro i
    change weightElement q • loweringIterate q V v ↑i ∈ W
    rw [weightElement_smul_loweringIterate q V v lam hKv ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  have hLW : ∀ i : Fin (orderOf q), inverseWeightElement q • b i ∈ W := by
    intro i
    change inverseWeightElement q • loweringIterate q V v ↑i ∈ W
    rw [inverseWeightElement_smul_loweringIterate q V v lam hlam hKv ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  have clOf : ∀ (a : QuantumSL2 q), (∀ i : Fin (orderOf q), a • b i ∈ W) → ∀ x ∈ W, a • x ∈ W := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ha i
    | zero => rw [smul_zero]; exact W.zero_mem
    | add p r _ _ hp hr => rw [smul_add]; exact W.add_mem hp hr
    | smul c p _ hp => rw [smul_comm]; exact W.smul_mem c hp
  
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (W : Set V)
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      smul_mem' := fun a x hx => smul_mem_of_stable_generators q V W (clOf (raisingElement q) heW)
        (clOf (loweringElement q) hfW) (clOf (weightElement q) hKW) (clOf (inverseWeightElement q) hLW) a x hx }
  have hvW' : v ∈ W' := hvW
  have hne' : W' ≠ ⊥ := by
    intro hbot
    apply hv0
    have hmem : v ∈ (⊥ : Submodule (QuantumSL2 q) V) := hbot ▸ hvW'
    exact (Submodule.mem_bot (QuantumSL2 q)).mp hmem
  have hW'top : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne'
  have hWtop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxW' : x ∈ W' := by rw [hW'top]; exact Submodule.mem_top
    exact hxW'
  
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range b)) ≤ orderOf q := by
    have hcard := finrank_range_le_card (R := ℂ) b
    rwa [Set.finrank, Fintype.card_fin] at hcard
  rw [← hW, hWtop, finrank_top] at hspan
  exact hspan

/-- If the order-th power of the lowering element annihilates a finite-dimensional simple module, then its finrank is at most the parameter order. -/
theorem finrank_le_orderOf_of_lowering_pow_smul_eq_zero (q : ℂˣ) (hq : IsOfFinOrder q) (hq2 : (q : ℂ) ^ 2 ≠ 1)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V]
    (hf0 : ∀ w : V, loweringElement q ^ orderOf q • w = 0) :
    Module.finrank ℂ V ≤ orderOf q := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  have hℓpos : 0 < orderOf q := hq.orderOf_pos
  have hqinv : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one q hq2
  classical
  
  have key : ∃ (w : V) (lam : ℂ),
      w ≠ 0 ∧ loweringElement q • w = 0 ∧ weightElement q • w = lam • w ∧ lam ≠ 0 := by
    obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (weightActionEnd q V)
    obtain ⟨w₀, hw₀mem, hw₀0⟩ := hμ₀.exists_hasEigenvector
    have hμ₀0 : μ₀ ≠ 0 := weightActionEnd_eigenvalue_ne_zero q V μ₀ hμ₀
    have hKw₀ : weightActionEnd q V w₀ = μ₀ • w₀ := Module.End.mem_eigenspace_iff.mp hw₀mem
    
    have hchain : ∀ j : ℕ,
        weightActionEnd q V (loweringElement q ^ j • w₀) = ((((q : ℂ) ^ 2)⁻¹) ^ j * μ₀) • (loweringElement q ^ j • w₀) := by
      intro j
      induction j with
      | zero => simpa using hKw₀
      | succ n ih =>
        have hsplit : loweringElement q ^ (n + 1) • w₀ = loweringElement q • (loweringElement q ^ n • w₀) := by rw [pow_succ', mul_smul]
        rw [hsplit, weightActionEnd_smul_loweringElement q V _ _ ih]
        congr 1
        rw [pow_succ]
        ring
    have hex : ∃ k, loweringElement q ^ k • w₀ = 0 := ⟨orderOf q, hf0 w₀⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have hs := Nat.find_spec hex
      rw [h, pow_zero, one_smul] at hs
      exact hw₀0 hs
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    refine ⟨loweringElement q ^ m • w₀, (((q : ℂ) ^ 2)⁻¹) ^ m * μ₀, Nat.find_min hex (by omega), ?_, ?_, ?_⟩
    · have hs := Nat.find_spec hex
      rw [hm] at hs
      rw [← mul_smul, ← pow_succ']
      exact hs
    · have h := hchain m
      rw [weightActionEnd_apply] at h
      exact h
    · exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ q.ne_zero))) hμ₀0
  obtain ⟨w, lam, hw0, hf, hKw, hlam⟩ := key
  
  obtain ⟨ea, hea⟩ := raisingElement_order_pow_smul_eq_scalar q V hq2
  have heladder_ℓ : raisingIterate q V w (orderOf q) = ea • w := hea w
  
  set b : Fin (orderOf q) → V := fun i => raisingIterate q V w ↑i with hb
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hW
  have hb_mem : ∀ (n : ℕ), n < orderOf q → raisingIterate q V w n ∈ W :=
    fun n hn => Submodule.subset_span (Set.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩)
  have hwW : w ∈ W := by
    have h0 := hb_mem 0 hℓpos
    rwa [raisingIterate_zero] at h0
  
  have hfW : ∀ i : Fin (orderOf q), loweringElement q • b i ∈ W := by
    intro i
    change loweringElement q • raisingIterate q V w ↑i ∈ W
    rcases Nat.eq_zero_or_pos (↑i : ℕ) with hi0 | hipos
    · rw [hi0, raisingIterate_zero, hf]; exact W.zero_mem
    · obtain ⟨j, hj⟩ : ∃ j, (↑i : ℕ) = j + 1 := ⟨↑i - 1, by omega⟩
      have hi := i.isLt
      rw [hj, loweringElement_smul_raisingIterate_succ q V hqinv w lam hlam hf hKw j]
      exact W.smul_mem _ (hb_mem j (by omega))
  have heW : ∀ i : Fin (orderOf q), raisingElement q • b i ∈ W := by
    intro i
    change raisingElement q • raisingIterate q V w ↑i ∈ W
    rw [← raisingIterate_succ q V w ↑i]
    rcases eq_or_lt_of_le (show (↑i : ℕ) + 1 ≤ orderOf q from i.isLt) with heq | hlt
    · rw [heq, heladder_ℓ]; exact W.smul_mem _ hwW
    · exact hb_mem (↑i + 1) hlt
  have hKW : ∀ i : Fin (orderOf q), weightElement q • b i ∈ W := by
    intro i
    change weightElement q • raisingIterate q V w ↑i ∈ W
    rw [weightElement_smul_raisingIterate q V w lam hKw ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  have hLW : ∀ i : Fin (orderOf q), inverseWeightElement q • b i ∈ W := by
    intro i
    change inverseWeightElement q • raisingIterate q V w ↑i ∈ W
    rw [inverseWeightElement_smul_raisingIterate q V w lam hlam hKw ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  have clOf : ∀ (a : QuantumSL2 q), (∀ i : Fin (orderOf q), a • b i ∈ W) → ∀ x ∈ W, a • x ∈ W := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ha i
    | zero => rw [smul_zero]; exact W.zero_mem
    | add p r _ _ hp hr => rw [smul_add]; exact W.add_mem hp hr
    | smul c p _ hp => rw [smul_comm]; exact W.smul_mem c hp
  
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (W : Set V)
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      smul_mem' := fun a x hx => smul_mem_of_stable_generators q V W (clOf (raisingElement q) heW)
        (clOf (loweringElement q) hfW) (clOf (weightElement q) hKW) (clOf (inverseWeightElement q) hLW) a x hx }
  have hwW' : w ∈ W' := hwW
  have hne' : W' ≠ ⊥ := by
    intro hbot
    apply hw0
    have hmem : w ∈ (⊥ : Submodule (QuantumSL2 q) V) := hbot ▸ hwW'
    exact (Submodule.mem_bot (QuantumSL2 q)).mp hmem
  have hW'top : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne'
  have hWtop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxW' : x ∈ W' := by rw [hW'top]; exact Submodule.mem_top
    exact hxW'
  
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range b)) ≤ orderOf q := by
    have hcard := finrank_range_le_card (R := ℂ) b
    rwa [Set.finrank, Fintype.card_fin] at hcard
  rw [← hW, hWtop, finrank_top] at hspan
  exact hspan

/-- If the order-th powers of the raising and lowering elements act by nonzero scalars, then the finrank of the simple module is at most the parameter order. -/
theorem finrank_le_orderOf_of_raising_lowering_pow_smul_ne_zero (q : ℂˣ) (hq : IsOfFinOrder q) (hq2 : (q : ℂ) ^ 2 ≠ 1)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V]
    (a : ℂ) (_ha : ∀ v : V, raisingElement q ^ orderOf q • v = a • v) (_ha0 : a ≠ 0)
    (b : ℂ) (hb : ∀ v : V, loweringElement q ^ orderOf q • v = b • v) (hb0 : b ≠ 0) :
    Module.finrank ℂ V ≤ orderOf q := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (QuantumSL2 q) V
  have hℓpos : 0 < orderOf q := hq.orderOf_pos
  have hqinv : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one q hq2
  classical
  
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (weightActionEnd q V)
  have hμ₀0 : μ₀ ≠ 0 := weightActionEnd_eigenvalue_ne_zero q V μ₀ hμ₀
  
  
  have hmaps : ∀ w ∈ Module.End.eigenspace (weightActionEnd q V) μ₀,
      algebraActionEnd q V (loweringElement q * raisingElement q) w ∈ Module.End.eigenspace (weightActionEnd q V) μ₀ := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw
    have hqz : (q : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 q.ne_zero
    have hew : weightActionEnd q V (raisingElement q • w) = ((q : ℂ) ^ 2 * μ₀) • (raisingElement q • w) :=
      weightActionEnd_smul_raisingElement q V μ₀ w hw
    have hfew : weightActionEnd q V (loweringElement q • (raisingElement q • w))
        = (((q : ℂ) ^ 2)⁻¹ * ((q : ℂ) ^ 2 * μ₀)) • (loweringElement q • (raisingElement q • w)) :=
      weightActionEnd_smul_loweringElement q V ((q : ℂ) ^ 2 * μ₀) (raisingElement q • w) hew
    rw [algebraActionEnd_apply, Module.End.mem_eigenspace_iff, mul_smul, hfew,
      inv_mul_cancel_left₀ hqz]
  
  haveI : Nontrivial (Module.End.eigenspace (weightActionEnd q V) μ₀) := by
    obtain ⟨w₀, hw₀mem, hw₀0⟩ := hμ₀.exists_hasEigenvector
    exact ⟨⟨⟨w₀, hw₀mem⟩, 0, fun h => hw₀0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨ρ, v, hv0, hKv, hfe⟩ : ∃ (ρ : ℂ) (v : V),
      v ≠ 0 ∧ weightElement q • v = μ₀ • v ∧ loweringElement q • (raisingElement q • v) = ρ • v := by
    obtain ⟨ρ, hρ⟩ :=
      Module.End.exists_eigenvalue ((algebraActionEnd q V (loweringElement q * raisingElement q)).restrict hmaps)
    obtain ⟨v', hv'mem, hv'0⟩ := hρ.exists_hasEigenvector
    refine ⟨ρ, (v' : V), ?_, ?_, ?_⟩
    · simp only [ne_eq, Submodule.coe_eq_zero]; exact hv'0
    · have h := Module.End.mem_eigenspace_iff.mp v'.2
      rwa [weightActionEnd_apply] at h
    · have hTv := Module.End.mem_eigenspace_iff.mp hv'mem
      have hcoe := congrArg (Subtype.val) hTv
      simpa only [LinearMap.coe_restrict_apply, algebraActionEnd_apply, Submodule.coe_smul,
        mul_smul] using hcoe
  
  obtain ⟨m, hm⟩ : ∃ m, orderOf q = m + 1 := ⟨orderOf q - 1, by omega⟩
  have hev : raisingElement q • v = (b⁻¹ * ρ) • loweringIterate q V v m := by
    have h1 : loweringElement q ^ m • (loweringElement q • (raisingElement q • v)) = loweringElement q ^ m • (ρ • v) := by rw [hfe]
    rw [← mul_smul, ← pow_succ, ← hm, hb (raisingElement q • v), smul_comm (loweringElement q ^ m) ρ v] at h1
    have h2 := congrArg (fun x : V => (b⁻¹ : ℂ) • x) h1
    simp only [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h2
    exact h2
  
  set bv : Fin (orderOf q) → V := fun i => loweringIterate q V v ↑i with hbv
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range bv) with hW
  have hb_mem : ∀ (n : ℕ), n < orderOf q → loweringIterate q V v n ∈ W :=
    fun n hn => Submodule.subset_span (Set.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩)
  have hvW : v ∈ W := by
    have h0 := hb_mem 0 hℓpos
    rwa [loweringIterate_zero] at h0
  have hladder_ℓ : loweringIterate q V v (orderOf q) = b • v := hb v
  
  have hfW : ∀ i : Fin (orderOf q), loweringElement q • bv i ∈ W := by
    intro i
    change loweringElement q • loweringIterate q V v ↑i ∈ W
    rw [← loweringIterate_succ q V v ↑i]
    rcases eq_or_lt_of_le (show (↑i : ℕ) + 1 ≤ orderOf q from i.isLt) with heq | hlt
    · rw [heq, hladder_ℓ]; exact W.smul_mem _ hvW
    · exact hb_mem (↑i + 1) hlt
  have clOf : ∀ (a : QuantumSL2 q), (∀ i : Fin (orderOf q), a • bv i ∈ W) → ∀ x ∈ W, a • x ∈ W := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ha i
    | zero => rw [smul_zero]; exact W.zero_mem
    | add p r _ _ hp hr => rw [smul_add]; exact W.add_mem hp hr
    | smul c p _ hp => rw [smul_comm]; exact W.smul_mem c hp
  have hfWall : ∀ x ∈ W, loweringElement q • x ∈ W := clOf (loweringElement q) hfW
  
  have hladder_all : ∀ n, loweringIterate q V v n ∈ W := by
    intro n
    induction n with
    | zero => rw [loweringIterate_zero]; exact hvW
    | succ k ih => rw [loweringIterate_succ]; exact hfWall _ ih
  have hevW : raisingElement q • v ∈ W := by rw [hev]; exact W.smul_mem _ (hladder_all m)
  
  have heW_all : ∀ n, raisingElement q • loweringIterate q V v n ∈ W := by
    intro n
    induction n with
    | zero => rw [loweringIterate_zero]; exact hevW
    | succ k ih =>
      have hrec : raisingElement q • loweringIterate q V v (k + 1)
          = loweringElement q • (raisingElement q • loweringIterate q V v k)
            + (((q : ℂ) - (q : ℂ)⁻¹)⁻¹ * (loweringWeight q μ₀ k - (loweringWeight q μ₀ k)⁻¹)) • loweringIterate q V v k := by
        rw [loweringIterate_succ]
        exact raisingElement_smul_loweringElement_smul q V hqinv (loweringIterate q V v k) (loweringWeight q μ₀ k)
          (weightElement_smul_loweringIterate q V v μ₀ hKv k) (inverseWeightElement_smul_loweringIterate q V v μ₀ hμ₀0 hKv k)
      rw [hrec]
      exact W.add_mem (hfWall _ ih) (W.smul_mem _ (hladder_all k))
  have heW : ∀ i : Fin (orderOf q), raisingElement q • bv i ∈ W := fun i => heW_all ↑i
  have hKW : ∀ i : Fin (orderOf q), weightElement q • bv i ∈ W := by
    intro i
    change weightElement q • loweringIterate q V v ↑i ∈ W
    rw [weightElement_smul_loweringIterate q V v μ₀ hKv ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  have hLW : ∀ i : Fin (orderOf q), inverseWeightElement q • bv i ∈ W := by
    intro i
    change inverseWeightElement q • loweringIterate q V v ↑i ∈ W
    rw [inverseWeightElement_smul_loweringIterate q V v μ₀ hμ₀0 hKv ↑i]
    exact W.smul_mem _ (hb_mem ↑i i.isLt)
  
  let W' : Submodule (QuantumSL2 q) V :=
    { carrier := (W : Set V)
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      smul_mem' := fun a x hx => smul_mem_of_stable_generators q V W (clOf (raisingElement q) heW)
        (clOf (loweringElement q) hfW) (clOf (weightElement q) hKW) (clOf (inverseWeightElement q) hLW) a x hx }
  have hvW' : v ∈ W' := hvW
  have hne' : W' ≠ ⊥ := by
    intro hbot
    apply hv0
    have hmem : v ∈ (⊥ : Submodule (QuantumSL2 q) V) := hbot ▸ hvW'
    exact (Submodule.mem_bot (QuantumSL2 q)).mp hmem
  have hW'top : W' = ⊤ := (eq_bot_or_eq_top W').resolve_left hne'
  have hWtop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxW' : x ∈ W' := by rw [hW'top]; exact Submodule.mem_top
    exact hxW'
  
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range bv)) ≤ orderOf q := by
    have hcard := finrank_range_le_card (R := ℂ) bv
    rwa [Set.finrank, Fintype.card_fin] at hcard
  rw [← hW, hWtop, finrank_top] at hspan
  exact hspan

/-- A finite-dimensional simple module at a finite-order parameter has finrank at most the parameter order when its square is not one. -/
theorem finrank_le_orderOf (q : ℂˣ) (hq : IsOfFinOrder q)
    (hq2 : (q : ℂ) ^ 2 ≠ 1)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (QuantumSL2 q) V]
    [IsScalarTower ℂ (QuantumSL2 q) V] [FiniteDimensional ℂ V] [IsSimpleModule (QuantumSL2 q) V] :
    Module.finrank ℂ V ≤ orderOf q := by
  obtain ⟨a, ha⟩ := raisingElement_order_pow_smul_eq_scalar q V hq2
  by_cases ha0 : a = 0
  · exact finrank_le_orderOf_of_raising_pow_smul_eq_zero q hq hq2 V
      (fun w => by rw [ha w, ha0, zero_smul])
  · obtain ⟨b, hb⟩ := loweringElement_order_pow_smul_eq_scalar q V hq2
    by_cases hb0 : b = 0
    · exact finrank_le_orderOf_of_lowering_pow_smul_eq_zero q hq hq2 V
        (fun w => by rw [hb w, hb0, zero_smul])
    · exact finrank_le_orderOf_of_raising_lowering_pow_smul_ne_zero q hq hq2 V a ha ha0 b hb hb0

end RepresentationTheory.QuantumGroup.SL2Representations



attribute [nolint defsWithUnderscore]
  RepresentationTheory.QuantumGroup.SL2Representations.Generator
  RepresentationTheory.QuantumGroup.SL2Representations.auxiliaryFreeAlgebraElementThree
  RepresentationTheory.QuantumGroup.SL2Representations.auxiliaryFreeAlgebraElementFour
  RepresentationTheory.QuantumGroup.SL2Representations.auxiliaryFreeAlgebraElementOne
  RepresentationTheory.QuantumGroup.SL2Representations.auxiliaryFreeAlgebraElementTwo
  RepresentationTheory.QuantumGroup.SL2Representations.QuantumSL2
  RepresentationTheory.QuantumGroup.SL2Representations.freeAlgebraMap
  RepresentationTheory.QuantumGroup.SL2Representations.raisingElement
  RepresentationTheory.QuantumGroup.SL2Representations.loweringElement
  RepresentationTheory.QuantumGroup.SL2Representations.weightElement
  RepresentationTheory.QuantumGroup.SL2Representations.inverseWeightElement
  RepresentationTheory.QuantumGroup.SL2Representations.complexCharacter
  RepresentationTheory.QuantumGroup.SL2Representations.weightActionEnd
  RepresentationTheory.QuantumGroup.SL2Representations.loweringIterate
  RepresentationTheory.QuantumGroup.SL2Representations.loweringWeight
  RepresentationTheory.QuantumGroup.SL2Representations.raisingOnLoweringPowerCoeff
  RepresentationTheory.QuantumGroup.SL2Representations.algebraActionEnd
  RepresentationTheory.QuantumGroup.SL2Representations.raisingIterate
  RepresentationTheory.QuantumGroup.SL2Representations.raisingWeight
  RepresentationTheory.QuantumGroup.SL2Representations.loweringOnRaisingPowerCoeff
