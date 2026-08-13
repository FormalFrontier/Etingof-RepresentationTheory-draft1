/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Weighted components
-/

noncomputable section

namespace RepresentationTheory.Algebra.MvPolynomial.WeightedComponents

open scoped Classical

variable (k N : ℕ)

/-- A type family indexed by two natural numbers. -/
abbrev NatPairIndexedType : Type := MvPolynomial (Fin k × Fin N × Fin N) ℂ

/-- A family, indexed by a finite type, of square matrices with entries in the indexed type. -/
noncomputable def NatPairIndexedType.finIndexedMatrix (i : Fin k) :
    Matrix (Fin N) (Fin N) (NatPairIndexedType k N) :=
  fun r c => MvPolynomial.X (i, r, c)

/-- An algebra endomorphism of the indexed type parametrized by a unit of complex square matrices. -/
noncomputable def NatPairIndexedType.matrixUnitsAlgHom (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    NatPairIndexedType k N →ₐ[ℂ] NatPairIndexedType k N :=
  MvPolynomial.aeval fun v : Fin k × Fin N × Fin N =>
    (((↑g : Matrix (Fin N) (Fin N) ℂ).map (algebraMap ℂ (NatPairIndexedType k N)))
        * NatPairIndexedType.finIndexedMatrix k N v.1
        * ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ).map (algebraMap ℂ (NatPairIndexedType k N))))
      v.2.1 v.2.2

/-- A complex subalgebra of the indexed type. -/
@[source_ref "Chapter5/Problem5.24.2" (role := supporting)]
noncomputable def NatPairIndexedType.complexSubalgebra : Subalgebra ℂ (NatPairIndexedType k N) :=
  ⨅ g : (Matrix (Fin N) (Fin N) ℂ)ˣ,
    AlgHom.equalizer (NatPairIndexedType.matrixUnitsAlgHom k N g)
      (AlgHom.id ℂ (NatPairIndexedType k N))

/-- An element of the indexed type assigned to every list of finite indices. -/
@[source_ref "Chapter5/Problem5.24.2" (role := supporting)]
noncomputable def NatPairIndexedType.listIndexedElement (w : List (Fin k)) : NatPairIndexedType k N :=
  Matrix.trace ((w.map (NatPairIndexedType.finIndexedMatrix k N)).prod)

private lemma prod_map_conj {M : Type*} [Monoid M] (a a' : M) (haa' : a * a' = 1)
    (ha'a : a' * a = 1) {ι : Type*} (f : ι → M) :
    ∀ l : List ι, (l.map (fun i => a * f i * a')).prod = a * (l.map f).prod * a'
  | [] => by simp [haa']
  | i :: t => by
      simp only [List.map_cons, List.prod_cons, prod_map_conj a a' haa' ha'a f t]
      simp only [mul_assoc]
      rw [← mul_assoc a' a, ha'a, one_mul]

/-- Every list-indexed element belongs to the displayed complex subalgebra. -/
theorem NatPairIndexedType.listIndexedElement_mem_complexSubalgebra (w : List (Fin k)) :
    NatPairIndexedType.listIndexedElement k N w ∈ NatPairIndexedType.complexSubalgebra k N := by
  rw [NatPairIndexedType.complexSubalgebra, Algebra.mem_iInf]
  intro g
  rw [AlgHom.mem_equalizer, AlgHom.id_apply]
  set G : Matrix (Fin N) (Fin N) (NatPairIndexedType k N) :=
    (↑g : Matrix (Fin N) (Fin N) ℂ).map (algebraMap ℂ (NatPairIndexedType k N)) with hG
  set G' : Matrix (Fin N) (Fin N) (NatPairIndexedType k N) :=
    (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ).map (algebraMap ℂ (NatPairIndexedType k N)) with hG'
  have hGG' : G * G' = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG'G : G' * G = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hconj : ∀ i, (NatPairIndexedType.finIndexedMatrix k N i).map
      (NatPairIndexedType.matrixUnitsAlgHom k N g)
      = G * NatPairIndexedType.finIndexedMatrix k N i * G' := by
    intro i
    refine Matrix.ext fun r c => ?_
    rw [Matrix.map_apply]
    change NatPairIndexedType.matrixUnitsAlgHom k N g (MvPolynomial.X (i, r, c)) = _
    rw [NatPairIndexedType.matrixUnitsAlgHom, MvPolynomial.aeval_X, ← hG, ← hG']
  have key : (NatPairIndexedType.matrixUnitsAlgHom k N g).mapMatrix
      ((w.map (NatPairIndexedType.finIndexedMatrix k N)).prod)
      = G * (w.map (NatPairIndexedType.finIndexedMatrix k N)).prod * G' := by
    rw [map_list_prod, List.map_map]
    have hcomp : ((NatPairIndexedType.matrixUnitsAlgHom k N g).mapMatrix ∘
        NatPairIndexedType.finIndexedMatrix k N)
        = fun i => G * NatPairIndexedType.finIndexedMatrix k N i * G' := by
      funext i; simp only [Function.comp_apply, AlgHom.mapMatrix_apply]; exact hconj i
    rw [hcomp]
    exact prod_map_conj G G' hGG' hG'G (NatPairIndexedType.finIndexedMatrix k N) w
  rw [NatPairIndexedType.listIndexedElement,
    AddMonoidHom.map_trace (NatPairIndexedType.matrixUnitsAlgHom k N g),
    ← AlgHom.mapMatrix_apply, key, Matrix.trace_mul_comm, ← mul_assoc, hG'G, one_mul]

open _root_.MvPolynomial

/-- A weight vector assigned to a tuple coordinate and a pair of matrix indices. -/
def NatPairIndexedType.variableWeight : Fin k × Fin N × Fin N → (Fin k →₀ ℕ) :=
  fun v => Finsupp.single v.1 1

/-- The image of a coordinate variable under the displayed algebra homomorphism is weighted homogeneous with its assigned weight. -/
theorem NatPairIndexedType.matrixUnitsAlgHom_X_isWeightedHomogeneous
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (v : Fin k × Fin N × Fin N) :
    IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
      (NatPairIndexedType.matrixUnitsAlgHom k N g (X v))
      (NatPairIndexedType.variableWeight k N v) := by
  obtain ⟨i, r, c⟩ := v
  have hCXC : ∀ (α β : ℂ) (a b : Fin N),
      IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
        (C α * X ((i, a, b) : Fin k × Fin N × Fin N) * C β) (Finsupp.single i 1) := by
    intro α β a b
    have hcxc : C α * X ((i, a, b) : Fin k × Fin N × Fin N) * C β
        = C (α * β) * X ((i, a, b) : Fin k × Fin N × Fin N) := by
      rw [mul_right_comm, ← map_mul]
    rw [hcxc]
    have hX : IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
        (X ((i, a, b) : Fin k × Fin N × Fin N) : NatPairIndexedType k N)
        (Finsupp.single i 1) :=
      isWeightedHomogeneous_X (R := ℂ) (NatPairIndexedType.variableWeight k N) (i, a, b)
    exact hX.C_mul _
  simp only [NatPairIndexedType.matrixUnitsAlgHom, MvPolynomial.aeval_X]
  rw [Matrix.mul_apply]
  apply IsWeightedHomogeneous.sum
  intro b _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply IsWeightedHomogeneous.sum
  intro a _
  simp only [Matrix.map_apply, MvPolynomial.algebraMap_eq, NatPairIndexedType.finIndexedMatrix]
  exact hCXC ((↑g : Matrix (Fin N) (Fin N) ℂ) r a) ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) b c) a b

/-- The image of a monomial under the displayed algebra homomorphism is weighted homogeneous with the weight of its exponent. -/
theorem NatPairIndexedType.matrixUnitsAlgHom_monomial_isWeightedHomogeneous
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (u : (Fin k × Fin N × Fin N) →₀ ℕ) (a : ℂ) :
    IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
      (NatPairIndexedType.matrixUnitsAlgHom k N g (monomial u a))
      (Finsupp.weight (NatPairIndexedType.variableWeight k N) u) := by
  have hbase : ∀ v, IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
      (NatPairIndexedType.matrixUnitsAlgHom k N g (X v))
      (NatPairIndexedType.variableWeight k N v) :=
    NatPairIndexedType.matrixUnitsAlgHom_X_isWeightedHomogeneous k N g
  rw [monomial_eq, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    MvPolynomial.algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  simp only [Finsupp.prod, map_prod, map_pow]
  rw [show Finsupp.weight (NatPairIndexedType.variableWeight k N) u
      = ∑ n ∈ u.support, (u n) • (NatPairIndexedType.variableWeight k N n) by
        rw [Finsupp.weight_apply]; rfl]
  exact IsWeightedHomogeneous.prod u.support
    (fun n => (NatPairIndexedType.matrixUnitsAlgHom k N g (X n)) ^ (u n))
    (fun n => (u n) • NatPairIndexedType.variableWeight k N n)
    (fun n _ => (hbase n).pow (u n))

/-- The displayed algebra homomorphism commutes with taking a weighted homogeneous component. -/
theorem NatPairIndexedType.weightedHomogeneousComponent_matrixUnitsAlgHom
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (d : Fin k →₀ ℕ) (p : NatPairIndexedType k N) :
    weightedHomogeneousComponent (NatPairIndexedType.variableWeight k N) d
        (NatPairIndexedType.matrixUnitsAlgHom k N g p)
      = NatPairIndexedType.matrixUnitsAlgHom k N g
          (weightedHomogeneousComponent (NatPairIndexedType.variableWeight k N) d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N) (monomial u a)
        (Finsupp.weight (NatPairIndexedType.variableWeight k N) u) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hcm : IsWeightedHomogeneous (NatPairIndexedType.variableWeight k N)
        (NatPairIndexedType.matrixUnitsAlgHom k N g (monomial u a))
        (Finsupp.weight (NatPairIndexedType.variableWeight k N) u) :=
      NatPairIndexedType.matrixUnitsAlgHom_monomial_isWeightedHomogeneous k N g u a
    by_cases hd : d = Finsupp.weight (NatPairIndexedType.variableWeight k N) u
    · subst hd
      rw [hcm.weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
    · rw [hcm.weightedHomogeneousComponent_ne d hd,
        hm.weightedHomogeneousComponent_ne d hd, map_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq]

/-- Taking a weighted homogeneous component preserves membership in the displayed complex subalgebra. -/
theorem NatPairIndexedType.weightedHomogeneousComponent_mem_complexSubalgebra
    (d : Fin k →₀ ℕ) {f : NatPairIndexedType k N}
    (hf : f ∈ NatPairIndexedType.complexSubalgebra k N) :
    weightedHomogeneousComponent (NatPairIndexedType.variableWeight k N) d f ∈
      NatPairIndexedType.complexSubalgebra k N := by
  rw [NatPairIndexedType.complexSubalgebra, Algebra.mem_iInf] at hf ⊢
  intro g
  rw [AlgHom.mem_equalizer, AlgHom.id_apply]
  have hg : NatPairIndexedType.matrixUnitsAlgHom k N g f = f := by
    have := hf g; rwa [AlgHom.mem_equalizer, AlgHom.id_apply] at this
  rw [← NatPairIndexedType.weightedHomogeneousComponent_matrixUnitsAlgHom k N g d f, hg]

end RepresentationTheory.Algebra.MvPolynomial.WeightedComponents
