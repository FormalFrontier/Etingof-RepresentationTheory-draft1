/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
import RepresentationTheory.Quiver.FiniteOrbitDimensionBounds
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.PolynomialRepresentation.FiniteOrbits

open _root_.MvPolynomial MulAction
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization

variable {k : Type} [Field k]




/-- The coordinate vector of a vector relative to a basis indexed by `Fin`. -/
noncomputable def basisCoordinates {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (v : V) : Fin d → k :=
  fun i => b.repr v i



/-- A subset of a finite-dimensional vector space is polynomially dense when every coordinate polynomial that vanishes on the subset is zero. -/
def IsPolynomiallyDense {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (X : Set V) : Prop :=
  ∀ f : MvPolynomial (Fin d) k,
    (∀ v ∈ X, aeval (basisCoordinates b v) f = 0) → f = 0

private noncomputable def vectorOfCoords {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (c : Fin d → k) : V :=
  b.repr.symm (Finsupp.equivFunOnFinite.symm c)

@[simp] private theorem vectorCoords_vectorOfCoords
    {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (c : Fin d → k) :
    basisCoordinates b (vectorOfCoords b c) = c := by
  funext i
  simp [basisCoordinates, vectorOfCoords]



/-- An action with finitely many orbits on a finite-dimensional vector space over an infinite field has a polynomially dense orbit. -/
@[source_ref "Chapter6/Problem6.1.2" (role := primary)]
theorem exists_isPolynomiallyDense_orbit_of_finite_orbits
    [Infinite k] {G V : Type*} [Group G] [AddCommGroup V] [Module k V] [MulAction G V]
    {d : ℕ} (b : Module.Basis (Fin d) k V)
    [Finite (orbitRel.Quotient G V)] :
    ∃ v₀ : V, IsPolynomiallyDense b (orbit G v₀) := by
  classical
  by_contra h
  push Not at h
  letI : Fintype (orbitRel.Quotient G V) := Fintype.ofFinite _
  have hw : ∀ q : orbitRel.Quotient G V,
      ∃ f : MvPolynomial (Fin d) k,
        (∀ v ∈ orbit G q.out, aeval (basisCoordinates b v) f = 0) ∧ f ≠ 0 := by
    intro q
    have hq := h q.out
    unfold IsPolynomiallyDense at hq
    push Not at hq
    exact hq
  choose f hfvan hf0 using hw
  let F : MvPolynomial (Fin d) k := ∏ q : orbitRel.Quotient G V, f q
  have hFne : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => hf0 q
  apply hFne
  apply MvPolynomial.funext
  intro c
  rw [map_zero]
  let v := vectorOfCoords b c
  let q : orbitRel.Quotient G V := Quotient.mk'' v
  have hv : v ∈ orbit G q.out := by
    rw [← q.orbit_eq_orbit_out Quotient.out_eq', orbitRel.Quotient.orbit_mk]
    exact mem_orbit_self v
  have hzero : aeval (basisCoordinates b v) (f q) = 0 := hfvan q v hv
  have hc : basisCoordinates b v = c := vectorCoords_vectorOfCoords b c
  change eval c F = 0
  rw [← hc, show F = ∏ q : orbitRel.Quotient G V, f q from rfl, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ q) hzero



section RegularCoefficients

variable {G V B : Type*} [Group G] [AddCommGroup V] [Module k V]
  [CommRing B] [Algebra k B] [MulAction G V]
  (ev : G → B →ₐ[k] k) (ρ : Representation k G V)
  {d : ℕ} (b : Module.Basis (Fin d) k V)
  (P : Fin d → Fin d → B)



/-- The algebra homomorphism sending coordinate variables to the entries of a coefficient matrix applied to the coordinate vector of a based vector. -/
noncomputable def matrixVectorSubstitutionAlgHom (v₀ : V) : MvPolynomial (Fin d) k →ₐ[k] B :=
  aeval fun a => ∑ c : Fin d, (b.repr v₀ c) • P a c

omit [MulAction G V] in
private theorem repr_apply_eq_sum (g : G) (v : V) (a : Fin d) :
    b.repr (ρ g v) a = ∑ c : Fin d, b.repr v c * b.repr (ρ g (b c)) a := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, LinearMapClass.map_smul]
  change (Finsupp.applyAddHom a) (∑ x, (b.repr v) x • b.repr (ρ g (b x))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change ((b.repr v c) • b.repr (ρ g (b c))) a = _
  rw [Finsupp.smul_apply, smul_eq_mul]

omit [MulAction G V] in


/-- Evaluating a matrix-vector substitution at a group element agrees with polynomial evaluation at the coordinates of the represented vector when the matrix entries realize the representation. -/
theorem eval_comp_matrixVectorSubstitutionAlgHom
    (hP : ∀ (g : G) (a c : Fin d), b.repr (ρ g (b c)) a = ev g (P a c))
    (g : G) (v₀ : V) :
    (ev g).comp (matrixVectorSubstitutionAlgHom b P v₀) =
      aeval (basisCoordinates b (ρ g v₀)) := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [AlgHom.comp_apply, matrixVectorSubstitutionAlgHom, aeval_X, aeval_X, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [basisCoordinates, repr_apply_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hP]


/-- A matrix-vector substitution is injective when its evaluations realize a representation on a polynomially dense orbit. -/
theorem matrixVectorSubstitutionAlgHom_injective_of_isPolynomiallyDense_orbit
    (hact : ∀ (g : G) (v : V), g • v = ρ g v)
    (hP : ∀ (g : G) (a c : Fin d), b.repr (ρ g (b c)) a = ev g (P a c))
    (v₀ : V)
    (hdense : IsPolynomiallyDense b (orbit G v₀)) :
    Function.Injective (matrixVectorSubstitutionAlgHom b P v₀) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply hdense
  intro v hv
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  have h := congrArg (ev g) hf
  rw [map_zero, ← AlgHom.comp_apply,
    eval_comp_matrixVectorSubstitutionAlgHom ev ρ b P hP] at h
  simpa only [hact] using h

end RegularCoefficients






/-- The multiplicative action on a representation space obtained by applying the representing linear maps. -/
@[reducible] def mulActionOfRepresentation
    {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : MulAction G V where
  smul := fun g v => ρ g v
  one_smul := by
    intro v
    change ρ 1 v = v
    rw [map_one]
    rfl
  mul_smul := by
    intro g h v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl


/-- The orbit quotient of a representation, using the multiplicative action induced by its linear operators. -/
abbrev RepresentationOrbitQuotient
    {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :=
  @orbitRel.Quotient G V _ (mulActionOfRepresentation ρ)




/-- Evaluation of the determinant-localized matrix polynomial ring at an invertible matrix. -/
noncomputable def generalLinearEvalAlgHom {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) →ₐ[k] k where
  toFun := fun x => RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom x g
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' := fun r => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n × Fin n) k)
      (Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)), RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_algebraMap]
    simp [RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.matrix_polynomial_evaluation_apply]





/-- The algebra homomorphism obtained by multiplying a polynomial matrix by the coordinate vector of a based vector and passing to the determinant localization. -/
noncomputable def localizedMatrixVectorSubstitutionAlgHom
    {V : Type*} [AddCommGroup V] [Module k V]
    {n d : ℕ}
    (b : Module.Basis (Fin d) k V)
    (P : Fin d → Fin d → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k)
    (v₀ : V) :
    MvPolynomial (Fin d) k →ₐ[k] Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) :=
  matrixVectorSubstitutionAlgHom b (fun a c => RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)) v₀



/-- A polynomial representation of a general linear group with finitely many orbits admits an injective coordinate algebra map into the determinant-localized matrix polynomial ring. -/
@[source_ref "Chapter6/Problem6.1.2" (role := supporting)]
theorem exists_injective_localizedMatrixVectorSubstitutionAlgHom_of_finite_orbits
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty n ρ)
    [MulAction (Matrix.GeneralLinearGroup (Fin n) k) V]
    (hact : ∀ g v, g • v = ρ g v)
    [Finite (orbitRel.Quotient (Matrix.GeneralLinearGroup (Fin n) k) V)] :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k V)
      (P : Fin d → Fin d → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k)
      (v₀ : V),
      d = Module.finrank k V ∧
      Function.Injective (localizedMatrixVectorSubstitutionAlgHom b P v₀) := by
  classical
  obtain ⟨d, b, P, hP⟩ := hρ
  obtain ⟨v₀, hv₀⟩ :=
    exists_isPolynomiallyDense_orbit_of_finite_orbits (G := Matrix.GeneralLinearGroup (Fin n) k) b
  refine ⟨d, b, P, v₀, ?_, ?_⟩
  · simpa using (Module.finrank_eq_card_basis b).symm
  apply matrixVectorSubstitutionAlgHom_injective_of_isPolynomiallyDense_orbit
    (ev := fun g => generalLinearEvalAlgHom g) ρ b (fun a c => RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)) hact _ v₀ hv₀
  intro g a c
  change b.repr (ρ g (b c)) a = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)) g
  rw [← RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom_action_apply]
  exact hP g a c



/-- A polynomial representation of a general linear group carried by a compatible action with finitely many orbits has dimension at most the square of the matrix size. -/
theorem finrank_le_sq_of_finite_compatible_action_orbits
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty n ρ)
    [MulAction (Matrix.GeneralLinearGroup (Fin n) k) V]
    (hact : ∀ g v, g • v = ρ g v)
    [Finite (orbitRel.Quotient (Matrix.GeneralLinearGroup (Fin n) k) V)] :
    Module.finrank k V ≤ n ^ 2 := by
  obtain ⟨d, b, P, v₀, hd, hφ⟩ :=
    exists_injective_localizedMatrixVectorSubstitutionAlgHom_of_finite_orbits ρ hρ hact
  haveI : IsDomain (Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) :=
    IsLocalization.isDomain_localization (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.powers_auxiliary_polynomial_le_nonZeroDivisors (k := k) (N := n))
  have hle := RepresentationTheory.Quiver.FiniteOrbitDimensionBounds.MvPolynomial.card_le_card_of_injective_algHom_to_localization
    (S := Submonoid.powers (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) (localizedMatrixVectorSubstitutionAlgHom b P v₀) hφ
  rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, hd] at hle
  simpa [pow_two] using hle




/-- A polynomial representation of a general linear group with finite orbit quotient has dimension at most the square of the matrix size. -/
@[source_ref "Chapter6/Problem6.1.2" (role := supporting)]
theorem finrank_le_sq_of_finite_representation_orbits
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty n ρ)
    [Finite (RepresentationOrbitQuotient ρ)] :
    Module.finrank k V ≤ n ^ 2 := by
  letI : MulAction (Matrix.GeneralLinearGroup (Fin n) k) V :=
    mulActionOfRepresentation ρ
  exact finrank_le_sq_of_finite_compatible_action_orbits ρ hρ (fun _ _ => rfl)






/-- The condition that a finite-dimensional representation of a product of general linear groups is polynomial in the matrix entries. -/
def IsPolynomialGeneralLinearProductRepresentation
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) k V)
    (P : Fin d → Fin d →
      Localization.Away (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)),
    ∀ (g : RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (a c : Fin d),
      b.repr (ρ g (b c)) a =
        RepresentationTheory.Quiver.Representation.DenseOrbit.baseChangePointEval m g (P a c)




/-- A polynomial representation of a product of general linear groups carried by a compatible action with finitely many orbits has dimension at most the sum of the squares of the block sizes. -/
theorem finrank_le_sum_sq_of_finite_compatible_action_orbits
    [Infinite k]
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V)
    [MulAction (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V]
    (hact : ∀ g v, g • v = ρ g v)
    (hρ : IsPolynomialGeneralLinearProductRepresentation m ρ)
    [Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V)] :
    Module.finrank k V ≤ ∑ i : Fin r, (m i) ^ 2 := by
  classical
  obtain ⟨d, b, P, hP⟩ := hρ
  obtain ⟨v₀, hv₀⟩ := exists_isPolynomiallyDense_orbit_of_finite_orbits (G := RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) b
  let φ := matrixVectorSubstitutionAlgHom b P v₀
  have hφ : Function.Injective φ :=
    matrixVectorSubstitutionAlgHom_injective_of_isPolynomiallyDense_orbit
      (ev := fun g => RepresentationTheory.Quiver.Representation.DenseOrbit.baseChangePointEval m g) ρ b P hact hP v₀ hv₀
  haveI : IsDomain
      (Localization.Away (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct_ne_zero (k := k) m))
  have hle := RepresentationTheory.Quiver.FiniteOrbitDimensionBounds.MvPolynomial.card_le_card_of_injective_algHom_to_localization
    (S := Submonoid.powers (RepresentationTheory.Quiver.GenericBaseChange.genericVertexDeterminantProduct (k := k) m)) φ hφ
  rw [Fintype.card_fin, RepresentationTheory.Quiver.GenericBaseChange.card_vertexMatrixIndex,
    show d = Module.finrank k V by simpa using (Module.finrank_eq_card_basis b).symm] at hle
  exact hle




/-- A polynomial representation of a product of general linear groups with finite orbit quotient has dimension at most the sum of the squares of the block sizes. -/
@[source_ref "Chapter6/Problem6.1.2" (role := primary)]
theorem finrank_le_sum_sq_of_finite_representation_orbits
    [Infinite k]
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V)
    (hρ : IsPolynomialGeneralLinearProductRepresentation m ρ)
    [Finite (RepresentationOrbitQuotient ρ)] :
    Module.finrank k V ≤ ∑ i : Fin r, (m i) ^ 2 := by
  letI : MulAction (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) V := mulActionOfRepresentation ρ
  exact finrank_le_sum_sq_of_finite_compatible_action_orbits
    m ρ (fun _ _ => rfl) hρ

end RepresentationTheory.PolynomialRepresentation.FiniteOrbits
