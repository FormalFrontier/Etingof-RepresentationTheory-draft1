/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction
import RepresentationTheory.IntegerMatrix.ReflectionDynamics
import RepresentationTheory.IntegerVectorPredicate
import RepresentationTheory.Alignment.Attribute










































namespace RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup

open Matrix

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}





/-- The integer-valued pairing associated with an adjacency matrix. -/
def IntegralRootSystem.pairing (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) : ℤ :=
  dotProduct x ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec y)

/-- The associated pairing is the dot product with the corresponding matrix-vector product. -/
lemma IntegralRootSystem.pairing_eq_dotProduct_mulVec (x y : Fin n → ℤ) :
    IntegralRootSystem.pairing n adj x y = dotProduct x ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec y) := rfl


/-- A vector is a root exactly when it is nonzero and has self-pairing two. -/
lemma IntegralRootSystem.isRoot_iff_ne_zero_and_pairing_self_eq_two {x : Fin n → ℤ} :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x ↔ x ≠ 0 ∧ IntegralRootSystem.pairing n adj x x = 2 := Iff.rfl



section Reflection

variable {A : Matrix (Fin n) (Fin n) ℤ}


/-- A symmetric integer matrix gives the same paired dot product after exchanging its two vectors. -/
lemma Matrix.dotProduct_mulVec_comm_of_isSymm (hA : A.IsSymm) (x y : Fin n → ℤ) :
    dotProduct x (A.mulVec y) = dotProduct y (A.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show A j i = A i j from congr_fun (congr_fun hA i) j]
  ring


/-- Reflection fixes a vector whose dot product with the matrix image of the reflecting vector is zero. -/
@[source_ref "Chapter6/Remark6.4.11" (role := supporting)]
theorem IntegralRootSystem.reflection_eq_self_of_dotProduct_eq_zero (α v : Fin n → ℤ)
    (h : dotProduct v (A.mulVec α) = 0) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v = v := by
  simp [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, h]



/-- Reflection in a vector of self-pairing two sends that vector to its negation. -/
@[source_ref "Chapter6/Remark6.4.11" (role := supporting)]
theorem IntegralRootSystem.reflection_self (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α α = -α := by
  ext j
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, hα, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring


private lemma dotProduct_rootReflection (α v : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) :
    dotProduct (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v) (A.mulVec α) = -dotProduct v (A.mulVec α) := by
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, sub_dotProduct, smul_dotProduct, smul_eq_mul, hα]
  ring


/-- Reflection in a vector of self-pairing two is an involution. -/
theorem IntegralRootSystem.reflection_involutive (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) (v : Fin n → ℤ) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v) = v := by
  conv_lhs => rw [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, dotProduct_rootReflection α v hα, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  ring

/-- Reflection in a vector preserves addition. -/
lemma IntegralRootSystem.reflection_add (α u v : Fin n → ℤ) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α (u + v) = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α u + RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v := by
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, add_dotProduct, add_smul]
  abel

/-- Reflection in a vector commutes with integer scalar multiplication. -/
lemma IntegralRootSystem.reflection_zsmul (α : Fin n → ℤ) (c : ℤ) (v : Fin n → ℤ) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α (c • v) = c • RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v := by
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, smul_dotProduct, smul_eq_mul, mul_smul, smul_sub]





/-- The integer linear equivalence defined by reflection in a vector of self-pairing two. -/
def IntegralRootSystem.reflectionEquiv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) where
  toFun := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α
  map_add' := IntegralRootSystem.reflection_add α
  map_smul' := IntegralRootSystem.reflection_zsmul α
  invFun := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α
  left_inv := IntegralRootSystem.reflection_involutive α hα
  right_inv := IntegralRootSystem.reflection_involutive α hα

/-- The reflection equivalence acts by the corresponding reflection map. -/
@[simp]
lemma IntegralRootSystem.reflectionEquiv_apply (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) (v : Fin n → ℤ) :
    IntegralRootSystem.reflectionEquiv n A α hα v = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v := rfl

/-- The inverse of a reflection equivalence is the reflection equivalence itself. -/
@[simp]
lemma IntegralRootSystem.reflectionEquiv_symm (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) :
    (IntegralRootSystem.reflectionEquiv n A α hα).symm = IntegralRootSystem.reflectionEquiv n A α hα := rfl


/-- For a symmetric matrix, reflection in a vector of self-pairing two preserves the induced pairing. -/
@[source_ref "Chapter6/Remark6.4.11" (role := supporting)]
theorem IntegralRootSystem.reflection_preserves_dotProduct_mulVec (hA : A.IsSymm) (α : Fin n → ℤ)
    (hα : dotProduct α (A.mulVec α) = 2) (v w : Fin n → ℤ) :
    dotProduct (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v) (A.mulVec (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α w)) =
      dotProduct v (A.mulVec w) := by
  have hαw : dotProduct α (A.mulVec w) = dotProduct w (A.mulVec α) :=
    Matrix.dotProduct_mulVec_comm_of_isSymm hA α w
  have hαα : dotProduct α (A.mulVec α) = 2 := hα
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hαw, hαα]
  ring

end Reflection






/-- The subgroup of integer linear equivalences preserving the pairing associated with a matrix. -/
def IntegralRootSystem.isometrySubgroup (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Subgroup ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) where
  carrier := {f | ∀ v w, IntegralRootSystem.pairing n adj (f v) (f w) = IntegralRootSystem.pairing n adj v w}
  mul_mem' {f g} hf hg := fun v w => by
    change IntegralRootSystem.pairing n adj (f (g v)) (f (g w)) = IntegralRootSystem.pairing n adj v w
    rw [hf (g v) (g w), hg v w]
  one_mem' := fun _ _ => rfl
  inv_mem' {f} hf := fun v w => by
    have := hf (f.symm v) (f.symm w)
    rwa [f.apply_symm_apply, f.apply_symm_apply, eq_comm] at this

/-- An integer linear equivalence belongs to the isometry subgroup exactly when it preserves the associated pairing. -/
lemma IntegralRootSystem.mem_isometrySubgroup_iff {f : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} :
    f ∈ IntegralRootSystem.isometrySubgroup n adj ↔
      ∀ v w, IntegralRootSystem.pairing n adj (f v) (f w) = IntegralRootSystem.pairing n adj v w := Iff.rfl





/-- The integer linear equivalence given by reflection in a distinguished coordinate root. -/
def IntegralRootSystem.simpleReflectionEquiv (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  IntegralRootSystem.reflectionEquiv n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i) (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin i)

/-- A simple reflection equivalence acts by the corresponding coordinate reflection map. -/
@[simp]
lemma IntegralRootSystem.simpleReflectionEquiv_apply (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n)
    (v : Fin n → ℤ) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i v = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i v := rfl



/-- The square of a simple reflection equivalence is the identity. -/
@[simp]
lemma IntegralRootSystem.simpleReflectionEquiv_sq (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i * IntegralRootSystem.simpleReflectionEquiv hDynkin i = 1 := by
  refine LinearEquiv.ext fun v => ?_
  exact IntegralRootSystem.reflection_involutive _ (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin i) v


/-- A simple reflection sends its distinguished coordinate root to its negation. -/
lemma IntegralRootSystem.simpleReflectionEquiv_simpleRoot (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i) = -RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i :=
  IntegralRootSystem.reflection_self _ (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin i)


/-- A simple reflection fixes a vector paired to zero with its distinguished coordinate root. -/
lemma IntegralRootSystem.simpleReflectionEquiv_apply_eq_self_of_pairing_eq_zero (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n)
    (v : Fin n → ℤ) (h : IntegralRootSystem.pairing n adj v (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i) = 0) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i v = v :=
  IntegralRootSystem.reflection_eq_self_of_dotProduct_eq_zero _ _ h



/-- The subgroup of integer linear equivalences associated with the simple reflections of a finite integral root system. -/
def IntegralRootSystem.weylGroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Subgroup ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :=
  Subgroup.closure (Set.range (IntegralRootSystem.simpleReflectionEquiv hDynkin))

/-- Each simple reflection belongs to the associated reflection subgroup. -/
lemma IntegralRootSystem.simpleReflectionEquiv_mem_weylGroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i ∈ IntegralRootSystem.weylGroup hDynkin :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Each simple reflection belongs to the subgroup preserving the associated pairing. -/
lemma IntegralRootSystem.simpleReflectionEquiv_mem_isometrySubgroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (i : Fin n) :
    IntegralRootSystem.simpleReflectionEquiv hDynkin i ∈ IntegralRootSystem.isometrySubgroup n adj := fun v w =>
  IntegralRootSystem.reflection_preserves_dotProduct_mulVec (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1) _
    (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin i) v w


/-- The reflection subgroup is contained in the subgroup preserving the associated pairing. -/
theorem IntegralRootSystem.weylGroup_le_isometrySubgroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    IntegralRootSystem.weylGroup hDynkin ≤ IntegralRootSystem.isometrySubgroup n adj := by
  rw [IntegralRootSystem.weylGroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact IntegralRootSystem.simpleReflectionEquiv_mem_isometrySubgroup hDynkin i

/-- Every element of the reflection subgroup preserves the associated pairing. -/
theorem IntegralRootSystem.weylGroup_preserves_pairing (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} (hw : w ∈ IntegralRootSystem.weylGroup hDynkin) (v u : Fin n → ℤ) :
    IntegralRootSystem.pairing n adj (w v) (w u) = IntegralRootSystem.pairing n adj v u :=
  IntegralRootSystem.weylGroup_le_isometrySubgroup hDynkin hw v u




/-- Each distinguished coordinate root is a root for the specified adjacency matrix. -/
theorem IntegralRootSystem.isRoot_simpleRoot (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (i : Fin n) :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i) := by
  refine ⟨?_, RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin i⟩
  intro h
  have := congr_fun h i
  simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue] at this


/-- An element of the associated reflection subgroup sends a root to a root. -/
theorem _root_.RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_apply (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} (hw : w ∈ IntegralRootSystem.weylGroup hDynkin)
    {x : Fin n → ℤ} (hx : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x) : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj (w x) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact hx.1 ((LinearEquiv.map_eq_zero_iff w).mp h)
  · exact (IntegralRootSystem.weylGroup_preserves_pairing hDynkin hw x x).trans hx.2

/-- Every element of the reflection subgroup maps roots to roots. -/
theorem IntegralRootSystem.weylGroup_mapsTo_roots (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} (hw : w ∈ IntegralRootSystem.weylGroup hDynkin) :
    Set.MapsTo w {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} :=
  fun _ hx => RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_apply hDynkin hw hx


/-- The image of a distinguished coordinate root under an element of the reflection subgroup is a root. -/
theorem IntegralRootSystem.isRoot_weylGroup_apply_simpleRoot (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} (hw : w ∈ IntegralRootSystem.weylGroup hDynkin) (i : Fin n) :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj (w (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i)) :=
  RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_apply hDynkin hw (IntegralRootSystem.isRoot_simpleRoot hDynkin i)




/-- The inverse of an element of the associated reflection subgroup sends a root to a root. -/
theorem _root_.RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_symm_apply (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (w : IntegralRootSystem.weylGroup hDynkin)
    {x : Fin n → ℤ} (hx : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x) :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj ((w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)).symm x) :=
  RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_apply hDynkin (w⁻¹).2 hx


/-- The permutation of roots induced by an element of the reflection subgroup. -/
def IntegralRootSystem.weylGroupRootPerm (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (w : IntegralRootSystem.weylGroup hDynkin) :
    Equiv.Perm {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} where
  toFun x := ⟨(w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) x, RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_apply hDynkin w.2 x.2⟩
  invFun x := ⟨(w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)).symm x, RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.weylGroup_symm_apply hDynkin w x.2⟩
  left_inv _ := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (LinearEquiv.apply_symm_apply _ _)

/-- The root permutation induced by a reflection-subgroup element has the same underlying value as its linear action. -/
@[simp]
lemma IntegralRootSystem.weylGroupRootPerm_apply (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (w : IntegralRootSystem.weylGroup hDynkin)
    (x : {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x}) :
    (IntegralRootSystem.weylGroupRootPerm hDynkin w x : Fin n → ℤ) = (w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) x := rfl


/-- The monoid homomorphism from the reflection subgroup to permutations of the roots. -/
def IntegralRootSystem.weylGroupRootAction (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    IntegralRootSystem.weylGroup hDynkin →* Equiv.Perm {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} where
  toFun := IntegralRootSystem.weylGroupRootPerm hDynkin
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl



/-- Two integer linear equivalences are equal if they agree on every distinguished coordinate root. -/
theorem IntegralRootSystem.linearEquiv_ext_on_simpleRoots (f g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (h : ∀ i, f (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i) = g (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i)) : f = g := by
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
  simpa [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.basisFun_apply] using h i



/-- The action of the reflection subgroup on the roots is faithful. -/
@[source_ref "Chapter6/Remark6.4.11" (role := primary)]
theorem IntegralRootSystem.weylGroupRootAction_injective (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Function.Injective (IntegralRootSystem.weylGroupRootAction hDynkin) := by
  intro w₁ w₂ h
  refine Subtype.ext (IntegralRootSystem.linearEquiv_ext_on_simpleRoots _ _ fun i => ?_)
  have := congrArg (fun σ => (σ ⟨RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i, IntegralRootSystem.isRoot_simpleRoot hDynkin i⟩ : _)) h
  exact congrArg Subtype.val this







/-- The reflection subgroup associated with a finite integral root system is finite. -/
@[source_ref "Chapter6/Remark6.4.11" (role := primary)]
theorem IntegralRootSystem.finite_weylGroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Finite (IntegralRootSystem.weylGroup hDynkin) := by
  have hfin : Set.Finite {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} :=
    RepresentationTheory.IntegerVectorPredicate.finite_setOf_integerVectorPredicate hDynkin
  have : Finite {x : Fin n → ℤ | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x} := hfin.to_subtype
  exact Finite.of_injective _ (IntegralRootSystem.weylGroupRootAction_injective hDynkin)


/-- The reflection subgroup associated with a finite integral root system has a fintype structure. -/
noncomputable instance IntegralRootSystem.instFintypeWeylGroup (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Fintype (IntegralRootSystem.weylGroup hDynkin) :=
  @Fintype.ofFinite _ (IntegralRootSystem.finite_weylGroup hDynkin)







/-- An iterated simple-reflection map is induced by an element of the reflection subgroup. -/
theorem IntegralRootSystem.exists_mem_weylGroup_eq_iteratedSimpleReflection (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (l : List (Fin n)) :
    ∃ w ∈ IntegralRootSystem.weylGroup hDynkin,
      ∀ v, w v = RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) l v := by
  induction l with
  | nil => exact ⟨1, one_mem _, fun _ => rfl⟩
  | cons i rest ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    refine ⟨w * IntegralRootSystem.simpleReflectionEquiv hDynkin i,
      mul_mem hw (IntegralRootSystem.simpleReflectionEquiv_mem_weylGroup hDynkin i), fun v => ?_⟩
    change w (IntegralRootSystem.simpleReflectionEquiv hDynkin i v) = _
    rw [hwv]
    rfl


/-- A right-folded composition of simple reflections is induced by an element of the reflection subgroup. -/
theorem IntegralRootSystem.exists_mem_weylGroup_eq_foldr_simpleReflection (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (l : List (Fin n)) :
    ∃ w ∈ IntegralRootSystem.weylGroup hDynkin, ∀ v,
      w v = (l.map (fun i => RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i)).foldr (· ∘ ·) id v := by
  induction l with
  | nil => exact ⟨1, one_mem _, fun _ => rfl⟩
  | cons i rest ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    refine ⟨IntegralRootSystem.simpleReflectionEquiv hDynkin i * w,
      mul_mem (IntegralRootSystem.simpleReflectionEquiv_mem_weylGroup hDynkin i) hw, fun v => ?_⟩
    change IntegralRootSystem.simpleReflectionEquiv hDynkin i (w v) = _
    rw [hwv v]
    rfl


/-- There is an element of the reflection subgroup whose action agrees pointwise with the specified map. -/
theorem IntegralRootSystem.exists_mem_weylGroup_apply_eq (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    ∃ w ∈ IntegralRootSystem.weylGroup hDynkin, ∀ v, w v = RepresentationTheory.IntegerMatrixVectorCoordinateFunction.matrixVectorCoordinateValue n adj v := by
  obtain ⟨w, hw, hwv⟩ := IntegralRootSystem.exists_mem_weylGroup_eq_foldr_simpleReflection hDynkin (List.finRange n)
  refine ⟨w, hw, fun v => ?_⟩
  rw [hwv v, RepresentationTheory.IntegerMatrixVectorCoordinateFunction.matrixVectorCoordinateValue, List.ofFn_eq_map]

end RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup
