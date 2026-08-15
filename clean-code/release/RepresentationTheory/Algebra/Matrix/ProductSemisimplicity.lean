/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import RepresentationTheory.Algebra.Module.IsotypicDecomposition
import RepresentationTheory.Alignment.Attribute


open Matrix.Module Finset

open scoped DirectSum

namespace RepresentationTheory.Algebra.Matrix.ProductSemisimplicity

private theorem matrix_single_smul_vec {k : Type*} [Field k] {d : ℕ}
    (j i : Fin d) (c : k) (v : Fin d → k) :
    (Matrix.single j i c • v) = fun l => if l = j then c * v i else 0 := by
  ext l
  simp only [smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hjl : j = l
  · subst hjl
    simp only [true_and, ite_mul, zero_mul]
    rw [sum_ite_eq univ i]
    simp
  · simp only [show ¬(j = l) from hjl, false_and, ite_false, zero_mul, sum_const_zero,
      show ¬(l = j) from Ne.symm hjl, ite_false]


private theorem isSimpleModule_matrix_vecModule (k : Type*) [Field k]
    (d : ℕ) [NeZero d] :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) where
  eq_bot_or_eq_top s := by
    by_cases hs : s = ⊥
    · exact Or.inl hs
    · right
      obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
      have ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h; push Not at h
        exact hne (funext fun j => by simpa using h j)
      have basis_mem : ∀ j, Pi.single j (1 : k) ∈ s := by
        intro j
        have h1 := s.smul_mem (Matrix.single j i (v i)⁻¹) hv
        rw [matrix_single_smul_vec] at h1
        convert h1 using 1
        ext l
        simp [Pi.single_apply, inv_mul_cancel₀ hi]
      rw [eq_top_iff]
      intro w _
      suffices w = ∑ j ∈ univ, Matrix.single j j (w j) •
          (Pi.single j (1 : k) : Fin d → k) by
        rw [this]
        exact sum_mem fun j _ => s.smul_mem _ (basis_mem j)
      ext l
      simp only [sum_apply, matrix_single_smul_vec, Pi.single_apply, ite_true, mul_one]
      rw [sum_ite_eq univ l]; simp


private theorem matrix_simpleModule_iso_std (k : Type*) [Field k]
    (d : ℕ) [NeZero d] (V : Type*)
    [AddCommGroup V] [Module k V] [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  letI := isSimpleModule_matrix_vecModule k d
  letI : IsSimpleRing (Matrix (Fin d) (Fin d) k) := IsSimpleRing.matrix ..
  letI : IsArtinianRing (Matrix (Fin d) (Fin d) k) := inferInstance
  have ⟨I, ⟨eI⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) V
  have ⟨I', ⟨eI'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) (Fin d → k)
  haveI : IsSimpleModule _ I := IsSimpleModule.congr eI.symm
  haveI : IsSimpleModule _ I' := IsSimpleModule.congr eI'.symm
  have hiso := IsSimpleRing.isIsotypic (Matrix (Fin d) (Fin d) k) (Matrix (Fin d) (Fin d) k)
  have ⟨eII'⟩ := hiso I I'
  exact ⟨eI.trans (eII'.symm.trans eI'.symm)⟩


/-- The type of a finite product of square matrix algebras with prescribed sizes. -/
@[source_ref "Chapter3/Introduction_to_3.3" (role := supporting)]
abbrev MatrixProduct (k : Type*) {r : ℕ} (d : Fin r → ℕ) : Type _ :=
  ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

section Product

variable {k : Type*} [Field k] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]

/-- The standard module structure of a matrix-product algebra on the column space of a selected component. -/
local instance standardModule (j : Fin r) : Module (MatrixProduct k d) (Fin (d j) → k) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j)

omit [∀ i, NeZero (d i)] in
/-- The matrix-product action on a standard column vector is the action of the selected matrix component. -/
theorem standardModule_smul (j : Fin r) (a : MatrixProduct k d) (v : Fin (d j) → k) :
    a • v = a j • v := rfl

/-- The base-field and matrix-product actions on a standard column module form a scalar tower. -/
instance standardModule_isScalarTower (j : Fin r) : IsScalarTower k (MatrixProduct k d) (Fin (d j) → k) where
  smul_assoc c a v := by
    rw [standardModule_smul]
    change (c • a) j • v = c • (a j • v)
    rw [Pi.smul_apply, smul_assoc]

/-- Each standard column module over a product of nonzero-size matrix algebras is simple. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary),
  source_ref "Chapter3/Theorem3.3.1" (role := primary)]
theorem standardModule_isSimpleModule (j : Fin r) :
    IsSimpleModule (MatrixProduct k d) (Fin (d j) → k) := by
  haveI : IsSimpleModule (Matrix (Fin (d j)) (Fin (d j)) k) (Fin (d j) → k) :=
    isSimpleModule_matrix_vecModule k (d j)
  haveI : RingHomSurjective
      (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j) :=
    ⟨Function.surjective_eval j⟩
  let l : (Fin (d j) → k) →ₛₗ[Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j]
      (Fin (d j) → k) :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

omit [∀ i, NeZero (d i)] in
/-- Every module over a finite product of matrix algebras is semisimple. -/
theorem isSemisimpleModule_matrixProduct (X : Type*) [AddCommGroup X]
    [Module (MatrixProduct k d) X] : IsSemisimpleModule (MatrixProduct k d) X :=
  inferInstance

/-- Every finite-dimensional simple module over a product of nonzero-size matrix algebras is equivalent to one of its standard column modules. -/
@[source_ref "Chapter3/Theorem3.3.1" (role := primary)]
theorem simpleModule_linearEquiv_standardModule (W : Type*) [AddCommGroup W] [Module (MatrixProduct k d) W]
    [Module k W] [IsScalarTower k (MatrixProduct k d) W] [FiniteDimensional k W]
    [IsSimpleModule (MatrixProduct k d) W] :
    ∃ j, Nonempty (W ≃ₗ[MatrixProduct k d] (Fin (d j) → k)) := by
  classical
  have e_mul_self : ∀ i : Fin r,
      (Pi.single i 1 : MatrixProduct k d) * Pi.single i 1 = Pi.single i 1 := fun i => by
    rw [← Pi.single_mul, mul_one]
  have e_left : ∀ (i : Fin r) (a : MatrixProduct k d),
      (Pi.single i 1 : MatrixProduct k d) * a = Pi.single i (a i) := fun i a => by
    rw [← Pi.single_mul_left, one_mul]
  have e_right : ∀ (i : Fin r) (a : MatrixProduct k d),
      a * (Pi.single i 1 : MatrixProduct k d) = Pi.single i (a i) := fun i a => by
    rw [← Pi.single_mul_right, mul_one]
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MatrixProduct k d) W
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hsum : ∑ i, (Pi.single i 1 : MatrixProduct k d) • w₀ = w₀ := by
    rw [← Finset.sum_smul, show (∑ i, (Pi.single i 1 : MatrixProduct k d)) = 1 by
      simpa using Finset.univ_sum_single (1 : MatrixProduct k d), one_smul]
  obtain ⟨i, hi⟩ : ∃ i, (Pi.single i 1 : MatrixProduct k d) • w₀ ≠ 0 := by
    by_contra h; push Not at h
    exact hw₀ (by rw [← hsum, Finset.sum_eq_zero (fun i _ => h i)])
  let μ : W →ₗ[MatrixProduct k d] W :=
    { toFun := fun w => (Pi.single i 1 : MatrixProduct k d) • w
      map_add' := fun w w' => smul_add _ _ _
      map_smul' := fun a w => by
        change (Pi.single i 1 : MatrixProduct k d) • (a • w) =
          a • ((Pi.single i 1 : MatrixProduct k d) • w)
        rw [smul_smul, smul_smul, e_left, e_right] }
  have hμμ : ∀ w, μ (μ w) = μ w := fun w => by
    change (Pi.single i 1 : MatrixProduct k d) • ((Pi.single i 1 : MatrixProduct k d) • w)
        = (Pi.single i 1 : MatrixProduct k d) • w
    rw [smul_smul, e_mul_self]
  have hrange : LinearMap.range μ = ⊤ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun h => hi ?_
    have hmem : μ w₀ ∈ LinearMap.range μ := LinearMap.mem_range_self _ _
    rw [h, Submodule.mem_bot] at hmem
    exact hmem
  have hid : ∀ w : W, (Pi.single i 1 : MatrixProduct k d) • w = w := fun w => by
    obtain ⟨w', hw'⟩ := (by rw [hrange]; exact Submodule.mem_top : w ∈ LinearMap.range μ)
    have h := hμμ w'
    rw [hw'] at h
    exact h
  have key : ∀ (a : MatrixProduct k d) (w : W),
      a • w = (Pi.single i (a i) : MatrixProduct k d) • w := fun a w => by
    conv_lhs => rw [← hid w, smul_smul, e_right]
  letI : Module (Matrix (Fin (d i)) (Fin (d i)) k) W :=
    { smul := fun b w => (Pi.single i b : MatrixProduct k d) • w
      one_smul := fun w => hid w
      mul_smul := fun b b' w => by
        change (Pi.single i (b * b') : MatrixProduct k d) • w
            = (Pi.single i b : MatrixProduct k d) • ((Pi.single i b' : MatrixProduct k d) • w)
        rw [Pi.single_mul, smul_smul]
      smul_zero := fun b => smul_zero _
      smul_add := fun b w w' => smul_add _ _ _
      add_smul := fun b b' w => by
        change (Pi.single i (b + b') : MatrixProduct k d) • w
            = (Pi.single i b : MatrixProduct k d) • w + (Pi.single i b' : MatrixProduct k d) • w
        rw [Pi.single_add, add_smul]
      zero_smul := fun w => by
        change (Pi.single i (0 : Matrix (Fin (d i)) (Fin (d i)) k) : MatrixProduct k d) • w = 0
        rw [Pi.single_zero, zero_smul] }
  haveI : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) k) W :=
    { smul_assoc := fun c b w => by
        change (Pi.single i (c • b) : MatrixProduct k d) • w =
          c • ((Pi.single i b : MatrixProduct k d) • w)
        rw [Pi.single_smul, smul_assoc] }
  haveI : IsSimpleModule (Matrix (Fin (d i)) (Fin (d i)) k) W := by
    haveI : RingHomSurjective
        (Pi.evalRingHom (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i) :=
      ⟨Function.surjective_eval i⟩
    let l : W →ₛₗ[Pi.evalRingHom (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i] W :=
      { AddMonoidHom.id W with map_smul' := fun a w => key a w }
    exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mp inferInstance
  obtain ⟨eW⟩ := matrix_simpleModule_iso_std k (d i) W
  exact ⟨i, ⟨{ eW.toAddEquiv with
    map_smul' := fun a w => by
      change eW (a • w) = a • eW w
      rw [key a w, standardModule_smul]
      exact eW.map_smul (a i) w }⟩⟩

/-- The standard column modules over a finite product of nonzero-size matrix algebras are simple, exhaust the finite-dimensional simple modules, and every module over the product is semisimple. -/
@[source_ref "Chapter3/Introduction_to_3.3" (role := supporting),
  source_ref "Chapter3/Problem3.3.3/Derived17" (role := supporting),
  source_ref "Chapter3/Theorem3.6.2/Derived12" (role := supporting)]
theorem matrixProduct_simpleModule_classification :
    (∀ j, IsSimpleModule (MatrixProduct k d) (Fin (d j) → k)) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module (MatrixProduct k d) W] [Module k W]
        [IsScalarTower k (MatrixProduct k d) W] [FiniteDimensional k W] [IsSimpleModule (MatrixProduct k d) W],
        ∃ j, Nonempty (W ≃ₗ[MatrixProduct k d] (Fin (d j) → k))) ∧
    (∀ (X : Type*) [AddCommGroup X] [Module (MatrixProduct k d) X], IsSemisimpleModule (MatrixProduct k d) X) :=
  ⟨standardModule_isSimpleModule, fun W => simpleModule_linearEquiv_standardModule W,
    isSemisimpleModule_matrixProduct⟩

/-- Equivalent standard column modules of nonzero-size components have equal component indices. -/
@[source_ref "Chapter3/Theorem3.3.1" (role := primary)]
theorem standardModule_equiv_imp_eq {i j : Fin r}
    (h : Nonempty ((Fin (d i) → k) ≃ₗ[MatrixProduct k d] (Fin (d j) → k))) : i = j := by
  obtain ⟨φ⟩ := h
  by_contra hij
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin (d i) → k)
  have hVi : (Pi.single i 1 : MatrixProduct k d) • v = v := by
    rw [standardModule_smul, Pi.single_eq_same, one_smul]
  have hVj : (Pi.single i 1 : MatrixProduct k d) • φ v = 0 := by
    rw [standardModule_smul, Pi.single_eq_of_ne (Ne.symm hij), zero_smul]
  have hz : φ v = 0 := by
    have h1 := map_smul φ (Pi.single i 1 : MatrixProduct k d) v
    rw [hVi, hVj] at h1
    exact h1
  exact hv (φ.injective (by rw [hz, map_zero]))


/-- The module-linear map extracting an indexed column vector from a selected matrix component. -/
def columnLinearMap (i : Fin r) (c : Fin (d i)) :
    MatrixProduct k d →ₗ[MatrixProduct k d] (Fin (d i) → k) where
  toFun M := fun j => M i j c
  map_add' M N := by funext j; simp
  map_smul' N M := by
    funext j
    rw [RingHom.id_apply, standardModule_smul, Matrix.Module.smul_apply, smul_eq_mul, Pi.mul_apply,
      Matrix.mul_apply]
    simp [smul_eq_mul]

/-- The module-linear map from a product of matrix algebras to one matrix component. -/
def componentLinearMap (i : Fin r) : MatrixProduct k d →ₗ[MatrixProduct k d] (Fin (d i) → (Fin (d i) → k)) :=
  LinearMap.pi fun c => columnLinearMap i c

/-- A module-linear equivalence from a product of matrix algebras to the direct sum of the column spaces of its components. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary),
  source_ref "Chapter3/Remark3.3.4/Derived6" (role := primary)]
noncomputable def matrixProductLinearEquivDirectSumColumns :
    MatrixProduct k d ≃ₗ[MatrixProduct k d] (⨁ i, (Fin (d i) → (Fin (d i) → k))) :=
  (LinearEquiv.ofBijective (LinearMap.pi componentLinearMap)
      (Function.bijective_iff_has_inverse.mpr
        ⟨fun w i j c => w i c j, fun _ => rfl, fun _ => rfl⟩)).trans
    (DirectSum.linearEquivFunOnFintype (MatrixProduct k d) (Fin r)
      (fun i => Fin (d i) → (Fin (d i) → k))).symm

omit [∀ i, NeZero (d i)] in
/-- The direct-sum column equivalence sends a matrix-product element to its component matrices with the row and column indices transposed in the column view. -/
@[simp] theorem matrixProductLinearEquivDirectSumColumns_apply (M : MatrixProduct k d) (i : Fin r) (c j : Fin (d i)) :
    matrixProductLinearEquivDirectSumColumns M i c j = M i j c := rfl


/-- The module-linear map that flattens the columns in a finite family of matrix-product elements into a family of standard column vectors. -/
def flattenedColumnMap (n : ℕ) (i : Fin r) :
    (Fin n → MatrixProduct k d) →ₗ[MatrixProduct k d] (Fin (n * d i) → (Fin (d i) → k)) :=
  LinearMap.pi fun m =>
    (columnLinearMap i (finProdFinEquiv.symm m).2).comp (LinearMap.proj (finProdFinEquiv.symm m).1)

omit [∀ i, NeZero (d i)] in
/-- The flattened column map evaluates by unpairing its combined family-and-column index and reading the corresponding matrix entry. -/
@[simp] theorem flattenedColumnMap_apply (n : ℕ) (i : Fin r) (M : Fin n → MatrixProduct k d)
    (m : Fin (n * d i)) (j : Fin (d i)) :
    flattenedColumnMap n i M m j =
      M (finProdFinEquiv.symm m).1 i j (finProdFinEquiv.symm m).2 := rfl

/-- A module-linear equivalence from a finite family of matrix-product elements to the direct sum of their flattened standard-column families. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary),
  source_ref "Chapter3/Remark3.3.4/Derived7" (role := primary)]
noncomputable def piMatrixProductLinearEquivDirectSum (n : ℕ) :
    (Fin n → MatrixProduct k d) ≃ₗ[MatrixProduct k d] (⨁ i, (Fin (n * d i) → (Fin (d i) → k))) :=
  (LinearEquiv.ofBijective (LinearMap.pi fun i => flattenedColumnMap n i)
      (Function.bijective_iff_has_inverse.mpr
        ⟨fun w l i => Matrix.of fun j c => w i (finProdFinEquiv (l, c)) j,
          fun M => by
            funext l i j c
            simp only [LinearMap.pi_apply, flattenedColumnMap_apply, Matrix.of_apply,
              Equiv.symm_apply_apply],
          fun w => by
            funext i m j
            simp only [LinearMap.pi_apply, flattenedColumnMap_apply, Matrix.of_apply, Prod.mk.eta,
              Equiv.apply_symm_apply]⟩)).trans
    (DirectSum.linearEquivFunOnFintype (MatrixProduct k d) (Fin r)
       (fun i => Fin (n * d i) → (Fin (d i) → k))).symm

end Product


section Duality

variable {k : Type*} [Field k]

/-- An algebra equivalence from a square matrix algebra to its opposite algebra. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
abbrev matrixAlgEquivOpposite (k : Type*) [Field k] (D : ℕ) :
    Matrix (Fin D) (Fin D) k ≃ₐ[k] (Matrix (Fin D) (Fin D) k)ᵐᵒᵖ :=
  Matrix.transposeAlgEquiv (Fin D) k k

/-- The ring equivalence between a family of opposite semirings and the opposite of the corresponding product semiring. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
def piOppositeRingEquiv {ι : Type*} (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, (R i)ᵐᵒᵖ) ≃+* (∀ i, R i)ᵐᵒᵖ where
  toFun f := MulOpposite.op fun i => (f i).unop
  invFun g := fun i => MulOpposite.op ((MulOpposite.unop g) i)
  left_inv f := by funext i; simp
  right_inv g := by simp
  map_mul' f g := MulOpposite.unop_injective <| funext fun i => by simp [MulOpposite.unop_mul]
  map_add' f g := MulOpposite.unop_injective <| funext fun i => by simp

/-- The ring equivalence from a product of matrix algebras to its opposite ring given componentwise by transpose. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary)]
def transposeRingEquivOpposite {r : ℕ} (d : Fin r → ℕ) :
    MatrixProduct k d ≃+* (MatrixProduct k d)ᵐᵒᵖ :=
  (RingEquiv.piCongrRight fun i => Matrix.transposeRingEquiv (Fin (d i)) k).trans
    (piOppositeRingEquiv _)

/-- The dual map of a surjective linear map between vector spaces is injective. -/
theorem dualMap_injective_of_surjective {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {φ : M →ₗ[k] N} (hφ : Function.Surjective φ) :
    Function.Injective φ.dualMap :=
  LinearMap.dualMap_injective_of_surjective hφ

end Duality


section TwistedDual

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- The base-field-linear endomorphism of a scalar-tower module given by the action of an algebra element. -/
def algebraSmulLinearMap (b : A) (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] : X →ₗ[k] X where
  toFun x := b • x
  map_add' := smul_add b
  map_smul' c x := (smul_comm c b x).symm

/-- The linear endomorphism associated to an algebra element evaluates as scalar multiplication by that element. -/
@[simp] theorem algebraSmulLinearMap_apply (b : A) (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] (x : X) : algebraSmulLinearMap (k := k) b X x = b • x := rfl

variable (e : A ≃+* Aᵐᵒᵖ)

/-- A module structure on a base-field dual induced by a ring equivalence from the acting algebra to its opposite. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary), reducible]
def moduleDualOfRingEquivOpposite (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] : Module A (Module.Dual k X) where
  smul a f := f ∘ₗ algebraSmulLinearMap (e a).unop X
  one_smul f := by
    ext x
    change f ((e 1).unop • x) = f x
    rw [map_one, MulOpposite.unop_one, one_smul]
  mul_smul a b f := by
    ext x
    change f ((e (a * b)).unop • x) = f ((e b).unop • (e a).unop • x)
    rw [map_mul, MulOpposite.unop_mul, mul_smul]
  smul_zero a := by ext x; rfl
  smul_add a f g := by ext x; rfl
  add_smul a b f := by
    ext x
    change f ((e (a + b)).unop • x) = f ((e a).unop • x) + f ((e b).unop • x)
    rw [map_add, MulOpposite.unop_add, add_smul, map_add]
  zero_smul f := by
    ext x
    change f ((e 0).unop • x) = 0
    rw [map_zero, MulOpposite.unop_zero, zero_smul, map_zero]

/-- The induced action on a dual functional evaluates by applying the functional after the opposite-ring image acts on its argument. -/
@[simp] theorem moduleDualOfRingEquivOpposite_smul_apply (X : Type*) [AddCommGroup X] [Module k X]
    [Module A X] [IsScalarTower k A X] (a : A) (f : Module.Dual k X) (x : X) :
    letI : Module A (Module.Dual k X) := moduleDualOfRingEquivOpposite e X
    (a • f) x = f ((e a).unop • x) := rfl

/-- A scalar-compatible equivalence to the opposite ring makes the base-field and induced dual actions into a scalar tower. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
theorem moduleDualOfRingEquivOpposite_isScalarTower (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X]
    (he : ∀ (c : k) (a : A), (e (c • a)).unop = c • (e a).unop) :
    letI : Module A (Module.Dual k X) := moduleDualOfRingEquivOpposite e X
    IsScalarTower k A (Module.Dual k X) := by
  letI : Module A (Module.Dual k X) := moduleDualOfRingEquivOpposite e X
  refine ⟨fun c a f => ?_⟩
  ext x
  change f ((e (c • a)).unop • x) = c • f ((e a).unop • x)
  rw [he, smul_assoc, map_smul]

end TwistedDual


section DualRoute

open _root_.Matrix

variable {k : Type*} [Field k] {r : ℕ} {d : Fin r → ℕ}

/-- After removing the opposite-ring wrapper, the transpose equivalence acts componentwise by matrix transpose. -/
theorem transposeRingEquivOpposite_apply (a : MatrixProduct k d) :
    (transposeRingEquivOpposite d a).unop = fun i => (a i)ᵀ := rfl

/-- The componentwise transpose equivalence commutes with scalar multiplication after removing the opposite-ring wrapper. -/
theorem transposeRingEquivOpposite_smul (c : k) (a : MatrixProduct k d) :
    (transposeRingEquivOpposite d (c • a)).unop = c • (transposeRingEquivOpposite d a).unop := by
  rw [transposeRingEquivOpposite_apply, transposeRingEquivOpposite_apply]
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Matrix.transpose_smul]

variable {X : Type*} [AddCommGroup X] [Module k X] [Module (MatrixProduct k d) X]
  [IsScalarTower k (MatrixProduct k d) X]

/-- The matrix-product module structure on the base-field dual of a module. -/
local instance moduleDualModule : Module (MatrixProduct k d) (Module.Dual k X) :=
  moduleDualOfRingEquivOpposite (transposeRingEquivOpposite d) X

/-- The base-field action and matrix-product action on the dual module form a scalar tower. -/
local instance moduleDual_isScalarTower : IsScalarTower k (MatrixProduct k d) (Module.Dual k X) := by
  refine ⟨fun c a f => ?_⟩
  refine LinearMap.ext fun x => ?_
  change f ((transposeRingEquivOpposite d (c • a)).unop • x)
       = c • f ((transposeRingEquivOpposite d a).unop • x)
  rw [transposeRingEquivOpposite_smul, smul_assoc, map_smul]

/-- The linear functional on a matrix product obtained from an element by the componentwise transpose-trace pairing. -/
def traceDual (a : MatrixProduct k d) : Module.Dual k (MatrixProduct k d) where
  toFun x := ∑ i, Matrix.trace ((a i)ᵀ * x i)
  map_add' x y := by
    simp only [Pi.add_apply, Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm, Matrix.trace_smul,
      Finset.smul_sum]

/-- The trace-dual functional evaluates as the sum of the componentwise traces of a transposed matrix times the argument matrix. -/
@[simp] theorem traceDual_apply (a x : MatrixProduct k d) :
    traceDual a x = ∑ i, Matrix.trace ((a i)ᵀ * x i) := rfl

/-- The module-linear map from a matrix product to its linear dual defined by the componentwise transpose-trace pairing. -/
def traceDualLinearMap : MatrixProduct k d →ₗ[MatrixProduct k d] Module.Dual k (MatrixProduct k d) where
  toFun := traceDual
  map_add' a b := by
    refine LinearMap.ext fun x => ?_
    simp only [traceDual_apply, Pi.add_apply, Matrix.transpose_add, Matrix.add_mul,
      Matrix.trace_add, Finset.sum_add_distrib, LinearMap.add_apply]
  map_smul' a' a := by
    refine LinearMap.ext fun x => ?_
    change (∑ i, Matrix.trace (((a' * a) i)ᵀ * x i))
         = ∑ i, Matrix.trace ((a i)ᵀ * ((transposeRingEquivOpposite d a').unop • x) i)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_eq_mul, Pi.mul_apply, transposeRingEquivOpposite_apply]
    rw [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The trace-dual linear map evaluates as the sum of traces of the products of the transposed first components with the second components. -/
@[simp] theorem traceDualLinearMap_apply (a x : MatrixProduct k d) :
    traceDualLinearMap a x = ∑ i, Matrix.trace ((a i)ᵀ * x i) := rfl

/-- The transpose-trace map from a matrix product to its dual is injective. -/
theorem traceDualLinearMap_injective : Function.Injective (traceDualLinearMap (k := k) (d := d)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  ext p q
  have h0 : traceDualLinearMap a (Pi.single i (Matrix.single p q 1)) = 0 := by rw [ha]; rfl
  rw [traceDualLinearMap_apply, Finset.sum_eq_single i] at h0
  · rw [Pi.single_eq_same, Matrix.trace_mul_single] at h0
    simpa [Matrix.transpose_apply] using h0
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, Matrix.mul_zero, Matrix.trace_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The transpose-trace map from a matrix product to its dual is bijective. -/
theorem traceDualLinearMap_bijective : Function.Bijective (traceDualLinearMap (k := k) (d := d)) := by
  refine ⟨traceDualLinearMap_injective, ?_⟩
  have hdim : Module.finrank k (MatrixProduct k d)
      = Module.finrank k (Module.Dual k (MatrixProduct k d)) := Subspace.dual_finrank_eq.symm
  have hinj : Function.Injective ((traceDualLinearMap (k := k) (d := d)).restrictScalars k) := by
    simpa [LinearMap.coe_restrictScalars] using traceDualLinearMap_injective
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  simpa [LinearMap.coe_restrictScalars] using hsurj

/-- A module-linear equivalence between a matrix product and its base-field dual. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
noncomputable def matrixProductLinearEquivDual :
    MatrixProduct k d ≃ₗ[MatrixProduct k d] Module.Dual k (MatrixProduct k d) :=
  LinearEquiv.ofBijective traceDualLinearMap traceDualLinearMap_bijective

/-- The module-linear map sending a family of matrix-product coefficients to the corresponding linear combination of a basis of the dual module. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary)]
noncomputable def basisLinearCombination {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X)) :
    (Fin n → MatrixProduct k d) →ₗ[MatrixProduct k d] Module.Dual k X where
  toFun a := ∑ l, a l • yb l
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' b a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- The basis linear-combination map evaluates as the finite sum of each coefficient acting on its corresponding basis vector. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary), simp]
theorem basisLinearCombination_apply {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X))
    (a : Fin n → MatrixProduct k d) : basisLinearCombination yb a = ∑ l, a l • yb l := rfl

/-- The module-linear map forming combinations of a basis of the dual module is surjective. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary)]
theorem basisLinearCombination_surjective {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X)) :
    Function.Surjective (basisLinearCombination (d := d) yb) := by
  intro f
  refine ⟨fun l => algebraMap k (MatrixProduct k d) (yb.repr f l), ?_⟩
  change ∑ l, algebraMap k (MatrixProduct k d) (yb.repr f l) • yb l = f
  simp only [algebraMap_smul]
  exact yb.sum_repr f

/-- Applying the componentwise transpose-to-opposite equivalence twice and removing both wrappers returns the original element. -/
theorem transposeRingEquivOpposite_apply_apply (a : MatrixProduct k d) :
    (transposeRingEquivOpposite d (transposeRingEquivOpposite d a).unop).unop = a := by
  funext i
  simp only [transposeRingEquivOpposite_apply, Matrix.transpose_transpose]

section DualMap

variable {M N : Type*}
  [AddCommGroup M] [Module k M] [Module (MatrixProduct k d) M] [IsScalarTower k (MatrixProduct k d) M]
  [AddCommGroup N] [Module k N] [Module (MatrixProduct k d) N] [IsScalarTower k (MatrixProduct k d) N]

/-- The module-linear dual map associated with a module-linear map between matrix-product modules. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
noncomputable def moduleDualMap (f : M →ₗ[MatrixProduct k d] N) :
    Module.Dual k N →ₗ[MatrixProduct k d] Module.Dual k M where
  toFun g := (f.restrictScalars k).dualMap g
  map_add' g h := by simp only [map_add]
  map_smul' a g := by
    refine LinearMap.ext fun m => ?_
    change g ((transposeRingEquivOpposite d a).unop • f m)
         = g (f ((transposeRingEquivOpposite d a).unop • m))
    rw [map_smul f]

/-- The module-linear dual map of a surjective module homomorphism is injective. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
theorem moduleDualMap_injective_of_surjective {f : M →ₗ[MatrixProduct k d] N} (hf : Function.Surjective f) :
    Function.Injective (moduleDualMap f) := by
  have hf' : Function.Surjective (f.restrictScalars k) := by
    simpa [LinearMap.coe_restrictScalars] using hf
  exact dualMap_injective_of_surjective hf'

end DualMap

/-- The module-linear equivalence from a finite-dimensional matrix-product module to its base-field double dual. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
noncomputable def toDoubleDualLinearEquiv (X : Type*)
    [AddCommGroup X] [Module k X] [Module (MatrixProduct k d) X] [IsScalarTower k (MatrixProduct k d) X]
    [FiniteDimensional k X] :
    X ≃ₗ[MatrixProduct k d] Module.Dual k (Module.Dual k X) :=
  { (Module.evalEquiv k X).toAddEquiv with
    map_smul' := fun a x => by
      refine LinearMap.ext fun g => ?_
      change g (a • x)
           = g ((transposeRingEquivOpposite d (transposeRingEquivOpposite d a).unop).unop • x)
      rw [transposeRingEquivOpposite_apply_apply] }

variable (X) [FiniteDimensional k X]

/-- A module-linear map embedding a finite-dimensional module into the dual of a finite free module over the matrix-product algebra. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
noncomputable def dualFreeEmbedding :
    X →ₗ[MatrixProduct k d]
      Module.Dual k (Fin (Module.finrank k (Module.Dual k X)) → MatrixProduct k d) :=
  (moduleDualMap (basisLinearCombination (Module.finBasis k (Module.Dual k X)))).comp
    (toDoubleDualLinearEquiv X).toLinearMap

/-- The map from a finite-dimensional module into the dual of the associated finite free module is injective. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
theorem dualFreeEmbedding_injective : Function.Injective (dualFreeEmbedding (k := k) (d := d) X) := by
  rw [dualFreeEmbedding, LinearMap.coe_comp]
  exact (moduleDualMap_injective_of_surjective (basisLinearCombination_surjective _)).comp (toDoubleDualLinearEquiv X).injective


/-- The module-linear equivalence between the dual of a finite family of matrix-product elements and the corresponding family of duals. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := supporting)]
noncomputable def dualPiLinearEquivPiDual (n : ℕ) :
    Module.Dual k (Fin n → MatrixProduct k d) ≃ₗ[MatrixProduct k d]
      (Fin n → Module.Dual k (MatrixProduct k d)) where
  toFun f l := f ∘ₗ LinearMap.single k (fun _ : Fin n => MatrixProduct k d) l
  map_add' f g := by funext l; ext b; simp
  map_smul' a f := by
    funext l
    refine LinearMap.ext fun b => ?_
    change f ((transposeRingEquivOpposite d a).unop
              • LinearMap.single k (fun _ : Fin n => MatrixProduct k d) l b)
       = f (LinearMap.single k (fun _ : Fin n => MatrixProduct k d) l
              ((transposeRingEquivOpposite d a).unop • b))
    congr 1
    funext l'
    simp only [LinearMap.single_apply, Pi.single_apply, Pi.smul_apply]
    by_cases h : l' = l <;> simp [h]
  invFun g := ∑ l, (g l) ∘ₗ LinearMap.proj l
  left_inv f := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply]
    rw [← map_sum]
    congr 1
    exact Finset.univ_sum_single x
  right_inv g := by
    funext l
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.comp_apply, LinearMap.single_apply, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'; simp [Ne.symm hl']
    · intro h; exact absurd (Finset.mem_univ l) h

/-- The module-linear equivalence from the dual of a finite family of matrix-product elements to a finite family of matrix-product elements. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary)]
noncomputable def dualPiLinearEquiv (n : ℕ) :
    Module.Dual k (Fin n → MatrixProduct k d) ≃ₗ[MatrixProduct k d] (Fin n → MatrixProduct k d) :=
  (dualPiLinearEquivPiDual n).trans
    (LinearEquiv.piCongrRight fun _ : Fin n => (matrixProductLinearEquivDual (k := k) (d := d)).symm)

variable [∀ i, NeZero (d i)]

/-- The standard column-module structure used in direct-sum decompositions over a matrix-product algebra. -/
local instance decompositionStandardModule (j : Fin r) : Module (MatrixProduct k d) (Fin (d j) → k) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j)

/-- Every finite-dimensional module over a product of nonzero-size matrix algebras is equivalent to a direct sum of finite multiplicities of the standard column modules. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.3.1" (role := primary),
  source_ref "Chapter3/Problem3.3.3/Derived17" (role := supporting),
  source_ref "Chapter3/Remark3.3.4/Derived8" (role := primary),
  source_ref "Chapter3/Theorem3.3.1" (role := primary)]
theorem exists_linearEquiv_directSum_standardModules :
    ∃ m : Fin r → ℕ,
      Nonempty (X ≃ₗ[MatrixProduct k d] ⨁ i, (Fin (m i) → (Fin (d i) → k))) := by
  haveI : ∀ i, IsSimpleModule (MatrixProduct k d) (Fin (d i) → k) := standardModule_isSimpleModule
  let e := (dualPiLinearEquiv (k := k) (d := d) (Module.finrank k (Module.Dual k X))).trans
    (piMatrixProductLinearEquivDirectSum (Module.finrank k (Module.Dual k X)))
  let F := e.toLinearMap.comp (dualFreeEmbedding X)
  have hF : Function.Injective F := e.injective.comp (dualFreeEmbedding_injective X)
  obtain ⟨m, -, ⟨φ⟩⟩ := _root_.RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_equiv_directSum_fin
    (V := fun i => Fin (d i) → k)
    (fun i => Module.finrank k (Module.Dual k X) * d i)
    (fun ⦃i j⦄ h => standardModule_equiv_imp_eq h) (LinearMap.range F)
  exact ⟨m, ⟨(LinearEquiv.ofInjective F hF).trans φ⟩⟩

end DualRoute

end RepresentationTheory.Algebra.Matrix.ProductSemisimplicity
