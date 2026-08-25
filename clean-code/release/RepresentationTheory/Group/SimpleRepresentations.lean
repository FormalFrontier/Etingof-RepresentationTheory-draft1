/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

open FDRep CategoryTheory

universe u v

section CenterDimension

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [NeZero (Nat.card G : k)]

omit [IsAlgClosed k] [Fintype G] [DecidableEq G] [NeZero (Nat.card G : k)] in
private lemma center_coeff_conj_invariant
    {a : MonoidAlgebra k G} (ha : a ∈ Subalgebra.center k (MonoidAlgebra k G))
    (g h : G) : a.coeff (g * h * g⁻¹) = a.coeff h := by
  rw [Subalgebra.mem_center_iff] at ha
  have key := congrArg (fun z : MonoidAlgebra k G ↦ z.coeff (g * h))
    (ha (MonoidAlgebra.single g 1))
  simpa using key.symm

omit [IsAlgClosed k] [Fintype G] [DecidableEq G] [NeZero (Nat.card G : k)] in
private lemma mem_center_of_conj_invariant (a : MonoidAlgebra k G)
    (ha : ∀ g h : G, a.coeff (g * h * g⁻¹) = a.coeff h) :
    a ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    ext x
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
      MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one]
    have h1 := ha g⁻¹ (x * g⁻¹)
    simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h1
    exact h1
  | hadd b₁ b₂ hb₁ hb₂ =>
    rw [mul_add, add_mul, hb₁, hb₂]
  | hsmul r b hb =>
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hb]

omit [IsAlgClosed k] [NeZero (Nat.card G : k)] in
private lemma finrank_center_monoidAlgebra :
    Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Fintype.card (ConjClasses G) := by
  let fwd : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k] (ConjClasses G → k) :=
    { toFun := fun a C => (a : MonoidAlgebra k G).coeff (Quotient.out C)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let bwd : (ConjClasses G → k) →ₗ[k] ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
    { toFun := fun f => ⟨MonoidAlgebra.ofCoeff (Finsupp.onFinset Finset.univ
          (fun g => f (ConjClasses.mk g)) (fun _ _ => Finset.mem_univ _)),
        mem_center_of_conj_invariant _ (fun g h => by
          simp only [Finsupp.onFinset_apply]
          congr 1
          rw [ConjClasses.mk_eq_mk_iff_isConj]
          exact isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩
      map_add' := fun f₁ f₂ => by ext g; simp [Finsupp.onFinset_apply]
      map_smul' := fun r f => by ext g; simp [Finsupp.onFinset_apply] }
  have hfb : ∀ f, fwd (bwd f) = f := fun f => funext fun C => by
    simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
    congr 1; exact Quotient.out_eq C
  have hbf : ∀ a : ↥(Subalgebra.center k (MonoidAlgebra k G)), bwd (fwd a) = a :=
    fun ⟨a, ha⟩ => by
    ext g
    simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
    have hconj : IsConj (Quotient.out (ConjClasses.mk g) : G) g := by
      have h := Quotient.out_eq (ConjClasses.mk g)
      rw [ConjClasses.quotient_mk_eq_mk] at h
      exact ConjClasses.mk_eq_mk_iff_isConj.mp h
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [show a.coeff (Quotient.out (ConjClasses.mk g)) =
        a.coeff (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
      (center_coeff_conj_invariant ha c _).symm, hc]
  have e : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k] (ConjClasses G → k) :=
    { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
  have : Module.finrank k (ConjClasses G → k) = Fintype.card (ConjClasses G) :=
    Module.finrank_fintype_fun_eq_card k
  linarith [e.finrank_eq]

omit [DecidableEq G] in
private lemma finrank_center_pi_matrix
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) :
    Module.finrank k ↥(Subalgebra.center k
      (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)) = D.count := by
  let PiMat := (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)
  let fwd : ↥(Subalgebra.center k PiMat) →ₗ[k] (Fin D.count → k) :=
    { toFun := fun a i =>
        haveI := D.dimension_neZero i
        (a : PiMat) i ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
          ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  let bwd_fun : (Fin D.count → k) → PiMat :=
    fun c i => c i • (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)
  have bwd_mem : ∀ c, bwd_fun c ∈ Subalgebra.center k PiMat := fun c => by
    rw [Subalgebra.mem_center_iff]; intro N; ext i : 1
    change N i * (c i • 1) = (c i • 1) * N i
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  let bwd : (Fin D.count → k) →ₗ[k] ↥(Subalgebra.center k PiMat) :=
    { toFun := fun c => ⟨bwd_fun c, bwd_mem c⟩
      map_add' := fun c₁ c₂ => by
        apply Subtype.ext; funext i
        change (c₁ i + c₂ i) • (1 : Matrix _ _ k) = _
        rw [add_smul]; rfl
      map_smul' := fun r c => by
        apply Subtype.ext; funext i
        change (r * c i) • (1 : Matrix _ _ k) = _
        rw [mul_smul]; rfl }
  have hfb : ∀ c, fwd (bwd c) = c := fun c => funext fun i => by
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    simp [Matrix.smul_apply]
  have hbf : ∀ x : ↥(Subalgebra.center k PiMat), bwd (fwd x) = x := fun ⟨f, hf⟩ => by
    apply Subtype.ext; ext i a b
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    have hfc : f i ∈ Subalgebra.center k (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) := by
      rw [Subalgebra.mem_center_iff]; intro M
      have hf' : ∀ b : PiMat, b * f = f * b := Subalgebra.mem_center_iff.mp hf
      have h := hf' (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M)
      have lhs : (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M * f) i =
          M * f i := by rw [Pi.mul_apply, Pi.single_eq_same]
      have rhs : (f * Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M) i =
          f i * M := by rw [Pi.mul_apply, Pi.single_eq_same]
      rw [show M * f i = (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M * f) i
        from lhs.symm, h, rhs]
    rw [Algebra.IsCentral.center_eq_bot] at hfc
    rw [Algebra.mem_bot] at hfc
    obtain ⟨c, hc⟩ := Set.mem_range.mp hfc
    have hfi : f i = c • (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) := by
      rw [← hc, Algebra.algebraMap_eq_smul_one]
    rw [hfi]; simp [Matrix.smul_apply, Matrix.one_apply]
  have e : ↥(Subalgebra.center k PiMat) ≃ₗ[k] (Fin D.count → k) :=
    { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
  have : Module.finrank k (Fin D.count → k) = D.count := by
    rw [Module.finrank_fintype_fun_eq_card k, Fintype.card_fin]
  linarith [e.finrank_eq]

private noncomputable def AlgEquiv.centerLinearEquiv
    {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    ↥(Subalgebra.center R A) ≃ₗ[R] ↥(Subalgebra.center R B) where
  toFun := fun ⟨a, ha⟩ => ⟨e a, by
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro b; obtain ⟨a', rfl⟩ := e.surjective b
    simp [← map_mul, ha a']⟩
  invFun := fun ⟨b, hb⟩ => ⟨e.symm b, by
    rw [Subalgebra.mem_center_iff] at hb ⊢
    intro a; apply e.injective
    simp [map_mul, hb (e a)]⟩
  left_inv := by intro ⟨a, _⟩; ext; simp
  right_inv := by intro ⟨b, _⟩; ext; simp
  map_add' := by intro ⟨a, _⟩ ⟨b, _⟩; ext; simp [map_add]
  map_smul' := by intro r ⟨a, _⟩; ext; simp [Algebra.smul_def, map_mul]

/-- The displayed natural-number invariant of the given data equals the number of conjugacy classes. -/
theorem RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.invariant_eq_card_conjClasses
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) :
    D.count = Fintype.card (ConjClasses G) := by
  have h1 := (AlgEquiv.centerLinearEquiv D.groupAlgebraEquivMatrix).finrank_eq
  have h2 := finrank_center_pi_matrix D
  have h3 := finrank_center_monoidAlgebra (k := k) (G := G)
  linarith

end CenterDimension

/-- There is a complete finite family of pairwise nonisomorphic simple finite-dimensional representations whose cardinality equals the number of conjugacy classes. -/
@[source_ref "Chapter4/Corollary4.2.2" (role := primary)]
theorem RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses
    {G : Type v} [Group G] [Fintype G] [DecidableEq G]
    {k : Type u} [Field k] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      n = Fintype.card (ConjClasses G) := by
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero
  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default (k := k) (G := G)
  obtain ⟨V, hsimp, hinj, hsurj⟩ := D.exists_completeSimpleFamily
  exact ⟨D.count, V, hsimp, hinj, hsurj, D.invariant_eq_card_conjClasses⟩
