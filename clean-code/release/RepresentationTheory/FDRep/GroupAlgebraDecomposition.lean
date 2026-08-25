/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.FDRep.GroupAlgebraDecomposition



open CategoryTheory

universe u v

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]



omit [Fintype G] in
/-- The monoid-algebra space indexed by a finite type is finite-dimensional over the field. -/
noncomputable instance finiteDimensional_monoidAlgebra [Finite G] :
    FiniteDimensional k (MonoidAlgebra k G) :=
  inferInstance

omit [Fintype G] in
/-- The group algebra of a finite group is semisimple when its cardinality is nonzero in the field. -/
instance isSemisimpleRing_monoidAlgebra [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance



omit [Fintype G] in

/-- A finite group algebra over an algebraically closed field is equivalent to a finite family of nonzero square matrix algebras. -/
theorem exists_groupAlgebraEquiv_pi_matrix [Finite G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    (F := k) (R := MonoidAlgebra k G)




/-- Auxiliary decomposition data for representations of a finite group over an algebraically closed field. -/
structure DecompositionData (k : Type u) (G : Type v) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] where
  
  /-- The number of indices associated with the decomposition data. -/
  count : ℕ
  
  /-- The natural number assigned to an index of the decomposition data. -/
  dimension : Fin count → ℕ
  
  /-- Every indexed dimension in the decomposition data is nonzero. -/
  dimension_neZero : ∀ i, NeZero (dimension i)
  
  /-- The group algebra is equivalent to a family of square matrix algebras with the stored dimensions. -/
  groupAlgebraEquivMatrix : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (dimension i)) (Fin (dimension i)) k


/-- An auxiliary decomposition datum available under the finite-group field assumptions. -/
noncomputable def DecompositionData.default [NeZero (Nat.card G : k)] :
    DecompositionData k G := by
  choose n d hd he using exists_groupAlgebraEquiv_pi_matrix (k := k) (G := G)
  exact ⟨n, d, hd, he.some⟩



omit [IsAlgClosed k] [Group G] in

/-- The dimension of the monoid-algebra space over its field equals the cardinality of its finite indexing type. -/
theorem finrank_monoidAlgebra :
    Module.finrank k (MonoidAlgebra k G) = Fintype.card G := by
  exact Module.finrank_eq_card_basis (MonoidAlgebra.basis G k)

omit [IsAlgClosed k] [Group G] [Fintype G] in

/-- The dimension of a finite family of square matrix algebras is the sum of the squares of their sizes. -/
theorem finrank_pi_matrix (n : ℕ) (d : Fin n → ℕ) :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) =
      ∑ i, (d i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  congr 1
  ext i
  simp [Module.finrank_matrix, Fintype.card_fin, sq]


/-- The sum of the squares of the stored dimensions equals the cardinality of the group. -/
theorem DecompositionData.sum_dimension_sq_eq_card [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) :
    ∑ i, (D.dimension i) ^ 2 = Fintype.card G := by
  have hfr := finrank_monoidAlgebra (k := k) (G := G)
  have hiso := D.groupAlgebraEquivMatrix.toLinearEquiv.finrank_eq
  rw [hfr] at hiso
  rw [finrank_pi_matrix] at hiso
  omega




/-- The standard coordinate module is simple over the square matrix ring of nonzero size. -/
instance isSimpleModule_matrix_fin {k : Type*} [Field k] (n : ℕ) [NeZero n] :
    IsSimpleModule (Matrix (Fin n) (Fin n) k) (Fin n → k) where
  eq_bot_or_eq_top m := by
    by_cases hm : m = ⊥
    · left; exact hm
    · right; rw [Submodule.eq_top_iff']
      intro v
      obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra h; push Not at h; exact hwne (funext h)

      let M : Matrix (Fin n) (Fin n) k := fun j l => if l = i then v j * (w i)⁻¹ else 0
      have : M.mulVec w = v := by
        ext j; simp only [Matrix.mulVec, M, dotProduct]; simp [mul_assoc, inv_mul_cancel₀ hi]
      rw [← this]; exact m.smul_mem M hw


/-- Restricting a simple module along a surjective ring homomorphism preserves simplicity. -/
lemma isSimpleModule_restrictScalars_of_surjective {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) [hM : IsSimpleModule S M] :
    @IsSimpleModule R _ M _ (Module.compHom M f) := by
  letI : Module R M := Module.compHom M f
  have key : ∀ m : Submodule R M, m = ⊥ ∨ m = ⊤ := by
    intro m
    let m' : Submodule S M := {
      toAddSubmonoid := m.toAddSubmonoid
      smul_mem' := fun s x hx => by obtain ⟨r, rfl⟩ := hf s; exact m.smul_mem r hx
    }
    have hcarrier : ∀ x, x ∈ m' ↔ x ∈ m := fun _ => Iff.rfl
    cases hM.eq_bot_or_eq_top m' with
    | inl h =>
      left; ext x; constructor
      · intro hx; have := (hcarrier x).mpr hx; rw [h] at this; simpa using this
      · intro hx; simp at hx; rw [hx]; exact m.zero_mem'
    | inr h =>
      right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _; exact (hcarrier x).mp (h ▸ Submodule.mem_top)
  haveI : Nontrivial (Submodule R M) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    obtain ⟨a, b, hab⟩ := @IsSimpleModule.nontrivial S _ M _ _ hM
    have ha : a ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    have hb : b ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    simp at ha hb; exact hab (ha ▸ hb.symm)
  exact { eq_bot_or_eq_top := key }




/-- A ring homomorphism from the group algebra to the square matrix algebra at an index of the decomposition data. -/
noncomputable def DecompositionData.matrixBlockHom [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    MonoidAlgebra k G →+* Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k :=
  (Pi.evalRingHom (fun i => Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) i).comp
    D.groupAlgebraEquivMatrix.toRingEquiv.toRingHom


/-- Each indexed homomorphism from the group algebra to its matrix algebra is surjective. -/
lemma DecompositionData.matrixBlockHom_surjective [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    Function.Surjective (D.matrixBlockHom i) := by
  intro M
  exact ⟨D.groupAlgebraEquivMatrix.symm (Pi.single i M), by simp [matrixBlockHom, Pi.evalRingHom, Pi.single]⟩


/-- A representation on the coordinate space whose size is the indexed natural number in the decomposition data. -/
noncomputable def DecompositionData.coordinateRepresentation [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    Representation k G (Fin (D.dimension i) → k) where
  toFun g := Matrix.mulVecLin (D.matrixBlockHom i (MonoidAlgebra.of k G g))
  map_one' := by rw [map_one, map_one, Matrix.mulVecLin_one]; rfl
  map_mul' g h := by rw [map_mul, map_mul, Matrix.mulVecLin_mul]; rfl


/-- The finite-dimensional representation indexed by an entry of the decomposition data. -/
noncomputable def DecompositionData.representation [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) : FDRep k G :=
  FDRep.of (D.coordinateRepresentation i)


/-- The dimension of an indexed representation equals its stored natural number. -/
lemma DecompositionData.finrank_representation [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    Module.finrank k (D.representation i) = D.dimension i := by
  rw [show Module.finrank k (D.representation i) = Module.finrank k (Fin (D.dimension i) → k) from rfl]
  exact Module.finrank_fin_fun k


/-- The group algebra is equivalent to the family of endomorphism algebras of the indexed representations. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := primary)]
noncomputable def DecompositionData.groupAlgebraEquivRepresentationEnd [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) :
    MonoidAlgebra k G ≃ₐ[k] Π i, Module.End k (D.representation i) :=
  D.groupAlgebraEquivMatrix.trans (AlgEquiv.piCongrRight fun i => Matrix.toLinAlgEquiv')




private lemma Simple.of_full_faithful_preservesMono {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f


private lemma DecompositionData.projRingHom_smul [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count)
    (r : k) (a : MonoidAlgebra k G) :
    D.matrixBlockHom i (r • a) = r • D.matrixBlockHom i a := by
  simp [DecompositionData.matrixBlockHom]


private lemma DecompositionData.asModule_smul_eq_mulVec [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count)
    (a : MonoidAlgebra k G) (v : (D.coordinateRepresentation i).asModule) :
    (D.coordinateRepresentation i).asModuleEquiv (a • v) =
      (D.matrixBlockHom i a).mulVec ((D.coordinateRepresentation i).asModuleEquiv v) := by
  simp only [Representation.asModuleEquiv_map_smul]
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    simp [Representation.asAlgebraHom, MonoidAlgebra.lift_apply,
          Finsupp.sum_single_index, DecompositionData.coordinateRepresentation]
  | hadd a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Matrix.add_mulVec, ha, hb]
  | hsmul r a ha =>
    simp only [map_smul, LinearMap.smul_apply, ha]
    rw [D.projRingHom_smul i r a, Matrix.smul_mulVec r]


/-- The group-algebra module associated with each coordinate representation is simple. -/
noncomputable instance DecompositionData.isSimpleModule_coordinateRepresentation [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    @IsSimpleModule (MonoidAlgebra k G) _ (D.coordinateRepresentation i).asModule _
      (Representation.instModuleMonoidAlgebraAsModule (D.coordinateRepresentation i)) := by
  letI : Module (MonoidAlgebra k G) (D.coordinateRepresentation i).asModule :=
    Representation.instModuleMonoidAlgebraAsModule (D.coordinateRepresentation i)
  haveI := D.dimension_neZero i
  haveI : Nontrivial (D.coordinateRepresentation i).asModule := by
    change Nontrivial (Fin (D.dimension i) → k); infer_instance
  rw [isSimpleModule_iff]
  exact IsSimpleOrder.mk fun m => by
    let m' : Submodule (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) (Fin (D.dimension i) → k) :=
      { carrier := { w | (D.coordinateRepresentation i).asModuleEquiv.symm w ∈ m }
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at *; exact m.add_mem ha hb
        zero_mem' := by simp [m.zero_mem]
        smul_mem' := fun M w hw => by
          simp only [Set.mem_setOf_eq] at *
          change (D.coordinateRepresentation i).asModuleEquiv.symm (M.mulVec w) ∈ m
          obtain ⟨a, ha⟩ := D.matrixBlockHom_surjective i M
          have heq : M.mulVec w = (D.coordinateRepresentation i).asModuleEquiv
              (a • (D.coordinateRepresentation i).asModuleEquiv.symm w) := by
            rw [D.asModule_smul_eq_mulVec, ha]; simp
          rw [heq, LinearEquiv.symm_apply_apply]
          exact m.smul_mem a hw }
    cases (isSimpleModule_matrix_fin (D.dimension i)).eq_bot_or_eq_top m' with
    | inl h =>
      left; apply SetLike.ext; intro x
      simp only [Submodule.mem_bot]
      constructor
      · intro hx
        have hmem : (D.coordinateRepresentation i).asModuleEquiv x ∈ m'.carrier := by
          change (D.coordinateRepresentation i).asModuleEquiv.symm ((D.coordinateRepresentation i).asModuleEquiv x) ∈ m
          rw [LinearEquiv.symm_apply_apply]; exact hx
        rw [h] at hmem; simp at hmem
        exact (D.coordinateRepresentation i).asModuleEquiv.injective hmem
      · intro hx; rw [hx]; exact m.zero_mem
    | inr h =>
      right; apply SetLike.ext; intro x
      simp only [Submodule.mem_top, iff_true]
      have hmem : (D.coordinateRepresentation i).asModuleEquiv x ∈ m'.carrier := by
        rw [h]; exact Submodule.mem_top
      have h2 : (D.coordinateRepresentation i).asModuleEquiv.symm ((D.coordinateRepresentation i).asModuleEquiv x) ∈ m := hmem
      rwa [LinearEquiv.symm_apply_apply] at h2


/-- A finite-dimensional representation whose group-algebra module is simple is a simple categorical representation. -/
noncomputable instance simple_fdRep_of_isSimpleModule [NeZero (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hρ : @IsSimpleModule (MonoidAlgebra k G) _ ρ.asModule _
      (Representation.instModuleMonoidAlgebraAsModule ρ)] :
    Simple (FDRep.of ρ) := by
  letI : Module (MonoidAlgebra k G) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  haveI := hρ
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ))) := by
    exact @simple_of_isSimpleModule (MonoidAlgebra k G) ρ.asModule _ _
      (Representation.instModuleMonoidAlgebraAsModule ρ) hρ
  haveI : Simple ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    Simple.of_full_faithful_preservesMono E.functor _
  exact Simple.of_full_faithful_preservesMono (forget₂ (FDRep k G) (Rep k G)) _




private lemma equivariant_ext [NeZero (Nat.card G : k)] (D : DecompositionData k G) (i j : Fin D.count)
    (f : (Fin (D.dimension i) → k) →ₗ[k] (Fin (D.dimension j) → k))
    (hf : ∀ g : G, ∀ v, f ((D.matrixBlockHom i (MonoidAlgebra.of k G g)).mulVec v) =
      (D.matrixBlockHom j (MonoidAlgebra.of k G g)).mulVec (f v))
    (a : MonoidAlgebra k G) (v : Fin (D.dimension i) → k) :
    f ((D.matrixBlockHom i a).mulVec v) = (D.matrixBlockHom j a).mulVec (f v) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact hf g v
  | hadd a b ha hb =>
    simp only [map_add, Matrix.add_mulVec, f.map_add, ha, hb]
  | hsmul r a ha =>
    rw [D.projRingHom_smul i, D.projRingHom_smul j,
        Matrix.smul_mulVec r, f.map_smul, ha, Matrix.smul_mulVec r]


private lemma DecompositionData.isoToLinearEquiv_equivariant [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i j : Fin D.count)
    (f : D.representation i ≅ D.representation j) (g : G) (v : Fin (D.dimension i) → k) :
    FDRep.isoToLinearEquiv f ((D.matrixBlockHom i (MonoidAlgebra.of k G g)).mulVec v) =
      (D.matrixBlockHom j (MonoidAlgebra.of k G g)).mulVec (FDRep.isoToLinearEquiv f v) := by
  have key := LinearMap.ext_iff.mp (FDRep.Iso.conj_ρ f g) (FDRep.isoToLinearEquiv f v)
  simp [LinearEquiv.conj_apply] at key
  exact key.symm




/-- Every representation indexed by the decomposition data is simple. -/
theorem DecompositionData.simple_representation [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) : Simple (D.representation i) :=
  simple_fdRep_of_isSimpleModule (D.coordinateRepresentation i)


/-- Isomorphic indexed representations in the decomposition data have equal indices. -/
theorem DecompositionData.representation_index_eq_of_iso [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i j : Fin D.count)
    (h : Nonempty ((D.representation i) ≅ (D.representation j))) : i = j := by
  obtain ⟨f⟩ := h
  by_contra hij
  let φ := FDRep.isoToLinearEquiv f
  have hext := equivariant_ext D i j φ.toLinearMap
    (D.isoToLinearEquiv_equivariant i j f)
  let e := D.groupAlgebraEquivMatrix.symm (Pi.single i (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k))
  have h_ei : D.matrixBlockHom i e = 1 := by
    simp [e, DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single, Function.update]
  have h_ej : D.matrixBlockHom j e = 0 := by
    simp [e, DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single, Function.update, Ne.symm hij]
  have hzero : ∀ v : Fin (D.dimension i) → k, φ.toLinearMap v = 0 := by
    intro v; have := hext e v; rw [h_ei, h_ej] at this
    simp [Matrix.one_mulVec, Matrix.zero_mulVec] at this; exact this
  haveI := D.dimension_neZero i
  have hne : (fun (_ : Fin (D.dimension i)) => (1 : k)) ≠ 0 := by
    intro h; exact one_ne_zero (congr_fun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩)
  exact hne (φ.injective ((hzero _).trans (map_zero φ.toLinearMap).symm))




private noncomputable def DecompositionData.centralIdem [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) : MonoidAlgebra k G :=
  D.groupAlgebraEquivMatrix.symm (Pi.single i 1)


private lemma pi_single_sq {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, MulZeroOneClass (R i)] (i : ι) :
    Pi.single (M := R) i 1 * Pi.single i 1 = Pi.single i 1 := by
  funext j; simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]


private lemma DecompositionData.centralIdem_sq [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) :
    D.centralIdem i * D.centralIdem i = D.centralIdem i := by
  simp only [centralIdem, ← map_mul]; congr 1; exact pi_single_sq i


private lemma pi_single_sum {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, AddCommMonoid (R i)] [∀ i, One (R i)] :
    ∑ i, Pi.single (M := R) i 1 = 1 := by
  funext j; simp only [Finset.sum_apply, Pi.one_apply]
  rw [show ∀ (s : Finset ι), ∑ i ∈ s, Pi.single (M := R) i 1 j =
    ∑ i ∈ s, if i = j then (1 : R j) else 0 from fun s => by
    congr 1; ext i; by_cases h : i = j
    · subst h; simp [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]]
  · simp


private lemma DecompositionData.centralIdem_sum [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) :
    ∑ i, D.centralIdem i = 1 := by
  simp only [centralIdem, ← map_sum, ← map_one D.groupAlgebraEquivMatrix.symm]; congr 1; exact pi_single_sum


private lemma pi_single_central {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (a : ∀ j, R j) : Pi.single (M := R) i 1 * a = a * Pi.single i 1 := by
  funext j; simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm h)]; simp


private lemma DecompositionData.centralIdem_comm [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (i : Fin D.count) (a : MonoidAlgebra k G) :
    D.centralIdem i * a = a * D.centralIdem i := by
  apply D.groupAlgebraEquivMatrix.injective
  simp only [centralIdem, map_mul, AlgEquiv.apply_symm_apply]
  exact pi_single_central i (D.groupAlgebraEquivMatrix a)


private lemma DecompositionData.centralIdemAction_comm [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (W : FDRep k G) (i : Fin D.count) (g : G) :
    (Representation.asAlgebraHom W.ρ (D.centralIdem i)).comp (W.ρ g) =
    (W.ρ g).comp (Representation.asAlgebraHom W.ρ (D.centralIdem i)) := by
  have hg : (W.ρ g : W →ₗ[k] W) = Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) := by
    ext v; simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  ext v; simp only [LinearMap.comp_apply, hg]
  have := congr_arg (fun a => Representation.asAlgebraHom W.ρ a v)
    (D.centralIdem_comm i (MonoidAlgebra.of k G g))
  simp only [map_mul] at this
  exact this


private noncomputable def DecompositionData.centralIdemEndo [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (W : FDRep k G) (i : Fin D.count) : W ⟶ W where
  hom := FGModuleCat.ofHom (Representation.asAlgebraHom W.ρ (D.centralIdem i))
  comm h := by
    have heq := D.centralIdemAction_comm W i h
    ext v
    exact LinearMap.congr_fun heq v


private lemma Matrix.one_eq_sum_single (n : ℕ) [NeZero n] :
    (1 : Matrix (Fin n) (Fin n) k) = ∑ j, Matrix.single j j (1 : k) := by
  ext p q; simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply]
  by_cases h : p = q
  · subst h
    convert (Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : k))).symm using 1
    · simp
    · congr 1; ext x; by_cases hx : x = p <;> simp_all
  · convert (Finset.sum_eq_zero (fun c _ => ?_)).symm
    · simp [h]
    · simp only [ite_eq_right_iff]; rintro ⟨rfl, rfl⟩; exact absurd rfl h


private lemma Matrix.mul_single_eq_sum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (j j₀ : Fin n) :
    M * Matrix.single j j₀ (1 : k) =
      ∑ a, M a j • Matrix.single a j₀ (1 : k) := by
  ext p q; simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply,
    mul_one, mul_ite, mul_zero]



  trans (if j₀ = q then M p j else 0)
  · convert Finset.sum_ite_eq Finset.univ j
      (fun x => if j₀ = q then M p x else 0) using 1
    · congr 1; ext x
      by_cases hx : j = x <;> by_cases hq : j₀ = q <;> simp [hx, hq]
    · simp
  · symm; convert Finset.sum_ite_eq' Finset.univ p
      (fun a => if j₀ = q then M a j else 0) using 1
    · congr 1; ext x
      by_cases hxp : x = p <;> by_cases hq : j₀ = q <;> simp [hxp, hq]
    · simp

set_option maxHeartbeats 400000 in

/-- Every simple finite-dimensional representation is isomorphic to an indexed representation from the decomposition data. -/
theorem DecompositionData.exists_iso_representation_of_simple [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (W : FDRep k G) (hW : Simple W) :
    ∃ i, Nonempty (W ≅ D.representation i) := by

  have hschur : ∀ i : Fin D.count, ∃ c : k,
      c • 𝟙 W = D.centralIdemEndo W i := fun i =>
    endomorphism_simple_eq_smul_id k (D.centralIdemEndo W i)
  choose c hc using hschur

  have hc_idem : ∀ i, c i * c i = c i := by
    intro i

    have hendo_sq : D.centralIdemEndo W i ≫ D.centralIdemEndo W i = D.centralIdemEndo W i := by
      ext v
      change Representation.asAlgebraHom W.ρ (D.centralIdem i)
        (Representation.asAlgebraHom W.ρ (D.centralIdem i) v) =
        Representation.asAlgebraHom W.ρ (D.centralIdem i) v
      conv_lhs =>
        rw [show Representation.asAlgebraHom W.ρ (D.centralIdem i)
          (Representation.asAlgebraHom W.ρ (D.centralIdem i) v) =
          (Representation.asAlgebraHom W.ρ (D.centralIdem i * D.centralIdem i)) v from by
            rw [map_mul]; rfl]
      rw [D.centralIdem_sq]



    have hcv : ∀ w : W.V, (D.centralIdemEndo W i).hom.hom w = c i • w := by
      intro w
      exact congr_fun (congr_arg (fun f => f.hom.hom) (hc i).symm) w
    have hpt : ∀ v : W.V,
        (c i * c i - c i) • v = 0 := by
      intro v

      have hsqv := congr_fun (congr_arg (fun f => f.hom.hom) hendo_sq) v



      change (D.centralIdemEndo W i).hom.hom
          ((D.centralIdemEndo W i).hom.hom v) =
          (D.centralIdemEndo W i).hom.hom v at hsqv
      simp only [hcv, smul_smul] at hsqv

      have : (c i * c i - c i) • v = 0 := by rw [sub_smul, hsqv, sub_self]
      exact this

    by_contra hne
    have hne' : c i * c i - c i ≠ 0 := sub_ne_zero.mpr hne

    have : ∀ v : W.V, v = 0 := by
      intro v
      have := hpt v
      rwa [smul_eq_zero, or_iff_right hne'] at this

    exact id_nonzero W (by ext v; simp [this v])

  have hc_sum : ∑ i, c i = 1 := by

    have hcv' : ∀ (i : Fin D.count) (w : W.V),
        (D.centralIdemEndo W i).hom.hom w = c i • w := by
      intro j w
      exact congr_fun (congr_arg (fun f => f.hom.hom) (hc j).symm) w

    have hsum_pt : ∀ v : W.V, (∑ i, c i) • v = v := by
      intro v

      rw [Finset.sum_smul]

      have : ∑ i, c i • v = ∑ i, Representation.asAlgebraHom W.ρ (D.centralIdem i) v :=
        Finset.sum_congr rfl (fun i _ => (hcv' i v).symm)
      rw [this]

      rw [← LinearMap.sum_apply, ← map_sum, D.centralIdem_sum]
      simp [Representation.asAlgebraHom_single, MonoidAlgebra.one_def]

    by_contra hne
    have hne' : ∑ i, c i - 1 ≠ 0 := sub_ne_zero.mpr hne
    have : ∀ v : W.V, v = 0 := by
      intro v
      have h := hsum_pt v
      have h2 : (∑ i, c i - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
      rwa [smul_eq_zero, or_iff_right hne'] at h2
    exact id_nonzero W (by ext v; simp [this v])

  have hc_01 : ∀ i, c i = 0 ∨ c i = 1 := by
    intro i
    have h := hc_idem i
    have h2 : c i * (c i - 1) = 0 := by
      have : c i * (c i - 1) = c i * c i - c i := by ring
      rw [this, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; exact h3
    · right; exact sub_eq_zero.mp h3
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, c i₀ = 1 := by
    by_contra h; push Not at h
    have hall : ∀ i, c i = 0 := fun i => (hc_01 i).resolve_right (h i)
    rw [show ∑ i, c i = ∑ i, (0 : k) from Finset.sum_congr rfl (fun i _ => hall i),
      Finset.sum_const_zero] at hc_sum
    exact one_ne_zero hc_sum.symm



  refine ⟨i₀, ?_⟩

  have hid : D.centralIdemEndo W i₀ = 𝟙 W := by
    have := (hc i₀).symm; rwa [hi₀, one_smul] at this

  have hid_pt : ∀ w : W,
      Representation.asAlgebraHom W.ρ (D.centralIdem i₀) w = w := by
    intro w
    exact congr_arg (fun f => f.hom.hom w) hid

  have heidem_mul : ∀ a : MonoidAlgebra k G,
      D.centralIdem i₀ * a = D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (D.matrixBlockHom i₀ a)) := by
    intro a
    apply D.groupAlgebraEquivMatrix.injective
    simp only [AlgEquiv.apply_symm_apply]
    ext j
    simp only [centralIdem, map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply]
    by_cases h : i₀ = j
    · subst h; simp [Pi.single_eq_same, matrixBlockHom, Pi.evalRingHom]
    · simp [Pi.single_eq_of_ne (Ne.symm h)]

  have hfactor : ∀ (a : MonoidAlgebra k G) (w : W),
      Representation.asAlgebraHom W.ρ a w =
      Representation.asAlgebraHom W.ρ (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (D.matrixBlockHom i₀ a))) w := by
    intro a w
    rw [← heidem_mul, map_mul]
    change Representation.asAlgebraHom W.ρ a w =
      Representation.asAlgebraHom W.ρ (D.centralIdem i₀)
        (Representation.asAlgebraHom W.ρ a w)
    rw [hid_pt]


  haveI := D.dimension_neZero i₀
  haveI := D.simple_representation i₀

  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W.V, w₀ ≠ 0 := by
    by_contra h; push Not at h
    exact id_nonzero W (by ext v; simp [h v])

  have hproj_single : ∀ X : Matrix (Fin (D.dimension i₀)) (Fin (D.dimension i₀)) k,
      D.matrixBlockHom i₀ (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ X)) = X := by
    intro X; simp [matrixBlockHom, Pi.evalRingHom, Pi.single]

  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (D.dimension i₀),
      Representation.asAlgebraHom W.ρ
        (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single j₀ j₀ (1 : k)))) w₀ ≠ 0 := by
    by_contra h; push Not at h
    apply hw₀; rw [← hid_pt w₀]
    have : D.centralIdem i₀ =
        ∑ j, D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single j j (1 : k))) := by
      apply D.groupAlgebraEquivMatrix.injective; rw [map_sum]
      simp only [centralIdem, AlgEquiv.apply_symm_apply]
      conv_lhs => rw [Matrix.one_eq_sum_single (D.dimension i₀) (k := k)]
      ext l; simp only [Finset.sum_apply]
      by_cases hl : i₀ = l
      · subst hl; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne (Ne.symm hl)]
    rw [this, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero (fun j _ => h j)

  set φ : Fin (D.dimension i₀) → W.V :=
    fun j => Representation.asAlgebraHom W.ρ
      (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single j j₀ (1 : k)))) w₀

  have hphi_equivar : ∀ (g : G) (j : Fin (D.dimension i₀)),
      W.ρ g (φ j) = ∑ a, (D.matrixBlockHom i₀ (MonoidAlgebra.of k G g)) a j • φ a := by
    intro g j
    set M := D.matrixBlockHom i₀ (MonoidAlgebra.of k G g)

    have hρ_eq : W.ρ g (φ j) =
        Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) (φ j) := by
      rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul]
    rw [hρ_eq, show Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) (φ j) =
      Representation.asAlgebraHom W.ρ
        (MonoidAlgebra.of k G g * D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single j j₀ 1))) w₀ from by
          rw [map_mul]; rfl]
    rw [hfactor, show D.matrixBlockHom i₀ (MonoidAlgebra.of k G g *
        D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single j j₀ (1 : k)))) =
      M * Matrix.single j j₀ 1 from by rw [map_mul, hproj_single]]
    rw [Matrix.mul_single_eq_sum]


    change (Representation.asAlgebraHom W.ρ)
      (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (∑ a, M a j • Matrix.single a j₀ (1 : k)))) w₀ =
      ∑ a, M a j • (Representation.asAlgebraHom W.ρ)
        (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ (Matrix.single a j₀ 1))) w₀

    let L : Matrix (Fin (D.dimension i₀)) (Fin (D.dimension i₀)) k →ₗ[k] W.V :=
      { toFun := fun X => (Representation.asAlgebraHom W.ρ)
          (D.groupAlgebraEquivMatrix.symm (Pi.single i₀ X)) w₀
        map_add' := fun X Y => by
          simp only [Pi.single_add, map_add, map_add, LinearMap.add_apply]
        map_smul' := fun r X => by
          simp only [Pi.single_smul (f := fun i => Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k),
            map_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
    change L (∑ a, M a j • Matrix.single a j₀ 1) = ∑ a, M a j • L (Matrix.single a j₀ 1)
    rw [map_sum]; congr 1; ext a; rw [map_smul]

  let fHom : D.representation i₀ ⟶ W :=
    { hom := FGModuleCat.ofHom
        { toFun := fun v => ∑ j, v j • φ j
          map_add' := fun v w => by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          map_smul' := fun r v => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [Finset.smul_sum]; congr 1; ext j; rw [smul_smul] }
      comm := fun g => by
        ext v

        change ∑ j, ((D.coordinateRepresentation i₀) g v) j • φ j = W.ρ g (∑ j, v j • φ j)

        rw [map_sum]; simp_rw [map_smul]

        simp_rw [hphi_equivar g]








        simp_rw [show ∀ j, ((D.coordinateRepresentation i₀) g v) j =
          ∑ a, (D.matrixBlockHom i₀ (MonoidAlgebra.of k G g)) j a * v a from fun j => rfl]

        conv_lhs => arg 2; ext x; rw [Finset.sum_smul]

        conv_rhs => arg 2; ext x; rw [Finset.smul_sum]; arg 2; ext a; rw [smul_smul]
        rw [Finset.sum_comm]
        congr 1; ext x; congr 1; ext a; ring }

  have hfHom_ne : fHom ≠ 0 := by
    intro h
    apply hj₀


    have h2 : ∀ v : Fin (D.dimension i₀) → k, ∑ j, v j • φ j = 0 := by
      intro v
      exact congr_arg (fun (f : D.representation i₀ ⟶ W) => f.hom.hom v) h
    specialize h2 (Pi.single (M := fun _ => k) j₀ 1)

    have hs : ∑ j, (Pi.single (M := fun _ => k) j₀ 1) j • φ j = φ j₀ := by
      rw [show ∑ j, (Pi.single (M := fun _ => k) j₀ 1) j • φ j =
        ∑ j, if j = j₀ then φ j else 0 from by
          congr 1; ext j; by_cases hj : j = j₀ <;> simp [hj]]
      rw [Finset.sum_ite_eq']; simp
    rw [hs] at h2; exact h2

  haveI : IsIso fHom := isIso_of_hom_simple hfHom_ne
  exact ⟨(asIso fHom).symm⟩


/-- There exists an indexed family of simple, pairwise nonisomorphic representations containing every simple representation up to isomorphism. -/
theorem DecompositionData.exists_completeSimpleFamily [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) :
    ∃ (V : Fin D.count → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :=
  ⟨D.representation, D.simple_representation, D.representation_index_eq_of_iso, D.exists_iso_representation_of_simple⟩


/-- A pairwise nonisomorphic simple family indexed by the decomposition count admits a reindexing matching the stored dimensions with its dimensions. -/
theorem DecompositionData.exists_reindex_dimension_eq_finrank [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    ∃ σ : Equiv.Perm (Fin D.count), ∀ i, D.dimension (σ i) = Module.finrank k (V i) := by

  choose τ hτ using fun i => D.exists_iso_representation_of_simple (V i) (hV i)

  have hτ_inj : Function.Injective τ := by
    intro i j h
    exact hinj i j ⟨(hτ i).some ≪≫ (h ▸ (hτ j).some.symm)⟩

  have hτ_bij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτ_inj
  let σ := Equiv.ofBijective τ hτ_bij
  refine ⟨σ, fun i => ?_⟩

  rw [show (σ : Fin D.count → Fin D.count) i = τ i from rfl, ← D.finrank_representation (τ i)]
  exact (LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ i).some)).symm




/-- For an indexed pairwise nonisomorphic simple family of the decomposition count, the sum of squared dimensions equals the group cardinality. -/
theorem DecompositionData.sum_finrank_sq_eq_card_of_simple_pairwise [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    ∑ i, (Module.finrank k (V i)) ^ 2 = Fintype.card G := by
  obtain ⟨σ, hσ⟩ := D.exists_reindex_dimension_eq_finrank V hV hinj
  calc ∑ i, (Module.finrank k (V i)) ^ 2
      = ∑ i, (D.dimension (σ i)) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [hσ i]
    _ = ∑ i, (D.dimension i) ^ 2 := Equiv.sum_comp σ (fun i => D.dimension i ^ 2)
    _ = Fintype.card G := D.sum_dimension_sq_eq_card


/-- There exists a complete pairwise nonisomorphic simple family whose squared dimensions sum to the group cardinality. -/
theorem exists_completeSimpleFamily_sum_finrank_sq_eq_card (k : Type u) (G : Type v) [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      ∑ i, (Module.finrank k (V i)) ^ 2 = Fintype.card G := by
  let D : DecompositionData k G := DecompositionData.default
  refine ⟨D.count, D.representation, D.simple_representation, D.representation_index_eq_of_iso,
    D.exists_iso_representation_of_simple, ?_⟩
  exact D.sum_finrank_sq_eq_card_of_simple_pairwise D.representation D.simple_representation D.representation_index_eq_of_iso


/-- For a complete pairwise nonisomorphic simple family, the sum of squared dimensions equals the group cardinality. -/
theorem sum_finrank_sq_eq_card_of_completeSimpleFamily [NeZero (Nat.card G : k)]
    {n : ℕ} (V : Fin n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∑ i, (Module.finrank k (V i)) ^ 2 = Fintype.card G := by
  let D : DecompositionData k G := DecompositionData.default

  choose τ hτ using fun i => D.exists_iso_representation_of_simple (V i) (hV i)
  have hτ_inj : Function.Injective τ := fun i j h =>
    hinj i j ⟨(hτ i).some ≪≫ (h ▸ (hτ j).some.symm)⟩
  have hτ_surj : Function.Surjective τ := fun j => by
    obtain ⟨i, hi⟩ := hsurj (D.representation j) (D.simple_representation j)
    exact ⟨i, (D.representation_index_eq_of_iso j (τ i) ⟨hi.some ≪≫ (hτ i).some⟩).symm⟩
  let e : Fin n ≃ Fin D.count := Equiv.ofBijective τ ⟨hτ_inj, hτ_surj⟩
  calc ∑ i, (Module.finrank k (V i)) ^ 2
      = ∑ i, (D.dimension (e i)) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (e : Fin n → Fin D.count) i = τ i from rfl, ← D.finrank_representation (τ i)]
        exact congrArg (· ^ 2) (LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ i).some))
    _ = ∑ j, (D.dimension j) ^ 2 := Equiv.sum_comp e (fun j => D.dimension j ^ 2)
    _ = Fintype.card G := D.sum_dimension_sq_eq_card

end RepresentationTheory.FDRep.GroupAlgebraDecomposition
