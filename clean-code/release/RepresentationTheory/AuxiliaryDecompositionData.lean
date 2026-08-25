/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.FDRep.GroupAlgebraDecomposition




































open CategoryTheory

namespace RepresentationTheory.AuxiliaryDecompositionData

universe u v

variable (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G]

/-- Auxiliary data associated with a field and a group. -/



structure AuxiliaryDecompositionData where

  /-- The number of indexed entries in the auxiliary data. -/
  count : ℕ

  /-- The natural-number dimension associated with an indexed module. -/
  dimension : Fin count → ℕ

  /-- Every indexed dimension is nonzero. -/
  dimension_neZero : ∀ i, NeZero (dimension i)

  /-- The algebra homomorphism from the group monoid algebra to the product of all indexed matrix algebras. -/
  matrixProductRepresentation : MonoidAlgebra K G →ₐ[K]
    Π i, Matrix (Fin (dimension i)) (Fin (dimension i)) K

  /-- The product of the indexed matrix representations is surjective. -/
  matrixProductRepresentation_surjective : Function.Surjective matrixProductRepresentation




  /-- The kernel of the product matrix representation is the Jacobson radical of the group monoid algebra. -/
  ker_matrixProductRepresentation : RingHom.ker matrixProductRepresentation.toRingHom =
    Ring.jacobson (MonoidAlgebra K G)

variable {K G}

/-- Auxiliary decomposition data for a finite group over an algebraically closed field. -/


noncomputable def AuxiliaryDecompositionData.auxiliaryData : AuxiliaryDecompositionData K G := by
  classical
  haveI : Module.Finite K (MonoidAlgebra K G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G K)
  haveI : IsArtinianRing (MonoidAlgebra K G) := IsArtinianRing.of_finite K (MonoidAlgebra K G)
  haveI : IsSemiprimaryRing (MonoidAlgebra K G) := inferInstance
  set J := Ring.jacobson (MonoidAlgebra K G) with hJ
  haveI : IsSemisimpleRing (MonoidAlgebra K G ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite K (MonoidAlgebra K G ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K J).toLinearMap (Ideal.Quotient.mkₐ_surjective K J)
  have hwed := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K (MonoidAlgebra K G ⧸ J)
  choose n d hd hn using hwed
  refine
    { count := n
      dimension := d
      dimension_neZero := hd
      matrixProductRepresentation := ((hn.some).toAlgHom).comp (Ideal.Quotient.mkₐ K J)
      matrixProductRepresentation_surjective := ?_
      ker_matrixProductRepresentation := ?_ }
  · intro x
    obtain ⟨y, hy⟩ := EquivLike.surjective hn.some x
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective K J y
    exact ⟨z, by rw [AlgHom.comp_apply, hz]; exact hy⟩
  ·
    have hinj : Function.Injective ((hn.some).toAlgHom.toRingHom) :=
      (EquivLike.injective hn.some)
    have hcomp : (((hn.some).toAlgHom).comp (Ideal.Quotient.mkₐ K J)).toRingHom
        = ((hn.some).toAlgHom.toRingHom).comp ((Ideal.Quotient.mkₐ K J).toRingHom) := rfl
    rw [hcomp, RingHom.ker_comp_of_injective _ hinj, Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker]

/-- The algebra homomorphism from the group monoid algebra to matrices attached to an index. -/
noncomputable def AuxiliaryDecompositionData.matrixRepresentation (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    MonoidAlgebra K G →ₐ[K] Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K :=
  (Pi.evalAlgHom K (fun i => Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) i).comp D.matrixProductRepresentation

/-- Each indexed matrix representation is surjective under the stated finiteness and closure assumptions. -/
lemma AuxiliaryDecompositionData.matrixRepresentation_surjective (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    Function.Surjective (D.matrixRepresentation i) := by
  intro M
  obtain ⟨a, ha⟩ := D.matrixProductRepresentation_surjective (Pi.single i M)
  refine ⟨a, ?_⟩
  simp only [AuxiliaryDecompositionData.matrixRepresentation, AlgHom.comp_apply, ha, Pi.evalAlgHom_apply, Pi.single_eq_same]



/-- The module type indexed by an entry of the auxiliary data. -/
def AuxiliaryDecompositionData.indexedType (D : AuxiliaryDecompositionData K G) (i : Fin D.count) : Type u := Fin (D.dimension i) → K

namespace AuxiliaryDecompositionData

/-- The additive commutative group structure on an indexed module. -/
instance instAddCommGroupModule (D : AuxiliaryDecompositionData K G) (i : Fin D.count) : AddCommGroup (D.indexedType i) :=
  inferInstanceAs (AddCommGroup (Fin (D.dimension i) → K))

/-- The vector-space structure of an indexed module over the field. -/
instance instModuleField (D : AuxiliaryDecompositionData K G) (i : Fin D.count) : Module K (D.indexedType i) :=
  inferInstanceAs (Module K (Fin (D.dimension i) → K))

/-- The module structure of an indexed module over its matrix algebra. -/
instance instModuleMatrix (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    Module (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (D.indexedType i) :=
  inferInstanceAs (Module (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (Fin (D.dimension i) → K))

/-- Field scalars and the indexed matrix algebra form a scalar tower on the indexed module. -/
instance isScalarTower_matrix_module (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    IsScalarTower K (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (D.indexedType i) :=
  inferInstanceAs (IsScalarTower K (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (Fin (D.dimension i) → K))

/-- Each indexed module is finite-dimensional over the field. -/
instance module_finite (D : AuxiliaryDecompositionData K G) (i : Fin D.count) : Module.Finite K (D.indexedType i) :=
  inferInstanceAs (Module.Finite K (Fin (D.dimension i) → K))

/-- The module structure of an indexed module over the group monoid algebra. -/
noncomputable instance instModuleMonoidAlgebra (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    Module (MonoidAlgebra K G) (D.indexedType i) :=
  Module.compHom (D.indexedType i) (D.matrixRepresentation i).toRingHom

/-- Field scalars and the group monoid algebra form a scalar tower on the indexed module. -/

instance isScalarTower_monoidAlgebra_module (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    IsScalarTower K (MonoidAlgebra K G) (D.indexedType i) where
  smul_assoc c x m := by
    change (D.matrixRepresentation i).toRingHom (c • x) • m = c • ((D.matrixRepresentation i).toRingHom x • m)
    have hlin : (D.matrixRepresentation i).toRingHom (c • x) = c • (D.matrixRepresentation i).toRingHom x := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul]
    rw [hlin, smul_assoc]

/-- Each indexed module is simple over the group monoid algebra under the stated assumptions. -/

theorem isSimpleModule_module (D : AuxiliaryDecompositionData K G) (i : Fin D.count) :
    IsSimpleModule (MonoidAlgebra K G) (D.indexedType i) := by
  haveI := D.dimension_neZero i
  haveI : IsSimpleModule (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (D.indexedType i) :=
    inferInstanceAs (IsSimpleModule (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K) (Fin (D.dimension i) → K))
  exact RepresentationTheory.FDRep.GroupAlgebraDecomposition.isSimpleModule_restrictScalars_of_surjective (D.matrixRepresentation i).toRingHom (D.matrixRepresentation_surjective i)










/-- Any two simple modules over an Artinian simple ring are nonemptily linearly equivalent. -/


theorem nonempty_linearEquiv_of_simpleModules {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  obtain ⟨I', ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  haveI : IsSimpleModule R I := IsSimpleModule.congr eM.symm
  haveI : IsSimpleModule R I' := IsSimpleModule.congr eN.symm
  have h : Nonempty ((I' : Submodule R R) ≃ₗ[R] (I : Submodule R R)) :=
    (IsSimpleRing.isIsotypic R R : IsIsotypic R R) I I'
  exact ⟨eM.trans (h.some.symm.trans eN.symm)⟩

/-- The monoid-algebra action on an indexed module agrees with the matrix action through its representation. -/


lemma smul_eq_matrix_smul (D : AuxiliaryDecompositionData K G) (i : Fin D.count) (x : MonoidAlgebra K G) (v : D.indexedType i) :
    x • v = D.matrixRepresentation i x • v := rfl

/-- Two indices are equal when their indexed modules are linearly equivalent over the group monoid algebra. -/




theorem index_eq_of_nonempty_linearEquiv (D : AuxiliaryDecompositionData K G) (i j : Fin D.count)
    (h : Nonempty (D.indexedType i ≃ₗ[MonoidAlgebra K G] D.indexedType j)) : i = j := by
  obtain ⟨φ⟩ := h
  by_contra hij

  obtain ⟨e, he⟩ := D.matrixProductRepresentation_surjective (Pi.single i 1)

  have hei : ∀ v : D.indexedType i, e • v = v := by
    intro v
    have hblock : D.matrixRepresentation i e = 1 := by
      simp only [AuxiliaryDecompositionData.matrixRepresentation, AlgHom.comp_apply, he, Pi.evalAlgHom_apply, Pi.single_eq_same]
    rw [smul_eq_matrix_smul, hblock, one_smul]

  have hej : ∀ w : D.indexedType j, e • w = 0 := by
    intro w
    have hblock : D.matrixRepresentation j e = 0 := by
      simp only [AuxiliaryDecompositionData.matrixRepresentation, AlgHom.comp_apply, he, Pi.evalAlgHom_apply,
        Pi.single_eq_of_ne (Ne.symm hij)]
    rw [smul_eq_matrix_smul, hblock, zero_smul]

  have hzero : ∀ v : D.indexedType i, φ v = 0 := fun v => by
    calc φ v = φ (e • v) := by rw [hei v]
      _ = e • φ v := map_smul φ e v
      _ = 0 := hej (φ v)

  haveI := D.dimension_neZero i
  have hv : (fun _ => (1 : K)) ≠ (0 : D.indexedType i) := fun hcontra =>
    one_ne_zero (congr_fun hcontra ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩)
  exact hv (φ.injective ((hzero _).trans (map_zero φ).symm))

/-- Every simple module over the group monoid algebra is linearly equivalent to an indexed module. -/

theorem exists_module_linearEquiv (D : AuxiliaryDecompositionData K G)
    (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    [IsSimpleModule (MonoidAlgebra K G) M] :
    ∃ i, Nonempty (M ≃ₗ[MonoidAlgebra K G] D.indexedType i) := by
  classical

  have hann : ∀ a : MonoidAlgebra K G, D.matrixProductRepresentation a = 0 → ∀ m : M, a • m = (0 : M) := by
    intro a ha m
    have hmem : a ∈ Ring.jacobson (MonoidAlgebra K G) := by
      rw [← D.ker_matrixProductRepresentation, RingHom.mem_ker]; exact ha
    exact Module.mem_annihilator.mp
      (IsSemisimpleModule.jacobson_le_annihilator (MonoidAlgebra K G) M hmem) m

  have hcentral : ∀ (i : Fin D.count) (b : Π j, Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) K),
      (Pi.single i (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K)) * b
        = b * Pi.single i 1 := by
    intro i b; funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp [Pi.mul_apply, Pi.single_eq_same]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]

  choose ε hε using
    fun i : Fin D.count => D.matrixProductRepresentation_surjective (Pi.single i (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) K))

  have hlin : ∀ (i : Fin D.count) (a : MonoidAlgebra K G) (m : M),
      a • (ε i • m) = ε i • (a • m) := by
    intro i a m
    have h0 : (a * ε i) • m = (ε i * a) • m := by
      apply sub_eq_zero.mp
      rw [← sub_smul]
      apply hann
      rw [map_sub, map_mul, map_mul, hε i, hcentral i (D.matrixProductRepresentation a), sub_self]
    rw [mul_smul, mul_smul] at h0
    exact h0

  have hidem : ∀ (i : Fin D.count) (m : M), ε i • (ε i • m) = ε i • m := by
    intro i m
    rw [← mul_smul]
    apply sub_eq_zero.mp
    rw [← sub_smul]
    apply hann
    rw [map_sub, map_mul, hε i, sub_eq_zero]
    funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp [Pi.mul_apply, Pi.single_eq_same]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]

  have hsum : ∀ m : M, ∑ i, ε i • m = m := by
    intro m
    have h1 : ((∑ i, ε i) - 1) • m = 0 := by
      apply hann
      rw [map_sub, map_one, map_sum]
      have hone : ∑ i, D.matrixProductRepresentation (ε i)
          = (1 : Π j, Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) K) := by
        simp only [hε]
        exact Finset.univ_sum_single 1
      rw [hone, sub_self]
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [← Finset.sum_smul]; exact h1

  let fmap : Fin D.count → (M →ₗ[MonoidAlgebra K G] M) := fun i =>
    { toFun := fun m => ε i • m
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun a m => by simp only [RingHom.id_apply]; exact (hlin i a m).symm }

  haveI : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra K G) M
  obtain ⟨m₀, hm₀⟩ : ∃ m : M, m ≠ 0 := exists_ne 0
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ε i₀ • m₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hm₀ ((hsum m₀).symm.trans (Finset.sum_eq_zero (fun i _ => h i)))
  refine ⟨i₀, ?_⟩

  have hid : ∀ m : M, ε i₀ • m = m := by
    have hne : fmap i₀ ≠ 0 := fun hcontra => hi₀ (by
      have := LinearMap.congr_fun hcontra m₀; simpa [fmap] using this)
    rcases eq_bot_or_eq_top (LinearMap.range (fmap i₀)) with hbot | htop
    · exact absurd (LinearMap.range_eq_bot.mp hbot) hne
    · intro m
      obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp htop m
      have hfx : fmap i₀ (fmap i₀ x) = fmap i₀ x := hidem i₀ x
      have : fmap i₀ m = m := by rw [← hx]; exact hfx
      exact this

  haveI : IsArtinianRing (MonoidAlgebra K G) := IsArtinianRing.of_finite K (MonoidAlgebra K G)
  haveI := D.dimension_neZero i₀
  have hblock : ∀ a : MonoidAlgebra K G, D.matrixRepresentation i₀ a = (D.matrixProductRepresentation a) i₀ := fun _ => rfl
  have hφ_surj : Function.Surjective (D.matrixRepresentation i₀) := D.matrixRepresentation_surjective i₀

  have hkerφ : ∀ a : MonoidAlgebra K G, D.matrixRepresentation i₀ a = 0 → ∀ m : M, a • m = 0 := by
    intro a ha m
    rw [show a • m = (a * ε i₀) • m by rw [mul_smul, hid m]]
    apply hann
    rw [map_mul, hε i₀]
    have hcol : D.matrixProductRepresentation a * Pi.single i₀ (1 : Matrix (Fin (D.dimension i₀)) (Fin (D.dimension i₀)) K)
        = Pi.single i₀ (D.matrixRepresentation i₀ a) := by
      funext j
      rcases eq_or_ne j i₀ with h | h
      · subst h; simp [Pi.mul_apply, Pi.single_eq_same, hblock]
      · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
    rw [hcol, ha, Pi.single_zero]


  have hTM : Module.IsTorsionBySet (MonoidAlgebra K G) M
      (RingHom.ker (D.matrixRepresentation i₀).toRingHom) :=
    fun x a => hkerφ (a : MonoidAlgebra K G) (RingHom.mem_ker.mp a.2) x
  have hTS : Module.IsTorsionBySet (MonoidAlgebra K G) (D.indexedType i₀)
      (RingHom.ker (D.matrixRepresentation i₀).toRingHom) := fun v a => by
    have ha : D.matrixRepresentation i₀ (a : MonoidAlgebra K G) = 0 := RingHom.mem_ker.mp a.2
    rw [smul_eq_matrix_smul, ha, zero_smul]
  letI hQM : Module (MonoidAlgebra K G ⧸ RingHom.ker (D.matrixRepresentation i₀).toRingHom) M := hTM.module
  letI hQS : Module (MonoidAlgebra K G ⧸ RingHom.ker (D.matrixRepresentation i₀).toRingHom) (D.indexedType i₀) :=
    hTS.module

  let e := RingHom.quotientKerEquivOfSurjective (f := (D.matrixRepresentation i₀).toRingHom) hφ_surj
  haveI : IsSimpleRing (MonoidAlgebra K G ⧸ RingHom.ker (D.matrixRepresentation i₀).toRingHom) :=
    IsSimpleRing.of_ringEquiv e.symm inferInstance
  haveI : IsSimpleModule (MonoidAlgebra K G ⧸ RingHom.ker (D.matrixRepresentation i₀).toRingHom) M :=
    (hTM.semilinearMap.isSimpleModule_iff_of_bijective Function.bijective_id).mp inferInstance
  haveI : IsSimpleModule (MonoidAlgebra K G ⧸ RingHom.ker (D.matrixRepresentation i₀).toRingHom) (D.indexedType i₀) :=
    (hTS.semilinearMap.isSimpleModule_iff_of_bijective Function.bijective_id).mp
      (isSimpleModule_module D i₀)

  obtain ⟨eQ⟩ := nonempty_linearEquiv_of_simpleModules (R := MonoidAlgebra K G ⧸
    RingHom.ker (D.matrixRepresentation i₀).toRingHom) M (D.indexedType i₀)

  refine ⟨{ eQ with
    map_smul' := fun a m => by
      have h1 : a • m
          = (Ideal.Quotient.mk (RingHom.ker (D.matrixRepresentation i₀).toRingHom) a) • m :=
        (hTM.mk_smul a m).symm
      have h2 : (Ideal.Quotient.mk (RingHom.ker (D.matrixRepresentation i₀).toRingHom) a) • eQ m
          = a • eQ m := hTS.mk_smul a (eQ m)
      calc eQ (a • m)
          = eQ ((Ideal.Quotient.mk _ a) • m) := by rw [h1]
        _ = (Ideal.Quotient.mk _ a) • eQ m := eQ.map_smul _ _
        _ = a • eQ m := h2 }⟩

/-- The cardinality of the referenced auxiliary type for the monoid algebra equals the number of indexed entries. -/

theorem card_auxiliaryType_eq_count (D : AuxiliaryDecompositionData K G) :
    Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (MonoidAlgebra K G)) = D.count := by

  let P : Fin D.count → (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty (ModuleCat.{u} (MonoidAlgebra K G))).FullSubcategory := fun i =>
    { obj := ModuleCat.of (MonoidAlgebra K G) (D.indexedType i)
      property := by
        haveI := isSimpleModule_module D i
        exact (simple_iff_isSimpleModule (M := D.indexedType i)).mpr inferInstance }
  let f : Fin D.count → RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (MonoidAlgebra K G) :=
    fun i => Quotient.mk (isIsomorphicSetoid _) (P i)
  have hf : Function.Bijective f := by
    constructor
    ·
      intro i j hij
      obtain ⟨iso⟩ := Quotient.exact hij
      exact index_eq_of_nonempty_linearEquiv D i j ⟨(((RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty _).ι).mapIso iso).toLinearEquiv⟩
    ·
      intro c
      obtain ⟨Q, rfl⟩ := Quotient.exists_rep c
      haveI : Simple Q.obj := Q.property
      obtain ⟨i, ⟨e⟩⟩ := exists_module_linearEquiv D (Q.obj : Type u)
      refine ⟨i, Quotient.sound
        ⟨((RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty _).fullyFaithfulι).preimageIso (LinearEquiv.toModuleIso e.symm)⟩⟩
  rw [← Nat.card_fin D.count]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end AuxiliaryDecompositionData

/-- There exists auxiliary decomposition data whose count equals the cardinality of the referenced type for the monoid algebra. -/


theorem exists_auxiliaryDecompositionData_card_eq_count (K : Type u) (G : Type v)
    [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    ∃ (D : AuxiliaryDecompositionData K G), Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} (MonoidAlgebra K G)) = D.count :=
  ⟨AuxiliaryDecompositionData.auxiliaryData, AuxiliaryDecompositionData.card_auxiliaryType_eq_count _⟩

end RepresentationTheory.AuxiliaryDecompositionData
