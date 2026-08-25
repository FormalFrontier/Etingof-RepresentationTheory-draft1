/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Module.IsotypicDecomposition
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Hom-space decomposition for semisimple modules

Module homomorphisms between finite-dimensional semisimple modules decompose into their induced
maps on multiplicity spaces.
-/

open scoped DirectSum TensorProduct

namespace RepresentationTheory.Module.SemisimpleHomDecomposition

open RepresentationTheory.Module.IsotypicDecomposition

variable (k A : Type*) {ι : Type*} (X : ι → Type*) (V U : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
  [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- The linear map sending a module homomorphism to its family of postcomposition maps on Hom spaces from the displayed modules. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := supporting)]
def homMultiplicityMap :
    (V →ₗ[A] U) →ₗ[k] (∀ i, (X i →ₗ[A] V) →ₗ[k] (X i →ₗ[A] U)) where
  toFun f := fun i =>
    { toFun := fun g => f ∘ₗ g
      map_add' := fun g g' => by ext x; simp
      map_smul' := fun c g => by ext x; simp }
  map_add' f f' := by ext i g x; simp
  map_smul' c f := by ext i g x; simp

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- At an index and a map from the indexed module, the induced multiplicity map is composition with the original module homomorphism. -/
@[simp,
  source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := supporting),
  source_ref "Chapter3/Discussion_after_Lemma3.1.6/Derived2" (role := supporting)]
theorem homMultiplicityMap_apply_apply (f : V →ₗ[A] U) (i : ι) (g : X i →ₗ[A] V) :
    homMultiplicityMap k A X V U f i g = f ∘ₗ g := rfl

section Equiv

variable (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
  [FiniteDimensional k V] [IsSemisimpleModule A V]
  [FiniteDimensional k U] [IsSemisimpleModule A U]
  (hcV : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))
  (hcU : ∀ (W : Submodule A U), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))

include hpair hcV hcU

/-- The restriction of scalars of a module map is reconstructed by decomposing the source, applying the induced multiplicity maps componentwise, and recombining the target. -/
@[source_ref "Chapter3/Discussion_after_Lemma3.1.6/Derived2" (role := supporting)]
theorem restrictScalars_eq_semisimpleDecomposition_comp (f : V →ₗ[A] U) :
    f.restrictScalars k =
      (isotypicDecompositionEquiv k A X U hpair hcU).toLinearMap ∘ₗ
        (DirectSum.lmap fun i => LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i)) ∘ₗ
          (isotypicDecompositionEquiv k A X V hpair hcV).symm.toLinearMap := by
  have H : (f.restrictScalars k) ∘ₗ
      (isotypicDecompositionEquiv k A X V hpair hcV).toLinearMap =
      (isotypicDecompositionEquiv k A X U hpair hcU).toLinearMap ∘ₗ
        (DirectSum.lmap fun i => LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i)) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    refine TensorProduct.ext' fun g x => ?_
    have heV : (isotypicDecompositionEquiv k A X V hpair hcV)
        (DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x)) = g x :=
      isotypicEvaluation_lof_tmul k A X V i g x
    have heU : (isotypicDecompositionEquiv k A X U hpair hcU)
        (DirectSum.lof k ι (fun i => (X i →ₗ[A] U) ⊗[k] X i) i ((f ∘ₗ g) ⊗ₜ[k] x)) =
          (f ∘ₗ g) x :=
      isotypicEvaluation_lof_tmul k A X U i (f ∘ₗ g) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
      DirectSum.lmap_lof, LinearMap.rTensor_tmul, homMultiplicityMap_apply_apply, heV, heU]
  rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm, H]

/-- Under the semisimple direct-sum decomposition, a vector lies in the kernel exactly when every induced multiplicity-space map annihilates its corresponding component. -/
@[source_ref "Chapter3/Discussion_after_Lemma3.1.6/Derived3" (role := primary)]
theorem mem_ker_iff_forall_multiplicityComponent_eq_zero (f : V →ₗ[A] U) (v : V) :
    v ∈ LinearMap.ker f ↔
      ∀ i, LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i)
        ((isotypicDecompositionEquiv k A X V hpair hcV).symm v i) = 0 := by
  rw [LinearMap.mem_ker]
  have hfacv :
      f v =
        (isotypicDecompositionEquiv k A X U hpair hcU)
          (DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i))
            ((isotypicDecompositionEquiv k A X V hpair hcV).symm v)) := by
    have h := LinearMap.congr_fun
      (restrictScalars_eq_semisimpleDecomposition_comp k A X V U hpair hcV hcU f) v
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe] using h
  rw [hfacv]
  constructor
  · intro hzero i
    have hcomponents :
        DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i))
            ((isotypicDecompositionEquiv k A X V hpair hcV).symm v) = 0 := by
      apply (isotypicDecompositionEquiv k A X U hpair hcU).injective
      simpa using hzero
    have hi := congrArg (fun z => z i) hcomponents
    simpa using hi
  · intro hcomponents
    have hzero :
        DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (homMultiplicityMap k A X V U f i))
            ((isotypicDecompositionEquiv k A X V hpair hcV).symm v) = 0 := by
      ext i
      simpa using hcomponents i
    simp [hzero]

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum factorization, although it does not occur in
the proposition returned by `Function.Injective`. -/
set_option linter.unusedFintypeInType false in
/-- For semisimple modules with the displayed complete pairwise nonisomorphic simple family, the map to multiplicity-space maps is injective. -/
theorem homMultiplicityMap_injective :
    Function.Injective (homMultiplicityMap k A X V U) := by
  classical
  intro f f' h
  have hres : f.restrictScalars k = f'.restrictScalars k := by
    rw [restrictScalars_eq_semisimpleDecomposition_comp k A X V U hpair hcV hcU f,
      restrictScalars_eq_semisimpleDecomposition_comp k A X V U hpair hcV hcU f', h]
  ext v
  exact DFunLike.congr_fun hres v

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum construction, although it does not occur in
the proposition returned by `Function.Surjective`. -/
set_option linter.unusedFintypeInType false in
/-- For semisimple modules with the displayed complete pairwise nonisomorphic simple family, every family of multiplicity-space maps comes from a module homomorphism. -/
theorem homMultiplicityMap_surjective :
    Function.Surjective (homMultiplicityMap k A X V U) := by
  classical
  intro φ
  set eV := isotypicDecompositionEquiv k A X V hpair hcV with heVdef
  set eU := isotypicDecompositionEquiv k A X U hpair hcU with heUdef
  have heU : ∀ i (h : X i →ₗ[A] U) (x : X i),
      eU (DirectSum.lof k ι (fun i => (X i →ₗ[A] U) ⊗[k] X i) i (h ⊗ₜ[k] x)) = h x :=
    fun i h x => isotypicEvaluation_lof_tmul k A X U i h x
  have heVsymm : ∀ i (g : X i →ₗ[A] V) (x : X i),
      eV.symm (g x) = DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x) := by
    intro i g x
    rw [LinearEquiv.symm_apply_eq]
    exact (isotypicEvaluation_lof_tmul k A X V i g x).symm
  set T : (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) →ₗ[k] (⨁ i, (X i →ₗ[A] U) ⊗[k] X i) :=
    DirectSum.lmap (fun i => LinearMap.rTensor (X i) (φ i)) with hTdef
  set fk : V →ₗ[k] U := eU.toLinearMap ∘ₗ T ∘ₗ eV.symm.toLinearMap with hfkdef
  have hfk_gen : ∀ i (g : X i →ₗ[A] V) (x : X i), fk (g x) = (φ i g) x := by
    intro i g x
    simp only [hfkdef, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [heVsymm i g x, hTdef, DirectSum.lmap_lof, LinearMap.rTensor_tmul]
    exact heU i (φ i g) x
  have hAlin : ∀ (a : A) (v : V), fk (a • v) = a • fk v := by
    intro a v
    obtain ⟨w, rfl⟩ := eV.surjective v
    induction w using DirectSum.induction_on with
    | zero => simp
    | of i t =>
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul g x =>
            have hlof :
                eV (DirectSum.of (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x)) = g x :=
              isotypicEvaluation_lof_tmul k A X V i g x
            rw [hlof, ← g.map_smul a x, hfk_gen i g (a • x), hfk_gen i g x,
              (φ i g).map_smul a x]
        | add t₁ t₂ h₁ h₂ =>
            simp only [map_add, smul_add]
            rw [h₁, h₂]
    | add w₁ w₂ h₁ h₂ =>
        simp only [map_add, smul_add]
        rw [h₁, h₂]
  let fA : V →ₗ[A] U :=
    { toFun := fun v => fk v
      map_add' := fun a b => map_add fk a b
      map_smul' := fun a v => hAlin a v }
  refine ⟨fA, ?_⟩
  ext i g x
  exact hfk_gen i g x

/-- The linear equivalence from maps between semisimple modules to families of postcomposition maps between their Hom spaces from representative simple modules. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
noncomputable def homEquivMultiplicityMaps :
    (V →ₗ[A] U) ≃ₗ[k] (∀ i, (X i →ₗ[A] V) →ₗ[k] (X i →ₗ[A] U)) :=
  LinearEquiv.ofBijective (homMultiplicityMap k A X V U)
    ⟨homMultiplicityMap_injective k A X V U hpair hcV hcU,
      homMultiplicityMap_surjective k A X V U hpair hcV hcU⟩

omit [DecidableEq ι] in
/-- The component of the Hom-space equivalence sends a map from a representative simple module to its composite with the original module map. -/
@[simp,
  source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem homEquivMultiplicityMaps_apply_apply (f : V →ₗ[A] U) (i : ι) (g : X i →ₗ[A] V) :
    homEquivMultiplicityMaps k A X V U hpair hcV hcU f i g = f ∘ₗ g := rfl

section Criteria

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum criterion, although it does not occur in the
resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- For semisimple modules with the displayed complete simple family, a linear map is injective exactly when all induced maps on the corresponding Hom spaces are injective. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem injective_iff_forall_injective_homMultiplicityMap (f : V →ₗ[A] U) :
    Function.Injective f ↔
      ∀ i, Function.Injective (homMultiplicityMap k A X V U f i) := by
  classical
  rw [show Function.Injective f ↔ Function.Injective ⇑(f.restrictScalars k) from Iff.rfl,
    restrictScalars_eq_semisimpleDecomposition_comp k A X V U hpair hcV hcU f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp, DirectSum.lmap_injective]
  refine forall_congr' fun i => ?_
  haveI : Nontrivial (X i) := IsSimpleModule.nontrivial (R := A) (M := X i)
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj,
    Module.FaithfullyFlat.lTensor_injective_iff_injective]

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum criterion, although it does not occur in the
resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- For semisimple modules with the displayed complete simple family, a linear map is surjective exactly when all induced maps on the corresponding Hom spaces are surjective. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem surjective_iff_forall_surjective_homMultiplicityMap (f : V →ₗ[A] U) :
    Function.Surjective f ↔
      ∀ i, Function.Surjective (homMultiplicityMap k A X V U f i) := by
  classical
  rw [show Function.Surjective f ↔ Function.Surjective ⇑(f.restrictScalars k) from Iff.rfl,
    restrictScalars_eq_semisimpleDecomposition_comp k A X V U hpair hcV hcU f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    EquivLike.surjective_comp, DirectSum.lmap_surjective]
  refine forall_congr' fun i => ?_
  haveI : Nontrivial (X i) := IsSimpleModule.nontrivial (R := A) (M := X i)
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj,
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective]

omit [DecidableEq ι] in
/- Finiteness is inherited from the injectivity and surjectivity criteria, although it does not
occur in the resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- For semisimple modules whose simple submodules come from a fixed pairwise nonisomorphic family, a linear map is bijective exactly when all induced maps on the corresponding Hom spaces are bijective. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem bijective_iff_forall_bijective_homMultiplicityMap (f : V →ₗ[A] U) :
    Function.Bijective f ↔
      ∀ i, Function.Bijective (homMultiplicityMap k A X V U f i) := by
  classical
  simp_rw [Function.Bijective, forall_and]
  rw [injective_iff_forall_injective_homMultiplicityMap k A X V U hpair hcV hcU f,
    surjective_iff_forall_surjective_homMultiplicityMap k A X V U hpair hcV hcU f]

end Criteria

end Equiv

section Naturality

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- The multiplicity map of the identity is the pointwise identity family. -/
@[simp,
  source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem homMultiplicityMap_id :
    homMultiplicityMap k A X V V (LinearMap.id) = fun _ => LinearMap.id := by
  ext i g x
  simp

variable (W : Type*) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- The multiplicity map of a composite is the pointwise composite of the corresponding multiplicity maps. -/
@[source_ref "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4" (role := primary)]
theorem homMultiplicityMap_comp (f : V →ₗ[A] U) (f' : U →ₗ[A] W) :
    homMultiplicityMap k A X V W (f' ∘ₗ f) =
      fun i => (homMultiplicityMap k A X U W f' i) ∘ₗ
        (homMultiplicityMap k A X V U f i) := by
  ext i g x
  simp

end Naturality

end RepresentationTheory.Module.SemisimpleHomDecomposition
