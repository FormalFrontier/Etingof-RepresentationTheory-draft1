/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import RepresentationTheory.LinearAlgebra.TensorOperations
import Mathlib.Data.Sym.Card
import RepresentationTheory.Alignment.Attribute

/-! # Symmetric tensors -/

namespace RepresentationTheory.LinearAlgebra.SymmetricTensors

open PiTensorProduct

section Tuples

/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness {ι I : Type*} [Fintype ι] {f g : ι → I}
    (h : (Finset.univ : Finset ι).val.map f = (Finset.univ : Finset ι).val.map g) :
    ∃ σ : Equiv.Perm ι, f = g ∘ σ := by
  classical
  have hcard : ∀ c : I, Fintype.card {i // f i = c} = Fintype.card {i // g i = c} := by
    intro c
    have hc := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    simpa only [eq_comm] using hc
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := g) fun c => Fintype.equivOfCardEq (hcard c), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux3 {I : Type*} {n : ℕ} (g : Fin n → I) : Sym I n :=
  ⟨(Finset.univ : Finset (Fin n)).val.map g, by simp⟩

/-- The two displayed expressions are equal. -/
@[simp]
lemma displayed_eq_aux1 {I : Type*} {n : ℕ} (g : Fin n → I) :
    (distinguishedElement_aux3 g : Multiset I) = (Finset.univ : Finset (Fin n)).val.map g := rfl

/-- The displayed map sends the specified input to the stated value. -/
@[simp]
lemma map_apply_aux8 {I : Type*} {n : ℕ} (g : Fin n → I) (σ : Equiv.Perm (Fin n)) :
    distinguishedElement_aux3 (fun i => g (σ i)) = distinguishedElement_aux3 g := by
  refine Sym.ext ?_
  rw [displayed_eq_aux1, displayed_eq_aux1, show (fun i => g (σ i)) = g ∘ σ from rfl, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- There exists a value satisfying the displayed conditions. -/
lemma exists_witness_aux1 {I : Type*} {n : ℕ} {g h : Fin n → I} :
    distinguishedElement_aux3 g = distinguishedElement_aux3 h ↔ ∃ σ : Equiv.Perm (Fin n), g = fun i => h (σ i) := by
  constructor
  · intro hgh
    obtain ⟨σ, hσ⟩ := exists_witness
      (f := g) (g := h) (by simpa using congrArg Sym.toMultiset hgh)
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact map_apply_aux8 h σ

/-- The displayed map is surjective. -/
lemma map_surjective {I : Type*} {n : ℕ} :
    Function.Surjective (distinguishedElement_aux3 (I := I) (n := n)) := by
  intro s
  have hlen : (s : Multiset I).toList.length = n := by
    rw [Multiset.length_toList]; exact s.2
  refine ⟨fun i => (s : Multiset I).toList.get (Fin.cast hlen.symm i), Sym.ext ?_⟩
  rw [displayed_eq_aux1, Fin.univ_val_map, ← List.ofFn_congr hlen, List.ofFn_get,
    Multiset.coe_toList]

end Tuples

section UniversalProperty

variable {k : Type*} [CommRing k] {V N : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup N] [Module k N]

/-- The first displayed submodule is contained in the second. -/
lemma submodule_le {n : ℕ} (Φ : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n →ₗ[k] N)
    (hΦ : ∀ (σ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n), Φ (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) = Φ T) :
    RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n ≤ LinearMap.ker Φ := by
  rw [RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1, Submodule.span_le]
  rintro _ ⟨T, i, j, hij, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦ, sub_self]

/-- A permutation-invariant multilinear map induces a permutation-invariant map on tensors. -/
lemma tensorLift_perm {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f)
    (σ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    PiTensorProduct.lift φ (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) = PiTensorProduct.lift φ T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, RepresentationTheory.LinearAlgebra.TensorOperations.tensor_eq_aux1, PiTensorProduct.lift.tprod]
      rw [hφ σ.symm f]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A linear map between the displayed modules. -/
def linearMap_aux1 {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f) :
    RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n →ₗ[k] N :=
  Submodule.liftQ _ (PiTensorProduct.lift φ) (submodule_le _ (tensorLift_perm φ hφ))

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux3 {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f)
    (f : Fin n → V) : linearMap_aux1 φ hφ (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n f) = φ f := by
  simp [linearMap_aux1, RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap, Submodule.liftQ_apply]

/-- The two displayed expressions are equal. -/
lemma displayed_eq {n : ℕ} {F G : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n →ₗ[k] N}
    (h : ∀ f : Fin n → V, F (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n f) = G (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n f)) : F = G := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      have := h f
      simp only [RepresentationTheory.LinearAlgebra.TensorOperations.tensor_eq_aux3, Submodule.mkQ_apply] at this
      simp only [Submodule.mkQ_apply, map_smul, this]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (k V N) in

/-- An equivalence between permutation-invariant multilinear maps and linear maps from the displayed symmetric quotient. -/
def invariantMultilinearMapEquiv (n : ℕ) :
    {φ : MultilinearMap k (fun _ : Fin n => V) N //
      ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f} ≃
      (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n →ₗ[k] N) where
  toFun φ := linearMap_aux1 φ.1 φ.2
  invFun F := ⟨F.compMultilinearMap (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n), fun σ f => by
    simp only [LinearMap.compMultilinearMap_apply, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux6]⟩
  left_inv φ := by
    ext f
    exact map_apply_aux3 φ.1 φ.2 f
  right_inv F := by
    refine displayed_eq fun f => ?_
    exact map_apply_aux3 (F.compMultilinearMap (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n)) _ f

end UniversalProperty

section Basis

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
  {I : Type*} (b : Module.Basis I k V) (n : ℕ)

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux2 : Module.Basis (Fin n → I) k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :=
  Basis.piTensorProduct fun _ : Fin n => b

/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq (g : Fin n → I) :
    distinguishedElement_aux2 b n g = PiTensorProduct.tprod k fun i => b (g i) :=
  Basis.piTensorProduct_apply _ _

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux1 (σ : Equiv.Perm (Fin n)) (g : Fin n → I) :
    RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ (distinguishedElement_aux2 b n g) = distinguishedElement_aux2 b n (g ∘ σ.symm) := by
  simp [Function.comp_def]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux5 {g h : Fin n → I} (hgh : distinguishedElement_aux3 g = distinguishedElement_aux3 h) :
    RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n (fun i => b (g i)) = RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (h i) := by
  obtain ⟨σ, rfl⟩ := exists_witness_aux1.1 hgh
  exact RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux6 σ fun i => b (h i)

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux4 : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n →ₗ[k] Sym I n →₀ k :=
  Finsupp.lmapDomain k k distinguishedElement_aux3 ∘ₗ (distinguishedElement_aux2 b n).repr.toLinearMap

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux6 (g : Fin n → I) :
    linearMap_aux4 b n (distinguishedElement_aux2 b n g) = Finsupp.single (distinguishedElement_aux3 g) 1 := by
  rw [linearMap_aux4, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq_aux1 (g : Fin n → I) :
    linearMap_aux4 b n (PiTensorProduct.tprod k fun i => b (g i))
      = Finsupp.single (distinguishedElement_aux3 g) 1 := by
  rw [← tensor_eq b n g, map_apply_aux6]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux7 (σ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap_aux4 b n (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) = linearMap_aux4 b n T := by
  have key : linearMap_aux4 b n ∘ₗ (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (k := k) (V := V) σ).toLinearMap
      = linearMap_aux4 b n := by
    refine (distinguishedElement_aux2 b n).ext fun g => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, map_apply_aux1,
      map_apply_aux6, map_apply_aux6,
      show (g ∘ ⇑σ.symm) = fun i => g (σ.symm i) from rfl, map_apply_aux8]
  exact congrArg (fun F => F T) key

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux3 : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n →ₗ[k] Sym I n →₀ k :=
  Submodule.liftQ _ (linearMap_aux4 b n)
    (submodule_le _ (map_apply_aux7 b n))

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux4 (g : Fin n → I) :
    linearMap_aux3 b n (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (g i)) = Finsupp.single (distinguishedElement_aux3 g) 1 := by
  rw [RepresentationTheory.LinearAlgebra.TensorOperations.tensor_eq_aux3, linearMap_aux3, Submodule.mkQ_apply, Submodule.liftQ_apply,
    tensor_eq_aux1]

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement : Sym I n → Fin n → I :=
  Function.surjInv map_surjective

/-- The two displayed expressions are equal. -/
@[simp]
lemma displayed_eq_aux2 (s : Sym I n) : distinguishedElement_aux3 (distinguishedElement n s) = s :=
  Function.surjInv_eq map_surjective s

/-- A linear map between the displayed modules. -/
noncomputable def linearMap : (Sym I n →₀ k) →ₗ[k] RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n :=
  Finsupp.linearCombination k fun s => RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (distinguishedElement n s i)

/-- The displayed map sends the specified input to the stated value. -/
@[simp]
lemma map_apply (s : Sym I n) (c : k) :
    linearMap b n (Finsupp.single s c)
      = c • RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (distinguishedElement n s i) := by
  simp [linearMap]

/-- A linear equivalence between the displayed modules. -/
noncomputable def linearEquiv : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n ≃ₗ[k] Sym I n →₀ k :=
  LinearEquiv.ofLinear (linearMap_aux3 b n) (linearMap b n)
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      change linearMap_aux3 b n (linearMap b n (Finsupp.single s 1)) = Finsupp.single s 1
      rw [map_apply, one_smul, map_apply_aux4, displayed_eq_aux2])
    (by

      have key : (linearMap b n ∘ₗ linearMap_aux3 b n) ∘ₗ
          (RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ = (RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ := by
        refine (distinguishedElement_aux2 b n).ext fun g => ?_
        have h : (RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ (distinguishedElement_aux2 b n g)
            = RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (g i) := by
          rw [tensor_eq, RepresentationTheory.LinearAlgebra.TensorOperations.tensor_eq_aux3]
        rw [LinearMap.comp_apply, LinearMap.comp_apply, h, map_apply_aux4,
          map_apply, one_smul]
        exact map_apply_aux5 b n (by rw [displayed_eq_aux2])
      refine displayed_eq fun f => ?_
      exact congrArg (fun F => F (PiTensorProduct.tprod k f)) key)

/-- A distinguished value of the displayed type. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
noncomputable def distinguishedElement_aux1 : Module.Basis (Sym I n) k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n) :=
  Module.Basis.ofRepr (linearEquiv b n)

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux2 (s : Sym I n) (g : Fin n → I) (hg : distinguishedElement_aux3 g = s) :
    distinguishedElement_aux1 b n s = RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n fun i => b (g i) := by
  have h0 : distinguishedElement_aux1 b n s = (linearEquiv b n).symm (Finsupp.single s 1) :=
    (Module.Basis.repr_symm_single_one (distinguishedElement_aux1 b n) s).symm
  rw [h0, linearEquiv, LinearEquiv.ofLinear_symm_apply, map_apply, one_smul]
  exact map_apply_aux5 b n (by simp [hg])

end Basis

section Finrank

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
theorem finrank_eq [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n) = (Module.finrank k V + n - 1).choose n := by
  classical
  rw [Module.finrank_eq_card_basis (distinguishedElement_aux1 (Module.finBasis k V) n),
    Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem finrank_eq_aux1 [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n) = Nat.multichoose (Module.finrank k V) n := by
  rw [finrank_eq, Nat.multichoose_eq]

end Finrank

end RepresentationTheory.LinearAlgebra.SymmetricTensors

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 RepresentationTheory.LinearAlgebra.SymmetricTensors.linearMap_aux1
  RepresentationTheory.LinearAlgebra.SymmetricTensors.invariantMultilinearMapEquiv RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux2
  RepresentationTheory.LinearAlgebra.SymmetricTensors.linearMap_aux4 RepresentationTheory.LinearAlgebra.SymmetricTensors.linearMap_aux3
  RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement RepresentationTheory.LinearAlgebra.SymmetricTensors.linearMap
  RepresentationTheory.LinearAlgebra.SymmetricTensors.linearEquiv RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux1
