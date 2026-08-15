/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricPower.Basis
import RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary

open scoped TensorProduct BigOperators
open Module
open RepresentationTheory.SymmetricPower.Basis.SymmetricPower.Basis

namespace RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
variable {d n : ℕ}

section Transvection

/-- A linear map associated with a basis and an ordered pair of finite indices. -/
noncomputable def basisPairLinearMap (bV : Basis (Fin d) k V) (i j : Fin d) : V →ₗ[k] V :=
  LinearMap.id + (bV.coord j).smulRight (bV i)

/-- On the l-th basis vector, the basis-pair linear map adds the i-th basis vector exactly when l equals j. -/
@[simp] lemma basisPairLinearMap_apply_basis
    (bV : Basis (Fin d) k V) (i j l : Fin d) :
    basisPairLinearMap bV i j (bV l) = bV l + (if l = j then bV i else 0) := by
  simp only [basisPairLinearMap, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self]
  by_cases h : l = j <;> simp [h]

private lemma transElem_comp_self
    (bV : Basis (Fin d) k V) {i j : Fin d} (hij : i ≠ j) :
    ((bV.coord j).smulRight (bV i)).comp ((bV.coord j).smulRight (bV i)) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.zero_apply, map_smul,
    Basis.coord_apply, Basis.repr_self, smul_smul]
  rw [Finsupp.single_apply, if_neg hij]
  simp

/-- A linear equivalence associated with a basis and a pair of distinct finite indices. -/
noncomputable def basisPairLinearEquiv
    (bV : Basis (Fin d) k V) (i j : Fin d) (hij : i ≠ j) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (basisPairLinearMap bV i j)
    (LinearMap.id - (bV.coord j).smulRight (bV i))
    (by
      simp only [basisPairLinearMap, LinearMap.add_comp, LinearMap.comp_sub,
        LinearMap.id_comp, LinearMap.comp_id, transElem_comp_self bV hij]
      abel)
    (by
      simp only [basisPairLinearMap, LinearMap.sub_comp, LinearMap.comp_add,
        LinearMap.id_comp, LinearMap.comp_id, transElem_comp_self bV hij]
      abel)

/-- For distinct indices, the linear map underlying the basis-pair equivalence is the associated basis-pair linear map. -/
@[simp] lemma basisPairLinearEquiv_toLinearMap
    (bV : Basis (Fin d) k V) (i j : Fin d) (hij : i ≠ j) :
    (basisPairLinearEquiv bV i j hij : V →ₗ[k] V) = basisPairLinearMap bV i j :=
  rfl

end Transvection

section Expansion

variable [Module.Finite k V]

omit [Module.Finite k V] in
/-- The displayed transformation of the element indexed by p is the sum over subsets of positions where p equals j, replacing p by i on each selected subset. -/
theorem basisPairLinearMap_apply_eq_sum
    (bV : Basis (Fin d) k V) (i j : Fin d) (p : Fin n → Fin d) :
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
        (basisPairLinearMap bV i j) (basis bV (indexOfFunction p)) =
      ∑ s ∈ (Finset.univ.filter (fun m => p m = j)).powerset,
        basis bV (indexOfFunction (fun m => if m ∈ s then i else p m)) := by
  classical
  have expand : PiTensorProduct.tprod k (fun m => basisPairLinearMap bV i j (bV (p m))) =
      ∑ s : Finset (Fin n), PiTensorProduct.tprod k
        (s.piecewise (fun m => if p m = j then bV i else 0) (fun m => bV (p m))) := by
    rw [← MultilinearMap.map_add_univ]
    congr 1
    funext m
    rw [basisPairLinearMap_apply_basis, Pi.add_apply]
    exact add_comm _ _
  rw [basis_ofFunction,
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap_mk, tensorBasis,
    Basis.piTensorProduct_apply]
  simp only [PiTensorProduct.map_tprod]
  rw [expand, map_sum,
    ← Finset.sum_subset
      (Finset.subset_univ ((Finset.univ.filter (fun m => p m = j)).powerset))
      (fun s _ hs => by
        rw [Finset.mem_powerset] at hs
        obtain ⟨m, hms, hmJ⟩ := Finset.not_subset.mp hs
        have hpm : p m ≠ j :=
          fun h => hmJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        have hz :
            (Finset.piecewise s (fun m => if p m = j then bV i else 0)
              (fun m => bV (p m))) m = 0 := by
          rw [Finset.piecewise_eq_of_mem (s := s)
            (f := fun m => if p m = j then bV i else 0) (g := fun m => bV (p m)) hms]
          simp [hpm]
        rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod k) m hz, map_zero])]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Finset.mem_powerset] at hs
  rw [basis_ofFunction, tensorBasis, Basis.piTensorProduct_apply]
  refine congrArg (SymmetricPower.mk k (Fin n) V)
    (congrArg (fun f => PiTensorProduct.tprod k f) (funext (fun m => ?_)))
  by_cases hm : m ∈ s
  · have hpj : p m = j := (Finset.mem_filter.mp (hs hm)).2
    rw [Finset.piecewise_eq_of_mem (s := s)
      (f := fun m => if p m = j then bV i else 0) (g := fun m => bV (p m)) hm]
    simp [hpj, hm]
  · rw [Finset.piecewise_eq_of_notMem (s := s)
      (f := fun m => if p m = j then bV i else 0) (g := fun m => bV (p m)) hm]
    simp [hm]

omit [Module.Finite k V] in
/-- If p maps m₀ to j, the coefficient at the index obtained by updating p at m₀ to i is nonzero after the displayed transformation. -/
theorem basisPairLinearMap_update_coeff_ne_zero [CharZero k]
    (bV : Basis (Fin d) k V) (i j : Fin d) (p : Fin n → Fin d) (m₀ : Fin n)
    (hm₀ : p m₀ = j) :
    (basis bV).repr
        (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
          (basisPairLinearMap bV i j) (basis bV (indexOfFunction p)))
        (indexOfFunction (Function.update p m₀ i)) ≠ 0 := by
  classical
  rw [basisPairLinearMap_apply_eq_sum, map_sum, Finsupp.finsetSum_apply]
  simp only [Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_boole, Ne, Nat.cast_eq_zero, Finset.card_eq_zero,
    ← Ne, ← Finset.nonempty_iff_ne_empty]
  refine ⟨{m₀}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩⟩
  · exact Finset.singleton_subset_iff.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₀⟩)
  · refine congrArg indexOfFunction (funext (fun m => ?_))
    simp only [Finset.mem_singleton, Function.update_apply]

end Expansion

section Connectivity

/-- A binary relation on two elements of the same indexed type. -/
def objectRelation : Index n (Fin d) → Index n (Fin d) → Prop :=
  fun M N => ∃ (p : Fin n → Fin d) (m₀ : Fin n) (c : Fin d),
    indexOfFunction p = M ∧ indexOfFunction (Function.update p m₀ c) = N ∧ p m₀ ≠ c

/-- Every pair of elements of the indexed type lies in the reflexive-transitive closure of the binary relation. -/
theorem objectRelation_reflTransGen (M N : Index n (Fin d)) :
    Relation.ReflTransGen (objectRelation (n := n) (d := d)) M N := by
  classical
  refine Quotient.inductionOn₂ M N (fun p q => ?_)
  suffices H : ∀ (D : Finset (Fin n)) (p : Fin n → Fin d),
      (∀ m, p m ≠ q m → m ∈ D) →
      Relation.ReflTransGen (objectRelation (n := n) (d := d))
        (indexOfFunction p) (indexOfFunction q) by
    exact H (Finset.univ.filter (fun m => p m ≠ q m)) p (by intro m h; simp [h])
  intro D
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    intro p hp
    by_cases hpq : ∀ m, p m = q m
    · rw [congrArg indexOfFunction (funext hpq)]
    · simp only [not_forall] at hpq
      obtain ⟨m₀, hm₀⟩ := hpq
      have hm₀D : m₀ ∈ D := hp m₀ hm₀
      have step : objectRelation (n := n) (d := d) (indexOfFunction p)
          (indexOfFunction (Function.update p m₀ (q m₀))) :=
        ⟨p, m₀, q m₀, rfl, rfl, hm₀⟩
      have hsub : D.erase m₀ ⊂ D := Finset.erase_ssubset hm₀D
      have hp' : ∀ m, (Function.update p m₀ (q m₀)) m ≠ q m → m ∈ D.erase m₀ := by
        intro m hm
        have hmm0 : m ≠ m₀ := by
          rintro rfl; exact hm (by rw [Function.update_self])
        refine Finset.mem_erase.mpr ⟨hmm0, hp m ?_⟩
        rwa [Function.update_of_ne hmm0] at hm
      exact Relation.ReflTransGen.head step (ih _ hsub _ hp')

end Connectivity

section Step

variable [CharZero k] [Module.Finite k V]

omit [Module.Finite k V] in
/-- Under the scaling and invariance hypotheses, membership of the displayed vector indexed by M passes to the displayed vector indexed by any related N. -/
theorem _root_.RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps.Submodule.mem_of_objectRelation
    (bV : Basis (Fin d) k V)
    {T : Module.End k (SymmetricPower k (Fin n) V)} {w : Index n (Fin d) → k}
    (hT : ∀ M, T (basis bV M) = w M • basis bV M)
    (hw : Function.Injective w)
    {W : Submodule k (SymmetricPower k (Fin n) V)}
    (hWT : ∀ x ∈ W, T x ∈ W)
    (hWG : ∀ g : V ≃ₗ[k] V, ∀ x ∈ W,
      RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
        (g : V →ₗ[k] V) x ∈ W)
    (M N : Index n (Fin d))
    (hMW : basis bV M ∈ W)
    (hMN : objectRelation M N) :
    basis bV N ∈ W := by
  obtain ⟨p, m₀, c, rfl, rfl, hpc⟩ := hMN
  have hy : RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap
      (basisPairLinearEquiv bV c (p m₀) (fun h => hpc h.symm) : V →ₗ[k] V)
      (basis bV (indexOfFunction p)) ∈ W :=
    hWG _ _ hMW
  rw [basisPairLinearEquiv_toLinearMap] at hy
  exact RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis.basis_mem_of_mem_invariant_and_repr_ne_zero
    (basis bV) hT hw hWT hy
    (basisPairLinearMap_update_coeff_ne_zero bV c (p m₀) p m₀ rfl)

end Step

end RepresentationTheory.LinearAlgebra.SymmetricPower.BasisPairMaps
