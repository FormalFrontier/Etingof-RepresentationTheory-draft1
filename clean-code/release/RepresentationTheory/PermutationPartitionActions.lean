/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Complex.InvariantInnerProduct
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.Auxiliary.PartitionIndexedAlgebra
import RepresentationTheory.Representation.PermutationGroupSpectrum
import RepresentationTheory.Auxiliary.PartitionPermutationRelations
import RepresentationTheory.Module.PartitionComponentsAndTraces
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.PermutationPartitionActions

open scoped Classical


/-- An auxiliary degree-indexed element, defined for nonzero `n`. -/
@[source_ref "Chapter5/Problem5.16.3" (role := supporting)]
noncomputable def auxiliaryDegreeElementForPartitionPredicate (n : ℕ) [NeZero n] : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (0 : Fin n) < j),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap 0 j)


/-- An auxiliary degree-indexed element, defined for nonzero `n`. -/
noncomputable def auxiliaryDegreeElement (n : ℕ) [NeZero n] : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (0 : Fin n) < p.1 ∧ p.1 < p.2),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)


/-- The monoid homomorphism lifting permutations of `Fin m` to permutations of `Fin (m + 1)` while fixing zero. -/
noncomputable def fixZeroPermutationHom (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.viaEmbeddingHom (Fin.succEmb m)


/-- An auxiliary construction sending a complex representation of permutations of `Fin (m + 1)` to a representation of permutations of `Fin m`. -/
noncomputable def auxiliaryRepresentationToLowerFin (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    Representation ℂ (Equiv.Perm (Fin m)) V :=
  MonoidHom.comp ρ (fixZeroPermutationHom m)


/-- Auxiliary predicate on partitions of a natural number. -/
def auxiliaryPartitionPredicate {n : ℕ} (la : Nat.Partition n) : Prop :=
  ∃ r c : ℕ, la.parts = Multiset.replicate r c


/-- The zero-fixing lift of a transposition is the transposition of the corresponding successor indices. -/
lemma fixZeroPermutationHom_apply_swap (m : ℕ) (i j : Fin m) :
    fixZeroPermutationHom m (Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  rw [fixZeroPermutationHom, Equiv.Perm.viaEmbeddingHom_apply]
  ext x
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨k, rfl⟩
  ·
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
    · simp only [Fin.coe_succEmb, Set.mem_range, not_exists]
      exact fun a => (Fin.succ_ne_zero a)
  ·
    rw [show k.succ = (Fin.succEmb m) k from (Fin.coe_succEmb ▸ rfl),
      Equiv.Perm.viaEmbedding_apply]
    simp only [Fin.coe_succEmb, Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl


/-- For nonzero `n`, the auxiliary degree element for the partition predicate equals the difference of the two other displayed degree-indexed elements. -/
@[source_ref "Chapter5/Problem5.16.3" (role := supporting)]
lemma auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements (n : ℕ) [NeZero n] :
    auxiliaryDegreeElementForPartitionPredicate n = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement n - auxiliaryDegreeElement n := by
  rw [eq_sub_iff_add_eq]

  rw [_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement]
  rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) (fun p => p.1 = 0)]
  congr 1
  ·
    rw [auxiliaryDegreeElementForPartitionPredicate]
    have hset1 : ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
          (fun p => p.1 = 0))
        = (Finset.univ.filter (fun j : Fin n => (0 : Fin n) < j)).map
            ⟨fun j => ((0 : Fin n), j), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hlt, h0⟩
        exact ⟨p.2, by rw [h0] at hlt; exact hlt, Prod.ext h0.symm rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hj, rfl⟩
    rw [hset1, Finset.sum_map]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Function.Embedding.coeFn_mk]
  ·
    rw [auxiliaryDegreeElement]
    apply Finset.sum_congr _ (fun p _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.pos_iff_ne_zero]
    tauto


/-- For a complex representation of permutations of `Fin (m + 1)`, the action of the displayed degree-`(m + 1)` element equals the action of the displayed degree-`m` element after the auxiliary representation-to-lower-`Fin` construction. -/
lemma auxiliaryRepresentationToLowerFin_action_eq (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    Representation.asAlgebraHom ρ (auxiliaryDegreeElement (m + 1))
      = Representation.asAlgebraHom (auxiliaryRepresentationToLowerFin m ρ) (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) := by
  rw [auxiliaryDegreeElement, _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement, map_sum, map_sum]

  have hset : (Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => (0 : Fin (m + 1)) < q.1 ∧ q.1 < q.2))
      = (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).map
          ((Fin.succEmb m).prodMap (Fin.succEmb m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coe_prodMap, Fin.coe_succEmb, Prod.exists,
      Prod.map_apply]
    constructor
    · rintro ⟨h0, hlt⟩
      refine ⟨q.1.pred (Fin.pos_iff_ne_zero.mp h0), q.2.pred (Fin.pos_iff_ne_zero.mp
        (lt_trans h0 hlt)), ?_, ?_⟩
      · rw [Fin.pred_lt_pred_iff]; exact hlt
      · rw [Fin.succ_pred, Fin.succ_pred]
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨Fin.succ_pos a, Fin.succ_lt_succ_iff.mpr hab⟩
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [Function.Embedding.coe_prodMap, Fin.coe_succEmb]
  rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
  change ρ (Equiv.swap p.1.succ p.2.succ) = ρ (fixZeroPermutationHom m (Equiv.swap p.1 p.2))
  rw [fixZeroPermutationHom_apply_swap]


/-- Every eigenvalue of the auxiliary degree element for the partition predicate in a finite complex representation of permutations of `Fin (m + 1)` is an integer. -/
@[source_ref "Chapter5/Problem5.16.3" (role := primary)]
lemma auxiliaryDegreeElementForPartitionPredicate_eigenvalue_is_integer (m : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue
        (Representation.asAlgebraHom ρ (auxiliaryDegreeElementForPartitionPredicate (m + 1))) μ) :
    ∃ z : ℤ, μ = (z : ℂ) := by
  classical
  set A : Module.End ℂ V := Representation.asAlgebraHom ρ (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement (m + 1)) with hA
  set B : Module.End ℂ V := Representation.asAlgebraHom ρ (auxiliaryDegreeElement (m + 1)) with hB
  set T : Module.End ℂ V := Representation.asAlgebraHom ρ (auxiliaryDegreeElementForPartitionPredicate (m + 1)) with hT

  have hTAB : T = A - B := by
    rw [hT, hA, hB, ← map_sub, auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements]

  have hAB : Commute A B := by
    change A * B = B * A
    rw [hA, hB, ← map_mul, ← map_mul,
      _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_commutes (m + 1) (auxiliaryDegreeElement (m + 1))]

  have hAT : Commute A T := by rw [hTAB]; exact (Commute.refl A).sub_right hAB

  obtain ⟨_, hAeig⟩ := _root_.RepresentationTheory.Representation.PermutationGroupSpectrum.representationEndomorphism_isSemisimple_and_eigenvalues_eq_intCast (m + 1) ρ
  have hAint : ∀ α : ℂ, Module.End.HasEigenvalue A α → ∃ z : ℤ, α = (z : ℂ) := by
    intro α hα
    obtain ⟨la, hla⟩ := hAeig α (by rw [hA] at hα; exact hα)
    exact ⟨_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la, hla⟩

  obtain ⟨_, hBeig⟩ := _root_.RepresentationTheory.Representation.PermutationGroupSpectrum.representationEndomorphism_isSemisimple_and_eigenvalues_eq_intCast m (auxiliaryRepresentationToLowerFin m ρ)
  have hBint : ∀ β : ℂ, Module.End.HasEigenvalue B β → ∃ z : ℤ, β = (z : ℂ) := by
    intro β hβ
    rw [hB, auxiliaryRepresentationToLowerFin_action_eq m ρ] at hβ
    obtain ⟨la, hla⟩ := hBeig β hβ
    exact ⟨_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la, hla⟩

  set E := Module.End.eigenspace T μ with hE
  have hAmaps : ∀ x ∈ E, A x ∈ E := by
    intro x hx
    rw [hE, Module.End.mem_eigenspace_iff] at hx ⊢
    calc T (A x) = (A * T) x := by rw [← hAT.symm.eq]; rfl
      _ = A (T x) := rfl
      _ = A (μ • x) := by rw [hx]
      _ = μ • A x := by rw [map_smul]
  haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hμ
  haveI : FiniteDimensional ℂ E := inferInstance

  set A' : Module.End ℂ E := LinearMap.restrict A hAmaps with hA'
  obtain ⟨α, hα'⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨w', hw'mem, hw'ne⟩ := hα'.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hw'mem

  set w : V := (w' : V) with hw
  have hwne : w ≠ 0 := by rw [hw]; exact fun h => hw'ne (Submodule.coe_eq_zero.mp h)
  have hAw : A w = α • w := by
    have h := congrArg (Subtype.val) hw'mem
    simp only [Submodule.coe_smul] at h
    exact h
  have hTw : T w = μ • w := Module.End.mem_eigenspace_iff.mp w'.2

  have hAα : Module.End.HasEigenvalue A α :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAw, hwne⟩

  have hBw : B w = (α - μ) • w := by
    have hBAT : B = A - T := by rw [hTAB]; abel
    rw [hBAT, LinearMap.sub_apply, hAw, hTw, sub_smul]
  have hBβ : Module.End.HasEigenvalue B (α - μ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hBw, hwne⟩
  obtain ⟨za, hza⟩ := hAint α hAα
  obtain ⟨zb, hzb⟩ := hBint (α - μ) hBβ
  refine ⟨za - zb, ?_⟩
  push_cast
  rw [← hza, ← hzb]; ring


/-- For nonzero `n` and a finite complex representation of permutations of `Fin n`, there is a displayed `Fin (finrank)`-indexed collection on whose members the element acts by some scalar; moreover, every eigenvalue of its action is an integer between `1 - n` and `n - 1`. -/
@[source_ref "Chapter5/Problem5.16.3" (role := primary)]
theorem auxiliaryDegreeElementForPartitionPredicate_exists_indexed_scalar_actions_and_eigenvalue_bounds
    (n : ℕ) [NeZero n]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V),
        ∀ i, ∃ μ : ℂ, (Representation.asAlgebraHom ρ) (auxiliaryDegreeElementForPartitionPredicate n) (b i) = μ • b i) ∧
      (∀ μ : ℂ, Module.End.HasEigenvalue
          ((Representation.asAlgebraHom ρ) (auxiliaryDegreeElementForPartitionPredicate n)) μ →
        ∃ m : ℤ, μ = (m : ℂ) ∧ (1 - (n : ℤ)) ≤ m ∧ m ≤ (n : ℤ) - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  haveI : FiniteDimensional ℂ V := inferInstance


  obtain ⟨c, hc⟩ := _root_.RepresentationTheory.Complex.InvariantInnerProduct.Representation.exists_invariantInnerProductCore (Equiv.Perm (Fin (m + 1))) V ρ
  letI icore : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore inferInstance

  have hc' : ∀ (g : Equiv.Perm (Fin (m + 1))) (v w : V),
      (inner ℂ (ρ g v) (ρ g w) : ℂ) = (inner ℂ v w : ℂ) := hc

  have hnorm : ∀ (g : Equiv.Perm (Fin (m + 1))) (x : V), ‖ρ g x‖ = ‖x‖ := by
    intro g x
    have h1 : ‖ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hc' g x x]
    rw [← Real.sqrt_sq (norm_nonneg (ρ g x)), ← Real.sqrt_sq (norm_nonneg x), h1]

  set S : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun j : Fin (m + 1) => (0 : Fin (m + 1)) < j) with hSdef
  have hScard : S.card = m := by
    have hSe : S = Finset.univ.erase (0 : Fin (m + 1)) := by
      ext j; simp [hSdef, Fin.pos_iff_ne_zero, Finset.mem_erase]
    rw [hSe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  set T : Module.End ℂ V :=
    Representation.asAlgebraHom ρ (auxiliaryDegreeElementForPartitionPredicate (m + 1)) with hTdef

  have hTsum : T = ∑ j ∈ S, ρ (Equiv.swap 0 j) := by
    rw [hTdef, auxiliaryDegreeElementForPartitionPredicate, map_sum]
    exact Finset.sum_congr rfl (fun j _ => Representation.asAlgebraHom_of ρ (Equiv.swap 0 j))

  have hswap_symm : ∀ j : Fin (m + 1), (ρ (Equiv.swap (0 : Fin (m + 1)) j)).IsSymmetric := by
    intro j x y
    have hinv : ρ (Equiv.swap (0 : Fin (m + 1)) j) (ρ (Equiv.swap 0 j) y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_self, map_one, Module.End.one_apply]
    calc (inner ℂ (ρ (Equiv.swap 0 j) x) y : ℂ)
        = (inner ℂ (ρ (Equiv.swap 0 j) x)
            (ρ (Equiv.swap 0 j) (ρ (Equiv.swap 0 j) y)) : ℂ) := by rw [hinv]
      _ = (inner ℂ x (ρ (Equiv.swap 0 j) y) : ℂ) := hc' _ _ _

  have hTsym : T.IsSymmetric := by
    intro x y
    rw [hTsum, LinearMap.sum_apply, LinearMap.sum_apply, sum_inner, inner_sum]
    exact Finset.sum_congr rfl (fun j _ => hswap_symm j x y)
  refine ⟨?_, ?_⟩
  ·
    refine ⟨(hTsym.eigenvectorBasis rfl).toBasis, fun i => ⟨(hTsym.eigenvalues rfl i : ℂ), ?_⟩⟩
    rw [OrthonormalBasis.coe_toBasis]
    exact hTsym.apply_eigenvectorBasis rfl i
  · intro μ hμ
    obtain ⟨z, hz⟩ := auxiliaryDegreeElementForPartitionPredicate_eigenvalue_is_integer m ρ μ hμ

    obtain ⟨w, hwmem, hwne⟩ := hμ.exists_hasEigenvector
    have hTw : T w = μ • w := Module.End.mem_eigenspace_iff.mp hwmem
    have hwnorm_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
    set w' : V := ((‖w‖⁻¹ : ℝ) : ℂ) • w with hw'def
    have hw'norm : ‖w'‖ = 1 := by
      rw [hw'def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hwnorm_pos)]
    have hTw' : T w' = μ • w' := by rw [hw'def, map_smul, hTw, smul_comm]

    have hμeq : (inner ℂ w' (T w') : ℂ) = μ := by
      rw [hTw', inner_smul_right, inner_self_eq_norm_sq_to_K, hw'norm]; simp

    have hbound : ‖μ‖ ≤ (m : ℝ) := by
      rw [← hμeq]
      have hexp : (inner ℂ w' (T w') : ℂ)
          = ∑ j ∈ S, (inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ) := by
        rw [hTsum, LinearMap.sum_apply, inner_sum]
      rw [hexp]
      calc ‖∑ j ∈ S, (inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖
          ≤ ∑ j ∈ S, ‖(inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ S, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            calc ‖(inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖
                ≤ ‖w'‖ * ‖ρ (Equiv.swap 0 j) w'‖ := norm_inner_le_norm _ _
              _ = 1 := by rw [hnorm, hw'norm]; norm_num
        _ = (m : ℝ) := by rw [Finset.sum_const, hScard]; simp

    have hzabs : |z| ≤ (m : ℤ) := by
      have hnormμ : ‖μ‖ = |(z : ℝ)| := by rw [hz, Complex.norm_intCast]
      rw [hnormμ] at hbound
      exact_mod_cast hbound
    obtain ⟨hb1, hb2⟩ := abs_le.mp hzabs
    refine ⟨z, hz, ?_, ?_⟩
    · push_cast; omega
    · push_cast; omega




/-- The last-fixing lift sends a cast index to the cast of its image. -/
lemma fixLastPermutationHom_apply_castSucc (m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ (Fin.castSucc k) = Fin.castSucc (σ k) := by
  have h : _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ (Fin.castSuccEmb k) = Fin.castSuccEmb (σ k) := by
    rw [_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ, Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb k
  simpa using h


/-- Every last-fixing permutation lift fixes the last index. -/
lemma fixLastPermutationHom_apply_last (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ (Fin.last m) = Fin.last m := by
  rw [_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
  simp only [Fin.coe_castSuccEmb, Set.mem_range, not_exists]
  exact fun k => ne_of_lt (Fin.castSucc_lt_last k)


/-- Every zero-fixing permutation lift sends zero to zero. -/
lemma fixZeroPermutationHom_apply_zero (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    fixZeroPermutationHom m σ 0 = 0 := by
  rw [fixZeroPermutationHom, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
  simp only [Fin.coe_succEmb, Set.mem_range, not_exists]
  exact fun k => Fin.succ_ne_zero k


/-- The zero-fixing lift sends the successor of an index to the successor of its image. -/
lemma fixZeroPermutationHom_apply_succ (m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    fixZeroPermutationHom m σ (Fin.succ k) = Fin.succ (σ k) := by
  have h : fixZeroPermutationHom m σ (Fin.succEmb m k) = Fin.succEmb m (σ k) := by
    rw [fixZeroPermutationHom, Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply σ (Fin.succEmb m) k
  simpa using h


/-- Rotation on `Fin (m + 1)` sends the cast of `k : Fin m` to its successor. -/
lemma finRotate_apply_castSucc (m : ℕ) (k : Fin m) :
    finRotate (m + 1) (Fin.castSucc k) = Fin.succ k := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (ne_of_lt (Fin.castSucc_lt_last k))]
  simp [Fin.val_succ, Fin.val_castSucc]


/-- The zero-fixing permutation lift is the conjugate of the last-fixing lift by rotation. -/
lemma fixZeroPermutationHom_eq_rotate_mul_fixLast_mul_rotate_inv (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    fixZeroPermutationHom m σ = finRotate (m + 1) * _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ * (finRotate (m + 1))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  induction x using Fin.lastCases with
  | last => rw [finRotate_last, fixLastPermutationHom_apply_last, finRotate_last, fixZeroPermutationHom_apply_zero]
  | cast k => rw [fixLastPermutationHom_apply_castSucc, finRotate_apply_castSucc, finRotate_apply_castSucc, fixZeroPermutationHom_apply_succ]


/-- A partition evaluation has the same value on the zero-fixing and last-fixing lifts of a permutation. -/
lemma partitionEvaluation_fixZero_eq_fixLast (m : ℕ) (la : Nat.Partition (m + 1))
    (σ : Equiv.Perm (Fin m)) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (m + 1) la (fixZeroPermutationHom m σ) =
      _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (m + 1) la (_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ) := by
  rw [fixZeroPermutationHom_eq_rotate_mul_fixLast_mul_rotate_inv]
  exact (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation (m + 1) la).char_conj (_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ m σ) (finRotate (m + 1))


/-- The displayed value at the zero-fixing permutation extension equals the sum, over the specified collection of `m`-partitions, of the corresponding displayed values. -/
lemma partitionValue_fixZero_eq_sum_over_specifiedPartitions (m : ℕ) (la : Nat.Partition (m + 1))
    (σ : Equiv.Perm (Fin m)) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (m + 1) la (fixZeroPermutationHom m σ) =
      ∑ ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la, _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue m ν σ := by
  rw [partitionEvaluation_fixZero_eq_fixLast, _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.value_permutation_hom_succ_eq_sum_partition_finset_pred]


/-- For an `(m + 1)`-partition and an `m`-partition, the displayed auxiliary value is one when the latter belongs to the specified collection and zero otherwise. -/
lemma auxiliaryPartitionValue_eq_indicator (m : ℕ) (la : Nat.Partition (m + 1))
    (ν : Nat.Partition m) :
    _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryRepresentationPartitionCount m (auxiliaryRepresentationToLowerFin m (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation (m + 1) la)) ν
      = if ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la then 1 else 0 := by
  classical
  set ρW := auxiliaryRepresentationToLowerFin m (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation (m + 1) la) with hρW
  haveI : Module.Finite ℂ ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la) := inferInstance

  have hchar : ∀ σ : Equiv.Perm (Fin m),
      _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPermutationTrace m ρW.asModule σ = ∑ ρ ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la, _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue m ρ σ := by
    intro σ
    rw [← _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.representation_trace_eq_auxiliaryPermutationTrace m ρW σ]
    have h1 : LinearMap.trace ℂ _ (ρW σ) =
        _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (m + 1) la (fixZeroPermutationHom m σ) := rfl
    rw [h1, partitionValue_fixZero_eq_sum_over_specifiedPartitions]

  have hfac := _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.factorial_mul_auxiliaryPartitionCount_eq_sum_trace_mul_value_inv m ρW.asModule ν
  have hrhs : ∑ σ : Equiv.Perm (Fin m),
        _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPermutationTrace m ρW.asModule σ * _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue m ν σ⁻¹
      = (Nat.factorial m : ℂ) * (if ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la then 1 else 0) := by
    simp_rw [hchar, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ρ _ => _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.sum_auxiliaryPartitionPermutationValue_mul_inv m ρ ν), ← Finset.mul_sum,
      Finset.sum_ite_eq' (_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la) ν (fun _ => (1 : ℂ))]
  rw [hrhs] at hfac
  have hne : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hmul := mul_left_cancel₀ hne hfac
  change _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPartitionCount m ρW.asModule ν = _
  by_cases h : ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la
  · simp only [h, if_true] at hmul ⊢; exact_mod_cast hmul
  · simp only [h, if_false] at hmul ⊢; exact_mod_cast hmul




/-- In the auxiliary partition representation, applying an algebra element to a supported vector agrees with multiplication by that element. -/
lemma auxiliaryPartitionRepresentation_apply_eq_mul (n : ℕ) (la : Nat.Partition n) (a : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (y : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)) :
    ((Representation.asAlgebraHom (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la) a) y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      = a * (y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
  obtain ⟨mm, hmm⟩ := y
  induction a using MonoidAlgebra.induction_on with
  | hM σ =>
    rw [Representation.asAlgebraHom_of]
    rfl
  | hadd f g hf hg =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, hf, hg, add_mul]
  | hsmul r f hf =>
    have hsm : (Representation.asAlgebraHom (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la)) (r • f)
        = r • (Representation.asAlgebraHom (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la)) f := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, AlgHom.commutes]
    rw [hsm, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hf, smul_mul_assoc]




/-- For a fixed complex scalar, the stated scalar-action equality on every member of the specified subtype is equivalent to equality of the displayed integer-valued function with that scalar on every member of the specified collection. -/
lemma auxiliaryDegreeElement_scalarAction_iff_integerPartitionValue_eq (m : ℕ)
    (la : Nat.Partition (m + 1)) (c : ℂ) :
    (∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la, auxiliaryDegreeElement (m + 1) * x = c • x)
      ↔ ∀ ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la, (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) = c := by
  set ρW := auxiliaryRepresentationToLowerFin m (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation (m + 1) la) with hρW
  set B : Module.End ℂ ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la) :=
    Representation.asAlgebraHom ρW (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m) with hB

  have hBcoe : ∀ y : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la),
      (B y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType (m + 1))
        = auxiliaryDegreeElement (m + 1) * (y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType (m + 1)) := by
    intro y
    rw [hB, hρW, ← auxiliaryRepresentationToLowerFin_action_eq m (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation (m + 1) la)]
    exact auxiliaryPartitionRepresentation_apply_eq_mul (m + 1) la _ y

  have hPiff : (∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la, auxiliaryDegreeElement (m + 1) * x = c • x)
      ↔ ∀ y : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la), B y = c • y := by
    constructor
    · intro h y
      apply Subtype.ext
      rw [hBcoe, Submodule.coe_smul_of_tower]
      exact h _ y.2
    · intro h x hx
      have h2 := congrArg (Subtype.val) (h ⟨x, hx⟩)
      rwa [hBcoe, Submodule.coe_smul_of_tower] at h2
  rw [hPiff]
  constructor
  ·
    intro hB' ν hν
    have hmult : _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryRepresentationPartitionCount m ρW ν ≠ 0 := by
      have : _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryRepresentationPartitionCount m ρW ν = 1 := by
        rw [hρW, auxiliaryPartitionValue_eq_indicator, if_pos hν]
      rw [this]; exact one_ne_zero
    obtain ⟨f, hf_inj⟩ := _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliary_exists_injective_map_of_representationPartitionCount_ne_zero m ρW ν hmult
    set y₀ : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) := ⟨_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC m ν, Submodule.subset_span rfl⟩ with hy0
    have hy0ne : y₀ ≠ 0 := by
      intro h
      have hz : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC m ν : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) = 0 := congrArg Subtype.val h
      have h1 := _root_.RepresentationTheory.PartitionAuxiliary.coeff_one_eq_one m ν
      rw [hz] at h1
      exact zero_ne_one h1
    set w : ρW.asModule := f y₀ with hw
    have hwne : w ≠ 0 := by
      rw [hw]; intro h; exact hy0ne (hf_inj (h.trans (map_zero f).symm))

    have hy0act : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • y₀ = (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • y₀ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul]
      exact _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_at_partition m ν

    have hwact : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • w = (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • w := by
      have hfy : f (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • y₀) = f ((_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • y₀) := by rw [hy0act]
      rw [map_smul, LinearMap.map_smul_of_tower] at hfy
      rw [hw]; exact hfy

    have key : (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • (ρW.asModuleEquiv w) = c • (ρW.asModuleEquiv w) := by
      have e2 : ρW.asModuleEquiv (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • w) = B (ρW.asModuleEquiv w) := by
        rw [Representation.asModuleEquiv_map_smul, hB]
      calc (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • (ρW.asModuleEquiv w)
          = ρW.asModuleEquiv ((_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • w) := by rw [map_smul]
        _ = ρW.asModuleEquiv (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • w) := by rw [hwact]
        _ = B (ρW.asModuleEquiv w) := e2
        _ = c • (ρW.asModuleEquiv w) := hB' _
    have hwne' : ρW.asModuleEquiv w ≠ 0 :=
      fun h => hwne (ρW.asModuleEquiv.injective (by rw [h, map_zero]))
    exact smul_left_injective ℂ hwne' key
  ·
    intro hQ
    set q : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m := _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m - algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c with hq
    have hqcentral : ∀ a : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m, q * a = a * q := by
      intro a
      rw [hq, sub_mul, mul_sub, _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_commutes, Algebra.commutes]
    set L : ρW.asModule →ₗ[_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m] ρW.asModule :=
      { toFun := fun y => q • y
        map_add' := fun a b => smul_add q a b
        map_smul' := fun a y => by
          simp only [RingHom.id_apply]
          rw [smul_smul, smul_smul, hqcentral] } with hL
    have hker : LinearMap.ker L = ⊤ := by
      rw [← top_le_iff, ← IsSemisimpleModule.sSup_simples_eq_top (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule]
      refine sSup_le ?_
      rintro W hWsimple
      obtain ⟨ν, ⟨e⟩⟩ :=
        @_root_.RepresentationTheory.Module.PartitionComponentsAndTraces.exists_partition_linearEquiv_of_simple_submodule m ρW.asModule inferInstance
          (Representation.instModuleMonoidAlgebraAsModule ρW) W hWsimple
      have hνmem : ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la := by
        letI rhoWModule : Module (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule :=
          Representation.instModuleMonoidAlgebraAsModule ρW
        letI wModule : Module (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) W :=
          @Submodule.module (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule inferInstance inferInstance
            rhoWModule W
        letI : Module.Finite ℂ ρW.asModule := inferInstance
        letI : IsNoetherian ℂ ρW.asModule :=
          ⟨fun s ↦ Submodule.fg_of_fg_map_injective ρW.asModuleEquiv.toLinearMap
            ρW.asModuleEquiv.injective
            ((Submodule.fg_iff_finiteDimensional
              (s.map ρW.asModuleEquiv.toLinearMap)).2 inferInstance)⟩
        by_contra hνnot
        have hmult0 : _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryRepresentationPartitionCount m ρW ν = 0 := by
          rw [hρW, auxiliaryPartitionValue_eq_indicator, if_neg hνnot]
        have hcompbot :
            isotypicComponent (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) = ⊥ := by
          rw [← Submodule.restrictScalars_eq_bot_iff (S := ℂ)]
          letI : Module.Finite ℂ (_root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPartitionSubmodule m ρW.asModule ν) := by
            exact Module.Finite.of_injective (_root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPartitionSubmodule m ρW.asModule ν).subtype
              (Submodule.injective_subtype _)
          have hfrz : _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPartitionSubmodule m ρW.asModule ν = ⊥ := by
            rw [← Submodule.finrank_eq_zero (R := ℂ) (M := ρW.asModule), _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.finrank_auxiliaryPartitionSubmodule,
              show _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryPartitionCount m ρW.asModule ν = _root_.RepresentationTheory.Module.PartitionComponentsAndTraces.auxiliaryRepresentationPartitionCount m ρW ν from rfl, hmult0, zero_mul]
          exact hfrz
        have hWle :
            W ≤ isotypicComponent (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) :=
          (@Submodule.le_isotypicComponent (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule inferInstance
            inferInstance rhoWModule W).trans_eq
              (@LinearEquiv.isotypicComponent_eq (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule W
                (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) inferInstance inferInstance inferInstance inferInstance
                rhoWModule wModule inferInstance e)
        rw [hcompbot, le_bot_iff] at hWle
        haveI : Nontrivial (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) :=
          (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule m ν).nontrivial
        letI : Nontrivial W := e.toEquiv.nontrivial
        exact absurd hWle (Submodule.nontrivial_iff_ne_bot.mp inferInstance)
      have hcν : (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) = c := hQ ν hνmem
      intro w hw
      rw [LinearMap.mem_ker]
      change q • w = 0
      set wW : ↥W := ⟨w, hw⟩ with hwW
      have hact_Vnu : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • (e wW) = (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) • (e wW) := by
        apply Subtype.ext
        rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul]
        exact _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_of_mem m ν _ (e wW).2
      have hq_eWW : q • (e wW) = 0 := by
        rw [hq]
        calc
          (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m - algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c) • e wW =
              _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • e wW -
                algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c • e wW :=
            @sub_smul (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule m ν) inferInstance inferInstance
              inferInstance _ _ _
          _ = 0 := by rw [hact_Vnu, algebraMap_smul, hcν, sub_self]
      have hq_wW : q • wW = 0 := by
        apply e.injective
        rw [map_smul, map_zero, hq_eWW]
      have hcoe := congrArg (Subtype.val) hq_wW
      rw [Submodule.coe_smul, Submodule.coe_zero] at hcoe
      exact hcoe
    have hLzero : L = 0 := LinearMap.ker_eq_top.mp hker
    have hgoal : ∀ z : ρW.asModule, _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • z = c • z := by
      intro z
      have hqz : q • z = 0 := by
        have h : L z = 0 := by rw [hLzero, LinearMap.zero_apply]
        exact h
      rw [hq] at hqz
      have hsub :
          (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m - algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c) • z =
            _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • z - algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c • z :=
        @sub_smul (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) ρW.asModule inferInstance inferInstance
          (Representation.instModuleMonoidAlgebraAsModule ρW) _ _ _
      have halg : algebraMap ℂ (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) c • z = c • z :=
        @algebraMap_smul ℂ inferInstance (_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType m) inferInstance inferInstance
          ρW.asModule inferInstance (Representation.instModuleMonoidAlgebraAsModule ρW)
          inferInstance inferInstance c z
      have hqz' : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • z - c • z = 0 := by
        rw [← halg, ← hsub]
        exact hqz
      exact sub_eq_zero.mp hqz'
    intro y
    have hgy := hgoal (ρW.asModuleEquiv.symm y)
    have e1 : ρW.asModuleEquiv (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • ρW.asModuleEquiv.symm y) = B y := by
      rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, hB]
    calc B y = ρW.asModuleEquiv (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement m • ρW.asModuleEquiv.symm y) := e1.symm
      _ = ρW.asModuleEquiv (c • ρW.asModuleEquiv.symm y) := by rw [hgy]
      _ = c • ρW.asModuleEquiv (ρW.asModuleEquiv.symm y) := by rw [map_smul]
      _ = c • y := by rw [LinearEquiv.apply_symm_apply]


/-- For an `(m + 1)`-partition, scalar action by the auxiliary degree element on every member of the specified subtype is equivalent to constancy of the displayed integer-valued function on the specified collection of `m`-partitions. -/
@[source_ref "Chapter5/Problem5.16.3" (role := supporting)]
lemma auxiliaryDegreeElement_scalarAction_iff_constant_integerPartitionValue (m : ℕ) (la : Nat.Partition (m + 1)) :
    (∃ c : ℂ, ∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la, auxiliaryDegreeElement (m + 1) * x = c • x)
      ↔ ∃ c : ℂ, ∀ ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la, (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) = c :=
  exists_congr (auxiliaryDegreeElement_scalarAction_iff_integerPartitionValue_eq m la)




private lemma mem_auxiliaryYoungDiagram_cells_iff_auxiliaryPartitionNatList_getD {n : ℕ} (la : Nat.Partition n) (i j : ℕ) :
    (i, j) ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells ↔ j < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 := by
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD]


private lemma auxiliaryCellPredicate_iff {n : ℕ} (la : Nat.Partition n) (i j : ℕ) :
    (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) i j ↔
      j + 1 = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 ∧
        (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (i + 1) 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 := by
  simp only [_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate, mem_auxiliaryYoungDiagram_cells_iff_auxiliaryPartitionNatList_getD, not_lt]
  omega


private lemma partitionAuxiliaryInt_auxiliaryAtOuterCorner {m : ℕ} (la : Nat.Partition (m + 1)) (c : ℕ × ℕ)
    (hc : (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) c.1 c.2) :
    _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryAtOuterCorner la c hc) = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la - ((c.2 : ℤ) - c.1) := by
  rw [_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt, _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.toYoungDiagram_auxiliaryAtOuterCorner,
    show ((_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCornerTransform (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) c.1 c.2 hc).cells
      = (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells.erase (c.1, c.2) from rfl,
    Finset.sum_erase_eq_sub hc.1]


private lemma auxiliaryAtOuterCorner_mem_partitionFinsetPred {m : ℕ} (la : Nat.Partition (m + 1)) (c : ℕ × ℕ)
    (hc : (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) c.1 c.2) :
    _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryAtOuterCorner la c hc ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la := by
  rw [_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← YoungDiagram.cells_subset_iff, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.toYoungDiagram_auxiliaryAtOuterCorner,
    show ((_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCornerTransform (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) c.1 c.2 hc).cells
      = (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells.erase (c.1, c.2) from rfl]
  exact Finset.erase_subset _ _


private lemma partitionAuxiliaryInt_of_mem_partitionFinsetPred {m : ℕ} (la : Nat.Partition (m + 1)) (ν : Nat.Partition m)
    (hν : ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la) :
    ∃ d : ℕ × ℕ, (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) d.1 d.2 ∧
      _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la - ((d.2 : ℤ) - d.1) := by
  rw [_root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred, Finset.mem_filter] at hν
  have hle : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν) ≤ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) := hν.2
  have hsub : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells ⊆ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells :=
    YoungDiagram.cells_subset_iff.mpr hle
  have hcardla : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells.card = m + 1 := _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.card_toYoungDiagram_cells la
  have hcardν : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells.card = m := _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.card_toYoungDiagram_cells ν
  have hcardsdiff : ((_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells \ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcardla, hcardν]; omega
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcardsdiff
  have hd_mem : d ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells \ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells := by
    rw [hd]; exact Finset.mem_singleton_self d
  rw [Finset.mem_sdiff] at hd_mem
  obtain ⟨hd_la, hd_nν⟩ := hd_mem
  have hcontent : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν + ((d.2 : ℤ) - d.1) := by
    rw [_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt, _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt, ← Finset.sum_sdiff hsub, hd, Finset.sum_singleton]; ring
  have hcorner : (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) d.1 d.2 := by
    refine ⟨hd_la, ?_, ?_⟩
    · intro hbelow
      by_cases hb_ν : (d.1 + 1, d.2) ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells
      · exact hd_nν ((YoungDiagram.mem_cells _).mpr
          ((_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).up_left_mem (Nat.le_succ _) le_rfl
            ((YoungDiagram.mem_cells _).mp hb_ν)))
      · have hmemsd : (d.1 + 1, d.2) ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells \ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells :=
          Finset.mem_sdiff.mpr ⟨hbelow, hb_ν⟩
        rw [hd, Finset.mem_singleton] at hmemsd
        have hcontra : d.1 + 1 = d.1 := congrArg Prod.fst hmemsd
        omega
    · intro hright
      by_cases hr_ν : (d.1, d.2 + 1) ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells
      · exact hd_nν ((YoungDiagram.mem_cells _).mpr
          ((_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).up_left_mem le_rfl (Nat.le_succ _)
            ((YoungDiagram.mem_cells _).mp hr_ν)))
      · have hmemsd : (d.1, d.2 + 1) ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells \ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition ν).cells :=
          Finset.mem_sdiff.mpr ⟨hright, hr_ν⟩
        rw [hd, Finset.mem_singleton] at hmemsd
        have hcontra : d.2 + 1 = d.2 := congrArg Prod.snd hmemsd
        omega
  exact ⟨d, hcorner, by rw [hcontent]; ring⟩


/-- The auxiliary partition predicate holds exactly when the displayed integer-valued function is constant on every member of the specified collection of `m`-partitions. -/
@[source_ref "Chapter5/Problem5.16.3" (role := supporting)]
lemma exists_constant_partitionStatistic_iff_auxiliaryPartitionPredicate (m : ℕ) (la : Nat.Partition (m + 1)) :
    (∃ c : ℂ, ∀ ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la, (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) = c) ↔ auxiliaryPartitionPredicate la := by
  set r := (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length with hr
  have hsum : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = m + 1 := by
    have h1 : Multiset.sum (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)) = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := Multiset.sum_coe _
    rw [← h1, show (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts from
      Multiset.sort_eq la.parts (· ≥ ·), la.parts_sum]
  have hrpos : 0 < r := by
    rw [hr]
    by_contra h
    push Not at h
    have hnil : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    rw [hnil, List.sum_nil] at hsum
    exact absurd hsum (by omega)
  have hpos : ∀ i, i < r → 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 (hr ▸ hi)]
    apply la.parts_pos
    rw [← show (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts from Multiset.sort_eq la.parts (· ≥ ·)]
    exact Multiset.mem_coe.mpr (List.getElem_mem (hr ▸ hi))
  have hanti : ∀ i, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (i + 1) 0 ≤ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 := by
    intro i
    rw [← _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD la i,
        ← _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD la (i + 1)]
    exact (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen_anti i (i + 1) (Nat.le_succ i)
  have hzero : ∀ i, r ≤ i → (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 = 0 := by
    intro i hi
    exact List.getD_eq_default (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 (hr ▸ hi)

  have hbot : (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la))
      (r - 1, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 - 1).1
      (r - 1, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 - 1).2 := by
    change (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) (r - 1) ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 - 1)
    rw [auxiliaryCellPredicate_iff]
    have h1 : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 := hpos (r - 1) (by omega)
    have h2 : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD r 0 = 0 := hzero r le_rfl
    have hr1 : r - 1 + 1 = r := by omega
    exact ⟨by omega, by rw [hr1, h2]; exact h1⟩
  constructor
  ·
    rintro ⟨cc, hc⟩
    by_contra hnrect

    have hdescent : ∃ i, i + 1 < r ∧ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (i + 1) 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 := by
      by_contra hno
      push Not at hno
      apply hnrect
      have hconst : ∀ k, k < r → (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD k 0 = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0 := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ j ih =>
          intro hjr
          have hle := hno j (by omega)
          have hge := hanti j
          have hij := ih (by omega)
          omega
      have hallc : ∀ x ∈ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la), x = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0 := by
        rw [List.forall_mem_iff_getElem]
        intro i hi
        rw [← List.getD_eq_getElem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 hi]
        exact hconst i (hr.symm ▸ hi)
      have hcoe : (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
        Multiset.sort_eq la.parts (· ≥ ·)
      refine ⟨r, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0, ?_⟩
      have hrep : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) = List.replicate r ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0) := by
        rw [hr]; exact List.eq_replicate_length.mpr hallc
      calc la.parts = (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) := hcoe.symm
        _ = (↑(List.replicate r ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0)) : Multiset ℕ) := by rw [← hrep]
        _ = Multiset.replicate r ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD 0 0) := Multiset.coe_replicate _ _
    obtain ⟨i₀, hi₀r, hi₀desc⟩ := hdescent
    have hcorner1 : (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la))
        (i₀, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 - 1).1
        (i₀, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 - 1).2 := by
      change (_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)) i₀ ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 - 1)
      rw [auxiliaryCellPredicate_iff]
      have hpi : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 := hpos i₀ (by omega)
      exact ⟨by omega, hi₀desc⟩
    have hmem1 := auxiliaryAtOuterCorner_mem_partitionFinsetPred la (i₀, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 - 1) hcorner1
    have hmem2 :=
      auxiliaryAtOuterCorner_mem_partitionFinsetPred la (r - 1, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 - 1) hbot
    have hval1 := hc _ hmem1
    have hval2 := hc _ hmem2
    rw [partitionAuxiliaryInt_auxiliaryAtOuterCorner] at hval1 hval2
    have hZ := Int.cast_injective (α := ℂ) (hval1.trans hval2.symm)
    have hpi : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 := hpos i₀ (by omega)
    have hpb : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 := hpos (r - 1) (by omega)
    have hmono : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD (r - 1) 0 ≤ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i₀ 0 := by
      rw [← _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD la i₀,
          ← _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD la (r - 1)]
      exact (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen_anti i₀ (r - 1) (by omega)
    omega
  ·
    intro hrect
    obtain ⟨R, cval, hRc⟩ := hrect
    have hLc : ∀ x ∈ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la), x = cval := by
      intro x hx
      have hmem : x ∈ la.parts := by
        rw [← show (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts from Multiset.sort_eq la.parts (· ≥ ·)]
        exact Multiset.mem_coe.mpr hx
      rw [hRc] at hmem
      exact Multiset.eq_of_mem_replicate hmem
    have hconst : ∀ i, i < r → (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 = cval := by
      intro i hi
      rw [List.getD_eq_getElem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 (hr ▸ hi)]
      exact hLc _ (List.getElem_mem (hr ▸ hi))
    refine ⟨((_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la - (((cval - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))) : ℂ), ?_⟩
    intro ν hν
    obtain ⟨d, hd_corner, hd_content⟩ := partitionAuxiliaryInt_of_mem_partitionFinsetPred la ν hν
    rw [auxiliaryCellPredicate_iff] at hd_corner
    obtain ⟨hd1, hd2⟩ := hd_corner
    have hd1r : d.1 < r := by
      by_contra h
      push Not at h
      rw [hzero d.1 h] at hd1
      omega
    have hd1eq : d.1 = r - 1 := by
      by_contra h
      have hd1lt : d.1 + 1 < r := by omega
      rw [hconst d.1 hd1r, hconst (d.1 + 1) hd1lt] at hd2
      omega
    have hval : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD d.1 0 = cval := hconst d.1 hd1r
    have hd2val : d.2 = cval - 1 := by
      have hh := hd1
      rw [hval] at hh
      omega
    rw [hd_content, hd2val, hd1eq]
    push_cast
    ring


/-- For nonzero `n`, scalar action by the auxiliary degree element for the partition predicate on every member of the specified subtype is equivalent to the auxiliary partition predicate. -/
@[source_ref "Chapter5/Problem5.16.3" (role := primary)]
theorem auxiliaryDegreeElementForPartitionPredicate_scalarAction_iff_auxiliaryPartitionPredicate
    (n : ℕ) [NeZero n] (la : Nat.Partition n) :
    (∃ c : ℂ, ∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la, auxiliaryDegreeElementForPartitionPredicate n * x = c • x) ↔
      auxiliaryPartitionPredicate la := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rw [← exists_constant_partitionStatistic_iff_auxiliaryPartitionPredicate m la,
    ← auxiliaryDegreeElement_scalarAction_iff_constant_integerPartitionValue m la]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) - c, fun x hx => ?_⟩
    have hCn := _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_of_mem (m + 1) la x hx
    have hE := hc x hx
    have hstabx : auxiliaryDegreeElement (m + 1) * x
        = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement (m + 1) * x - auxiliaryDegreeElementForPartitionPredicate (m + 1) * x := by
      have hsub : auxiliaryDegreeElement (m + 1)
          = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement (m + 1) - auxiliaryDegreeElementForPartitionPredicate (m + 1) := by
        rw [auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements]; abel
      rw [hsub, sub_mul]
    rw [hstabx, hCn, hE, ← sub_smul]
  · rintro ⟨c, hc⟩
    refine ⟨(_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) - c, fun x hx => ?_⟩
    have hCn := _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_of_mem (m + 1) la x hx
    have hstab := hc x hx
    have hEx : auxiliaryDegreeElementForPartitionPredicate (m + 1) * x
        = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement (m + 1) * x - auxiliaryDegreeElement (m + 1) * x := by
      rw [auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements, sub_mul]
    rw [hEx, hCn, hstab, ← sub_smul]


/-- If `n` is nonzero and the parts of an `n`-partition are `r` copies of `c`, then the auxiliary degree element for the partition predicate acts on every member of the specified subtype by the scalar `c - r`. -/
@[source_ref "Chapter5/Problem5.16.3" (role := primary)]
theorem auxiliaryDegreeElementForPartitionPredicate_scalarAction_of_parts_eq_replicate
    (n : ℕ) [NeZero n] (la : Nat.Partition n) (r c : ℕ)
    (hrc : la.parts = Multiset.replicate r c) :
    ∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la, auxiliaryDegreeElementForPartitionPredicate n * x = ((c : ℤ) - r : ℂ) • x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩

  have hcoe : (↑(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts := Multiset.sort_eq la.parts (· ≥ ·)
  have hlen : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length = r := by
    rw [← Multiset.coe_card, hcoe, hrc, Multiset.card_replicate]
  have hval : ∀ i, i < r → (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 = c := by
    intro i hi
    have hib : i < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length := by omega
    rw [List.getD_eq_getElem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 hib]
    have hmem : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)[i] ∈ la.parts := by
      rw [← hcoe]; exact Multiset.mem_coe.mpr (List.getElem_mem hib)
    rw [hrc] at hmem
    exact Multiset.eq_of_mem_replicate hmem
  have hz : ∀ i, r ≤ i → (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i 0 = 0 := fun i hi =>
    List.getD_eq_default (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 (by omega)

  have hmul : r * c = m + 1 := by
    have h := la.parts_sum
    rwa [hrc, Multiset.sum_replicate, smul_eq_mul] at h
  have hrpos : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hmul)
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hmul)


  have hcontent_const : ∀ ν ∈ _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred la,
      (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν : ℂ) = (_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) - ((c : ℂ) - r) := by
    intro ν hν
    obtain ⟨d, hd_corner, hd_content⟩ := partitionAuxiliaryInt_of_mem_partitionFinsetPred la ν hν
    rw [auxiliaryCellPredicate_iff] at hd_corner
    obtain ⟨hd1, hd2⟩ := hd_corner

    have hpos1 : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD d.1 0 := lt_of_le_of_lt (Nat.zero_le _) hd2
    have hd1r : d.1 < r := by
      by_contra h; push Not at h; rw [hz d.1 h] at hpos1; omega
    have hvald1 : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD d.1 0 = c := hval d.1 hd1r

    have hd1eq : d.1 = r - 1 := by
      by_contra h
      have hlt : d.1 + 1 < r := by omega
      rw [hval (d.1 + 1) hlt, hvald1] at hd2; omega
    have hd2eq : d.2 = c - 1 := by rw [hvald1] at hd1; omega
    have hZ : _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt ν = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la - ((c : ℤ) - r) := by
      rw [hd_content, hd1eq, hd2eq]; omega
    rw [hZ]; push_cast; ring

  have hstab : ∀ x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule (m + 1) la,
      auxiliaryDegreeElement (m + 1) * x = ((_root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.partitionAuxiliaryInt la : ℂ) - ((c : ℂ) - r)) • x :=
    (auxiliaryDegreeElement_scalarAction_iff_integerPartitionValue_eq m la _).mpr hcontent_const

  intro x hx
  have hCn := _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement_mul_eq_smul_of_mem (m + 1) la x hx
  have hEx : auxiliaryDegreeElementForPartitionPredicate (m + 1) * x
      = _root_.RepresentationTheory.Auxiliary.PartitionIndexedAlgebra.auxiliaryElement (m + 1) * x - auxiliaryDegreeElement (m + 1) * x := by
    rw [auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements, sub_mul]
  rw [hEx, hCn, hstab x hx, ← sub_smul]
  congr 1
  push_cast
  ring

end RepresentationTheory.PermutationPartitionActions
