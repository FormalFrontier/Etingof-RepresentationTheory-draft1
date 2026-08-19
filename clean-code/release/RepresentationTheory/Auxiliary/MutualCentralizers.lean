/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.CentralizerDecomposition
import RepresentationTheory.AuxiliaryEndomorphismActions
import RepresentationTheory.PiTensorProduct.Constructions

open scoped TensorProduct

namespace RepresentationTheory.Auxiliary.MutualCentralizers

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.maxHeartbeats false

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- An auxiliary type associated with a field, a module, and a natural parameter. -/
abbrev auxiliarySpace := ⨂[k] (_ : Fin n), V

/-- The auxiliary space of a finite module is finite over the base field. -/
instance finite_auxiliarySpace : Module.Finite k (auxiliarySpace k V n) := by
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  let b := Module.Free.chooseBasis k V
  exact Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin n => b))

/-- A permutation of a finite index type induces a linear self-equivalence of the auxiliary space. -/
noncomputable def auxiliarySpacePermutationEquiv (σ : Equiv.Perm (Fin n)) :
    auxiliarySpace k V n ≃ₗ[k] auxiliarySpace k V n :=
  PiTensorProduct.reindex k (fun _ => V) σ

/-- The subalgebra of auxiliary-space endomorphisms associated with permutations. -/
noncomputable def permutationActionAlgebra :
    Subalgebra k (Module.End k (auxiliarySpace k V n)) :=
  Algebra.adjoin k (Set.range fun (σ : Equiv.Perm (Fin n)) =>
    (auxiliarySpacePermutationEquiv k V n σ).toLinearMap)

/-- An auxiliary subalgebra of endomorphisms of the auxiliary space. -/
noncomputable def auxiliaryEndomorphismAlgebra :
    Subalgebra k (Module.End k (auxiliarySpace k V n)) :=
  Algebra.adjoin k (Set.range fun (f : Module.End k V) =>
    PiTensorProduct.map (fun _ => f))

omit [Module.Finite k V] in
/-- The permutation equivalence commutes with the map induced by applying one linear endomorphism factorwise. -/
theorem auxiliarySpacePermutationEquiv_comp_factorwiseMap (σ : Equiv.Perm (Fin n)) (f : Module.End k V) :
    (auxiliarySpacePermutationEquiv k V n σ).toLinearMap ∘ₗ PiTensorProduct.map (fun _ => f) =
    PiTensorProduct.map (fun _ => f) ∘ₗ (auxiliarySpacePermutationEquiv k V n σ).toLinearMap := by
  unfold auxiliarySpacePermutationEquiv
  apply LinearMap.ext
  intro x
  change (PiTensorProduct.reindex k (fun _ => V) σ) (PiTensorProduct.map (fun _ => f) x) =
    PiTensorProduct.map (fun _ => f) ((PiTensorProduct.reindex k (fun _ => V) σ) x)
  exact (PiTensorProduct.map_reindex (fun (_ : Fin n) => f) σ x).symm

omit [Module.Finite k V] in
/-- Every permutation-action endomorphism commutes with the auxiliary endomorphism algebra. -/
theorem permutationActionAlgebra_le_centralizer_auxiliaryEndomorphismAlgebra :
    permutationActionAlgebra k V n ≤ Subalgebra.centralizer k
      (auxiliaryEndomorphismAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) := by
  unfold permutationActionAlgebra
  apply Algebra.adjoin_le
  rintro x ⟨σ, rfl⟩
  simp only [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro y hy
  unfold auxiliaryEndomorphismAlgebra at hy
  have hcomm : ∀ g ∈ Set.range (fun (f : Module.End k V) =>
      PiTensorProduct.map (R := k) (fun (_ : Fin n) => f)),
      Commute (↑(auxiliarySpacePermutationEquiv k V n σ) : Module.End k (auxiliarySpace k V n)) g := by
    rintro g ⟨f, rfl⟩
    exact auxiliarySpacePermutationEquiv_comp_factorwiseMap k V n σ f
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy hcomm).symm.eq

omit [Module.Finite k V] in
/-- Every element of the auxiliary endomorphism algebra commutes with the permutation-action algebra. -/
theorem auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra :
    auxiliaryEndomorphismAlgebra k V n ≤ Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) := by
  rw [Subalgebra.le_centralizer_iff]
  exact permutationActionAlgebra_le_centralizer_auxiliaryEndomorphismAlgebra k V n

/-- Permutations define a monoid homomorphism into auxiliary-space endomorphisms. -/
noncomputable def permutationAction :
    Equiv.Perm (Fin n) →* Module.End k (auxiliarySpace k V n) where
  toFun σ := (auxiliarySpacePermutationEquiv k V n σ).toLinearMap
  map_one' := by
    simp only [auxiliarySpacePermutationEquiv]
    apply LinearMap.ext; intro x
    change (PiTensorProduct.reindex k (fun _ => V) (Equiv.refl _)) x = x
    simp [PiTensorProduct.reindex_refl]
  map_mul' σ τ := by
    simp only [auxiliarySpacePermutationEquiv]
    apply LinearMap.ext
    intro x
    change (PiTensorProduct.reindex k (fun _ => V) (σ * τ)) x =
      (PiTensorProduct.reindex k (fun _ => V) σ)
        ((PiTensorProduct.reindex k (fun _ => V) τ) x)
    rw [show (σ * τ : Equiv.Perm (Fin n)) = τ.trans σ from rfl,
      ← PiTensorProduct.reindex_reindex]

/-- The permutation action on the auxiliary space extends to an algebra homomorphism from the permutation group algebra. -/
noncomputable def permutationGroupAlgebraAction :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] Module.End k (auxiliarySpace k V n) :=
  MonoidAlgebra.lift k (Module.End k (auxiliarySpace k V n)) (Equiv.Perm (Fin n))
    (permutationAction k V n)

omit [Module.Finite k V] in
/-- The range of the permutation group algebra action is the permutation-action subalgebra. -/
theorem range_permutationGroupAlgebraAction :
    (permutationGroupAlgebraAction k V n).range = permutationActionAlgebra k V n := by
  unfold permutationGroupAlgebraAction permutationActionAlgebra
  apply le_antisymm
  ·
    rintro x ⟨f, rfl⟩
    induction f using MonoidAlgebra.induction_linear with
    | zero => exact Subalgebra.zero_mem _
    | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
    | single a b =>
      change (MonoidAlgebra.lift k _ _ (permutationAction k V n))
        (MonoidAlgebra.single a b) ∈ _
      rw [MonoidAlgebra.lift_single]
      exact Subalgebra.smul_mem _
        (Algebra.subset_adjoin (Set.mem_range.mpr ⟨a, by simp [permutationAction]⟩)) _
  ·
    apply Algebra.adjoin_le
    rintro x ⟨σ, rfl⟩
    exact ⟨MonoidAlgebra.single σ 1, by
      simp [MonoidAlgebra.lift_single, permutationAction]⟩

/-- The permutation-action algebra is semisimple when the base field has characteristic zero. -/
instance permutationActionAlgebra_semisimple
    [CharZero k] :
    IsSemisimpleRing (permutationActionAlgebra k V n) := by
  rw [← range_permutationGroupAlgebraAction]
  haveI : NeZero (Nat.card (Equiv.Perm (Fin n)) : k) := by
    rw [Nat.card_perm, Nat.card_fin]
    exact ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)⟩
  exact (permutationGroupAlgebraAction k V n).toRingHom.rangeRestrict.isSemisimpleRing_of_surjective
    (permutationGroupAlgebraAction k V n).toRingHom.rangeRestrict_surjective

omit [Module.Finite k V] in
/-- The permutation-action algebra acts faithfully on the auxiliary space. -/
theorem faithfulSMul_permutationActionAlgebra_auxiliarySpace :
    FaithfulSMul (permutationActionAlgebra k V n) (auxiliarySpace k V n) := by
  constructor
  intro a b hab
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact hab x

/-- The centralizer of the permutation-action algebra is the auxiliary endomorphism algebra. -/
theorem centralizer_permutationActionAlgebra
    [CharZero k] :
    Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) =
    auxiliaryEndomorphismAlgebra k V n := by
  apply le_antisymm
  ·
    open TensorProducts.Auxiliary in
    intro φ hφ
    rw [Subalgebra.mem_centralizer_iff] at hφ
    change φ ∈ PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n
    have hconj : ∀ σ : Equiv.Perm (Fin n),
        (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap * φ *
        (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap = φ := by
      intro σ
      set e := PiTensorProduct.reindex k (fun _ => V) σ
      have hcomm := hφ e.toLinearMap (Algebra.subset_adjoin ⟨σ, rfl⟩)
      have he_inv : e.toLinearMap * e.symm.toLinearMap = 1 := by
        ext v; simp [Module.End.mul_eq_comp]
      calc e.toLinearMap * φ * e.symm.toLinearMap
          = φ * e.toLinearMap * e.symm.toLinearMap := by rw [hcomm]
        _ = φ * (e.toLinearMap * e.symm.toLinearMap) := by rw [mul_assoc]
        _ = φ * 1 := by rw [he_inv]
        _ = φ := mul_one _
    set fullDiag := PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n
    have hfact : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hmem : φ ∈ Submodule.span k (Set.range fun f : Fin n → Module.End k V =>
        PiTensorProduct.map f) :=
      @span_range_map_eq_top k _ V _ _ n _ _ ▸ Submodule.mem_top
    have hsum := sum_reindexConjugates_mem_auxiliary (k := k) (V := V) (n := n) φ hmem
    have heq : ∑ σ : Equiv.Perm (Fin n),
        (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap * φ *
        (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap =
        (n.factorial : k) • φ := by
      simp_rw [hconj, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k]
    rw [heq] at hsum
    have := fullDiag.toSubmodule.smul_mem (n.factorial : k)⁻¹ hsum
    rwa [inv_smul_smul₀ hfact] at this
  · exact auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
      k V n

/-- The two associated endomorphism subalgebras are centralizers of one another in characteristic zero. -/
@[source_ref "Chapter5/Theorem5.18.4" (role := primary)]
theorem mutual_centralizer_algebras
    [CharZero k] :
    permutationActionAlgebra k V n = Subalgebra.centralizer k
      (auxiliaryEndomorphismAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n)))
    ∧ auxiliaryEndomorphismAlgebra k V n = Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) := by
  have h_cent := centralizer_permutationActionAlgebra k V n
  constructor
  ·
    haveI := permutationActionAlgebra_semisimple k V n
    haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
    rw [← h_cent]
    exact (CentralizerDecomposition.centralizer_centralizer_eq k (auxiliarySpace k V n) (permutationActionAlgebra k V n)).symm
  ·
    exact h_cent.symm

/-- Both associated endomorphism subalgebras are semisimple over a characteristic-zero field. -/
@[source_ref "Chapter5/Theorem5.18.4" (role := supporting)]
theorem associatedSubalgebras_semisimple
    [CharZero k] :
    IsSemisimpleRing (permutationActionAlgebra k V n)
    ∧ IsSemisimpleRing (auxiliaryEndomorphismAlgebra k V n) := by
  constructor
  · exact permutationActionAlgebra_semisimple k V n
  ·
    rw [← centralizer_permutationActionAlgebra
      k V n]
    haveI := permutationActionAlgebra_semisimple k V n
    haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
    exact CentralizerDecomposition.isSemisimpleRing_centralizer k (auxiliarySpace k V n) (permutationActionAlgebra k V n)

/-- In characteristic zero, the auxiliary space of a finite module is linearly equivalent to a direct sum of tensor products. -/
theorem exists_auxiliarySpace_decomposition_of_charZero
    [CharZero k] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type (max u v)) (L : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i)),
      Nonempty (auxiliarySpace k V n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] L i)) := by
  haveI := permutationActionAlgebra_semisimple k V n
  haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  obtain ⟨ι, hι, hι_dec, V', W', hV'_acg, hV'_mod,
    hV'_Amod, hV'_simp, hW'_acg, hW'_mod, ⟨e⟩⟩ :=
    CentralizerDecomposition.exists_directSum_tensorProduct_equiv k
      (auxiliarySpace k V n) (permutationActionAlgebra k V n)
  exact ⟨ι, hι, hι_dec, V', W',
    hV'_acg, hV'_mod, hV'_Amod, hV'_simp, hW'_acg, hW'_mod, ⟨e⟩⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

/-- Over an algebraically closed field of characteristic zero, the auxiliary space of a finite module is linearly equivalent to a direct sum of tensor products. -/
theorem exists_auxiliarySpace_decomposition
    [IsAlgClosed k] [CharZero k] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type (max u v))
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i j, Nonempty (S i ≃ₗ[permutationActionAlgebra k V n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → Type (max u v)) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module (auxiliaryEndomorphismAlgebra k V n) (L i)),
      Nonempty (auxiliarySpace k V n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] L i)) := by
  haveI := permutationActionAlgebra_semisimple k V n
  haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  obtain ⟨ι, hι, hι_dec, S', hS'_acg, hS'_mod, hS'_Amod, hS'_simp,
    hS'_dist, hS'_fin, L', hL'_acg, hL'_mod, hL'_Bmod, _hL'_smul, _hL'_fin, ⟨e⟩⟩ :=
    CentralizerDecomposition.exists_auxiliary_tensor_decomposition k (auxiliarySpace k V n)
      (permutationActionAlgebra k V n)
  have h_eq : Subalgebra.centralizer k
      (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n))) =
        auxiliaryEndomorphismAlgebra k V n :=
    (mutual_centralizer_algebras k V n).2.symm
  refine ⟨ι, hι, hι_dec, S', hS'_acg, hS'_mod, hS'_Amod, hS'_simp, hS'_dist,
    hS'_fin, L', hL'_acg, hL'_mod, fun i => h_eq ▸ hL'_Bmod i, ⟨e⟩⟩

/-- The permutation-action subalgebra carries its induced ring structure. -/
noncomputable local instance (priority := high) permutationActionAlgebraRing :
    Ring (permutationActionAlgebra k V n) := (permutationActionAlgebra k V n).toRing

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1200000 in

/-- An auxiliary-space decomposition can be chosen whose inverse sends each component pure tensor to its evaluation. -/
theorem exists_auxiliarySpace_decomposition_evaluation
    [IsAlgClosed k] [CharZero k] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i j, Nonempty (↥(S i) ≃ₗ[permutationActionAlgebra k V n] ↥(S j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(S i))
      (_ : ∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k
          (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n)))))
        (↥(S i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n)),
      ∃ (e : auxiliarySpace k V n ≃ₗ[k]
          DirectSum ι
            (fun i => ↥(S i) ⊗[k] (↥(S i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n))),
        ∀ (i : ι) (v : ↥(S i))
          (l : ↥(S i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
          e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v := by
  haveI := permutationActionAlgebra_semisimple k V n
  haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  exact CentralizerDecomposition.exists_auxiliary_evaluation_equiv k (auxiliarySpace k V n)
    (permutationActionAlgebra k V n)

set_option maxHeartbeats 4000000 in

set_option synthInstance.maxHeartbeats 1500000 in

/-- An auxiliary-space decomposition can be selected with compatible component maps and an intertwining condition for an associated algebra action. -/
theorem exists_auxiliarySpace_decomposition_with_compatibility
    [IsAlgClosed k] [CharZero k] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Submodule (permutationActionAlgebra k V n) (auxiliarySpace k V n))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i j, Nonempty (↥(S i) ≃ₗ[permutationActionAlgebra k V n] ↥(S j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(S i))
      (_ : ∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k
          (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n)))))
        (↥(S i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n)),
      ∃ e : CentralizerDecomposition.AuxiliaryDecompositionData
          (k := k) (E := auxiliarySpace k V n) (A := permutationActionAlgebra k V n) S,
        (∀ (i : ι) (s : ↥(S i))
            (l : ↥(S i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
          e.equiv.symm (DirectSum.of _ i (s ⊗ₜ[k] l)) = l s) ∧
        ∀ (b : ↥(auxiliaryEndomorphismAlgebra k V n)) (x : auxiliarySpace k V n),
          e.equiv (b.val x) =
            CentralizerDecomposition.centralizerActionOnTensorDirectSum
              (k := k) (E := auxiliarySpace k V n) (A := permutationActionAlgebra k V n) S
              (⟨b.val, auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
                k V n b.property⟩ :
                ↥(Subalgebra.centralizer k
                  (permutationActionAlgebra k V n :
                    Set (Module.End k (auxiliarySpace k V n)))))
              (e.equiv x) := by
  obtain ⟨ι, hι, hιDec, S, hSSimple, hSDistinct, hSFinite, hLSimple, e, he⟩ :=
    CentralizerDecomposition.exists_auxiliary_decomposition_data k (auxiliarySpace k V n)
      (permutationActionAlgebra k V n)
  refine ⟨ι, hι, hιDec, S, hSSimple, hSDistinct, hSFinite, hLSimple, e, he, ?_⟩
  intro b x
  exact e.equiv_apply_centralizer
    (⟨b.val, auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra k V n b.property⟩ :
      ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n))))) x

/-- The general linear group of a coordinate module acts through the centralizer of the permutation-action algebra. -/
noncomputable def generalLinearGroupHomToPermutationCentralizer
    (k : Type u) [Field k] (N n : ℕ) :
    Matrix.GeneralLinearGroup (Fin N) k →*
      ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k (Fin N → k) n :
          Set (Module.End k (auxiliarySpace k (Fin N → k) n)))) where
  toFun g := ⟨PiTensorProduct.map
      (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val),
    auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra k (Fin N → k) n
      (Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩)⟩
  map_one' := by
    apply Subtype.ext
    change PiTensorProduct.map
        (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) = 1
    have h : (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) =
        (fun _ : Fin n => (LinearMap.id : (Fin N → k) →ₗ[k] (Fin N → k))) :=
      funext fun _ => Matrix.mulVecLin_one
    rw [h, PiTensorProduct.map_id]; rfl
  map_mul' g₁ g₂ := by
    apply Subtype.ext
    change PiTensorProduct.map
        (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
      PiTensorProduct.map
          (fun _ : Fin n => Matrix.mulVecLin (R := k) g₁.val) *
        PiTensorProduct.map
          (fun _ : Fin n => Matrix.mulVecLin (R := k) g₂.val)
    have h : (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
        (fun _ : Fin n => (Matrix.mulVecLin g₁.val).comp
          (Matrix.mulVecLin g₂.val)) :=
      funext fun _ => Matrix.mulVecLin_mul g₁.val g₂.val
    rw [h, PiTensorProduct.map_comp]; rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

/-- A coordinate-module decomposition can be chosen so that its component maps realize pure tensors and intertwine the general linear action. -/
theorem exists_fin_auxiliarySpace_decomposition_with_action_compatibility
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (_hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Submodule (permutationActionAlgebra k (Fin N → k) n)
        (auxiliarySpace k (Fin N → k) n))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (↥(S i) ≃ₗ[permutationActionAlgebra k (Fin N → k) n] ↥(S j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
        (↥(S i) →ₗ[permutationActionAlgebra k (Fin N → k) n]
          auxiliarySpace k (Fin N → k) n)),
      ∃ (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          DirectSum ι (fun i => ↥(S i) ⊗[k] (L i : Type u))),
        (∀ (i : ι) (v : ↥(S i)) (l : (L i : Type u)),
          e.symm (DirectSum.of (fun i => ↥(S i) ⊗[k] (L i : Type u)) i
              (v ⊗ₜ[k] l)) = (L_carrier i l) v) ∧
        (∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k)
            (l : (L i : Type u)) (v : ↥(S i)),
          (L_carrier i ((L i).ρ g l)) v =
            PiTensorProduct.map
              (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
              ((L_carrier i l) v)) := by
  set V : Type u := Fin N → k with hV
  haveI : Module.Finite k V := inferInstance
  haveI := permutationActionAlgebra_semisimple k V n
  haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, _, e, he⟩ :=
    exists_auxiliarySpace_decomposition_evaluation k V n
  let glHom : Matrix.GeneralLinearGroup (Fin N) k →*
      ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n)))) :=
    generalLinearGroupHomToPermutationCentralizer k N n
  haveI hLi_fin : ∀ i, Module.Finite k
      ((↥(S' i) : Type u) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :=
    fun i => by
      haveI : Module.Finite k (↥(S' i) : Type u) := hS'_fin i
      haveI : Module.Free k (↥(S' i) : Type u) :=
        Module.Free.of_divisionRing k (↥(S' i))
      haveI : Module.Finite k
          ((↥(S' i) : Type u) →ₗ[k] auxiliarySpace k V n) :=
        Module.Finite.linearMap k k (↥(S' i)) (auxiliarySpace k V n)
      letI : AddCommGroup
          ((↥(S' i) : Type u) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      letI : AddCommGroup ((↥(S' i) : Type u) →ₗ[k] auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      let f : ((↥(S' i) : Type u) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) →ₗ[k]
          ((↥(S' i) : Type u) →ₗ[k] auxiliarySpace k V n) :=
        LinearMap.restrictScalarsₗ k (permutationActionAlgebra k V n) (↥(S' i))
          (auxiliarySpace k V n) k
      refine @FiniteDimensional.of_injective k _ inferInstance inferInstance inferInstance _
        inferInstance inferInstance f ?_ inferInstance
      intro x y h
      exact LinearMap.ext fun v ↦ LinearMap.congr_fun h v
  let ρ : ∀ i, Matrix.GeneralLinearGroup (Fin N) k →*
      Module.End k (↥(S' i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) := fun i =>
    (CentralizerDecomposition.centralizerActionMonoidHom k (auxiliarySpace k V n) (permutationActionAlgebra k V n)
      (↥(S' i))).comp glHom
  let L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) := fun i =>
    FDRep.of (ρ i)
  let L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
      (↥(S' i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n) :=
    fun i => LinearEquiv.refl k _
  refine ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, L, L_carrier, e, he, ?_⟩
  intro i g l v
  rfl

set_option maxHeartbeats 3200000 in

set_option synthInstance.maxHeartbeats 1600000 in

/-- For a coordinate module and a bounded natural parameter, the auxiliary space is linearly equivalent to a direct sum of tensor products with representation carriers. -/
theorem exists_fin_auxiliarySpace_decomposition
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (S i ≃ₗ[permutationActionAlgebra k (Fin N → k) n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      Nonempty (auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] (L i : Type u))) := by
  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, L, _, e, _⟩ :=
    exists_fin_auxiliarySpace_decomposition_with_action_compatibility k N n hN
  exact ⟨ι, hι, hι_dec, fun i => ↥(S' i),
    fun _ => inferInstance,
    fun _ => inferInstance,
    fun _ => inferInstance,
    hS'_simp, hS'_dist, hS'_fin,
    L, ⟨e⟩⟩

end RepresentationTheory.Auxiliary.MutualCentralizers

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Auxiliary.MutualCentralizers.Auxiliary.statement016575 := _root_.RepresentationTheory.Auxiliary.MutualCentralizers.exists_auxiliarySpace_decomposition_with_compatibility

attribute [source_ref "Chapter5/Theorem5.18.4" (role := supporting)] _root_.RepresentationTheory.Auxiliary.MutualCentralizers.Auxiliary.statement016575
