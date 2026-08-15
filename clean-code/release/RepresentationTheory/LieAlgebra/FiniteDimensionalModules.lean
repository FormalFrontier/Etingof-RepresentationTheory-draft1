/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import RepresentationTheory.LieAlgebra.Sl2Representations
import RepresentationTheory.Alignment.Attribute

/-! # Finite-dimensional modules over a Lie algebra -/

open scoped Matrix
open LieModule Module

namespace RepresentationTheory.LieAlgebra.FiniteDimensionalModules

attribute [local instance] LieRing.ofAssociativeRing

/-- Lie representations on a module are equivalent to algebra representations of the universal enveloping algebra. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
def lieHomEquivEnvelopingAlgHom (V : Type*) [AddCommGroup V] [Module ℂ V] :
    (RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) ≃
      (UniversalEnvelopingAlgebra ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₐ[ℂ] Module.End ℂ V) :=
  UniversalEnvelopingAlgebra.lift ℂ

/-- A submodule is invariant under a Lie action exactly when it is invariant under the induced universal-enveloping-algebra action. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := supporting)]
theorem invariant_iff_enveloping_invariant
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) (W : Submodule ℂ V) :
    (∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), v ∈ W → ρ x v ∈ W) ↔
      (∀ (u : UniversalEnvelopingAlgebra ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), v ∈ W →
        UniversalEnvelopingAlgebra.lift ℂ ρ u v ∈ W) := by
  constructor
  · intro h
    let S : Subalgebra ℂ (Module.End ℂ V) :=
      { carrier := {g | ∀ v, v ∈ W → g v ∈ W}
        zero_mem' := fun _ _ => by simp
        add_mem' := fun hf hg v hv => W.add_mem (hf v hv) (hg v hv)
        one_mem' := fun _ hv => by simpa using hv
        mul_mem' := fun hf hg v hv => hf _ (hg v hv)
        algebraMap_mem' := fun c v hv => by
          simpa [Algebra.algebraMap_eq_smul_one] using W.smul_mem c hv }
    let ρS : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ S :=
      { toFun := fun x => ⟨ρ x, h x⟩
        map_add' := fun x y => by ext v; simp
        map_smul' := fun c x => by ext v; simp
        map_lie' := by
          intro x y
          exact Subtype.ext (ρ.map_lie x y) }
    have hlift :
        S.val.comp (UniversalEnvelopingAlgebra.lift ℂ ρS) =
          UniversalEnvelopingAlgebra.lift ℂ ρ := by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x v
      simp [ρS]
    intro u v hv
    rw [← hlift]
    exact (UniversalEnvelopingAlgebra.lift ℂ ρS u).property v hv
  · intro h x v hv
    simpa using h (UniversalEnvelopingAlgebra.ι ℂ x) v hv

/-- A linear map intertwines two Lie actions exactly when it intertwines their induced universal-enveloping-algebra actions. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := supporting)]
theorem intertwines_iff_enveloping_intertwines
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρV : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) (ρW : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ W) (f : V →ₗ[ℂ] W) :
    (∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), f (ρV x v) = ρW x (f v)) ↔
      (∀ (u : UniversalEnvelopingAlgebra ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V),
        f (UniversalEnvelopingAlgebra.lift ℂ ρV u v) =
          UniversalEnvelopingAlgebra.lift ℂ ρW u (f v)) := by
  constructor
  · intro h
    let S : Subalgebra ℂ (Module.End ℂ V × Module.End ℂ W) :=
      { carrier := {g | ∀ v, f (g.1 v) = g.2 (f v)}
        zero_mem' := fun v => by simp
        add_mem' := fun ha hb v => by simp [ha v, hb v]
        one_mem' := fun v => by simp
        mul_mem' := by
          intro a b ha hb v
          calc
            f ((a * b).1 v) = f (a.1 (b.1 v)) := rfl
            _ = a.2 (f (b.1 v)) := ha _
            _ = a.2 (b.2 (f v)) := congrArg a.2 (hb v)
            _ = (a * b).2 (f v) := rfl
        algebraMap_mem' := fun c v => by simp [map_smul] }
    let ρS : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ S :=
      { toFun := fun x => ⟨(ρV x, ρW x), h x⟩
        map_add' := fun x y => by ext v <;> simp
        map_smul' := fun c x => by ext v <;> simp
        map_lie' := by
          intro x y
          exact Subtype.ext (Prod.ext (ρV.map_lie x y) (ρW.map_lie x y)) }
    have hlift :
        S.val.comp (UniversalEnvelopingAlgebra.lift ℂ ρS) =
          (UniversalEnvelopingAlgebra.lift ℂ ρV).prod
            (UniversalEnvelopingAlgebra.lift ℂ ρW) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x v <;> simp [ρS]
    intro u v
    have hprop := (UniversalEnvelopingAlgebra.lift ℂ ρS u).property v
    rw [show ((UniversalEnvelopingAlgebra.lift ℂ ρS u : S) :
        Module.End ℂ V × Module.End ℂ W) =
          (UniversalEnvelopingAlgebra.lift ℂ ρV u,
            UniversalEnvelopingAlgebra.lift ℂ ρW u) from DFunLike.congr_fun hlift u] at hprop
    exact hprop
  · intro h x v
    simpa using h (UniversalEnvelopingAlgebra.ι ℂ x) v

section PrimitiveVectorTheory

open RepresentationTheory.LieAlgebra.Sl2Representations

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]

private lemma exists_highest_eigenvalue [Nontrivial V] :
    ∃ μ : ℂ, (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement).HasEigenvalue μ ∧
    ¬(toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement).HasEigenvalue (μ + 2) := by
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement)
  by_contra h_all
  push Not at h_all
  have h_chain : ∀ n : ℕ, (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement).HasEigenvalue (μ₀ + 2 * n) := by
    intro n; induction n with
    | zero => simpa using hμ₀
    | succ n ih =>
      have := h_all _ ih
      convert this using 1; push_cast; ring
  have h_inj : Function.Injective (fun n : ℕ ↦ μ₀ + 2 * (n : ℂ)) := by
    intro a b hab
    have h1 : 2 * (a : ℂ) = 2 * (b : ℂ) := add_left_cancel hab
    have h2 : (a : ℂ) = (b : ℂ) := mul_left_cancel₀ (two_ne_zero) h1
    exact_mod_cast h2
  have h_li := Module.End.eigenvectors_linearIndependent' (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement)
    (fun n : ℕ ↦ μ₀ + 2 * (n : ℂ)) h_inj
    (fun n ↦ (h_chain n).exists_hasEigenvector.choose)
    (fun n ↦ (h_chain n).exists_hasEigenvector.choose_spec)
  exact Module.Finite.not_linearIndependent_of_infinite _ h_li

private lemma exists_primitiveVector [Nontrivial V] :
    ∃ (v : V) (μ : ℂ), isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith v μ := by
  obtain ⟨μ, hμ, hμ2⟩ := exists_highest_eigenvalue (V := V)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨v, μ, ?_⟩
  constructor
  · exact hv.2
  · exact Module.End.mem_eigenspace_iff.mp hv.1
  ·
    by_contra he_ne
    apply hμ2
    have hmem : ⁅sl2_e, v⁆ ∈ (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement).eigenspace (μ + 2) := by
      rw [Module.End.mem_eigenspace_iff]
      change ⁅sl2_h, ⁅sl2_e, v⁆⁆ = (μ + 2) • ⁅sl2_e, v⁆
      have hv_eq : ⁅sl2_h, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
      calc ⁅sl2_h, ⁅sl2_e, v⁆⁆
          = ⁅⁅sl2_h, sl2_e⁆, v⁆ + ⁅sl2_e, ⁅sl2_h, v⁆⁆ := leibniz_lie ..
        _ = ⁅(2 : ℕ) • raisingElement, v⁆ + ⁅sl2_e, μ • v⁆ := by
            rw [isSl2Triple_weight_raising_lowering.lie_h_e_nsmul, hv_eq]
        _ = (2 : ℕ) • ⁅sl2_e, v⁆ + μ • ⁅sl2_e, v⁆ := by
            rw [nsmul_lie, lie_smul]
        _ = (μ + 2) • ⁅sl2_e, v⁆ := by
            rw [← Nat.cast_smul_eq_nsmul ℂ, ← add_smul, add_comm]; norm_cast
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, he_ne⟩

private lemma sl2_decomp (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) :
    x = x.val 0 0 • weightElement + x.val 0 1 • raisingElement + x.val 1 0 • loweringElement := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightElement, raisingElement, loweringElement,
      LieAlgebra.SpecialLinear.val_singleSubSingle,
      LieAlgebra.SpecialLinear.val_single,
      Matrix.single, smul_eq_mul, entry_one_one_eq_neg_entry_zero_zero x, Pi.add_apply, Pi.smul_apply]

private lemma lie_primitiveOrbit_mem (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ))
    (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (k : ℕ) (hk : k ≤ n) :
    ⁅x, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) m⁆ ∈ Submodule.span ℂ
      (Set.range (fun j : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (j : ℕ)) m)) := by
  set S := Submodule.span ℂ
    (Set.range (fun j : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (j : ℕ)) m))

  rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
  refine S.add_mem (S.add_mem (S.smul_mem _ ?_) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
  ·
    rw [P.lie_h_pow_toEnd_f k]
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
  ·
    by_cases hk0 : k = 0
    · subst hk0; simp [P.lie_e, S.zero_mem]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [P.lie_e_pow_succ_toEnd_f k']
      exact S.smul_mem _ (Submodule.subset_span ⟨⟨k', by omega⟩, rfl⟩)
  ·
    have : ⁅sl2_f, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) m⁆ =
        ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) m := by
      rw [pow_succ']; rfl
    rw [this]
    by_cases hk_last : k + 1 ≤ n
    · exact Submodule.subset_span ⟨⟨k + 1, by omega⟩, by simp [pow_succ']⟩
    · have hkn : k = n := by omega
      subst hkn
      rw [P.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)]
      exact S.zero_mem

private lemma primitiveOrbit_lieInvariant (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    let S := Submodule.span ℂ
      (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) m))
    ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), v ∈ S → ⁅x, v⁆ ∈ S := by
  intro S x v hv

  have hle : S ≤ S.comap (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V x) := by
    rw [Submodule.span_le]
    intro w ⟨⟨k, hk⟩, hw⟩
    change (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V x) w ∈ S
    rw [← hw]
    exact lie_primitiveOrbit_mem m n P x k (by omega)
  exact hle hv

private lemma primitiveOrbit_span_eq_top
    (hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    Submodule.span ℂ
      (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) m)) = ⊤ := by
  set S := Submodule.span ℂ
    (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) m))

  let N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
    LieSubmodule.mk S (fun {x v} hv ↦ primitiveOrbit_lieInvariant m n P x v hv)

  have hne : N ≠ ⊥ := by
    intro h
    have : m ∈ (⊥ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
      rw [← h]
      change m ∈ S
      exact Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ n⟩, by simp⟩
    simp only [LieSubmodule.mem_bot] at this
    exact P.ne_zero this
  have htop := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hne
  have : N.toSubmodule = ⊤ := by rw [htop]; rfl
  exact this

omit [FiniteDimensional ℂ V] in

private lemma primitiveOrbit_linearIndependent (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    LinearIndependent ℂ (fun k : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) m) := by

  apply Module.End.eigenvectors_linearIndependent' (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement)
    (fun k : Fin (n + 1) ↦ ((n : ℂ) - 2 * (k : ℕ)))
  ·
    intro a b hab
    have h := hab
    simp only at h

    exact Fin.ext (by exact_mod_cast (mul_left_cancel₀ (two_ne_zero (α := ℂ))
      (neg_injective (add_left_cancel (show (n : ℂ) + -(2 * ↑↑a) = ↑n + -(2 * ↑↑b) from by
        simp only [← sub_eq_add_neg]; exact h)))))
  · intro ⟨k, hk⟩
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact P.lie_h_pow_toEnd_f k
    · exact P.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega)

private noncomputable def primitiveOrbit_basis
    (hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    Basis (Fin (n + 1)) ℂ V :=
  Basis.mk (primitiveOrbit_linearIndependent m n P)
    (primitiveOrbit_span_eq_top hirr m n P ▸ le_refl _)

private lemma primitiveVector_dim
    (hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (m : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    Module.finrank ℂ V = n + 1 := by
  rw [finrank_eq_card_basis (primitiveOrbit_basis hirr m n P), Fintype.card_fin]

private lemma eigenspace_eq_bot_of_not_weight
    (hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (m₀ : V) (n : ℕ)
    (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m₀ (n : ℂ))
    (mu : ℂ) (hmu : ∀ k : Fin (n + 1), mu ≠ (n : ℂ) - 2 * ↑k.val) :
    (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement).eigenspace mu = ⊥ := by
  by_contra h_ne
  simp only [Submodule.eq_bot_iff, not_forall, exists_prop] at h_ne
  obtain ⟨v, hv_mem, hv_ne⟩ := h_ne

  have hdim := primitiveVector_dim hirr m₀ n P
  have hli := Module.End.eigenvectors_linearIndependent' (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement)
    (fun i : Option (Fin (n + 1)) => match i with | none => mu | some k => (n : ℂ) - 2 * ↑k.val)
    (by
      intro a b hab; match a, b with
      | none, none => rfl
      | none, some k => exact absurd hab (hmu k)
      | some k, none => exact absurd hab.symm (hmu k)
      | some a, some b =>
        congr 1; ext; exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := ℂ))
          (neg_injective (add_left_cancel (show (n : ℂ) + -(2 * ↑↑a) = ↑n + -(2 * ↑↑b) from by
            simp only [← sub_eq_add_neg]; exact hab))))
    (fun i => match i with
      | none => v
      | some k => ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) m₀)
    (fun i => match i with
      | none => ⟨hv_mem, hv_ne⟩
      | some k =>
        ⟨Module.End.mem_eigenspace_iff.mpr (P.lie_h_pow_toEnd_f k),
         P.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega)⟩)
  have : Fintype.card (Option (Fin (n + 1))) ≤ finrank ℂ V :=
    hli.fintype_card_le_finrank
  simp [Fintype.card_option, hdim] at this

omit [FiniteDimensional ℂ V] in

private lemma h_comm_pow_f (k : ℕ) (u : V) :
    ⁅sl2_h, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u⁆ =
    ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) ⁅sl2_h, u⁆ -
    (2 * (k : ℂ)) • (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>

    have step1 : ⁅sl2_h, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) u⁆ =
        ⁅⁅sl2_h, sl2_f⁆, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u⁆ +
        ⁅sl2_f, ⁅sl2_h, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u⁆⁆ := by
      rw [pow_succ', Module.End.mul_apply]; exact leibniz_lie ..
    rw [step1, isSl2Triple_weight_raising_lowering.lie_h_f_nsmul, ih, lie_sub, lie_smul, neg_lie, nsmul_lie]
    simp only [pow_succ', Module.End.mul_apply, ← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_ofNat, Nat.cast_succ,
      show ∀ x : V, ⁅sl2_f, x⁆ = (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) x from fun _ => rfl]
    rw [show (2 : ℂ) * ((k : ℂ) + 1) = 2 * (k : ℂ) + 2 from by ring, add_smul]
    abel

omit [FiniteDimensional ℂ V] in

private lemma e_f_pow_succ_comm (k : ℕ) (u : V) :
    ⁅sl2_e, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) u⁆ =
    ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) ⁅sl2_e, u⁆ +
    ((k + 1 : ℂ)) • (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) ⁅sl2_h, u⁆ -
    (k : ℂ) • (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u)) := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, Nat.cast_zero, zero_add, one_smul, zero_smul, sub_zero]

    change ⁅sl2_e, ⁅sl2_f, u⁆⁆ = ⁅sl2_f, ⁅sl2_e, u⁆⁆ + ⁅sl2_h, u⁆
    rw [leibniz_lie, isSl2Triple_weight_raising_lowering.bracket_raising_lowering, add_comm]
  | succ k ih =>

    have step1 : ⁅sl2_e, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 2)) u⁆ =
        ⁅⁅sl2_e, sl2_f⁆, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) u⁆ +
        ⁅sl2_f, ⁅sl2_e, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) u⁆⁆ := by
      rw [show (k + 2) = (k + 1) + 1 from by omega, pow_succ', Module.End.mul_apply]
      exact leibniz_lie ..
    rw [step1, isSl2Triple_weight_raising_lowering.bracket_raising_lowering, ih, h_comm_pow_f (k + 1) u,
      lie_add, lie_smul, lie_sub, lie_smul]
    simp only [pow_succ', Module.End.mul_apply, Nat.cast_succ,
      show ∀ x : V, ⁅sl2_f, x⁆ = (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) x from fun _ => rfl]
    module

private noncomputable def sl2_irrep_equiv
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W]
    (hirrV : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V)
    (hirrW : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W)
    (mV : V) (mW : W) (n : ℕ)
    (PV : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith mV (n : ℂ))
    (PW : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith mW (n : ℂ)) :
    V ≃ₗ⁅ℂ, sl2⁆ W := by

  let bV := primitiveOrbit_basis hirrV mV n PV
  let bW := primitiveOrbit_basis hirrW mW n PW
  let φ : V ≃ₗ[ℂ] W := bV.equiv bW (Equiv.refl _)

  exact {
    toLinearMap := φ.toLinearMap
    map_lie' := by
      intro x v

      have hφ : ∀ i, φ (bV i) = bW i := fun i => by simp [φ, Basis.equiv_apply]

      have hφ_pow : ∀ k (hk : k < n + 1),
          φ (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) mV) = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W loweringElement) ^ k) mW := by
        intro k hk
        have h1 : bV ⟨k, hk⟩ = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) mV := Basis.mk_apply _ _ _
        have h2 : bW ⟨k, hk⟩ = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W loweringElement) ^ k) mW := Basis.mk_apply _ _ _
        rw [← h1, hφ, h2]

      have h_key : ∀ (k : ℕ) (hk : k < n + 1),
          φ (⁅x, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) mV⁆) =
          ⁅x, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W loweringElement) ^ k) mW⁆ := by
        intro k hk

        rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie,
            map_add, map_add, map_smul, map_smul, map_smul,
            sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
        focus congr 1 <;> congr 1
        ·
          rw [PV.lie_h_pow_toEnd_f k, PW.lie_h_pow_toEnd_f k, map_smul, hφ_pow k hk]
        ·
          by_cases hk0 : k = 0
          · subst hk0; simp [PV.lie_e, PW.lie_e]
          · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            rw [PV.lie_e_pow_succ_toEnd_f k', PW.lie_e_pow_succ_toEnd_f k', map_smul,
                hφ_pow k' (by omega)]
        ·
          have hfV : ⁅sl2_f, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) mV⁆ =
              ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k + 1)) mV := by rw [pow_succ']; rfl
          have hfW : ⁅sl2_f, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W loweringElement) ^ k) mW⁆ =
              ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W loweringElement) ^ (k + 1)) mW := by rw [pow_succ']; rfl
          rw [hfV, hfW]
          by_cases hk_last : k + 1 ≤ n
          · rw [hφ_pow (k + 1) (by omega)]
          · have hkn : k + 1 = n + 1 := by omega
            rw [hkn, PV.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast),
                PW.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast), map_zero]

      change φ (⁅x, v⁆) = ⁅x, φ v⁆
      rw [show v = ∑ i, bV.repr v i • bV i from (bV.sum_repr v).symm]
      simp only [lie_sum, lie_smul, map_sum, map_smul]
      congr 1; ext ⟨k, hk⟩; congr 1

      have hbV : bV ⟨k, hk⟩ = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) mV := by
        change primitiveOrbit_basis hirrV mV n PV ⟨k, hk⟩ = _
        exact Basis.mk_apply _ _ _
      rw [hbV, h_key k hk, ← hφ_pow k hk]
    invFun := φ.symm
    left_inv := φ.symm_apply_apply
    right_inv := φ.apply_symm_apply
  }

end PrimitiveVectorTheory

/-- For every positive rank there exists an irreducible module of that rank, unique up to Lie-module equivalence. -/
theorem existsUniqueIrreducibleOfFinrank (d : ℕ+) :

    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
       (_ : LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (_ : LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V),
       Module.finrank ℂ V = d ∧ LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) ∧

    (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
       [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
       [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
       [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
       Module.finrank ℂ V = d → LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V →
       Module.finrank ℂ W = d → LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W →
       Nonempty (V ≃ₗ⁅ℂ, sl2⁆ W)) := by
  constructor
  ·
    have hd : NeZero (d : ℕ) := ⟨PNat.ne_zero d⟩
    exact ⟨Fin d → ℂ, inferInstance, inferInstance,
      RepresentationTheory.LieAlgebra.Sl2Representations.lieRingModule_finFunction d, RepresentationTheory.LieAlgebra.Sl2Representations.lieModule_finFunction d,
      RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction d, RepresentationTheory.LieAlgebra.Sl2Representations.isIrreducible_finFunction d⟩
  ·
    intro V W _ _ _ _ _ _ _ _ _ _  hdV hirrV hdW hirrW
    have hntV : Nontrivial V := by
      rw [← finrank_pos_iff (R := ℂ), hdV]; exact d.pos
    have hntW : Nontrivial W := by
      rw [← finrank_pos_iff (R := ℂ), hdW]; exact d.pos

    obtain ⟨mV, μV, PV⟩ := exists_primitiveVector (V := V)
    obtain ⟨mW, μW, PW⟩ := exists_primitiveVector (V := W)

    obtain ⟨nV, hnV⟩ := PV.exists_nat
    obtain ⟨nW, hnW⟩ := PW.exists_nat

    rw [hnV] at PV; rw [hnW] at PW

    have hdimV := primitiveVector_dim hirrV mV nV PV
    have hdimW := primitiveVector_dim hirrW mW nW PW
    have hneq : nV = nW := by omega
    subst hneq
    exact ⟨sl2_irrep_equiv hirrV hirrW mV mW nV PV PW⟩

/-- For every positive natural number there exists an irreducible module having that finite rank. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
theorem exists_irreducible_of_finrank (d : ℕ+) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (_ : LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V),
      Module.finrank ℂ V = d ∧ LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
  (existsUniqueIrreducibleOfFinrank d).1

/-- Two irreducible modules of the same prescribed positive rank are nonemptily Lie-module equivalent. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
theorem nonempty_equiv_of_irreducible_finrank_eq (d : ℕ+) :
    ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
      [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
      Module.finrank ℂ V = d → LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V →
      Module.finrank ℂ W = d → LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W →
      Nonempty (V ≃ₗ⁅ℂ, sl2⁆ W) :=
  (existsUniqueIrreducibleOfFinrank d).2

private noncomputable def binaryExponent (d : ℕ+) (i : Fin d) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ((d : ℕ) - 1 - (i : ℕ)) + Finsupp.single 1 (i : ℕ)

private lemma binaryExponent_degree (d : ℕ+) (i : Fin d) :
    (binaryExponent d i).degree = (d : ℕ) - 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp [binaryExponent]
  omega

private noncomputable def binaryExponentEquiv (d : ℕ+) :
    Fin d ≃ {m : Fin 2 →₀ ℕ | m.degree = (d : ℕ) - 1} where
  toFun i := ⟨binaryExponent d i, binaryExponent_degree d i⟩
  invFun m := ⟨m.1 1, by
    have hsum := m.2
    change m.1.degree = (d : ℕ) - 1 at hsum
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hsum
    have hd : 0 < (d : ℕ) := d.pos
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp [binaryExponent]
  right_inv m := by
    apply Subtype.ext
    apply Finsupp.ext
    intro j
    fin_cases j
    · have hsum := m.2
      change m.1.degree = (d : ℕ) - 1 at hsum
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hsum
      simp [binaryExponent]
      omega
    · simp [binaryExponent]

private noncomputable def binaryHomogeneousBasis (d : ℕ+) :
    Module.Basis {m : Fin 2 →₀ ℕ | m.degree = (d : ℕ) - 1} ℂ
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :=
  (MvPolynomial.basisRestrictSupport ℂ _).map
    (LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) ℂ
        ((d : ℕ) - 1)).symm)

private noncomputable def binaryPolynomialEquiv (d : ℕ+) :
    (Fin d → ℂ) ≃ₗ[ℂ]
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :=
  (Pi.basisFun ℂ (Fin d)).equiv (binaryHomogeneousBasis d) (binaryExponentEquiv d)

private lemma binaryPolynomialEquiv_basis (d : ℕ+) (i : Fin d) :
    ((binaryPolynomialEquiv d (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i) :
      MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :
        MvPolynomial (Fin 2) ℂ) = MvPolynomial.monomial (binaryExponent d i) 1 := by
  rw [show RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i = (Pi.basisFun ℂ (Fin d)) i by
    simp [RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector]]
  rw [binaryPolynomialEquiv, Module.Basis.equiv_apply]
  rw [binaryHomogeneousBasis, Module.Basis.map_apply]
  change (((MvPolynomial.basisRestrictSupport ℂ
    {m : Fin 2 →₀ ℕ | m.degree = (d : ℕ) - 1}) ((binaryExponentEquiv d) i) :
      MvPolynomial.restrictSupport ℂ _) : MvPolynomial (Fin 2) ℂ) = _
  have hb : MvPolynomial.basisRestrictSupport ℂ _ ((binaryExponentEquiv d) i) =
      (MvPolynomial.basisRestrictSupport ℂ _).repr.symm
        (Finsupp.single ((binaryExponentEquiv d) i) 1) := by
    apply (MvPolynomial.basisRestrictSupport ℂ _).repr.injective
    rw [Module.Basis.repr_self, LinearEquiv.apply_symm_apply]
  rw [hb]
  ext m
  simp [MvPolynomial.basisRestrictSupport, AddMonoidAlgebra.supportedEquivFinsupp,
    MvPolynomial.coeff, AddMonoidAlgebra.coeff_single]
  change _ = MvPolynomial.coeff m (MvPolynomial.monomial (binaryExponent d i) 1)
  rw [MvPolynomial.coeff_monomial]
  rw [show ↑((binaryExponentEquiv d) i) = binaryExponent d i by rfl]
  exact Finsupp.single_apply

private noncomputable def polynomialMap (d : ℕ+) :
    (Fin d → ℂ) →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (Submodule.subtype _).comp (binaryPolynomialEquiv d).toLinearMap

private noncomputable def xPderiv (x deriv : Fin 2) :
    MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (LinearMap.mulLeft ℂ (MvPolynomial.X x)).comp
    (MvPolynomial.pderiv deriv).toLinearMap

private lemma polynomialMap_basis (d : ℕ+) (i : Fin d) :
    polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i) =
      MvPolynomial.monomial (binaryExponent d i) 1 := by
  exact binaryPolynomialEquiv_basis d i

private lemma h_action_basis (d : ℕ+) (i : Fin d) :
    polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.weightElement
      (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) =
      (xPderiv 0 0 - xPderiv 1 1)
        (polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) := by
  rw [← RepresentationTheory.LieAlgebra.Sl2Representations.bracket_eq_representation_apply,
    RepresentationTheory.LieAlgebra.Sl2Representations.bracket_weight_coordinateVector]
  simp only [polynomialMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Submodule.coe_subtype, map_smul, xPderiv, LinearMap.sub_apply]
  rw [binaryPolynomialEquiv_basis,
    LinearMap.mulLeft_apply, LinearMap.mulLeft_apply]
  have hx0 : MvPolynomial.X (0 : Fin 2) *
        (MvPolynomial.pderiv (0 : Fin 2)).toLinearMap
          (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) =
      (binaryExponent d i) 0 •
        MvPolynomial.monomial (binaryExponent d i) (1 : ℂ) :=
    MvPolynomial.X_mul_pderiv_monomial
  have hx1 : MvPolynomial.X (1 : Fin 2) *
        (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
          (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) =
      (binaryExponent d i) 1 •
        MvPolynomial.monomial (binaryExponent d i) (1 : ℂ) :=
    MvPolynomial.X_mul_pderiv_monomial
  rw [hx0, hx1]
  have hd1 : 1 ≤ (d : ℕ) := d.pos
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  simp [binaryExponent]
  push_cast [Nat.cast_sub (by omega : (i : ℕ) ≤ (d : ℕ) - 1)]
  rw [Nat.cast_sub hd1]
  ring

private lemma e_action_basis (d : ℕ+) (i : Fin d) :
    polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement
      (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) =
      xPderiv 0 1 (polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) := by
  rw [← RepresentationTheory.LieAlgebra.Sl2Representations.bracket_eq_representation_apply,
    RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_coordinateVector d (i : ℕ) i.isLt]
  simp only [polynomialMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Submodule.coe_subtype, map_smul, xPderiv]
  rw [binaryPolynomialEquiv_basis, binaryPolynomialEquiv_basis,
    LinearMap.mulLeft_apply]
  have hp : (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
        (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) =
      MvPolynomial.monomial (binaryExponent d i - Finsupp.single 1 1)
        ((1 : ℂ) * ((binaryExponent d i) 1 : ℕ)) := by
    change (MvPolynomial.pderiv (1 : Fin 2))
      (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) = _
    rw [MvPolynomial.pderiv_monomial]
  rw [hp]
  change (i : ℂ) • MvPolynomial.monomial
      (binaryExponent d ⟨(i : ℕ) - 1, by omega⟩) 1 =
    MvPolynomial.monomial (Finsupp.single 0 1) 1 *
      MvPolynomial.monomial
        (binaryExponent d i - Finsupp.single 1 1)
        ((1 : ℂ) * ((binaryExponent d i) 1 : ℕ))
  rw [MvPolynomial.monomial_mul]
  by_cases hi0 : (i : ℕ) = 0
  · simp [binaryExponent, hi0]
  · have hexp : Finsupp.single (0 : Fin 2) 1 +
        (binaryExponent d i - Finsupp.single (1 : Fin 2) 1) =
        binaryExponent d ⟨(i : ℕ) - 1, by omega⟩ := by
      apply Finsupp.ext
      intro j
      fin_cases j
      · simp [binaryExponent]
        omega
      · simp [binaryExponent]
    rw [hexp]
    ext m
    simp [binaryExponent]

private lemma f_action_basis (d : ℕ+) (i : Fin d) :
    polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement
      (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) =
      xPderiv 1 0 (polynomialMap d (RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d i)) := by
  by_cases htop : (i : ℕ) + 1 = (d : ℕ)
  · rw [← RepresentationTheory.LieAlgebra.Sl2Representations.bracket_eq_representation_apply,
      RepresentationTheory.LieAlgebra.Sl2Representations.bracket_lowering_coordinateVector_eq_zero d (i : ℕ) i.isLt htop]
    simp only [map_zero, xPderiv, polynomialMap, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, Submodule.coe_subtype]
    rw [binaryPolynomialEquiv_basis, LinearMap.mulLeft_apply]
    have hp : (MvPolynomial.pderiv (0 : Fin 2)).toLinearMap
          (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) =
        MvPolynomial.monomial (binaryExponent d i - Finsupp.single 0 1)
          ((1 : ℂ) * ((binaryExponent d i) 0 : ℕ)) := by
      change (MvPolynomial.pderiv (0 : Fin 2))
        (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) = _
      rw [MvPolynomial.pderiv_monomial]
    rw [hp]
    simp [binaryExponent, htop]
  · have hbelow : (i : ℕ) + 1 < (d : ℕ) := by omega
    rw [← RepresentationTheory.LieAlgebra.Sl2Representations.bracket_eq_representation_apply,
      RepresentationTheory.LieAlgebra.Sl2Representations.bracket_lowering_coordinateVector d (i : ℕ) hbelow]
    simp only [polynomialMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Submodule.coe_subtype, map_smul, xPderiv]
    rw [binaryPolynomialEquiv_basis, binaryPolynomialEquiv_basis,
      LinearMap.mulLeft_apply]
    have hp : (MvPolynomial.pderiv (0 : Fin 2)).toLinearMap
          (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) =
        MvPolynomial.monomial (binaryExponent d i - Finsupp.single 0 1)
          ((1 : ℂ) * ((binaryExponent d i) 0 : ℕ)) := by
      change (MvPolynomial.pderiv (0 : Fin 2))
        (MvPolynomial.monomial (binaryExponent d i) (1 : ℂ)) = _
      rw [MvPolynomial.pderiv_monomial]
    rw [hp]
    change ((d : ℂ) - 1 - (i : ℕ)) •
        MvPolynomial.monomial (binaryExponent d ⟨(i : ℕ) + 1, hbelow⟩) 1 =
      MvPolynomial.monomial (Finsupp.single 1 1) 1 *
        MvPolynomial.monomial
          (binaryExponent d i - Finsupp.single 0 1)
          ((1 : ℂ) * ((binaryExponent d i) 0 : ℕ))
    rw [MvPolynomial.monomial_mul]
    have hexp : Finsupp.single (1 : Fin 2) 1 +
        (binaryExponent d i - Finsupp.single (0 : Fin 2) 1) =
        binaryExponent d ⟨(i : ℕ) + 1, hbelow⟩ := by
      apply Finsupp.ext
      intro j
      fin_cases j <;> simp [binaryExponent] <;> omega
    rw [hexp]
    ext m
    simp [binaryExponent]
    push_cast [Nat.cast_sub (by omega : (i : ℕ) ≤ (d : ℕ) - 1),
      Nat.cast_sub (d.pos : 1 ≤ (d : ℕ))]
    ring

private lemma h_action (d : ℕ+) :
    (polynomialMap d).comp
        (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.weightElement) =
      (xPderiv 0 0 - xPderiv 1 1).comp (polynomialMap d) := by
  apply (Pi.basisFun ℂ (Fin d)).ext
  intro i
  simpa [LinearMap.comp_apply, RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector] using h_action_basis d i

private lemma e_action (d : ℕ+) :
    (polynomialMap d).comp
        (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement) =
      (xPderiv 0 1).comp (polynomialMap d) := by
  apply (Pi.basisFun ℂ (Fin d)).ext
  intro i
  simpa [LinearMap.comp_apply, RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector] using e_action_basis d i

private lemma f_action (d : ℕ+) :
    (polynomialMap d).comp
        (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement) =
      (xPderiv 1 0).comp (polynomialMap d) := by
  apply (Pi.basisFun ℂ (Fin d)).ext
  intro i
  simpa [LinearMap.comp_apply, RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector] using f_action_basis d i

/-- There is a polynomial realization in which the three specified operators act by the displayed differential expressions. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
theorem exists_polynomialModel (d : ℕ+) :
    ∃ Φ : (Fin d → ℂ) ≃ₗ[ℂ]
        ↑(MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)),
      ∀ v : Fin d → ℂ,
        ((Φ (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.weightElement v) :
            MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :
              MvPolynomial (Fin 2) ℂ) =
            MvPolynomial.X (0 : Fin 2) *
                MvPolynomial.pderiv (0 : Fin 2) (Φ v : MvPolynomial (Fin 2) ℂ) -
              MvPolynomial.X (1 : Fin 2) *
                MvPolynomial.pderiv (1 : Fin 2) (Φ v : MvPolynomial (Fin 2) ℂ) ∧
        ((Φ (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement v) :
            MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :
              MvPolynomial (Fin 2) ℂ) =
            MvPolynomial.X (0 : Fin 2) *
              MvPolynomial.pderiv (1 : Fin 2) (Φ v : MvPolynomial (Fin 2) ℂ) ∧
        ((Φ (RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement v) :
            MvPolynomial.homogeneousSubmodule (Fin 2) ℂ ((d : ℕ) - 1)) :
              MvPolynomial (Fin 2) ℂ) =
            MvPolynomial.X (1 : Fin 2) *
              MvPolynomial.pderiv (0 : Fin 2) (Φ v : MvPolynomial (Fin 2) ℂ) := by
  refine ⟨binaryPolynomialEquiv d, ?_⟩
  intro v
  have hh := LinearMap.congr_fun (h_action d) v
  have he := LinearMap.congr_fun (e_action d) v
  have hf := LinearMap.congr_fun (f_action d) v
  simpa [polynomialMap, xPderiv, LinearMap.comp_apply, LinearMap.mulLeft_apply] using
    And.intro hh (And.intro he hf)

/-- An irreducible module of rank one more than a natural number is nonemptily equivalent to the corresponding finite function module. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem nonempty_lieModuleEquiv_finFunction_of_irreducible (lam : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (hdimV : Module.finrank ℂ V = lam + 1)
    (hirrV : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) :
    Nonempty (V ≃ₗ⁅ℂ, sl2⁆ (Fin (lam + 1) → ℂ)) := by

  haveI : NeZero (lam + 1) := ⟨Nat.succ_ne_zero lam⟩
  have hirrW : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (Fin (lam + 1) → ℂ) :=
    RepresentationTheory.LieAlgebra.Sl2Representations.isIrreducible_finFunction (lam + 1)
  have hdimW : Module.finrank ℂ (Fin (lam + 1) → ℂ) = lam + 1 :=
    RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction (lam + 1)
  have hntV : Nontrivial V := by
    rw [← finrank_pos_iff (R := ℂ), hdimV]; omega
  have hntW : Nontrivial (Fin (lam + 1) → ℂ) := by
    rw [← finrank_pos_iff (R := ℂ), hdimW]; omega

  obtain ⟨mV, μV, PV⟩ := exists_primitiveVector (V := V)
  obtain ⟨mW, μW, PW⟩ :=
    exists_primitiveVector (V := Fin (lam + 1) → ℂ)
  obtain ⟨nV, hnV⟩ := PV.exists_nat
  obtain ⟨nW, hnW⟩ := PW.exists_nat
  rw [hnV] at PV; rw [hnW] at PW

  have hdV := primitiveVector_dim hirrV mV nV PV
  have hdW := primitiveVector_dim hirrW mW nW PW
  have hnVeq : nV = lam := by omega
  have hnWeq : nW = lam := by omega
  exact ⟨sl2_irrep_equiv hirrV hirrW mV mW lam (hnVeq ▸ PV) (hnWeq ▸ PW)⟩

section Casimir

open RepresentationTheory.LieAlgebra.Sl2Representations

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]

/-- The distinguished linear endomorphism associated with the specified Lie-module structure. -/
@[nolint defsWithUnderscore]
noncomputable def distinguishedModuleEndomorphism : Module.End ℂ V :=
  (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement) ^ 2 +
  2 • ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement) * (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement)) +
  2 • ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) * (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement))

private lemma end_HE :
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement =
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement + 2 • toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement := by
  have := (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).map_lie weightElement raisingElement
  rw [isSl2Triple_weight_raising_lowering.lie_h_e_nsmul, map_nsmul, LieRing.of_associative_ring_bracket] at this

  rw [eq_comm, sub_eq_iff_eq_add, add_comm] at this; exact this

private lemma end_HF :
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement =
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement - 2 • toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement := by
  have := (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).map_lie weightElement loweringElement
  rw [isSl2Triple_weight_raising_lowering.lie_h_f_nsmul, map_neg, map_nsmul, LieRing.of_associative_ring_bracket] at this

  rw [eq_comm, sub_eq_iff_eq_add] at this

  rw [this]; abel

private lemma end_EF :
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement =
    toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement + toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement := by
  have := (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).map_lie raisingElement loweringElement
  rw [bracket_raising_lowering, LieRing.of_associative_ring_bracket] at this

  rw [eq_comm, sub_eq_iff_eq_add, add_comm] at this; exact this

private lemma sl2_casimir_eq :
    distinguishedModuleEndomorphism (V := V) = (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement) ^ 2 +
    2 • toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement + 4 • (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement * toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement) := by
  unfold distinguishedModuleEndomorphism
  have hEF := end_EF (V := V)
  simp only [sq]
  rw [hEF]
  simp only [smul_add]
  abel

private lemma sl2_casimir_comm (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) :
    distinguishedModuleEndomorphism (V := V) ∘ₗ (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V x) =
    (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V x) ∘ₗ distinguishedModuleEndomorphism := by
  set H := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement; set E := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement; set F := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement
  have hHE := end_HE (V := V)
  have hHF := end_HF (V := V)
  have hEF := end_EF (V := V)

  have pHE : ∀ w, H (E w) = E (H w) + 2 • E w := LinearMap.congr_fun hHE
  have pHF : ∀ w, H (F w) = F (H w) - 2 • F w := LinearMap.congr_fun hHF
  have pEF : ∀ w, E (F w) = F (E w) + H w := LinearMap.congr_fun hEF

  rw [sl2_decomp x]
  simp only [map_add, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp]

  have casimir_rw : ∀ (X : Module.End ℂ V), distinguishedModuleEndomorphism ∘ₗ X = X ∘ₗ distinguishedModuleEndomorphism →
      ∀ (c : ℂ), c • (distinguishedModuleEndomorphism ∘ₗ X) = c • (X ∘ₗ distinguishedModuleEndomorphism) :=
    fun _ h c => by rw [h]

  have hComm : ∀ X, X = H ∨ X = E ∨ X = F → distinguishedModuleEndomorphism ∘ₗ X = X ∘ₗ distinguishedModuleEndomorphism := by
    intro X hX; ext v; unfold distinguishedModuleEndomorphism
    simp only [sq, Module.End.mul_eq_comp, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply,
      show toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement = H from rfl, show toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement = E from rfl,
      show toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement = F from rfl]

    rcases hX with rfl | rfl | rfl <;> {

      simp only [map_add, map_sub, map_nsmul, pHE, pHF, pEF]
      module }
  congr 1
  · congr 1
    · congr 1; exact hComm H (Or.inl rfl)
    · congr 1; exact hComm E (Or.inr (Or.inl rfl))
  · congr 1; exact hComm F (Or.inr (Or.inr rfl))

private lemma casimir_eigenspace_lie_invariant (c₀ : ℂ) :
    ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V),
    v ∈ (distinguishedModuleEndomorphism (V := V)).eigenspace c₀ →
      ⁅x, v⁆ ∈ (distinguishedModuleEndomorphism (V := V)).eigenspace c₀ := by
  intro x v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcomm := sl2_casimir_comm (V := V) x
  have hCxv : distinguishedModuleEndomorphism (V := V) (⁅x, v⁆) = (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V x) (distinguishedModuleEndomorphism v) :=
    LinearMap.congr_fun hcomm v
  rw [hCxv, hv, map_smul, LieModule.toEnd_apply_apply]

private lemma casimir_on_irreducible_scalar
    (hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) [Nontrivial V]
    (m : V) (n : ℕ) (P : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith m (n : ℂ)) :
    distinguishedModuleEndomorphism (V := V) = (n * (n + 2) : ℂ) • (1 : Module.End ℂ V) := by

  set H := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement
  set E := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement
  set F := toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement
  set c := (n * (n + 2) : ℂ)

  have hHm : H m = (n : ℂ) • m := by
    change ⁅sl2_h, m⁆ = (n : ℂ) • m
    exact P.lie_h
  have hEm : E m = 0 := by
    change ⁅sl2_e, m⁆ = 0
    exact P.lie_e

  have hCm : distinguishedModuleEndomorphism (V := V) m = c • m := by
    rw [sl2_casimir_eq]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply]
    rw [hHm, map_smul, hHm, hEm, map_zero, smul_zero]
    simp only [c, smul_smul]
    simp only [add_zero, two_nsmul, ← add_smul]
    congr 1; ring

  have hm_eigen : m ∈ (distinguishedModuleEndomorphism (V := V)).eigenspace c := by
    rw [Module.End.mem_eigenspace_iff]; exact hCm

  let N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
    LieSubmodule.mk ((distinguishedModuleEndomorphism (V := V)).eigenspace c)
      (fun {x v} hv ↦ casimir_eigenspace_lie_invariant c x v hv)
  have hN_ne : N ≠ ⊥ := by
    intro h
    have : m ∈ (⊥ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := h ▸ hm_eigen
    simp only [LieSubmodule.mem_bot] at this
    exact P.ne_zero this

  have hN_top : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN_ne

  ext v
  have hv_in : v ∈ (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := LieSubmodule.mem_top v
  rw [← hN_top] at hv_in
  have hv_eigen := (Module.End.mem_eigenspace_iff.mp hv_in : distinguishedModuleEndomorphism v = c • v)
  simp only [LinearMap.smul_apply]
  exact hv_eigen

end Casimir

section CompleteReducibility

open RepresentationTheory.LieAlgebra.Sl2Representations

private lemma casimir_eigenvalue_injective :
    Function.Injective (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) + 2)) := by
  intro a b hab

  change (a : ℂ) * ((a : ℂ) + 2) = (b : ℂ) * ((b : ℂ) + 2) at hab

  have hab_nat : a * (a + 2) = b * (b + 2) := by
    have h1 : ((a : ℂ) * ((a : ℂ) + 2)) = ((a * (a + 2) : ℕ) : ℂ) := by push_cast; ring
    have h2 : ((b : ℂ) * ((b : ℂ) + 2)) = ((b * (b + 2) : ℕ) : ℂ) := by push_cast; ring
    exact_mod_cast h1 ▸ h2 ▸ hab

  have h1 : a * (a + 2) + 1 = (a + 1) ^ 2 := by ring
  have h2 : b * (b + 2) + 1 = (b + 1) ^ 2 := by ring
  have h3 : (a + 1) ^ 2 = (b + 1) ^ 2 := by omega
  have h4 : a + 1 = b + 1 := Nat.pow_left_injective (by omega) h3
  omega

private lemma sl2_isPerfect : ∀ x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra,
    x ∈ Submodule.span ℂ (Set.range (fun p : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra × RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ↦ ⁅p.1, p.2⁆)) := by
  intro x
  rw [Submodule.mem_span]
  intro S hS

  rw [sl2_decomp x]
  refine S.add_mem (S.add_mem (S.smul_mem _ ?_) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
  ·
    rw [← bracket_raising_lowering]
    exact hS ⟨(raisingElement, loweringElement), rfl⟩
  ·
    have : raisingElement = (1/2 : ℂ) • ⁅sl2_h, sl2_e⁆ := by
      rw [isSl2Triple_weight_raising_lowering.lie_h_e_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      simp [smul_smul]
    rw [this]
    exact S.smul_mem _ (hS ⟨(weightElement, raisingElement), rfl⟩)
  ·
    have : loweringElement = -(1/2 : ℂ) • ⁅sl2_h, sl2_f⁆ := by
      rw [isSl2Triple_weight_raising_lowering.lie_h_f_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      simp [smul_smul, neg_smul, smul_neg]
    rw [this]
    exact S.smul_mem _ (hS ⟨(weightElement, loweringElement), rfl⟩)

private lemma sl2_acts_trivially_of_quotient_and_sub
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V)
    (hN : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : N), ⁅x, (v : V)⁆ = 0)
    (hQ : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), (⁅x, v⁆ : V) ∈ N) :
    ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), ⁅x, v⁆ = 0 := by
  intro x v

  have hbracket : ∀ (y z : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra), ⁅⁅y, z⁆, v⁆ = 0 := by
    intro y z
    have h1 : ⁅y, ⁅z, v⁆⁆ = (0 : V) := by
      have hzv : ⁅z, v⁆ ∈ N := hQ z v
      exact hN y ⟨⁅z, v⁆, hzv⟩
    have h2 : ⁅z, ⁅y, v⁆⁆ = (0 : V) := by
      have hyv : ⁅y, v⁆ ∈ N := hQ y v
      exact hN z ⟨⁅y, v⁆, hyv⟩
    have := leibniz_lie y z v
    rw [h1, h2, add_zero] at this
    exact this.symm

  have hxv_mem : ⁅x, v⁆ ∈ N := hQ x v

  rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]

  have hh : ⁅sl2_h, v⁆ = (0 : V) := by rw [← bracket_raising_lowering]; exact hbracket raisingElement loweringElement

  have he : ⁅sl2_e, v⁆ = (0 : V) := by
    have h2e := hbracket weightElement raisingElement
    rw [isSl2Triple_weight_raising_lowering.lie_h_e_nsmul, nsmul_lie] at h2e
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h2e
    exact h2e.resolve_left (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0))
  have hf : ⁅sl2_f, v⁆ = (0 : V) := by
    have h2f := hbracket weightElement loweringElement
    rw [isSl2Triple_weight_raising_lowering.lie_h_f_nsmul, neg_lie, nsmul_lie, neg_eq_zero] at h2f
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h2f
    exact h2f.resolve_left (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0))
  simp [hh, he, hf]

private lemma sl2_trivial_of_casimir_zero_aux (d : ℕ) :
    ∀ {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
    finrank ℂ W ≤ d →
    (∀ v : W, distinguishedModuleEndomorphism (V := W) v = 0) →
    ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : W), ⁅x, v⁆ = 0 := by
  induction d with
  | zero =>
    intro W _ _ _ _ _ hd hC x v
    haveI : Subsingleton W := by
      by_contra h; rw [not_subsingleton_iff_nontrivial] at h; haveI := h
      exact absurd (Module.finrank_pos (R := ℂ) (M := W)) (not_lt.mpr hd)
    simp [Subsingleton.elim v 0]
  | succ d ih =>
    intro W _ _ _ _ _ hd hC x v
    by_cases hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W
    ·
      haveI : Nontrivial W := (LieSubmodule.nontrivial_iff ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := W)).mp hirr.toNontrivial
      obtain ⟨m, μ, P⟩ := exists_primitiveVector (V := W)
      obtain ⟨n, hn⟩ := P.exists_nat; rw [hn] at P
      have hCscalar := casimir_on_irreducible_scalar hirr m n P
      have hC0 : distinguishedModuleEndomorphism (V := W) = 0 := by ext w; exact hC w

      have hn0 : (n : ℂ) * ((n : ℂ) + 2) = 0 := by
        by_contra hne
        have h1 : (↑n * (↑n + 2) : ℂ) • (1 : Module.End ℂ W) = 0 := by
          rw [← hCscalar, hC0]
        exact (exists_ne (0 : W)).choose_spec
          (LinearMap.congr_fun ((smul_eq_zero.mp h1).resolve_left hne) _)

      have hn_zero : n = 0 := by
        rcases mul_eq_zero.mp hn0 with h1 | h2
        · exact_mod_cast h1
        · exfalso; have h3 : (n : ℂ) + 2 = 0 := h2
          have h4 : (↑(n + 2) : ℂ) = 0 := by push_cast; exact h3
          exact_mod_cast h4
      subst hn_zero

      have hHm : ⁅sl2_h, m⁆ = (0 : W) := by
        have := P.lie_h; simp only [Nat.cast_zero, zero_smul] at this; exact this
      have hEm : ⁅sl2_e, m⁆ = (0 : W) := P.lie_e
      have hFm : ⁅sl2_f, m⁆ = (0 : W) := by
        have h1 := P.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) rfl
        simpa [pow_succ, pow_zero] using h1

      have hxm : ⁅x, m⁆ = (0 : W) := by
        rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie, hHm, hEm, hFm]; simp

      let hbasis := primitiveOrbit_basis hirr m 0 P
      rw [show v = ∑ i : Fin 1, hbasis.repr v i • hbasis i from (hbasis.sum_repr v).symm,
          Fin.sum_univ_one, lie_smul]
      suffices hbasis (0 : Fin 1) = m by rw [this, hxm, smul_zero]
      change primitiveOrbit_basis hirr m 0 P ⟨0, _⟩ = _
      exact Basis.mk_apply _ _ _
    ·
      by_cases htriv : Subsingleton W
      · haveI := htriv; exact Subsingleton.elim _ _
      · rw [not_subsingleton_iff_nontrivial] at htriv

        have : ¬ ∀ a : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W, a = ⊥ ∨ a = ⊤ := by
          intro hall
          exact hirr (LieModule.IsIrreducible.mk (fun N hN => (hall N).resolve_left hN))
        push Not at this
        obtain ⟨N, hNbot, hNtop⟩ := this

        have hN_sub_lt : N.toSubmodule < ⊤ :=
          lt_top_iff_ne_top.mpr (mt (LieSubmodule.toSubmodule_eq_top (N := N)).mp hNtop)
        have hfN : finrank ℂ ↥N.toSubmodule < finrank ℂ W := by
          have := Submodule.finrank_lt_finrank_of_lt hN_sub_lt
          rwa [finrank_top] at this

        have hN_pos : 0 < finrank ℂ ↥N.toSubmodule := by
          have : Nontrivial ↥N := (LieSubmodule.nontrivial_iff_ne_bot ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := W)).mpr hNbot
          exact Module.finrank_pos (R := ℂ)
        have hfN_eq : finrank ℂ ↥N = finrank ℂ ↥N.toSubmodule := rfl
        have hfQ_eq : finrank ℂ (W ⧸ N) = finrank ℂ (W ⧸ N.toSubmodule) := rfl
        have hfQ : finrank ℂ (W ⧸ N.toSubmodule) < finrank ℂ W := by
          have := Submodule.finrank_quotient_add_finrank N.toSubmodule; omega

        have hCN : ∀ w : ↥N, distinguishedModuleEndomorphism (V := ↥N) w = 0 := by
          intro w; apply Subtype.val_injective
          simp only [ZeroMemClass.coe_zero, distinguishedModuleEndomorphism, LinearMap.add_apply,
            LinearMap.smul_apply, sq, Module.End.mul_apply,
            LieModule.toEnd_apply_apply]
          exact hC ↑w

        have hN_triv : ∀ (y : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (w : ↥N), ⁅y, (w : W)⁆ = 0 := by
          intro y w
          have h1 := ih (show finrank ℂ ↥N ≤ d from by omega) hCN y w
          rw [← LieSubmodule.coe_bracket]; simp [h1]

        have hCQ : ∀ w : W ⧸ N, distinguishedModuleEndomorphism (V := W ⧸ N) w = 0 := by
          intro w
          obtain ⟨w, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N w
          have mk'_lie := fun (a : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (b : W) =>
            (LieSubmodule.Quotient.mk' N).map_lie a b |>.symm
          simp only [distinguishedModuleEndomorphism, LinearMap.add_apply, LinearMap.smul_apply, sq,
            Module.End.mul_apply, LieModule.toEnd_apply_apply, mk'_lie]
          exact congrArg _ (hC w)

        have hQ : ∀ (y : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (w : W), (⁅y, w⁆ : W) ∈ N := by
          intro y w
          have hq := ih (show finrank ℂ (W ⧸ N) ≤ d from by omega) hCQ y
            (LieSubmodule.Quotient.mk' N w)
          rw [← (LieSubmodule.Quotient.mk' N).map_lie] at hq
          rwa [LieSubmodule.Quotient.mk_eq_zero] at hq
        exact sl2_acts_trivially_of_quotient_and_sub N hN_triv hQ x v

private lemma sl2_trivial_action_of_trivial_subquotients
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (h : ∀ (_x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), distinguishedModuleEndomorphism (V := V) v = 0) :
    ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), ⁅x, v⁆ = 0 :=
  sl2_trivial_of_casimir_zero_aux (finrank ℂ V) le_rfl (fun v => h weightElement v)

private lemma complementedLattice_of_trivial_action
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (h : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), ⁅x, v⁆ = 0) :
    ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
  constructor
  intro N

  obtain ⟨M, hM⟩ := N.toSubmodule.exists_isCompl
  let M' : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
    LieSubmodule.mk M (fun {x v} hv ↦ by rw [h x v]; exact M.zero_mem)
  exact ⟨M', LieSubmodule.isCompl_toSubmodule.mp hM⟩

private lemma casimir_eigenspace_complement
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (c₀ : ℂ)
    (hInj : ∀ v ∈ N.toSubmodule, distinguishedModuleEndomorphism v = c₀ • v → v = 0)
    (hImg : ∀ v : V, distinguishedModuleEndomorphism v - c₀ • v ∈ N.toSubmodule) :
    ∃ N' : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsCompl N N' := by

  set K := (distinguishedModuleEndomorphism (V := V)).eigenspace c₀
  have hK_lie : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), v ∈ K → ⁅x, v⁆ ∈ K :=
    casimir_eigenspace_lie_invariant c₀
  let K' : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
    LieSubmodule.mk K (fun {x v} hv ↦ hK_lie x v hv)
  refine ⟨K', ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule]
  constructor
  ·
    rw [disjoint_iff_inf_le]
    intro v ⟨hvN, hvK⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hvK
    exact hInj v hvN hvK
  ·

    rw [codisjoint_iff]

    have hK_eq : K = LinearMap.ker (distinguishedModuleEndomorphism (V := V) - c₀ • 1) :=
      Module.End.eigenspace_def

    have hRange : LinearMap.range (distinguishedModuleEndomorphism (V := V) - c₀ • 1) ≤ N.toSubmodule := by
      intro w hw
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
      simp only [LinearMap.sub_apply, LinearMap.smul_apply] at hv
      rw [← hv]
      exact hImg v

    have hRN := LinearMap.finrank_range_add_finrank_ker
      (distinguishedModuleEndomorphism (V := V) - c₀ • 1)
    have hRangeFinrank := Submodule.finrank_mono hRange
    rw [← hK_eq] at hRN

    apply Submodule.eq_top_of_disjoint N.toSubmodule K (by omega)
    exact disjoint_iff_inf_le.mpr (fun v ⟨hvN, hvK⟩ ↦
      hInj v hvN (Module.End.mem_eigenspace_iff.mp hvK))

private lemma casimir_quotient_comm
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (M : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (v : V) :
    LieSubmodule.Quotient.mk' M (distinguishedModuleEndomorphism v) =
    distinguishedModuleEndomorphism (V := V ⧸ M) (LieSubmodule.Quotient.mk' M v) := by
  have hmk_lie := fun (a : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (b : V) =>
    (LieSubmodule.Quotient.mk' M).map_lie a b |>.symm
  simp only [distinguishedModuleEndomorphism, LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply,
    LieModule.toEnd_apply_apply, hmk_lie, map_add, map_nsmul]

private lemma casimir_sub_maps_to_submodule
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (M : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (c₀ : ℂ)
    (hQ_casimir : ∀ v : V ⧸ M, distinguishedModuleEndomorphism (V := V ⧸ M) v = c₀ • v) :
    ∀ v : V, distinguishedModuleEndomorphism v - c₀ • v ∈ M.toSubmodule := by
  intro v
  have hq : LieSubmodule.Quotient.mk' M (distinguishedModuleEndomorphism v - c₀ • v) = 0 := by
    rw [map_sub, map_smul, casimir_quotient_comm, hQ_casimir, sub_self]
  rwa [LieSubmodule.Quotient.mk_eq_zero] at hq

private lemma exists_irreducible_lieSubmodule
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [Nontrivial V] :
    ∃ W : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsAtom W := by
  have : (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) ≠ ⊥ := by
    intro h
    have hsub := (LieSubmodule.eq_bot_iff (N := (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V))).mp h
    exact absurd (⟨fun a b => by simp [hsub a (LieSubmodule.mem_top a),
      hsub b (LieSubmodule.mem_top b)]⟩ : Subsingleton V) (not_subsingleton V)
  exact (eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V)).resolve_left this
    |>.imp fun W ⟨hW, _⟩ => hW

private lemma isAtom_isIrreducible
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    {N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V} (hN : IsAtom N) :
    LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ↥N := by
  haveI : Nontrivial ↥N :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hN.1
  exact LieModule.IsIrreducible.mk fun M hM => by
    set M' := LieSubmodule.map N.incl M
    have hM'_le : M' ≤ N := by
      intro v hv
      rw [LieSubmodule.mem_map] at hv
      obtain ⟨m, _, rfl⟩ := hv; exact m.property
    have hM'_ne : M' ≠ ⊥ := by
      intro h; apply hM; rw [eq_bot_iff]; intro m hm
      have : N.incl m ∈ (⊥ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := h ▸ LieSubmodule.mem_map_of_mem hm
      rw [LieSubmodule.mem_bot] at this
      rw [LieSubmodule.mem_bot]; exact Subtype.val_injective this
    have hM'_eq : M' = N := (hN.le_iff.mp hM'_le).resolve_left hM'_ne
    rw [eq_top_iff]; intro m _
    suffices hmem : (m : V) ∈ M' by
      rw [LieSubmodule.mem_map] at hmem
      obtain ⟨m', hm', hm'_eq⟩ := hmem
      exact (Subtype.val_injective hm'_eq) ▸ hm'
    rw [hM'_eq]; exact m.property

private lemma complement_case_disjoint.{u} (d : ℕ)
    (ih : ∀ d' < d, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
      finrank ℂ W ≤ d' → ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (hd : finrank ℂ V ≤ d)
    (N W : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (_hN_ne_bot : N ≠ ⊥) (hW_atom : IsAtom W)
    (hWN : W ⊓ N = ⊥) :
    ∃ S : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsCompl N S := by

  have hW_ne_bot := hW_atom.1
  have hW_pos : 0 < finrank ℂ (W : Submodule ℂ V) := by
    have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hW_ne_bot
    exact Module.finrank_pos (R := ℂ)
  have hVW_lt : finrank ℂ (V ⧸ W) < finrank ℂ V := by
    have h1 := Submodule.finrank_quotient_add_finrank W.toSubmodule
    have h2 : finrank ℂ (V ⧸ W) = finrank ℂ (V ⧸ W.toSubmodule) := rfl
    omega

  have hVW_compl : ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) :=
    ih (finrank ℂ (V ⧸ W)) (by omega) (V ⧸ W) (le_refl _)
  set π := LieSubmodule.Quotient.mk' W

  obtain ⟨S_bar, hS_bar⟩ := hVW_compl.exists_isCompl (LieSubmodule.map π N)

  refine ⟨LieSubmodule.comap π S_bar, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule]
  constructor
  ·
    rw [disjoint_iff_inf_le]
    intro v ⟨hvN, hvS⟩
    have hvS' : π v ∈ S_bar := hvS
    have hvNbar : π v ∈ LieSubmodule.map π N :=
      LieSubmodule.mem_map_of_mem (N := N) hvN
    have hπv0 : π v = 0 := by
      have : (π v : V ⧸ W) ∈ (LieSubmodule.map π N ⊓ S_bar : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) :=
        ⟨hvNbar, hvS'⟩
      rw [hS_bar.inf_eq_bot, LieSubmodule.mem_bot] at this
      exact this
    have hv_W : (v : V) ∈ (W : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
      rwa [LieSubmodule.Quotient.mk_eq_zero] at hπv0
    have : (v : V) ∈ (W ⊓ N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := ⟨hv_W, hvN⟩
    rw [hWN, LieSubmodule.mem_bot] at this
    exact Submodule.mem_bot ℂ |>.mpr this
  ·
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv_top : π v ∈ (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) := LieSubmodule.mem_top _
    rw [← hS_bar.sup_eq_top, LieSubmodule.mem_sup] at hv_top
    obtain ⟨a, ha, b, hb, hab⟩ := hv_top
    rw [LieSubmodule.mem_map] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    have hvn : v - n ∈ (LieSubmodule.comap π S_bar : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
      change π (v - n) ∈ S_bar
      rw [map_sub, ← hab, add_sub_cancel_left]
      exact hb
    exact Submodule.mem_sup.mpr ⟨n, hn, v - n, hvn, by abel⟩

private lemma exists_complement_of_irreducible_quotient.{u} (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V],
    finrank ℂ V ≤ d →
    ∀ N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, N ≠ ⊤ → IsAtom N →
    LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ N) →
    (∀ (d' : ℕ), d' < d →
      ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
      finrank ℂ W ≤ d' →
      ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W)) →
    ∃ S : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsCompl N S := by
  intro V _ _ _ _ _ hd N hN_top hN_atom hirr ih

  haveI : Nontrivial (V ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]; intro hs
    exact hN_top (by
      rw [eq_top_iff]; intro v _
      have := Subsingleton.elim (LieSubmodule.Quotient.mk' N v) 0
      rwa [LieSubmodule.Quotient.mk_eq_zero] at this)
  obtain ⟨m, μ, P⟩ := exists_primitiveVector (V := V ⧸ N)
  obtain ⟨n, hn⟩ := P.exists_nat; rw [hn] at P
  have hC := casimir_on_irreducible_scalar hirr m n P

  set c_irr := (n : ℂ) * ((n : ℂ) + 2)

  have hQ_casimir : ∀ v : V ⧸ N, distinguishedModuleEndomorphism (V := V ⧸ N) v = c_irr • v := by
    intro v
    have h := LinearMap.congr_fun hC v
    simp only [LinearMap.smul_apply] at h
    exact h

  have hImg : ∀ v : V, distinguishedModuleEndomorphism v - c_irr • v ∈ N.toSubmodule :=
    casimir_sub_maps_to_submodule N c_irr hQ_casimir

  by_cases hInj : ∀ v ∈ N.toSubmodule, distinguishedModuleEndomorphism v = c_irr • v → v = 0
  ·
    exact casimir_eigenspace_complement N c_irr hInj hImg
  ·

    by_cases hc_zero : c_irr = 0 ∧ ∀ v ∈ N.toSubmodule, distinguishedModuleEndomorphism v = c_irr • v
    ·
      have hc := hc_zero.1
      have hAllN := hc_zero.2
      simp only [hc, zero_smul, sub_zero] at hImg hAllN hQ_casimir ⊢

      have hN_triv : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : ↥N), ⁅x, (v : V)⁆ = 0 := by
        have hCN : ∀ w : ↥N, distinguishedModuleEndomorphism (V := ↥N) w = 0 := by
          intro w; apply Subtype.val_injective
          simp only [ZeroMemClass.coe_zero, distinguishedModuleEndomorphism, LinearMap.add_apply,
            LinearMap.smul_apply, sq, Module.End.mul_apply,
            LieModule.toEnd_apply_apply]
          exact hAllN w.val w.property
        have := sl2_trivial_action_of_trivial_subquotients (fun _ v => hCN v)
        intro x w
        have h1 := this x w
        rw [← LieSubmodule.coe_bracket]; simp [h1]

      have hQ_triv : ∀ (x : RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V), (⁅x, v⁆ : V) ∈ N := by

        have hCQ : ∀ w : V ⧸ N, distinguishedModuleEndomorphism (V := V ⧸ N) w = 0 := by

          intro w; exact hQ_casimir w
        have hQ_act := sl2_trivial_action_of_trivial_subquotients (fun _ v => hCQ v)
        intro x v
        have h1 := hQ_act x (LieSubmodule.Quotient.mk' N v)
        rw [← (LieSubmodule.Quotient.mk' N).map_lie] at h1
        rwa [LieSubmodule.Quotient.mk_eq_zero] at h1

      have htriv := sl2_acts_trivially_of_quotient_and_sub N hN_triv hQ_triv
      exact (complementedLattice_of_trivial_action htriv).exists_isCompl N
    ·

      have hN_irr := isAtom_isIrreducible hN_atom
      haveI hN_nt : Nontrivial ↥N :=
        (LieSubmodule.nontrivial_iff_ne_bot ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hN_atom.1

      push Not at hInj
      obtain ⟨v₀, hv₀_mem, hv₀_C, hv₀_ne⟩ := hInj

      have hv₀_eigen : v₀ ∈ (distinguishedModuleEndomorphism (V := V)).eigenspace c_irr :=
        Module.End.mem_eigenspace_iff.mpr hv₀_C

      let Ec : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V :=
        LieSubmodule.mk ((distinguishedModuleEndomorphism (V := V)).eigenspace c_irr)
          (fun {x v} hv ↦ casimir_eigenspace_lie_invariant c_irr x v hv)

      have hv₀_inter : v₀ ∈ (Ec ⊓ N : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := ⟨hv₀_eigen, hv₀_mem⟩
      have hEN_ne : Ec ⊓ N ≠ ⊥ := by
        intro h; rw [h, LieSubmodule.mem_bot] at hv₀_inter; exact hv₀_ne hv₀_inter
      have hN_le_Ec : N ≤ Ec := by
        rcases eq_or_lt_of_le (inf_le_right (a := Ec) (b := N)) with h | h
        · exact h ▸ inf_le_left
        · exact absurd (hN_atom.2 _ h) hEN_ne
      have hAllN : ∀ v ∈ N.toSubmodule, distinguishedModuleEndomorphism v = c_irr • v := by
        intro w hw; exact Module.End.mem_eigenspace_iff.mp (hN_le_Ec hw)

      obtain ⟨mN, μN, PN⟩ := exists_primitiveVector (V := N)
      obtain ⟨nN, hnN⟩ := PN.exists_nat; rw [hnN] at PN

      have hmN_h : ⁅sl2_h, (mN : V)⁆ = (nN : ℂ) • (mN : V) := by
        have := congrArg Subtype.val PN.lie_h
        simp only [LieSubmodule.coe_bracket, LieSubmodule.coe_smul] at this; exact this
      have hmN_e : ⁅sl2_e, (mN : V)⁆ = 0 := by
        have := congrArg Subtype.val PN.lie_e
        simp only [LieSubmodule.coe_bracket, ZeroMemClass.coe_zero] at this; exact this
      have hCmN : distinguishedModuleEndomorphism (V := V) (mN : V) = ((nN : ℂ) * ((nN : ℂ) + 2)) • (mN : V) := by
        have hH' : (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V weightElement) (mN : V) = (nN : ℂ) • (mN : V) := by
          change ⁅sl2_h, (mN : V)⁆ = _; exact hmN_h
        have hE' : (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V raisingElement) (mN : V) = 0 := by
          change ⁅sl2_e, (mN : V)⁆ = _; exact hmN_e
        rw [sl2_casimir_eq]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply,
          ← Nat.cast_smul_eq_nsmul ℂ, hE', map_zero, smul_zero, add_zero,
          hH', map_smul, smul_smul, ← add_smul]
        congr 1; push_cast; ring
      have hnn : (nN : ℂ) * ((nN : ℂ) + 2) = c_irr := by
        have h1 := hAllN (mN : V) mN.property
        rw [hCmN] at h1
        have hmN_ne : (mN : V) ≠ 0 := fun h => PN.ne_zero (Subtype.val_injective h)
        exact smul_left_injective ℂ hmN_ne h1
      have hnN_eq : nN = n := casimir_eigenvalue_injective hnn

      have hc_ne : c_irr ≠ 0 := fun hc => hc_zero ⟨hc, hAllN⟩

      have hn_pos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · simp [c_irr] at hc_ne
        · exact h

      have hdimN : finrank ℂ ↥N = n + 1 := primitiveVector_dim hN_irr mN n (hnN_eq ▸ PN)

      obtain ⟨v₁, hv₁⟩ := LieSubmodule.Quotient.surjective_mk' N m

      set π := LieSubmodule.Quotient.mk' N
      have hw_mem : ⁅sl2_h, v₁⁆ - (n : ℂ) • v₁ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, map_smul, π.map_lie, hv₁,
          sub_eq_zero]
        exact P.lie_h
      set w := ⁅sl2_h, v₁⁆ - (n : ℂ) • v₁

      have hfN_zero : ∀ u ∈ N.toSubmodule,
          ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (n + 1)) u = 0 := by

        have hPN' := (hnN_eq ▸ PN : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith mN (n : ℂ))
        have hPN_kill : ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ (n + 1)) mN = 0 :=
          hPN'.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)

        have hfk_kill : ∀ k, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ (n + 1 + k)) mN = 0 := by
          intro k; induction k with
          | zero => simpa using hPN_kill
          | succ k ih =>
            rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega,
              pow_succ', Module.End.mul_apply, ih, map_zero]

        have hfN_nil : (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (↥N) loweringElement) ^ (n + 1) = 0 := by
          let bN := primitiveOrbit_basis hN_irr mN n hPN'
          apply bN.ext; intro ⟨k, hk⟩
          rw [LinearMap.zero_apply,
            show bN ⟨k, hk⟩ = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ k) mN from Basis.mk_apply _ _ _,
            ← Module.End.mul_apply, ← pow_add]
          exact hfk_kill k

        intro u hu
        suffices h : ∀ (k : ℕ) (v : N),
            ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) (v : V) = (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ k) v : V) by
          rw [h (n + 1) ⟨u, hu⟩, hfN_nil, LinearMap.zero_apply, ZeroMemClass.coe_zero]
        intro k v; induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]; rfl

      have hPN' := (hnN_eq ▸ PN : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith mN (n : ℂ))

      have weight_vanish : ∀ (u : V), u ∈ N → ∀ μ : ℂ, ⁅sl2_h, u⁆ = μ • u →
          (∀ k : Fin (n + 1), μ ≠ (n : ℂ) - 2 * ↑k.val) → u = 0 := by
        intro u hu μ heigen hweights
        have h_mem : (⟨u, hu⟩ : N) ∈ (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N weightElement).eigenspace μ := by
          rw [Module.End.mem_eigenspace_iff]; apply Subtype.val_injective
          simp only [LieSubmodule.coe_smul]; exact heigen
        have h_bot := eigenspace_eq_bot_of_not_weight hN_irr mN n hPN' μ hweights
        rw [h_bot, Submodule.mem_bot] at h_mem; exact congr_arg Subtype.val h_mem

      have hev₁ : ⁅sl2_e, v₁⁆ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, π.map_lie, hv₁]; exact P.lie_e

      have hπ_f : ∀ (k : ℕ) (u : V), π (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) u) =
          ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ N) loweringElement) ^ k) (π u) := by
        intro k u; induction k with
        | zero => simp
        | succ k ih =>
          simp only [pow_succ', Module.End.mul_apply, ← ih]
          exact (π.map_lie loweringElement _).symm

      have hfn1v₁_mem : ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (n + 1)) v₁ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, hπ_f, hv₁]
        exact P.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)

      have hfn1_eigen : ⁅sl2_h, ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (n + 1)) v₁⁆ =
          (-(n : ℂ) - 2) • ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (n + 1)) v₁ := by
        rw [h_comm_pow_f (n + 1) v₁]
        have hw_eq : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [hw_eq, map_add, map_smul, hfN_zero w hw_mem, zero_add]; module

      have hfn1v₁ : ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (n + 1)) v₁ = 0 :=
        weight_vanish _ hfn1v₁_mem _ hfn1_eigen (by
          intro k heq
          have h1 : (2 : ℂ) * ↑k.val = 2 * ↑n + 2 := by linear_combination heq
          have h2 : 2 * (k.val : ℤ) = 2 * (n : ℤ) + 2 := by exact_mod_cast h1
          omega)

      have hfnw : ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ n) w = 0 := by
        have h1 := e_f_pow_succ_comm n v₁
        rw [hfn1v₁, lie_zero, hfN_zero _ hev₁, zero_add] at h1
        have hw_eq : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [hw_eq, map_add, map_smul, add_sub_cancel_right] at h1
        have hn1_ne : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        exact (smul_eq_zero.mp h1.symm).resolve_left hn1_ne

      obtain ⟨n₀, hn₀_mem, h_adj⟩ :
          ∃ n₀ : V, n₀ ∈ N ∧ ⁅sl2_h, n₀⁆ - (n : ℂ) • n₀ = w := by

        let bN := primitiveOrbit_basis hN_irr mN n hPN'
        set cw := bN.repr ⟨w, hw_mem⟩

        have hbN : ∀ k : Fin (n + 1), bN k = ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ (k : ℕ)) mN :=
          fun k => Basis.mk_apply _ _ _

        have hcoerce : ∀ (k : ℕ) (u : N),
            ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ k) (u : V) = (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ k) u : V) := by
          intro k u; induction k with
          | zero => simp
          | succ k ih =>
            rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]; rfl

        have hfN_nil : (toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ (n + 1) = 0 := by
          ext v; simp only [LinearMap.zero_apply]
          have h1 := hcoerce (n + 1) v
          rw [hfN_zero v.val v.property] at h1
          exact_mod_cast h1.symm

        have hcw0 : cw ⟨0, Nat.zero_lt_succ n⟩ = 0 := by

          have hfnw_N : ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N loweringElement) ^ n) ⟨w, hw_mem⟩ = 0 := by
            have h1 := hcoerce n ⟨w, hw_mem⟩; rw [hfnw] at h1; exact_mod_cast h1.symm

          rw [show (⟨w, hw_mem⟩ : N) = ∑ k, cw k • bN k from (bN.sum_repr _).symm,
            map_sum] at hfnw_N
          simp only [map_smul, hbN, ← Module.End.mul_apply, ← pow_add] at hfnw_N

          rw [Finset.sum_eq_single_of_mem ⟨0, Nat.zero_lt_succ n⟩ (Finset.mem_univ _)
            (fun k _ hk => by
              have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
              rw [show n + (k : ℕ) = (n + 1) + ((k : ℕ) - 1) from by omega, pow_add,
                Module.End.mul_apply, hfN_nil, LinearMap.zero_apply, smul_zero])] at hfnw_N
          simp only [Nat.add_zero] at hfnw_N
          exact (smul_eq_zero.mp hfnw_N).resolve_right
            (hPN'.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega))

        let n₀_N : ↥N := ∑ k : Fin (n + 1),
          (if (k : ℕ) = 0 then (0 : ℂ) else cw k / (-(2 * (k : ℂ)))) • bN k
        refine ⟨(n₀_N : V), n₀_N.property, ?_⟩

        suffices h_N : ⁅sl2_h, n₀_N⁆ - (n : ℂ) • n₀_N = ⟨w, hw_mem⟩ from
          congrArg Subtype.val h_N

        have heigen : ∀ k : Fin (n + 1),
            ⁅sl2_h, bN k⁆ - (n : ℂ) • bN k = (-(2 * (k : ℂ))) • bN k := by
          intro k; rw [hbN k, hPN'.lie_h_pow_toEnd_f]; module

        simp only [n₀_N, lie_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]

        refine ((bN.sum_repr ⟨w, hw_mem⟩).symm.trans (Finset.sum_congr rfl fun k _ => ?_)).symm

        set ck := (if (k : ℕ) = 0 then (0 : ℂ) else cw k / (-(2 * (k : ℂ)))) with hck_def

        have h1 : ⁅sl2_h, bN k⁆ = (-(2 * (k : ℂ))) • bN k + (n : ℂ) • bN k := by
          have := heigen k; rw [sub_eq_iff_eq_add] at this; exact this
        rw [lie_smul, h1, smul_add, smul_smul, smul_smul, smul_smul]

        rw [show ck * (n : ℂ) = (n : ℂ) * ck from mul_comm _ _, add_sub_cancel_right]

        congr 1

        rw [hck_def]

        change cw k = ck * (-(2 * (k : ℂ)))
        rw [hck_def]
        by_cases hk0 : (k : ℕ) = 0
        · have hk_eq : k = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hk0
          subst hk_eq
          simp only [↓reduceIte, Nat.cast_zero, mul_zero, neg_zero]
          exact hcw0
        · simp only [hk0, ↓reduceIte]
          have : (k.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
          field_simp

      set v := v₁ - n₀ with hv_def

      have hv_h : ⁅sl2_h, v⁆ = (n : ℂ) • v := by
        simp only [hv_def, lie_sub, smul_sub]
        have : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [this, ← h_adj]; abel

      have hπn₀ : π n₀ = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hn₀_mem
      have hv_e : ⁅sl2_e, v⁆ = 0 := by
        have hev_mem : ⁅sl2_e, v⁆ ∈ N := by
          rw [← LieSubmodule.Quotient.mk_eq_zero, π.map_lie, hv_def, map_sub, hπn₀, sub_zero,
            hv₁]
          exact P.lie_e
        have hev_eigen : ⁅sl2_h, ⁅sl2_e, v⁆⁆ = ((n : ℂ) + 2) • ⁅sl2_e, v⁆ := by
          rw [leibniz_lie, isSl2Triple_weight_raising_lowering.lie_h_e_nsmul, hv_h, nsmul_lie, lie_smul,
            ← Nat.cast_smul_eq_nsmul ℂ (2 : ℕ), ← add_smul]
          ring_nf
        exact weight_vanish _ hev_mem _ hev_eigen (by
          intro k heq
          have h1 : (2 : ℂ) * ↑k.val + 2 = 0 := by linear_combination heq
          have h2 : 2 * (k.val : ℤ) + 2 = 0 := by exact_mod_cast h1
          omega)

      have hv_ne : v ≠ 0 := by
        intro h
        have : π v = 0 := by rw [h, map_zero]
        rw [hv_def, map_sub, hπn₀, sub_zero, hv₁] at this
        exact P.ne_zero this

      have Pv : isSl2Triple_weight_raising_lowering.HasPrimitiveVectorWith v (n : ℂ) := ⟨hv_ne, hv_h, hv_e⟩
      let S : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V := LieSubmodule.mk
        (Submodule.span ℂ (Set.range (fun k : Fin (n + 1) ↦
          ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) v)))
        (fun {x u} hu ↦ primitiveOrbit_lieInvariant v n Pv x u hu)

      have hπ_fkv : ∀ k : Fin (n + 1), π (((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) v) =
          ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ N) loweringElement) ^ (k : ℕ)) m := by
        intro k; rw [hπ_f, hv_def, map_sub, hπn₀, sub_zero, hv₁]

      let fkv : Fin (n + 1) → V := fun k ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V loweringElement) ^ (k : ℕ)) v
      have hli_v : LinearIndependent ℂ fkv := by
        have hli_m := primitiveOrbit_linearIndependent m n P
        have : (fun k : Fin (n + 1) ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ N) loweringElement) ^ (k : ℕ)) m) =
            π.toLinearMap ∘ fkv :=
          funext (fun k => (hπ_fkv k).symm)
        rw [this] at hli_m
        exact hli_m.of_comp _
      have hSN : S ⊓ N = ⊥ := by
        rw [eq_bot_iff]; intro u ⟨huS, huN⟩
        rw [LieSubmodule.mem_bot]
        have hπu : π u = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr huN

        have huS' : u ∈ Submodule.span ℂ (Set.range fkv) := huS
        rw [Submodule.mem_span_range_iff_exists_fun] at huS'
        obtain ⟨c, rfl⟩ := huS'

        simp only [map_sum, map_smul] at hπu

        let fkm : Fin (n + 1) → V ⧸ N := fun k ↦ ((toEnd ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ N) loweringElement) ^ (k : ℕ)) m
        have hli_m := primitiveOrbit_linearIndependent m n P
        have hπu' : ∑ i, c i • fkm i = 0 := by
          simp only [fkm, ← hπ_fkv]; exact hπu
        have hc : ∀ i, c i = 0 :=
          (Fintype.linearIndependent_iffₛ (v := fkm)).mp hli_m c 0
            (by simp [hπu'])
        simp [show c = 0 from funext hc]

      have hS_ne : S ≠ ⊥ := by
        intro h; apply hv_ne
        have : v ∈ (⊥ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := h ▸ (show v ∈ S from
          Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ n⟩, by simp⟩)
        rwa [LieSubmodule.mem_bot] at this

      obtain ⟨W, hW_atom, hW_le⟩ := (eq_bot_or_exists_atom_le S).resolve_left hS_ne
      have hWN : W ⊓ N = ⊥ :=
        eq_bot_iff.mpr (le_trans (inf_le_inf_right N hW_le) (le_of_eq hSN))
      exact complement_case_disjoint d ih hd N W hN_atom.1 hW_atom hWN

private lemma complement_case_sub.{u} (d : ℕ)
    (ih : ∀ d' < d, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W],
      finrank ℂ W ≤ d' → ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (hd : finrank ℂ V ≤ d)
    (N W : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (hN_ne_top : N ≠ ⊤) (hW_atom : IsAtom W) (hWN : W ≤ N) :
    ∃ S : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsCompl N S := by
  have hW_ne_bot := hW_atom.1
  have hW_pos : 0 < finrank ℂ (W : Submodule ℂ V) := by
    have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hW_ne_bot
    exact Module.finrank_pos (R := ℂ)

  have hVW_lt : finrank ℂ (V ⧸ W) < finrank ℂ V := by
    have h1 := Submodule.finrank_quotient_add_finrank W.toSubmodule
    have h2 : finrank ℂ (V ⧸ W) = finrank ℂ (V ⧸ W.toSubmodule) := rfl
    omega

  have hVW_compl : ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) :=
    ih (finrank ℂ (V ⧸ W)) (by omega) (V ⧸ W) (le_refl _)
  set π := LieSubmodule.Quotient.mk' W

  obtain ⟨T_bar, hT_bar⟩ := hVW_compl.exists_isCompl (LieSubmodule.map π N)

  set T := LieSubmodule.comap π T_bar

  have hW_le_T : W ≤ T := by
    intro w hw
    change π w ∈ T_bar
    have : π w = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr hw
    rw [this]; exact T_bar.zero_mem
  have hNT_inf : N ⊓ T = W := by
    apply le_antisymm
    · intro v ⟨hvN, hvT⟩
      have hvN_bar : π v ∈ LieSubmodule.map π N := LieSubmodule.mem_map_of_mem hvN
      have : π v ∈ (LieSubmodule.map π N ⊓ T_bar : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) :=
        ⟨hvN_bar, hvT⟩
      rw [hT_bar.inf_eq_bot, LieSubmodule.mem_bot] at this
      exact (LieSubmodule.Quotient.mk_eq_zero (N := W)).mp this
    · exact le_inf hWN hW_le_T
  have hNT_sup : N ⊔ T = ⊤ := by
    rw [eq_top_iff]; intro v _
    have hv_top : π v ∈ (⊤ : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)) := LieSubmodule.mem_top _
    rw [← hT_bar.sup_eq_top, LieSubmodule.mem_sup] at hv_top
    obtain ⟨a, ha, b, hb, hab⟩ := hv_top
    rw [LieSubmodule.mem_map] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    have hvn : v - n ∈ (T : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
      change π (v - n) ∈ T_bar
      rw [map_sub, ← hab, add_sub_cancel_left]; exact hb
    rw [show v = n + (v - n) by abel, LieSubmodule.mem_sup]
    exact ⟨n, hn, v - n, hvn, rfl⟩

  by_cases hNW : N = W
  ·
    rw [hNW]
    by_cases hirr : LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W)
    ·
      exact exists_complement_of_irreducible_quotient d hd W (hNW ▸ hN_ne_top) hW_atom hirr ih
    ·
      haveI : Nontrivial (V ⧸ W) := by
        rw [← not_subsingleton_iff_nontrivial]; intro hs
        exact (hNW ▸ hN_ne_top) (by
          rw [eq_top_iff]; intro v _
          have := Subsingleton.elim (LieSubmodule.Quotient.mk' W v) 0
          rwa [LieSubmodule.Quotient.mk_eq_zero] at this)

      have hnotirr : ¬∀ S : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (V ⧸ W), S = ⊥ ∨ S = ⊤ := by
        intro hall; exact hirr (LieModule.IsIrreducible.mk (fun S hS => (hall S).resolve_left hS))
      push Not at hnotirr
      obtain ⟨S_bar, hS_ne_bot, hS_ne_top⟩ := hnotirr

      set E := LieSubmodule.comap π S_bar
      have hW_le_E : W ≤ E := fun w hw => by
        change π w ∈ S_bar
        rw [(LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr hw]; exact S_bar.zero_mem
      have hE_ne_top : (E : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) ≠ ⊤ := by
        intro h; apply hS_ne_top; rw [eq_top_iff]; intro v _
        obtain ⟨v₀, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W v
        exact (h ▸ LieSubmodule.mem_top v₀ : v₀ ∈ E)
      have hW_ne_E : W ≠ E := by
        intro h; apply hS_ne_bot; rw [eq_bot_iff]; intro v hv
        obtain ⟨v₀, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W v
        have : v₀ ∈ E := hv
        rw [← h] at this
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr this
      have hW_lt_E : W < E := lt_of_le_of_ne hW_le_E hW_ne_E

      have hE_lt : finrank ℂ (E : Submodule ℂ V) < finrank ℂ V := by
        have h1 : E.toSubmodule ≠ ⊤ := by
          intro h; apply hE_ne_top
          rw [eq_top_iff]; intro v _
          change v ∈ E.toSubmodule
          rw [h]
          trivial
        have h2 := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr h1)
        rwa [finrank_top] at h2

      have hE_compl : ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra E) :=
        ih (finrank ℂ (E : Submodule ℂ V)) (by omega) E le_rfl

      set W_E := LieSubmodule.comap (E : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).incl W

      have hW_E_ne_top : W_E ≠ ⊤ := by
        intro h; exact absurd (le_antisymm (fun v hv => by
          have : (⟨v, hv⟩ : E) ∈ W_E := h ▸ LieSubmodule.mem_top _
          exact this) hW_le_E) (ne_of_lt hW_lt_E).symm

      obtain ⟨C_E, hC_E⟩ := hE_compl.exists_isCompl W_E
      have hC_E_ne_bot : C_E ≠ ⊥ := by
        intro h; exact hW_E_ne_top (by rw [← hC_E.sup_eq_top, h, sup_bot_eq])

      set C_V := LieSubmodule.map (E : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).incl C_E

      have hC_V_disj : C_V ⊓ W = ⊥ := by
        rw [eq_bot_iff]; intro v ⟨hvC, hvW⟩
        have hvC' : v ∈ (C_V : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := hvC
        rw [LieSubmodule.mem_map] at hvC'
        obtain ⟨c, hc, rfl⟩ := hvC'
        have hcW : c ∈ W_E := hvW
        have : c ∈ (W_E ⊓ C_E : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra E) := ⟨hcW, hc⟩
        rw [hC_E.inf_eq_bot, LieSubmodule.mem_bot] at this
        simp [this]

      have hC_V_ne_bot : C_V ≠ ⊥ := by
        intro h; apply hC_E_ne_bot; rw [eq_bot_iff]; intro c hc
        have : (E : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V).incl c ∈ C_V :=
          LieSubmodule.mem_map_of_mem hc
        rw [h, LieSubmodule.mem_bot] at this
        rw [LieSubmodule.mem_bot]
        exact Subtype.val_injective this

      obtain ⟨W', hW'_atom, hW'_le⟩ :=
        (eq_bot_or_exists_atom_le C_V).resolve_left hC_V_ne_bot

      have hW'_disj : W' ⊓ W = ⊥ :=
        eq_bot_iff.mpr (le_trans (inf_le_inf_right W hW'_le) (le_of_eq hC_V_disj))

      exact complement_case_disjoint d ih hd W W' hW_ne_bot hW'_atom hW'_disj
  ·
    have hW_lt_N : W < N := lt_of_le_of_ne hWN (Ne.symm hNW)
    have hfW_lt_N : finrank ℂ (W : Submodule ℂ V) < finrank ℂ (N : Submodule ℂ V) :=
      Submodule.finrank_lt_finrank_of_lt (show W.toSubmodule < N.toSubmodule from hW_lt_N)

    have hfT_lt : finrank ℂ (T : Submodule ℂ V) < finrank ℂ V := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq N.toSubmodule T.toSubmodule
      have h2 : N.toSubmodule ⊔ T.toSubmodule = ⊤ := by
        have := congrArg LieSubmodule.toSubmodule hNT_sup
        rwa [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule] at this
      have h3 : N.toSubmodule ⊓ T.toSubmodule = W.toSubmodule := by
        have := congrArg LieSubmodule.toSubmodule hNT_inf
        rwa [LieSubmodule.inf_toSubmodule] at this
      rw [h2, h3, finrank_top] at h1; omega

    have hT_compl : ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra T) :=
      ih (finrank ℂ (T : Submodule ℂ V)) (by omega) T (le_refl _)

    set W_T := LieSubmodule.comap T.incl W

    obtain ⟨U_T, hU_T⟩ := hT_compl.exists_isCompl W_T

    set U := LieSubmodule.map T.incl U_T
    refine ⟨U, ?_⟩
    rw [← LieSubmodule.isCompl_toSubmodule]
    constructor
    ·
      rw [disjoint_iff_inf_le]
      intro v ⟨hvN, hvU⟩

      have hvU' : v ∈ (U : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := hvU
      rw [LieSubmodule.mem_map] at hvU'
      obtain ⟨u, hu, rfl⟩ := hvU'

      have h1 : T.incl u ∈ (N ⊓ T : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) :=
        ⟨hvN, u.property⟩
      rw [hNT_inf] at h1

      have h3 : u ∈ (W_T ⊓ U_T : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra T) := ⟨h1, hu⟩
      rw [hU_T.inf_eq_bot, LieSubmodule.mem_bot] at h3
      simp [h3]
    ·
      rw [codisjoint_iff, eq_top_iff]
      intro v _

      have hv_NT : v ∈ (N ⊔ T : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := hNT_sup ▸ LieSubmodule.mem_top v
      rw [LieSubmodule.mem_sup] at hv_NT
      obtain ⟨n, hn, t_val, ht, rfl⟩ := hv_NT

      have ht_WT : (⟨t_val, ht⟩ : T) ∈ (W_T ⊔ U_T : LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra T) :=
        hU_T.sup_eq_top ▸ LieSubmodule.mem_top _
      rw [LieSubmodule.mem_sup] at ht_WT
      obtain ⟨w, hw, u, hu, hwu⟩ := ht_WT

      have hw_N : (T.incl w : V) ∈ N := hWN hw

      have ht_eq : t_val = (w : V) + (u : V) := by
        have := congrArg Subtype.val hwu
        exact this.symm
      rw [ht_eq, show n + ((w : V) + (u : V)) = (n + (w : V)) + (u : V) by abel]
      exact Submodule.add_mem_sup (N.add_mem hn hw_N) (LieSubmodule.mem_map_of_mem hu)

private lemma complementedLattice_sl2_aux (d : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V],
    finrank ℂ V ≤ d →
    ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := by
  induction d using Nat.strongRecOn with | ind d ih => ?_
  intro V _ _ _ _ _ hd
  constructor
  intro N
  by_cases hNbot : N = ⊥
  · exact ⟨⊤, hNbot ▸ isCompl_bot_top⟩
  by_cases hNtop : N = ⊤
  · exact ⟨⊥, hNtop ▸ isCompl_top_bot⟩
  haveI hnt : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]; intro hs
    exact hNbot (by ext v; simp [Subsingleton.elim v 0])
  obtain ⟨W, hW_atom⟩ := exists_irreducible_lieSubmodule (V := V)
  by_cases hWN : W ≤ N
  · exact complement_case_sub d ih hd N W hNtop hW_atom hWN
  · have hWN_bot : W ⊓ N = ⊥ :=
      (hW_atom.le_iff.mp inf_le_left).resolve_right (fun h => hWN (h ▸ inf_le_right))
    exact complement_case_disjoint d ih hd N W hNbot hW_atom hWN_bot

/-- Lie submodules of a finite-dimensional module over the specified Lie algebra form a complemented lattice. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
theorem lieSubmodule_complementedLattice (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] :
    ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) :=
  complementedLattice_sl2_aux (finrank ℂ V) V le_rfl

/-- A proposition associated with a module over a Lie algebra. -/
def LieModuleCondition (R L V : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : LieSubmodule R L V),
    IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥

/-- The specified module condition implies irreducibility for a finite-dimensional module. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := primary)]
theorem isIrreducible_of_lieModuleCondition (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [LieRingModule RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    (hV : LieModuleCondition ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) :
    LieModule.IsIrreducible ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V := by
  letI : Nontrivial V := hV.1
  letI : ComplementedLattice (LieSubmodule ℂ RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := lieSubmodule_complementedLattice V
  refine IsSimpleOrder.of_forall_eq_top fun W hW ↦ ?_
  obtain ⟨P, hP⟩ := ComplementedLattice.exists_isCompl W
  rcases hV.2 W P hP with hbot | hPbot
  · exact (hW hbot).elim
  · have hsup : W ⊔ P = ⊤ := codisjoint_iff.mp hP.codisjoint
    simpa [hPbot] using hsup

end CompleteReducibility

end RepresentationTheory.LieAlgebra.FiniteDimensionalModules

