/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.PiTensorProduct.Constructions
import RepresentationTheory.TensorProducts.Auxiliary

open scoped TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

namespace RepresentationTheory.AuxiliaryEndomorphismActions

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- A type family associated to a field, a module, and a natural-number parameter. -/
abbrev auxiliarySpace := ⨂[k] (_ : Fin n), V

/-- A Lie algebra homomorphism from module endomorphisms to endomorphisms of the associated auxiliary type. -/
noncomputable def endomorphismLieHom :
    Module.End k V →ₗ⁅k⁆ Module.End k (auxiliarySpace k V n) where
  toLinearMap :=
    { toFun := fun b => ∑ i : Fin n,
        PiTensorProduct.map (fun j => if j = i then b else LinearMap.id)
      map_add' := by
        intro b₁ b₂
        have key : ∀ (i : Fin n) (b : Module.End k V),
            (fun j => if j = i then b else LinearMap.id) =
            Function.update (fun _ => LinearMap.id) i b := by
          intro i b; ext j; simp [Function.update, eq_comm]
        simp_rw [key]
        rw [← Finset.sum_add_distrib]
        congr 1; ext i
        rw [PiTensorProduct.map_update_add]
      map_smul' := by
        intro c b
        have key : ∀ (i : Fin n) (b : Module.End k V),
            (fun j => if j = i then b else LinearMap.id) =
            Function.update (fun _ => LinearMap.id) i b := by
          intro i b; ext j; simp [Function.update, eq_comm]
        simp_rw [key]
        rw [show RingHom.id k c = c from rfl, Finset.smul_sum]
        congr 1; ext i
        rw [PiTensorProduct.map_update_smul] }
  map_lie' := by
    intro b₁ b₂
    have key : ∀ (i : Fin n) (b : Module.End k V),
        (fun j => if j = i then b else LinearMap.id) =
        Function.update (fun _ => LinearMap.id) i b := by
      intro i b; ext j; simp [Function.update, eq_comm]
    simp_rw [key]
    simp only [LieRing.of_associative_ring_bracket]
    set δ := fun (i : Fin n) (b : Module.End k V) =>
      PiTensorProduct.map (R := k) (s := fun _ => V) (t := fun _ => V)
        (Function.update (fun _ => LinearMap.id) i b) with hδ
    have mul_eq : ∀ (i j : Fin n) (a b : Module.End k V),
        δ i a * δ j b = PiTensorProduct.map
          (fun l => Function.update (fun _ => LinearMap.id) i a l *
                    Function.update (fun _ => LinearMap.id) j b l) := by
      intro i j a b; exact (PiTensorProduct.map_mul _ _).symm
    have δ_sub : ∀ (i : Fin n) (a b : Module.End k V),
        δ i (a - b) = δ i a - δ i b := by
      intro i a b
      simp only [hδ]
      exact (PiTensorProduct.mapMultilinear (R := k) (s := fun _ => V)
        (t := fun _ => V)).map_update_sub (fun _ => LinearMap.id) i a b
    have δ_mul : ∀ (i : Fin n) (a b : Module.End k V),
        δ i (a * b) = δ i a * δ i b := by
      intro i a b
      simp only [hδ, ← PiTensorProduct.map_mul]
      congr 1; funext l
      by_cases h : l = i <;>
        simp [Function.update, h, Module.End.mul_eq_comp, LinearMap.comp_id]
    have lhs_eq : ∀ i : Fin n,
        δ i (b₁ * b₂ - b₂ * b₁) = δ i b₁ * δ i b₂ - δ i b₂ * δ i b₁ := by
      intro i; rw [δ_sub, δ_mul, δ_mul]
    rw [Finset.sum_congr rfl (fun i _ => lhs_eq i)]
    have comm : ∀ i j : Fin n, i ≠ j → δ i b₁ * δ j b₂ = δ j b₂ * δ i b₁ := by
      intro i j hij
      simp only [hδ, ← PiTensorProduct.map_mul]
      congr 1; funext l
      by_cases hi : l = i <;> by_cases hj : l = j <;>
        simp [Function.update, hi, hj, hij, Ne.symm hij,
          Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm (f := fun j i => δ j b₂ * δ i b₁)]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    symm
    exact Finset.sum_eq_single i
      (fun j _ hji => sub_eq_zero.mpr (comm i j hji.symm))
      (fun h => absurd (Finset.mem_univ _) h)

/-- An algebra homomorphism from the universal enveloping algebra of module endomorphisms to endomorphisms of the associated auxiliary type. -/
noncomputable def universalEnvelopingAlgebraHom :
    UniversalEnvelopingAlgebra k (Module.End k V) →ₐ[k]
      Module.End k (auxiliarySpace k V n) :=
  UniversalEnvelopingAlgebra.lift k (endomorphismLieHom k V n)

/-- A subalgebra of the endomorphism algebra of the associated auxiliary type. -/
noncomputable def auxiliarySubalgebra :
    Subalgebra k (Module.End k (auxiliarySpace k V n)) :=
  Algebra.adjoin k (Set.range fun (σ : Equiv.Perm (Fin n)) =>
    (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap)

omit [Module.Finite k V] in
private lemma endomorphismLieHom_commutes_reindex (b : Module.End k V)
    (σ : Equiv.Perm (Fin n)) :
    endomorphismLieHom k V n b *
      (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap =
    (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap *
      endomorphismLieHom k V n b := by
  simp only [endomorphismLieHom, LieHom.coe_mk]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_nbij σ.symm
  · exact fun _ _ => Finset.mem_univ _
  · exact σ.symm.injective.injOn
  · exact fun i _ => ⟨σ i, by simp, σ.symm_apply_apply i⟩
  · intro i _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    rw [← PiTensorProduct.map_comp_reindex_eq]
    congr 1; congr 1; funext j
    simp

/-- Over a characteristic-zero field, the centralizer of the auxiliary subalgebra equals the range of the universal-enveloping-algebra homomorphism. -/
@[source_ref "Chapter5/Theorem5.18.2" (role := primary)]
theorem centralizer_auxiliarySubalgebra_eq_range_universalEnvelopingAlgebraHom [CharZero k] :
    Subalgebra.centralizer k
      (auxiliarySubalgebra k V n : Set (Module.End k (auxiliarySpace k V n))) =
    (universalEnvelopingAlgebraHom k V n).range := by
  apply le_antisymm
  ·
    have h_cent_full : Subalgebra.centralizer k
        (auxiliarySubalgebra k V n : Set (Module.End k (auxiliarySpace k V n))) ≤
        PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n := by
      open TensorProducts.Auxiliary in
      intro φ hφ
      rw [Subalgebra.mem_centralizer_iff] at hφ
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
    have h_full_diag : PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n ≤
        PiTensorProduct.Constructions.piTensorEndSubalgebra k V n :=
      (PiTensorProduct.Constructions.piTensorEndSubalgebra_eq_alternate k V n).ge
    have h_diag_range : PiTensorProduct.Constructions.piTensorEndSubalgebra k V n ≤
        (universalEnvelopingAlgebraHom k V n).range := by
      apply Algebra.adjoin_le
      rintro _ ⟨b, rfl⟩
      exact (universalEnvelopingAlgebraHom k V n).mem_range.mpr
        ⟨UniversalEnvelopingAlgebra.ι k b,
          UniversalEnvelopingAlgebra.lift_ι_apply k (endomorphismLieHom k V n) b⟩
    exact (h_cent_full.trans h_full_diag).trans h_diag_range
  ·
    rw [Subalgebra.le_centralizer_iff]
    apply Algebra.adjoin_le
    rintro _ ⟨σ, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := (universalEnvelopingAlgebraHom k V n).mem_range.mp hx
    set e := PiTensorProduct.reindex k (fun _ : Fin n => V) σ
    have hext : (e.conjAlgEquiv k).toAlgHom.comp
        (universalEnvelopingAlgebraHom k V n) =
        universalEnvelopingAlgebraHom k V n := by
      apply UniversalEnvelopingAlgebra.hom_ext; ext1 b
      simp only [LieHom.comp_apply, AlgHom.toLieHom_apply,
        AlgHom.comp_apply,
        universalEnvelopingAlgebraHom,
        UniversalEnvelopingAlgebra.lift_ι_apply]
      have h := endomorphismLieHom_commutes_reindex k V n b σ
      have he_inv : (↑e : Module.End k (auxiliarySpace k V n)) *
          ↑e.symm = 1 := by
        ext v; simp [Module.End.mul_eq_comp]
      change ↑e * endomorphismLieHom k V n b * ↑e.symm =
        endomorphismLieHom k V n b
      rw [h.symm, mul_assoc, he_inv, mul_one]
    have key := AlgHom.congr_fun hext y
    simp only [AlgHom.comp_apply] at key
    have key_mul : (↑e : Module.End k (auxiliarySpace k V n)) *
        (universalEnvelopingAlgebraHom k V n) y * ↑e.symm =
        (universalEnvelopingAlgebraHom k V n) y := by
      simp only [Module.End.mul_eq_comp]; exact key
    have he_inv : (↑e.symm : Module.End k (auxiliarySpace k V n)) *
        ↑e = 1 := by
      ext v; simp [Module.End.mul_eq_comp]
    have := congr_arg (· * (↑e : Module.End k _)) key_mul
    simp only [mul_assoc, he_inv, mul_one] at this
    exact this.symm

end RepresentationTheory.AuxiliaryEndomorphismActions
