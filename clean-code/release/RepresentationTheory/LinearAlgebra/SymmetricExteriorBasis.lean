/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero

/-!
# Bases from symmetric and exterior powers

This module constructs a tensor-product basis from symmetric-algebra monomials and exterior-power
basis vectors and records its coordinate formulas.
-/

universe u v w

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis

open RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex
  RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction
  RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-! ### Ranks in finite sets -/

section Position

variable {κ : Type w} [LinearOrder κ]

/-- Assigns to an element its order rank relative to a finite ordered set. -/
def Finset.rank (s : Finset κ) (a : κ) : ℕ := (s.filter (· < a)).card

/-- The rank of a member of a finite ordered set is strictly below its cardinality. -/
theorem Finset.rank_lt_card {s : Finset κ} {a : κ} (ha : a ∈ s) :
    Finset.rank s a < s.card := by
  classical
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  exact absurd (Finset.mem_filter.mp (hsub ha)).2 (lt_irrefl a)

/-- The finite-set order embedding sends the rank of a member back to that member. -/
theorem Finset.orderEmbOfFin_rank {s : Finset κ} {n : ℕ} (h : s.card = n)
    {a : κ} (ha : a ∈ s) :
    s.orderEmbOfFin h ⟨Finset.rank s a, h ▸ Finset.rank_lt_card ha⟩ = a := by
  classical
  obtain ⟨j, rfl⟩ : a ∈ Set.range (s.orderEmbOfFin h) := by
    rw [Finset.range_orderEmbOfFin]
    exact ha
  congr 1
  refine Fin.ext ?_
  change Finset.rank s (s.orderEmbOfFin h j) = (j : ℕ)
  have himg : s.filter (· < s.orderEmbOfFin h j) =
      Finset.map (s.orderEmbOfFin h).toEmbedding (Finset.univ.filter (· < j)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hxs, hxlt⟩
      obtain ⟨i, rfl⟩ : x ∈ Set.range (s.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hxs
      exact ⟨i, by simpa using hxlt, rfl⟩
    · rintro ⟨i, hij, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, by simpa using hij⟩
  have hIio : Finset.univ.filter (· < j) = Finset.Iio j := by
    ext i
    simp
  rw [Finset.rank, himg, Finset.card_map, hIio, Fin.card_Iio]

end Position

/-! ### Exterior-power coordinates -/

section Contraction

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- After removing a member, the order embedding agrees with skipping that member's rank. -/
theorem Finset.orderEmbOfFin_erase_succAbove_rank
    {s : Finset κ} {n : ℕ} (h : s.card = n + 1) {a : κ} (ha : a ∈ s)
    (herase : (s.erase a).card = n) :
    (fun i => s.orderEmbOfFin h
        ((⟨Finset.rank s a, h ▸ Finset.rank_lt_card ha⟩ : Fin (n + 1)).succAbove i)) =
      (s.erase a).orderEmbOfFin herase := by
  set j₀ : Fin (n + 1) := ⟨Finset.rank s a, h ▸ Finset.rank_lt_card ha⟩ with hj₀
  have hemb : s.orderEmbOfFin h j₀ = a := Finset.orderEmbOfFin_rank h ha
  refine Finset.orderEmbOfFin_unique _ (fun i => ?_) ?_
  · refine Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem _ _ _⟩
    rw [← hemb]
    exact fun hcon => (Fin.succAbove_ne j₀ i) ((s.orderEmbOfFin h).injective hcon)
  · exact (s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j₀)

omit [DecidableEq κ] in
/-- An exterior-power coordinate functional vanishes on a basis subset that omits its index. -/
theorem Module.Basis.exteriorPower_coordinate_apply_eq_zero_of_not_mem
    (b : Module.Basis κ k V) (a : κ) (n : ℕ)
    (s : Set.powersetCard κ (n + 1)) (ha : a ∉ (s : Finset κ)) :
    exteriorPowerContraction k (b.coord a) n (b.exteriorPower (n + 1) s) = 0 := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPowerContraction_unrenderedAux]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (b.coord a) (b (Set.powersetCard.ofFinEmbEquiv.symm s j)) = 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    rintro rfl
    exact ha (Finset.orderEmbOfFin_mem _ _ _)
  simp [Function.comp_apply, this]

/-- States the asserted relation between the displayed exterior-coordinate constructions. -/
theorem exteriorPower_coordinate_delete (b : Module.Basis κ k V) (a : κ) (n : ℕ)
    (s : Set.powersetCard κ (n + 1)) (ha : a ∈ (s : Finset κ))
    (herase : ((s : Finset κ).erase a).card = n) :
    exteriorPowerContraction k (b.coord a) n (b.exteriorPower (n + 1) s) =
      ((-1 : k) ^ (Finset.rank (s : Finset κ) a + 1)) •
        b.exteriorPower n
          ⟨(s : Finset κ).erase a, Set.powersetCard.mem_iff.mpr herase⟩ := by
  have hcard : (s : Finset κ).card = n + 1 := s.2
  have hlt : Finset.rank (s : Finset κ) a < n + 1 := by
    have := Finset.rank_lt_card ha
    omega
  set j₀ : Fin (n + 1) := ⟨Finset.rank (s : Finset κ) a, hlt⟩ with hj₀
  have hemb : (s : Finset κ).orderEmbOfFin hcard j₀ = a :=
    Finset.orderEmbOfFin_rank hcard ha
  have hsymm : (Set.powersetCard.ofFinEmbEquiv.symm s : Fin (n + 1) → κ) =
      (s : Finset κ).orderEmbOfFin hcard := rfl
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPowerContraction_unrenderedAux]
  rw [Finset.sum_eq_single j₀]
  · rw [hsymm, Function.comp_apply, hemb, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one]
    congr 1
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    have := Finset.orderEmbOfFin_erase_succAbove_rank hcard ha herase
    funext i
    exact congrArg b (congrFun this i)
  · intro j _ hj
    have hz : (b.coord a) (b ((s : Finset κ).orderEmbOfFin hcard j)) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
      intro hcon
      exact hj ((((s : Finset κ).orderEmbOfFin hcard).injective (hemb.trans hcon.symm)).symm)
    simp [hsymm, Function.comp_apply, hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Contraction

/-! ### Symmetric-algebra monomials -/

section Monomial

variable {κ : Type w}

/-- The symmetric-algebra basis vector at an exponent is the corresponding unit-coefficient
monomial. -/
theorem Module.Basis.symmetricAlgebra_apply_eq_monomial
    (b : Module.Basis κ k V) (α : κ →₀ ℕ) :
    b.symmetricAlgebra α =
      (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1) := by
  simp [Module.Basis.symmetricAlgebra]

/-- Multiplying a symmetric basis vector by a basis generator increments that generator's
exponent. -/
theorem Module.Basis.symmetricAlgebra_mul_apply
    (b : Module.Basis κ k V) (a : κ) (α : κ →₀ ℕ) :
    SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α =
      b.symmetricAlgebra (α + Finsupp.single a 1) := by
  have hι : SymmetricAlgebra.ι k V (b a) =
      (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X a) := by
    simp
  rw [hι, Module.Basis.symmetricAlgebra_apply_eq_monomial,
    Module.Basis.symmetricAlgebra_apply_eq_monomial, ← map_mul]
  congr 1
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm]

end Monomial

/-! ### The tensor-product basis -/

section KBasis

variable {κ : Type w} [LinearOrder κ]

variable (k V) in
/-- Constructs a tensor-product basis from the symmetric-algebra basis and an exterior-power
basis. -/
noncomputable def Module.Basis.symmetricExteriorTensor
    (b : Module.Basis κ k V) (i : ℕ) :
    Module.Basis ((κ →₀ ℕ) × Set.powersetCard κ i) k (degreeIndexedType k V i) :=
  (b.symmetricAlgebra).tensorProduct (b.exteriorPower i)

/-- A tensor basis vector is the pure tensor of its symmetric and exterior basis vectors. -/
@[simp]
theorem Module.Basis.symmetricExteriorTensor_apply
    (b : Module.Basis κ k V) (i : ℕ)
    (p : (κ →₀ ℕ) × Set.powersetCard κ i) :
    Module.Basis.symmetricExteriorTensor k V b i p =
      b.symmetricAlgebra p.1 ⊗ₜ[k] b.exteriorPower i p.2 :=
  Module.Basis.tensorProduct_apply _ _ _ _

variable [DecidableEq κ]

/-- Deletes a specified element from a finite subset whose cardinality is one greater. -/
def erase {i : ℕ} (s : Set.powersetCard κ (i + 1)) (a : (s : Finset κ)) :
    Set.powersetCard κ i :=
  ⟨(s : Finset κ).erase a, Set.powersetCard.mem_iff.mpr (by
    rw [Finset.card_erase_of_mem a.2, s.2]
    rfl)⟩

omit [LinearOrder κ] in
/-- The underlying finset of the deletion map is obtained by erasing the chosen member. -/
@[simp]
theorem erase_val {i : ℕ} (s : Set.powersetCard κ (i + 1)) (a : (s : Finset κ)) :
    (erase s a : Finset κ) = (s : Finset κ).erase a := rfl

variable [Fintype κ]

/-- States the asserted reindexing relation between the displayed tensor-basis constructions. -/
theorem Module.Basis.symmetricExteriorTensor_reindex
    (b : Module.Basis κ k V) (i : ℕ)
    (α : κ →₀ ℕ) (s : Set.powersetCard κ (i + 1)) :
    basisSymmetricAlgebraComplexDifferential b i
        (Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s)) =
      ∑ a ∈ (s : Finset κ).attach,
        ((-1 : k) ^ (Finset.rank (s : Finset κ) a + 1)) •
          Module.Basis.symmetricExteriorTensor k V b i
            (α + Finsupp.single (a : κ) 1, erase s a) := by
  classical
  rw [Module.Basis.symmetricExteriorTensor_apply,
    basisSymmetricAlgebraComplexDifferential_tmul]
  have hsub : ∑ a : κ, (SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α) ⊗ₜ[k]
        exteriorPowerContraction k (b.coord a) i (b.exteriorPower (i + 1) s) =
      ∑ a ∈ (s : Finset κ),
        (SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α) ⊗ₜ[k]
          exteriorPowerContraction k (b.coord a) i (b.exteriorPower (i + 1) s) :=
    (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => by
      rw [Module.Basis.exteriorPower_coordinate_apply_eq_zero_of_not_mem b a i s ha,
        TensorProduct.tmul_zero]).symm
  rw [hsub, ← Finset.sum_attach (s := (s : Finset κ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have herase : ((s : Finset κ).erase (a : κ)).card = i := by
    rw [Finset.card_erase_of_mem a.2, s.2]
    rfl
  rw [exteriorPower_coordinate_delete b (a : κ) i s a.2 herase,
    Module.Basis.symmetricAlgebra_mul_apply, TensorProduct.tmul_smul,
    Module.Basis.symmetricExteriorTensor_apply]
  rfl

omit [Fintype κ] in
/-- Evaluating the displayed scalar functional on a degree-zero tensor basis element is one exactly
at the zero exponent. -/
theorem Module.Basis.symmetricExteriorTensor_counit_apply
    (b : Module.Basis κ k V) (α : κ →₀ ℕ) (s : Set.powersetCard κ 0) :
    degreeZero.equivBaseRing k V
        (tensorToDegreeZero k V (Module.Basis.symmetricExteriorTensor k V b 0 (α, s))) =
      if α = 0 then 1 else 0 := by
  classical
  rw [Module.Basis.symmetricExteriorTensor_apply,
    equivBaseRing_tensorToDegreeZero_tmul,
    Module.Basis.symmetricAlgebra_apply_eq_monomial]
  have hε : SymmetricAlgebra.algebraMapInv
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1)) =
      if α = 0 then 1 else 0 := by
    have : SymmetricAlgebra.algebraMapInv (R := k) (M := V) =
        (MvPolynomial.aeval (fun _ : κ => (0 : k))).comp
          (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
      apply SymmetricAlgebra.algHom_ext
      apply b.ext
      intro j
      simp [SymmetricAlgebra.algebraMapInv_ι]
    rw [this]
    change MvPolynomial.aeval (fun _ : κ => (0 : k))
        ((SymmetricAlgebra.equivMvPolynomial b)
          ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1))) =
        if α = 0 then 1 else 0
    rw [AlgEquiv.apply_symm_apply, MvPolynomial.aeval_monomial, map_one, one_mul]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα]
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
        by_contra hcon
        exact hα (Finsupp.ext (by simpa using not_exists.mp hcon))
      refine Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr hj) ?_
      exact zero_pow hj
  rw [hε]
  by_cases hα : α = 0 <;>
    simp [hα, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.zeroEquiv_ιMulti]

end KBasis

end RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis
