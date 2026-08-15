/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations

set_option linter.style.longLine false

namespace RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding

open _root_.MvPolynomial
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
  RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
  RepresentationTheory.MatrixPolynomialHomogeneity
  RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations

variable {k : Type*} [Field k] {N : ℕ}

/-- A finitely supported product of an updated function on second coordinates reduces to a power whose exponent is the selected column sum. -/
theorem finsupp_prod_update_snd_eq_pow_sum
    (i : Fin N) (t : kˣ) (s : (Fin N × Fin N) →₀ ℕ) :
    (s.prod fun p e => (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ e) =
      (t : k) ^ (∑ l, s (l, i)) := by
  classical
  have key : ∀ p ∈ s.support,
      (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ s p =
        (t : k) ^ (if p.2 = i then s p else 0) := by
    intro p _
    by_cases h : p.2 = i
    · rw [h, Function.update_self, if_pos rfl]
    · simp [h]
  rw [Finsupp.prod, Finset.prod_congr rfl key, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hext : (∑ p ∈ s.support, (if p.2 = i then s p else 0)) =
      ∑ p : Fin N × Fin N, (if p.2 = i then s p else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp, ite_self]
  rw [hext, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ i (fun b => s (a, b))]
  simp

/-- The displayed action at a coordinate-indexed auxiliary group element scales a monomial by the unit raised to the corresponding column sum. -/
theorem auxiliaryAction_monomial (i : Fin N) (t : kˣ)
    (s : (Fin N × Fin N) →₀ ℕ) (c : k) :
    generalLinearGroupMvPolynomialRightMul k N (diagonalUnit k N i t) (monomial s c) =
      (t : k) ^ (∑ l, s (l, i)) • monomial s c := by
  rw [generalLinearGroupMvPolynomialRightMul_apply]
  change mvPolynomialRightMul (Matrix.diagonal (Function.update 1 i (t : k)))
    (monomial s c) = _
  rw [mvPolynomialRightMul_diagonal_apply_monomial,
    finsupp_prod_update_snd_eq_pow_sum]

/-- Under the displayed action at a coordinate-indexed auxiliary group element, each polynomial coefficient is scaled by the corresponding power of the unit. -/
theorem coeff_auxiliaryAction (i : Fin N) (t : kˣ)
    (x : MvPolynomial (Fin N × Fin N) k) (s : (Fin N × Fin N) →₀ ℕ) :
    coeff s (generalLinearGroupMvPolynomialRightMul k N (diagonalUnit k N i t) x) =
      (t : k) ^ (∑ l, s (l, i)) * coeff s x := by
  classical
  conv_lhs => rw [x.as_sum, map_sum]
  simp_rw [auxiliaryAction_monomial, coeff_sum, coeff_smul, coeff_monomial,
    smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' x.support s
    (fun s' => (t : k) ^ (∑ l, s' (l, i)) * coeff s' x)]
  split_ifs with hs
  · rfl
  · rw [notMem_support_iff.mp hs, mul_zero]

/-- An auxiliary linear map from the displayed indexed representation into matrix-variable multivariate polynomials. -/
noncomputable def auxiliaryPolynomialEmbedding (d : ℕ) :
    auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k]
      MvPolynomial (Fin N × Fin N) k :=
  (homogeneousSubmodule (Fin N × Fin N) k d).subtype

/-- The auxiliary polynomial map from the displayed indexed representation is injective. -/
theorem auxiliaryPolynomialEmbedding_injective (d : ℕ) :
    Function.Injective (auxiliaryPolynomialEmbedding (k := k) (N := N) d) :=
  Subtype.coe_injective

/-- Every polynomial in the image of the auxiliary map is homogeneous of the indexed degree. -/
theorem auxiliaryPolynomialEmbedding_mem_homogeneousSubmodule
    (d : ℕ) (w : auxiliaryIndexedGeneralLinearFDRep k N d) :
    auxiliaryPolynomialEmbedding d w ∈ homogeneousSubmodule (Fin N × Fin N) k d :=
  w.2

/-- The auxiliary polynomial embedding intertwines the two displayed general linear group actions. -/
theorem auxiliaryPolynomialEmbedding_groupAction
    (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (w : auxiliaryIndexedGeneralLinearFDRep k N d) :
    auxiliaryPolynomialEmbedding d
        ((auxiliaryIndexedGeneralLinearFDRep k N d).ρ g w) =
      generalLinearGroupMvPolynomialRightMul k N g (auxiliaryPolynomialEmbedding d w) :=
  rfl

variable [IsAlgClosed k]

/-- Membership in the auxiliary submodule is equivalent to the embedded polynomial scaling by the prescribed power under each displayed coordinate-indexed action. -/
theorem mem_auxiliarySubmodule_iff_auxiliaryPolynomialEmbedding_action
    (d : ℕ) (μ : Fin N → ℕ)
    (w : auxiliaryIndexedGeneralLinearFDRep k N d) :
    w ∈ weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ ↔
      ∀ (i : Fin N) (t : kˣ),
        generalLinearGroupMvPolynomialRightMul k N (diagonalUnit k N i t)
            (auxiliaryPolynomialEmbedding d w) =
          (t : k) ^ μ i • auxiliaryPolynomialEmbedding d w := by
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [← auxiliaryPolynomialEmbedding_groupAction, ← map_smul]
  exact ⟨fun h => by rw [h], fun h => auxiliaryPolynomialEmbedding_injective d h⟩

/-- An auxiliary finite set of matrix-indexed finitely supported natural-number exponents. -/
def auxiliaryMatrixExponentFinset
    (N d : ℕ) (μ : Fin N → ℕ) : Finset ((Fin N × Fin N) →₀ ℕ) :=
  (Finset.univ.finsuppAntidiag d).filter (fun s => ∀ j, ∑ i, s (i, j) = μ j)

/-- Membership in the auxiliary exponent set is equivalent to having the specified total degree and prescribed column sums. -/
theorem mem_auxiliaryMatrixExponentFinset_iff
    (d : ℕ) (μ : Fin N → ℕ) (s : (Fin N × Fin N) →₀ ℕ) :
    s ∈ auxiliaryMatrixExponentFinset N d μ ↔
      (∑ p, s p = d) ∧ ∀ j, ∑ i, s (i, j) = μ j := by
  simp only [auxiliaryMatrixExponentFinset, Finset.mem_filter,
    Finset.mem_finsuppAntidiag]
  constructor
  · rintro ⟨⟨hsum, _⟩, hcol⟩; exact ⟨hsum, hcol⟩
  · rintro ⟨hsum, hcol⟩; exact ⟨⟨hsum, Finset.subset_univ _⟩, hcol⟩

omit [IsAlgClosed k] in
/-- A monomial whose exponent sum is the given degree belongs to the corresponding homogeneous polynomial submodule. -/
theorem monomial_mem_homogeneousSubmodule
    (d : ℕ) (s : (Fin N × Fin N) →₀ ℕ) (hs : ∑ p, s p = d) :
    (monomial s (1 : k)) ∈ homogeneousSubmodule (Fin N × Fin N) k d := by
  rw [mem_homogeneousSubmodule]
  exact isHomogeneous_monomial 1 (by rw [Finsupp.degree_eq_sum]; exact hs)

/-- The image of the indicated auxiliary submodule under the auxiliary polynomial embedding is spanned by monomials from the corresponding exponent set. -/
theorem map_auxiliarySubmodule_auxiliaryPolynomialEmbedding (d : ℕ) (μ : Fin N → ℕ) :
    Submodule.map (auxiliaryPolynomialEmbedding d)
        (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ) =
      Submodule.span k ((fun s => monomial s (1 : k)) ''
        (auxiliaryMatrixExponentFinset N d μ : Set _)) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    replace hw :=
      (mem_auxiliarySubmodule_iff_auxiliaryPolynomialEmbedding_action d μ w).mp hw
    rw [(auxiliaryPolynomialEmbedding d w).as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsDset : s ∈ auxiliaryMatrixExponentFinset N d μ := by
      rw [mem_auxiliaryMatrixExponentFinset_iff]
      refine ⟨?_, fun j => ?_⟩
      · have hH : (auxiliaryPolynomialEmbedding d w).IsHomogeneous d :=
          auxiliaryPolynomialEmbedding_mem_homogeneousSubmodule d w
        have hd := hH (MvPolynomial.mem_support_iff.mp hs)
        calc ∑ p, s p = s.degree := (Finsupp.degree_eq_sum s).symm
          _ = Finsupp.weight (fun _ => 1) s := by rw [Finsupp.degree_eq_weight_one]
          _ = d := hd
      · by_contra hne
        obtain ⟨t, ht⟩ := exists_unit_pow_ne_pow k hne
        have key := congrArg (coeff s) (hw j t)
        rw [coeff_auxiliaryAction, coeff_smul, smul_eq_mul] at key
        exact ht (mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hs) key)
    have hsmul :
        (monomial s (coeff s (auxiliaryPolynomialEmbedding d w)) :
            MvPolynomial (Fin N × Fin N) k) =
          coeff s (auxiliaryPolynomialEmbedding d w) • monomial s 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hsmul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨s, Finset.mem_coe.mpr hsDset, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [Finset.mem_coe, mem_auxiliaryMatrixExponentFinset_iff] at hs
    obtain ⟨hdeg, hcol⟩ := hs
    refine ⟨⟨monomial s 1, monomial_mem_homogeneousSubmodule d s hdeg⟩,
      (mem_auxiliarySubmodule_iff_auxiliaryPolynomialEmbedding_action d μ _).mpr
        (fun i t => ?_), rfl⟩
    change generalLinearGroupMvPolynomialRightMul k N (diagonalUnit k N i t)
        (monomial s (1 : k)) = (t : k) ^ μ i • monomial s (1 : k)
    rw [auxiliaryAction_monomial, hcol i]

/-- The dimension of the indicated auxiliary submodule equals the cardinality of the auxiliary matrix-exponent set. -/
theorem finrank_auxiliarySubmodule_eq_card_auxiliaryMatrixExponentFinset
    (d : ℕ) (μ : Fin N → ℕ) :
    Module.finrank k (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ) =
      (auxiliaryMatrixExponentFinset N d μ).card := by
  have hrange :
      (fun s => monomial s (1 : k)) ''
          (auxiliaryMatrixExponentFinset N d μ : Set _) =
        Set.range (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
          monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
    rw [show (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
          monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) =
        (fun s => monomial s (1 : k)) ∘ Subtype.val from rfl,
      Set.range_comp, Subtype.range_coe]
  have hli : LinearIndependent k
      (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
        monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
    have hb := (basisMonomials (Fin N × Fin N) k).linearIndependent.comp
      (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
        (s : (Fin N × Fin N) →₀ ℕ)) Subtype.val_injective
    have hfun : (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
        monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) =
      ⇑(basisMonomials (Fin N × Fin N) k) ∘
        (fun s : (auxiliaryMatrixExponentFinset N d μ) =>
          (s : (Fin N × Fin N) →₀ ℕ)) := by
      funext s; simp [coe_basisMonomials]
    rw [hfun]; exact hb
  rw [(Submodule.equivMapOfInjective (auxiliaryPolynomialEmbedding d)
        (auxiliaryPolynomialEmbedding_injective d)
        (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ)).finrank_eq,
    map_auxiliarySubmodule_auxiliaryPolynomialEmbedding, hrange,
    finrank_span_eq_card hli, Fintype.card_coe]

/-- The finitely supported antidiagonal over a finite index type has cardinality given by multichoose. -/
theorem card_piAntidiag_eq_multichoose (m : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin N)) m).card =
      Nat.multichoose N m := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
    Finset.card_univ]
  exact Sym.card_sym_fin_eq_multichoose N m

omit [IsAlgClosed k] in
/-- For a positive number of choices, multichoose is an ordinary binomial coefficient with shifted upper argument. -/
theorem multichoose_eq_choose_add_sub_one (m : ℕ) (hN : 1 ≤ N) :
    Nat.multichoose N m = (m + N - 1).choose (N - 1) := by
  rw [Nat.multichoose_eq, Nat.add_comm N m]
  have hsub : m + N - 1 - m = N - 1 := by omega
  rw [← hsub, Nat.choose_symm (by omega)]

/-- The auxiliary exponent set has the displayed product cardinality when the coordinate sum matches the degree, and is empty otherwise. -/
theorem card_auxiliaryMatrixExponentFinset (d : ℕ) (μ : Fin N → ℕ) :
    (auxiliaryMatrixExponentFinset N d μ).card =
      if (∑ j, μ j) = d then ∏ j, (μ j + N - 1).choose (N - 1) else 0 := by
  split_ifs with hd
  · rw [← hd]
    have hbij : (auxiliaryMatrixExponentFinset N (∑ j, μ j) μ).card =
        (Fintype.piFinset
          (fun j => Finset.piAntidiag (Finset.univ : Finset (Fin N)) (μ j))).card := by
      refine Finset.card_nbij' (fun s => fun j i => s (i, j))
        (fun g => Finsupp.equivFunOnFinite.symm (fun p => g p.2 p.1)) ?_ ?_ ?_ ?_
      · intro s hs
        rw [Finset.mem_coe, mem_auxiliaryMatrixExponentFinset_iff] at hs
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro j
        rw [Finset.mem_piAntidiag]
        exact ⟨hs.2 j, fun i _ => Finset.mem_univ i⟩
      · intro g hg
        rw [Finset.mem_coe, Fintype.mem_piFinset] at hg
        rw [Finset.mem_coe, mem_auxiliaryMatrixExponentFinset_iff]
        have hcol : ∀ j, ∑ i, g j i = μ j := fun j =>
          (Finset.mem_piAntidiag.mp (hg j)).1
        refine ⟨?_, fun j => ?_⟩
        · rw [Fintype.sum_prod_type]
          simp only [Finsupp.coe_equivFunOnFinite_symm]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => hcol j
        · simp only [Finsupp.coe_equivFunOnFinite_symm]
          exact hcol j
      · intro s _
        change Finsupp.equivFunOnFinite.symm
          (fun p : Fin N × Fin N => s (p.1, p.2)) = s
        rw [show (fun p : Fin N × Fin N => s (p.1, p.2)) =
          (s : Fin N × Fin N → ℕ) from funext fun p => by rw [Prod.mk.eta]]
        exact Finsupp.equivFunOnFinite_symm_coe s
      · intro g _
        funext j i
        simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [hbij, Fintype.card_piFinset]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [card_piAntidiag_eq_multichoose,
      multichoose_eq_choose_add_sub_one (μ j) (Fin.pos j)]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    rw [mem_auxiliaryMatrixExponentFinset_iff] at hs
    apply hd
    rw [← hs.1, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (hs.2 j).symm

/-- The auxiliary-submodule dimension is the displayed product of binomial coefficients when the index sum is the degree, and zero otherwise. -/
theorem finrank_auxiliarySubmodule (d : ℕ) (μ : Fin N → ℕ) :
    Module.finrank k
        (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ) =
      if (∑ j, μ j) = d then ∏ j, (μ j + N - 1).choose (N - 1) else 0 := by
  rw [finrank_auxiliarySubmodule_eq_card_auxiliaryMatrixExponentFinset,
    card_auxiliaryMatrixExponentFinset]

/-- A coefficient of the auxiliary polynomial for the displayed indexed representation is the stated binomial product when its total degree matches, and zero otherwise. -/
theorem auxiliaryPolynomial_coeff (d : ℕ) (μ : Fin N →₀ ℕ) :
    (weightCharacter k N (auxiliaryIndexedGeneralLinearFDRep k N d)).coeff μ =
      if (∑ j, μ j) = d then
        ((∏ j, (μ j + N - 1).choose (N - 1) : ℕ) : ℚ) else 0 := by
  rw [coeff_weightCharacter, finrank_auxiliarySubmodule]
  split_ifs with h
  · push_cast; rfl
  · rfl

end RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
