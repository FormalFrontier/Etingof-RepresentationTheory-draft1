import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyCharacterRight

/-!
# Weight-space dimension of the right-`GL_N` polynomial representation `A_d`

This file computes the dimension of every torus weight space of the degree-`d`
homogeneous component `A_d = k[Xᵢⱼ]_d` under the right-`GL_N` action
(`polyRightDegreeFDRep`, `CauchyCharacterRight.lean`). This is sub-issue A of the
right-`GL_N` Cauchy character identity (#4944): the elementary, **weight-space
side**, requiring no Schur-Weyl theory.

The main result is

```
finrank k (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
  = if (∑ j, μ j) = d then ∏ j, Nat.choose (μ j + N - 1) (N - 1) else 0.
```

## Strategy

Every monomial `X^s` is a right-torus eigenvector
(`rTransAlgHom_diagonal_monomial`, `PolynomialGLRightAction.lean`): the diagonal
matrix `diagUnit k N i t` (which puts `t` at coordinate `i`, `1` elsewhere) scales
`X^s` by `t ^ (∑_l s (l, i))`, the `i`-th **column degree** of `s`. Hence the
weight space for `μ` is exactly the span of the degree-`d` monomials whose
column-degree vector is `μ`, and its dimension is the number of such monomials.
Choosing each column independently (stars and bars) gives
`∏_j C(μ_j + N − 1, N − 1)` monomials when `∑_j μ_j = d`, and none otherwise.
-/

namespace Etingof.CauchyWeightSpaceDimension

open _root_.MvPolynomial
open Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.CauchyCharacterRight

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The diagonal torus eigenvalue on a monomial -/

/-- The exponent product `∏_{(i',j')} (update 1 i t)_{j'}^{s(i',j')}` collapses to
the single power `t ^ (∑_l s(l,i))`: only the factors in column `i` carry `t`. -/
theorem prod_update_pow (i : Fin N) (t : kˣ) (s : (Fin N × Fin N) →₀ ℕ) :
    (s.prod fun p e => (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ e)
      = (t : k) ^ (∑ l, s (l, i)) := by
  classical
  have key : ∀ p ∈ s.support,
      (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ s p
        = (t : k) ^ (if p.2 = i then s p else 0) := by
    intro p _
    by_cases h : p.2 = i
    · rw [h, Function.update_self, if_pos rfl]
    · simp [h]
  rw [Finsupp.prod, Finset.prod_congr rfl key, Finset.prod_pow_eq_pow_sum]
  congr 1
  -- `∑ p ∈ support, (if p.2 = i then s p else 0) = ∑ l, s (l, i)`
  have hext : (∑ p ∈ s.support, (if p.2 = i then s p else 0))
      = ∑ p : Fin N × Fin N, (if p.2 = i then s p else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp, ite_self]
  rw [hext, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ i (fun b => s (a, b))]
  simp

/-- **The diagonal torus acts on a monomial by its column-degree weight.** The
group element `diagUnit k N i t` scales `monomial s c` by `t ^ (∑_l s(l,i))`. -/
theorem polyRightRep_diagUnit_monomial (i : Fin N) (t : kˣ)
    (s : (Fin N × Fin N) →₀ ℕ) (c : k) :
    polyRightRep k N (diagUnit k N i t) (monomial s c)
      = (t : k) ^ (∑ l, s (l, i)) • monomial s c := by
  rw [polyRightRep_apply]
  change rTransAlgHom (Matrix.diagonal (Function.update 1 i (t : k))) (monomial s c) = _
  rw [rTransAlgHom_diagonal_monomial, prod_update_pow]

/-- **Coefficient extraction for the diagonal torus action.** Since `diagUnit k N i t`
acts diagonally in the monomial basis, the `s`-coefficient of `R_{diagUnit i t} x`
is the `s`-coefficient of `x` scaled by the eigenvalue `t ^ (∑_l s(l,i))`. -/
theorem coeff_polyRightRep_diagUnit (i : Fin N) (t : kˣ)
    (x : MvPolynomial (Fin N × Fin N) k) (s : (Fin N × Fin N) →₀ ℕ) :
    coeff s (polyRightRep k N (diagUnit k N i t) x)
      = (t : k) ^ (∑ l, s (l, i)) * coeff s x := by
  classical
  conv_lhs => rw [x.as_sum, map_sum]
  simp_rw [polyRightRep_diagUnit_monomial, coeff_sum, coeff_smul, coeff_monomial,
    smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' x.support s (fun s' => (t : k) ^ (∑ l, s' (l, i)) * coeff s' x)]
  split_ifs with hs
  · rfl
  · rw [notMem_support_iff.mp hs, mul_zero]

/-! ### The weight space as the span of column-degree-`μ` monomials -/

/-- The `k`-linear inclusion of the carrier `A_d` of `polyRightDegreeFDRep` into the
polynomial ring `k[Xᵢⱼ]`. It is the subtype map of the homogeneous component. -/
noncomputable def polyOf (d : ℕ) :
    polyRightDegreeFDRep k N d →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  (homogeneousSubmodule (Fin N × Fin N) k d).subtype

theorem polyOf_injective (d : ℕ) : Function.Injective (polyOf (k := k) (N := N) d) :=
  Subtype.coe_injective

theorem polyOf_mem (d : ℕ) (w : polyRightDegreeFDRep k N d) :
    polyOf d w ∈ homogeneousSubmodule (Fin N × Fin N) k d :=
  w.2

/-- The underlying polynomial of the right action on `A_d` is `polyRightRep`. -/
theorem polyOf_rho (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (w : polyRightDegreeFDRep k N d) :
    polyOf d ((polyRightDegreeFDRep k N d).ρ g w) = polyRightRep k N g (polyOf d w) :=
  rfl

variable [IsAlgClosed k]

/-- **Membership in the weight space, read on the underlying polynomial.** A vector
`w ∈ A_d` lies in the `μ`-weight space iff for every diagonal torus element the
right action multiplies `↑w` by the eigenvalue `t ^ μ i`. -/
theorem mem_glWeightSpace_polyRight_iff (d : ℕ) (μ : Fin N → ℕ)
    (w : polyRightDegreeFDRep k N d) :
    w ∈ glWeightSpace k N (polyRightDegreeFDRep k N d) μ
      ↔ ∀ (i : Fin N) (t : kˣ),
          polyRightRep k N (diagUnit k N i t) (polyOf d w)
            = (t : k) ^ μ i • polyOf d w := by
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [← polyOf_rho, ← map_smul]
  exact ⟨fun h => by rw [h], fun h => polyOf_injective d h⟩

/-- The finite set of degree-`d` monomial exponents whose column-degree vector is
`μ`: `s` with `∑_p s p = d` and `∑_i s(i,j) = μ_j` for every column `j`. -/
def Dset (N d : ℕ) (μ : Fin N → ℕ) : Finset ((Fin N × Fin N) →₀ ℕ) :=
  (Finset.univ.finsuppAntidiag d).filter (fun s => ∀ j, ∑ i, s (i, j) = μ j)

theorem mem_Dset (d : ℕ) (μ : Fin N → ℕ) (s : (Fin N × Fin N) →₀ ℕ) :
    s ∈ Dset N d μ ↔ (∑ p, s p = d) ∧ ∀ j, ∑ i, s (i, j) = μ j := by
  simp only [Dset, Finset.mem_filter, Finset.mem_finsuppAntidiag]
  constructor
  · rintro ⟨⟨hsum, _⟩, hcol⟩; exact ⟨hsum, hcol⟩
  · rintro ⟨hsum, hcol⟩; exact ⟨⟨hsum, Finset.subset_univ _⟩, hcol⟩

omit [IsAlgClosed k] in
/-- A degree-`d` monomial lies in the homogeneous component `A_d`. -/
theorem monomial_mem_homog (d : ℕ) (s : (Fin N × Fin N) →₀ ℕ) (hs : ∑ p, s p = d) :
    (monomial s (1 : k)) ∈ homogeneousSubmodule (Fin N × Fin N) k d := by
  rw [mem_homogeneousSubmodule]
  exact isHomogeneous_monomial 1 (by rw [Finsupp.degree_eq_sum]; exact hs)

/-- **The `μ`-weight space of `A_d` maps onto the span of its column-degree-`μ`
monomials.** Pushing the weight space into `k[Xᵢⱼ]` recovers exactly the span of
the degree-`d` monomials with column-degree vector `μ`. -/
theorem map_polyOf_glWeightSpace (d : ℕ) (μ : Fin N → ℕ) :
    Submodule.map (polyOf d) (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
      = Submodule.span k ((fun s => monomial s (1 : k)) '' (Dset N d μ : Set _)) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    replace hw := (mem_glWeightSpace_polyRight_iff d μ w).mp hw
    rw [(polyOf d w).as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    -- each monomial in the support has column degree `μ`, hence is a generator
    have hsDset : s ∈ Dset N d μ := by
      rw [mem_Dset]
      refine ⟨?_, fun j => ?_⟩
      · -- degree
        have hH : (polyOf d w).IsHomogeneous d := polyOf_mem d w
        have hd := hH (MvPolynomial.mem_support_iff.mp hs)
        calc ∑ p, s p = s.degree := (Finsupp.degree_eq_sum s).symm
          _ = Finsupp.weight (fun _ => 1) s := by rw [Finsupp.degree_eq_weight_one]
          _ = d := hd
      · -- column degree
        by_contra hne
        obtain ⟨t, ht⟩ := exists_unit_pow_ne k hne
        have key := congrArg (coeff s) (hw j t)
        rw [coeff_polyRightRep_diagUnit, coeff_smul, smul_eq_mul] at key
        exact ht (mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hs) key)
    have hsmul : (monomial s (coeff s (polyOf d w)) : MvPolynomial (Fin N × Fin N) k)
        = coeff s (polyOf d w) • monomial s 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hsmul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨s, Finset.mem_coe.mpr hsDset, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [Finset.mem_coe, mem_Dset] at hs
    obtain ⟨hdeg, hcol⟩ := hs
    refine ⟨⟨monomial s 1, monomial_mem_homog d s hdeg⟩,
      (mem_glWeightSpace_polyRight_iff d μ _).mpr (fun i t => ?_), rfl⟩
    change polyRightRep k N (diagUnit k N i t) (monomial s (1 : k))
      = (t : k) ^ μ i • monomial s (1 : k)
    rw [polyRightRep_diagUnit_monomial, hcol i]

/-- **The weight-space dimension equals the number of column-degree-`μ` monomials.**
The pushforward isomorphism plus linear independence of distinct monomials. -/
theorem finrank_glWeightSpace_eq_card (d : ℕ) (μ : Fin N → ℕ) :
    Module.finrank k (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
      = (Dset N d μ).card := by
  have hrange : (fun s => monomial s (1 : k)) '' (Dset N d μ : Set _)
      = Set.range (fun s : (Dset N d μ) => monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
    rw [show (fun s : (Dset N d μ) => monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k))
          = (fun s => monomial s (1 : k)) ∘ Subtype.val from rfl,
        Set.range_comp, Subtype.range_coe]
  have hli : LinearIndependent k
      (fun s : (Dset N d μ) => monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
    have hb := (basisMonomials (Fin N × Fin N) k).linearIndependent.comp
      (fun s : (Dset N d μ) => (s : (Fin N × Fin N) →₀ ℕ)) Subtype.val_injective
    have hfun : (fun s : (Dset N d μ) => monomial (s : (Fin N × Fin N) →₀ ℕ) (1 : k))
        = ⇑(basisMonomials (Fin N × Fin N) k) ∘
            (fun s : (Dset N d μ) => (s : (Fin N × Fin N) →₀ ℕ)) := by
      funext s; simp [coe_basisMonomials]
    rw [hfun]; exact hb
  rw [(Submodule.equivMapOfInjective (polyOf d) (polyOf_injective d)
        (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)).finrank_eq,
      map_polyOf_glWeightSpace, hrange, finrank_span_eq_card hli, Fintype.card_coe]

/-! ### Counting the column-degree-`μ` monomials (stars and bars) -/

/-- **Stars and bars.** The number of `N`-tuples of naturals summing to `m` is the
multichoose number `multichoose N m = C(m + N − 1, N − 1)`. -/
theorem card_piAntidiag_univ (m : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin N)) m).card = Nat.multichoose N m := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ]
  exact Sym.card_sym_fin_eq_multichoose N m

omit [IsAlgClosed k] in
/-- `multichoose N m = C(m + N − 1, N − 1)` for `N ≥ 1`. -/
theorem multichoose_eq_choose (m : ℕ) (hN : 1 ≤ N) :
    Nat.multichoose N m = (m + N - 1).choose (N - 1) := by
  rw [Nat.multichoose_eq, Nat.add_comm N m]
  have hsub : m + N - 1 - m = N - 1 := by omega
  rw [← hsub, Nat.choose_symm (by omega)]

/-- **The count of column-degree-`μ` monomials.** When `∑_j μ_j = d`, choosing each
column independently gives `∏_j C(μ_j + N − 1, N − 1)`; otherwise no degree-`d`
monomial has column-degree vector `μ`. -/
theorem card_Dset (d : ℕ) (μ : Fin N → ℕ) :
    (Dset N d μ).card
      = if (∑ j, μ j) = d then ∏ j, (μ j + N - 1).choose (N - 1) else 0 := by
  split_ifs with hd
  · -- d = ∑ μ
    rw [← hd]
    have hbij : (Dset N (∑ j, μ j) μ).card
        = (Fintype.piFinset
            (fun j => Finset.piAntidiag (Finset.univ : Finset (Fin N)) (μ j))).card := by
      refine Finset.card_nbij' (fun s => fun j i => s (i, j))
        (fun g => Finsupp.equivFunOnFinite.symm (fun p => g p.2 p.1)) ?_ ?_ ?_ ?_
      · -- MapsTo forward
        intro s hs
        rw [Finset.mem_coe, mem_Dset] at hs
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro j
        rw [Finset.mem_piAntidiag]
        exact ⟨hs.2 j, fun i _ => Finset.mem_univ i⟩
      · -- MapsTo backward
        intro g hg
        rw [Finset.mem_coe, Fintype.mem_piFinset] at hg
        rw [Finset.mem_coe, mem_Dset]
        have hcol : ∀ j, ∑ i, g j i = μ j := fun j =>
          (Finset.mem_piAntidiag.mp (hg j)).1
        refine ⟨?_, fun j => ?_⟩
        · rw [Fintype.sum_prod_type]
          simp only [Finsupp.coe_equivFunOnFinite_symm]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => hcol j
        · simp only [Finsupp.coe_equivFunOnFinite_symm]
          exact hcol j
      · -- left inverse
        intro s _
        change Finsupp.equivFunOnFinite.symm (fun p : Fin N × Fin N => s (p.1, p.2)) = s
        rw [show (fun p : Fin N × Fin N => s (p.1, p.2)) = (s : Fin N × Fin N → ℕ) from
          funext fun p => by rw [Prod.mk.eta]]
        exact Finsupp.equivFunOnFinite_symm_coe s
      · -- right inverse
        intro g _
        funext j i
        simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [hbij, Fintype.card_piFinset]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [card_piAntidiag_univ, multichoose_eq_choose (μ j) (Fin.pos j)]
  · -- ∑ μ ≠ d: the set is empty
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    rw [mem_Dset] at hs
    apply hd
    rw [← hs.1, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (hs.2 j).symm

/-! ### The weight-space dimension formula -/

/-- **Weight-space dimension of `A_d` (sub-issue A of #4944).** The `μ`-weight space
of the right-`GL_N` representation `A_d = k[Xᵢⱼ]_d` has dimension
`∏_j C(μ_j + N − 1, N − 1)` when `∑_j μ_j = d` (the number of degree-`d` monomials
with column-degree vector `μ`), and is zero otherwise. -/
theorem finrank_glWeightSpace_polyRightDegreeFDRep (d : ℕ) (μ : Fin N → ℕ) :
    Module.finrank k (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
      = if (∑ j, μ j) = d then ∏ j, (μ j + N - 1).choose (N - 1) else 0 := by
  rw [finrank_glWeightSpace_eq_card, card_Dset]

/-- The `μ`-coefficient of the formal character of `A_d` is the same count. -/
theorem formalCharacter_polyRightDegreeFDRep_coeff (d : ℕ) (μ : Fin N →₀ ℕ) :
    (formalCharacter k N (polyRightDegreeFDRep k N d)).coeff μ
      = if (∑ j, μ j) = d then ((∏ j, (μ j + N - 1).choose (N - 1) : ℕ) : ℚ) else 0 := by
  rw [formalCharacter_coeff, finrank_glWeightSpace_polyRightDegreeFDRep]
  split_ifs with h
  · push_cast; rfl
  · rfl

end Etingof.CauchyWeightSpaceDimension
