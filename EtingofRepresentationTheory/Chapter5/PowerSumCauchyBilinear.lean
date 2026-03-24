import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyIdentity
import EtingofRepresentationTheory.Chapter5.Theorem5_14_3

/-!
# Power Sum Cauchy Identity: Bilinear Version

This file establishes the bilinear power sum Cauchy identity:

  ∑_{σ∈S_n} P_σ(x) P_σ(y) = n! · [deg (n,n)] ∏_{i,j} 1/(1-xᵢyⱼ)

where P_σ(x) = `cycleTypePsumProduct n σ` is the product of power sum symmetric polynomials
indexed by the cycle type of σ.

## Proof strategy

The identity follows from a double-counting argument. Both sides count the same set
`ElementBicoloring n α β` (element-level bicolorings compatible with some permutation):

- **LHS grouping**: Group by permutation σ, count compatible bicolorings for each σ.
  This gives ∑_σ #{cycle colorings for α} × #{cycle colorings for β}.
- **RHS grouping**: Group by the induced matrix K (with row sums α, col sums β).
  For each K, there are n!/∏K_{ij}! multinomial partitions × ∏K_{ij}! block permutations = n!.
  Total: n! × #{matrices with given margins}.

## Application to Frobenius character formula

Combined with `cauchyRHS_coeff_diag` and the Cauchy determinant formula, this gives:

  ∑_σ ([x^{λ+ρ}](Δ P_σ))² = n! · [x^{λ+ρ} y^{λ+ρ}](cauchyRHS) = n!

which (via character orthogonality) implies `∑_ν L²_{νλ} = 1`.
-/

open Finset Equiv.Perm MvPowerSeries Etingof

noncomputable section

namespace Etingof

variable (N : ℕ)

/-! ### Bilinear exponent infrastructure -/

/-- The bilinear exponent: maps `Sum.inl j ↦ α j` and `Sum.inr j ↦ β j`.
Generalizes `diagExponent` which uses `α = β`. -/
def bilinExponent (α β : Fin N → ℕ) : CauchyVars N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim α β)

@[simp]
theorem bilinExponent_inl (α β : Fin N → ℕ) (i : Fin N) :
    bilinExponent N α β (Sum.inl i) = α i := by
  simp [bilinExponent, Finsupp.equivFunOnFinite]

@[simp]
theorem bilinExponent_inr (α β : Fin N → ℕ) (j : Fin N) :
    bilinExponent N α β (Sum.inr j) = β j := by
  simp [bilinExponent, Finsupp.equivFunOnFinite]

theorem diagExponent_eq_bilinExponent (α : Fin N → ℕ) :
    diagExponent N α = bilinExponent N α α := by
  ext v; cases v <;> simp [diagExponent, bilinExponent, Finsupp.equivFunOnFinite]

/-! ### cauchyRHS coefficient formulas -/

/-- General coefficient formula for `cauchyRHS`:

  [x^α y^β](cauchyRHS) = ∑_σ sign(σ) · [∀j, α_j = β_{σ(j)}]

This follows from `cauchyProd_coeff_perm` by distributing over the signed sum. -/
theorem cauchyRHS_coeff_general (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) :
    MvPowerSeries.coeff (R := k) (bilinExponent N α β) (cauchyRHS N k) =
    ∑ σ : Equiv.Perm (Fin N),
      (Int.cast (Equiv.Perm.sign σ : ℤ) : k) *
        if (∀ j : Fin N, α j = β (σ j)) then 1 else 0 := by
  simp only [cauchyRHS, map_sum]
  congr 1; ext σ
  rw [MvPowerSeries.coeff_C_mul, cauchyProd_coeff_perm N k σ (bilinExponent N α β)]
  simp only [bilinExponent_inl, bilinExponent_inr]

/-- For `α = β` both injective, the cauchyRHS coefficient at `(α, β)` is 1. -/
theorem cauchyRHS_coeff_bilin_of_injective (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) (_hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : ∀ j, α j = β j) :
    MvPowerSeries.coeff (R := k) (bilinExponent N α β) (cauchyRHS N k) = 1 := by
  rw [cauchyRHS_coeff_general]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = β (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext j
      simp only [Equiv.Perm.coe_one, id_eq]
      exact congr_arg Fin.val (hβ ((hαβ j).symm.trans (h1 j))).symm
    · exfalso; apply h1; intro j; subst h2
      simp only [Equiv.Perm.coe_one, id_eq]; exact hαβ j
    · rfl
  simp_rw [key]
  simp [Finset.sum_ite_eq']

/-! ### Full Cauchy product -/

/-- The full Cauchy product ∏_{i,j} 1/(1-xᵢyⱼ) as an MvPowerSeries. -/
def fullCauchyProd (n : ℕ) (k : Type*) [CommRing k] : MvPowerSeries (CauchyVars n) k :=
  ∏ i : Fin n, ∏ j : Fin n,
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
           MvPowerSeries.X (Sum.inr j : CauchyVars n))
      1

/-! ### Coefficient formula for the full Cauchy product

The coefficient of x^α y^β in ∏_{i,j} 1/(1-xᵢyⱼ) counts the number of
non-negative integer matrices with row sums α and column sums β.
-/

/-- A non-negative integer matrix with prescribed row and column sums.
Entries are bounded by `n + 1` (since row sums equal α_i ≤ n) to ensure finiteness. -/
def NNMatrixWithMargins (n : ℕ) (α β : Fin n → ℕ) : Type :=
  { K : Fin n → Fin n → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

instance (n : ℕ) (α β : Fin n → ℕ) : Fintype (NNMatrixWithMargins n α β) :=
  Subtype.fintype _

/-- The coefficient of x^α y^β in the full Cauchy product equals the number of
non-negative integer matrices with row sums α and column sums β. -/
theorem fullCauchyProd_coeff_eq_card (n : ℕ) (α β : Fin n → ℕ) :
    MvPowerSeries.coeff (bilinExponent n α β) (fullCauchyProd n ℂ) =
    ↑(Fintype.card (NNMatrixWithMargins n α β)) := by
  sorry

/-! ### Counting argument: the core of the proof

The key identity is proved by double counting. Define:
- An "element bicoloring" is a function h : Fin n → Fin n × Fin n
  together with a permutation σ that is compatible (monochromatic) with h.
- Grouping by σ gives ∑_σ #{cycle colorings α} × #{cycle colorings β}
- Grouping by the induced matrix K gives n! × #{matrices}
-/

/-- A cycle coloring for a composition α assigns each cycle of σ a "color" (variable index)
such that the total cycle lengths for each color match α.
This generalizes `MonochromaticColoring` from partitions to compositions. -/
def CycleColoring (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin n //
    ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) = α j }

instance (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CycleColoring n α σ) := by
  unfold CycleColoring
  exact Subtype.fintype _

/-- The MvPolynomial coefficient of P_σ at a composition α equals the number of
cycle colorings. This generalizes `coeff_psum_prod_eq_card_colorings` from
partitions to compositions. -/
private lemma finsupp_sum_single_iff' (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin n) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

theorem coeff_cycleTypePsumProduct_eq_card (n : ℕ) (α : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (cycleTypePsumProduct n σ) =
    ↑(Fintype.card (CycleColoring n α σ)) := by
  rw [cycleTypePsumProduct_eq_fullCycleType]
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast
  -- Goal: card of filter {f | ∑ single (f i) ... = α} = card CycleColoring
  -- Both count functions f with the marginal condition; they differ in how
  -- the condition is stated (finsupp sum vs pointwise).
  have equiv : CycleColoring n α σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α } := by
    unfold CycleColoring
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff' n α σ f).symm)
  rw [show Fintype.card (CycleColoring n α σ) = Fintype.card
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

/-- **Double counting lemma**: The total number of (σ, f, g) triples equals
n! times the number of matrices with given margins.

This is the combinatorial core. For each matrix K with given margins:
- There are n!/∏K_{ij}! ways to partition [n] into blocks of sizes K_{ij}
- There are ∏K_{ij}! permutations within each block
- Product = n! independent of K -/
theorem double_counting (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoring n α σ) * Fintype.card (CycleColoring n β σ) =
    n.factorial * Fintype.card (NNMatrixWithMargins n (⇑α) (⇑β)) := by
  sorry

/-- **Power Sum Cauchy Identity** (coefficient-level bilinear version):

For any `α β : Fin n →₀ ℕ` with total degree n,

  ∑_{σ∈Sₙ} [x^α](P_σ) · [x^β](P_σ) = n! · [x^α y^β](∏_{i,j} 1/(1-xᵢyⱼ))

The proof reduces to the `double_counting` lemma: both sides count the same
set of (permutation, bicoloring) triples with different groupings. -/
theorem powerSum_bilinear_coeff (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (cycleTypePsumProduct n σ) : ℂ) *
      (MvPolynomial.coeff β (cycleTypePsumProduct n σ) : ℂ)) =
    (Nat.factorial n : ℂ) * MvPowerSeries.coeff (bilinExponent n α β)
      (fullCauchyProd n ℂ) := by
  -- Rewrite each MvPolynomial coefficient as card of CycleColoring
  simp_rw [coeff_cycleTypePsumProduct_eq_card]
  -- Rewrite Cauchy product coefficient as card of NNMatrixWithMargins
  rw [fullCauchyProd_coeff_eq_card]
  -- Both sides are natural number casts; reduce to ℕ equality
  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  congr 1
  exact double_counting n α β hα hβ

end Etingof
