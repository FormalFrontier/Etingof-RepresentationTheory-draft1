import Mathlib
import EtingofRepresentationTheory.Chapter5.DiagonalCoordinate

/-!
# Irreducibility of `∧ⁿV` as a `GL(V)`-representation (Problem 4.12.3, exterior half)

This file proves that the exterior power `⋀[k]^n V` of a finite-dimensional vector space over a
characteristic-zero field is an *irreducible* `GL(V)`-representation: the only subspaces stable
under every `exteriorPower.map n g` (`g : V ≃ₗ[k] V`) are `⊥` and `⊤`.

This is the exterior half of Problem 4.12.3 from Etingof's book, cited in Example 5.19.3. The
proof follows the book's Hint, packaged through `Etingof.DiagonalCoordinate`:

* **Distinct eigenvalues.** Pick a basis `bV` of `V` and the diagonal element
  `H = diag(t₀, …, t_{d-1})` with `tᵢ = 2 ^ (2 ^ i)`. On the monomial basis `b_S = ⋀_{i ∈ S} eᵢ`
  of `⋀ⁿV` it acts with eigenvalue `∏_{i ∈ S} tᵢ = 2 ^ (∑_{i ∈ S} 2 ^ i)`. Because subsets have
  distinct sums of powers of two, these eigenvalues are pairwise distinct, so by
  `DiagonalCoordinate.mem_of_repr_ne_zero` any subrepresentation `W` is spanned by a subset of the
  `b_S`.

* **Connectivity by permutations.** Where the book uses transvections (needed for the symmetric
  case), for the exterior power it suffices that `GL(V)` contains the permutation matrices, which
  act *transitively* on the `n`-subsets `S`: an order-matching permutation `σ` sends `b_S` exactly
  to `b_T`. Hence once some `b_S ∈ W`, every `b_T ∈ W`, so `W = ⊤`.
-/

open scoped TensorProduct BigOperators
open Module

namespace Etingof

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]

section Reindex

/-- Reindex a product over the sorted enumeration of a finset back to the finset. -/
private lemma prod_over_orderEmb {α : Type*} [LinearOrder α] {s : Finset α} {m : ℕ}
    (h : s.card = m) (f : α → k) :
    ∏ i : Fin m, f (s.orderEmbOfFin h i) = ∏ j ∈ s, f j := by
  rw [← Finset.prod_coe_sort s f, ← Equiv.prod_comp (s.orderIsoOfFin h).toEquiv (fun x : s => f x)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Finset.coe_orderIsoOfFin_apply]

end Reindex

section ExteriorBasis

variable {d n : ℕ}

/-- A linear endomorphism `g` acts on a monomial basis vector `b_S = ⋀_{i ∈ S} eᵢ` of `⋀ⁿV` by
applying `g` to each factor. -/
private lemma map_exteriorBasis (bV : Basis (Fin d) k V) (g : V →ₗ[k] V)
    (S : Set.powersetCard (Fin d) n) :
    exteriorPower.map n g (bV.exteriorPower n S) =
      exteriorPower.ιMulti k n (fun i => g (bV (S.val.orderEmbOfFin S.prop i))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  refine congrArg _ (funext (fun i => ?_))
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]

end ExteriorBasis

section DiagonalWeights

variable {d n : ℕ}

/-- The diagonal weights `tᵢ = 2 ^ (2 ^ i)`, nonzero in characteristic zero. -/
private noncomputable def diagWeight [CharZero k] (i : Fin d) : k := (2 : k) ^ (2 ^ (i : ℕ))

private lemma diagWeight_ne_zero [CharZero k] (i : Fin d) : diagWeight (k := k) i ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- The diagonal units used to build the diagonal element `H ∈ GL(V)`. -/
private noncomputable def diagUnit [CharZero k] (i : Fin d) : kˣ :=
  Units.mk0 (diagWeight i) (diagWeight_ne_zero i)

/-- The eigenvalue of `b_S` under the diagonal element: `∏_{i ∈ S} tᵢ`. -/
private noncomputable def diagEig [CharZero k] (S : Set.powersetCard (Fin d) n) : k :=
  ∏ j ∈ S.val, diagWeight (k := k) j

/-- The eigenvalues `∏_{i ∈ S} tᵢ = 2 ^ (∑_{i ∈ S} 2 ^ i)` are pairwise distinct, because subsets
have distinct sums of powers of two. -/
private lemma diagEig_injective [CharZero k] :
    Function.Injective (diagEig (k := k) (d := d) (n := n)) := by
  intro S T h
  -- Rewrite each eigenvalue as `(2 : k) ^ (exponent S)`.
  have hexp : ∀ U : Set.powersetCard (Fin d) n,
      diagEig (k := k) U = (2 : k) ^ (∑ j ∈ U.val, 2 ^ (j : ℕ)) := by
    intro U
    rw [diagEig, ← Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hexp, hexp] at h
  -- Cancel the base `2` to get equal exponents.
  have hnat : (((2 : ℕ) ^ (∑ j ∈ S.val, 2 ^ (j : ℕ)) : ℕ) : k)
      = (((2 : ℕ) ^ (∑ j ∈ T.val, 2 ^ (j : ℕ)) : ℕ) : k) := by push_cast; exact h
  have hpow : (2 : ℕ) ^ (∑ j ∈ S.val, 2 ^ (j : ℕ)) = (2 : ℕ) ^ (∑ j ∈ T.val, 2 ^ (j : ℕ)) :=
    Nat.cast_injective hnat
  have hsum : (∑ j ∈ S.val, 2 ^ (j : ℕ)) = ∑ j ∈ T.val, 2 ^ (j : ℕ) :=
    Nat.pow_right_injective (le_refl 2) hpow
  -- Distinct subsets give distinct sums of powers of two (binary representation).
  have hmap : (S.val.map Fin.valEmbedding) = (T.val.map Fin.valEmbedding) := by
    apply Finset.equivBitIndices.symm.injective
    change (∑ i ∈ S.val.map Fin.valEmbedding, 2 ^ i) = ∑ i ∈ T.val.map Fin.valEmbedding, 2 ^ i
    rw [Finset.sum_map, Finset.sum_map]
    exact hsum
  exact Subtype.ext (Finset.map_injective Fin.valEmbedding hmap)

end DiagonalWeights

section Permutation

variable {d n : ℕ}

/-- For any two `n`-subsets `S`, `T` of `Fin d`, there is a permutation of `Fin d` carrying the
sorted enumeration of `S` to that of `T`. (Permutations act transitively on `n`-subsets.) -/
private lemma exists_perm_orderEmb (S T : Set.powersetCard (Fin d) n) :
    ∃ σ : Equiv.Perm (Fin d), ∀ i : Fin n,
      σ (S.val.orderEmbOfFin S.prop i) = T.val.orderEmbOfFin T.prop i := by
  classical
  -- An order-matching bijection between the elements of `S` and of `T`.
  let φ : {x // x ∈ S.val} ≃ {x // x ∈ T.val} :=
    (S.val.orderIsoOfFin S.prop).symm.toEquiv.trans (T.val.orderIsoOfFin T.prop).toEquiv
  refine ⟨φ.extendSubtype, fun i => ?_⟩
  have hmem : S.val.orderEmbOfFin S.prop i ∈ S.val := S.val.orderEmbOfFin_mem S.prop i
  rw [Equiv.extendSubtype_apply_of_mem φ _ hmem]
  -- Evaluate `φ` on the `i`-th sorted element of `S`.
  change ((T.val.orderIsoOfFin T.prop)
      ((S.val.orderIsoOfFin S.prop).symm ⟨_, hmem⟩) : Fin d) = T.val.orderEmbOfFin T.prop i
  have hSi : ((S.val.orderIsoOfFin S.prop).symm ⟨S.val.orderEmbOfFin S.prop i, hmem⟩) = i := by
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply S.val S.prop i)
  rw [hSi, Finset.coe_orderIsoOfFin_apply]

end Permutation

/-- **Irreducibility of `∧ⁿV` (Problem 4.12.3, exterior half).** Over a characteristic-zero field,
every subspace of `⋀[k]^n V` stable under the `GL(V)`-action `g ↦ exteriorPower.map n g` is `⊥` or
`⊤`. -/
theorem exteriorPower_eq_bot_or_top [CharZero k] [Module.Finite k V] {n : ℕ}
    (W : Submodule k (⋀[k]^n V))
    (hW : ∀ g : V ≃ₗ[k] V, ∀ w ∈ W, exteriorPower.map n (g : V →ₗ[k] V) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  set d := finrank k V with hd
  -- A basis of `V` and the induced monomial basis of `⋀ⁿV`.
  let bV : Basis (Fin d) k V := finBasis k V
  let b : Basis (Set.powersetCard (Fin d) n) k (⋀[k]^n V) := bV.exteriorPower n
  -- The diagonal element `H ∈ GL(V)` and the operator it induces on `⋀ⁿV`.
  let H : V ≃ₗ[k] V := bV.equiv (bV.unitsSMul diagUnit) (Equiv.refl _)
  set T : Module.End k (⋀[k]^n V) := exteriorPower.map n (H : V →ₗ[k] V) with hT_def
  -- `H` acts diagonally on `bV`.
  have hH : ∀ j : Fin d, H (bV j) = diagWeight (k := k) j • bV j := by
    intro j
    simp only [H, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]
    rfl
  -- `b S` written via the sorted enumeration of `S`.
  have hbS : ∀ S : Set.powersetCard (Fin d) n,
      b S = exteriorPower.ιMulti k n (fun i => bV (S.val.orderEmbOfFin S.prop i)) := by
    intro S
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    exact congrArg _ (funext (fun i => by
      rw [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]))
  -- `T = exteriorPower.map n H` acts diagonally on the monomial basis `b`.
  have hTdiag : ∀ S, T (b S) = diagEig (k := k) S • b S := by
    intro S
    rw [hT_def, map_exteriorBasis bV (H : V →ₗ[k] V) S]
    rw [show (fun i => (H : V →ₗ[k] V) (bV (S.val.orderEmbOfFin S.prop i))) =
        (fun i => diagWeight (k := k) (S.val.orderEmbOfFin S.prop i) •
          bV (S.val.orderEmbOfFin S.prop i)) from funext (fun i => hH _)]
    rw [AlternatingMap.map_smul_univ, prod_over_orderEmb, hbS S]
    rfl
  -- Distinct eigenvalues.
  have hinj : Function.Injective (diagEig (k := k) (d := d) (n := n)) := diagEig_injective
  -- `W` is `T`-invariant (apply the hypothesis to `g = H`).
  have hWT : ∀ x ∈ W, T x ∈ W := fun x hx => hW H x hx
  -- Connectivity: the total relation, realised by permutation matrices.
  refine DiagonalCoordinate.eq_bot_or_eq_top_of_connected b hTdiag hinj hWT
    (fun _ _ => True) (fun s t => Relation.ReflTransGen.tail Relation.ReflTransGen.refl trivial)
    (fun S U hS _ => ?_)
  -- From `b S ∈ W`, an order-matching permutation `σ` sends `b S` to `b U`.
  obtain ⟨σ, hσ⟩ := exists_perm_orderEmb S U
  have hmap : exteriorPower.map n (bV.equiv bV σ : V →ₗ[k] V) (b S) = b U := by
    rw [map_exteriorBasis bV (bV.equiv bV σ : V →ₗ[k] V) S, hbS U]
    refine congrArg _ (funext (fun i => ?_))
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hσ i]
  rw [← hmap]
  exact hW (bV.equiv bV σ) (b S) hS

end Etingof
