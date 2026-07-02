import Mathlib
import EtingofRepresentationTheory.Chapter5.DiagonalCoordinate
import EtingofRepresentationTheory.Chapter5.SymmetricPowerBasis
import EtingofRepresentationTheory.Chapter5.SymmetricTransvection

/-!
# Irreducibility of `SⁿV` as a `GL(V)`-representation (Problem 4.12.3, symmetric half)

This file proves that the symmetric power `SⁿV` of a finite-dimensional vector space over a
characteristic-zero field is an *irreducible* `GL(V)`-representation: the only subspaces stable
under every `symmetricPowerMap g` (`g : V ≃ₗ[k] V`) are `⊥` and `⊤`.

This is the symmetric half of Problem 4.12.3 from Etingof's book, cited in Example 5.19.3, and the
companion of `Etingof.exteriorPower_eq_bot_or_top`. It assembles the two foundational pieces built
earlier — the monomial basis of `SⁿV` (`Etingof.SymmetricPowerBasis`) and the transvection
connectivity (`Etingof.SymmetricTransvection`) — with a diagonal element of distinct eigenvalues,
through the abstract criterion `Etingof.DiagonalCoordinate.eq_bot_or_eq_top_of_connected`:

* **Distinct eigenvalues.** Pick a basis `bV` of `V` and the diagonal element
  `H = diag(t₀, …, t_{d-1})` with `tᵢ = pᵢ` the `i`-th prime (cast to `k`). On the monomial basis
  `e^α` of `SⁿV` it acts with eigenvalue `∏_m t_{α m} = ∏_i pᵢ^{cᵢ}`, where `cᵢ` is the multiplicity
  of `i`. Unique prime factorisation makes these eigenvalues pairwise distinct across monomials, so
  by `DiagonalCoordinate.mem_of_repr_ne_zero` any subrepresentation `W` is spanned by a subset of
  the monomial basis.

* **Connectivity by transvections.** Unlike the exterior case, permutation matrices act *trivially*
  on the monomial basis, so the connectivity is supplied by the transvections `1 + Eᵢⱼ`
  (`Etingof.monomialAdj_connected` and `Etingof.monomialAdj_step_mem`): any two monomials are joined
  by single-unit moves, each realised inside `W` by a transvection. Hence a nonzero
  subrepresentation is everything.

The hypothesis `[CharZero k]` (the book works over `ℂ`) is essential: over small finite fields the
diagonal element with distinct eigenvalues need not exist.
-/

open scoped TensorProduct BigOperators
open Module
open Etingof.SymmetricPowerBasis

namespace Etingof

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]

section Combinatorics

variable {n d : ℕ}

/-- Recovering the `j`-multiplicity of a tuple from the multiset count. -/
private lemma count_map_eq_card_filter (r : Fin n → Fin d) (j : Fin d) :
    Multiset.count j (Multiset.map r Finset.univ.val)
      = (Finset.univ.filter (fun m => r m = j)).card := by
  classical
  rw [Multiset.count_map]
  exact congrArg Multiset.card (Multiset.filter_congr (fun a _ => eq_comm))

/-- The `pr j`-adic valuation of `∏_m pr(r m)` (with `pr = i`-th prime) is the multiplicity of `j`
in the tuple `r`. This is the unique-factorisation heart that makes the eigenvalues injective. -/
private lemma factorization_prod_prime_eq_card_filter (r : Fin n → Fin d) (j : Fin d) :
    (∏ m, Nat.nth Nat.Prime (r m)).factorization (Nat.nth Nat.Prime j)
      = (Finset.univ.filter (fun m => r m = j)).card := by
  classical
  have hinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective Nat.infinite_setOf_prime
  rw [Nat.factorization_prod (fun m _ => (Nat.prime_nth_prime (r m)).ne_zero),
    Finsupp.finsetSum_apply]
  have hterm : ∀ m, (Nat.nth Nat.Prime (r m)).factorization (Nat.nth Nat.Prime j)
      = if r m = j then 1 else 0 := by
    intro m
    rw [(Nat.prime_nth_prime (r m)).factorization]
    simp only [Finsupp.single_apply, hinj.eq_iff, Fin.val_inj]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_boole, Nat.cast_id]

/-- Equal prime-products imply the two tuples give permutation-equivalent lists (same monomial). -/
private lemma prod_prime_eq_imp_ofFn_perm {p q : Fin n → Fin d}
    (h : ∏ m, Nat.nth Nat.Prime (p m) = ∏ m, Nat.nth Nat.Prime (q m)) :
    List.Perm (List.ofFn p) (List.ofFn q) := by
  classical
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
  refine Multiset.ext.mpr (fun j => ?_)
  rw [count_map_eq_card_filter, count_map_eq_card_filter,
    ← factorization_prod_prime_eq_card_filter p j,
    ← factorization_prod_prime_eq_card_filter q j, h]

/-- Two tuples whose `ofFn`-lists are permutation-equivalent describe the same monomial. Proved by
sorting both tuples: the sorted forms are monotone lists with the same multiset, hence equal, so the
two tuples differ by a permutation. -/
lemma toMonomial_eq_of_ofFn_perm {p q : Fin n → Fin d}
    (h : List.Perm (List.ofFn p) (List.ofFn q)) :
    (toMonomial p : Monomial n (Fin d)) = toMonomial q := by
  classical
  set σp := Tuple.sort p with hσp
  set σq := Tuple.sort q with hσq
  have hp' : List.Perm (List.ofFn (p ∘ σp)) (List.ofFn p) := Equiv.Perm.ofFn_comp_perm σp p
  have hq' : List.Perm (List.ofFn (q ∘ σq)) (List.ofFn q) := Equiv.Perm.ofFn_comp_perm σq q
  have hperm : List.Perm (List.ofFn (p ∘ σp)) (List.ofFn (q ∘ σq)) :=
    hp'.trans (h.trans hq'.symm)
  have hsp : (List.ofFn (p ∘ σp)).SortedLE := (List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort p)
  have hsq : (List.ofFn (q ∘ σq)).SortedLE := (List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort q)
  have heq : List.ofFn (p ∘ σp) = List.ofFn (q ∘ σq) := hperm.eq_of_sortedLE hsp hsq
  have hfun : p ∘ σp = q ∘ σq := List.ofFn_injective heq
  refine Quotient.sound ⟨σq.symm.trans σp, ?_⟩
  funext i
  have := congrFun hfun (σq.symm i)
  simpa using this.symm

end Combinatorics

section Diagonal

variable {n d : ℕ}

/-- The eigenvalue of the monomial `⟦p⟧` under a diagonal element with weights `t`: `∏_m t(p m)`.
Well-defined on monomial classes because the product is invariant under permuting the factors. -/
noncomputable def monWeight (t : Fin d → k) : Monomial n (Fin d) → k :=
  Quotient.lift (fun p => ∏ m, t (p m))
    (by rintro p q ⟨σ, rfl⟩; exact (Equiv.prod_comp σ (fun m => t (p m))).symm)

@[simp] lemma monWeight_toMonomial (t : Fin d → k) (p : Fin n → Fin d) :
    monWeight t (toMonomial p) = ∏ m, t (p m) := rfl

/-- A diagonal linear map `g` on `bV` acts on the monomial basis vector `⟦p⟧` of `SⁿV` by the scalar
`∏_m t(p m)`: descending `g ⊗ ⋯ ⊗ g` through `mk` and pulling the scalars out of the pure tensor. -/
lemma symmetricPowerMap_monomialBasis_diag (bV : Basis (Fin d) k V) (t : Fin d → k)
    (g : V →ₗ[k] V) (hg : ∀ l, g (bV l) = t l • bV l) (p : Fin n → Fin d) :
    symmetricPowerMap g (symmetricPowerMonomialBasis bV (toMonomial p))
      = (∏ m, t (p m)) • symmetricPowerMonomialBasis bV (toMonomial p) := by
  rw [symmetricPowerMonomialBasis_toMonomial, tensorBasis, Basis.piTensorProduct_apply,
    symmetricPowerMap_mk, PiTensorProduct.map_tprod]
  simp only [hg]
  rw [MultilinearMap.map_smul_univ, map_smul]

end Diagonal

/-- **Irreducibility of `SⁿV` (Problem 4.12.3, symmetric half).** Over a characteristic-zero field,
every subspace of `SⁿV = SymmetricPower k (Fin n) V` stable under the `GL(V)`-action
`g ↦ symmetricPowerMap g` is `⊥` or `⊤`. -/
theorem symmetricPower_eq_bot_or_top [CharZero k] [Module.Finite k V] {n : ℕ}
    (W : Submodule k (SymmetricPower k (Fin n) V))
    (hW : ∀ g : V ≃ₗ[k] V, ∀ w ∈ W, symmetricPowerMap (g : V →ₗ[k] V) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  set d := finrank k V with hd
  -- A basis of `V` and the induced monomial basis of `SⁿV`.
  let bV : Basis (Fin d) k V := finBasis k V
  let b : Basis (Monomial n (Fin d)) k (SymmetricPower k (Fin n) V) :=
    symmetricPowerMonomialBasis bV
  -- The diagonal weights `tᵢ = pᵢ` (the `i`-th prime cast to `k`), nonzero in characteristic zero.
  let t : Fin d → k := fun i => ((Nat.nth Nat.Prime i : ℕ) : k)
  have ht : ∀ i, t i ≠ 0 := fun i => by
    simp only [t, Ne, Nat.cast_eq_zero]; exact (Nat.prime_nth_prime i).ne_zero
  let u : Fin d → kˣ := fun i => Units.mk0 (t i) (ht i)
  -- The diagonal element `H ∈ GL(V)` and the operator it induces on `SⁿV`.
  let H : V ≃ₗ[k] V := bV.equiv (bV.unitsSMul u) (Equiv.refl _)
  have hH : ∀ j : Fin d, H (bV j) = t j • bV j := by
    intro j
    simp only [H, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]
    rfl
  set T : Module.End k (SymmetricPower k (Fin n) V) := symmetricPowerMap (H : V →ₗ[k] V) with hT_def
  -- `T` acts diagonally on the monomial basis, with eigenvalue `monWeight t`.
  have hTdiag : ∀ M, T (b M) = monWeight t M • b M := by
    intro M
    refine Quotient.inductionOn M (fun p => ?_)
    exact symmetricPowerMap_monomialBasis_diag bV t (H : V →ₗ[k] V) hH p
  -- Distinct eigenvalues, via unique prime factorisation.
  have hinj : Function.Injective (monWeight t (n := n) (d := d)) := by
    refine fun M N => Quotient.inductionOn₂ M N (fun p q hpq => ?_)
    have hpq' : (∏ m, t (p m)) = ∏ m, t (q m) := hpq
    have hnat : (∏ m, Nat.nth Nat.Prime (p m)) = ∏ m, Nat.nth Nat.Prime (q m) := by
      simp only [t, ← Nat.cast_prod] at hpq'
      exact Nat.cast_injective hpq'
    exact toMonomial_eq_of_ofFn_perm (prod_prime_eq_imp_ofFn_perm hnat)
  -- `W` is `T`-invariant (apply the hypothesis to `g = H`).
  have hWT : ∀ x ∈ W, T x ∈ W := fun x hx => hW H x hx
  -- Connectivity: the transvection relation on monomials.
  refine DiagonalCoordinate.eq_bot_or_eq_top_of_connected b hTdiag hinj hWT
    (MonomialAdj (n := n) (d := d)) monomialAdj_connected (fun M N hMW hMN => ?_)
  exact monomialAdj_step_mem bV hTdiag hinj hWT hW M N hMW hMN

/-- **Irreducibility of `L_{(n)} = SⁿV`** (Problem 4.12.3, the first half of the irreducibility
assertion in Example 5.19.3): every `GL(V)`-subrepresentation of the symmetric power — i.e. every
submodule stable under `symmetricPowerMap g` for all `g ∈ GL(V)` — is either `⊥` or `⊤`.

This is a genuine, complete proof of Problem 4.12.3 for the symmetric power, following the book's
Hint: the diagonal element `diag(p₀, …, p_{d-1})` of the first `d` primes has pairwise distinct
eigenvalues on the monomial basis `e_{i₁} ⊙ ⋯ ⊙ e_{iₙ}` of `SⁿV` (the eigenvalue of a monomial is
the product of the primes at its factors, distinct by unique factorisation), so any
subrepresentation is spanned by a subset of that basis; and the transvections `1 + E_{ij}`, which
connect any two monomials by single-unit moves, then force a nonzero subrepresentation to be
everything. See
`Etingof.symmetricPower_eq_bot_or_top` for the proof. The hypothesis `[CharZero k]` (the book works
over `ℂ`) is essential: over small finite fields the diagonal element with distinct eigenvalues need
not exist. This is the symmetric companion of `Example5_19_3_exterior_irreducible`. -/
theorem Example5_19_3_symmetric_irreducible [CharZero k] [Module.Finite k V] (n : ℕ) :
    ∀ W : Submodule k (SymmetricPower k (Fin n) V),
    (∀ g : V ≃ₗ[k] V, ∀ w ∈ W, symmetricPowerMap (g : V →ₗ[k] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤ :=
  fun W hW => symmetricPower_eq_bot_or_top W hW

end Etingof
