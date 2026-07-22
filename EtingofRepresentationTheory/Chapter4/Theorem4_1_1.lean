import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Theorem 4.1.1: Maschke's Theorem

**Maschke's theorem.** Let G be a finite group and k a field whose characteristic does
not divide |G|. Then:

(i) The group algebra k[G] is semisimple.

(ii) There is an isomorphism k[G] ≅ ⊕ᵢ End(Vᵢ), where Vᵢ are all the irreducible
representations of G. Moreover, the regular representation decomposes as
k[G] ≅ ⊕ᵢ Vᵢ^(dim Vᵢ), giving the dimension formula |G| = Σᵢ (dim Vᵢ)².

## Mathlib correspondence

Mathlib has `IsSemisimpleRing` and `MonoidAlgebra.instIsSemisimpleRing` for part (i).
Part (i) is `Etingof.Theorem4_1_1_semisimple`. Part (ii) is formalized in two forms:
`Etingof.Theorem4_1_1_algebra_iso` gives the full content — the family of irreducible
representations together with the algebra isomorphism `k[G] ≃ₐ[k] ⊕ᵢ End(Vᵢ)` and the
sum-of-squares formula — while `Etingof.Theorem4_1_1_sum_of_squares` records only the
dimension identity `Σᵢ (dim Vᵢ)² = |G|`.
-/

open CategoryTheory

universe u

/-- Maschke's theorem, part (i): The group algebra k[G] is semisimple when the
characteristic of k does not divide |G|. (Etingof Theorem 4.1.1) -/
theorem Etingof.Theorem4_1_1_semisimple
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    [DecidableEq G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance

/-- Maschke's theorem, part (ii): the sum-of-squares formula `|G| = Σᵢ (dim Vᵢ)²`.

Over an algebraically closed field `k` with `char k ∤ |G|`, the Wedderburn-Artin
decomposition `k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k` exhibits the
irreducible representations as the column-vector modules of the matrix blocks,
with `d i` their dimensions. Comparing `k`-dimensions on both sides gives
`Σᵢ (d i)² = |G|`. The decomposition data is packaged by `IrrepDecomp` and the
dimension identity is `IrrepDecomp.sum_sq_eq_card`. -/
theorem Etingof.Theorem4_1_1_sum_of_squares
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ),
      (∀ i, NeZero (d i)) ∧ ∑ i, (d i) ^ 2 = Fintype.card G :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.d, D.d_pos, D.sum_sq_eq_card⟩

/-- Maschke's theorem, part (ii), **algebra-isomorphism form**.

The full content of part (ii): there is a finite family `V : Fin n → FDRep k G` of the
irreducible representations of `G` — each `Simple`, pairwise non-isomorphic, and complete
(every simple `FDRep` is isomorphic to one of them) — together with an isomorphism of
`k`-algebras

  `ψ : k[G] ≃ₐ[k] ⊕ᵢ End(Vᵢ)`,

which is the book's `ψ : k[G] → ⊕ᵢ End(Vᵢ)`, `g ↦ ⊕ᵢ g|_{Vᵢ}`. Comparing dimensions on
the two sides yields the sum-of-squares formula `Σᵢ (dim Vᵢ)² = |G|`.

This statement surfaces the algebra isomorphism and the irreducible enumeration that the
weaker `Etingof.Theorem4_1_1_sum_of_squares` (which only records the dimension identity)
leaves implicit. The representations `Vᵢ` are the column-vector representations of the
Wedderburn-Artin decomposition (`IrrepDecomp.columnFDRep`), and `ψ` is `IrrepDecomp.endIso`,
the Wedderburn-Artin isomorphism with each matrix block read as `End(Vᵢ)`. -/
theorem Etingof.Theorem4_1_1_algebra_iso
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Module.End k (V i)) ∧
      ∑ i, Module.finrank k (V i) ^ 2 = Fintype.card G :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.columnFDRep, D.columnFDRep_simple, D.columnFDRep_injective,
    D.columnFDRep_surjective, ⟨D.endIso⟩,
    D.sum_finrank_sq_eq_card D.columnFDRep D.columnFDRep_simple D.columnFDRep_injective⟩
