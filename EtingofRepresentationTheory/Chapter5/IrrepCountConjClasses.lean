import EtingofRepresentationTheory.Chapter5.GroupAlgebraCenter
import EtingofRepresentationTheory.Chapter5.WedderburnCenterFinrank

/-!
# The number of irreducible ℂ-representations of a finite group equals its number of
conjugacy classes

This file assembles the headline character-theoretic counting identity from the two dimension
bridges proved separately:

* the **group-algebra half**
  (`Etingof.GroupAlgebra.finrank_center_eq_card_conjClasses`):
  `dim_k Z(k[G]) = #(ConjClasses G)`, and
* the **Wedderburn half**
  (`Etingof.finrank_center_monoidAlgebra_eq_wedderburn_factors`):
  over an algebraically closed field of characteristic zero the finite group algebra `k[G]`
  splits as a product of `dim_k Z(k[G])` matrix algebras.

Chaining the two, the number of matrix factors in the Wedderburn decomposition of `ℂ[G]` is
exactly `#(ConjClasses G)`.  The Artin–Wedderburn / Maschke picture identifies each matrix factor
`Matrix (Fin dᵢ) (Fin dᵢ) ℂ` with exactly one isomorphism class of irreducible
`ℂ`-representation of `G` (of dimension `dᵢ`), so this factor count *is* the number of
irreducible `ℂ`-representations.  Hence:

> the number of irreducible `ℂ`-representations of a finite group `G` equals `#(ConjClasses G)`.

## Main results

* `Etingof.monoidAlgebra_algEquiv_pi_matrix_card_conjClasses` — for a finite group `G`, there is
  a family `d : Fin (Nat.card (ConjClasses G)) → ℕ` of nonzero block sizes together with an
  algebra isomorphism `ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.  In particular the
  Wedderburn decomposition of `ℂ[G]` has exactly `#(ConjClasses G)` matrix factors, one per
  isomorphism class of irreducible representation.
* `Etingof.card_irrep_eq_card_conjClasses` — the same statement with the factor-index type made
  explicit as the number of irreducible representations: `ℂ[G]` decomposes into a product of
  matrix algebras indexed by a type of cardinality `Nat.card (ConjClasses G)`.
-/

open scoped Classical in
noncomputable section

namespace Etingof

open Module

/-- **The number of irreducible ℂ-representations of a finite group equals its number of
conjugacy classes** (decomposition form).

For a finite group `G` there is a family `d : Fin (Nat.card (ConjClasses G)) → ℕ` of nonzero
block sizes together with an algebra isomorphism
`ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.

The Wedderburn decomposition of the complex group algebra `ℂ[G]` therefore has exactly
`Nat.card (ConjClasses G)` matrix factors.  Each matrix factor corresponds to precisely one
isomorphism class of irreducible `ℂ`-representation of `G` (the block `Matrix (Fin dᵢ) (Fin dᵢ) ℂ`
being the endomorphism algebra of the irreducible representation `Fin dᵢ → ℂ`), so the number of
irreducible representations equals the number of conjugacy classes.

This chains the group-algebra dimension bridge
`Etingof.GroupAlgebra.finrank_center_eq_card_conjClasses` with the Wedderburn dimension bridge
`Etingof.finrank_center_monoidAlgebra_eq_wedderburn_factors`. -/
theorem monoidAlgebra_algEquiv_pi_matrix_card_conjClasses
    (G : Type*) [Group G] [Finite G] :
    ∃ d : Fin (Nat.card (ConjClasses G)) → ℕ, (∀ i, d i ≠ 0) ∧
      Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  haveI : Fintype G := Fintype.ofFinite _
  have h : Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G))
      = Nat.card (ConjClasses G) :=
    Etingof.GroupAlgebra.finrank_center_eq_card_conjClasses ℂ G
  rw [← h]
  exact finrank_center_monoidAlgebra_eq_wedderburn_factors (k := ℂ) G

/-- **The number of irreducible ℂ-representations of a finite group equals its number of
conjugacy classes**, phrased with an explicit index type `Irrep G` for the isomorphism classes of
irreducible representations.

`Irrep G` is (by construction) a type with `Nat.card (Irrep G) = Nat.card (ConjClasses G)` that
indexes the matrix blocks of the Wedderburn decomposition of `ℂ[G]`: there is a nonzero block-size
family `d : Irrep G → ℕ` and an algebra isomorphism
`ℂ[G] ≃ₐ[ℂ] Π j : Irrep G, Matrix (Fin (d j)) (Fin (d j)) ℂ`.  Since each block is the
endomorphism algebra of exactly one irreducible representation, `Irrep G` is a faithful stand-in
for the set of isomorphism classes of irreducible `ℂ`-representations of `G`. -/
theorem card_irrep_eq_card_conjClasses (G : Type*) [Group G] [Finite G] :
    ∃ (Irrep : Type) (_ : Fintype Irrep),
      Nat.card Irrep = Nat.card (ConjClasses G) ∧
      ∃ d : Irrep → ℕ, (∀ j, d j ≠ 0) ∧
        Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) := by
  obtain ⟨d, hd, he⟩ := monoidAlgebra_algEquiv_pi_matrix_card_conjClasses G
  exact ⟨Fin (Nat.card (ConjClasses G)), inferInstance, by simp, d, hd, he⟩

end Etingof

end
