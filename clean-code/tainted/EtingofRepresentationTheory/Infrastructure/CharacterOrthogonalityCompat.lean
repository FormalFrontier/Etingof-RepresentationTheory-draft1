import Mathlib

/-!
# Finite-character orthogonality compatibility

Mathlib's character orthogonality theorems use `Nat.card` and ordinary inversion.  The project
historically uses an explicit `Fintype` together with `Fintype.card` and `Invertible`.  These
infrastructure lemmas keep that interface without introducing dependencies on later book items.
-/

open CategoryTheory

universe u v

namespace FDRep

theorem scalar_product_char_eq_finrank_equivariant_fintype
    {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      Module.finrank k (W ⟶ V) := by
  haveI : Invertible (Nat.card G : k) := by
    rwa [← Fintype.card_eq_nat_card]
  simpa only [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card] using
    scalar_product_char_eq_finrank_equivariant W V

open scoped Classical in
theorem char_orthonormal_fintype
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then (1 : k) else (0 : k) := by
  haveI : Invertible (Nat.card G : k) := by
    rwa [← Fintype.card_eq_nat_card]
  simpa only [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card] using
    char_orthonormal V W

end FDRep
