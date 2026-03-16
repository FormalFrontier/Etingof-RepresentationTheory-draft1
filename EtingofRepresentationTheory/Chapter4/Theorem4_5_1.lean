import Mathlib

/-!
# Theorem 4.5.1: Orthogonality of Characters (First Orthogonality Relation)

For finite dimensional representations V, W of a finite group G over a field k:

(i) ⟨χ_V, χ_W⟩ = dim Hom_G(W, V), where ⟨f, g⟩ = (1/|G|) Σ_{x∈G} f(x) g(x⁻¹).

(ii) If V, W are irreducible and k is algebraically closed,
then ⟨χ_V, χ_W⟩ = δ_{V,W} (1 if V ≅ W, 0 otherwise).

The proof uses the averaging (Reynolds) operator P = (1/|G|) Σ_{g∈G} g acting on Hom(W, V),
which projects onto Hom_G(W, V).

## Mathlib correspondence

Part (i) corresponds to `FDRep.scalar_product_char_eq_finrank_equivariant`.
Part (ii) corresponds to `FDRep.char_orthonormal`.
-/

open FDRep CategoryTheory

universe u

/-- First orthogonality relation, part (i): the inner product of characters equals the
dimension of the equivariant Hom space.
⟨χ_V, χ_W⟩ = dim_k Hom_G(W, V). (Etingof Theorem 4.5.1(i)) -/
theorem Etingof.Theorem4_5_1_i
    {k G : Type u} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
    Module.finrank k (W ⟶ V) := by
  exact scalar_product_char_eq_finrank_equivariant W V

open scoped Classical in
/-- First orthogonality relation, part (ii): for irreducible representations, the inner
product of characters is 1 if they are isomorphic, 0 otherwise.
⟨χ_V, χ_W⟩ = δ_{V,W}. (Etingof Theorem 4.5.1(ii)) -/
theorem Etingof.Theorem4_5_1_ii
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
    if Nonempty (V ≅ W) then (1 : k) else (0 : k) := by
  exact char_orthonormal V W
