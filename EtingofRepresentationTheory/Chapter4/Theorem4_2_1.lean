import Mathlib

/-!
# Theorem 4.2.1: Characters Form a Basis of Class Functions

If k is algebraically closed and char(k) does not divide |G|, the characters of irreducible
representations of G form a basis of the space Fc(G, k) of class functions on G.

We state this as: every class function (a function G → k constant on conjugacy classes)
lies in the k-linear span of characters of simple (irreducible) FDRep objects.
Linear independence of distinct irreducible characters follows from orthogonality
(Theorem 4.5.1 / `FDRep.char_orthonormal`).

## Mathlib correspondence

Mathlib has `FDRep.character`, `FDRep.char_conj` (characters are class functions),
and `FDRep.char_orthonormal` (orthonormality). The spanning/basis property is not yet
in Mathlib.
-/

open FDRep CategoryTheory

universe u

/-- Characters of irreducible representations span the space of class functions:
every function G → k that is constant on conjugacy classes is a k-linear combination
of characters of simple (irreducible) representations. (Etingof Theorem 4.2.1) -/
theorem Etingof.Theorem4_2_1
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) := by
  sorry
