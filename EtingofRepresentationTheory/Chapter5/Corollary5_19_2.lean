import EtingofRepresentationTheory.Chapter5.SchurWeylPartition

/-!
# Corollary 5.19.2: Schur-Weyl Decomposition

As a representation of Sₙ × GL(V), V⊗ⁿ decomposes as
  V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ
where Vλ are irreducible Sₙ-representations (Specht modules) and
Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ) are distinct irreducible GL(V)-representations (or zero).

## Mathlib correspondence

Requires Schur-Weyl duality, which is not yet in Mathlib.
-/

open scoped TensorProduct
open Etingof

universe u v

/-- Schur-Weyl decomposition: as an Sₙ × GL(V) representation,
V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ where the sum ranges over partitions of n.
Here Vλ are irreducible Sₙ-representations (Specht modules) and
Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ) are distinct irreducible GL(V)-representations
(or zero when the partition has more parts than dim V).

This refines Theorem 5.18.4(iii) by identifying the indexing set
as partitions of n. The existential carries the genuine module-theoretic
content: each `S p` (= `Vλ`) is a simple `symGroupImage`-module or zero,
each `L p` (= `Lλ`) is a distinct irreducible `diagonalActionImage`-module
or zero, and the iso decomposes `V⊗ⁿ` as `⊕_p S p ⊗ L p`. The proof
delegates to `Theorem5_18_4_partition_decomposition`, whose `sorry` records
the one open dependency (the Specht labelling of the simple
`symGroupImage`-modules); see issue #5326.
(Etingof Corollary 5.19.2) -/
theorem Etingof.Corollary5_19_2
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (hN : n ≤ Module.finrank k V) :
    ∃ (S : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (S p))
      (_ : ∀ p, Module k (S p))
      (_ : ∀ p, Module (symGroupImage k V n) (S p))
      (L : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (L p))
      (_ : ∀ p, Module k (L p))
      (_ : ∀ p, Module (diagonalActionImage k V n) (L p)),
      (∀ p, IsSimpleModule (symGroupImage k V n) (S p) ∨ Subsingleton (S p)) ∧
      (∀ p, IsSimpleModule (diagonalActionImage k V n) (L p) ∨ Subsingleton (L p)) ∧
      (∀ p q, ¬ Subsingleton (L p) →
        Nonempty (L p ≃ₗ[diagonalActionImage k V n] L q) → p = q) ∧
      Nonempty (TensorPower k V n ≃ₗ[k]
        DirectSum (Nat.Partition n) (fun p => S p ⊗[k] L p)) :=
  Theorem5_18_4_partition_decomposition k V n hN
