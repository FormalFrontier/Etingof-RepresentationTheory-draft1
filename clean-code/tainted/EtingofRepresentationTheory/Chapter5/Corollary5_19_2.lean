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
(or zero when the corresponding simple does not occur).

The theorem exposes the full book-faithful data: an injective genuine Specht label,
literal `Hom_{symGroupImage}(Sᵢ,V⊗ⁿ)` multiplicity spaces, simplicity and pairwise
nonisomorphism of those multiplicities, and a structured equivalence intertwining both
commuting actions on all vectors. No hypothesis `n ≤ finrank k V` is needed: the
partition-indexed structured equivalence zero-pads the absent constituents.
(Etingof Corollary 5.19.2) -/
theorem Etingof.Corollary5_19_2
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    ∃ (iota : Type) (_ : Fintype iota) (_ : DecidableEq iota)
      (S : iota → Submodule (symGroupImage k V n) (TensorPower k V n)),
      letI : ∀ i, AddCommGroup (S i) := fun i =>
        { Module.addCommMonoidToAddCommGroup k with
          toAddCommMonoid := (S i).addCommMonoid }
      ∃ (label : iota ↪ Nat.Partition n)
        (specht : ∀ i, ↥(S i) ≃ₗ[k] ↥(SpechtModuleK k n (label i))),
      (∀ p, Subsingleton {i : iota // label i = p}) ∧
      (∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k
          (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
        (↥(S i) →ₗ[symGroupImage k V n] TensorPower k V n)) ∧
      (∀ i j, Nonempty
        ((↥(S i) →ₗ[symGroupImage k V n] TensorPower k V n) ≃ₗ[
          ↥(Subalgebra.centralizer k
            (symGroupImage k V n : Set (Module.End k (TensorPower k V n))))]
          (↥(S j) →ₗ[symGroupImage k V n] TensorPower k V n)) → i = j) ∧
      (∀ (i : iota) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : ↥(S i)),
        specht i ((symGroupAlgHomToImage k V n a) • x) = a • specht i x) ∧
      ∃ e : PartitionBimoduleDecompositionEquiv k n S label,
        ∀ (b : ↥(diagonalActionImage k V n)) (x : TensorPower k V n),
          e.toLinearEquiv (b.val x) =
            partitionBimoduleCentralizerAction k n S label
              (⟨b.val, diagonalActionImage_le_centralizer_symGroupImage
                k V n b.property⟩ :
                ↥(Subalgebra.centralizer k
                  (symGroupImage k V n :
                    Set (Module.End k (TensorPower k V n)))))
              (e.toLinearEquiv x) :=
  Theorem5_18_4_partition_bimodule_decomposition_equivariant k V n
