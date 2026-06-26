import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.MultiplicitySpaceBiduality

/-!
# Schur-Weyl duality, part (iii): bimodule decomposition with full multiplicity content

`Theorem5_18_4_bimodule_decomposition` (in `Theorem5_18_4.lean`) records, over the
abstract index set `ι` enumerating the distinct simple `A = symGroupImage k V n`
modules appearing in `V^⊗n`, that each Specht summand `Sᵢ` is a simple `A`-module,
that the `Sᵢ` are pairwise non-isomorphic, and that each multiplicity space `Lᵢ`
carries a `B = diagonalActionImage k V n`-module structure. It stops short of two
facts the book asserts about the `B`-side (Etingof Theorem 5.18.4(iii) /
Corollary 5.19.2):

* each `Lᵢ` is itself a **simple** `B`-module (an irreducible polynomial
  `GL(V)`-representation), and
* the `Lᵢ` are **pairwise non-isomorphic** as `B`-modules.

This file supplies both, sorry-free, for a general finite-dimensional `V`. The
`L`-simplicity comes from `Theorem5_18_1_bimodule_decomposition_explicit`
(`hL_simp`: each `↥(Sᵢ) →ₗ[A] V^⊗n` is simple over `centralizer A`), and the
`L`-distinctness from `multiplicitySpace_Cdistinct` (distinct simple `A`-summands
give non-isomorphic multiplicity spaces over `centralizer A`). Both are transported
across the Schur-Weyl centralizer identity
`centralizer(symGroupImage) = diagonalActionImage` (`Theorem5_18_4_centralizers`).

The one remaining gap to the book's *partition-indexed* statement
(`Theorem5_18_4_partition_decomposition`) is purely the **Specht labelling**: an
injection `ι ↪ Nat.Partition n` re-indexing this abstract decomposition by
partitions of `n`. That labelling reduces to the cardinality bound
`Fintype.card ι ≤ Fintype.card (Nat.Partition n)` (each `Sᵢ`, restricted along the
surjection `k[Sₙ] ↠ symGroupImage`, is a simple `k[Sₙ]`-module, and over an
algebraically closed field of characteristic `0` there are at most
`|ConjClasses (Perm (Fin n))| ≤ p(n)` of those, via `Etingof.Corollary4_2_2`). See
the tracking issue for that step.
-/

open scoped TensorProduct

namespace Etingof

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

-- Heartbeat bumps match `Theorem5_18_4_bimodule_decomposition`: the deep
-- `Subalgebra → Ring → Module.End` instance chain plus the `h_eq ▸` transports
-- across the centralizer equality exceed the defaults.
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- Schur-Weyl duality, part (iii), bimodule form with full multiplicity content.

As an `(A ⊗[k] B)`-module (with `A = symGroupImage k V n` and
`B = diagonalActionImage k V n`), `V^⊗n` decomposes as
  `V^⊗n ≅ ⨁ᵢ Sᵢ ⊗[k] Lᵢ`
where, in addition to everything `Theorem5_18_4_bimodule_decomposition` provides
(the `Sᵢ` are pairwise non-isomorphic simple `A`-modules with `Module B`-structures
on the `Lᵢ`), this strengthening asserts:

* each `Lᵢ` is a **simple** `B`-module (irreducible polynomial `GL(V)`-rep), and
* the `Lᵢ` are **pairwise non-isomorphic** as `B`-modules.

These are exactly the `B`-side facts dropped from the earlier sorry-free statements.
(Etingof Theorem 5.18.4, part iii, bimodule form, full multiplicity content.) -/
theorem Theorem5_18_4_bimodule_decomposition_full
    [IsAlgClosed k] [CharZero k]
    (_hN : n ≤ Module.finrank k V) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type (max u v))
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (symGroupImage k V n) (S i))
      (_ : ∀ i, IsSimpleModule (symGroupImage k V n) (S i))
      (_ : ∀ i j, Nonempty (S i ≃ₗ[symGroupImage k V n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → Type (max u v)) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module (diagonalActionImage k V n) (L i))
      (_ : ∀ i, IsSimpleModule (diagonalActionImage k V n) (L i)),
      (∀ i j, Nonempty (L i ≃ₗ[diagonalActionImage k V n] L j) → i = j) ∧
      Nonempty (TensorPower k V n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] L i)) := by
  haveI := symGroupImage_isSemisimpleRing k V n
  haveI := symGroupImage_faithfulSMul k V n
  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, hL_simp, e, _he⟩ :=
    Theorem5_18_4_bimodule_decomposition_explicit k V n
  -- The Schur-Weyl centralizer identity, used to transport the `centralizer A`
  -- module structure / simplicity / distinctness of the `Lᵢ` to `diagonalActionImage`.
  have h_eq : Subalgebra.centralizer k
      (symGroupImage k V n : Set (Module.End k (TensorPower k V n))) =
        diagonalActionImage k V n :=
    (Theorem5_18_4_centralizers k V n).2.symm
  haveI hsimpI : ∀ i, IsSimpleModule (symGroupImage k V n) (S' i) := hS'_simp
  -- Rewrite the goal's `diagonalActionImage` back to `centralizer(symGroupImage)`,
  -- so every `B`-side datum is the canonical `centralizer A`-structure: the
  -- `Module` instance is `centralizerModuleHom`, `L`-simplicity is `hL_simp`, and
  -- `L`-distinctness is `multiplicitySpace_Cdistinct` applied directly.
  rw [← h_eq]
  refine ⟨ι, hι, hι_dec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    hS'_simp, hS'_dist, hS'_fin,
    fun i => (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n),
    fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    hL_simp, ?_, ⟨e⟩⟩
  intro i j hiso
  obtain ⟨f⟩ := hiso
  exact multiplicitySpace_Cdistinct k (TensorPower k V n) (symGroupImage k V n)
    S' hS'_dist i j ⟨f⟩

end Etingof
