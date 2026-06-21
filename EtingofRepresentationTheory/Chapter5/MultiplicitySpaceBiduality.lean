import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_1

/-!
# Multiplicity-space biduality and `C`-distinctness (Schur-Weyl, Part 2)

For a semisimple subalgebra `A ⊆ End_k(E)` acting faithfully on a
finite-dimensional `k`-vector space `E` (`k` algebraically closed), let
`C = centralizer(A)` be the commutant. Each simple `A`-submodule `S ≤ E`
has a **multiplicity space** `M_S := ↥S →ₗ[A] E`, which is a simple
`C`-module (post-composition action, `Theorem5_18_1.isSimpleModule_homA_centralizer`).

This file proves **Part 2** of the Schur-Weyl GL-side distinctness output
(parent #4849, reducing #4731's `glTensorRep_equivariant_schurWeyl_decomposition`):
a `C`-linear iso of multiplicity spaces forces the underlying simple
`A`-modules to coincide,

  `M_{S_i} ≃ₗ[C] M_{S_j}  ⟹  i = j`,

given the `A`-side distinctness `hS'_dist : S_i ≃ₗ[A] S_j → i = j` produced by
`Theorem5_18_4_bimodule_decomposition_explicit`.

## Strategy — biduality (double-centralizer reflexivity)

The crux is the natural `A`-linear iso (symmetric double centralizer / biduality)

  `bidualityMap_S : ↥S ≃ₗ[A] (M_S →ₗ[C] E)`,

the curried evaluation `v ↦ (l ↦ l v)`. Given a `C`-iso `ψ : M_{S_i} ≃ₗ[C] M_{S_j}`,
precomposition `(- ∘ ψ.symm)` is an `A`-linear iso
`(M_{S_i} →ₗ[C] E) ≃ₗ[A] (M_{S_j} →ₗ[C] E)`; threading the two biduality maps
gives `S_i ≃ₗ[A] S_j`, whence `i = j` by `hS'_dist`.

The reusable `k`-linear precomposition congruence `homCongrLeftOverSubring`
(mirror of `Theorem5_18_1.homCongrRightOverSubring`) is proved here. The
biduality iso itself is the research core, isolated as
`multiplicitySpace_biduality_Aiso`.
-/

open scoped TensorProduct

universe u v

namespace Etingof

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- Pre-composition equivalence: an `R`-linear equivalence of the **domain**
induces a `k`-linear equivalence of hom-spaces (contravariantly). This is the
domain-side mirror of `homCongrRightOverSubring`, and like it works for
non-commutative `R` (where `LinearEquiv.congrLeft` does not apply directly). -/
noncomputable def homCongrLeftOverSubring
    (k : Type*) [CommSemiring k]
    (R : Type*) [Ring R] [Algebra k R]
    (E : Type*) [AddCommGroup E] [Module k E] [Module R E] [IsScalarTower k R E]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
    (e : M ≃ₗ[R] N) :
    (N →ₗ[R] E) ≃ₗ[k] (M →ₗ[R] E) where
  toFun f := f.comp e.toLinearMap
  invFun f := f.comp e.symm.toLinearMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp [LinearMap.smul_apply, LinearMap.comp_apply]

-- Heartbeats bumped: the `Module ↥(centralizer A) (↥S →ₗ[A] E)` instance
-- (`Theorem5_18_1.centralizerModuleHom`, a `Subalgebra → Module.End` chain)
-- needed to even state the `≃ₗ[C]` overruns the default 20000 synth /
-- 200000 elaboration budgets, exactly as in `SchurWeylLDistinct` / `Theorem5_18_1`.
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Biduality (research core).** For a simple `A`-submodule `S ≤ E` of a
faithful semisimple `A`-module, the curried evaluation
`↥S → (M_S →ₗ[C] E)`, `v ↦ (l ↦ l v)`, is an `A`-linear isomorphism, where
`M_S := ↥S →ₗ[A] E` and `C = centralizer(A)`. Consequently a `C`-iso of
multiplicity spaces yields an `A`-iso of the underlying simple modules.

This is the symmetric double-centralizer / biduality statement: re-running the
bimodule decomposition with `C` in the `A`-slot identifies `M_S →ₗ[C] E` with
the `S`-isotypic component, and the natural evaluation realises the matching. -/
theorem multiplicitySpace_biduality_Aiso
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    (S T : Submodule A E) [IsSimpleModule A S] [IsSimpleModule A T]
    (h : Nonempty ((↥S →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))]
      (↥T →ₗ[A] E))) :
    Nonempty (↥S ≃ₗ[A] ↥T) := by
  sorry

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Part 2: multiplicity-space `C`-distinctness.** Given a family `S'` of
simple `A`-submodules of `E` that are pairwise `A`-distinct (`hS'_dist`), a
`C`-linear isomorphism of multiplicity spaces `M_{S'_i} ≃ₗ[C] M_{S'_j}` forces
`i = j`. Here `A` is a semisimple subalgebra of `End_k(E)` acting faithfully,
`k` is algebraically closed, and `C = centralizer(A)`.

This is the B-side distinctness consumed by parent #4849: it upgrades the
multiplicity-space iso produced by Part 1 to the index identity needed to
complete the GL-equivariant Schur-Weyl decomposition. -/
theorem multiplicitySpace_Cdistinct
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    {ι : Type*} (S' : ι → Submodule A E) [∀ i, IsSimpleModule A (S' i)]
    (hS'_dist : ∀ i j, Nonempty (↥(S' i) ≃ₗ[A] ↥(S' j)) → i = j)
    (i j : ι)
    (h : Nonempty ((↥(S' i) →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))]
      (↥(S' j) →ₗ[A] E))) :
    i = j :=
  hS'_dist i j (multiplicitySpace_biduality_Aiso k E A (S' i) (S' j) h)

end Etingof
