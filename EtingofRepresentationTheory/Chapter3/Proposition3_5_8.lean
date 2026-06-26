import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.List.TFAE
import EtingofRepresentationTheory.Chapter3.Theorem3_5_4

/-!
# Proposition 3.5.8: Equivalent Characterizations of Semisimple Algebras

For a finite dimensional algebra `A` over an algebraically closed field `k`, the following are
equivalent:

(1) `A` is semisimple (`Rad(A) = 0`, i.e. `IsSemisimpleRing A`).
(2) `∑ᵢ (dim Vᵢ)² = dim A`, where the `Vᵢ` are the irreducible representations of `A`.
(3) `A ≅ ⊕ᵢ Mat_{dᵢ}(k)` for some `dᵢ`.
(4) Any finite dimensional representation of `A` is completely reducible.
(5) `A` is a completely reducible representation of `A`.

The proof follows Etingof: `(1) ⇔ (2)` by the dimension count
`dim A - dim Rad(A) = ∑ᵢ (dim Vᵢ)²` coming from Theorem 3.5.4 (`A / Rad(A) ≅ ⊕ᵢ End Vᵢ`);
`(1) ⇒ (3)` by Wedderburn–Artin over an algebraically closed field; `(3) ⇒ (4)` because a
finite product of matrix algebras is semisimple, so all its modules are; `(4) ⇒ (5)` by
specializing to `A` itself; and `(5) ⇒ (1)` definitionally (`IsSemisimpleRing` *is*
`IsSemisimpleModule A A`).
-/

open Module

universe u

/-- Equivalent characterizations of semisimple algebras, stated relative to a complete set
`V : ι → Type` of pairwise nonisomorphic irreducible representations (the same data as in
Theorem 3.5.4). Etingof Proposition 3.5.8. -/
theorem Etingof.semisimple_algebra_equiv (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    [ -- (1) A is semisimple
      IsSemisimpleRing A,
      -- (2) ∑ᵢ (dim Vᵢ)² = dim A
      ∑ i, finrank k (V i) ^ 2 = finrank k A,
      -- (3) A ≅ ⊕ᵢ Mat_{dᵢ}(k)
      ∃ (n : ℕ) (d : Fin n → ℕ), (∀ j, NeZero (d j)) ∧
        Nonempty (A ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k),
      -- (4) every finite dimensional representation of A is completely reducible
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
        [FiniteDimensional k M], IsSemisimpleModule A M,
      -- (5) A is a completely reducible representation of A
      IsSemisimpleModule A A ].TFAE := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Theorem 3.5.4: `A / Rad(A) ≅ ⊕ᵢ End_k(Vᵢ)`, so `dim(A/Rad) = ∑ᵢ (dim Vᵢ)²`.
  have key : finrank k (A ⧸ Etingof.Radical A) = ∑ i, finrank k (V i) ^ 2 := by
    obtain ⟨e⟩ := Etingof.structure_mod_radical k A ι V h_noniso h_complete
    calc finrank k (A ⧸ Etingof.Radical A)
        = finrank k (∀ i, End k (V i)) := e.toLinearEquiv.finrank_eq
      _ = ∑ i, finrank k (End k (V i)) := finrank_pi_fintype k
      _ = ∑ i, finrank k (V i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sq, ← finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)]
  -- `dim(A/Rad) + dim Rad = dim A`, with `Rad` viewed as a `k`-submodule.
  have bridge : finrank k (A ⧸ Etingof.Radical A)
      + finrank k ((Etingof.Radical A).restrictScalars k) = finrank k A := by
    have h := Submodule.finrank_quotient_add_finrank ((Etingof.Radical A).restrictScalars k)
    rwa [(Submodule.Quotient.restrictScalarsEquiv k (Etingof.Radical A)).finrank_eq] at h
  -- `Rad(A) = ⊥ ↔ IsSemisimpleRing A`, with `Rad(A) = Ring.jacobson A`.
  have rad_jac : Etingof.Radical A = ⊥ ↔ IsSemisimpleRing A := by
    rw [Etingof.Radical, Ideal.jacobson_bot, ← IsArtinianRing.isSemisimpleRing_iff_jacobson]
  tfae_have 1 → 2 := by
    intro h1
    -- semisimple ⇒ Rad = ⊥ ⇒ its `k`-dimension is 0 ⇒ `dim A = ∑ᵢ (dim Vᵢ)²`.
    have hbot : Etingof.Radical A = ⊥ := rad_jac.mpr h1
    have : ((Etingof.Radical A).restrictScalars k) = ⊥ := by
      rw [hbot, Submodule.restrictScalars_bot]
    rw [← bridge, this, finrank_bot, add_zero, key]
  tfae_have 2 → 1 := by
    intro h2
    -- `dim A = ∑ᵢ (dim Vᵢ)²` ⇒ `dim Rad = 0` ⇒ `Rad = ⊥` ⇒ semisimple.
    rw [← rad_jac]
    have hr : finrank k ((Etingof.Radical A).restrictScalars k) = 0 := by
      have := bridge
      rw [key, ← h2] at this
      omega
    rw [← Submodule.restrictScalars_eq_bot_iff (S := k)]
    exact Submodule.finrank_eq_zero.mp hr
  tfae_have 1 → 3 := by
    intro h1
    exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k A
  tfae_have 3 → 1 := by
    rintro ⟨n, d, _, ⟨e⟩⟩
    exact e.toRingEquiv.symm.isSemisimpleRing
  tfae_have 1 → 4 := by
    intro h1 M _ _ _ _ _
    exact IsSemisimpleRing.isSemisimpleModule
  tfae_have 4 → 5 := fun h4 => h4 A
  tfae_have 5 → 1 := id
  tfae_finish
