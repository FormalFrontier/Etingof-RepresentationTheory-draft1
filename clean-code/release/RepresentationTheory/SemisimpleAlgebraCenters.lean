/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Semisimple Algebra Centers

Results on centers of semisimple algebras.
-/

open scoped Classical in
noncomputable section

namespace RepresentationTheory.SemisimpleAlgebraCenters

open Subalgebra Module

variable {k : Type*} [Field k]

/-- The center of a product of algebras is linearly equivalent to the product of their centers. -/
def centerPiLinearEquiv {ι : Type*} {S : ι → Type*} [∀ i, Ring (S i)]
    [∀ i, Algebra k (S i)] :
    Subalgebra.center k (Π i, S i) ≃ₗ[k] Π i, Subalgebra.center k (S i) where
  toFun x i := ⟨(x : Π i, S i) i, by
    classical
    rw [Subalgebra.mem_center_iff]
    intro b
    simpa [Pi.mul_apply, Pi.single_eq_same] using
      congrFun (Subalgebra.mem_center_iff.mp x.2 (Pi.single i b)) i⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun f := ⟨fun i => (f i : S i), by
    rw [Subalgebra.mem_center_iff]
    intro c
    funext i
    simpa [Pi.mul_apply] using (Subalgebra.mem_center_iff.mp (f i).2) (c i)⟩
  left_inv x := by ext i; rfl
  right_inv f := by ext i; rfl

/-- An algebra equivalence maps the center of its source onto the center of its target. -/
theorem map_center_eq_of_algEquiv {R P : Type*} [Ring R] [Ring P] [Algebra k R]
    [Algebra k P] (e : R ≃ₐ[k] P) :
    (Subalgebra.center k R).map (e : R →ₐ[k] P) = Subalgebra.center k P := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subalgebra.mem_center_iff] at hx ⊢
    intro b
    simp only [AlgEquiv.coe_algHom]
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hx a]
  · intro hy
    rw [Subalgebra.mem_center_iff] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subalgebra.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e a)

/-- Algebra-equivalent algebras have centers of equal dimension. -/
theorem center_finrank_eq_of_algEquiv {R P : Type*} [Ring R] [Ring P] [Algebra k R]
    [Algebra k P] (e : R ≃ₐ[k] P) :
    Module.finrank k (Subalgebra.center k R) = Module.finrank k (Subalgebra.center k P) :=
  LinearEquiv.finrank_eq
    ((AlgEquiv.subalgebraMap e (Subalgebra.center k R)).trans
      (Subalgebra.equivOfEq _ _ (map_center_eq_of_algEquiv e))).toLinearEquiv

/-- The center of a nonempty finite square matrix algebra has dimension one. -/
theorem center_matrix_finrank {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    Module.finrank k (Subalgebra.center k (Matrix n n k)) = 1 := by
  have : Nontrivial (Matrix n n k) := inferInstance
  rw [Algebra.IsCentral.center_eq_bot,
    LinearEquiv.finrank_eq (Algebra.botEquiv k (Matrix n n k)).toLinearEquiv, finrank_self]

/-- The center of a finite product of nonzero matrix algebras has dimension equal to the number of factors. -/
theorem center_pi_matrix_finrank {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i ≠ 0) :
    Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k))
      = Fintype.card ι := by
  rw [LinearEquiv.finrank_eq centerPiLinearEquiv, Module.finrank_pi_fintype]
  have : ∀ i, Module.finrank k (Subalgebra.center k (Matrix (Fin (d i)) (Fin (d i)) k)) = 1 := by
    intro i
    have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (hd i)⟩⟩
    exact center_matrix_finrank
  simp [this]

/-- An algebra equivalent to a finite product of nonzero matrix algebras has center dimension equal to the number of factors. -/
theorem center_finrank_eq_card_of_algEquiv_pi_matrix {R : Type*} [Ring R] [Algebra k R]
    {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, d i ≠ 0)
    (e : R ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Module.finrank k (Subalgebra.center k R) = Fintype.card ι := by
  rw [center_finrank_eq_of_algEquiv e, center_pi_matrix_finrank hd]

/-- A finite-dimensional semisimple algebra over an algebraically closed field is equivalent to a finite product of nonzero matrix algebras indexed by the dimension of its center. -/
theorem exists_algEquiv_pi_matrix_of_isSemisimpleRing {k : Type*} [Field k] [IsAlgClosed k]
    (R : Type*) [Ring R] [Algebra k R] [IsSemisimpleRing R] [FiniteDimensional k R] :
    ∃ d : Fin (Module.finrank k (Subalgebra.center k R)) → ℕ, (∀ i, d i ≠ 0) ∧
      Nonempty (R ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k R
  have hdne : ∀ i, d i ≠ 0 := fun i => (hd i).out
  have hn : Module.finrank k (Subalgebra.center k R) = n := by
    rw [center_finrank_eq_card_of_algEquiv_pi_matrix hdne e, Fintype.card_fin]
  subst hn
  exact ⟨d, hdne, ⟨e⟩⟩

set_option linter.unusedFintypeInType false in
/-- A finite group algebra over an algebraically closed field of characteristic zero is equivalent to a product of nonzero matrix algebras indexed by the dimension of its center. -/
theorem exists_algEquiv_pi_matrix_monoidAlgebra {k : Type*} [Field k]
    [IsAlgClosed k] [CharZero k] (G : Type*) [Group G] [Fintype G] :
    ∃ d : Fin (Module.finrank k (Subalgebra.center k (MonoidAlgebra k G))) → ℕ,
      (∀ i, d i ≠ 0) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  haveI : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  exact exists_algEquiv_pi_matrix_of_isSemisimpleRing (MonoidAlgebra k G)

end RepresentationTheory.SemisimpleAlgebraCenters

end
