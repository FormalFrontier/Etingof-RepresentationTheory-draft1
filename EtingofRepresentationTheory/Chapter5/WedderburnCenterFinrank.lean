import Mathlib

/-!
# The center of a semisimple algebra: the Wedderburn dimension count

This file supplies the "Wedderburn half" of the character-theoretic bridge
`#(irreducible ℂ-reps of `G`) = #(ConjClasses `G`)`.  The group-algebra half
computes `finrank_k Z(k[G]) = #(ConjClasses G)`; here we compute the same
dimension from the Wedderburn decomposition.

For a finite-dimensional algebra `R` over a field `k` that is isomorphic (as a
`k`-algebra) to a finite product `Π i, Matrix (Fin (d i)) (Fin (d i)) k` of
matrix algebras with each `d i` nonzero, the center `Z(R)` has
`k`-dimension equal to the number of matrix factors:

* `Etingof.finrank_center_eq_card_of_algEquiv_pi_matrix` —
  `Module.finrank k ↥(Subalgebra.center k R) = Fintype.card ι`.

Combined with the Artin–Wedderburn theorem over an algebraically closed field
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`) this gives, for a
finite-dimensional semisimple algebra over an algebraically closed field, that
the number of Wedderburn factors equals `finrank` of the center:

* `Etingof.exists_wedderburn_factors_eq_finrank_center` and its `MonoidAlgebra`
  specialization `Etingof.finrank_center_monoidAlgebra_eq_wedderburn_factors`.

## Route

* Center transports along an algebra isomorphism (`Etingof.map_center_algEquiv`),
  so `finrank_k Z(R) = finrank_k Z(P)` for `P` the product.
* `Subalgebra.center_pi`: the center of a product is the product of the centers,
  packaged here as a `k`-linear equivalence `Etingof.centerPiLinearEquiv`.
* Over a field each `Matrix (Fin (d i)) (Fin (d i)) k` is a central algebra
  (`Algebra.IsCentral.matrix`), so its center is `⊥`, of dimension `1`
  (`Algebra.botEquiv`) whenever `d i ≠ 0`.
* `Module.finrank_pi_fintype` sums the `1`s over `ι`, giving `Fintype.card ι`.
-/

open scoped Classical in
noncomputable section

namespace Etingof

open Subalgebra Module

variable {k : Type*} [Field k]

/-- The center of a product of algebras, viewed componentwise: a `k`-linear
equivalence between `Z(Π i, S i)` and `Π i, Z(S i)`. -/
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

/-- The center is preserved by an algebra isomorphism: the image of `Z(R)` under
`e : R ≃ₐ[k] P` is `Z(P)`. -/
theorem map_center_algEquiv {R P : Type*} [Ring R] [Ring P] [Algebra k R]
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

/-- The center's `k`-dimension is invariant under an algebra isomorphism. -/
theorem finrank_center_congr {R P : Type*} [Ring R] [Ring P] [Algebra k R]
    [Algebra k P] (e : R ≃ₐ[k] P) :
    Module.finrank k (Subalgebra.center k R) = Module.finrank k (Subalgebra.center k P) :=
  LinearEquiv.finrank_eq
    ((AlgEquiv.subalgebraMap e (Subalgebra.center k R)).trans
      (Subalgebra.equivOfEq _ _ (map_center_algEquiv e))).toLinearEquiv

/-- Over a field, the center of a nontrivial matrix algebra has dimension `1`. -/
theorem finrank_center_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    Module.finrank k (Subalgebra.center k (Matrix n n k)) = 1 := by
  have : Nontrivial (Matrix n n k) := inferInstance
  rw [Algebra.IsCentral.center_eq_bot,
    LinearEquiv.finrank_eq (Algebra.botEquiv k (Matrix n n k)).toLinearEquiv, finrank_self]

/-- **The center of a product of matrix algebras.** For a `Fintype`-indexed
family with each `d i` nonzero, the center of `Π i, Matrix (Fin (d i)) (Fin (d i)) k`
has `k`-dimension equal to the number of factors. -/
theorem finrank_center_pi_matrix {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i ≠ 0) :
    Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k))
      = Fintype.card ι := by
  rw [LinearEquiv.finrank_eq centerPiLinearEquiv, Module.finrank_pi_fintype]
  have : ∀ i, Module.finrank k (Subalgebra.center k (Matrix (Fin (d i)) (Fin (d i)) k)) = 1 := by
    intro i
    have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (hd i)⟩⟩
    exact finrank_center_matrix
  simp [this]

/-- **The Wedderburn dimension count.** For a field `k` and a `k`-algebra `R`
carrying an algebra equivalence to a finite product of matrix algebras
`Π i, Matrix (Fin (d i)) (Fin (d i)) k` with each `d i` nonzero, the center of
`R` has `k`-dimension equal to the number of matrix factors. -/
theorem finrank_center_eq_card_of_algEquiv_pi_matrix {R : Type*} [Ring R] [Algebra k R]
    {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, d i ≠ 0)
    (e : R ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Module.finrank k (Subalgebra.center k R) = Fintype.card ι := by
  rw [finrank_center_congr e, finrank_center_pi_matrix hd]

/-- **Artin–Wedderburn dimension count over an algebraically closed field.** A
finite-dimensional semisimple algebra `R` over an algebraically closed field `k`
splits as a product of `finrank_k Z(R)` matrix algebras: there is an algebra
equivalence `R ≃ₐ[k] Π i : Fin (finrank_k Z(R)), Matrix (Fin (d i)) (Fin (d i)) k`
with each `d i` nonzero. -/
theorem exists_wedderburn_factors_eq_finrank_center {k : Type*} [Field k] [IsAlgClosed k]
    (R : Type*) [Ring R] [Algebra k R] [IsSemisimpleRing R] [FiniteDimensional k R] :
    ∃ d : Fin (Module.finrank k (Subalgebra.center k R)) → ℕ, (∀ i, d i ≠ 0) ∧
      Nonempty (R ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k R
  have hdne : ∀ i, d i ≠ 0 := fun i => (hd i).out
  have hn : Module.finrank k (Subalgebra.center k R) = n := by
    rw [finrank_center_eq_card_of_algEquiv_pi_matrix hdne e, Fintype.card_fin]
  subst hn
  exact ⟨d, hdne, ⟨e⟩⟩

set_option linter.unusedFintypeInType false in
/-- The number of Wedderburn factors of `k[G]` for a finite group `G` over an
algebraically closed field of characteristic zero equals `finrank_k Z(k[G])`.
This is the Wedderburn side of the counting bridge; the group-algebra side
identifies the same dimension with `#(ConjClasses G)`. -/
theorem finrank_center_monoidAlgebra_eq_wedderburn_factors {k : Type*} [Field k]
    [IsAlgClosed k] [CharZero k] (G : Type*) [Group G] [Fintype G] :
    ∃ d : Fin (Module.finrank k (Subalgebra.center k (MonoidAlgebra k G))) → ℕ,
      (∀ i, d i ≠ 0) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  haveI : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  exact exists_wedderburn_factors_eq_finrank_center (MonoidAlgebra k G)

end Etingof

end
