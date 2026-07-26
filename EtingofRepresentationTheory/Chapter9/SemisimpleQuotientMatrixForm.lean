import EtingofRepresentationTheory.Chapter3.Theorem3_5_4_CompleteFamily
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Chapter9.Discussion_after_Definition9_7_1
import Mathlib.LinearAlgebra.Matrix.ToLin

universe u v w

/-!
# The semisimple quotient in matrix form

Etingof's discussion after Definition 9.7.1 refers to the Wedderburn decomposition of the
semisimple quotient in its matrix form,

`B_𝐧 / Rad(B_𝐧) = ⊕_i Mat_{n_i}(k)`,

and reads off from it that `B_(1,…,1)` is the only member of the family `{B_𝐧}` with commutative
semisimple quotient.

`Chapter9/Discussion_after_Definition9_7_1.lean` proves the commutativity criterion for the
product of matrix algebras `∀ i, Matrix (Fin (n i)) (Fin (n i)) k`
(`Etingof.semisimpleQuotient_comm_iff`). This file supplies the missing half: that for **any**
finite-dimensional algebra `A` over an algebraically closed field the actual quotient
`A / Rad(A)` really is such a product of matrix algebras, so the criterion applies to the
genuine object and not only to its Wedderburn model.

Theorem 3.5.4 (`Etingof.exists_structure_mod_radical`) already produces a finite complete family
`s` of pairwise non-isomorphic simples `A ⧸ M`, `M ∈ s`, together with

`A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} End_k (A ⧸ M)`.

Each `A ⧸ M` is finite dimensional, so choosing a basis identifies `End_k (A ⧸ M)` with the
matrix algebra `Mat_{d_M}(k)`, `d_M = dim_k (A ⧸ M)`; assembling these identifications over the
family gives

`A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} Mat_{d_M}(k)`.

Since a simple module is nonzero, every `d_M ≥ 1`, so `Etingof.semisimpleQuotient_comm_iff`
applies to the genuine quotient and yields: `A / Rad(A)` is commutative iff every `d_M = 1`.

## Results

* `Etingof.exists_matrix_structure_mod_radical` — the matrix form of Theorem 3.5.4.
* `Etingof.isBasicAlgebra_iff_of_matrixForm` — given any presentation of `A / Rad(A)` as
  `∏_i Mat_{d_i}(k)` with `d_i ≥ 1`, the quotient is commutative iff every `d_i = 1`.
* `Etingof.exists_matrix_structure_isBasicAlgebra_iff` — the two combined.
-/

open Module

namespace Etingof

section Transport

variable {R : Type*} {S : Type*} [Ring R] [Ring S]

/-- Commutativity of multiplication transports along a ring equivalence. -/
theorem mul_comm_of_ringEquiv (e : R ≃+* S) (h : ∀ x y : S, x * y = y * x) (x y : R) :
    x * y = y * x :=
  e.injective (by rw [map_mul, map_mul, h])

/-- Commutativity of multiplication is invariant under ring equivalence. -/
theorem mul_comm_iff_of_ringEquiv (e : R ≃+* S) :
    (∀ x y : R, x * y = y * x) ↔ ∀ x y : S, x * y = y * x :=
  ⟨fun h => mul_comm_of_ringEquiv e.symm h, fun h => mul_comm_of_ringEquiv e h⟩

end Transport

section MatrixForm

variable (k : Type w) (A : Type u)
variable [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]

omit [IsAlgClosed k] in
/-- A simple module over a finite-dimensional algebra has positive dimension: it is nonzero. -/
theorem one_le_finrank_of_isSimpleModule (M : Submodule A A) (hM : IsCoatom M) :
    1 ≤ finrank k (A ⧸ M) := by
  haveI : FiniteDimensional k (A ⧸ M) := finiteDimensional_quotient k A M
  haveI : IsSimpleModule A (A ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  haveI : Nontrivial (A ⧸ M) := IsSimpleModule.nontrivial A (A ⧸ M)
  exact finrank_pos

/-- **Theorem 3.5.4 in matrix form.** For a finite dimensional algebra `A` over an algebraically
closed field there is a finite complete family of pairwise non-isomorphic simple modules
`A ⧸ M`, `M ∈ s`, and

`A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} Mat_{d_M}(k)`,  `d_M = dim_k (A ⧸ M) ≥ 1`.

This is the form of the Wedderburn decomposition that Etingof uses in the discussion after
Definition 9.7.1, where the family of simples of `B_𝐧` is indexed by the simple objects of `𝒞`
and `d_i = n_i`. -/
theorem exists_matrix_structure_mod_radical :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      (∀ M : {x // x ∈ s}, 1 ≤ finrank k (A ⧸ (M : Submodule A A))) ∧
      Nonempty ((A ⧸ Etingof.Radical A) ≃ₐ[k]
        ∀ M : {x // x ∈ s},
          Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
            (Fin (finrank k (A ⧸ (M : Submodule A A)))) k) := by
  classical
  obtain ⟨s, hcoatom, -, hnoniso, hexh, ⟨e⟩⟩ := exists_structure_mod_radical k A
  haveI hfd : ∀ M : {x // x ∈ s}, FiniteDimensional k (A ⧸ (M : Submodule A A)) := fun M =>
    finiteDimensional_quotient k A _
  -- Choosing a basis of each simple turns its `k`-endomorphism algebra into a matrix algebra.
  let toMat : ∀ M : {x // x ∈ s},
      Module.End k (A ⧸ (M : Submodule A A)) ≃ₐ[k]
        Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
          (Fin (finrank k (A ⧸ (M : Submodule A A)))) k := fun M =>
    LinearMap.toMatrixAlgEquiv (Module.finBasis k (A ⧸ (M : Submodule A A)))
  exact ⟨s, hcoatom, hnoniso, hexh,
    fun M => one_le_finrank_of_isSimpleModule k A _ (hcoatom M M.2),
    ⟨e.trans (AlgEquiv.piCongrRight toMat)⟩⟩

omit [IsAlgClosed k] [FiniteDimensional k A] in
/-- Definition 9.7.2's "`A / Rad(A)` is commutative" written with the Chapter 3 radical
`Etingof.Radical A = Ideal.jacobson ⊥`, which is the ideal Theorem 3.5.4 quotients by.
`Etingof.IsBasicAlgebra` is phrased with `Ring.jacobson A`; the two ideals are equal
(`Ideal.jacobson_bot`), so the quotients are isomorphic rings. -/
theorem isBasicAlgebra_iff_comm_radicalQuotient :
    Etingof.IsBasicAlgebra k A ↔ ∀ x y : A ⧸ Etingof.Radical A, x * y = y * x :=
  (mul_comm_iff_of_ringEquiv (Ideal.quotEquivOfEq (Ideal.jacobson_bot (R := A)))).symm

omit [IsAlgClosed k] [FiniteDimensional k A] in
/-- **Etingof's commutativity criterion, for the genuine semisimple quotient.** If the actual
quotient `A / Rad(A)` is presented as a product of matrix algebras `∏_i Mat_{d_i}(k)` with every
`d_i ≥ 1`, then `A` is basic in the sense of Definition 9.7.2 (i.e. `A / Rad(A)` is commutative)
iff every `d_i = 1`.

This is the reading of "`B_𝐧 / Rad(B_𝐧) = ⊕_i Mat_{n_i}(k)` is commutative iff every `n_i = 1`"
in which `Rad` is the honest Jacobson radical of the honest algebra:
`Etingof.semisimpleQuotient_comm_iff` proves the criterion for the product of matrix algebras,
and it transports along the presenting isomorphism. -/
theorem isBasicAlgebra_iff_of_matrixForm {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (e : (A ⧸ Etingof.Radical A) ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Etingof.IsBasicAlgebra k A ↔ ∀ i, d i = 1 := by
  rw [isBasicAlgebra_iff_comm_radicalQuotient k A, mul_comm_iff_of_ringEquiv e.toRingEquiv]
  exact semisimpleQuotient_comm_iff (k := k) d hd

/-- **The commutativity criterion for the genuine semisimple quotient, existential form.**
For a finite dimensional algebra `A` over an algebraically closed field there is a finite
complete family of pairwise non-isomorphic simples `A ⧸ M`, `M ∈ s`, presenting

`A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} Mat_{d_M}(k)`,  `d_M = dim_k (A ⧸ M) ≥ 1`,

and `A / Rad(A)` is commutative exactly when every `d_M = 1`. Specialised to `A = B_𝐧` (where
`d_M = n_M`) this is Etingof's assertion, in the discussion after Definition 9.7.1, that
`B_(1,…,1)` is the only member of the family `{B_𝐧}` with commutative semisimple quotient. -/
theorem exists_matrix_structure_isBasicAlgebra_iff :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      (∀ M : {x // x ∈ s}, 1 ≤ finrank k (A ⧸ (M : Submodule A A))) ∧
      Nonempty ((A ⧸ Etingof.Radical A) ≃ₐ[k]
        ∀ M : {x // x ∈ s},
          Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
            (Fin (finrank k (A ⧸ (M : Submodule A A)))) k) ∧
      (Etingof.IsBasicAlgebra k A ↔
        ∀ M : {x // x ∈ s}, finrank k (A ⧸ (M : Submodule A A)) = 1) := by
  obtain ⟨s, hcoatom, hnoniso, hexh, hpos, ⟨e⟩⟩ := exists_matrix_structure_mod_radical k A
  exact ⟨s, hcoatom, hnoniso, hexh, hpos, ⟨e⟩,
    isBasicAlgebra_iff_of_matrixForm k A _ hpos e⟩

end MatrixForm

end Etingof
