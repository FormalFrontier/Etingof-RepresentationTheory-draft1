import Mathlib.RingTheory.Morita.Matrix
import EtingofRepresentationTheory.Chapter9.Discussion_after_Definition9_7_1

/-!
# Remark 7.7.4: the module category does not determine the ring

Etingof's Remark 7.7.4 warns that Definition 7.7.1 (visualizing an abelian category as the
category of modules over a ring `A`) has a drawback: even when `𝒞` is the whole category
`A`-mod, the ring `A` is **not** determined by `𝒞`. Two different, nonisomorphic rings can have
equivalent module categories; such rings are called **Morita equivalent**.

This file records a concrete witness of that phenomenon: `R = ℚ` and its `2 × 2` matrix ring
`Matrix (Fin 2) (Fin 2) ℚ`.

* Their module categories are equivalent (`nonempty_moduleCat_equiv_matrix`), via Mathlib's
  `ModuleCat.matrixEquivalence`. This is the positive, Morita-equivalence half.
* Yet they are not isomorphic as rings (`isEmpty_ringEquiv_matrix`): a ring isomorphism out of
  the commutative ring `ℚ` would transport commutativity to `Matrix (Fin 2) (Fin 2) ℚ`, which is
  noncommutative (`Etingof.exists_matrix_not_comm_of_ne`).

`morita_equivalent_not_ringEquiv` packages the two halves as the counterexample asserted by the
remark. The further philosophical claim of the remark — that many abelian categories admit no
natural or manageable ring `A` at all — remains prose.
-/

open CategoryTheory

namespace Etingof

/-- **Remark 7.7.4 (positive half).** `ℚ` and its `2 × 2` matrix ring have equivalent module
categories, i.e. they are Morita equivalent. This is `ModuleCat.matrixEquivalence` for the index
`Fin 2` and base ring `ℚ`. -/
theorem nonempty_moduleCat_equiv_matrix :
    Nonempty (ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ)) :=
  ⟨ModuleCat.matrixEquivalence ℚ (0 : Fin 2)⟩

/-- **Remark 7.7.4 (negative half).** There is no ring isomorphism `ℚ ≃+* Matrix (Fin 2) (Fin 2) ℚ`.
A ring isomorphism out of the commutative ring `ℚ` would make its image commutative, but the matrix
ring is noncommutative (`Etingof.exists_matrix_not_comm_of_ne`, using the distinct indices `0 ≠ 1`
in `Fin 2`). -/
theorem isEmpty_ringEquiv_matrix :
    IsEmpty (ℚ ≃+* Matrix (Fin 2) (Fin 2) ℚ) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨x, y, hxy⟩ :=
    exists_matrix_not_comm_of_ne (k := ℚ) (m := Fin 2) (a := 0) (b := 1) (by decide)
  refine hxy ?_
  -- A ring equivalence transports commutativity of `ℚ` to `Matrix (Fin 2) (Fin 2) ℚ`.
  have ha : f (f.symm x) = x := f.apply_symm_apply x
  have hb : f (f.symm y) = y := f.apply_symm_apply y
  calc
    x * y = f (f.symm x) * f (f.symm y) := by rw [ha, hb]
    _ = f (f.symm x * f.symm y) := (f.map_mul _ _).symm
    _ = f (f.symm y * f.symm x) := by rw [mul_comm]
    _ = f (f.symm y) * f (f.symm x) := f.map_mul _ _
    _ = y * x := by rw [ha, hb]

/-- **Remark 7.7.4.** The module category does not determine the ring: `ℚ` and
`Matrix (Fin 2) (Fin 2) ℚ` have equivalent module categories (they are Morita equivalent) yet are
not isomorphic as rings. -/
theorem morita_equivalent_not_ringEquiv :
    Nonempty (ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ)) ∧
      IsEmpty (ℚ ≃+* Matrix (Fin 2) (Fin 2) ℚ) :=
  ⟨nonempty_moduleCat_equiv_matrix, isEmpty_ringEquiv_matrix⟩

end Etingof
