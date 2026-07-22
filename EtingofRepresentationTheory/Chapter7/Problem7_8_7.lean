import Mathlib

/-!
# Problem 7.8.7: The tensor product of complexes and the Künneth formula

**Problem 7.8.7.** Let `C•` and `D•` be complexes of modules over a commutative ring `A`.
Define the tensor product complex `(C ⊗ D)•` by the formula

`(C ⊗ D)_i = ⨁_{j+m=i} C_j ⊗_A D_m`,

with differentials

`d_i^{C⊗D}|_{C_j ⊗ D_m} = d_j^C ⊗ 1 + (-1)^j · 1 ⊗ d_m^D`.

* (i) Show that this is a complex.
* Now assume that `A = k` is a field.
* (ii) Show that if `C` or `D` is an exact sequence, then so is `C ⊗ D`.
  (Hint: Use the decomposition of Exercise 7.8.4.)
* (iii) Show that any complex `C` can be identified with a direct sum of an exact sequence
  and the complex consisting of `Hⁱ(C)` with the zero differentials, in such a way that the
  induced isomorphism `Hⁱ(C) → Hⁱ(C)` is the identity.
* (iv) Show that there is a natural isomorphism of vector spaces
  `Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. This is the **Künneth** formula.

## Formalization

We model complexes as `CochainComplex (ModuleCat k) ℤ` (i.e.
`HomologicalComplex (ModuleCat k) (ComplexShape.up ℤ)`). Mathlib's
`HomologicalComplex.tensorObj` is exactly the tensor product complex of the statement: the
degree-`i` object is the coproduct of `Cⱼ ⊗ Dₘ` over `j + m = i` (with `j + m = i` supplied
by `ComplexShape.up ℤ` via `TensorSigns`) and its differential carries the Koszul sign
`(-1)ʲ`, matching Etingof's formula. We write `Etingof.tensorComplex C D` for it.

* **(i)** `Etingof.Problem7_8_7_i` records that `tensorComplex C D` is a complex
  (`d ≫ d = 0` in every degree); it holds by construction (`HomologicalComplex.d_comp_d`).
* **(ii)** `Etingof.Problem7_8_7_ii`: over a field, if `C` or `D` is acyclic then so is
  `C ⊗ D`.
* **(iii)** `Etingof.Problem7_8_7_iii`: every complex `C` is isomorphic to
  `E ⊞ (homologyZeroComplex C)` with `E` acyclic, where `homologyZeroComplex C` is the
  complex whose degree-`i` object is `Hⁱ(C)` with zero differentials. The clause "the
  induced isomorphism `Hⁱ(C) → Hⁱ(C)` is the identity" is encoded as: the map
  `homologyZeroComplex C ⟶ C` given by `biprod.inr ≫ iso.inv` induces an isomorphism on
  `Hⁱ` (its `homologyMap` is `IsIso`); since `Hⁱ(homologyZeroComplex C)` is canonically
  `Hⁱ(C)`, this is exactly the "identity on homology" refinement.
* **(iv)** `Etingof.Problem7_8_7_iv` (Künneth): `Hⁱ(C ⊗ D)` is isomorphic to the coproduct
  of `Hʲ(C) ⊗ Hᵐ(D)` over `j + m = i`.
-/

open CategoryTheory Limits MonoidalCategory

namespace Etingof

variable {k : Type} [Field k]

/-- Etingof's tensor product complex `(C ⊗ D)•`, with degree-`i` object `⨁_{j+m=i} Cⱼ ⊗ Dₘ`
and the Koszul-signed differential `dᶜ ⊗ 1 + (-1)ʲ · 1 ⊗ dᴰ`. This is Mathlib's
`HomologicalComplex.tensorObj`. -/
noncomputable def tensorComplex (C D : CochainComplex (ModuleCat.{0} k) ℤ) :
    CochainComplex (ModuleCat.{0} k) ℤ :=
  HomologicalComplex.tensorObj C D

/-- The complex whose degree-`i` object is the homology `Hⁱ(C)` and whose differentials are
all zero (used in part (iii)). -/
noncomputable def homologyZeroComplex (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    CochainComplex (ModuleCat.{0} k) ℤ where
  X i := C.homology i
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Problem 7.8.7(i): the tensor product `C ⊗ D` is a complex, i.e. consecutive
differentials compose to zero. -/
theorem Problem7_8_7_i (C D : CochainComplex (ModuleCat.{0} k) ℤ) (i j l : ℤ) :
    (tensorComplex C D).d i j ≫ (tensorComplex C D).d j l = 0 :=
  (tensorComplex C D).d_comp_d i j l

/-- Problem 7.8.7(ii): over a field, if either factor is an exact (acyclic) complex, then so
is the tensor product `C ⊗ D`. -/
theorem Problem7_8_7_ii (C D : CochainComplex (ModuleCat.{0} k) ℤ)
    (h : C.Acyclic ∨ D.Acyclic) :
    (tensorComplex C D).Acyclic := by
  sorry

/-- Problem 7.8.7(iii): every complex `C` decomposes as a direct sum of an acyclic complex
`E` and the zero-differential complex on its homology `Hⁱ(C)`, in a way that induces the
identity on homology (encoded here as: the summand map `homologyZeroComplex C ⟶ C` is a
homology isomorphism in every degree). -/
theorem Problem7_8_7_iii (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{0} k) ℤ) (_ : E.Acyclic)
      (iso : C ≅ E ⊞ homologyZeroComplex C),
      ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap
        ((biprod.inr : homologyZeroComplex C ⟶ E ⊞ homologyZeroComplex C) ≫ iso.inv) i) := by
  sorry

/-- Problem 7.8.7(iv), the **Künneth formula**: there is a natural isomorphism of vector
spaces `Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. -/
theorem Problem7_8_7_iv (C D : CochainComplex (ModuleCat.{0} k) ℤ) (i : ℤ) :
    Nonempty ((tensorComplex C D).homology i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) := by
  sorry

end Etingof
