import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# Example 2.2.4: Examples of Algebras

Examples of algebras over k:
1. A = k.
2. A = k[x₁, …, xₙ], the algebra of polynomials.
3. A = End V, the algebra of endomorphisms of a vector space V.
4. The free algebra A = k⟨x₁, …, xₙ⟩.
5. The group algebra A = k[G] of a group G.

## Mathlib correspondence

Exact match. All five examples have Mathlib counterparts:
- k as an algebra over itself
- `MvPolynomial (Fin n) k` for polynomial algebras in `n` variables
- `Module.End` for endomorphism algebras
- `FreeAlgebra` for free algebras
- `MonoidAlgebra` for group algebras
-/

/-- k is an algebra over itself. (Etingof Example 2.2.4(1)) -/
example (k : Type*) [CommRing k] : Algebra k k := inferInstance

/-- The polynomial algebra `k[x₁, ..., xₙ]` is an algebra over `k`.
(Etingof Example 2.2.4(2)) -/
noncomputable example (k : Type*) [CommRing k] (n : ℕ) :
    Algebra k (MvPolynomial (Fin n) k) := inferInstance

/-- End(V) is an algebra over k. (Etingof Example 2.2.4(3)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] :
    Algebra k (Module.End k V) := inferInstance

/-- Multiplication in `End(V)` is composition of operators. -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V]
    (f g : Module.End k V) : f * g = f.comp g := rfl

/-- The free algebra k⟨x₁, …, xₙ⟩ is an algebra over k. (Etingof Example 2.2.4(4)) -/
example (k : Type*) [CommRing k] (n : ℕ) : Algebra k (FreeAlgebra k (Fin n)) := inferInstance

/-- Words in the generators form the standard basis of the free algebra. -/
noncomputable example (k : Type*) [CommRing k] (n : ℕ) :
    Module.Basis (FreeMonoid (Fin n)) k (FreeAlgebra k (Fin n)) :=
  FreeAlgebra.basisFreeMonoid k (Fin n)

/-- Multiplication of word-basis vectors in a free algebra is concatenation of words. -/
example (k : Type*) [CommRing k] (n : ℕ) (u v : FreeMonoid (Fin n)) :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n))
        ((FreeAlgebra.basisFreeMonoid k (Fin n)) u *
          (FreeAlgebra.basisFreeMonoid k (Fin n)) v) =
      MonoidAlgebra.single (u * v) 1 := by
  rw [map_mul]
  have hu :
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n))
          ((FreeAlgebra.basisFreeMonoid k (Fin n)) u) = MonoidAlgebra.single u 1 := by
    change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n))
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n)).symm
          (MonoidAlgebra.single u 1)) = _
    exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n)).apply_symm_apply _
  have hv :
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n))
          ((FreeAlgebra.basisFreeMonoid k (Fin n)) v) = MonoidAlgebra.single v 1 := by
    change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n))
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n)).symm
          (MonoidAlgebra.single v 1)) = _
    exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin n)).apply_symm_apply _
  rw [hu, hv]
  simp

/-- The group algebra k[G] is an algebra over k. (Etingof Example 2.2.4(5)) -/
noncomputable example (k : Type*) [CommRing k] (G : Type*) [Group G] :
    Algebra k (MonoidAlgebra k G) := inferInstance

/-- The elements `a_g` indexed by `g : G` form the standard basis of the group algebra. -/
noncomputable example (k : Type*) [CommRing k] (G : Type*) [Group G] :
    Module.Basis G k (MonoidAlgebra k G) :=
  MonoidAlgebra.basis G k

/-- The group-algebra basis obeys `a_g a_h = a_{gh}`. -/
example (k : Type*) [CommRing k] (G : Type*) [Group G] (g h : G) :
    MonoidAlgebra.single g (1 : k) * MonoidAlgebra.single h 1 =
      MonoidAlgebra.single (g * h) 1 := by
  simp
