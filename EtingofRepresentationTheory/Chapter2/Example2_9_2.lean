import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Derivation.Lie

/-!
# Example 2.9.2: Examples of Lie Algebras

The book lists the following examples of Lie algebras:

(1) Any space `𝔤` with `[·, ·] = 0` (abelian Lie algebra).
(2) Any associative algebra `A` with `[a, b] = ab − ba`, in particular `End(V)`, denoted `𝔤𝔩(V)`.
(3) Any subspace `U` of an associative algebra `A` closed under `[·, ·]`.
(4) The space `Der(A)` of derivations of an algebra `A`, i.e. linear maps `D : A → A` satisfying
    the Leibniz rule `D(ab) = D(a) b + a D(b)`.

## Mathlib correspondence

All four are formalized below.

- (1) is built explicitly as the type synonym `Etingof.Example2_9_2.Abelian k V`, the module `V`
  equipped with the zero bracket; we prove it is an `IsLieAbelian` Lie algebra.
- (2) uses the `LieRing`/`LieAlgebra` instances coming from the ring commutator
  (`Mathlib.Algebra.Lie.OfAssociative`), with `End(V) = 𝔤𝔩(V)` as the named special case.
- (3) is a `LieSubalgebra k A` of an associative algebra `A` regarded as a Lie algebra.
- (4) is `Derivation k A A`, whose `LieAlgebra` instance lives in
  `Mathlib.RingTheory.Derivation.Lie`; we record that its defining Leibniz rule is exactly the
  book's, and that its bracket is the commutator `D₁ ∘ D₂ − D₂ ∘ D₁`.
-/

namespace Etingof.Example2_9_2

/-! ## (1) Abelian Lie algebra: any space with `[·, ·] = 0` -/

/-- The **abelian Lie algebra** on a `k`-module `V`: the underlying additive group of `V`
equipped with the zero bracket `[·, ·] = 0`. (Etingof Example 2.9.2(1)) -/
def Abelian (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V] : Type _ := V

namespace Abelian

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

instance : AddCommGroup (Abelian k V) := inferInstanceAs (AddCommGroup V)
instance : Module k (Abelian k V) := inferInstanceAs (Module k V)
instance : Bracket (Abelian k V) (Abelian k V) := ⟨fun _ _ => 0⟩

@[simp] theorem bracket_eq_zero (x y : Abelian k V) : ⁅x, y⁆ = 0 := rfl

instance : LieRing (Abelian k V) where
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance : LieAlgebra k (Abelian k V) where
  lie_smul _ _ _ := by simp

/-- The abelian Lie algebra is abelian: its bracket vanishes identically. -/
instance : IsLieAbelian (Abelian k V) := ⟨fun x y => bracket_eq_zero x y⟩

end Abelian

/-! ## (2) Any associative algebra, with `End(V) = 𝔤𝔩(V)` as the key example -/

-- `LieRing.ofAssociativeRing` is only a *local* instance from v4.31 onward (to
-- avoid a bracket diamond when a ring acts on itself), so re-enable it locally.
-- On v4.28.1 it is already a global instance and this attribute is harmless.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Any associative algebra has a Lie algebra structure via `[a, b] = ab - ba`.
(Etingof Example 2.9.2(2)) -/
example (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :
    LieRing A := inferInstance

/-- `End(V) = 𝔤𝔩(V)` is a Lie algebra. (Etingof Example 2.9.2(2)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] :
    LieAlgebra k (Module.End k V) := inferInstance

/-! ## (3) Any subspace of an associative algebra closed under the bracket -/

/-- Any `k`-subspace `U` of an associative algebra `A` that is closed under the commutator bracket
`[a, b] = ab - ba` is itself a Lie algebra — a *Lie subalgebra* of `A` regarded as a Lie algebra.
(Etingof Example 2.9.2(3)) -/
example (k A : Type*) [CommRing k] [Ring A] [Algebra k A] (U : LieSubalgebra k A) :
    LieAlgebra k U := inferInstance

/-! ## (4) The space `Der(A)` of derivations of an algebra `A` -/

/-- The space `Der(A)` of derivations of a (commutative) `k`-algebra `A` is a Lie algebra.
(Etingof Example 2.9.2(4)) -/
example (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] :
    LieAlgebra k (Derivation k A A) := inferInstance

/-- Membership in `Der(A)` is governed by the book's Leibniz rule `D(ab) = D(a) b + a D(b)`.
(Etingof Example 2.9.2(4)) -/
example (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (a b : A) : D (a * b) = D a * b + a * D b := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (D a), add_comm]

/-- The Lie bracket on `Der(A)` is the commutator `[D₁, D₂] = D₁ ∘ D₂ − D₂ ∘ D₁`.
(Etingof Example 2.9.2(4)) -/
example (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (D₁ D₂ : Derivation k A A) (a : A) : ⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a) :=
  Derivation.commutator_apply a

end Etingof.Example2_9_2
