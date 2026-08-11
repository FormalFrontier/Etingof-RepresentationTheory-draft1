import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.NoncommRing

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
- (4) is built here as `Etingof.Example2_9_2.Der k A`, for an **arbitrary associative**
  `k`-algebra `A`, as a `LieSubalgebra k (Module.End k A)`. Mathlib's `Derivation k A A`
  requires `[CommSemiring A]`, so it cannot state the book's example at its stated
  generality; `derivationLieEquiv` identifies the two in the commutative case.
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
@[reducible] def associativeLieRing (k : Type*) [CommRing k]
    (A : Type*) [Ring A] [Algebra k A] :
    LieRing A := inferInstance

/-- `End(V) = 𝔤𝔩(V)` is a Lie algebra. (Etingof Example 2.9.2(2)) -/
@[reducible] def endomorphismLieAlgebra (k : Type*) [CommRing k] (V : Type*)
    [AddCommGroup V] [Module k V] :
    LieAlgebra k (Module.End k V) := inferInstance

/-! ## (3) Any subspace of an associative algebra closed under the bracket -/

/-- Any `k`-subspace `U` of an associative algebra `A` that is closed under the commutator bracket
`[a, b] = ab - ba` is itself a Lie algebra: a Lie subalgebra of `A` regarded as a Lie algebra.
(Etingof Example 2.9.2(3)) -/
@[reducible] def lieSubalgebraLieAlgebra (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
    (U : LieSubalgebra k A) :
    LieAlgebra k U := inferInstance

/-! ## (4) The space `Der(A)` of derivations of an algebra `A`

The book's `A` here is an arbitrary (associative, not necessarily commutative) algebra, so
Mathlib's `Derivation k A A` — which requires `[CommSemiring A]` — is too narrow to state
the example at the book's generality. We therefore build `Der k A` directly, for any
associative `k`-algebra `A`, as the set of `k`-linear endomorphisms satisfying the Leibniz
rule, and exhibit it as a Lie subalgebra of `𝔤𝔩(A) = End_k(A)` from part (2). The
commutative case is bridged back to Mathlib's `Derivation` at the end of the section. -/

section Der

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

/-- The book's Leibniz rule `D(ab) = D(a) b + a D(b)` for a `k`-linear endomorphism of an
associative `k`-algebra `A`. (Etingof Example 2.9.2(4)) -/
def IsLeibniz (D : Module.End k A) : Prop := ∀ a b : A, D (a * b) = D a * b + a * D b

/-- The space `Der(A)` of derivations of an arbitrary associative `k`-algebra `A`: the
`k`-linear maps `D : A → A` satisfying the Leibniz rule `D(ab) = D(a) b + a D(b)`, packaged
as a Lie subalgebra of `𝔤𝔩(A) = End_k(A)`. In particular `Der(A)` is closed under the
commutator bracket, which is the content of Example 2.9.2(4).

Note that no commutativity of `A` is assumed; Mathlib's `Derivation k A A` covers only the
commutative case. (Etingof Example 2.9.2(4)) -/
def Der : LieSubalgebra k (Module.End k A) where
  carrier := {D | IsLeibniz k A D}
  add_mem' {D₁ D₂} h₁ h₂ a b := by
    simp only [LinearMap.add_apply, h₁ a b, h₂ a b, add_mul, mul_add]; abel
  zero_mem' a b := by simp
  smul_mem' c D h a b := by
    simp only [LinearMap.smul_apply, h a b, smul_add, smul_mul_assoc, mul_smul_comm]
  lie_mem' {D₁ D₂} h₁ h₂ a b := by
    change ⁅D₁, D₂⁆ (a * b) = ⁅D₁, D₂⁆ a * b + a * ⁅D₁, D₂⁆ b
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      h₁ a b, h₂ a b, map_add, h₁ (D₂ a) b, h₁ a (D₂ b), h₂ (D₁ a) b, h₂ a (D₁ b)]
    noncomm_ring

variable {k A}

/-- Membership in `Der(A)` is exactly the book's Leibniz rule. (Etingof Example 2.9.2(4)) -/
@[simp] theorem mem_Der {D : Module.End k A} :
    D ∈ Der k A ↔ ∀ a b : A, D (a * b) = D a * b + a * D b := Iff.rfl

/-- The defining Leibniz rule, in usable form. (Etingof Example 2.9.2(4)) -/
theorem Der.leibniz (D : Der k A) (a b : A) :
    (D : Module.End k A) (a * b) = (D : Module.End k A) a * b + a * (D : Module.End k A) b :=
  D.2 a b

/-- The Lie bracket on `Der(A)` is the commutator `[D₁, D₂] = D₁ ∘ D₂ − D₂ ∘ D₁`.
(Etingof Example 2.9.2(4)) -/
theorem Der.bracket_apply (D₁ D₂ : Der k A) (a : A) :
    ((⁅D₁, D₂⁆ : Der k A) : Module.End k A) a =
      (D₁ : Module.End k A) ((D₂ : Module.End k A) a) -
        (D₂ : Module.End k A) ((D₁ : Module.End k A) a) := by
  simp [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]

/-- The **inner derivation** `ad x = [x, ·] = x · (−) − (−) · x` of an arbitrary associative
`k`-algebra `A`. It witnesses that `Der(A)` is not degenerate. -/
def Der.inner (x : A) : Der k A :=
  ⟨LinearMap.mulLeft k x - LinearMap.mulRight k x, fun a b => by
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      sub_mul, mul_sub, mul_assoc]
    noncomm_ring⟩

@[simp] theorem Der.inner_apply (x a : A) :
    ((Der.inner x : Der k A) : Module.End k A) a = x * a - a * x := rfl

variable (k A)

/-- **Example 2.9.2(4)**: for an arbitrary associative `k`-algebra `A`, the space `Der(A)` of
derivations is a Lie algebra over `k`. -/
example : LieAlgebra k (Der k A) := inferInstance

/-- `Der(A)` is a Lie ring under the commutator. -/
example : LieRing (Der k A) := inferInstance

end Der

/-! ### Agreement with Mathlib's `Derivation` in the commutative case -/

section CommBridge

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- A Mathlib `Derivation k A A` of a commutative algebra satisfies the book's Leibniz rule. -/
theorem isLeibniz_of_derivation (D : Derivation k A A) :
    IsLeibniz k A (D : A →ₗ[k] A) := fun a b => by
  rw [Derivation.coeFn_coe, D.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (D a), add_comm]

/-- For a commutative `k`-algebra `A`, the book's `Der(A)` is isomorphic, as a Lie algebra over
`k`, to Mathlib's `Derivation k A A`. This checks that the noncommutative-generality definition
above specializes to the expected object. -/
def derivationLieEquiv : Derivation k A A ≃ₗ⁅k⁆ Der k A where
  toFun D := ⟨(D : A →ₗ[k] A), isLeibniz_of_derivation k A D⟩
  invFun D := Derivation.mk' (D : Module.End k A) fun a b => by
    rw [Der.leibniz D a b, smul_eq_mul, smul_eq_mul, mul_comm b, add_comm]
  left_inv D := by ext a; rfl
  right_inv D := by ext a; rfl
  map_add' D₁ D₂ := rfl
  map_smul' c D := rfl
  map_lie' {D₁ D₂} := by
    ext a
    rw [Der.bracket_apply]
    exact Derivation.commutator_apply a

end CommBridge

end Etingof.Example2_9_2
