import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Example 8.1.7: Duality between projective and injective modules

Let `A` be an algebra and `P` be a left `A`-module. Then `P` is projective if and only if
`P*` is an injective right `A`-module.

## Formalization

The dual space `P* = Hom_k(P, k) = Module.Dual k P` carries the **contragredient** right
`A`-module structure: for `φ : P*` and `a : A`,
`(φ ⬝ a)(p) = φ(a • p)`.
We model a right `A`-module as a left `Aᵐᵒᵖ`-module, so this is the
`Module Aᵐᵒᵖ (Module.Dual k P)` instance `Etingof.Example817.contragredient` below, with
defining equation `Etingof.Example817.contragredient_smul_apply`.

The statement asserts the genuine biconditional over a general algebra `A` (not merely a
field, where every module is trivially injective). The single standing hypothesis
`[FiniteDimensional k A]` is the book's running convention that algebras are
finite dimensional, and it is *mathematically necessary*, not decorative:

* The contragredient duality `Hom_k(-, k)` is an exact contravariant functor (as `k` is a
  field), so by Lambek's theorem `P*` is injective as a right `A`-module **iff `P` is flat**
  as a left `A`-module — for an arbitrary algebra `A` and arbitrary `P`.
* A finite dimensional algebra is left (and right) perfect, and over a left perfect ring
  *every* flat left module is projective (Bass). Hence `P` projective ⟺ `P` flat ⟺ `P*`
  injective, for every left `A`-module `P`.
* Without `[FiniteDimensional k A]` the equivalence is false: it degrades to
  "`P*` injective ⟺ `P` flat", and flat does not imply projective in general.

## Proof status

The biconditional is still a `sorry`, but the **injective cogenerator** at its heart is now
available sorry-free as `Etingof.Example817.dual_regular_injective`: for any `k`-algebra `A`,
the contragredient right module `A* = Module.Dual k A` is injective. This is the `P = A` case
of the forward implication and the genuine mathematical crux; it is proved directly via Baer's
criterion plus extension of `k`-functionals, with no tensor product.

The remaining gap to the full biconditional needs:
* the forward direction for general `P` (pass from `A*` to `P*` via direct summands of free
  modules: `Module.Injective.pi` for products of duals of free modules, plus a retract lemma);
* the converse, which over a finite dimensional algebra uses that such algebras are left perfect
  and that over a left perfect ring flat ⟹ projective (Bass).

Note that the originally planned route through "`P` flat ⟺ `P*` injective" (Lambek for the
`k`-linear dual) cannot be stated as written: `Module.Flat A P` requires `A` commutative
(`Module.Flat` is declared over a `CommSemiring`), whereas here `A` is an arbitrary algebra,
and the balanced tensor product `X ⊗_A P` over a noncommutative `A` is absent from Mathlib.
The cogenerator route above sidesteps both obstructions.
-/

namespace Etingof.Example817

open MulOpposite

variable (k : Type*) [Field k]
variable (A : Type*) [Ring A] [Algebra k A]
variable (P : Type*) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

/-- The **contragredient** right `A`-action on the dual space `P* = Module.Dual k P`,
modelled as a left `Aᵐᵒᵖ`-module: `(a • φ)(p) = φ(unop a • p)`.

This is the genuine right `A`-module structure of Example 8.1.7, not merely the underlying
`k`-vector space: see `contragredient_smul_apply` for the defining equation. -/
noncomputable instance contragredient : Module Aᵐᵒᵖ (Module.Dual k P) where
  smul a φ := φ ∘ₗ Algebra.lsmul k k P a.unop
  one_smul φ := by
    ext p
    change φ ((1 : Aᵐᵒᵖ).unop • p) = φ p
    rw [MulOpposite.unop_one, one_smul]
  mul_smul a b φ := by
    ext p
    change φ ((a * b).unop • p) = φ (b.unop • a.unop • p)
    rw [MulOpposite.unop_mul, mul_smul]
  smul_zero a := by ext p; rfl
  zero_smul φ := by
    ext p
    change φ ((0 : Aᵐᵒᵖ).unop • p) = (0 : Module.Dual k P) p
    rw [MulOpposite.unop_zero, zero_smul, map_zero, LinearMap.zero_apply]
  smul_add a φ ψ := by ext p; rfl
  add_smul a b φ := by
    ext p
    change φ ((a + b).unop • p) = φ (a.unop • p) + φ (b.unop • p)
    rw [MulOpposite.unop_add, add_smul, map_add]

/-- Defining equation of the contragredient action: `(a • φ)(p) = φ(unop a • p)`. -/
@[simp]
theorem contragredient_smul_apply (a : Aᵐᵒᵖ) (φ : Module.Dual k P) (p : P) :
    (a • φ) p = φ (a.unop • p) :=
  rfl

/-- The contragredient `Aᵐᵒᵖ`-action and the base `k`-action on `P*` form a scalar tower:
the `k`-vector space structure on `P*` is the one underlying the contragredient module. -/
instance contragredient_isScalarTower : IsScalarTower k Aᵐᵒᵖ (Module.Dual k P) where
  smul_assoc c a φ := by
    ext p
    change φ ((c • a).unop • p) = c • φ (a.unop • p)
    rw [unop_smul, smul_assoc, map_smul]

/-- **The dual of the regular module is injective.** For a `k`-algebra `A`, the contragredient
right `A`-module `A* = Module.Dual k A` is injective.

This is the injective cogenerator at the heart of Example 8.1.7: it is the special case `P = A`
of the forward implication "`P` projective ⟹ `P*` injective" (a free module is projective), and
the general statement is obtained from it by passing to direct summands of free modules.

The proof is Baer's criterion: a right-`A`-linear map `g` from a right ideal `I ⊆ A` into `A*`
is the same datum as the `k`-functional `x ↦ g(x)(1)` on `I`; since `k` is a field this functional
extends to all of `A` (`LinearMap.exists_extend`), and the extension `γ'` reconstitutes a
right-`A`-linear extension `g'(y)(a) = γ'(op a · y)` of `g`. No tensor product is needed. -/
theorem dual_regular_injective :
    Module.Injective Aᵐᵒᵖ (Module.Dual k A) := by
  apply Module.Baer.injective
  intro I g
  -- `eval1` : evaluation of a functional at `1`.
  let eval1 : Module.Dual k A →ₗ[k] k :=
    { toFun := fun φ => φ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  -- the `k`-linear inclusion of the ideal (viewed over `k`) into the ideal.
  let restr : (I.restrictScalars k) →ₗ[k] I :=
    { toFun := fun v => ⟨v.1, v.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  -- `γ` : the underlying `k`-functional on the ideal, `γ x = g x 1`.
  let γ : (I.restrictScalars k) →ₗ[k] k := eval1 ∘ₗ (g.restrictScalars k) ∘ₗ restr
  -- Extend `γ` to all of `Aᵐᵒᵖ` since `k` is a field.
  obtain ⟨γ', hγ'⟩ := γ.exists_extend
  -- `g'` : the extension, `g' y a = γ' (op a * y)`.
  refine ⟨{ toFun := fun y =>
              γ' ∘ₗ (LinearMap.mulRight k y) ∘ₗ (opLinearEquiv k (M := A)).toLinearMap
            map_add' := fun y z => by ext a; simp [mul_add]
            map_smul' := fun b y => by
              ext a
              simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
                LinearEquiv.coe_coe, coe_opLinearEquiv, contragredient_smul_apply,
                RingHom.id_apply, smul_eq_mul]
              rw [op_mul, op_unop, ← mul_assoc] }, ?_⟩
  intro x hx
  ext a
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulRight_apply, LinearEquiv.coe_coe, coe_opLinearEquiv]
  -- `op a * x ∈ I` because `I` is a right ideal of `A`, i.e. a left ideal of `Aᵐᵒᵖ`.
  have hmem : op a * x ∈ I := I.smul_mem (op a) hx
  have hext : γ' (op a * x) = g ⟨op a * x, hmem⟩ (1 : A) := by
    have h1 : γ' (op a * x) = γ ⟨op a * x, hmem⟩ :=
      LinearMap.congr_fun hγ' (⟨op a * x, hmem⟩ : I.restrictScalars k)
    rw [h1]; rfl
  rw [hext]
  have hsm : (⟨op a * x, hmem⟩ : I) = (op a) • (⟨x, hx⟩ : I) := by
    apply Subtype.ext; rfl
  rw [hsm, map_smul, contragredient_smul_apply]
  change g ⟨x, hx⟩ (a • (1 : A)) = g ⟨x, hx⟩ a
  rw [smul_eq_mul, mul_one]

end Etingof.Example817

/-- **Example 8.1.7.** Let `A` be an algebra and `P` be a left `A`-module. Then `P` is
projective if and only if its dual `P* = Module.Dual k P` is injective as a right `A`-module
(modelled as a left `Aᵐᵒᵖ`-module, with the contragredient action `(a • φ)(p) = φ(unop a • p)`
from `Etingof.Example817.contragredient`).

The hypothesis `[FiniteDimensional k A]` is the book's standing convention and is necessary:
without it the right-hand side characterizes flatness of `P` rather than projectivity. See the
module docstring for the mathematical content and the (deferred) proof strategy. -/
theorem Etingof.Example_8_1_7
    (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (P : Type*) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] :
    Module.Projective A P ↔ Module.Injective Aᵐᵒᵖ (Module.Dual k P) := by
  sorry
