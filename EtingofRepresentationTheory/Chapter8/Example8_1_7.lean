import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Finsupp.LSum
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

The **forward direction** `P` projective ⟹ `P*` injective is now available sorry-free as
`Etingof.Example817.projective_dual_injective`, for *any* `k`-algebra `A` (no finite
dimensionality needed). Its crux is the **injective cogenerator**
`Etingof.Example817.dual_regular_injective`: for any `k`-algebra `A`, the contragredient right
module `A* = Module.Dual k A` is injective (the `P = A` case), proved directly via Baer's
criterion plus extension of `k`-functionals, with no tensor product. The general case passes
from `A*` to `P*` by writing `P` as a retract of a free module `P →₀ A`, dualising
contravariantly (`contragredientMap`), identifying `(P →₀ A)* ≃ ∀ p, A*` (`freeDualEquiv`), and
combining "a product of injectives is injective" (`Module.Injective.pi`) with a retract argument
carried out at the level of Baer's criterion (so it survives the universe gap between `P*` and
`(P →₀ A)*`).

The remaining gap to the full biconditional is:
* the converse `P*` injective ⟹ `P` projective, which over a finite dimensional algebra uses
  that such algebras are left perfect and that over a left perfect ring flat ⟹ projective (Bass).

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

/-! ## Forward direction: `P` projective ⟹ `P*` injective

We build the contravariant dual functor on morphisms, identify the dual of a free module
with a product of copies of `A*`, and combine "product of injectives is injective" with a
universe-robust retract argument at the level of Baer's criterion. -/

/-- Transfer of injectivity along a split injection (retract): if `r ∘ i = id` with `M`
injective, then `N` is injective. Proved directly from the universal lifting property, so it
is free of `Small` hypotheses (but requires `M` and `N` in the same universe). -/
theorem injective_of_leftInverse {R : Type*} [Ring R] {M N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r ∘ₗ i = LinearMap.id)
    (hM : Module.Injective R M) : Module.Injective R N :=
  ⟨fun X Y _ _ _ _ f hf g => by
    obtain ⟨t, ht⟩ := hM.out f hf (i ∘ₗ g)
    exact ⟨r ∘ₗ t, fun x => by
      have h1 : t (f x) = i (g x) := ht x
      change r (t (f x)) = g x
      rw [h1]; exact LinearMap.congr_fun h (g x)⟩⟩

section Functor

variable {M N : Type*}
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The **contragredient (dual) functor on morphisms**: an `A`-linear map `f : M →ₗ[A] N`
induces, by `k`-linear precomposition, an `Aᵐᵒᵖ`-linear map `N* →ₗ[Aᵐᵒᵖ] M*` between the
contragredient duals. This is the action of the contravariant functor `Hom_k(-, k)` on arrows. -/
def contragredientMap (f : M →ₗ[A] N) : Module.Dual k N →ₗ[Aᵐᵒᵖ] Module.Dual k M where
  toFun φ := φ ∘ₗ f.restrictScalars k
  map_add' φ ψ := by ext m; rfl
  map_smul' a φ := by
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      contragredient_smul_apply, RingHom.id_apply]
    rw [f.map_smul]

@[simp]
theorem contragredientMap_apply (f : M →ₗ[A] N) (φ : Module.Dual k N) (m : M) :
    contragredientMap k A f φ m = φ (f m) :=
  rfl

end Functor

/-- The dual of the free module `P →₀ A` is, as a contragredient right `A`-module, the product
`∀ p : P, A*` of copies of the dual of the regular module. The underlying `k`-linear bijection is
`Finsupp.lsum`; the content here is that it intertwines the contragredient `Aᵐᵒᵖ`-actions. -/
noncomputable def freeDualEquiv :
    Module.Dual k (P →₀ A) ≃ₗ[Aᵐᵒᵖ] (P → Module.Dual k A) where
  toFun φ := fun p => φ ∘ₗ Finsupp.lsingle (R := k) p
  map_add' φ ψ := by ext p a; rfl
  map_smul' a φ := by
    ext p b
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      contragredient_smul_apply, Pi.smul_apply, RingHom.id_apply, Finsupp.smul_single]
  invFun g := Finsupp.lsum (R := k) k g
  left_inv φ := by
    have hsymm : (fun p => φ ∘ₗ Finsupp.lsingle (R := k) p) = (Finsupp.lsum (R := k) k).symm φ := by
      funext p; exact (Finsupp.lsum_symm_apply (S := k) φ p).symm
    change Finsupp.lsum (R := k) k (fun p => φ ∘ₗ Finsupp.lsingle (R := k) p) = φ
    rw [hsymm, LinearEquiv.apply_symm_apply]
  right_inv g := by
    funext p
    exact Finsupp.lsum_comp_lsingle (S := k) g p

/-- **Forward direction of Example 8.1.7.** Over any `k`-algebra `A`, if a left `A`-module `P`
is projective then its contragredient dual `P* = Module.Dual k P` is injective as a right
`A`-module (modelled over `Aᵐᵒᵖ`).

`P` is a retract of the free module `P →₀ A`; dualising contravariantly makes `P*` a retract of
`(P →₀ A)* ≃ ∀ p, A*`, a product of injectives (`dual_regular_injective`). The retract step is
performed at the level of Baer's criterion so that it is robust under the universe gap between
`P*` and `(P →₀ A)*`. No `[FiniteDimensional k A]` is needed. -/
theorem projective_dual_injective.{uk, uA, uP}
    {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
    {P : Type uP} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Projective A P] :
    Module.Injective Aᵐᵒᵖ (Module.Dual k P) := by
  -- `P` is a retract of the free module `F = P →₀ A`.
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := A) (P := P)).mp ‹_›
  set π : (P →₀ A) →ₗ[A] P := Finsupp.linearCombination A id with hπ
  -- `F*` is injective: it is the product `∀ p, A*` of injectives.
  haveI sA : Small.{max uA uk} Aᵐᵒᵖ := small_max.{uk, uA} Aᵐᵒᵖ
  have hpi : Module.Injective Aᵐᵒᵖ (P → Module.Dual k A) :=
    @Module.Injective.pi Aᵐᵒᵖ _ P (fun _ : P => Module.Dual k A) sA _ _
      (fun _ => dual_regular_injective k A)
  have hF : Module.Injective Aᵐᵒᵖ (Module.Dual k (P →₀ A)) :=
    injective_of_leftInverse (freeDualEquiv k A P).toLinearMap
      (freeDualEquiv k A P).symm.toLinearMap (by ext x; simp) hpi
  -- Retract `P* ◁ F*` at the level of Baer's criterion (universe-robust).
  haveI sB : Small.{max uP uA uk} Aᵐᵒᵖ := small_max.{max uP uk, uA} Aᵐᵒᵖ
  have hBF : Module.Baer Aᵐᵒᵖ (Module.Dual k (P →₀ A)) := Module.Baer.of_injective hF
  have hid : ∀ ψ : Module.Dual k P,
      contragredientMap k A s (contragredientMap k A π ψ) = ψ := by
    intro ψ; ext m
    simp only [contragredientMap_apply]
    rw [show π (s m) = m from LinearMap.congr_fun hs m]
  apply Module.Baer.injective
  intro I g
  obtain ⟨g', hg'⟩ := hBF I ((contragredientMap k A π) ∘ₗ g)
  refine ⟨(contragredientMap k A s) ∘ₗ g', fun x hx => ?_⟩
  rw [LinearMap.comp_apply, hg' x hx, LinearMap.comp_apply, hid]

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
  refine ⟨fun hP => ?_, fun hInj => ?_⟩
  · -- Forward direction: holds for any algebra (no finite-dimensionality needed).
    haveI := hP
    exact Etingof.Example817.projective_dual_injective
  · -- Converse (`P*` injective ⟹ `P` projective): the Bass direction. Over a finite
    -- dimensional — a fortiori left perfect — algebra every flat module is projective, and
    -- `P*` injective forces `P` flat (Lambek). This direction is the genuine remaining gap;
    -- see issue #5476 and the module docstring.
    sorry
