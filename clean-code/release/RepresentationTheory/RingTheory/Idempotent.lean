/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Idempotent-Associated Submodules

This module constructs the submodule associated with multiplication on both sides by a fixed
algebra element, equips its subtype with ring and algebra structures when that element is
idempotent, and identifies its opposite ring with endomorphisms of the corresponding principal
submodule.
-/

universe u

variable {k : Type u} [Field k]
variable {A : Type u} [Ring A] [Algebra k A]

namespace RepresentationTheory.RingTheory.Idempotent

/-- The linear map that multiplies an algebra element on both sides by a fixed element. -/
noncomputable def sandwichLinearMap (e : A) : A →ₗ[k] A where
  toFun a := e * a * e
  map_add' a b := by simp [mul_add, add_mul]
  map_smul' c a := by simp [Algebra.smul_mul_assoc]

/-- Evaluating the sandwich linear map sends an element to the corresponding double product. -/
@[simp]
lemma sandwichLinearMap_apply (e a : A) : sandwichLinearMap (k := k) e a = e * a * e := rfl

/-- The submodule associated to products with a fixed element on both sides. -/
noncomputable def sandwichSubmodule (e : A) : Submodule k A :=
  LinearMap.range (sandwichLinearMap (k := k) e)

/-- Membership in the sandwich submodule is equivalent to being a double product with the fixed
element. -/
lemma mem_sandwichSubmodule_iff (e a : A) :
    a ∈ sandwichSubmodule (k := k) e ↔ ∃ b : A, e * b * e = a :=
  LinearMap.mem_range

/-- An idempotent acts as a left identity on elements of the sandwich submodule. -/
lemma left_mul_eq_of_mem_sandwichSubmodule {e : A} (he : IsIdempotentElem e) {x : A}
    (hx : x ∈ sandwichSubmodule (k := k) e) : e * x = x := by
  obtain ⟨a, rfl⟩ := (mem_sandwichSubmodule_iff e x).mp hx
  rw [← mul_assoc, ← mul_assoc, he.eq]

/-- An idempotent acts as a right identity on elements of the sandwich submodule. -/
lemma right_mul_eq_of_mem_sandwichSubmodule {e : A} (he : IsIdempotentElem e) {x : A}
    (hx : x ∈ sandwichSubmodule (k := k) e) : x * e = x := by
  obtain ⟨a, rfl⟩ := (mem_sandwichSubmodule_iff e x).mp hx
  rw [mul_assoc, he.eq]

/-- The product of two elements of the sandwich submodule belongs to it. -/
lemma mul_mem_sandwichSubmodule {e : A} {x y : A}
    (hx : x ∈ sandwichSubmodule (k := k) e) (hy : y ∈ sandwichSubmodule (k := k) e) :
    x * y ∈ sandwichSubmodule (k := k) e := by
  obtain ⟨a, rfl⟩ := (mem_sandwichSubmodule_iff e x).mp hx
  obtain ⟨b, rfl⟩ := (mem_sandwichSubmodule_iff e y).mp hy
  rw [mem_sandwichSubmodule_iff]
  refine ⟨a * e * e * b, ?_⟩
  simp only [mul_assoc]

/-- An idempotent belongs to its sandwich submodule. -/
lemma idempotent_mem_sandwichSubmodule (e : A) (he : IsIdempotentElem e) :
    e ∈ sandwichSubmodule (k := k) e := by
  rw [mem_sandwichSubmodule_iff]
  exact ⟨1, by rw [mul_one, he.eq]⟩

/-- The finite dimension of the sandwich submodule is bounded by that of the ambient algebra. -/
theorem sandwichSubmodule_finrank_le (e : A) [Module.Finite k A] :
    Module.finrank k (sandwichSubmodule (k := k) e) ≤ Module.finrank k A :=
  Submodule.finrank_le _

/-- The sandwich submodule is finite over the base field when the ambient algebra is finite. -/
noncomputable instance sandwichSubmodule_moduleFinite (e : A) [Module.Finite k A] :
    Module.Finite k (sandwichSubmodule (k := k) e) :=
  Module.Finite.of_injective (Submodule.subtype _) (Submodule.subtype_injective _)

/-! ### Ring structure on the corner ring

The corner ring `eAe` has a ring structure with:
- Multiplication: inherited from `A` (product of elements in `eAe` stays in `eAe`)
- Unit: `e` (not `1` of `A`)
- Addition: inherited from `A`

We define `submodule` as a type alias to hold the Ring and Algebra instances,
since the standard unit of `↥(sandwichSubmodule e)` (inherited from the submodule)
is `0`, not `e`. -/

/-- The submodule associated to an element of an algebra. -/
noncomputable def submodule (e : A) := sandwichSubmodule (k := k) e

namespace submodule

variable {e : A} (he : IsIdempotentElem e)

-- The Ring instance on eAe. The multiplication is inherited from A
-- (which is well-defined by mul_mem_sandwichSubmodule), and the unit is e
-- (which is in eAe by idempotent_mem_sandwichSubmodule).
-- The ring axioms (associativity, distributivity) follow from A's ring axioms.
-- The only non-trivial part is that e acts as an identity: e * x = x = x * e
-- for x ∈ eAe, which is left_mul_eq_of_mem_sandwichSubmodule and
-- right_mul_eq_of_mem_sandwichSubmodule.
--
-- This is a `def`, not an `instance`: it depends on the idempotency proof `he`,
-- which is not instance-implicit and cannot be synthesised. (Lean v4.31 rejects
-- such an `instance` outright; under v4.28.1 it was a latent lint warning.) All
-- consumers already pass `he` explicitly via `letI := submodule.ring he`.
-- `@[reducible]` silences v4.31's "class-typed def must be reducible" warning and
-- is a no-op on v4.28.1.
/-- The ring structure on the associated subtype induced by an idempotent element. -/
@[reducible] noncomputable def ring : Ring (submodule (k := k) e) :=
  { (inferInstance : AddCommGroup (submodule (k := k) e)) with
    mul := fun x y => ⟨(x : A) * (y : A), mul_mem_sandwichSubmodule x.prop y.prop⟩
    one := ⟨e, idempotent_mem_sandwichSubmodule e he⟩
    mul_assoc := fun a b c => Subtype.ext (mul_assoc _ _ _)
    one_mul := fun a => Subtype.ext (left_mul_eq_of_mem_sandwichSubmodule he a.prop)
    mul_one := fun a => Subtype.ext (right_mul_eq_of_mem_sandwichSubmodule he a.prop)
    left_distrib := fun a b c => Subtype.ext (left_distrib _ _ _)
    right_distrib := fun a b c => Subtype.ext (right_distrib _ _ _)
    zero_mul := fun a => Subtype.ext (zero_mul _)
    mul_zero := fun a => Subtype.ext (mul_zero _) }

-- The Algebra instance on eAe over k.
-- The algebra map sends r : k to (algebraMap k A r) • e, which is in eAe
-- since e * ((algebraMap k A r) • e) * e = (algebraMap k A r) • (e * e * e)
--                                        = (algebraMap k A r) • e  (using he.eq).
-- Commutativity of the algebra map with multiplication follows from
-- r • (eae) = e(ra)e = (eae) • r for elements of eAe.
-- A `def` for the same reason as `ring`: it depends on the explicit `he`.
/-- The algebra structure on the associated subtype obtained from an idempotent element. -/
@[reducible] noncomputable def algebra :
    @Algebra k (submodule (k := k) e) _ (ring he).toSemiring :=
  -- The `k`-module on `submodule e` is the one inherited from `sandwichSubmodule e`,
  -- passed positionally: v4.31 instance synthesis no longer unfolds the
  -- semireducible `submodule` wrapper to discover it (v4.28.1 did).
  @Algebra.ofModule k (submodule (k := k) e) _ (ring he).toSemiring
    (inferInstanceAs (Module k (sandwichSubmodule (k := k) e)))
    (fun r x y => Subtype.ext (Algebra.smul_mul_assoc r (x : A) (y : A)))
    (fun r x y => Subtype.ext (Algebra.mul_smul_comm r (x : A) (y : A)))

/-- The subtype of the associated submodule is finite as a module when the ambient algebra is
finite. -/
noncomputable instance moduleFinite [Module.Finite k A] :
    Module.Finite k (submodule (k := k) e) :=
  sandwichSubmodule_moduleFinite e

/-- The finite dimension of the associated submodule is at most that of the ambient algebra. -/
theorem finrank_le [Module.Finite k A] :
    Module.finrank k (submodule (k := k) e) ≤ Module.finrank k A :=
  sandwichSubmodule_finrank_le e

end submodule

/-! ### Endomorphism algebra of left ideal Ae ≅ (eAe)ᵒᵖ

For an idempotent `e` in a `k`-algebra `A`, the `A`-module endomorphism ring of the
left ideal `Ae = Submodule.span A {e}` is anti-isomorphic to the corner ring `eAe`.
The isomorphism sends `φ ↦ φ(e)` and the inverse sends `c ∈ eAe` to right
multiplication by `c`. -/

section EndLeftIdeal

variable {e : A} (he : IsIdempotentElem e)
include he

/-- Right multiplication by an idempotent fixes every element of its principal span. -/
lemma mul_idempotent_eq_of_mem_span_singleton {x : A}
    (hx : x ∈ Submodule.span A ({e} : Set A)) : x * e = x := by
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [smul_eq_mul, mul_assoc, he.eq]

/-- Applying an endomorphism of the principal submodule to the idempotent gives an element of the
sandwich submodule. -/
lemma apply_idempotent_mem_sandwichSubmodule
    (φ : Module.End A ↥(Submodule.span A ({e} : Set A))) :
    (φ ⟨e, Submodule.subset_span rfl⟩).val ∈ sandwichSubmodule (k := k) e := by
  -- φ(e) ∈ Ae, so φ(e) = b * e for some b
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (φ ⟨e, Submodule.subset_span rfl⟩).prop
  rw [smul_eq_mul] at hb
  -- e * φ(e) = φ(e) by A-linearity and e² = e
  have he_mem : (⟨e, Submodule.subset_span rfl⟩ : ↥(Submodule.span A ({e} : Set A))) =
      e • ⟨e, Submodule.subset_span rfl⟩ := by
    ext
    change e = e * e
    exact he.eq.symm
  have key : φ ⟨e, Submodule.subset_span rfl⟩ =
      e • φ ⟨e, Submodule.subset_span rfl⟩ := by
    conv_lhs => rw [he_mem]
    exact φ.map_smul e ⟨e, Submodule.subset_span rfl⟩
  rw [mem_sandwichSubmodule_iff]
  refine ⟨b, ?_⟩
  have := congr_arg Subtype.val key
  simp only [SetLike.val_smul, smul_eq_mul] at this
  -- this : (φ ⟨e, _⟩).val = e * (φ ⟨e, _⟩).val
  -- goal : e * b * e = (φ ⟨e, _⟩).val
  rw [mul_assoc, hb, ← this]

/-- Right multiplication by `c ∈ eAe` sends `Ae` to `Ae`. -/
private lemma rightMul_mem_leftIdeal {c : A} (hc : c ∈ sandwichSubmodule (k := k) e) (x : A) :
    x * c ∈ Submodule.span A ({e} : Set A) := by
  rw [Submodule.mem_span_singleton]
  exact ⟨x * c, by rw [smul_eq_mul, mul_assoc, right_mul_eq_of_mem_sandwichSubmodule he hc]⟩

/-- A construction sending an element of the associated subtype to an endomorphism of the
principal submodule. -/
noncomputable def submoduleElementToEnd (c : submodule (k := k) e) :
    Module.End A ↥(Submodule.span A ({e} : Set A)) where
  toFun x := ⟨x.val * c.val, rightMul_mem_leftIdeal he c.prop x.val⟩
  map_add' x y := by
    ext
    change ((x : A) + (y : A)) * (c : A) = (x : A) * (c : A) + (y : A) * (c : A)
    rw [add_mul]
  map_smul' a x := by
    ext
    change (a * (x : A)) * (c : A) = a * ((x : A) * (c : A))
    rw [mul_assoc]

/-- The ring equivalence from endomorphisms of the principal submodule to the opposite associated
subtype. -/
noncomputable def moduleEndRingEquivOpposite :
    letI := submodule.ring (k := k) he
    Module.End A ↥(Submodule.span A ({e} : Set A)) ≃+*
      (submodule (k := k) e)ᵐᵒᵖ := by
  letI := submodule.ring (k := k) he
  exact {
    toFun := fun φ => MulOpposite.op
      ⟨(φ ⟨e, Submodule.subset_span rfl⟩).val,
        apply_idempotent_mem_sandwichSubmodule he φ⟩
    invFun := fun c => submoduleElementToEnd he c.unop
    left_inv := by
      intro φ
      ext ⟨x, hx⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      rw [smul_eq_mul] at ha; subst ha
      -- Goal: (a * e) * φ(e).val = φ(⟨a * e, _⟩).val
      simp only [submoduleElementToEnd, MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_assoc, left_mul_eq_of_mem_sandwichSubmodule (k := k) he
        (apply_idempotent_mem_sandwichSubmodule he φ)]
      exact (congr_arg Subtype.val (φ.map_smul a ⟨e, Submodule.subset_span rfl⟩)).symm
    right_inv := by
      intro c_op
      simp only []
      congr 1
      ext
      -- Goal: (submoduleElementToEnd he c_op.unop)(⟨e, _⟩).val = c_op.unop.val
      simp only [submoduleElementToEnd]
      -- Goal: e * c_op.unop.val = c_op.unop.val
      exact left_mul_eq_of_mem_sandwichSubmodule he c_op.unop.prop
    map_mul' := by
      intro φ ψ
      -- Goal: Θ(φ * ψ) = Θ(φ) * Θ(ψ) in (eAe)^op
      -- i.e., op((φ ∘ ψ)(e)) = op(φ(e)) * op(ψ(e)) = op(ψ(e) * φ(e))
      apply MulOpposite.unop_injective
      ext
      -- Goal: (φ(ψ(e))).val = ψ(e).val * φ(e).val  (in submodule mul)
      -- Use: ψ(e) = b • e for some b (since ψ(e) ∈ Ae)
      -- Then φ(ψ(e)) = φ(b • e) = b • φ(e), so (φ(ψ(e))).val = b * φ(e).val
      -- And ψ(e).val * φ(e).val = (b * e) * φ(e).val = b * (e * φ(e).val) = b * φ(e).val ✓
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
        (ψ ⟨e, Submodule.subset_span rfl⟩).prop
      rw [smul_eq_mul] at hb
      -- hb : b * e = ψ(e).val
      change (φ (ψ ⟨e, Submodule.subset_span rfl⟩)).val =
        (ψ ⟨e, Submodule.subset_span rfl⟩).val * (φ ⟨e, Submodule.subset_span rfl⟩).val
      -- LHS: φ(⟨b * e, _⟩) = φ(b • ⟨e, _⟩) = b • φ(⟨e, _⟩)
      -- = ⟨b * φ(e).val, _⟩
      have hlhs : (φ (ψ ⟨e, Submodule.subset_span rfl⟩)).val =
          b * (φ ⟨e, Submodule.subset_span rfl⟩).val := by
        have h1 : ψ ⟨e, Submodule.subset_span rfl⟩ =
            b • ⟨e, Submodule.subset_span rfl⟩ := by
          ext
          change (ψ ⟨e, Submodule.subset_span rfl⟩).val = b * e
          exact hb.symm
        rw [h1, map_smul]
        change b * (φ ⟨e, Submodule.subset_span rfl⟩).val =
          b * (φ ⟨e, Submodule.subset_span rfl⟩).val
        rfl
      -- RHS: (b * e) * φ(e).val = b * (e * φ(e).val) = b * φ(e).val
      have hrhs : (ψ ⟨e, Submodule.subset_span rfl⟩).val *
          (φ ⟨e, Submodule.subset_span rfl⟩).val =
          b * (φ ⟨e, Submodule.subset_span rfl⟩).val := by
        rw [← hb, mul_assoc]
        congr 1
        exact left_mul_eq_of_mem_sandwichSubmodule (k := k) he
          (apply_idempotent_mem_sandwichSubmodule he φ)
      rw [hlhs, hrhs]
    map_add' := by
      intro φ ψ
      simp only [LinearMap.add_apply]
      rfl
  }

end EndLeftIdeal

end RepresentationTheory.RingTheory.Idempotent
