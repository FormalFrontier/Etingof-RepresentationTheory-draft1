/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Complex.InvariantInnerProduct
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Group.ConjugateDuality

open scoped ComplexConjugate

universe u

variable {G : Type*} [Group G]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A type construction on complex vector spaces. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.6.2" (role := supporting)]
def conjugateModule (V : Type u) : Type u := V

namespace conjugateModule

/-- The additive commutative group structure on the displayed type construction. -/
instance instAddCommGroup : AddCommGroup (conjugateModule V) := inferInstanceAs (AddCommGroup V)

/-- The complex module structure on the displayed type construction. -/
noncomputable instance instModule : Module ℂ (conjugateModule V) := Module.compHom V (starRingEnd ℂ)

/-- The displayed scalar action has the stated underlying value. -/
lemma smul_apply (z : ℂ) (v : conjugateModule V) :
    z • v = (starRingEnd ℂ) z • (show V from v) := rfl

end conjugateModule

/-- The representation induced on the displayed conjugate module. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.6.2" (role := supporting)]
noncomputable def conjugateRepresentation (ρ : Representation ℂ G V) :
    Representation ℂ G (conjugateModule V) where
  toFun g :=
    { toFun := fun v => ρ g v
      map_add' := fun v w => map_add (ρ g) v w
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, conjugateModule.smul_apply, map_smul] }
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]; rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]; rfl

/-- The conjugate representation has the displayed action on elements. -/
@[simp] lemma conjugateRepresentation_apply (ρ : Representation ℂ G V) (g : G) (v : conjugateModule V) :
    conjugateRepresentation ρ g v = ρ g v := rfl

variable [FiniteDimensional ℂ V]

/-- An inner-product-space core identifies the conjugate of a finite-dimensional complex module with its linear dual. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.6.2" (role := supporting)]
noncomputable def conjugateLinearEquivDual (c : InnerProductSpace.Core ℂ V) :
    conjugateModule V ≃ₗ[ℂ] Module.Dual ℂ V :=
  { toFun := fun v => RepresentationTheory.Complex.InvariantInnerProduct.InnerProductSpace.Core.conjLinearEquivDual c v
    map_add' := fun v v' => (RepresentationTheory.Complex.InvariantInnerProduct.InnerProductSpace.Core.conjLinearEquivDual c).map_add v v'
    map_smul' := fun r v => by
      simp only [RingHom.id_apply]
      rw [conjugateModule.smul_apply, map_smulₛₗ]
      simp
    invFun := fun f => (RepresentationTheory.Complex.InvariantInnerProduct.InnerProductSpace.Core.conjLinearEquivDual c).symm f
    left_inv := fun v => (RepresentationTheory.Complex.InvariantInnerProduct.InnerProductSpace.Core.conjLinearEquivDual c).left_inv v
    right_inv := fun f => (RepresentationTheory.Complex.InvariantInnerProduct.InnerProductSpace.Core.conjLinearEquivDual c).right_inv f }

/-- Evaluating the conjugate-to-dual equivalence on two vectors gives their inner product. -/
@[simp] lemma conjugateLinearEquivDual_apply (c : InnerProductSpace.Core ℂ V) (v : conjugateModule V) (w : V) :
    conjugateLinearEquivDual c v w = c.inner v w := rfl

/-- For an inner-product-preserving representation, the conjugate-to-dual equivalence intertwines the conjugate and dual actions. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.6.2" (role := primary)]
theorem conjugateLinearEquivDual_intertwines (ρ : Representation ℂ G V)
    (c : InnerProductSpace.Core ℂ V)
    (hc : ∀ (g : G) (v w : V), c.inner (ρ g v) (ρ g w) = c.inner v w)
    (g : G) (v : conjugateModule V) :
    conjugateLinearEquivDual c (conjugateRepresentation ρ g v) = (Representation.dual ρ) g (conjugateLinearEquivDual c v) := by
  ext w
  change c.inner (ρ g v) w = c.inner v (ρ g⁻¹ w)
  have hw : ρ g (ρ g⁻¹ w) = w := by
    have h : ρ g (ρ g⁻¹ w) = ρ (g * g⁻¹) w := by rw [map_mul]; rfl
    rw [h, mul_inv_cancel, map_one]; rfl
  calc c.inner (ρ g v) w
      = c.inner (ρ g v) (ρ g (ρ g⁻¹ w)) := by rw [hw]
    _ = c.inner v (ρ g⁻¹ w) := hc g v (ρ g⁻¹ w)

set_option linter.unusedFintypeInType false in
/-- For a finite group representation, there is a map from the conjugate module to the dual that intertwines their actions. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.6.2" (role := supporting)]
theorem exists_intertwiningMap_conjugate_dual [Fintype G] (ρ : Representation ℂ G V) :
    ∃ e : conjugateModule V ≃ₗ[ℂ] Module.Dual ℂ V,
      ∀ (g : G) (v : conjugateModule V),
        e (conjugateRepresentation ρ g v) = (Representation.dual ρ) g (e v) := by
  obtain ⟨c, hc⟩ := RepresentationTheory.Complex.InvariantInnerProduct.Representation.exists_invariantInnerProductCore G V ρ
  exact ⟨conjugateLinearEquivDual c, conjugateLinearEquivDual_intertwines ρ c hc⟩

end RepresentationTheory.Group.ConjugateDuality
