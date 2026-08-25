/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Tactic.Abel
import RepresentationTheory.Alignment.Attribute

/-!
# Balanced tensor products over arbitrary rings

The balanced tensor product of a right module and a left module over a possibly
noncommutative ring, constructed as a quotient of a free abelian group.
-/

namespace RepresentationTheory.Algebra.Module.BalancedTensorProduct

open MulOpposite

/-- An auxiliary set in the free abelian group on pairs of module elements. -/
def auxiliaryRelations (A : Type*) [Ring A]
    (V : Type*) [AddCommGroup V] [Module Aᵐᵒᵖ V]
    (W : Type*) [AddCommGroup W] [Module A W] :
    Set (FreeAbelianGroup (V × W)) :=
  {x |
    (∃ (v₁ : V) (v₂ : V) (w : W), x = FreeAbelianGroup.of (v₁ + v₂, w)
        - FreeAbelianGroup.of (v₁, w) - FreeAbelianGroup.of (v₂, w)) ∨
    (∃ (v : V) (w₁ : W) (w₂ : W), x = FreeAbelianGroup.of (v, w₁ + w₂)
        - FreeAbelianGroup.of (v, w₁) - FreeAbelianGroup.of (v, w₂)) ∨
    (∃ (v : V) (a : A) (w : W), x = FreeAbelianGroup.of (op a • v, w)
        - FreeAbelianGroup.of (v, a • w))}

/-- An auxiliary type associated with a right module and a left module over a ring. -/
@[source_ref "Chapter2/Problem2.11.6" (role := supporting),
  source_ref "Chapter2/Remark2.11.4" (role := supporting)]
abbrev Auxiliary (A : Type*) [Ring A]
    (V : Type*) [AddCommGroup V] [Module Aᵐᵒᵖ V]
    (W : Type*) [AddCommGroup W] [Module A W] : Type _ :=
  FreeAbelianGroup (V × W) ⧸ AddSubgroup.closure (auxiliaryRelations A V W)

namespace Auxiliary

variable (A : Type*) [Ring A]
    (V : Type*) [AddCommGroup V] [Module Aᵐᵒᵖ V]
    (W : Type*) [AddCommGroup W] [Module A W]

variable {V W}

/-- The auxiliary element associated with a pair of module elements. -/
@[source_ref "Chapter2/Remark2.11.4" (role := supporting)]
def mk (v : V) (w : W) : Auxiliary A V W :=
  QuotientAddGroup.mk (FreeAbelianGroup.of (v, w))

/-- The auxiliary constructor is additive in its left argument. -/
@[source_ref "Chapter2/Remark2.11.4" (role := supporting)]
theorem add_left (v₁ v₂ : V) (w : W) :
    mk A (v₁ + v₂) w = mk A v₁ w + mk A v₂ w := by
  change QuotientAddGroup.mk (FreeAbelianGroup.of (v₁ + v₂, w)) =
    QuotientAddGroup.mk (FreeAbelianGroup.of (v₁, w)) +
      QuotientAddGroup.mk (FreeAbelianGroup.of (v₂, w))
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
  refine AddSubgroup.subset_closure (Or.inl ⟨v₁, v₂, w, ?_⟩)
  abel

/-- The auxiliary constructor is additive in its right argument. -/
@[source_ref "Chapter2/Remark2.11.4" (role := supporting)]
theorem add_right (v : V) (w₁ w₂ : W) :
    mk A v (w₁ + w₂) = mk A v w₁ + mk A v w₂ := by
  change QuotientAddGroup.mk (FreeAbelianGroup.of (v, w₁ + w₂)) =
    QuotientAddGroup.mk (FreeAbelianGroup.of (v, w₁)) +
      QuotientAddGroup.mk (FreeAbelianGroup.of (v, w₂))
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
  refine AddSubgroup.subset_closure (Or.inr (Or.inl ⟨v, w₁, w₂, ?_⟩))
  abel

/-- The auxiliary constructor identifies the opposite-ring action on the left input with the ring action on the right input. -/
@[source_ref "Chapter2/Remark2.11.4" (role := supporting)]
theorem op_smul_left_eq_smul_right (v : V) (a : A) (w : W) :
    mk A (op a • v) w = mk A v (a • w) := by
  change QuotientAddGroup.mk (FreeAbelianGroup.of (op a • v, w)) =
    QuotientAddGroup.mk (FreeAbelianGroup.of (v, a • w))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (Or.inr (Or.inr ⟨v, a, w, rfl⟩))

end Auxiliary

end RepresentationTheory.Algebra.Module.BalancedTensorProduct
