/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.Dual.SimpleFamilies
import RepresentationTheory.Alignment.Attribute

open Module

namespace RepresentationTheory.Module.SubmoduleQuotientAuxiliary

section Exercise361

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V]
  (W : Submodule A V)



/-- An invariant submodule of a finite-dimensional module is finite over the base field. -/
instance submodule_moduleFinite : Module.Finite k (W : Type _) :=
  Module.Finite.of_injective (W.subtype.restrictScalars k) Subtype.val_injective



/-- The quotient by an invariant submodule of a finite-dimensional module is finite over the base field. -/
instance quotient_moduleFinite : Module.Finite k (V ⧸ W) :=
  Module.Finite.of_surjective (W.mkQ.restrictScalars k) W.mkQ_surjective




/-- The auxiliary function for a finite-dimensional module is the sum of those for an invariant submodule and the corresponding quotient. -/
@[source_ref "Chapter3/Exercise3.6.1" (role := primary)]
theorem auxiliaryFunction_eq_submodule_add_quotient :
    RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A V =
      RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A (W : Type _) +
        RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A (V ⧸ W) := by
  classical
  ext a

  set fV : Module.End k V := (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a with hfV
  set fW : Module.End k (W : Type _) :=
    (Algebra.lsmul k k (W : Type _) : A →ₐ[k] Module.End k (W : Type _)) a with hfW
  set fQ : Module.End k (V ⧸ W) :=
    (Algebra.lsmul k k (V ⧸ W) : A →ₐ[k] Module.End k (V ⧸ W)) a with hfQ

  change LinearMap.trace k V fV
      = LinearMap.trace k (W : Type _) fW + LinearMap.trace k (V ⧸ W) fQ

  set i : (W : Type _) →ₗ[k] V := (W.subtype).restrictScalars k with hi_def
  set q : V →ₗ[k] (V ⧸ W) := (W.mkQ).restrictScalars k with hq_def

  have hiW : i ∘ₗ fW = fV ∘ₗ i := by ext w; rfl
  have hqV : q ∘ₗ fV = fQ ∘ₗ q := by ext v; rfl


  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr W.mkQ_surjective)

  set pW : V →ₗ[k] V := LinearMap.id - s ∘ₗ q with hpW_def
  have hpW_mem : ∀ v : V, pW v ∈ W := by
    intro v
    have hqpW : q (pW v) = 0 := by
      have hqs : q (s (q v)) = q v := LinearMap.congr_fun hs (q v)
      simp only [hpW_def, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply,
        map_sub, hqs, sub_self]
    exact (Submodule.Quotient.mk_eq_zero W).mp hqpW

  set r : V →ₗ[k] (W : Type _) :=
    { toFun := fun v => ⟨pW v, hpW_mem v⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp } with hr_def

  have hir : i ∘ₗ r = pW := by ext v; rfl
  have hri : r ∘ₗ i = LinearMap.id := by
    ext w
    have hqiw : q (i w) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr w.2
    change (pW (i w) : V) = (w : V)
    have hpi : pW (i w) = i w := by
      rw [hpW_def]
      simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, hqiw,
        map_zero, sub_zero]
    rw [hpi]
    rfl

  have hid : pW + s ∘ₗ q = LinearMap.id := by rw [hpW_def]; abel

  have hqfVs : q ∘ₗ (fV ∘ₗ s) = fQ := by
    rw [← LinearMap.comp_assoc, hqV, LinearMap.comp_assoc, hs, LinearMap.comp_id]

  have hrfVi : r ∘ₗ (fV ∘ₗ i) = fW := by
    rw [← hiW, ← LinearMap.comp_assoc, hri, LinearMap.id_comp]

  have hterm2 : LinearMap.trace k V (fV ∘ₗ (s ∘ₗ q)) = LinearMap.trace k (V ⧸ W) fQ := by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm' q (fV ∘ₗ s), hqfVs]
  have hterm1 : LinearMap.trace k V (fV ∘ₗ pW) = LinearMap.trace k (W : Type _) fW := by
    rw [← hir, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm' r (fV ∘ₗ i), hrfVi]

  calc LinearMap.trace k V fV
      = LinearMap.trace k V (fV ∘ₗ LinearMap.id) := by rw [LinearMap.comp_id]
    _ = LinearMap.trace k V (fV ∘ₗ (pW + s ∘ₗ q)) := by rw [← hid]
    _ = LinearMap.trace k V (fV ∘ₗ pW + fV ∘ₗ (s ∘ₗ q)) := by rw [LinearMap.comp_add]
    _ = LinearMap.trace k V (fV ∘ₗ pW) + LinearMap.trace k V (fV ∘ₗ (s ∘ₗ q)) := by rw [map_add]
    _ = LinearMap.trace k (W : Type _) fW + LinearMap.trace k (V ⧸ W) fQ := by
        rw [hterm1, hterm2]

attribute [source_ref "Chapter3/Theorem3.7.1/Derived6" (role := supporting)]
  auxiliaryFunction_eq_submodule_add_quotient

end Exercise361

end RepresentationTheory.Module.SubmoduleQuotientAuxiliary
