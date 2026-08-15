/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Algebra.ModuleActions

open scoped TensorProduct
open Module (End)

namespace RepresentationTheory.Representation.AlgebraDensity

section dualTensorHom

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Applying a linear map to the vector factor of a dual tensor postcomposes its associated endomorphism. -/
theorem dualTensorHom_map_right (T : V →ₗ[k] V)
    (z : Module.Dual k V ⊗[k] V) :
    dualTensorHom k V V (TensorProduct.map LinearMap.id T z)
      = T ∘ₗ dualTensorHom k V V z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
      rw [TensorProduct.map_tmul]
      ext w
      simp [dualTensorHom_apply, map_smul]
  | add a b ha hb => simp only [map_add, LinearMap.comp_add, ha, hb]

/-- Precomposing a rank-one endomorphism by a linear map precomposes its covector factor. -/
theorem dualTensorHom_tmul_comp (φ : Module.Dual k V) (w : V) (S : V →ₗ[k] V) :
    dualTensorHom k V V (φ ⊗ₜ[k] w) ∘ₗ S
      = dualTensorHom k V V ((φ ∘ₗ S) ⊗ₜ[k] w) := by
  ext x
  simp [dualTensorHom_apply]

end dualTensorHom

section traceNondegenerate

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The trace pairing detects every nonzero endomorphism of a finite-dimensional vector space. -/
theorem eq_zero_of_trace_comp_eq_zero (S : V →ₗ[k] V)
    (h : ∀ T : V →ₗ[k] V, LinearMap.trace k V (T ∘ₗ S) = 0) : S = 0 := by
  ext w
  rw [LinearMap.zero_apply]
  rw [← Module.forall_dual_apply_eq_zero_iff k (S w)]
  intro φ
  have hT := h (dualTensorHom k V V (φ ⊗ₜ[k] w))
  rw [dualTensorHom_tmul_comp, LinearMap.trace_eq_contract_apply, contractLeft_apply] at hT
  simpa using hT

end traceNondegenerate

end RepresentationTheory.Representation.AlgebraDensity

namespace RepresentationTheory.Algebra.ModuleActions.RingActionStructure

section burnside

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 8000000 in
/-- An irreducible finite-dimensional representation over an algebraically closed field realizes every linear endomorphism through its induced algebra map. -/
theorem asAlgebraHom_surjective (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Function.Surjective ⇑(Representation.asAlgebraHom ρ) := by
  classical
  haveI : Module.Finite (Module.End (MonoidAlgebra k G) ρ.asModule) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k
      (Module.End (MonoidAlgebra k G) ρ.asModule) ρ.asModule
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (A := MonoidAlgebra k G) (V := ρ.asModule) k
  intro T
  set e := Representation.asModuleEquiv ρ with he
  set Tas : ρ.asModule →ₗ[k] ρ.asModule :=
    e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap with hTas
  have hTsmul : ∀ (f : Module.End (MonoidAlgebra k G) ρ.asModule) (m : ρ.asModule),
      Tas (f • m) = f • Tas m := by
    intro f m
    obtain ⟨r, hr⟩ := hschur.surjective f
    have hf : ∀ x : ρ.asModule, f • x = r • x := by
      intro x
      rw [← hr, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [hf m, hf (Tas m), map_smul]
  let T' : ρ.asModule →ₗ[Module.End (MonoidAlgebra k G) ρ.asModule] ρ.asModule :=
    { toFun := Tas, map_add' := Tas.map_add, map_smul' := hTsmul }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := MonoidAlgebra k G) (M := ρ.asModule) T'
  refine ⟨a, ?_⟩
  ext v
  have hm : a • e.symm v = Tas (e.symm v) := LinearMap.congr_fun ha (e.symm v)
  have hkey := congrArg e hm
  rw [Representation.asModuleEquiv_map_smul] at hkey
  simp only [hTas, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    he] at hkey
  exact hkey

/-- The images of the acting monoid in an irreducible representation linearly generate the full endomorphism space. -/
theorem span_range_eq_top (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Submodule.span k (Set.range (fun g => (ρ g : V →ₗ[k] V))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro T
  obtain ⟨a, rfl⟩ :=
    RepresentationTheory.Algebra.ModuleActions.RingActionStructure.asAlgebraHom_surjective ρ T
  induction a using MonoidAlgebra.induction_on with
  | hM g => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨g, rfl⟩
  | hadd f₁ f₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | hsmul r f h => rw [map_smul]; exact Submodule.smul_mem _ r h

end burnside

end RepresentationTheory.Algebra.ModuleActions.RingActionStructure

namespace RepresentationTheory.Representation.AlgebraDensity

section main

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A dual tensor is zero when each displayed contraction after the representation action is zero. -/
theorem eq_zero_of_contractLeft_representation_map_eq_zero (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule]
    (z : Module.Dual k V ⊗[k] V)
    (h : ∀ g, contractLeft k V (TensorProduct.map LinearMap.id (ρ g) z) = 0) :
    z = 0 := by
  set S : V →ₗ[k] V := dualTensorHom k V V z with hS
  have htr : ∀ g, LinearMap.trace k V ((ρ g : V →ₗ[k] V) ∘ₗ S) = 0 := by
    intro g
    have := h g
    rw [← LinearMap.trace_eq_contract_apply, dualTensorHom_map_right] at this
    rw [hS]; exact this
  have hall : ∀ T : V →ₗ[k] V, LinearMap.trace k V (T ∘ₗ S) = 0 := by
    have hspan :=
      RepresentationTheory.Algebra.ModuleActions.RingActionStructure.span_range_eq_top ρ
    intro T
    have hT : T ∈ Submodule.span k (Set.range (fun g => (ρ g : V →ₗ[k] V))) := by
      rw [hspan]; trivial
    induction hT using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact htr g
    | zero => simp
    | add x y _ _ hx hy => rw [LinearMap.add_comp, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.smul_comp, map_smul, hx, smul_zero]
  have hS0 : S = 0 := eq_zero_of_trace_comp_eq_zero S hall
  have hz : dualTensorHom k V V z = 0 := by rw [← hS]; exact hS0
  exact (dualTensorHomEquiv k V V).injective (by simpa using hz)

end main

end RepresentationTheory.Representation.AlgebraDensity
