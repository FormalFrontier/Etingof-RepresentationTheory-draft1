import Mathlib

/-!
# Matrix coefficients of a finite-dimensional simple representation are independent

This file proves the within-summand half of Peter-Weyl orthogonality at the abstract
level: for a finite-dimensional simple representation `ρ` of a monoid `G` over an
algebraically closed field `k`, the matrix coefficients of `V` are linearly
independent. Concretely, if `z : Module.Dual k V ⊗[k] V` satisfies

  `contractLeft k V (TensorProduct.map id (ρ g) z) = 0`   for every `g : G`,

then `z = 0`.

The argument is the trace-form / Burnside-density one:

* under `Module.Dual k V ⊗ V ≃ End k V` (`dualTensorHom`) a kernel element `z`
  becomes `S : End k V`, and the vanishing condition reads `trace (ρ g ∘ S) = 0`
  for every `g` (`trace_eq_contract_apply` together with
  `dualTensorHom_tensorMap_id_right`);
* **Burnside density** (`Representation.span_range_eq_top_of_isSimpleModule`): the
  `k`-linear span of `{ρ g}` is all of `End k V`. This is Schur's lemma over an
  algebraically closed field (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`,
  giving `End_{k[G]} V = k`) followed by the Jacobson density theorem
  (`Module.Finite.toModuleEnd_moduleEnd_surjective`);
* so `trace (T ∘ S) = 0` for *all* `T : End k V`, and nondegeneracy of the trace
  pairing (`eq_zero_of_forall_trace_comp_eq_zero`) forces `S = 0`, hence `z = 0`.

The output `matrixCoeff_injective_of_isSimpleModule` is the abstract engine behind
`Etingof.peterWeylSummandMap_injective`: the only representation-theoretic input it
needs is the simplicity of `ρ.asModule` as a `k[G]`-module.
-/

open scoped TensorProduct
open Module (End)

namespace Etingof

section dualTensorHom

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Pushing the right factor of a tensor through `dualTensorHom`: post-composition.
`dualTensorHom (id ⊗ T) z = T ∘ dualTensorHom z`. -/
theorem dualTensorHom_tensorMap_id_right (T : V →ₗ[k] V)
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

/-- Post-composing `dualTensorHom (φ ⊗ w)` with `S` re-expresses it as
`dualTensorHom ((φ ∘ S) ⊗ w)`: pre-composition pulls into the dual factor. -/
theorem dualTensorHom_comp_right (φ : Module.Dual k V) (w : V) (S : V →ₗ[k] V) :
    dualTensorHom k V V (φ ⊗ₜ[k] w) ∘ₗ S
      = dualTensorHom k V V ((φ ∘ₗ S) ⊗ₜ[k] w) := by
  ext x
  simp [dualTensorHom_apply]

end dualTensorHom

section traceNondegenerate

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Nondegeneracy of the trace pairing.** If `trace (T ∘ S) = 0` for every
`T : End k V`, then `S = 0`. (Take `T = dualTensorHom (φ ⊗ w)`; then
`trace (T ∘ S) = φ (S w)`, so every dual functional kills every `S w`.) -/
theorem eq_zero_of_forall_trace_comp_eq_zero (S : V →ₗ[k] V)
    (h : ∀ T : V →ₗ[k] V, LinearMap.trace k V (T ∘ₗ S) = 0) : S = 0 := by
  ext w
  rw [LinearMap.zero_apply]
  rw [← Module.forall_dual_apply_eq_zero_iff k (S w)]
  intro φ
  have hT := h (dualTensorHom k V V (φ ⊗ₜ[k] w))
  rw [dualTensorHom_comp_right, LinearMap.trace_eq_contract_apply, contractLeft_apply] at hT
  simpa using hT

end traceNondegenerate

section burnside

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Burnside density.** The `k`-linear span of the image `{ρ g}` of a
finite-dimensional simple representation over an algebraically closed field is all of
`End k V`. Equivalently, the algebra map `k[G] → End k V` (`ρ.asAlgebraHom`) is
surjective. -/
theorem Representation.asAlgebraHom_surjective_of_isSimpleModule (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Function.Surjective ⇑(Representation.asAlgebraHom ρ) := by
  classical
  -- `M = ρ.asModule` is finite over its endomorphism ring `End_{k[G]} M` (Jacobson input).
  haveI : Module.Finite (Module.End (MonoidAlgebra k G) ρ.asModule) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k
      (Module.End (MonoidAlgebra k G) ρ.asModule) ρ.asModule
  -- Schur's lemma over `k` algebraically closed: `End_{k[G]} M = k` (every endomorphism scalar).
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (A := MonoidAlgebra k G) (V := ρ.asModule) k
  intro T
  -- Transport `T` to an endomorphism of `M = ρ.asModule` (instances live there).
  set e := Representation.asModuleEquiv ρ with he
  set Tas : ρ.asModule →ₗ[k] ρ.asModule :=
    e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap with hTas
  -- `Tas` commutes with the scalars `End_{k[G]} M`, hence is `End_{k[G]} M`-linear.
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
  -- Jacobson density: `T'` is `m ↦ a • m` for some `a ∈ k[G]`.
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := MonoidAlgebra k G) (M := ρ.asModule) T'
  refine ⟨a, ?_⟩
  ext v
  -- `a • (e.symm v) = Tas (e.symm v)`; apply `e` and simplify both sides.
  have hm : a • e.symm v = Tas (e.symm v) := LinearMap.congr_fun ha (e.symm v)
  have hkey := congrArg e hm
  rw [Representation.asModuleEquiv_map_smul] at hkey
  -- LHS: `asAlgebraHom ρ a (e (e.symm v)) = asAlgebraHom ρ a v`.
  -- RHS: `e (Tas (e.symm v)) = T (e (e.symm v)) = T v`.
  simp only [hTas, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    he] at hkey
  exact hkey

/-- The `k`-linear span of `{ρ g}` is all of `End k V`. -/
theorem Representation.span_range_eq_top_of_isSimpleModule (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Submodule.span k (Set.range (fun g => (ρ g : V →ₗ[k] V))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro T
  obtain ⟨a, rfl⟩ := Representation.asAlgebraHom_surjective_of_isSimpleModule ρ T
  -- `asAlgebraHom a` is a `k`-linear combination of the `ρ g`.
  induction a using MonoidAlgebra.induction_on with
  | hM g => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨g, rfl⟩
  | hadd f₁ f₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | hsmul r f h => rw [map_smul]; exact Submodule.smul_mem _ r h

end burnside

section main

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Matrix coefficients of a simple representation are independent.** If
`z : Module.Dual k V ⊗ V` satisfies `contractLeft (id ⊗ ρ g) z = 0` for every `g`,
then `z = 0`. -/
theorem matrixCoeff_injective_of_isSimpleModule (ρ : Representation k G V)
    [IsSimpleModule (MonoidAlgebra k G) ρ.asModule]
    (z : Module.Dual k V ⊗[k] V)
    (h : ∀ g, contractLeft k V (TensorProduct.map LinearMap.id (ρ g) z) = 0) :
    z = 0 := by
  set S : V →ₗ[k] V := dualTensorHom k V V z with hS
  -- The vanishing condition reads `trace (ρ g ∘ S) = 0`.
  have htr : ∀ g, LinearMap.trace k V ((ρ g : V →ₗ[k] V) ∘ₗ S) = 0 := by
    intro g
    have := h g
    rw [← LinearMap.trace_eq_contract_apply, dualTensorHom_tensorMap_id_right] at this
    rw [hS]; exact this
  -- Burnside: upgrade to all `T`.
  have hall : ∀ T : V →ₗ[k] V, LinearMap.trace k V (T ∘ₗ S) = 0 := by
    have hspan := Representation.span_range_eq_top_of_isSimpleModule ρ
    intro T
    have hT : T ∈ Submodule.span k (Set.range (fun g => (ρ g : V →ₗ[k] V))) := by
      rw [hspan]; trivial
    induction hT using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact htr g
    | zero => simp
    | add x y _ _ hx hy => rw [LinearMap.add_comp, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.smul_comp, map_smul, hx, smul_zero]
  -- Trace nondegeneracy: `S = 0`, hence `z = 0`.
  have hS0 : S = 0 := eq_zero_of_forall_trace_comp_eq_zero S hall
  have hz : dualTensorHom k V V z = 0 := by rw [← hS]; exact hS0
  exact (dualTensorHomEquiv k V V).injective (by simpa using hz)

end main

end Etingof
