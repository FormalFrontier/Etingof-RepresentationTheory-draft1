/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.Alignment.Attribute

/-!
# Duality for modules over an algebra

This module equips linear duals with their natural opposite-algebra action and relates
projective modules to injective dual modules.
-/

universe u

namespace RepresentationTheory.Algebra.Module.Duality

open MulOpposite

variable (k : Type*) [Field k]
variable (A : Type*) [Ring A] [Algebra k A]
variable (P : Type*) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

/-- The natural `Aᵐᵒᵖ`-module structure on the `k`-linear dual of an `A`-module. -/
noncomputable instance Module.Dual.oppositeModule : Module Aᵐᵒᵖ (Module.Dual k P) where
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

/-- An opposite-ring scalar acts on a dual functional by precomposing with its underlying scalar action. -/
@[simp]
theorem Module.Dual.opposite_smul_apply (a : Aᵐᵒᵖ) (φ : Module.Dual k P) (p : P) :
    (a • φ) p = φ (a.unop • p) :=
  rfl

/-- Scalars from `k` and `Aᵐᵒᵖ` act compatibly on the dual of an `A`-module. -/
instance Module.Dual.isScalarTower : IsScalarTower k Aᵐᵒᵖ (Module.Dual k P) where
  smul_assoc c a φ := by
    ext p
    change φ ((c • a).unop • p) = c • φ (a.unop • p)
    rw [unop_smul, smul_assoc, map_smul]

/-- The `k`-linear dual of an algebra is injective as a module over its opposite ring. -/
theorem Module.Dual.algebra_isInjective :
    Module.Injective Aᵐᵒᵖ (Module.Dual k A) := by
  apply Module.Baer.injective
  intro I g
  let eval1 : Module.Dual k A →ₗ[k] k :=
    { toFun := fun φ => φ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let restr : (I.restrictScalars k) →ₗ[k] I :=
    { toFun := fun v => ⟨v.1, v.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let γ : (I.restrictScalars k) →ₗ[k] k := eval1 ∘ₗ (g.restrictScalars k) ∘ₗ restr
  obtain ⟨γ', hγ'⟩ := γ.exists_extend
  refine ⟨{ toFun := fun y =>
              γ' ∘ₗ (LinearMap.mulRight k y) ∘ₗ (opLinearEquiv k (M := A)).toLinearMap
            map_add' := fun y z => by ext a; simp [mul_add]
            map_smul' := fun b y => by
              ext a
              simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
                LinearEquiv.coe_coe, coe_opLinearEquiv, Module.Dual.opposite_smul_apply,
                RingHom.id_apply, smul_eq_mul]
              rw [op_mul, op_unop, ← mul_assoc] }, ?_⟩
  intro x hx
  ext a
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulRight_apply, LinearEquiv.coe_coe, coe_opLinearEquiv]
  have hmem : op a * x ∈ I := I.smul_mem (op a) hx
  have hext : γ' (op a * x) = g ⟨op a * x, hmem⟩ (1 : A) := by
    have h1 : γ' (op a * x) = γ ⟨op a * x, hmem⟩ :=
      LinearMap.congr_fun hγ' (⟨op a * x, hmem⟩ : I.restrictScalars k)
    rw [h1]; rfl
  rw [hext]
  have hsm : (⟨op a * x, hmem⟩ : I) = (op a) • (⟨x, hx⟩ : I) := by
    apply Subtype.ext; rfl
  rw [hsm, map_smul, Module.Dual.opposite_smul_apply]
  change g ⟨x, hx⟩ (a • (1 : A)) = g ⟨x, hx⟩ a
  rw [smul_eq_mul, mul_one]

/-- A retract of an injective module is injective. -/
theorem Module.Injective.ofRetract {R : Type*} [Ring R] {M N : Type w}
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

/-- The transpose of an `A`-linear map as an `Aᵐᵒᵖ`-linear map between `k`-linear duals. -/
def Module.Dual.linearTranspose (f : M →ₗ[A] N) : Module.Dual k N →ₗ[Aᵐᵒᵖ] Module.Dual k M where
  toFun φ := φ ∘ₗ f.restrictScalars k
  map_add' φ ψ := by ext m; rfl
  map_smul' a φ := by
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      Module.Dual.opposite_smul_apply, RingHom.id_apply]
    rw [f.map_smul]

/-- Evaluating a transposed linear map is evaluation of the functional after the original map. -/
@[simp]
theorem Module.Dual.linearTranspose_apply (f : M →ₗ[A] N) (φ : Module.Dual k N) (m : M) :
    Module.Dual.linearTranspose k A f φ m = φ (f m) :=
  rfl

end Functor

/-- The dual of finitely supported `A`-valued functions is linearly equivalent to arbitrary functions into the dual of `A`. -/
noncomputable def Module.Dual.finsuppLinearEquiv :
    Module.Dual k (P →₀ A) ≃ₗ[Aᵐᵒᵖ] (P → Module.Dual k A) where
  toFun φ := fun p => φ ∘ₗ Finsupp.lsingle (R := k) p
  map_add' φ ψ := by ext p a; rfl
  map_smul' a φ := by
    ext p b
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      Module.Dual.opposite_smul_apply, Pi.smul_apply, RingHom.id_apply, Finsupp.smul_single]
  invFun g := Finsupp.lsum (R := k) k g
  left_inv φ := by
    have hsymm : (fun p => φ ∘ₗ Finsupp.lsingle (R := k) p) =
        (Finsupp.lsum (R := k) k).symm φ := by
      funext p; exact (Finsupp.lsum_symm_apply (S := k) φ p).symm
    change Finsupp.lsum (R := k) k (fun p => φ ∘ₗ Finsupp.lsingle (R := k) p) = φ
    rw [hsymm, LinearEquiv.apply_symm_apply]
  right_inv g := by
    funext p
    exact Finsupp.lsum_comp_lsingle (S := k) g p

/-- The `k`-linear dual of a projective algebra module is injective over the opposite algebra. -/
theorem Module.Dual.injective_of_projective.{uk, uA, uP}
    {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
    {P : Type uP} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Projective A P] :
    Module.Injective Aᵐᵒᵖ (Module.Dual k P) := by
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := A) (P := P)).mp ‹_›
  set π : (P →₀ A) →ₗ[A] P := Finsupp.linearCombination A id with hπ
  haveI sA : Small.{max uA uk} Aᵐᵒᵖ := small_max.{uk, uA} Aᵐᵒᵖ
  have hpi : Module.Injective Aᵐᵒᵖ (P → Module.Dual k A) :=
    @Module.Injective.pi Aᵐᵒᵖ _ P (fun _ : P => Module.Dual k A) sA _ _
      (fun _ => Module.Dual.algebra_isInjective k A)
  have hF : Module.Injective Aᵐᵒᵖ (Module.Dual k (P →₀ A)) :=
    Module.Injective.ofRetract (Module.Dual.finsuppLinearEquiv k A P).toLinearMap
      (Module.Dual.finsuppLinearEquiv k A P).symm.toLinearMap (by ext x; simp) hpi
  haveI sB : Small.{max uP uA uk} Aᵐᵒᵖ := small_max.{max uP uk, uA} Aᵐᵒᵖ
  have hBF : Module.Baer Aᵐᵒᵖ (Module.Dual k (P →₀ A)) := Module.Baer.of_injective hF
  have hid : ∀ ψ : Module.Dual k P,
      Module.Dual.linearTranspose k A s (Module.Dual.linearTranspose k A π ψ) = ψ := by
    intro ψ; ext m
    simp only [Module.Dual.linearTranspose_apply]
    rw [show π (s m) = m from LinearMap.congr_fun hs m]
  apply Module.Baer.injective
  intro I g
  obtain ⟨g', hg'⟩ := hBF I ((Module.Dual.linearTranspose k A π) ∘ₗ g)
  refine ⟨(Module.Dual.linearTranspose k A s) ∘ₗ g', fun x hx => ?_⟩
  rw [LinearMap.comp_apply, hg' x hx, LinearMap.comp_apply, hid]

/-- A finite-dimensional module is projective when its `k`-linear dual is injective over the opposite algebra. -/
theorem Module.Projective.ofDualInjective {k : Type u} [Field k]
    {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {P : Type u} [AddCommGroup P] [Module k P] [Module A P]
    [IsScalarTower k A P] [FiniteDimensional k P]
    (hInj : Module.Injective Aᵐᵒᵖ (Module.Dual k P)) :
    Module.Projective A P := by
  classical
  haveI : Module.Finite A P := Module.Finite.of_restrictScalars_finite k A P
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  set F := Fin n → A with hF
  have hDπ : Function.Injective (Module.Dual.linearTranspose k A π) := by
    intro φ ψ h
    ext p
    obtain ⟨x, rfl⟩ := hπ p
    simpa only [Module.Dual.linearTranspose_apply] using LinearMap.congr_fun h x
  haveI := hInj
  obtain ⟨ρ, hρ⟩ := Module.Injective.extension_property Aᵐᵒᵖ (Module.Dual k P)
    (Module.Dual k P) (Module.Dual k F) (Module.Dual.linearTranspose k A π) hDπ LinearMap.id
  set σₖ : P →ₗ[k] F := (Module.evalEquiv k F).symm.toLinearMap ∘ₗ
      (ρ.restrictScalars k).dualMap ∘ₗ (Module.evalEquiv k P).toLinearMap with hσₖ
  have hkey : ∀ (p : P) (ψ : Module.Dual k F),
      Module.evalEquiv k F (σₖ p) ψ = Module.evalEquiv k P p (ρ ψ) := by
    intro p ψ
    have h := (Module.evalEquiv k F).apply_symm_apply
      ((ρ.restrictScalars k).dualMap (Module.evalEquiv k P p))
    rw [hσₖ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h, LinearMap.dualMap_apply, LinearMap.coe_restrictScalars]
  have hσ_smul : ∀ (a : A) (p : P), σₖ (a • p) = a • σₖ p := by
    intro a p
    refine (Module.evalEquiv k F).injective ?_
    ext ψ
    have e1 : Module.evalEquiv k F (σₖ (a • p)) ψ = ρ ψ (a • p) := by
      rw [hkey, Module.evalEquiv_apply, Module.Dual.eval_apply]
    have e2 : Module.evalEquiv k F (a • σₖ p) ψ = ρ ψ (a • p) := by
      have h1 : Module.evalEquiv k F (a • σₖ p) ψ =
          Module.evalEquiv k F (σₖ p) (op a • ψ) := rfl
      rw [h1, hkey, map_smul]
      rfl
    rw [e1, e2]
  have hπσ : ∀ p : P, π (σₖ p) = p := by
    intro p
    refine (Module.evalEquiv k P).injective ?_
    ext φ
    have hc : Module.evalEquiv k P (π (σₖ p)) φ =
        Module.evalEquiv k F (σₖ p) (Module.Dual.linearTranspose k A π φ) := rfl
    rw [hc, hkey,
      show ρ (Module.Dual.linearTranspose k A π φ) = φ from LinearMap.congr_fun hρ φ]
  let σ : P →ₗ[A] F :=
    { toFun := σₖ
      map_add' := map_add σₖ
      map_smul' := fun a p => hσ_smul a p }
  exact Module.Projective.of_split σ π (by ext p; exact hπσ p)

/-- For finite-dimensional algebra modules, projectivity is equivalent to injectivity of the `k`-linear dual over the opposite algebra. -/
@[source_ref "Chapter8/Example8.1.7" (role := primary)]
theorem Module.projective_iff_dual_injective
    {k : Type u} [Field k]
    {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {P : Type u} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [FiniteDimensional k P] :
    Module.Projective A P ↔ Module.Injective Aᵐᵒᵖ (Module.Dual k P) := by
  refine ⟨fun hP => ?_, fun hInj => ?_⟩
  · haveI := hP
    exact Module.Dual.injective_of_projective
  · exact Module.Projective.ofDualInjective hInj

end RepresentationTheory.Algebra.Module.Duality
