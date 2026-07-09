import Mathlib
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Power
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Cancellation

/-!
# Problem 3.8.4, the finite-extension case of scalar extension

This file assembles the two Problem 3.8.4 prerequisites into the **finite-extension case** of
part (i): for a finite field extension `L / K`, an `L ⊗[K] A`-linear isomorphism
`L ⊗[K] V ≃ L ⊗[K] W` forces `V ≃ W` over `A`.

The mechanism is exactly the book's hint restricted to a finite `L / K`:

* `Etingof.Problem3_8_4.baseChange_alinEquiv_pow` (from `Problem3_8_4_Power`) identifies the
  base change `L ⊗[K] V`, viewed as an `A`-module by restricting the `L ⊗[K] A`-action along
  `Algebra.TensorProduct.includeRight`, with the power `Vⁿ` where `n = finrank K L`;
* `bcRestrictScalars` below turns the given `L ⊗[K] A`-linear isomorphism into an `A`-linear
  one (both `A`-actions are the restricted `bcModRestrict`), because an `L ⊗[K] A`-linear map
  automatically commutes with the action of `1 ⊗ a`;
* composing gives `Vⁿ ≃ₗ[A] Wⁿ`, and `Etingof.Problem3_8_4.iso_pow_cancel` (Krull-Schmidt
  cancellation over the arbitrary field `K`, from `Problem3_8_4_Cancellation`) cancels the
  common power to yield `V ≃ₗ[A] W`.

The reduction of a *general* extension `L / K` to a finite subextension (the book's "reduce to
finitely generated, then finite extension" step) is the remaining ingredient needed to
discharge `Etingof.Problem3_8_4.iso_of_baseChange_iso`; it is tracked separately.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- Restrict an `L ⊗[K] A`-linear isomorphism of base changes to an `A`-linear isomorphism,
where both `A`-module structures are the restricted-scalars structure `bcModRestrict` (`a` acts
through `1 ⊗ a`). An `L ⊗[K] A`-linear map already commutes with the action of `1 ⊗ a`, so no
data is lost. -/
noncomputable def bcRestrictScalars (e : (L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W)) :
    (L ⊗[K] V) ≃ₗ[A] (L ⊗[K] W) where
  toFun := e
  map_add' := map_add e
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [bcModRestrict_smul (a := a) (x := x), bcModRestrict_smul (a := a) (x := e x)]
    exact e.map_smul _ x
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

@[simp]
theorem bcRestrictScalars_apply (e : (L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W)) (x : L ⊗[K] V) :
    bcRestrictScalars e x = e x := rfl

/-- **Problem 3.8.4(i), finite-extension case.** For a finite field extension `L / K`, if the
base changes `L ⊗[K] V` and `L ⊗[K] W` are isomorphic as `L ⊗[K] A`-modules, then `V` and `W`
are isomorphic as `A`-modules.

Restricting scalars along `Algebra.TensorProduct.includeRight` and applying the power
identification `L ⊗[K] V ≃ₗ[A] Vⁿ` (and likewise for `W`) turns the hypothesis into
`Vⁿ ≃ₗ[A] Wⁿ` with `n = finrank K L > 0`; Krull-Schmidt cancellation gives `V ≃ₗ[A] W`. -/
theorem iso_of_baseChange_iso_finite [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K L]
    (h : Nonempty ((L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W))) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨e⟩ := h
  obtain ⟨fV⟩ := baseChange_alinEquiv_pow (K := K) (A := A) (V := V) (L := L)
  obtain ⟨fW⟩ := baseChange_alinEquiv_pow (K := K) (A := A) (V := W) (L := L)
  have hpow :
      Nonempty ((Fin (Module.finrank K L) → V) ≃ₗ[A] (Fin (Module.finrank K L) → W)) :=
    ⟨fV.symm ≪≫ₗ bcRestrictScalars e ≪≫ₗ fW⟩
  exact iso_pow_cancel K A V W Module.finrank_pos hpow

end Etingof.Problem3_8_4
