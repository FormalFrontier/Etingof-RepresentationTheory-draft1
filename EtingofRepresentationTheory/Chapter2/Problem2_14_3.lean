import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Problem 2.14.3: The tensor-Hom adjunction for Lie algebra representations

Let `V, W, U` be finite dimensional representations of a Lie algebra `𝔤`. The problem asks to show
that `Hom_𝔤(V ⊗ W, U)` is isomorphic to `Hom_𝔤(V, U ⊗ W*)`.

## Formalization

Representations of `𝔤` are Lie modules; `Hom_𝔤(A, B)` is the space of Lie-module homomorphisms
`A →ₗ⁅k,L⁆ B`. The tensor product `V ⊗ W` carries its Lie-module structure from
`Mathlib.Algebra.Lie.TensorProduct`, and `W* = Module.Dual k W` carries the contragredient
Lie-module structure from `Module.Dual.instLieModule`. The isomorphism is `k`-linear.

## Proof outline

The isomorphism is the composition of the standard adjunction chain, restricted to the
Lie-equivariant subspaces:

* `TensorProduct.LieModule.liftLie` is the Lie-equivariant tensor-Hom adjunction
  `Hom_𝔤(V ⊗ W, U) ≅ Hom_𝔤(V, Hom_k(W, U))`.
* `dualHomEquiv` below is a Lie-module isomorphism `Hom_k(W, U) ≅ U ⊗ W*`, built from Mathlib's
  `dualTensorHomEquiv` (an equivalence because `W` is finite dimensional) and `TensorProduct.comm`,
  together with a check that the underlying map is `𝔤`-equivariant.
* `congrHomRight` postcomposes a fixed source `V` against a Lie-module equivalence, turning the
  Lie-module iso of the previous step into a `k`-linear iso of Hom spaces.
-/

namespace Etingof.Problem2_14_3

open scoped TensorProduct

-- Definitions in this file retain the stable book-number namespace, so they are explicitly
-- exempted from the naming linter that otherwise rejects underscores in declaration names.

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V W U : Type*}
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
  [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]
  [AddCommGroup U] [Module k U] [LieRingModule L U] [LieModule k L U]
  [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k U]

/-- The Lie-module equivalence `Hom_k(W, U) ≅ U ⊗ W*` sending `u ⊗ φ` (on the right) to the map
`w ↦ φ(w) • u`. The underlying `k`-linear equivalence is Mathlib's `dualTensorHomEquiv` composed
with `TensorProduct.comm`; the content here is that it is `𝔤`-equivariant. -/
@[nolint defsWithUnderscore]
noncomputable def dualHomEquiv :
    (W →ₗ[k] U) ≃ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W) :=
  LieModuleEquiv.symm
    { (TensorProduct.comm k U (Module.Dual k W)).trans (dualTensorHomEquiv k W U) with
      map_lie' := by
        intro x t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul u φ =>
          ext w
          simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
            TensorProduct.LieModule.lie_tmul_right, map_add, TensorProduct.comm_tmul,
            dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
            LinearMap.add_apply, Module.Dual.lie_apply, LieHom.lie_apply, lie_smul, neg_smul]
          abel
        | add a b ha hb =>
          simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe] at ha hb ⊢
          simp only [lie_add, map_add, ha, hb] }

/-- Postcomposition by a Lie-module equivalence `d : B ≃ₗ⁅k,L⁆ C` induces a `k`-linear equivalence
`Hom_𝔤(V, B) ≅ Hom_𝔤(V, C)`. -/
@[nolint defsWithUnderscore]
def congrHomRight {B C : Type*}
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    (d : B ≃ₗ⁅k,L⁆ C) : (V →ₗ⁅k,L⁆ B) ≃ₗ[k] (V →ₗ⁅k,L⁆ C) where
  toFun f := (d : B →ₗ⁅k,L⁆ C).comp f
  map_add' f g := by ext v; simp [LieModuleHom.comp_apply]
  map_smul' c f := by ext v; simp [LieModuleHom.comp_apply]
  invFun g := (d.symm : C →ₗ⁅k,L⁆ B).comp g
  left_inv f := by ext v; simp [LieModuleHom.comp_apply]
  right_inv g := by ext v; simp [LieModuleHom.comp_apply]

/-- **Problem 2.14.3.** The explicit linear equivalence
`Hom_𝔤(V ⊗ W, U) ≅ Hom_𝔤(V, U ⊗ W*)` for finite-dimensional Lie representations. -/
@[nolint defsWithUnderscore]
noncomputable def tensorHomAdjunction :
    (TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (V →ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W)) :=
  (TensorProduct.LieModule.liftLie k L V W U).symm.trans (congrHomRight dualHomEquiv)

omit [FiniteDimensional k V] [FiniteDimensional k U] in
/-- The existence form of `tensorHomAdjunction`, retained for compatibility with the original
statement-level formalization. -/
theorem exists_tensorHom_adjunction :
    Nonempty ((TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (V →ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W))) :=
  ⟨tensorHomAdjunction⟩

end Etingof.Problem2_14_3
