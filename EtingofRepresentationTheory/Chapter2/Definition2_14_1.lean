import Mathlib.Algebra.Lie.TensorProduct

/-!
# Definition 2.14.1: Tensor Product of Lie Algebra Representations

The **tensor product** of two representations V, W of a Lie algebra 𝔤 is the space
V ⊗ W with ρ_{V⊗W}(x) = ρ_V(x) ⊗ Id + Id ⊗ ρ_W(x).

## Mathlib correspondence

`Mathlib.Algebra.Lie.TensorProduct` equips `V ⊗ W` with the Leibniz Lie action via the
instances `TensorProduct.LieModule.lieRingModule` and `TensorProduct.LieModule.lieModule`.
Importing it brings those instances into scope, so `LieTensorProduct` below genuinely
carries the Lie module structure the book defines (not a plain `k`-module). The defining
Leibniz identity is recorded as `Etingof.LieTensorProduct.lie_tmul`.
-/

open scoped TensorProduct

/-- The tensor product of two Lie algebra representations, in the sense of
Etingof Definition 2.14.1. With `Mathlib.Algebra.Lie.TensorProduct` imported, the
`LieRingModule`/`LieModule` instances on `V ⊗ W` are in scope, so this abbrev carries
the Lie action `x · (v ⊗ w) = (x · v) ⊗ w + v ⊗ (x · w)` (the Leibniz rule), not merely
the underlying `k`-module. See `Etingof.LieTensorProduct.lie_tmul`. -/
abbrev Etingof.LieTensorProduct (k : Type*) (L : Type*) (V : Type*) (W : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W] :=
  TensorProduct k V W

namespace Etingof

variable {k L V W : Type*}
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]

/-- The defining content of Definition 2.14.1: the Lie action on the tensor product
`V ⊗ W` obeys the Leibniz rule `ρ_{V⊗W}(x) = ρ_V(x) ⊗ Id + Id ⊗ ρ_W(x)`, i.e. on simple
tensors `x · (v ⊗ w) = (x · v) ⊗ w + v ⊗ (x · w)`. -/
theorem LieTensorProduct.lie_tmul (x : L) (v : V) (w : W) :
    ⁅x, (v ⊗ₜ[k] w : LieTensorProduct k L V W)⁆ = ⁅x, v⁆ ⊗ₜ[k] w + v ⊗ₜ[k] ⁅x, w⁆ :=
  TensorProduct.LieModule.lie_tmul_right x v w

end Etingof
