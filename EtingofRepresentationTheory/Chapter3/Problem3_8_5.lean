import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Problem 3.8.5: periodic and antiperiodic functions

Let `A` be the algebra of real-valued continuous functions on `ℝ` that are periodic with
period `1`, and let `M` be the `A`-module of continuous functions `f` that are
**antiperiodic**: `f(x + 1) = −f(x)`.

* **(i)** `A` and `M` are indecomposable `A`-modules.
* **(ii)** `A` is not isomorphic to `M`, but `A ⊕ A ≅ M ⊕ M`.

We model `A` as the subalgebra `periodicSubalg` of `C(ℝ, ℝ)` cut out by `f(x+1) = f(x)`,
and `M` as the `A`-submodule `antiperiodicSubmod` of `C(ℝ, ℝ)` cut out by `f(x+1) = −f(x)`.
(`M` is closed under multiplication by a periodic function: if `g(x+1) = g(x)` and
`f(x+1) = −f(x)` then `(gf)(x+1) = −(gf)(x)`.) The regular module `A` and the module `M` are
then genuine `↥periodicSubalg`-modules.

`A ⊕ A ≅ M ⊕ M` reflects that `M ⊗_A M ≅ A` (antiperiodic × antiperiodic = periodic), so `M`
is an invertible module of order `2` in the Picard group of `A`; it is a nontrivial line
bundle on the circle (the Möbius bundle), whence `M ≇ A` yet `M ⊕ M ≅ A ⊕ A`.

The subalgebra and submodule carriers are genuine and their closure proof obligations are
discharged; the four theorems are left as `sorry`.
-/

namespace Etingof.Problem3_8_5

open scoped ContinuousMap

/-- The algebra `A` of continuous period-1 functions `ℝ → ℝ`, as a subalgebra of `C(ℝ, ℝ)`.
The carrier is the genuine set of periodic functions; closure under multiplication, addition,
and the algebra map follows from the defining identity `f (x + 1) = f x`. -/
noncomputable def periodicSubalg : Subalgebra ℝ C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = f x}
  mul_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.mul_apply, hf x, hg x]
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
  algebraMap_mem' := by
    intro r x
    simp

/-- The `A`-module `M` of continuous antiperiodic functions `f(x+1) = −f(x)`, as a submodule
of `C(ℝ, ℝ)` over the algebra `A = periodicSubalg`. The carrier is genuine; closure under
addition and multiplication by a periodic scalar follows from `f (x + 1) = - f x`. -/
noncomputable def antiperiodicSubmod : Submodule (periodicSubalg) C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = - f x}
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
    ring
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c f hf x
    have key : ∀ y : ℝ, (c • f) y = (c : C(ℝ, ℝ)) y * f y := by
      intro y
      rw [Algebra.smul_def]
      rfl
    rw [key (x + 1), key x, hf x, c.2 x]
    ring

/-- **Problem 3.8.5(i).** `A` is indecomposable as an `A`-module: the function algebra of the
circle has no nontrivial idempotents. -/
theorem periodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (periodicSubalg) := by
  sorry

/-- **Problem 3.8.5(i).** `M` is indecomposable as an `A`-module. -/
theorem antiperiodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (antiperiodicSubmod) := by
  sorry

/-- **Problem 3.8.5(ii), first part.** `A` is not isomorphic to `M` as `A`-modules: `M` is a
nontrivial line bundle on the circle (the Möbius bundle), so it is not free of rank 1. -/
theorem periodic_not_linearEquiv_antiperiodic :
    IsEmpty (periodicSubalg ≃ₗ[periodicSubalg] antiperiodicSubmod) := by
  sorry

/-- **Problem 3.8.5(ii), second part.** `A ⊕ A ≅ M ⊕ M` as `A`-modules. -/
theorem periodic_sq_linearEquiv_antiperiodic_sq :
    Nonempty ((periodicSubalg × periodicSubalg) ≃ₗ[periodicSubalg]
      (antiperiodicSubmod × antiperiodicSubmod)) := by
  sorry

end Etingof.Problem3_8_5
