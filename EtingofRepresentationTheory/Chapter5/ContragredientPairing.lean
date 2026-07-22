import Mathlib

/-!
# The canonical evaluation pairing of a representation and its contragredient

For a representation `ρ : Representation k G V` the contragredient (dual)
representation `ρ.dual` acts on `Module.Dual k V` by `(ρ.dual g) f = f ∘ ρ g⁻¹`
(`Representation.dual`). The canonical evaluation `Module.Dual k V ⊗[k] V → k`,
`f ⊗ v ↦ f v` (`contractLeft`), is the universal invariant pairing
between a representation and its contragredient.

This file records the two structural facts that make it a *pairing of
representations*:

* `contractLeft_dual_invariant` — the evaluation is `G`-invariant for the
  *diagonal* action `(ρ.dual g, ρ g)`: `⟨ρ.dual g · f, ρ g · v⟩ = ⟨f, v⟩`.
* `contractLeft_ne_zero` — for a nonzero finite-dimensional `V` the evaluation is
  a nonzero map.

This is the elementary, GL-agnostic "the contragredient pairing is the canonical
evaluation" brick of Etingof §5.23 (issue
https://github.com/.../issues/5515). The genuine `GL_n` contragredient pairing
`AlgIrrepGLDual n lam k ⊗ AlgIrrepGL n lam k → k` is obtained by transporting this
evaluation along the contragredient identity `L*_λ ≅ L_λ^∨` (tracked separately):
`AlgIrrepGLDual = L_{w₀λ}` is the *Schur-module* realization of the contragredient,
isomorphic to the linear dual `Module.Dual k (AlgIrrepGL n lam k)` carrying
`(algIrrepGLRepρ n lam k).dual`, and the evaluation pulls back across that
isomorphism.
-/

open scoped TensorProduct

namespace Etingof

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The canonical evaluation pairing is `G`-invariant.** For the diagonal action
`(ρ.dual g, ρ g)` on `Module.Dual k V ⊗[k] V`, the contraction
`f ⊗ v ↦ f v` is unchanged: `⟨ρ.dual g · f, ρ g · v⟩ = ⟨f, v⟩`. This is the
defining invariance of the contragredient pairing. -/
theorem contractLeft_dual_invariant (ρ : Representation k G V) (g : G)
    (f : Module.Dual k V) (v : V) :
    contractLeft k V ((ρ.dual g) f ⊗ₜ[k] (ρ g v))
      = contractLeft k V (f ⊗ₜ[k] v) := by
  rw [contractLeft_apply, contractLeft_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- **The canonical evaluation pairing is nonzero.** For a nonzero
finite-dimensional `V`, the contraction `Module.Dual k V ⊗[k] V → k` is not the
zero map: pick `v ≠ 0`, then some functional does not vanish on it. -/
theorem contractLeft_ne_zero [Nontrivial V] [FiniteDimensional k V] :
    contractLeft k V ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine hv ((Module.forall_dual_apply_eq_zero_iff k v).mp (fun f => ?_))
  have := congrArg (fun (m : Module.Dual k V ⊗[k] V →ₗ[k] k) => m (f ⊗ₜ[k] v)) h
  simpa [contractLeft_apply] using this

end Etingof
