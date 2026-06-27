import Mathlib
import EtingofRepresentationTheory.Chapter5.ContragredientPairing
import EtingofRepresentationTheory.Chapter5.ContragredientIdentity

/-!
# The typed contragredient pairing `L*_λ ⊗ L_λ → k` and its perfectness

Theorem 5.23.2(ii) (`Theorem5_23_2_PeterWeyl.lean`) needs the canonical evaluation
pairing in its *typed* form, between the two concrete `GL_n`-models

  `L*_λ = AlgIrrepGLDual n lam k`   (action `algIrrepGLRepDualρ`)
  `L_λ  = AlgIrrepGL n lam k`        (action `algIrrepGLRepρ`).

The elementary GL-agnostic evaluation `contractLeft k V : Module.Dual k V ⊗ V → k`
already carries the two structural facts (`ContragredientPairing.lean`, #5515):
it is invariant under the diagonal `(ρ.dual, ρ)`-action
(`contractLeft_dual_invariant`) and nonzero for nonzero finite-dimensional `V`
(`contractLeft_ne_zero`). The contragredient identity
`AlgIrrepGLDual n lam k ≃ₗ[k] Module.Dual k (AlgIrrepGL n lam k)` intertwining
`algIrrepGLRepDualρ` and `(algIrrepGLRepρ).dual` is real data (#5522,
`algIrrepGLDual_iso_linearDual`).

This file transports `contractLeft` across that isomorphism:

* `algIrrepDualPairing` — the typed pairing
  `AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k →ₗ[k] k`, defined as
  `contractLeft ∘ₗ TensorProduct.map e id` with `e` the #5522 iso.
* `algIrrepDualPairing_invariant` — `GL_n`-invariance for the diagonal action.
* `algIrrepDualPairing_ne_zero` — nonvanishing.
* `algIrrepDualPairing_nondegenerate` — **perfectness**. A nonzero `GL_n`-invariant
  pairing between two simple `k[GL_n]`-modules is nondegenerate on both sides: each
  radical is an invariant submodule, hence `⊥` by simplicity
  (`algIrrepGLRep_isSimple`). Scoped to `ℂ` and the Schur-Weyl range, where
  simplicity is available.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

/-! ## Abstract perfectness: one trivial radical from one simple factor -/

section AbstractPerfect

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **A nonzero invariant pairing has trivial left radical when the left factor is
simple.** For representations `ρV`, `ρW` and a bilinear `B : V →ₗ[k] W →ₗ[k] k`
invariant under the diagonal action (`B (ρV g v) (ρW g w) = B v w`), the left
radical `{v | ∀ w, B v w = 0} = ker B` is a `ρV`-invariant `k[G]`-submodule. It is
proper because `B ≠ 0`, hence `⊥` when `ρV` is simple. This is exactly left
nondegeneracy. -/
theorem ker_eq_bot_of_invariant_of_simple
    (ρV : Representation k G V) (ρW : Representation k G W)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρV.asModule)
    (B : V →ₗ[k] W →ₗ[k] k) (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρV g v) (ρW g w) = B v w) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  -- The radical `ker B` is `ρV`-invariant.
  have hRinv : LinearMap.ker B ∈ ρV.invtSubmodule := by
    rw [ρV.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext w
    simp only [LinearMap.zero_apply]
    have hgg : ρW g (ρW g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : B (ρV g x) w = B (ρV g x) (ρW g (ρW g⁻¹ w)) := by rw [hgg]
    rw [h1, hinv g x (ρW g⁻¹ w), hx]
    simp
  -- Simplicity transports to the lattice of `ρV`-invariant submodules.
  haveI := hV
  haveI hSO : IsSimpleOrder ρV.invtSubmodule :=
    (Representation.mapSubmodule ρV).isSimpleOrder_iff.mpr hV.toIsSimpleOrder
  have hker : LinearMap.ker B = ⊥ := by
    rcases hSO.eq_bot_or_eq_top ⟨LinearMap.ker B, hRinv⟩ with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (LinearMap.ker_eq_top.mp (by simpa using congrArg Subtype.val h)) hBne
  intro v hv
  have hv' : v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]; ext w; exact hv w
  rw [hker, Submodule.mem_bot] at hv'
  exact hv'

/-- **Perfectness of a nonzero invariant pairing between two simple modules.** If
both factors are simple and `B : V →ₗ[k] W →ₗ[k] k` is a nonzero pairing invariant
under the diagonal action, then `B` is nondegenerate on both sides. The left radical
is `ρV`-invariant, the right radical (`B.flip`) is `ρW`-invariant; each is `⊥` by
simplicity of the respective factor. -/
theorem nondegenerate_pairing_of_invariant_of_simple
    (ρV : Representation k G V) (ρW : Representation k G W)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρV.asModule)
    (hW : IsSimpleModule (MonoidAlgebra k G) ρW.asModule)
    (B : V →ₗ[k] W →ₗ[k] k) (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρV g v) (ρW g w) = B v w) :
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) := by
  refine ⟨ker_eq_bot_of_invariant_of_simple ρV ρW hV B hBne hinv, ?_⟩
  -- The right radical is the left radical of the flipped pairing.
  have hflipne : B.flip ≠ 0 := fun h => hBne (by rw [← LinearMap.flip_flip B, h]; rfl)
  have hflipinv : ∀ g w v, B.flip (ρW g w) (ρV g v) = B.flip w v := by
    intro g w v; simp only [LinearMap.flip_apply]; exact hinv g v w
  exact ker_eq_bot_of_invariant_of_simple ρW ρV hW B.flip hflipne hflipinv

end AbstractPerfect

/-! ## The contragredient identity iso as data -/

variable (n : ℕ) (lam : DominantWeight n) (k : Type*)
  [Field k] [IsAlgClosed k] [CharZero k]

/-- A choice of the contragredient-identity isomorphism
`L*_λ ≃ₗ Module.Dual k L_λ` from #5522 (`algIrrepGLDual_iso_linearDual`). Real data:
the `Nonempty` is discharged, not sorried. -/
noncomputable def algIrrepGLDualIso :
    AlgIrrepGLDual n lam k ≃ₗ[k] Module.Dual k (AlgIrrepGL n lam k) :=
  (Classical.choice (algIrrepGLDual_iso_linearDual n lam k)).1

/-- The chosen iso intertwines the Schur-module contragredient action
`algIrrepGLRepDualρ` with the linear-dual action `(algIrrepGLRepρ).dual`. -/
theorem algIrrepGLDualIso_intertwines (g : Matrix.GeneralLinearGroup (Fin n) k)
    (v : AlgIrrepGLDual n lam k) :
    algIrrepGLDualIso n lam k (algIrrepGLRepDualρ n lam k g v)
      = (algIrrepGLRepρ n lam k).dual g (algIrrepGLDualIso n lam k v) :=
  (Classical.choice (algIrrepGLDual_iso_linearDual n lam k)).2 g v

/-! ## The typed pairing -/

/-- **The typed contragredient pairing.** `L*_λ ⊗ L_λ → k`, obtained from the
canonical evaluation `contractLeft k L_λ : Module.Dual k L_λ ⊗ L_λ → k` by
transporting the left factor along the contragredient identity
`e : L*_λ ≃ₗ Module.Dual k L_λ` (#5522). The book's pairing of Theorem 5.23.2(ii). -/
noncomputable def algIrrepDualPairing :
    AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k →ₗ[k] k :=
  contractLeft k (AlgIrrepGL n lam k) ∘ₗ
    TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id

@[simp] theorem algIrrepDualPairing_tmul (u : AlgIrrepGLDual n lam k)
    (v : AlgIrrepGL n lam k) :
    algIrrepDualPairing n lam k (u ⊗ₜ[k] v)
      = contractLeft k (AlgIrrepGL n lam k) (algIrrepGLDualIso n lam k u ⊗ₜ[k] v) := by
  simp [algIrrepDualPairing]

/-- **The typed pairing is `GL_n`-invariant.** For the diagonal action
`(algIrrepGLRepDualρ g, algIrrepGLRepρ g)`, `algIrrepDualPairing` is unchanged.
Transports `contractLeft_dual_invariant` across the contragredient identity. -/
theorem algIrrepDualPairing_invariant (g : Matrix.GeneralLinearGroup (Fin n) k)
    (u : AlgIrrepGLDual n lam k) (v : AlgIrrepGL n lam k) :
    algIrrepDualPairing n lam k
        (algIrrepGLRepDualρ n lam k g u ⊗ₜ[k] algIrrepGLRepρ n lam k g v)
      = algIrrepDualPairing n lam k (u ⊗ₜ[k] v) := by
  rw [algIrrepDualPairing_tmul, algIrrepDualPairing_tmul,
    algIrrepGLDualIso_intertwines]
  exact contractLeft_dual_invariant (algIrrepGLRepρ n lam k) g
    (algIrrepGLDualIso n lam k u) v

/-- **The typed pairing is nonzero.** For a nonzero finite-dimensional `L_λ` the
canonical evaluation `contractLeft` is nonzero (`contractLeft_ne_zero`); since the
contragredient identity makes `TensorProduct.map e id` surjective, the composite is
nonzero too. -/
theorem algIrrepDualPairing_ne_zero [Nontrivial (AlgIrrepGL n lam k)] :
    algIrrepDualPairing n lam k ≠ 0 := by
  intro h
  -- `TensorProduct.map e id` is the underlying map of the equivalence `congr e refl`.
  have hsurj : Function.Surjective
      (TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap
        (LinearMap.id : AlgIrrepGL n lam k →ₗ[k] AlgIrrepGL n lam k)) := by
    have : TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap
        (LinearMap.id : AlgIrrepGL n lam k →ₗ[k] AlgIrrepGL n lam k)
        = (TensorProduct.congr (algIrrepGLDualIso n lam k)
            (LinearEquiv.refl k (AlgIrrepGL n lam k))).toLinearMap := by
      rw [TensorProduct.toLinearMap_congr]; rfl
    rw [this]
    exact (TensorProduct.congr (algIrrepGLDualIso n lam k)
      (LinearEquiv.refl k (AlgIrrepGL n lam k))).surjective
  refine contractLeft_ne_zero (k := k) (V := AlgIrrepGL n lam k) ?_
  refine LinearMap.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hsurj t
  have := congrArg (fun (m : _ →ₗ[k] k) => m s) h
  simpa [algIrrepDualPairing, LinearMap.comp_apply, LinearMap.zero_apply] using this

/-! ## Perfectness for `GL_n` over `ℂ` -/

/-- **Perfectness of the contragredient pairing for `GL_n(ℂ)`.** In the Schur-Weyl
range, both `L_λ` and its contragredient `L*_λ = L_{w₀λ}` are simple
(`algIrrepGLRep_isSimple`), and the typed pairing `algIrrepDualPairing` is a nonzero
`GL_n`-invariant pairing. Hence it is nondegenerate on both sides.

The range hypotheses `hN`/`hN'` scope to where `algIrrepGLRep_isSimple` currently
applies (over `ℂ`, weight sum `≤ n`); `hN'` is the same condition for the
`w₀`-twisted weight realizing `L*_λ`. -/
theorem algIrrepDualPairing_nondegenerate
    (hN : (∑ i, lam.toNatWeight i) ≤ n)
    (hN' : (∑ i, (lam.w0Twist).toNatWeight i) ≤ n) :
    (∀ u, (∀ v, algIrrepDualPairing n lam ℂ (u ⊗ₜ[ℂ] v) = 0) → u = 0) ∧
    (∀ v, (∀ u, algIrrepDualPairing n lam ℂ (u ⊗ₜ[ℂ] v) = 0) → v = 0) := by
  -- Simplicity of `L_λ` and `L*_λ = L_{w₀λ}`.
  haveI hWsimple : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (algIrrepGLRepρ n lam ℂ).asModule := algIrrepGLRep_isSimple n lam hN
  haveI hVsimple : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (algIrrepGLRepDualρ n lam ℂ).asModule := algIrrepGLRep_isSimple n lam.w0Twist hN'
  -- `L_λ` is nontrivial (simple modules are), so the pairing is nonzero.
  haveI : Nontrivial (AlgIrrepGL n lam ℂ) := by
    have hnt : Nontrivial (algIrrepGLRepρ n lam ℂ).asModule :=
      (Submodule.nontrivial_iff (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))).mp
        hWsimple.toNontrivial
    exact hnt
  -- The curried bilinear form of the pairing.
  set B := TensorProduct.curry (algIrrepDualPairing n lam ℂ) with hB
  have hBapp : ∀ u v, B u v = algIrrepDualPairing n lam ℂ (u ⊗ₜ[ℂ] v) := fun u v => rfl
  have hBne : B ≠ 0 := by
    intro h0
    refine algIrrepDualPairing_ne_zero n lam ℂ ?_
    apply TensorProduct.ext'
    intro u v
    rw [LinearMap.zero_apply, ← hBapp, h0]
    rfl
  have hBinv : ∀ g u v, B (algIrrepGLRepDualρ n lam ℂ g u) (algIrrepGLRepρ n lam ℂ g v)
      = B u v := by
    intro g u v
    rw [hBapp, hBapp]
    exact algIrrepDualPairing_invariant n lam ℂ g u v
  have := nondegenerate_pairing_of_invariant_of_simple
    (algIrrepGLRepDualρ n lam ℂ) (algIrrepGLRepρ n lam ℂ) hVsimple hWsimple B hBne hBinv
  simpa only [hBapp] using this

end Etingof
