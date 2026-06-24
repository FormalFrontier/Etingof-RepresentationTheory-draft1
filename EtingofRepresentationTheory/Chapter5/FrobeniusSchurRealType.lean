import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.Definition5_1_4

/-!
# Frobenius-Schur indicator bridge: `FS(ρ) = 1 ⟹ IsRealType ρ`

This file connects the *numerical* Frobenius-Schur indicator
(`Etingof.frobeniusSchurIndicator`, Definition 5.1.4) to the *structural* type
predicate `Etingof.IsRealType` (Definition 5.1.1): a simple complex
representation `ρ` with `frobeniusSchurIndicator ρ = 1` admits a nondegenerate
symmetric `G`-invariant bilinear form, so it is of real type.

This bridge is the shared dependency of the S₃, S₄ and A₅ cases of Example 5.1.3.

## Proof strategy (Etingof, around Theorem 5.1.5)

Work in `Bil := V →ₗ[ℂ] V →ₗ[ℂ] ℂ`, the space of bilinear forms, which carries
the `G`-action `(g · B)(v, w) = B (ρ g⁻¹ v) (ρ g⁻¹ w)` — this is
`Representation.linHom ρ ρ.dual`. The swap `τ B := fun v w => B w v` is
`G`-equivariant with `τ² = 1`; its `+1`/`-1` eigenspaces are the symmetric /
skew-symmetric forms.

1. The invariant forms `Bil^G ≅ Hom_G(V, V*) = IntertwiningMap ρ ρ.dual`; for
   simple `V` this is `0`- or `1`-dimensional (Schur, via
   `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`).
2. The crux trace identity:
   `dim (sym ∩ Bil^G) − dim (skew ∩ Bil^G) = trace(τ ∘ P)
   = (|G|)⁻¹ ∑_g trace(τ ∘ (g·)) = (|G|)⁻¹ ∑_g χ_V(g²) = FS(ρ)`,
   where `P` is the averaging projector onto `Bil^G`. The middle trace
   `trace(τ ∘ (g·))` on `V* ⊗ V*` evaluates to `χ_V(g²) = tr(ρ g)²`, the
   `χ(g²) = χ_{S²} − χ_{Λ²}` identity of Theorem 5.1.5 phrased via the swap.
3. `FS = 1` with `dim(sym∩Bil^G) + dim(skew∩Bil^G) ∈ {0,1}` forces
   `dim(sym∩Bil^G) = 1`: a nonzero invariant **symmetric** form exists.
4. Nondegeneracy: the radical `{v | ∀ w, B v w = 0} = ker B` is a `ρ`-invariant
   submodule, proper (since `B ≠ 0`), hence `⊥` by simplicity. So `B` is
   nondegenerate.

Step 4 (the nondegeneracy bridge) is fully proved below as
`Etingof.nondegenerate_of_invariant_of_simple`. Steps 1–3 — the existence of a
nonzero invariant symmetric form, packaged as
`Etingof.exists_nonzero_invariant_symmetric_of_FS_eq_one` — are the trace-identity
heart and are currently isolated as a `sorry`.
-/

open scoped MonoidAlgebra

namespace Etingof

variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero `G`-invariant bilinear form on a *simple* representation is
automatically nondegenerate: its left radical `ker B = {v | ∀ w, B v w = 0}` is
a `ρ`-invariant submodule, proper (as `B ≠ 0`), hence `⊥` by simplicity.

No symmetry or finite-dimensionality hypothesis is needed. -/
theorem nondegenerate_of_invariant_of_simple
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  -- The radical `ker B` is `ρ`-invariant.
  have hRinv : LinearMap.ker B ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext w
    simp only [LinearMap.zero_apply]
    have hgg : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : B (ρ g x) w = B (ρ g x) (ρ g (ρ g⁻¹ w)) := by rw [hgg]
    rw [h1, hinv g x (ρ g⁻¹ w)]
    rw [hx]
    simp
  -- Simplicity transports to the lattice of `ρ`-invariant submodules.
  haveI := hρ
  haveI hSO : IsSimpleOrder ρ.invtSubmodule :=
    (Representation.mapSubmodule ρ).isSimpleOrder_iff.mpr hρ.toIsSimpleOrder
  -- The radical is `⊥` or `⊤`; `B ≠ 0` rules out `⊤`.
  have hker : LinearMap.ker B = ⊥ := by
    rcases hSO.eq_bot_or_eq_top ⟨LinearMap.ker B, hRinv⟩ with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (LinearMap.ker_eq_top.mp (by simpa using congrArg Subtype.val h)) hBne
  -- `ker B = ⊥` is exactly nondegeneracy.
  intro v hv
  have hv' : v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]; ext w; exact hv w
  rw [hker, Submodule.mem_bot] at hv'
  exact hv'

variable [Fintype G] [DecidableEq G] [Module.Finite ℂ V]

/-- **Existence of a nonzero invariant symmetric form when `FS = 1`** (steps 1–3
of the strategy above). For a simple complex representation `ρ` with
`frobeniusSchurIndicator ρ = 1`, there is a nonzero `G`-invariant *symmetric*
bilinear form on `V`.

The proof is the trace-identity argument
`dim(sym ∩ Bil^G) − dim(skew ∩ Bil^G) = FS(ρ)` together with the Schur bound
`dim Bil^G ≤ 1`. Isolated as a `sorry` pending that computation. -/
theorem exists_nonzero_invariant_symmetric_of_FS_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : Etingof.frobeniusSchurIndicator ρ = 1) :
    ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ v w, B v w = B w v) ∧ B ≠ 0 ∧ (∀ g v w, B (ρ g v) (ρ g w) = B v w) := by
  sorry

/-- **The FS-indicator bridge.** A simple complex representation whose
Frobenius-Schur indicator equals `1` is of real type (Etingof, around
Theorem 5.1.5; the per-representation companion of Definition 5.1.4). -/
theorem isRealType_of_frobeniusSchurIndicator_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : Etingof.frobeniusSchurIndicator ρ = 1) :
    Etingof.IsRealType ρ := by
  obtain ⟨B, hsym, hBne, hinv⟩ :=
    exists_nonzero_invariant_symmetric_of_FS_eq_one ρ hρ hFS
  exact ⟨B, hsym, nondegenerate_of_invariant_of_simple ρ hρ B hBne hinv, hinv⟩

end Etingof
