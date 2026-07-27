import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Analysis.Complex.Polynomial.Basic


/-!
# Problem 2.16.1: Lie's theorem

The **commutant** `K(𝔤)` of a Lie algebra `𝔤` is the linear span of the elements `[x, y]`; it is
an ideal in `𝔤`. A finite dimensional Lie algebra `𝔤` is **solvable** if `Kⁿ(𝔤) = 0` for some `n`.
**Lie's theorem:** if `k = ℂ` and `V` is a finite dimensional irreducible representation of a
solvable Lie algebra `𝔤`, then `V` is 1-dimensional.

## Formalization

Solvability is Mathlib's `LieAlgebra.IsSolvable` (defined via the derived series, matching the
`Kⁿ(𝔤) = 0` condition). A representation of `𝔤` is a `LieModule`; irreducibility ("the only
subrepresentations are `0` and `V`") is `IsSimpleOrder (LieSubmodule ℂ 𝔤 V)`. The conclusion
"`V` is 1-dimensional" is `Module.finrank ℂ V = 1`.

The proof wraps Mathlib's Lie's theorem
(`LieModule.exists_nontrivial_weightSpace_of_isSolvable`), which supplies a common eigenvector
`v` for the whole solvable Lie algebra. The line `ℂ ∙ v` is then an `L`-invariant submodule (each
`x` sends `v` to the scalar multiple `χ x • v`), hence a nonzero `LieSubmodule`; irreducibility
forces it to be all of `V`, so `V` is one-dimensional.
-/

namespace Etingof.Problem2_16_1

open Module (finrank)

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- **Problem 2.16.1 (Lie's theorem).** A finite dimensional irreducible representation `V` of a
solvable complex Lie algebra `L` is one-dimensional. -/
theorem finrank_eq_one_of_isSolvable [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℂ V] [Nontrivial V] (hirr : IsSimpleOrder (LieSubmodule ℂ L V)) :
    finrank ℂ V = 1 := by
  -- Lie's theorem: a common eigenvector `v` for the action of every `x ∈ L` exists.
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable ℂ L V
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  rw [LieModule.mem_weightSpace] at hv
  have hv0 : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  -- The line `ℂ ∙ v` is `L`-invariant, hence a `LieSubmodule`.
  let N : LieSubmodule ℂ L V :=
    { __ := Submodule.span ℂ {v}
      lie_mem := fun {x m} hm => by
        have hm' : m ∈ Submodule.span ℂ {v} := hm
        rw [Submodule.mem_span_singleton] at hm'
        obtain ⟨c, rfl⟩ := hm'
        exact Submodule.mem_span_singleton.mpr ⟨c * χ x, by rw [lie_smul, hv x, smul_smul]⟩ }
  -- It is nonzero (contains `v ≠ 0`), so by irreducibility it is all of `V`.
  have hN : N ≠ ⊥ := fun h => hv0 (by
    have : v ∈ N := Submodule.mem_span_singleton_self v
    rwa [h, LieSubmodule.mem_bot] at this)
  have hspan : Submodule.span ℂ {v} = ⊤ := by
    have : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
    rwa [← LieSubmodule.toSubmodule_eq_top] at this
  rw [← finrank_top ℂ V, ← hspan, finrank_span_singleton hv0]

end Etingof.Problem2_16_1
