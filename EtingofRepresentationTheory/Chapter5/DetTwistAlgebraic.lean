import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2

/-!
# Algebraicity of the determinant-twisted Schur module representation

This file proves `detTwistedSchurModuleRep_isAlgebraic`: the determinant-twisted
Schur module representation `g ↦ det(g) • L_λ(g)` is an algebraic representation
of `GL_N(k)` in the sense of `Etingof.IsAlgebraicRepresentation`
(Definition 5.23.1). This is the algebraicity hypothesis consumed by
`decompose_polynomial_gl_rep` at the call site `schurModule_shift_iso_detTwist`
(#4756, sub-A of #4745).

The general algebraicity infrastructure (`glTensorRep_isAlgebraic`,
`IsAlgebraicRepresentation.restrict`, `IsAlgebraicRepresentation.detTwist`) now lives
upstream in `GLRepAlgebraic`, so that `schurModule_shift_iso_detTwist` can build its own
algebraicity hypothesis inline without an import cycle. This file just assembles them at
the concrete `detTwistedSchurModuleRep`:
`detTwistedSchurModuleRep = detTwist (restrict glTensorRep)`.
-/

open scoped TensorProduct
open Matrix

noncomputable section

namespace Etingof

/-! ### Algebraicity of the determinant-twisted Schur module -/

/-- The determinant-twisted Schur module representation `g ↦ det(g) • L_λ(g)` is
an algebraic representation of `GL_N(k)` (Etingof Definition 5.23.1).

Assembled from `glTensorRep_isAlgebraic` (the diagonal action is algebraic),
`IsAlgebraicRepresentation.restrict` (restrict to the Schur module submodule,
giving `schurModuleRep`), and `IsAlgebraicRepresentation.detTwist` (twist by the
determinant character). -/
theorem detTwistedSchurModuleRep_isAlgebraic (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (N : ℕ) (lam : Fin N → ℕ) :
    Etingof.IsAlgebraicRepresentation N
      (FDRep.of (detTwistedSchurModuleRep k N lam)).ρ := by
  rw [FDRep.of_ρ']
  have hrestrict :
      Etingof.IsAlgebraicRepresentation N (schurModuleRep k N lam) :=
    (glTensorRep_isAlgebraic k N (∑ i, lam i)).restrict
      (SchurModuleSubmodule k N lam)
      (fun g v hv => glTensorRep_mem_range k N lam g v hv)
  exact hrestrict.detTwist

end Etingof
