import EtingofRepresentationTheory.Chapter2.Definition2_12_1

/-!
# Remark 2.9.10: independence of the chosen basis

Definition 2.9.9 presents the enveloping algebra using a chosen basis and its structure
constants.  The later coordinate-free construction in Definition 2.12.1 proves that this choice
does not affect the resulting algebra.  `basisPresentationEquiv` is the source-facing name for
that equivalence.
-/

namespace Etingof.Remark2_9_10

universe u v w

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]
variable {ι : Type w} (b : Module.Basis ι k L)

/-- The basis-and-structure-constants presentation of Definition 2.9.9 is algebra-equivalent to
the coordinate-free universal enveloping algebra, so it is independent of the chosen basis up
to canonical algebra equivalence. -/
noncomputable def basisPresentationEquiv :
    Etingof.UEABasisPresentation k L b ≃ₐ[k] Etingof.UniversalEnvelopingAlgebraDef k L :=
  Etingof.ueaBasisAlgEquiv k L b

end Etingof.Remark2_9_10
