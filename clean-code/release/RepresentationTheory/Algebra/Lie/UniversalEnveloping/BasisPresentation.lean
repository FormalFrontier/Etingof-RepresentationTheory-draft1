/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.BasisQuotientPresentations
import RepresentationTheory.Alignment.Attribute

/-! # Basis presentations of universal enveloping algebras -/

namespace RepresentationTheory.Algebra.Lie.UniversalEnveloping.BasisPresentation

universe u v w

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]
variable {ι : Type w} (b : Module.Basis ι k L)

/-- An algebra equivalence between a basis-dependent presentation of a Lie algebra and its universal enveloping algebra. -/
@[source_ref "Chapter2/Remark2.9.10" (role := primary)]
noncomputable def basisPresentationEquivUniversalEnveloping :
    RepresentationTheory.Algebra.BasisQuotientPresentations.UniversalEnvelopingAlgebra.BasisQuotientModel
        k L b ≃ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L :=
  RepresentationTheory.Algebra.BasisQuotientPresentations.UniversalEnvelopingAlgebra.basisQuotientEquivEnvelope
    k L b

end RepresentationTheory.Algebra.Lie.UniversalEnveloping.BasisPresentation
