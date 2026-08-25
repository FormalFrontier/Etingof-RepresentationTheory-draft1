/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.AuxiliaryLieModuleConstructions
import RepresentationTheory.Alignment.Attribute

/-! # A basis-dependent auxiliary algebra equivalence -/

namespace RepresentationTheory.Algebra.Lie.BasisAlgEquivAuxiliary

open RepresentationTheory.Algebra.AuxiliaryLieModuleConstructions

universe u v w

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]
variable {ι : Type w} (b : Module.Basis ι k L)

/-- An auxiliary algebra equivalence between the two displayed algebras associated with a chosen basis. -/
@[source_ref "Chapter2/Remark2.9.10" (role := primary)]
noncomputable def auxiliaryBasisAlgEquiv :
    UniversalEnvelopingAlgebra.auxiliaryBasisType k L b ≃ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L :=
  UniversalEnvelopingAlgebra.auxiliaryBasisEquiv k L b

end RepresentationTheory.Algebra.Lie.BasisAlgEquivAuxiliary
