/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib

/-! # Tensor scalar extension -/

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.TensorScalarExtension

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- An algebra homomorphism from the original algebra to endomorphisms of the scalar-extended module. -/
noncomputable def scalarExtendedAction : A →ₐ[K] Module.End L (L ⊗[K] V) :=
  (Module.End.baseChangeHom K L V).comp (Algebra.lsmul K K V)

/-- An algebra homomorphism from the tensor-product algebra to endomorphisms of the scalar-extended module. -/
noncomputable def tensorProductAction : (L ⊗[K] A) →ₐ[L] Module.End L (L ⊗[K] V) :=
  AlgHom.liftEquiv K L A (Module.End L (L ⊗[K] V))
    (scalarExtendedAction (A := A) (V := V) (L := L))

/-- A module structure on tensor products of a scalar algebra, an algebra, and a module. -/
noncomputable instance tensorProductModule : Module (L ⊗[K] A) (L ⊗[K] V) :=
  Module.compHom (L ⊗[K] V) (R := Module.End L (L ⊗[K] V))
    (tensorProductAction (A := A) (V := V) (L := L)).toRingHom

end RepresentationTheory.Algebra.Module.TensorScalarExtension
