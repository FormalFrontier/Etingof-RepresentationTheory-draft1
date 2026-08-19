/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.Dual.SimpleFamilies
import RepresentationTheory.Alignment.Attribute

open Module
open RepresentationTheory.Algebra.Module.Dual.SimpleFamilies

variable (k : Type*) (A : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [Free k V] [Module.Finite k V]

namespace RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap


/-- The displayed auxiliary linear map takes the same value on x times y and y times x. -/
theorem auxiliaryLinearMap_mul_comm (x y : A) :
    moduleDualElement k A V (x * y) = moduleDualElement k A V (y * x) := by
  simp only [moduleDualElement, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  exact LinearMap.trace_mul_comm k _ _


/-- An auxiliary base-linear submodule of an algebra. -/
def auxiliarySubmodule : Submodule k A :=
  Submodule.span k {z : A | ∃ x y : A, z = x * y - y * x}


/-- The displayed auxiliary submodule is contained in the kernel of the displayed auxiliary linear map. -/
theorem auxiliarySubmodule_le_ker :
    auxiliarySubmodule k A ≤ LinearMap.ker (moduleDualElement k A V) := by
  rw [auxiliarySubmodule, Submodule.span_le]
  rintro z ⟨x, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
  rw [auxiliaryLinearMap_mul_comm, sub_self]


/-- A linear map from the quotient of an algebra by the displayed auxiliary submodule to the base ring. -/
noncomputable def linearMapOnAuxiliaryQuotient : (A ⧸ auxiliarySubmodule k A) →ₗ[k] k :=
  Submodule.liftQ _ (moduleDualElement k A V) (auxiliarySubmodule_le_ker k A V)


/-- The displayed linear map on the auxiliary quotient agrees on a quotient class with the displayed auxiliary linear map. -/
theorem linearMapOnAuxiliaryQuotient_mk (a : A) :
    linearMapOnAuxiliaryQuotient k A V (Submodule.Quotient.mk a) =
      moduleDualElement k A V a :=
  rfl

end RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliaryLinearMap_mul_comm

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliarySubmodule

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := primary)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliarySubmodule_le_ker

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := primary)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.linearMapOnAuxiliaryQuotient

attribute [source_ref "Chapter3/Theorem3.6.2" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.linearMapOnAuxiliaryQuotient

attribute [source_ref "Chapter3/Introduction_to_3.6" (role := supporting)] _root_.RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.linearMapOnAuxiliaryQuotient_mk
