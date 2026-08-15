/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.FGModuleCat.Basic
import RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory
import RepresentationTheory.Alignment.Attribute

/-!
# Linear and abelian module categories

This module records linear and abelian category structures for modules over an algebra.
-/

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.ModuleCategories

/-- The category of modules over an algebra is linear over its base field. -/
@[reducible, source_ref "Chapter7/Discussion_after_Remark7.7.4" (role := primary)]
def moduleCatLinear (k : Type*) [Field k] (A : Type*) [Ring A]
    [Algebra k A] :
    Linear k (ModuleCat A) := inferInstance

/-- The category of modules over a ring is abelian. -/
@[reducible, source_ref "Chapter7/Discussion_after_Remark7.7.4" (role := primary)]
noncomputable def moduleCatAbelian (A : Type*) [Ring A] :
    Abelian (ModuleCat A) := inferInstance

/-- Finitely generated modules over a finite-dimensional algebra over a field form a linear category over that field. -/
@[reducible, source_ref "Chapter7/Discussion_after_Remark7.7.4" (role := primary)]
def fgModuleCatLinear (k : Type*) [Field k] (A : Type*) [Ring A]
    [Algebra k A]
    [FiniteDimensional k A] : Linear k (FGModuleCat A) := inferInstance

/-- The category of finitely generated modules over a finite-dimensional algebra over a field is abelian. -/
@[reducible, source_ref "Chapter7/Discussion_after_Remark7.7.4" (role := primary)]
noncomputable def fgModuleCatAbelian (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] [FiniteDimensional k A] : Abelian (FGModuleCat A) :=
  RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory.FGModuleCat.instAbelian_of_finiteDimensional k A

end RepresentationTheory.CategoryTheory.ModuleCategories
