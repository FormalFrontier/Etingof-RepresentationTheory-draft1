/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import RepresentationTheory.Alignment.Attribute

/-!
# Integer-indexed cochain complexes

This module defines integer-indexed cochain complexes and their degreewise constructions
and properties.
-/

open CategoryTheory

namespace RepresentationTheory.CochainComplex

/-- The type of integer-indexed cochain complexes in a category with zero morphisms. -/
@[source_ref "Chapter7/Introduction_7.8" (role := supporting),
  source_ref "Chapter7/Definition7.8.1" (role := supporting)]
abbrev IntIndexed (C : Type*) [Category C] [Limits.HasZeroMorphisms C] :=
  _root_.CochainComplex C ℤ

namespace IntIndexed

/-- The morphism from the component in one degree to the component in the succeeding degree. -/
@[source_ref "Chapter7/Definition7.8.1" (role := supporting)]
abbrev nextDifferential {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : IntIndexed C) (i : ℤ) : K.X i ⟶ K.X (i + 1) := K.d i (i + 1)

/-- An object assigned to an integer degree of a cochain complex in an abelian category. -/
@[source_ref "Chapter7/Introduction_7.8" (role := supporting),
  source_ref "Chapter7/Definition7.8.1" (role := supporting)]
noncomputable abbrev degreeObject {C : Type*} [Category C] [Abelian C]
    (K : IntIndexed C) (i : ℤ) := K.homology i

/-- A property of an integer-indexed cochain complex at a specified degree. -/
@[source_ref "Chapter7/Definition7.8.1" (role := supporting)]
abbrev degreeProperty {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : IntIndexed C) (i : ℤ) : Prop := K.ExactAt i

/-- A property of an integer-indexed cochain complex. -/
@[source_ref "Chapter7/Definition7.8.1" (role := supporting)]
abbrev property {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : IntIndexed C) : Prop := K.Acyclic

end IntIndexed

end RepresentationTheory.CochainComplex
