/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Polynomials indexed by finite groups -/

namespace RepresentationTheory.Group.IndexedPolynomial

/-- A multivariate polynomial whose variables are indexed by the elements of a finite group. -/
@[source_ref "Chapter4/Definition4.10.1" (role := supporting),
  source_ref "Chapter4/Introduction_4.10" (role := supporting)]
noncomputable def groupIndexedPolynomial
    (k : Type*) (G : Type*) [CommRing k] [Group G] [Fintype G] [DecidableEq G] :
    MvPolynomial G k :=
  Matrix.det (Matrix.of fun (g h : G) => (MvPolynomial.X (g * h) : MvPolynomial G k))

end RepresentationTheory.Group.IndexedPolynomial
