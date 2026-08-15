/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import RepresentationTheory.Alignment.Attribute

open CategoryTheory Limits

namespace RepresentationTheory.Algebra.Homology.LinearYoneda

universe u

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]

/-- The degree-n k-module represented by linear Yoneda homology for two A-module objects. -/
noncomputable def ModuleCat.linearYonedaHomology (M N : ModuleCat.{u} A) (n : ℕ) :
    ModuleCat.{u} k :=
  ((_root_.Ext k (ModuleCat.{u} A) n).obj (Opposite.op M)).obj N

/-- An isomorphism from the degree-n linear Yoneda homology object to the homology of the linear
Yoneda complex obtained from a projective resolution of the first A-module and the second
A-module. -/
@[source_ref "Chapter8/Definition8.2.4" (role := primary)]
noncomputable def ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution
    (M N : ModuleCat.{u} A) (P : ProjectiveResolution M) (n : ℕ) :
    ModuleCat.linearYonedaHomology k A M N n ≅
      (P.complex.linearYonedaObj k N).homology n :=
  P.isoExt n N

end RepresentationTheory.Algebra.Homology.LinearYoneda
