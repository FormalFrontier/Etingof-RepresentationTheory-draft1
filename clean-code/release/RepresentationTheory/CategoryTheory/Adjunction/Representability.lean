/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Adjunction representability

This module records the representability consequences of an adjunction.
-/

open CategoryTheory Opposite

namespace RepresentationTheory.CategoryTheory.Adjunction.Representability

variable {C : Type*} {D : Type*} [Category C] [Category D]
variable {F : Functor C D} {G : Functor D C}

/-- The composite of a right adjoint with the covariant hom functor at an object is corepresented by the image of that object under the left adjoint. -/
@[source_ref "Chapter7/Discussion_after_Definition7.6.1" (role := supporting)]
noncomputable def corepresentableBy (adj : F ⊣ G) (X : C) :
    (G ⋙ coyoneda.obj (op X)).CorepresentableBy (F.obj X) :=
  adj.corepresentableBy X

/-- The composite of the opposite left adjoint with the contravariant hom functor at an object is represented by the image of that object under the right adjoint. -/
@[source_ref "Chapter7/Discussion_after_Definition7.6.1" (role := supporting)]
noncomputable def representableBy (adj : F ⊣ G) (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) :=
  adj.representableBy Y

end RepresentationTheory.CategoryTheory.Adjunction.Representability
