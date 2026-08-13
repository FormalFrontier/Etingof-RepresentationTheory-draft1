/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Projectivity in finitely generated module categories
-/

open CategoryTheory Limits

namespace RepresentationTheory.FGModuleCat.Projectivity

universe u

variable (A : Type u) [Ring A]

/-- A functor from finitely generated modules over a ring to modules over the same ring. -/
abbrev toModuleCat : FGModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)

variable {A}

/-- A morphism of finitely generated modules is epic when its image under the functor to modules is epic. -/
theorem epi_of_toModuleCat_map_epi {X Y : FGModuleCat.{u} A} (φ : X ⟶ Y)
    (h : Epi ((toModuleCat A).map φ)) : Epi φ := by
  haveI := h
  constructor
  intro Z a b hab
  apply (toModuleCat A).map_injective
  have hcomp : (toModuleCat A).map φ ≫ (toModuleCat A).map a =
      (toModuleCat A).map φ ≫ (toModuleCat A).map b := by
    rw [← Functor.map_comp, ← Functor.map_comp, hab]
  exact (cancel_epi ((toModuleCat A).map φ)).mp hcomp

/-- A finitely generated module is projective if its image in the module category is projective. -/
theorem projective_of_toModuleCat_projective {P : FGModuleCat.{u} A}
    (h : Projective ((toModuleCat A).obj P)) : Projective P := by
  haveI := h
  constructor
  intro E X f e he
  haveI := he
  haveI : Epi ((toModuleCat A).map e) := inferInstance
  obtain ⟨g, hg⟩ := Projective.factors ((toModuleCat A).map f) ((toModuleCat A).map e)
  refine ⟨(toModuleCat A).preimage g, ?_⟩
  apply (toModuleCat A).map_injective
  rw [Functor.map_comp, (toModuleCat A).map_preimage, hg]

/-- The category of finitely generated modules over a Noetherian ring has enough projective objects. -/
instance enoughProjectives_of_isNoetherianRing [IsNoetherianRing A] :
    EnoughProjectives (FGModuleCat.{u} A) where
  presentation X := by
    obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' (R := A) (M := X)
    let φ : (toModuleCat A).obj (FGModuleCat.of A (Fin n → A)) ⟶
        (toModuleCat A).obj X := ModuleCat.ofHom l
    refine ⟨{ p := FGModuleCat.of A (Fin n → A)
              projective := projective_of_toModuleCat_projective (inferInstanceAs
                (Projective (ModuleCat.of A (Fin n → A))))
              f := (toModuleCat A).preimage φ
              epi := epi_of_toModuleCat_map_epi _ ?_ }⟩
    rw [(toModuleCat A).map_preimage]
    exact (ModuleCat.epi_iff_surjective φ).mpr hl

end RepresentationTheory.FGModuleCat.Projectivity
