import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# `FGModuleCat A` has enough projectives

For a left-Noetherian ring `A` (in particular a finite-dimensional `k`-algebra) the category
`FGModuleCat A` of finitely generated `A`-modules has enough projectives. This supplies the
`EnoughProjectives (FGModuleCat A)` field required by
`Etingof.IsFiniteAbelianCategory (FGModuleCat A)` (see issue #7424, sub-issue #7638).

The construction is the elementary one: every finitely generated `A`-module is a quotient of a
finitely generated free module `Aⁿ`, which is projective. The two supporting facts we prove are

* `FGModuleCat.projective_of_forget₂_projective`: projectivity transfers from `ModuleCat A` to the
  full subcategory `FGModuleCat A` along the (fully faithful, epimorphism-preserving) inclusion
  `forget₂ (FGModuleCat A) (ModuleCat A)`;
* `FGModuleCat.epi_of_forget₂_epi`: the inclusion, being faithful, reflects epimorphisms.

The inclusion preserves finite colimits (Mathlib), hence epimorphisms, and is fully faithful, which
is what makes both transfers go through.
-/

open CategoryTheory Limits

namespace FGModuleCat

universe u

variable (A : Type u) [Ring A]

/-- The full-subcategory inclusion `FGModuleCat A ⥤ ModuleCat A`, spelled out so we can use dot
notation for its functorial operations. -/
abbrev incl : FGModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)

variable {A}

/-- The inclusion `FGModuleCat A ⥤ ModuleCat A` reflects epimorphisms: if the underlying
`ModuleCat`-morphism of `φ` is an epimorphism, so is `φ`. (This is the general fact that faithful
functors reflect epimorphisms, spelled out for this inclusion.) -/
theorem epi_of_forget₂_epi {X Y : FGModuleCat.{u} A} (φ : X ⟶ Y)
    (h : Epi ((incl A).map φ)) : Epi φ := by
  haveI := h
  constructor
  intro Z a b hab
  apply (incl A).map_injective
  have hcomp : (incl A).map φ ≫ (incl A).map a = (incl A).map φ ≫ (incl A).map b := by
    rw [← Functor.map_comp, ← Functor.map_comp, hab]
  exact (cancel_epi ((incl A).map φ)).mp hcomp

/-- Projectivity transfers from `ModuleCat A` to `FGModuleCat A` along the inclusion: if the
underlying `ModuleCat`-object of `P` is projective, then `P` is projective in `FGModuleCat A`. -/
theorem projective_of_forget₂_projective {P : FGModuleCat.{u} A}
    (h : Projective ((incl A).obj P)) : Projective P := by
  haveI := h
  constructor
  intro E X f e he
  haveI := he
  -- The inclusion preserves epimorphisms, so `(incl A).map e` is again an epimorphism.
  haveI : Epi ((incl A).map e) := inferInstance
  obtain ⟨g, hg⟩ := Projective.factors ((incl A).map f) ((incl A).map e)
  refine ⟨(incl A).preimage g, ?_⟩
  apply (incl A).map_injective
  rw [Functor.map_comp, (incl A).map_preimage, hg]

/-- **`FGModuleCat A` has enough projectives** for a left-Noetherian ring `A`. Every finitely
generated `A`-module is a quotient of a finitely generated free module `Aⁿ`, which is projective. -/
instance enoughProjectives [IsNoetherianRing A] :
    EnoughProjectives (FGModuleCat.{u} A) where
  presentation X := by
    obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' (R := A) (M := X)
    -- The surjection `Aⁿ ↠ X`, viewed through the inclusion into `ModuleCat A`.
    let φ : (incl A).obj (FGModuleCat.of A (Fin n → A)) ⟶ (incl A).obj X := ModuleCat.ofHom l
    refine ⟨{ p := FGModuleCat.of A (Fin n → A)
              projective := projective_of_forget₂_projective (inferInstanceAs
                (Projective (ModuleCat.of A (Fin n → A))))
              f := (incl A).preimage φ
              epi := epi_of_forget₂_epi _ ?_ }⟩
    rw [(incl A).map_preimage]
    exact (ModuleCat.epi_iff_surjective φ).mpr hl

end FGModuleCat
