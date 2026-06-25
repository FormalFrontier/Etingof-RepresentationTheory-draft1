import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Length
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Existence of the indecomposable decomposition (Krull–Schmidt, link 2/5)

This file proves the **existence** half of the Krull–Schmidt theorem for a finite abelian
category `C`: every object `X` is a finite biproduct of indecomposable objects
(`Etingof.exists_indecomposable_biproduct`), together with a projective-preserving variant
(`Etingof.exists_indecomposable_projective_biproduct`) consumed by the §9.7 projective-generator
classification.

## Proof outline

The argument is a strong induction on the composition length `Etingof.clength X` from
`KrullSchmidt/Length.lean`:

* `clength X = 0` (equivalently `IsZero X`): take the empty family — `⨁` over `Empty` is a zero
  object, isomorphic to `X`.
* `Indecomposable X`: take the one-element family `fun _ : PUnit => X`.
* otherwise `X ≅ Y ⊞ Z` with both `Y`, `Z` nonzero; `clength_biprod` and
  `clength_pos_of_not_isZero` give `clength Y, clength Z < clength X`, so the inductive hypothesis
  decomposes each, and the two finite families are concatenated over `κ_Y ⊕ κ_Z` via the
  biproduct-of-a-sum isomorphism `biproductSumIso`.

The projective variant reuses the same family: each summand `f k` is a retract of `X` (through
the biproduct inclusion/projection), and a retract of a projective is projective
(`CategoryTheory.Retract.projective`).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

-- An abelian category has finite biproducts; Mathlib keeps this as a local instance only
-- (a global instance breaks unrelated `ModuleCat` files), so we re-activate it here.
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

/-- Composition length is an isomorphism invariant: an iso `X ≅ Y` of objects induces an order
isomorphism of subobject lattices, and `Order.height` (hence `clength`) is preserved by order
isomorphisms. -/
theorem clength_eq_of_iso {X Y : C} (e : X ≅ Y) : clength X = clength Y := by
  unfold clength
  rw [← Order.height_orderIso (Subobject.mapIsoToOrderIso e) (⊤ : Subobject X),
    (Subobject.mapIsoToOrderIso e).map_top]

section BiproductSum

variable {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]

/-- The biproduct of a family indexed by a sum type `κ₁ ⊕ κ₂` is the binary biproduct of the two
biproducts over `κ₁` and `κ₂`. This is the reindexing step that concatenates two finite
indecomposable decompositions in the Krull–Schmidt existence induction. -/
noncomputable def biproductSumIso (f₁ : κ₁ → C) (f₂ : κ₂ → C) :
    (⨁ f₁) ⊞ (⨁ f₂) ≅ ⨁ (Sum.elim f₁ f₂) where
  hom := biprod.desc
    (biproduct.desc fun a => biproduct.ι (Sum.elim f₁ f₂) (Sum.inl a))
    (biproduct.desc fun b => biproduct.ι (Sum.elim f₁ f₂) (Sum.inr b))
  inv := biproduct.desc fun k => match k with
    | Sum.inl a => biproduct.ι f₁ a ≫ biprod.inl
    | Sum.inr b => biproduct.ι f₂ b ≫ biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> rintro j <;> simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro (a | b) <;> simp

end BiproductSum

/-- **Existence half of Krull–Schmidt.** Every object of a finite abelian category is a finite
biproduct of indecomposable objects. Proved by strong induction on `clength X`. -/
theorem exists_indecomposable_biproduct (X : C) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
      (∀ k, CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
  -- Strong induction on the composition length.
  have key : ∀ n, ∀ X : C, clength X = n →
      ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
        (∀ k, CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hX
      by_cases hzero : IsZero X
      · -- Zero object: the empty family.
        refine ⟨Empty, inferInstance, Empty.elim, fun k => k.elim, ⟨?_⟩⟩
        have hbip : IsZero (⨁ (Empty.elim : Empty → C)) := by
          refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
          · exact biproduct.hom_ext' _ _ fun j => j.elim
          · exact biproduct.hom_ext _ _ fun j => j.elim
        exact hzero.iso hbip
      · by_cases hindec : CategoryTheory.Indecomposable X
        · -- Indecomposable: the one-element family.
          exact ⟨PUnit, inferInstance, fun _ => X, fun _ => hindec,
            ⟨(biproductUniqueIso (fun _ : PUnit => X)).symm⟩⟩
        · -- Decomposable and nonzero: split and recurse.
          have hsplit : ¬ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z :=
            fun hall => hindec ⟨hzero, hall⟩
          push Not at hsplit
          obtain ⟨Y, Z, hiso, hY, hZ⟩ := hsplit
          have hsum : clength X = clength Y + clength Z := by
            rw [clength_eq_of_iso hiso, clength_biprod]
          have hzposY := clength_pos_of_not_isZero hY
          have hzposZ := clength_pos_of_not_isZero hZ
          have hltY : clength Y < n := by omega
          have hltZ : clength Z < n := by omega
          obtain ⟨κY, finY, fY, hindecY, ⟨eY⟩⟩ := ih (clength Y) hltY Y rfl
          obtain ⟨κZ, finZ, fZ, hindecZ, ⟨eZ⟩⟩ := ih (clength Z) hltZ Z rfl
          haveI := finY
          haveI := finZ
          refine ⟨κY ⊕ κZ, inferInstance, Sum.elim fY fZ, ?_, ⟨?_⟩⟩
          · rintro (a | b)
            · exact hindecY a
            · exact hindecZ b
          · exact hiso ≪≫ biprod.mapIso eY eZ ≪≫ biproductSumIso fY fZ
  exact key (clength X) X rfl

/-- **Projective-preserving existence.** A projective object of a finite abelian category is a
finite biproduct of projective indecomposable objects. Used by the §9.7 assembly. -/
theorem exists_indecomposable_projective_biproduct {X : C} (hX : Projective X) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
      (∀ k, Projective (f k) ∧ CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
  obtain ⟨κ, fin, f, hindec, ⟨e⟩⟩ := exists_indecomposable_biproduct X
  haveI := fin
  refine ⟨κ, fin, f, fun k => ⟨?_, hindec k⟩, ⟨e⟩⟩
  -- `f k` is a retract of `X`, hence projective.
  haveI : Projective X := hX
  exact Retract.projective
    { i := biproduct.ι f k ≫ e.inv
      r := e.hom ≫ biproduct.π f k
      retract := by simp }

end Etingof
