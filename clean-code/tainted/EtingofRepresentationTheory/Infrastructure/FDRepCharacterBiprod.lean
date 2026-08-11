/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import Mathlib

/-!
# Character additivity over binary biproducts in `FDRep ℂ G`

A binary biproduct `X ⊞ Y` in `FDRep ℂ G` carries the direct-sum representation, so its
character is the sum of the characters of `X` and `Y`. This file isolates that fact, together
with the two ingredients it needs: the underlying-linear-map intertwining property of an
`FDRep` morphism, and the `ℂ`-linear equivalence `X ⊞ Y ≃ₗ X × Y` given by the two projections.

Used wherever a decomposition `V ≅ X ⊞ Y` is turned into a character identity (Chapter 5's
induced-representation decompositions, and the `GL₂(𝔽_q)` principal series).
-/

open CategoryTheory CategoryTheory.Limits

/-- Underlying-linear-map intertwining for a morphism of `FDRep`: the underlying `ℂ`-linear map
of `f : A ⟶ B` commutes with the `G`-actions. -/
lemma fdrep_hom_comm {G : Type} [Group G] {A B : FDRep ℂ G} (f : A ⟶ B) (g : G) (a : (A : Type)) :
    f.hom.hom.hom (A.ρ g a) = B.ρ g (f.hom.hom.hom a) := by
  have h := f.comm g
  apply_fun (fun m : A.V ⟶ B.V => m.hom.hom) at h
  have h2 := congrFun (congrArg (fun (m : (A.V.obj) →ₗ[ℂ] (B.V.obj)) => (m : _ → _)) h) a
  simpa using h2

/-- The `ℂ`-linear equivalence underlying a binary biproduct in `FDRep ℂ G`, sending `v` to its
two projections. -/
noncomputable def biprodProdEquiv {G : Type} [Group G] (X Y : FDRep ℂ G) :
    (X ⊞ Y : FDRep ℂ G) ≃ₗ[ℂ] Prod (X : Type) (Y : Type) where
  toFun v := ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
              (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
  map_add' a b := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' r a := Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  invFun p := (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
              (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
  left_inv v := by
    change ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
      (X ⊞ Y : FDRep ℂ G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
    rw [biprod.total]; rfl
  right_inv p := by
    have hzero : ∀ (A B : FDRep ℂ G) (x : (A : Type)), (0 : A ⟶ B).hom.hom.hom x = 0 := by
      intro A B x
      change (0 : A.V.obj ⟶ B.V.obj).hom x = 0
      simp [ModuleCat.Hom.hom]
    have hid : ∀ (A : FDRep ℂ G) (x : (A : Type)), (𝟙 A : A ⟶ A).hom.hom.hom x = x :=
      fun _ _ => rfl
    ext <;> dsimp only
    · change ((biprod.fst : X ⊞ Y ⟶ X)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.1
      rw [map_add]
      change ((biprod.inl ≫ biprod.fst : X ⟶ X)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.fst : Y ⟶ X)).hom.hom.hom p.2 = p.1
      rw [biprod.inl_fst, biprod.inr_fst, hid, hzero, add_zero]
    · change ((biprod.snd : X ⊞ Y ⟶ Y)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.2
      rw [map_add]
      change ((biprod.inl ≫ biprod.snd : X ⟶ Y)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.snd : Y ⟶ Y)).hom.hom.hom p.2 = p.2
      rw [biprod.inl_snd, biprod.inr_snd, hzero, hid, zero_add]

/-- **Character additivity over a binary biproduct** in `FDRep ℂ G`:
`(X ⊞ Y).character = X.character + Y.character`. -/
lemma character_biprod {G : Type} [Group G] (X Y : FDRep ℂ G) (g : G) :
    (X ⊞ Y).character g = X.character g + Y.character g := by
  have hequiv : ∀ v, (biprodProdEquiv X Y) ((X ⊞ Y).ρ g v)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) ((biprodProdEquiv X Y) v) := by
    intro v
    apply Prod.ext
    · change (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom ((X ⊞ Y).ρ g v)
        = X.ρ g ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v)
      exact fdrep_hom_comm (biprod.fst : X ⊞ Y ⟶ X) g v
    · change (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom ((X ⊞ Y).ρ g v)
        = Y.ρ g ((biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
      exact fdrep_hom_comm (biprod.snd : X ⊞ Y ⟶ Y) g v
  have hconj : (biprodProdEquiv X Y).conj ((X ⊞ Y).ρ g)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have hv := hequiv ((biprodProdEquiv X Y).symm w)
    rw [LinearEquiv.apply_symm_apply] at hv
    simpa using hv
  calc (X ⊞ Y).character g
      = LinearMap.trace ℂ _ ((X ⊞ Y).ρ g) := rfl
    _ = LinearMap.trace ℂ _ ((biprodProdEquiv X Y).conj ((X ⊞ Y).ρ g)) :=
        (LinearMap.trace_conj' _ _).symm
    _ = LinearMap.trace ℂ _ (LinearMap.prodMap (X.ρ g) (Y.ρ g)) := by rw [hconj]
    _ = X.character g + Y.character g := LinearMap.trace_prodMap' _ _
