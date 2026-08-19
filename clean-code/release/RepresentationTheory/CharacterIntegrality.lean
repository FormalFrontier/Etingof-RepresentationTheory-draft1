/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For a finite simple complex representation of positive dimension, the character value scaled by the conjugacy class size and divided by the dimension is integral over the integers. -/
@[source_ref "Chapter5/Theorem5.3.1" (role := supporting),
  source_ref "Chapter5/Proposition5.3.2" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.3.1" (role := supporting)]
theorem RepresentationTheory.CharacterIntegrality.isIntegral_card_conjClass_mul_character_div_finrank
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    IsIntegral ℤ ((Fintype.card { h : G // IsConj g h } : ℂ) * V.character g /
      (Module.finrank ℂ V : ℂ)) := by
  set C := Fintype.card { h : G // IsConj g h }
  set d := Module.finrank ℂ V
  set σ := ∑ h : { h : G // IsConj g h }, V.ρ (h : G) with hσ_def
  have ⟨c, hc⟩ : ∃ c : ℂ, σ = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj) := by
    have hσ_comm : ∀ a : G, σ.comp (V.ρ a) = (V.ρ a).comp σ := by
      intro a
      ext v
      simp only [hσ_def, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [map_sum]
      simp_rw [← Module.End.mul_apply, ← map_mul]
      let e : { h : G // IsConj g h } ≃ { h : G // IsConj g h } :=
        { toFun := fun ⟨h, hh⟩ => ⟨a⁻¹ * h * a, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a⁻¹ * k, by group⟩⟩
          invFun := fun ⟨h, hh⟩ => ⟨a * h * a⁻¹, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a * k, by group⟩⟩
          left_inv := fun ⟨h, _⟩ => by ext; simp; group
          right_inv := fun ⟨h, _⟩ => by ext; simp; group }
      exact Fintype.sum_equiv e _ _ (fun x => by
        dsimp [e]; congr 1; group)
    have hrank : Module.finrank ℂ (V ⟶ V) = 1 := by
      rw [FDRep.finrank_hom_simple_simple V V, if_pos ⟨Iso.refl V⟩]
    have hid_ne : (𝟙 V : V ⟶ V) ≠ 0 := by
      intro h
      apply id_nonzero V
      exact_mod_cast h
    let σ_hom : V ⟶ V :=
      { hom := FGModuleCat.ofHom σ
        comm := fun g => by
          ext v
          exact congr_fun (congr_arg DFunLike.coe (hσ_comm g)) v }
    obtain ⟨c, hc_eq⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 V) hid_ne).mp hrank σ_hom
    refine ⟨c, ?_⟩
    have h1 : σ_hom.hom = (c • 𝟙 V).hom := congr_arg Action.Hom.hom hc_eq.symm
    have h2 := congr_arg (fun f : V.V ⟶ V.V => InducedCategory.Hom.hom f |>.hom) h1
    apply LinearMap.ext
    intro v
    have := congr_arg (fun f : V.V.obj →ₗ[ℂ] V.V.obj => f v) h2
    exact this
  have hc_val : c = (C : ℂ) * V.character g / (d : ℂ) := by
    have hdim_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ht1 : LinearMap.trace ℂ V.V.obj σ = (C : ℂ) * V.character g := by
      simp only [hσ_def, map_sum]
      have : ∀ h : { h : G // IsConj g h },
          (LinearMap.trace ℂ V.V.obj) (V.ρ (h : G)) = V.character g := by
        intro ⟨h, hh⟩
        change V.character h = V.character g
        obtain ⟨c, rfl⟩ := isConj_iff.mp hh
        exact V.char_conj g c
      simp_rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
    rw [hc] at ht1
    simp only [map_smul, LinearMap.trace_id, smul_eq_mul] at ht1
    have hd_eq : (Module.finrank ℂ (V.V.obj) : ℂ) = (d : ℂ) := by rfl
    rw [hd_eq] at ht1
    exact eq_div_of_mul_eq hdim_ne ht1
  rw [← hc_val]
  set e : MonoidAlgebra ℤ G := ∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h
  have he : IsIntegral ℤ e := IsIntegral.of_finite ℤ e
  let φ : MonoidAlgebra ℤ G →+* Module.End ℂ V.V.obj :=
    ((Representation.asAlgebraHom V.ρ).toRingHom).comp
      (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))
  have hφe : φ e = c • LinearMap.id := by
    have hφ_of : ∀ h : G, φ (MonoidAlgebra.of ℤ G h) = V.ρ h := by
      intro h; simp [φ]
    change φ (∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h) = c • LinearMap.id
    rw [map_sum]; simp_rw [hφ_of]; exact hc
  have hφe_int : IsIntegral ℤ (φ e) := he.map φ.toIntAlgHom
  rw [hφe] at hφe_int
  haveI : Nontrivial V.V.obj := Module.nontrivial_of_finrank_pos hn
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V.V.obj))
    (FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V.V.obj))).mp
    (by convert hφe_int using 2; simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id])
