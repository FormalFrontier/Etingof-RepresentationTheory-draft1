/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
import RepresentationTheory.Alignment.Attribute

open scoped MonoidAlgebra Matrix Kronecker TensorProduct
open Representation

namespace RepresentationTheory.Representation.Character.AuxiliaryVanishing

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

private lemma matrix_trace_swap_kronecker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (((1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix Prod.swap _root_.id) * (A ⊗ₖ A)).trace
      = (A * A).trace := by
  have hdiag : ∀ p : ι × ι,
      (((1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix Prod.swap _root_.id) * (A ⊗ₖ A)) p p
        = (A ⊗ₖ A) (Prod.swap p) p := by
    intro p
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (Prod.swap p)]
    · simp [Matrix.submatrix_apply, Matrix.one_apply]
    · intro q _ hq
      rw [Matrix.submatrix_apply, Matrix.one_apply, if_neg (by simpa [eq_comm] using hq),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, hdiag, Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap,
    Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

private lemma trace_comm_comp_map (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (V ⊗[ℂ] V)
        ((TensorProduct.comm ℂ V V : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V) ∘ₗ TensorProduct.map A A)
      = LinearMap.trace ℂ V (A ∘ₗ A) := by
  classical
  let b := Module.finBasis ℂ V
  let bb := b.tensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ bb, LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.toMatrix_comp bb bb bb, LinearMap.toMatrix_comp b b b,
    TensorProduct.toMatrix_comm b b, TensorProduct.toMatrix_map b b b b]
  exact matrix_trace_swap_kronecker (LinearMap.toMatrix b b A)

private lemma trace_involution_eq_pm_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (h1 : Module.finrank ℂ W = 1)
    (g : W →ₗ[ℂ] W) (hg : g ∘ₗ g = LinearMap.id) :
    LinearMap.trace ℂ W g = 1 ∨ LinearMap.trace ℂ W g = -1 := by
  classical
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) ℂ W) :=
    ⟨(Module.finBasis ℂ W).reindex (finCongr h1)⟩
  set M := LinearMap.toMatrix b b g with hM
  have hM2 : M * M = 1 := by
    rw [hM, ← LinearMap.toMatrix_comp b b b, hg, LinearMap.toMatrix_id]
  have htr : LinearMap.trace ℂ W g = M 0 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_fin_one]
  have hsq : M 0 0 * M 0 0 = 1 := by
    have h := congrFun (congrFun hM2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply] using h
  rw [htr]
  exact mul_self_eq_one_iff.mp hsq

private lemma exists_involution_trace_eq_frobeniusSchur
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (ρ : Representation ℂ G V) :
    ∃ g₀ : (Representation.tprod ρ ρ).invariants →ₗ[ℂ] (Representation.tprod ρ ρ).invariants,
      g₀ ∘ₗ g₀ = LinearMap.id ∧
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ
        = LinearMap.trace ℂ (Representation.tprod ρ ρ).invariants g₀ := by
  classical
  haveI : Invertible (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]; infer_instance
  set T : Representation ℂ G (V ⊗[ℂ] V) := Representation.tprod ρ ρ with hT
  set cm : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V :=
    (TensorProduct.comm ℂ V V : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V) with hcm
  have hequiv : ∀ g, cm ∘ₗ T g = T g ∘ₗ cm := by
    intro g
    rw [hcm, hT, Representation.tprod_apply]
    apply TensorProduct.ext'
    intro x y
    simp [TensorProduct.map_tmul]
  have hcm2 : cm ∘ₗ cm = LinearMap.id := by
    rw [hcm]; apply TensorProduct.ext'; intro x y; simp
  have hpres : ∀ x ∈ T.invariants, cm x ∈ T.invariants := by
    intro x hx
    rw [Representation.mem_invariants]
    intro g
    have key : (T g ∘ₗ cm) x = (cm ∘ₗ T g) x := by rw [hequiv]
    have hxg : T g x = x := hx g
    simpa [hxg] using key
  have hP : T.averageMap = ⅟(Fintype.card G : ℂ) • ∑ g : G, T g := by
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of]
  have hdist : cm ∘ₗ (∑ g : G, T g) = ∑ g : G, cm ∘ₗ T g := by
    ext z
    simp [LinearMap.sum_apply, map_sum]
  have hterm : ∀ g : G, LinearMap.trace ℂ V (ρ (g * g))
      = LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T g) := by
    intro g
    rw [hcm, hT, Representation.tprod_apply, trace_comm_comp_map,
      show ρ (g * g) = ρ g ∘ₗ ρ g by rw [map_mul]; rfl]
  have hFS : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ
      = LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T.averageMap) := by
    have hR : LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T.averageMap)
        = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T g) := by
      rw [hP, LinearMap.comp_smul, hdist]
      simp only [map_smul, map_sum, smul_eq_mul, invOf_eq_inv]
    rw [hR, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar]
    exact congrArg (fun s => (Fintype.card G : ℂ)⁻¹ * s)
      (Finset.sum_congr rfl (fun g _ => hterm g))
  have hmaps : ∀ x, (cm ∘ₗ T.averageMap) x ∈ T.invariants := by
    intro x
    exact hpres _ (T.averageMap_invariant x)
  have hmaps' : ∀ x ∈ T.invariants, (cm ∘ₗ T.averageMap) x ∈ T.invariants :=
    fun x _ => hmaps x
  have htr := LinearMap.trace_restrict_eq_of_forall_mem T.invariants
    (cm ∘ₗ T.averageMap) hmaps hmaps'
  set g₀ := (cm ∘ₗ T.averageMap).restrict hmaps' with hg₀
  have hg₀sq : g₀ ∘ₗ g₀ = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : (x : V ⊗[ℂ] V) ∈ T.invariants := x.2
    have e1 : (g₀ x : V ⊗[ℂ] V) = cm x := by
      change (cm ∘ₗ T.averageMap) (x : V ⊗[ℂ] V) = cm x
      rw [LinearMap.comp_apply, T.averageMap_id _ hx]
    have hcmx : cm (x : V ⊗[ℂ] V) ∈ T.invariants := hpres _ hx
    have e2 : (g₀ (g₀ x) : V ⊗[ℂ] V) = (x : V ⊗[ℂ] V) := by
      change (cm ∘ₗ T.averageMap) ((g₀ x : V ⊗[ℂ] V)) = (x : V ⊗[ℂ] V)
      rw [e1, LinearMap.comp_apply, T.averageMap_id _ hcmx]
      have hinv := LinearMap.congr_fun hcm2 (x : V ⊗[ℂ] V)
      simpa using hinv
    rw [LinearMap.comp_apply, e2]
    simp
  exact ⟨g₀, hg₀sq, hFS.trans htr.symm⟩

/-- Auxiliary declaration whose formal type could not be displayed. -/
@[source_ref "Chapter5/Theorem5.1.5" (role := supporting)]
theorem auxiliaryStatement
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∀ g, ρ.character g⁻¹ = ρ.character g) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 ∨ RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = -1 := by
  classical
  haveI : Invertible (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]; infer_instance
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  obtain ⟨g₀, hg₀sq, hfs⟩ := exists_involution_trace_eq_frobeniusSchur ρ
  have hdim : Module.finrank ℂ ((Representation.tprod ρ ρ).invariants) = 1 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.tprod ρ ρ)
    have hortho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
    have hchar : ∀ g, (Representation.tprod ρ ρ).character g = ρ.character g * ρ.character g := by
      intro g; rw [Representation.char_tensor]; rfl
    have hsum : (Nat.card G : ℂ)⁻¹ * ∑ g : G, (Representation.tprod ρ ρ).character g = 1 := by
      rw [Finset.sum_congr rfl (fun g _ => hchar g)]
      rw [show (∑ g : G, ρ.character g * ρ.character g)
            = ∑ g : G, ρ.character g * ρ.character g⁻¹ from
          Finset.sum_congr rfl (fun g _ => by rw [hsd g])]
      exact hortho
    rw [hkey] at hsum
    exact_mod_cast hsum
  rw [hfs]
  exact trace_involution_eq_pm_one hdim g₀ hg₀sq

/-- For a simple complex representation whose character is not invariant under inversion, an associated auxiliary value vanishes. -/
@[source_ref "Chapter5/Theorem5.1.5" (role := supporting)]
theorem auxiliaryValue_eq_zero_of_character_not_inversionInvariant
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnsd : ¬ ∀ g, ρ.character g⁻¹ = ρ.character g) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 0 := by
  classical
  haveI : Invertible (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]; infer_instance
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  obtain ⟨g₀, _, hfs⟩ := exists_involution_trace_eq_frobeniusSchur ρ
  have hempty : IsEmpty (ρ.Equiv ρ.dual) := by
    rw [isEmpty_iff]
    intro φ
    refine hnsd (fun g => ?_)
    have hc := congrFun (Representation.char_iso φ) g
    rw [Representation.char_dual] at hc
    exact hc.symm
  haveI hsub : Subsingleton (Representation.IntertwiningMap ρ ρ.dual) := by
    refine ⟨fun f h => ?_⟩
    suffices hz : ∀ e : Representation.IntertwiningMap ρ ρ.dual, e = 0 by rw [hz f, hz h]
    intro e
    rcases Representation.IsIrreducible.injective_or_eq_zero e with hinj | h0
    · exfalso
      have hdimeq : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) :=
        (Subspace.dual_finrank_eq).symm
      have hsurj : Function.Surjective ⇑e :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq
          (f := e.toLinearMap)).mp hinj
      exact hempty.false (e.ofBijective ⟨hinj, hsurj⟩)
    · exact h0
  have hdim : Module.finrank ℂ ((Representation.tprod ρ ρ).invariants) = 0 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.tprod ρ ρ)
    have hInt := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ.dual
    have hsum : (∑ g : G, (Representation.tprod ρ ρ).character g)
        = ∑ g : G, ρ.dual.character g * ρ.character g⁻¹ := by
      rw [Finset.sum_congr rfl
            (fun g _ => by rw [Representation.char_tensor, Pi.mul_apply] :
              ∀ g ∈ Finset.univ, (Representation.tprod ρ ρ).character g
                = ρ.character g * ρ.character g),
          Finset.sum_congr rfl
            (fun g _ => by rw [Representation.char_dual] :
              ∀ g ∈ Finset.univ, ρ.dual.character g * ρ.character g⁻¹
                = ρ.character g⁻¹ * ρ.character g⁻¹)]
      exact (Equiv.sum_comp (Equiv.inv G) (fun g => ρ.character g * ρ.character g)).symm
    rw [hsum, hInt] at hkey
    have hInt0 : Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) = 0 :=
      (finrank_zero_iff_forall_zero (K := ℂ)).mpr fun x => Subsingleton.elim x 0
    rw [hInt0] at hkey
    exact_mod_cast hkey.symm
  haveI : Subsingleton ((Representation.tprod ρ ρ).invariants) :=
    ⟨fun a b => ((finrank_zero_iff_forall_zero (K := ℂ)).mp hdim a).trans
      ((finrank_zero_iff_forall_zero (K := ℂ)).mp hdim b).symm⟩
  rw [hfs, Subsingleton.elim g₀ 0, map_zero]

end RepresentationTheory.Representation.Character.AuxiliaryVanishing
