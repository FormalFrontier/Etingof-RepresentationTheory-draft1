/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.PolynomialQuotientEmbeddings
import RepresentationTheory.Submodules

noncomputable section

namespace RepresentationTheory.PolynomialRepresentation.Subrepresentation

open MvPolynomial
open RepresentationTheory.GeneralLinear.PolynomialQuotientEmbeddings
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.Submodules
open RepresentationTheory.SymmetricPolynomials.Alternant

variable {k : Type} [Field k] {N : ℕ}

/-- A non-bottom subrepresentation contains a nonzero vector in a displayed indexed submodule
whose index has a negative coordinate. -/
theorem exists_negative_coordinate_of_ne_bot (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    (W : Subrepresentation (naturalIndexedQuotientRepresentation k N r)) (hW : W ≠ ⊥) :
    ∃ μ : Fin N → ℤ, (∃ i, μ i < 0) ∧
      ∃ v ∈ W.toSubmodule, v ≠ 0 ∧
        v ∈ integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r) μ := by
  classical
  have hW₀ne : W.toSubmodule ≠ ⊥ := by
    intro h
    exact hW (Subrepresentation.toSubmodule_injective h)
  have hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W.toSubmodule,
        matrixPolynomialQuotientRepresentation k N g w ∈ W.toSubmodule := by
    intro g w hw
    set c : kˣ := (generalLinearGroupToUnits k N ^ (-(r : ℤ))) g with hc
    have htwist : naturalIndexedQuotientRepresentation k N r g w =
        (c : k) • matrixPolynomialQuotientRepresentation k N g w := rfl
    have hmem : naturalIndexedQuotientRepresentation k N r g w ∈ W.toSubmodule :=
      W.apply_mem_toSubmodule g hw
    have hcc1 : ((c⁻¹ : kˣ) : k) * ((c : k)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have : matrixPolynomialQuotientRepresentation k N g w =
        ((c⁻¹ : kˣ) : k) • naturalIndexedQuotientRepresentation k N r g w := by
      rw [htwist, smul_smul, hcc1, one_smul]
    rw [this]
    exact W.toSubmodule.smul_mem _ hmem
  obtain ⟨L, φ, hLsimp, hφ_inj, hφ_equiv, hφ_range⟩ :=
    exists_isSimpleModule_embedding_of_nonzero_submodule k N hW_inv hW₀ne
  obtain ⟨ν, hν_anti, hν_zero, hν_char⟩ :=
    exists_auxiliary_antitone_with_zero_of_equivariant_embedding
      k N L hLsimp φ hφ_inj hφ_equiv
  obtain ⟨i₀, hi₀⟩ := hν_zero
  have hcoeff :
      (partitionPolynomial N ν).coeff (Finsupp.equivFunOnFinite.symm ν) ≠ 0 :=
    coeff_partitionPolynomial_ne_zero N ν hν_anti
  have hfin_ne : Module.finrank k
      (weightSpace k N L (fun i => (Finsupp.equivFunOnFinite.symm ν) i)) ≠ 0 := by
    have hcc := coeff_weightCharacter k N L (Finsupp.equivFunOnFinite.symm ν)
    rw [hν_char] at hcc
    intro h
    rw [h] at hcc
    simp only [Nat.cast_zero] at hcc
    exact hcoeff hcc
  have hfun : (fun i => (Finsupp.equivFunOnFinite.symm ν) i) = ν := rfl
  rw [hfun] at hfin_ne
  have hws_ne : weightSpace k N L ν ≠ ⊥ := by
    intro h
    apply hfin_ne
    rw [h]
    simp
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp hws_ne
  have hw_wt : ∀ (i : Fin N) (t : kˣ),
      L.ρ (diagonalUnit k N i t) w = ((t : k) ^ ν i) • w := by
    intro i t
    have hk : w ∈ LinearMap.ker
        (L.ρ (diagonalUnit k N i t) - ((t : k) ^ ν i) • LinearMap.id) :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hwmem i) t
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hk
    exact hk
  set v : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N := φ w with hv
  have hvmem : v ∈ W.toSubmodule := hφ_range ⟨w, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hv]
    intro hh
    exact hw0 (hφ_inj (hh.trans (map_zero φ).symm))
  have hv_wt : v ∈ integerTupleSubmodule k N (matrixPolynomialQuotientRepresentation k N)
      (fun i => (ν i : ℤ)) := by
    rw [integerTupleSubmodule]
    refine (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun t => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    have hcast : (((t ^ (ν i : ℤ) : kˣ) : k)) = (t : k) ^ ν i := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hcast, hv, ← hφ_equiv, hw_wt i t, map_smul]
  refine ⟨fun i => (ν i : ℤ) - r, ⟨i₀, by simp only [hi₀]; omega⟩, v, hvmem, hv0, ?_⟩
  rw [integerTupleSubmodule_naturalIndexedRepresentation k N r (fun i => (ν i : ℤ) - r)]
  have hshift : (fun i => (ν i : ℤ) - r + r) = (fun i => (ν i : ℤ)) := by
    funext i; ring
  rw [hshift]
  exact hv_wt

/-- A subrepresentation contained in the supremum of the displayed family of submodules is
bottom. -/
theorem subrepresentation_eq_bot_of_le_iSup (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    (W : Subrepresentation (naturalIndexedQuotientRepresentation k N r))
    (hW : W.toSubmodule ≤ ⨆ (μ : Fin N → ℕ),
      integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r)
        (fun i => (μ i : ℤ))) :
    W = ⊥ := by
  by_contra hne
  obtain ⟨μ, hμneg, v, hvW, hv0, hvμ⟩ :=
    exists_negative_coordinate_of_ne_bot k N r hr W hne
  exact integerTupleSubmodule_not_mem_iSup_natCast_of_exists_neg
    k N r μ hμneg hv0 hvμ (hW hvW)

/-- An invariant submodule of the quotient polynomial module that lies in the displayed supremum
is bottom. -/
theorem submodule_eq_bot_of_invariant_of_le_iSup
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    {W : Submodule k
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N)}
    (hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W, naturalIndexedQuotientRepresentation k N r g w ∈ W)
    (hW : W ≤ ⨆ (μ : Fin N → ℕ),
      integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r)
        (fun i => (μ i : ℤ))) :
    W = ⊥ := by
  let W' : Subrepresentation (naturalIndexedQuotientRepresentation k N r) :=
    ⟨W, fun g _ hw => hW_inv g _ hw⟩
  have hW'bot : W' = ⊥ := subrepresentation_eq_bot_of_le_iSup k N r hr W' hW
  have : W'.toSubmodule =
      (⊥ : Subrepresentation (naturalIndexedQuotientRepresentation k N r)).toSubmodule :=
    congrArg Subrepresentation.toSubmodule hW'bot
  exact this

end RepresentationTheory.PolynomialRepresentation.Subrepresentation

end
