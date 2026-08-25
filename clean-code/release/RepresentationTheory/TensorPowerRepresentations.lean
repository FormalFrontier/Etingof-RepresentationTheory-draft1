/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.TensorPowerRepresentations

open scoped TensorProduct

set_option linter.unusedFintypeInType false

noncomputable section

variable {k : Type*} [CommRing k] {G : Type*} [Monoid G]
  {V : Type*} [AddCommGroup V] [Module k V]

/-- The representation induced on the nth tensor power of the representation space. -/
def tensorPowerRepresentation (ρ : Representation k G V) (n : ℕ) :
    Representation k G (⨂[k]^n V) where
  toFun g := PiTensorProduct.map (fun _ : Fin n => ρ g)
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_id
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp]
    rw [← PiTensorProduct.map_comp]

/-- The action of the tensor-power representation is the tensor-product map obtained by applying the original action in every factor. -/
@[simp]
theorem tensorPowerRepresentation_apply (ρ : Representation k G V) (n : ℕ) (g : G) :
    tensorPowerRepresentation ρ n g = PiTensorProduct.map (fun _ : Fin n => ρ g) := rfl

end

section TracePow

open Module

/-- The trace of the map induced by an endomorphism on an nth tensor power equals the nth power of the endomorphism's trace. -/
theorem trace_piTensorProduct_map
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (n : ℕ) (f : V →ₗ[k] V) :
    LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = (LinearMap.trace k V f) ^ n := by
  classical
  set D := Module.finrank k V with hD
  let b : Basis (Fin D) k V := Module.finBasis k V
  have key : LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = ∑ s : Fin n → Fin D, ∏ i : Fin n, (LinearMap.toMatrix b b f) (s i) (s i) := by
    rw [LinearMap.trace_eq_matrix_trace k (Basis.piTensorProduct (fun _ : Fin n => b)),
      Matrix.trace]
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
      PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply]
  rw [key]
  have htr : LinearMap.trace k V f = ∑ j : Fin D, (LinearMap.toMatrix b b f) j j := by
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diag_apply]
  rw [htr, Finset.sum_pow', Fintype.piFinset_univ]

/-- The character of the nth tensor-power representation at an element is the nth power of the original character value. -/
theorem character_tensorPowerRepresentation
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (n : ℕ) (g : G) :
    (tensorPowerRepresentation ρ n).character g = (ρ.character g) ^ n := by
  rw [Representation.character, tensorPowerRepresentation_apply, trace_piTensorProduct_map]
  rfl

end TracePow

open scoped Matrix in
private theorem eq_one_of_conjTranspose_mul_self_eq_one_of_trace_eq_card
    {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (htr : U.trace = (d : ℂ)) : U = 1 := by
  classical
  have hcol : ∀ i, ∑ k, Complex.normSq (U k i) = 1 := by
    intro i
    have hdiag : (Uᴴ * U) i i = 1 := by rw [hU, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at hdiag
    have hcast : (∑ k, (Complex.normSq (U k i) : ℂ)) = 1 := by
      rw [← hdiag]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_sum] at hcast
    exact_mod_cast hcast
  have hdiag_le : ∀ i, Complex.normSq (U i i) ≤ 1 := by
    intro i
    rw [← hcol i]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (U k i))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hre_le : ∀ i, (U i i).re ≤ 1 := by
    intro i
    have hn := hdiag_le i
    rw [Complex.normSq_apply] at hn
    nlinarith [mul_self_nonneg (U i i).im, mul_self_nonneg ((U i i).re - 1)]
  have hsum_re : ∑ i, (U i i).re = ∑ i : Fin d, (1 : ℝ) := by
    have htrace : U.trace = ∑ i, U i i := rfl
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← Complex.re_sum, ← htrace, htr, Complex.natCast_re]
  have hre_one : ∀ i, (U i i).re = 1 := by
    have hall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hre_le i)).1 hsum_re
    intro i; exact hall i (Finset.mem_univ i)
  have hdiag_one : ∀ i, U i i = 1 := by
    intro i
    have hn := hdiag_le i
    rw [Complex.normSq_apply, hre_one i] at hn
    have him : (U i i).im = 0 := by nlinarith [mul_self_nonneg (U i i).im]
    apply Complex.ext
    · rw [Complex.one_re]; exact hre_one i
    · rw [Complex.one_im]; exact him
  have hoff : ∀ i k, k ≠ i → U k i = 0 := by
    intro i k hk
    have hsplit : Complex.normSq (U i i) + ∑ k ∈ Finset.univ.erase i, Complex.normSq (U k i)
        = ∑ k, Complex.normSq (U k i) :=
      Finset.add_sum_erase Finset.univ (fun k => Complex.normSq (U k i)) (Finset.mem_univ i)
    rw [hcol i, hdiag_one i, Complex.normSq_one] at hsplit
    have hrest : ∑ k ∈ Finset.univ.erase i, Complex.normSq (U k i) = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).1 hrest
    exact Complex.normSq_eq_zero.mp (hall k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩))
  ext k i
  rcases eq_or_ne k i with rfl | hk
  · rw [hdiag_one k, Matrix.one_apply_eq]
  · rw [hoff i k hk, Matrix.one_apply_ne hk]

open scoped Matrix ComplexOrder MatrixOrder in
/-- If a group element has character value equal to the representation dimension, then its action in a finite-dimensional complex representation is the identity. -/
theorem apply_eq_one_of_character_eq_finrank
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (h : ρ.character g = (Module.finrank ℂ V : ℂ)) :
    ρ g = 1 := by
  classical
  haveI : Nonempty G := ⟨1⟩
  let b := Module.finBasis ℂ V
  set M : G → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun h => LinearMap.toMatrix b b (ρ h) with hM
  have hM_mul : ∀ a c : G, M (a * c) = M a * M c := by
    intro a c; simp only [hM, map_mul, LinearMap.toMatrix_mul]
  have hM_one : M 1 = 1 := by simp only [hM, map_one, LinearMap.toMatrix_one]
  have hunit : ∀ h : G, IsUnit (M h) := fun h =>
    ⟨⟨M h, M h⁻¹, by rw [← hM_mul, mul_inv_cancel, hM_one],
      by rw [← hM_mul, inv_mul_cancel, hM_one]⟩, rfl⟩
  have hdet : ∀ h : G, IsUnit (M h).det :=
    fun h => (Matrix.isUnit_iff_isUnit_det _).mp (hunit h)
  set H : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    ∑ h : G, (M h)ᴴ * M h with hH
  have hH_pd : H.PosDef := by
    rw [hH]
    refine Matrix.posDef_sum Finset.univ_nonempty (fun h _ => ?_)
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (hunit h)).mpr Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH_pd.isUnit
  have hinv : (M g)ᴴ * H * M g = H := by
    have step : ∀ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g = (M (h * g))ᴴ * M (h * g) := by
      intro h; rw [hM_mul, Matrix.conjTranspose_mul]; simp only [mul_assoc]
    calc (M g)ᴴ * H * M g
        = ∑ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g := by rw [hH, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G, (M (h * g))ᴴ * M (h * g) := Finset.sum_congr rfl (fun h _ => step h)
      _ = ∑ h : G, (M h)ᴴ * M h := Equiv.sum_comp (Equiv.mulRight g) fun h => (M h)ᴴ * M h
      _ = H := rfl
  set L : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ := CFC.sqrt H with hL
  have hHnonneg : (0 : Matrix _ _ ℂ) ≤ H := hH_pd.posSemidef.nonneg
  have hL_sq : L * L = H := CFC.sqrt_mul_sqrt_self H hHnonneg
  have hLnonneg : (0 : Matrix _ _ ℂ) ≤ L := CFC.sqrt_nonneg H
  have hL_herm : Lᴴ = L := (Matrix.nonneg_iff_posSemidef.mp hLnonneg).isHermitian
  have hLdet : IsUnit L.det := by
    have hprod : L.det * L.det = H.det := by rw [← Matrix.det_mul, hL_sq]
    have hne : L.det ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hprod; exact hH_det.ne_zero hprod.symm
    exact isUnit_iff_ne_zero.mpr hne
  have hLinv_l : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hLdet
  have hLinv_r : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hLdet
  have hLinv_herm : (L⁻¹)ᴴ = L⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hL_herm]
  set U : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ := L * M g * L⁻¹ with hU
  have hUunit : Uᴴ * U = 1 := by
    have hUH : Uᴴ = L⁻¹ * (M g)ᴴ * L := by
      rw [hU]; simp only [Matrix.conjTranspose_mul, hLinv_herm, hL_herm, mul_assoc]
    rw [hUH, hU]
    calc L⁻¹ * (M g)ᴴ * L * (L * M g * L⁻¹)
        = L⁻¹ * ((M g)ᴴ * (L * L) * M g) * L⁻¹ := by simp only [mul_assoc]
      _ = L⁻¹ * ((M g)ᴴ * H * M g) * L⁻¹ := by rw [hL_sq]
      _ = L⁻¹ * H * L⁻¹ := by rw [hinv]
      _ = L⁻¹ * (L * L) * L⁻¹ := by rw [← hL_sq]
      _ = (L⁻¹ * L) * (L * L⁻¹) := by simp only [mul_assoc]
      _ = 1 := by rw [hLinv_l, hLinv_r, Matrix.one_mul]
  have hUtr : U.trace = (Module.finrank ℂ V : ℂ) := by
    have h1 : U.trace = (M g).trace := by
      rw [hU, Matrix.trace_mul_comm, ← mul_assoc, hLinv_l, Matrix.one_mul]
    rw [h1]
    have hMgdef : M g = LinearMap.toMatrix b b (ρ g) := by simp only [hM]
    rw [hMgdef, ← LinearMap.trace_eq_matrix_trace ℂ b (ρ g)]
    exact h
  have hUone : U = 1 := eq_one_of_conjTranspose_mul_self_eq_one_of_trace_eq_card U hUunit hUtr
  have hMg1 : M g = 1 := by
    have key : L⁻¹ * U * L = M g := by
      rw [hU, show L⁻¹ * (L * M g * L⁻¹) * L = (L⁻¹ * L) * M g * (L⁻¹ * L) from by
        simp only [mul_assoc], hLinv_l, Matrix.one_mul, Matrix.mul_one]
    rw [← key, hUone, Matrix.mul_one, hLinv_l]
  have hMgdef : M g = LinearMap.toMatrix b b (ρ g) := by simp only [hM]
  rw [hMgdef] at hMg1
  have hfin : LinearMap.toMatrix b b (ρ g) = LinearMap.toMatrix b b (1 : V →ₗ[ℂ] V) := by
    rw [hMg1, LinearMap.toMatrix_one]
  exact (LinearMap.toMatrix b b).injective hfin

/-- Every simple complex representation of a finite group admits a nonzero intertwining map into some tensor power of an injective representation. -/
@[source_ref "Chapter4/Problem4.12.10" (role := primary)]
theorem exists_nonzero_intertwiner_to_tensorPower_of_injective {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (⨂[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (tensorPowerRepresentation ρ n g) ∘ₗ φ := by
  classical
  have hcardℕ : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hcardℕ
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  haveI : Nontrivial W := by
    have : Nontrivial σ.asModule := hσ.nontrivial
    exact this
  have hWpos : (Module.finrank ℂ W : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (M := W)).ne'
  set d : ℂ := (Module.finrank ℂ V : ℂ) with hd
  suffices hex : ∃ n, 0 < Module.finrank ℂ (Representation.IntertwiningMap σ (tensorPowerRepresentation ρ n)) by
    obtain ⟨n, hn⟩ := hex
    haveI : Nontrivial (Representation.IntertwiningMap σ (tensorPowerRepresentation ρ n)) :=
      Module.nontrivial_of_finrank_pos hn
    obtain ⟨T, hT⟩ := exists_ne (0 : Representation.IntertwiningMap σ (tensorPowerRepresentation ρ n))
    refine ⟨n, T.toLinearMap, ?_, fun g => T.isIntertwining' g⟩
    intro hzero
    exact hT (Representation.IntertwiningMap.ext (by rw [hzero]; rfl))
  by_contra hex
  rw [not_exists] at hex
  have hmult0 : ∀ n, Module.finrank ℂ (Representation.IntertwiningMap σ (tensorPowerRepresentation ρ n)) = 0 :=
    fun n => Nat.le_zero.mp (not_lt.mp (hex n))
  have hsum : ∀ n, ∑ g : G, (ρ.character g) ^ n * σ.character g⁻¹ = 0 := by
    intro n
    have hmf := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ (tensorPowerRepresentation ρ n)
    rw [hmult0 n, Nat.cast_zero] at hmf
    simp only [character_tensorPowerRepresentation] at hmf
    rcases mul_eq_zero.mp hmf with h | h
    · exact absurd (inv_eq_zero.mp h) hcard
    · exact h
  have hpoly : ∀ p : Polynomial ℂ, ∑ g : G, p.eval (ρ.character g) * σ.character g⁻¹ = 0 := by
    intro p
    simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hsum k, mul_zero]
  set S : Finset ℂ := (Finset.univ.image ρ.character).erase d with hS
  set p : Polynomial ℂ := ∏ μ ∈ S, (Polynomial.X - Polynomial.C μ) with hp
  have hp_eval : ∀ x : ℂ, p.eval x = ∏ μ ∈ S, (x - μ) := by
    intro x
    rw [hp, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun μ _ => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hpd_ne : p.eval d ≠ 0 := by
    rw [hp_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro μ hμ
    have hne : μ ≠ d := (Finset.mem_erase.mp hμ).1
    exact sub_ne_zero.mpr fun hc => hne hc.symm
  have hval := hpoly p
  rw [Finset.sum_eq_single (1 : G)] at hval
  · rw [inv_one, Representation.char_one, Representation.char_one, ← hd] at hval
    exact (mul_ne_zero hpd_ne hWpos) hval
  · intro b _ hb
    have hbd : ρ.character b ≠ d := by
      intro hbd
      exact hb (hρ (by rw [apply_eq_one_of_character_eq_finrank ρ b (by rw [hbd, hd]), map_one]))
    rw [hp_eval, Finset.prod_eq_zero (i := ρ.character b), zero_mul]
    · exact Finset.mem_erase.mpr ⟨hbd, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
    · exact sub_self _
  · intro h; exact absurd (Finset.mem_univ _) h

end RepresentationTheory.TensorPowerRepresentations
