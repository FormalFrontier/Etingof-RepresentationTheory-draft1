import Mathlib

/-!
# Proposition 5.25.1: Commutator Subgroup of GL₂(𝔽_q)

[G, G] = SL₂(𝔽_q) where G = GL₂(𝔽_q), for q ≥ 3.

The proof shows det(xyx⁻¹y⁻¹) = 1 so [G,G] ⊆ SL₂, then exhibits the
generators of SL₂ as explicit commutators.

Note: The original statement omitted the hypothesis q ≥ 3. For q = 2,
GL₂(𝔽₂) ≅ S₃ and [S₃, S₃] = A₃ ⊊ S₃ = SL₂(𝔽₂), so the equality fails.
The hypothesis `hq : 2 < Nat.card (GaloisField p n)` corrects this.

## Mathlib correspondence

Uses `GaloisField`, `Matrix.SpecialLinearGroup`, `Matrix.GeneralLinearGroup`.
-/

open Matrix

namespace Proposition5_25_1_aux

variable {F : Type*} [Field F]

abbrev GL₂ (F : Type*) [CommRing F] := GeneralLinearGroup (Fin 2) F

-- GL₂ elements

def E12 (t : F) : GL₂ F where
  val := !![1, t; 0, 1]
  inv := !![1, -t; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

def E21 (t : F) : GL₂ F where
  val := !![1, 0; t, 1]
  inv := !![1, 0; -t, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

def diagGL (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : GL₂ F where
  val := !![a, 0; 0, b]
  inv := !![a⁻¹, 0; 0, b⁻¹]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]

def weylGL : GL₂ F where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem commutator_of_comm (g h : GL₂ F) :
    g * h * g⁻¹ * h⁻¹ ∈ commutator (GL₂ F) :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)

-- Commutator formulas

theorem comm_diag_E12 (a t : F) (ha : a ≠ 0) :
    diagGL a 1 ha one_ne_zero * E12 t * (diagGL a 1 ha one_ne_zero)⁻¹ * (E12 t)⁻¹ =
      E12 ((a - 1) * t) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, E12, diagGL, Units.inv_mk] <;> field_simp <;> ring

theorem comm_diag_E21 (a t : F) (ha : a ≠ 0) :
    diagGL 1 a one_ne_zero ha * E21 t * (diagGL 1 a one_ne_zero ha)⁻¹ * (E21 t)⁻¹ =
      E21 ((a - 1) * t) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, E21, diagGL, Units.inv_mk] <;> field_simp <;> ring

theorem comm_diag_weyl (d : F) (hd : d ≠ 0) :
    diagGL d 1 hd one_ne_zero * weylGL * (diagGL d 1 hd one_ne_zero)⁻¹ * weylGL⁻¹ =
      diagGL d d⁻¹ hd (inv_ne_zero hd) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, diagGL, weylGL, Units.inv_mk]

-- Commutator membership

theorem E12_mem_commutator (t : F) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    E12 (F := F) t ∈ commutator (GL₂ F) := by
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  rw [show E12 t = diagGL a 1 ha0 one_ne_zero * E12 (t * (a - 1)⁻¹) *
      (diagGL a 1 ha0 one_ne_zero)⁻¹ * (E12 (t * (a - 1)⁻¹))⁻¹
    from by rw [comm_diag_E12]; congr 1; field_simp]
  exact commutator_of_comm _ _

theorem E21_mem_commutator (t : F) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    E21 (F := F) t ∈ commutator (GL₂ F) := by
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  rw [show E21 t = diagGL 1 a one_ne_zero ha0 * E21 (t * (a - 1)⁻¹) *
      (diagGL 1 a one_ne_zero ha0)⁻¹ * (E21 (t * (a - 1)⁻¹))⁻¹
    from by rw [comm_diag_E21]; congr 1; field_simp]
  exact commutator_of_comm _ _

theorem diag_det1_mem_commutator (d : F) (hd : d ≠ 0) :
    diagGL (F := F) d d⁻¹ hd (inv_ne_zero hd) ∈ commutator (GL₂ F) := by
  rw [show diagGL d d⁻¹ hd (inv_ne_zero hd) =
    diagGL d 1 hd one_ne_zero * weylGL * (diagGL d 1 hd one_ne_zero)⁻¹ * weylGL⁻¹
    from (comm_diag_weyl d hd).symm]
  exact commutator_of_comm _ _

-- Existence of a ≠ 0, 1

theorem exists_ne_zero_ne_one (hcard : 2 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hcard
  by_contra h; push_neg at h
  have huniv : ∀ x : F, x = 0 ∨ x = 1 := fun x => by
    by_contra hx; push_neg at hx; exact absurd (h x hx.1) hx.2
  have : Fintype.card F ≤ 2 := Fintype.card_le_of_surjective
    (fun b : Bool => if b then (1 : F) else 0)
    (fun x => by rcases huniv x with rfl | rfl; exact ⟨false, rfl⟩; exact ⟨true, rfl⟩)
    |>.trans (by simp [Fintype.card_bool])
  omega

-- Main factorization

theorem sl2_mem_commutator (s : SpecialLinearGroup (Fin 2) F)
    (a₀ : F) (ha0 : a₀ ≠ 0) (ha1 : a₀ ≠ 1) :
    SpecialLinearGroup.toGL s ∈ commutator (GL₂ F) := by
  set M := (s : Matrix (Fin 2) (Fin 2) F)
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := s.prop; rwa [det_fin_two] at this
  by_cases hc : M 1 0 = 0
  · -- Case c = 0: ad = 1
    have had : M 0 0 * M 1 1 = 1 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    have ha_ne : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hd_eq : M 1 1 = (M 0 0)⁻¹ :=
      mul_left_cancel₀ ha_ne (had.trans (mul_inv_cancel₀ ha_ne).symm)
    -- s = diag(a, a⁻¹) * E₁₂(a⁻¹ * b)
    have hM : ∀ i j, (↑s : Matrix (Fin 2) (Fin 2) F) i j = M i j := fun _ _ => rfl
    have hval : SpecialLinearGroup.toGL s =
        diagGL (M 0 0) (M 0 0)⁻¹ ha_ne (inv_ne_zero ha_ne) *
        E12 ((M 0 0)⁻¹ * M 0 1) := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, E12, diagGL, mul_apply, Fin.sum_univ_two,
          SpecialLinearGroup.coe_GL_coe_matrix, hM, hc, hd_eq] <;>
        field_simp
    rw [hval]
    exact (commutator _).mul_mem (diag_det1_mem_commutator _ ha_ne)
      (E12_mem_commutator _ a₀ ha0 ha1)
  · -- Case c ≠ 0: s = E₁₂((a-1)/c) * E₂₁(c) * E₁₂((d-1)/c)
    have hM : ∀ i j, (↑s : Matrix (Fin 2) (Fin 2) F) i j = M i j := fun _ _ => rfl
    have hval : SpecialLinearGroup.toGL s =
        E12 ((M 0 0 - 1) / M 1 0) * E21 (M 1 0) * E12 ((M 1 1 - 1) / M 1 0) := by
      have hbc : M 0 1 * M 1 0 = M 0 0 * M 1 1 - 1 := by
        clear_value M; linear_combination -hdet
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, E12, E21, mul_apply, Fin.sum_univ_two,
          SpecialLinearGroup.coe_GL_coe_matrix, hM]
      · -- (0,0)
        rw [div_mul_cancel₀ _ hc]; ring
      · -- (0,1)
        rw [div_mul_cancel₀ _ hc]
        clear_value M; field_simp; linear_combination hbc
      · -- (1,1)
        rw [mul_div_cancel₀ _ hc]; ring
    rw [hval]
    exact (commutator _).mul_mem
      ((commutator _).mul_mem (E12_mem_commutator _ a₀ ha0 ha1)
        (E21_mem_commutator _ a₀ ha0 ha1))
      (E12_mem_commutator _ a₀ ha0 ha1)

end Proposition5_25_1_aux

/-- The commutator subgroup of GL₂(𝔽_q) equals SL₂(𝔽_q) for q ≥ 3.
(Etingof Proposition 5.25.1) -/
theorem Etingof.Proposition5_25_1
    (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (_hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) :
    commutator (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) =
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField p n)).range := by
  apply le_antisymm
  · -- ⊆: [GL, GL] ≤ SL = ker(det)
    intro g hg
    rw [MonoidHom.mem_range]
    have hdet : g ∈ (Matrix.GeneralLinearGroup.det).ker :=
      Abelianization.commutator_subset_ker _ hg
    rw [MonoidHom.mem_ker] at hdet
    exact ⟨⟨g, Units.ext_iff.mp hdet⟩, Units.ext rfl⟩
  · -- ⊇: SL ≤ [GL, GL]
    intro g hg
    obtain ⟨s, rfl⟩ := hg
    obtain ⟨a₀, ha0, ha1⟩ := Proposition5_25_1_aux.exists_ne_zero_ne_one hq
    exact Proposition5_25_1_aux.sl2_mem_commutator s a₀ ha0 ha1
