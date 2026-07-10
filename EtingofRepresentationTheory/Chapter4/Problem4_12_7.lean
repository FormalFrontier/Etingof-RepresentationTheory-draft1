import Mathlib

/-!
# Problem 4.12.7: `SU(2)`, the quaternions, and `SU(2) → SO(3)`

**Problem 4.12.7.** Let `G = SU(2)` (the group of unitary `2 × 2` matrices with determinant
`1`), and let `V = ℂ²` be the standard `2`-dimensional representation of `SU(2)`. We regard
`V` as a real representation, so it is `4`-dimensional.

(a) Show that `V` is irreducible (as a real representation).

(b) Let `ℍ` be the subspace of `End_ℝ(V)` consisting of endomorphisms of `V` as a real
representation. Show that `ℍ` is `4`-dimensional and closed under multiplication, and that
every nonzero element is invertible (`ℍ` is a division algebra).

(c) Find a basis `1, i, j, k` of `ℍ` with `i² = j² = k² = -1`, `ij = -ji = k`, etc. Thus
`Q₈` is a subgroup of `ℍˣ`.

(d) For `q = a + bi + cj + dk`, let `q̄ = a - bi - cj - dk` and `‖q‖² = q q̄`. Show that
`overline(q₁ q₂) = q̄₂ q̄₁` and `‖q₁ q₂‖ = ‖q₁‖ · ‖q₂‖`.

(e) Let `G` be the group of quaternions of norm `1`. Show that this group is isomorphic to
`SU(2)`.

(f) Consider the action of `G` on the space `V ⊆ ℍ` spanned by `i, j, k`, by
`x ↦ q x q⁻¹`. Since this preserves the norm, we get a homomorphism `h : SU(2) → SO(3)`.
Show that `h` is surjective and that its kernel is `{1, -1}`.

## Formalization

We model `SU(2)` by Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ` (unitary `2×2` complex
matrices of determinant `1`, a `Group`), `SO(3)` by `Matrix.specialOrthogonalGroup (Fin 3) ℝ`,
and the quaternions by `ℍ[ℝ] = Quaternion ℝ`. The group of unit quaternions is
`unitary ℍ[ℝ]` (`{q : star q * q = 1 = q * star q}`, i.e. `normSq q = 1`).

This is a statement pass: we give faithful signatures for parts **(a)**, **(d)**, **(e)**,
**(f)** with `sorry` proofs. Parts (b) and (c) (the commutant description of `ℍ` and the
explicit `1, i, j, k` basis) are left for a later pass.

* **(a)** `V = ℂ²` as a real representation: `Fin 2 → ℂ` is an `ℝ`-module and `SU(2)` acts
  `ℝ`-linearly by `Matrix.mulVec`. Irreducibility over `ℝ` is: every `SU(2)`-invariant
  `ℝ`-submodule is `⊥` or `⊤`.
* **(d)** conjugation reverses products (`star (q₁ q₂) = star q₂ * star q₁`) and the norm is
  multiplicative (`normSq (q₁ q₂) = normSq q₁ * normSq q₂`).
* **(e)** the group of unit quaternions is isomorphic (as a group) to `SU(2)`.
* **(f)** there is a surjective homomorphism `SU(2) → SO(3)` whose kernel consists exactly of
  `±1` (the two matrices `1` and `-1`).
-/

open scoped Quaternion
open Matrix

namespace Etingof.Problem4_12_7

/-- **Part (a).** The standard `2`-dimensional representation `V = ℂ²` of `SU(2)`, regarded as
a *real* representation (`SU(2)` acts `ℝ`-linearly on `Fin 2 → ℂ` by matrix-vector
multiplication), is irreducible: every `SU(2)`-invariant `ℝ`-subspace of `Fin 2 → ℂ` is
either `⊥` or `⊤`. -/
theorem real_irreducible
    (W : Submodule ℝ (Fin 2 → ℂ))
    (hW : ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ v : Fin 2 → ℂ,
      v ∈ W → (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hne
  -- Two elements of `SU(2)`: the diagonal phase `D = diag(i, -i)` and the "swap" `J`.
  have hD : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two]
  have hJ : (!![(0 : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two]
  -- The images of `v` under `D`, `J` and `D ∘ J` as explicit vectors.
  have eDv : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
      = ![Complex.I * v 0, -Complex.I * v 1] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have eJv : (!![(0 : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
      = ![-(v 1), v 0] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have eDJv : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).mulVec
      ![-(v 1), v 0] = ![-Complex.I * v 1, -Complex.I * v 0] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hDv : ![Complex.I * v 0, -Complex.I * v 1] ∈ W := eDv ▸ hW ⟨_, hD⟩ v hvW
  have hJv : ![-(v 1), v 0] ∈ W := eJv ▸ hW ⟨_, hJ⟩ v hvW
  have hDJv : ![-Complex.I * v 1, -Complex.I * v 0] ∈ W := eDJv ▸ hW ⟨_, hD⟩ _ hJv
  -- These four vectors form a real basis of `ℂ²`, hence `W = ⊤`.
  set f : Fin 4 → (Fin 2 → ℂ) :=
    ![v, ![Complex.I * v 0, -Complex.I * v 1], ![-(v 1), v 0],
      ![-Complex.I * v 1, -Complex.I * v 0]] with hf
  -- The squared norm of `v`; nonzero since `v ≠ 0`.
  set Nr : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1) with hNr_def
  have hNr : Nr ≠ 0 := by
    intro h
    apply hv0
    have h0 : Complex.normSq (v 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    have h1 : Complex.normSq (v 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp only [hf, Finset.sum_apply, Fin.sum_univ_four, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply,
      Complex.real_smul] at h0 h1
    -- `h0`, `h1` are the two coordinate equations. Rearrange into `v₀·α - v₁·β = 0`
    -- and (after conjugation) `conj v₁·α + conj v₀·β = 0`, with
    -- `α = g₀ + i g₁`, `β = g₂ + i g₃`.
    set α : ℂ := (g 0 : ℂ) + Complex.I * (g 1 : ℂ) with hα_def
    set β : ℂ := (g 2 : ℂ) + Complex.I * (g 3 : ℂ) with hβ_def
    have eqI : v 0 * α - v 1 * β = 0 := by linear_combination h0
    have h1c := congrArg (starRingEnd ℂ) h1
    simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, map_zero,
      Complex.conj_I] at h1c
    have eqII : (starRingEnd ℂ) (v 1) * α + (starRingEnd ℂ) (v 0) * β = 0 := by
      linear_combination h1c
    -- Eliminate to obtain `Nr·α = 0` and `Nr·β = 0`.
    have hNc : (Nr : ℂ) = v 0 * (starRingEnd ℂ) (v 0) + v 1 * (starRingEnd ℂ) (v 1) := by
      rw [Complex.mul_conj, Complex.mul_conj, hNr_def]; push_cast; ring
    have hαz : (Nr : ℂ) * α = 0 := by
      rw [hNc]
      linear_combination (starRingEnd ℂ) (v 0) * eqI + v 1 * eqII
    have hβz : (Nr : ℂ) * β = 0 := by
      rw [hNc]
      linear_combination (-(starRingEnd ℂ) (v 1)) * eqI + v 0 * eqII
    have hα0 : α = 0 := by
      rcases mul_eq_zero.mp hαz with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hNr
      · exact h
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp hβz with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hNr
      · exact h
    -- Read off the real coefficients from `α = 0` and `β = 0`.
    have hg0 : g 0 = 0 := by
      have := congrArg Complex.re hα0
      simpa [hα_def, Complex.add_re, Complex.mul_re] using this
    have hg1 : g 1 = 0 := by
      have := congrArg Complex.im hα0
      simpa [hα_def, Complex.add_im, Complex.mul_im] using this
    have hg2 : g 2 = 0 := by
      have := congrArg Complex.re hβ0
      simpa [hβ_def, Complex.add_re, Complex.mul_re] using this
    have hg3 : g 3 = 0 := by
      have := congrArg Complex.im hβ0
      simpa [hβ_def, Complex.add_im, Complex.mul_im] using this
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
    · exact hg3
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Fin 2 → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  have hsub : Submodule.span ℝ (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hvW
    · exact hDv
    · exact hJv
    · exact hDJv
  exact le_antisymm le_top (hspan ▸ hsub)

/-- **Part (d), conjugate of a product.** Quaternion conjugation (`star`) reverses products:
`overline(q₁ q₂) = q̄₂ q̄₁`. -/
theorem star_mul_rev (q₁ q₂ : ℍ[ℝ]) :
    star (q₁ * q₂) = star q₂ * star q₁ :=
  star_mul q₁ q₂

/-- **Part (d), multiplicativity of the norm.** The quaternion norm-square is multiplicative:
`‖q₁ q₂‖² = ‖q₁‖² · ‖q₂‖²`. -/
theorem normSq_mul (q₁ q₂ : ℍ[ℝ]) :
    Quaternion.normSq (q₁ * q₂) = Quaternion.normSq q₁ * Quaternion.normSq q₂ :=
  map_mul Quaternion.normSq q₁ q₂

/-- The standard embedding of quaternions into `2 × 2` complex matrices,
`q = a + b·i + c·j + d·k ↦ !![a + b·I, c + d·I; -c + d·I, a - b·I]`.  It is a ring
homomorphism whose restriction to unit quaternions lands in `SU(2)` (see below). -/
noncomputable def qmat (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]

@[simp] lemma qmat_apply_zero_zero (q : ℍ[ℝ]) :
    qmat q 0 0 = (q.re : ℂ) + q.imI * Complex.I := rfl
@[simp] lemma qmat_apply_zero_one (q : ℍ[ℝ]) :
    qmat q 0 1 = (q.imJ : ℂ) + q.imK * Complex.I := rfl
@[simp] lemma qmat_apply_one_zero (q : ℍ[ℝ]) :
    qmat q 1 0 = -(q.imJ : ℂ) + q.imK * Complex.I := rfl
@[simp] lemma qmat_apply_one_one (q : ℍ[ℝ]) :
    qmat q 1 1 = (q.re : ℂ) - q.imI * Complex.I := rfl

/-- `qmat` sends `1` to the identity matrix. -/
lemma qmat_one : qmat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `qmat` is multiplicative: it turns quaternion multiplication into matrix multiplication. -/
lemma qmat_mul (q₁ q₂ : ℍ[ℝ]) : qmat (q₁ * q₂) = qmat q₁ * qmat q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [qmat, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] ;
      apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero, sub_zero,
        zero_sub, add_zero, zero_add] <;> ring)

/-- Conjugation of a quaternion corresponds to the conjugate transpose of the matrix. -/
lemma qmat_conjTranspose (q : ℍ[ℝ]) : qmat (star q) = (qmat q)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [qmat, Matrix.conjTranspose_apply, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] ;
      apply Complex.ext <;> simp)

/-- The determinant of the matrix `qmat q` is the quaternion norm-square of `q`. -/
lemma qmat_det (q : ℍ[ℝ]) : (qmat q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def']
  simp only [qmat_apply_zero_zero, qmat_apply_zero_one, qmat_apply_one_zero, qmat_apply_one_one]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero, sub_zero,
      zero_sub, add_zero, zero_add] <;> ring

/-- A quaternion is a unit (`normSq = 1`) exactly when it lies in `unitary ℍ[ℝ]`. -/
lemma mem_unitary_iff_normSq {q : ℍ[ℝ]} : q ∈ unitary ℍ[ℝ] ↔ Quaternion.normSq q = 1 := by
  rw [Unitary.mem_iff]
  constructor
  · rintro ⟨h, -⟩
    rw [Quaternion.star_mul_self, ← Quaternion.coe_one, Quaternion.coe_inj] at h
    exact h
  · intro h
    have hc : ((Quaternion.normSq q : ℝ) : ℍ[ℝ]) = 1 := by rw [h, Quaternion.coe_one]
    exact ⟨by rw [Quaternion.star_mul_self]; exact hc, by rw [Quaternion.self_mul_star]; exact hc⟩

/-- The group homomorphism from unit quaternions to `SU(2)` given by `qmat`. -/
noncomputable def qmatHom : unitary ℍ[ℝ] →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨qmat (q : ℍ[ℝ]), by
    have hq : Quaternion.normSq (q : ℍ[ℝ]) = 1 := mem_unitary_iff_normSq.mp q.2
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← qmat_conjTranspose,
        ← qmat_mul, Quaternion.star_mul_self, hq, Quaternion.coe_one, qmat_one]
    · rw [qmat_det, hq]; norm_num⟩
  map_one' := Subtype.ext (by simpa using qmat_one)
  map_mul' a b := Subtype.ext (by simpa using qmat_mul (a : ℍ[ℝ]) (b : ℍ[ℝ]))

lemma qmatHom_injective : Function.Injective qmatHom := by
  intro a b h
  have hm : qmat (a : ℍ[ℝ]) = qmat (b : ℍ[ℝ]) := congrArg Subtype.val h
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp only [qmat_apply_zero_zero, qmat_apply_zero_one] at e00 e01
  apply Subtype.ext
  apply Quaternion.ext
  · simpa using congrArg Complex.re e00
  · simpa using congrArg Complex.im e00
  · simpa using congrArg Complex.re e01
  · simpa using congrArg Complex.im e01

lemma qmatHom_surjective : Function.Surjective qmatHom := by
  intro A
  set M : Matrix (Fin 2) (Fin 2) ℂ := (A : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hmem := A.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hmem
  obtain ⟨hu, hdet⟩ := hmem
  have huc : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  have hinvL : M⁻¹ = Mᴴ := Matrix.inv_eq_left_inv huc
  have hinvR : M⁻¹ = M.adjugate := by
    apply Matrix.inv_eq_right_inv; rw [Matrix.mul_adjugate, hdet, one_smul]
  have hadj : Mᴴ = M.adjugate := by rw [← hinvL, hinvR]
  rw [Matrix.adjugate_fin_two] at hadj
  have h11 : M 1 1 = star (M 0 0) := by
    have h := congrFun (congrFun hadj 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    exact h.symm
  have h10 : M 1 0 = -star (M 0 1) := by
    have h := congrFun (congrFun hadj 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    rw [h]; ring
  set q : ℍ[ℝ] := ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩ with hq
  have key : (Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) = 1 := by
    have hdet2 : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
    rw [h11, h10, mul_neg, sub_neg_eq_add] at hdet2
    have e0 : M 0 0 * star (M 0 0) = (Complex.normSq (M 0 0) : ℂ) := Complex.mul_conj (M 0 0)
    have e1 : M 0 1 * star (M 0 1) = (Complex.normSq (M 0 1) : ℂ) := Complex.mul_conj (M 0 1)
    rw [e0, e1, hdet] at hdet2
    exact_mod_cast hdet2.symm
  have hnorm : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_def']
    simp only [hq, Complex.normSq_apply] at key ⊢
    nlinarith [key]
  refine ⟨⟨q, mem_unitary_iff_normSq.mpr hnorm⟩, ?_⟩
  apply Subtype.ext
  change qmat q = M
  rw [Matrix.eta_fin_two M, h11, h10]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, hq, Complex.ext_iff]

/-- **Part (e).** The group of unit quaternions (`unitary ℍ[ℝ]`, i.e. quaternions of norm `1`)
is isomorphic, as a group, to `SU(2)`. -/
theorem unit_quaternions_mulEquiv_SU2 :
    Nonempty (unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨MulEquiv.ofBijective qmatHom ⟨qmatHom_injective, qmatHom_surjective⟩⟩

/-- **Part (f).** There is a surjective group homomorphism `h : SU(2) → SO(3)` whose kernel is
exactly `{1, -1}`: `A ∈ ker h` iff the matrix of `A` is `1` or `-1`. -/
theorem exists_surjective_hom_to_SO3 :
    ∃ h : Matrix.specialUnitaryGroup (Fin 2) ℂ →*
        Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Surjective h ∧
      ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        A ∈ h.ker ↔
          ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
           (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
  sorry

end Etingof.Problem4_12_7
