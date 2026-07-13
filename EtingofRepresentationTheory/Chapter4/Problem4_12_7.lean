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

Parts **(a)**, **(d)**, **(e)** are proved sorry-free.  Part **(f)** builds the conjugation
homomorphism `h : SU(2) → SO(3)` genuinely and proves its kernel is exactly `{1, -1}`; the one
remaining `sorry` is the *surjectivity* of `h` (`rotHom_surjective`), the classical `2:1`-cover
statement that every rotation of `ℝ³` is conjugation by a unit quaternion (axis–angle normal form,
not yet in Mathlib).  Parts (b) and (c) (the commutant description of `ℍ` and the explicit
`1, i, j, k` basis) are left for a later pass.

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

/-- `qmat` is injective as a function on all of `ℍ[ℝ]`: the matrix `qmat q` determines the four
real components of `q`. -/
lemma qmat_injective : Function.Injective qmat := by
  intro a b h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp only [qmat_apply_zero_zero, qmat_apply_zero_one] at e00 e01
  apply Quaternion.ext
  · simpa using congrArg Complex.re e00
  · simpa using congrArg Complex.im e00
  · simpa using congrArg Complex.re e01
  · simpa using congrArg Complex.im e01

/-- `qmat (-1) = -1` (the matrix of `-1 ∈ ℍ[ℝ]` is the negative identity). -/
lemma qmat_neg_one : qmat (-1 : ℍ[ℝ]) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, Complex.ext_iff]

/-! ### Part (f): the conjugation action `SU(2) → SO(3)`

We realize the imaginary quaternions `V = span{i, j, k}` as `ℝ³` (a quaternion's coordinates
`(imI, imJ, imK)`) and, for a unit quaternion `q`, form the `3×3` real matrix `rotMat q` of the
conjugation `x ↦ q · x · star q` (`= q x q⁻¹`, since `star q = q⁻¹` for unit `q`).  Because
`q x star q` is purely imaginary for imaginary `x`, and conjugation preserves the norm, `rotMat q`
lands in `SO(3)`, and `rotMat` is multiplicative. -/

section PartF

/-- The unit imaginary quaternion `i = (0,1,0,0)`. -/
noncomputable def qI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The unit imaginary quaternion `j = (0,0,1,0)`. -/
noncomputable def qJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- The unit imaginary quaternion `k = (0,0,0,1)`. -/
noncomputable def qK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

@[simp] lemma qI_re : qI.re = 0 := rfl
@[simp] lemma qI_imI : qI.imI = 1 := rfl
@[simp] lemma qI_imJ : qI.imJ = 0 := rfl
@[simp] lemma qI_imK : qI.imK = 0 := rfl
@[simp] lemma qJ_re : qJ.re = 0 := rfl
@[simp] lemma qJ_imI : qJ.imI = 0 := rfl
@[simp] lemma qJ_imJ : qJ.imJ = 1 := rfl
@[simp] lemma qJ_imK : qJ.imK = 0 := rfl
@[simp] lemma qK_re : qK.re = 0 := rfl
@[simp] lemma qK_imI : qK.imI = 0 := rfl
@[simp] lemma qK_imJ : qK.imJ = 0 := rfl
@[simp] lemma qK_imK : qK.imK = 1 := rfl

/-- The `3 × 3` real matrix of the conjugation `x ↦ q · x · star q` acting on the imaginary
quaternions `span{i, j, k}`, written in the ordered basis `i, j, k`.  Column `j` records the
`(imI, imJ, imK)` coordinates of the image of the `j`-th basis imaginary quaternion. -/
noncomputable def rotMat (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ (q * qI * star q).imI, (q * qJ * star q).imI, (q * qK * star q).imI;
      (q * qI * star q).imJ, (q * qJ * star q).imJ, (q * qK * star q).imJ;
      (q * qI * star q).imK, (q * qJ * star q).imK, (q * qK * star q).imK ]

attribute [local simp] Quaternion.re_mul Quaternion.imI_mul Quaternion.imJ_mul Quaternion.imK_mul
  Quaternion.re_star Quaternion.imI_star Quaternion.imJ_star Quaternion.imK_star

/-- Conjugation by `-q` equals conjugation by `q` (the two sign changes cancel), so
`rotMat (-q) = rotMat q`. -/
lemma rotMat_neg (q : ℍ[ℝ]) : rotMat (-q) = rotMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, star_neg, neg_mul, mul_neg, neg_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]

/-- `rotMat` sends `1` to the identity matrix. -/
lemma rotMat_one : rotMat (1 : ℍ[ℝ]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, star_one, one_mul, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue, qI_imI, qI_imJ, qI_imK, qJ_imI, qJ_imJ, qJ_imK,
      qK_imI, qK_imJ, qK_imK, Matrix.one_apply] <;> norm_num

/-- `rotMat (-1) = 1`. -/
lemma rotMat_neg_one : rotMat (-1 : ℍ[ℝ]) = 1 := by
  rw [rotMat_neg, rotMat_one]

/-- `rotMat` is multiplicative: `rotMat (q₁ * q₂) = rotMat q₁ * rotMat q₂`.  This is the algebraic
heart of the homomorphism `SU(2) → SO(3)`: `q₁ q₂ · x · star (q₁ q₂) = q₁ (q₂ x star q₂) star q₁`,
and `q₂ x star q₂` is again imaginary. -/
lemma rotMat_mul (q₁ q₂ : ℍ[ℝ]) : rotMat (q₁ * q₂) = rotMat q₁ * rotMat q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
    simp <;> ring

/-- The `(0,0)` entry of `rotMat q` in closed form. -/
lemma rotMat_apply_00 (q : ℍ[ℝ]) :
    rotMat q 0 0 = q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [rotMat, Matrix.cons_val_zero, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply]
  simp <;> ring

/-- The `(1,1)` entry of `rotMat q` in closed form. -/
lemma rotMat_apply_11 (q : ℍ[ℝ]) :
    rotMat q 1 1 = q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [rotMat, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  simp <;> ring

/-- For a unit quaternion `q` (`normSq q = 1`), the conjugation matrix `rotMat q` is a special
orthogonal matrix: it preserves the standard inner product on `ℝ³` and has determinant `1`. -/
lemma rotMat_mem_SO3 (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    rotMat q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have h4 : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hq; linarith
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
        Matrix.one_apply, Fin.isValue] <;>
      simp <;>
      · first
        | linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * h4
        | linear_combination (0 : ℝ)
  · rw [Matrix.det_fin_three]
    simp only [rotMat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    simp
    linear_combination
      ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 +
        (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) + 1) * h4

/-- For a unit quaternion `q`, the conjugation `rotMat q` is the identity exactly when `q = ±1`:
conjugation fixes `i, j, k` iff `q` is central in `ℍ[ℝ]`, i.e. real, and a unit real quaternion is
`±1`. -/
lemma rotMat_eq_one_iff (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    rotMat q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have h4 : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
      rw [Quaternion.normSq_def'] at hq; linarith
    have e00 : rotMat q 0 0 = 1 := by rw [h]; simp [Matrix.one_apply]
    have e11 : rotMat q 1 1 = 1 := by rw [h]; simp [Matrix.one_apply]
    rw [rotMat_apply_00] at e00
    rw [rotMat_apply_11] at e11
    have hb : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hc : q.imJ = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hd : q.imK = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have ha : q.re = 1 ∨ q.re = -1 := mul_self_eq_one_iff.mp (by nlinarith)
    rcases ha with ha | ha
    · left; ext <;> simp [ha, hb, hc, hd]
    · right; ext <;> simp [ha, hb, hc, hd]
  · rintro (rfl | rfl)
    · exact rotMat_one
    · exact rotMat_neg_one

/-- The conjugation homomorphism `unitary ℍ[ℝ] →* SO(3)`, `q ↦ (x ↦ q x q⁻¹)` on the imaginary
quaternions. -/
noncomputable def rotHom : unitary ℍ[ℝ] →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun q := ⟨rotMat (q : ℍ[ℝ]), rotMat_mem_SO3 _ (mem_unitary_iff_normSq.mp q.2)⟩
  map_one' := Subtype.ext (by simpa using rotMat_one)
  map_mul' a b := Subtype.ext (by simpa using rotMat_mul (a : ℍ[ℝ]) (b : ℍ[ℝ]))

@[simp] lemma rotHom_coe (q : unitary ℍ[ℝ]) :
    (rotHom q : Matrix (Fin 3) (Fin 3) ℝ) = rotMat (q : ℍ[ℝ]) := rfl

/-! ### Coordinate-axis rotations in the image of `rotMat`

The conjugation by the "half-angle" quaternion `⟨c, s, 0, 0⟩` (real part `c`, `i`-part `s`) is the
rotation of `ℝ³` about the `i`-axis whose block on the `j,k`-plane is
`!![c²-s², -2cs; 2cs, c²-s²]`.  With `c = cos (θ/2)`, `s = sin (θ/2)` the double-angle identities
`c²-s² = cos θ`, `2cs = sin θ` turn this into the standard rotation `Rx θ`.  The `j`- and `k`-axis
analogues are `rotMat_yAxis`/`rotMat_zAxis`.  These are the one-parameter subgroups that generate
`SO(3)` (Euler decomposition), the route to `rotHom_surjective`.  Stated as exact polynomial
identities in `c, s` (no `c²+s²=1` needed), so they compose cleanly under `rotMat_mul`. -/
lemma rotMat_xAxis (c s : ℝ) :
    rotMat (⟨c, s, 0, 0⟩ : ℍ[ℝ]) =
      !![c ^ 2 + s ^ 2, 0, 0;
         0, c ^ 2 - s ^ 2, -(2 * c * s);
         0, 2 * c * s, c ^ 2 - s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, qI, qJ, qK] <;> ring

/-- Conjugation by `⟨c, 0, s, 0⟩` is the rotation of `ℝ³` about the `j`-axis; with
`c = cos (θ/2)`, `s = sin (θ/2)` it is the standard rotation `Ry θ`. -/
lemma rotMat_yAxis (c s : ℝ) :
    rotMat (⟨c, 0, s, 0⟩ : ℍ[ℝ]) =
      !![c ^ 2 - s ^ 2, 0, 2 * c * s;
         0, c ^ 2 + s ^ 2, 0;
         -(2 * c * s), 0, c ^ 2 - s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, qI, qJ, qK] <;> ring

/-- Conjugation by `⟨c, 0, 0, s⟩` is the rotation of `ℝ³` about the `k`-axis; with
`c = cos (θ/2)`, `s = sin (θ/2)` it is the standard rotation `Rz θ`. -/
lemma rotMat_zAxis (c s : ℝ) :
    rotMat (⟨c, 0, 0, s⟩ : ℍ[ℝ]) =
      !![c ^ 2 - s ^ 2, -(2 * c * s), 0;
         2 * c * s, c ^ 2 - s ^ 2, 0;
         0, 0, c ^ 2 + s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, qI, qJ, qK] <;> ring

/-- **Surjectivity of the quaternion cover.** Every rotation of Euclidean `ℝ³` is conjugation by a
unit quaternion — the classical statement that `SU(2) → SO(3)` is the (`2:1`) universal cover.
This is the axis–angle decomposition: a rotation by angle `θ` about a unit axis
`n = (n₁, n₂, n₃)` is `rotMat (cos (θ/2) + sin (θ/2) · (n₁ i + n₂ j + n₃ k))`.

TODO: this remaining piece requires the axis–angle normal form for `SO(3)` (every element of
`SO(3)` fixes an axis, as `1` is an eigenvalue in odd dimension with determinant `1`), which is not
yet available in Mathlib. -/
theorem rotHom_surjective : Function.Surjective rotHom := by
  sorry

end PartF

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
  -- The group iso `e : unit quaternions ≃* SU(2)` from part (e).
  let e : unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    MulEquiv.ofBijective qmatHom ⟨qmatHom_injective, qmatHom_surjective⟩
  -- Transport the conjugation homomorphism `rotHom` along `e⁻¹`.
  refine ⟨rotHom.comp e.symm.toMonoidHom, ?_, ?_⟩
  · -- Surjectivity: `rotHom` is surjective and `e` is a bijection.
    intro M
    obtain ⟨q, hq⟩ := rotHom_surjective M
    refine ⟨e q, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hq
  · -- Kernel: `A ∈ ker h ↔ rotMat (e⁻¹ A) = 1 ↔ e⁻¹ A = ±1 ↔ (A : Matrix) = ±1`.
    intro A
    have hnorm : Quaternion.normSq ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) = 1 :=
      mem_unitary_iff_normSq.mp (e.symm A).2
    have hAq : (A : Matrix (Fin 2) (Fin 2) ℂ) = qmat ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) := by
      have h1 : qmatHom (e.symm A) = A := e.apply_symm_apply A
      calc (A : Matrix (Fin 2) (Fin 2) ℂ)
            = ((qmatHom (e.symm A) : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
                Matrix (Fin 2) (Fin 2) ℂ) := by rw [h1]
        _ = qmat ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) := rfl
    have hker : A ∈ (rotHom.comp e.symm.toMonoidHom).ker ↔
        rotMat ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) = 1 := by
      rw [MonoidHom.mem_ker]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subtype.ext_iff, rotHom_coe,
        Submonoid.coe_one]
    rw [hker, rotMat_eq_one_iff _ hnorm, hAq]
    constructor
    · rintro (h | h)
      · left; rw [h, qmat_one]
      · right; rw [h, qmat_neg_one]
    · rintro (h | h)
      · left; exact qmat_injective (by rw [qmat_one]; exact h)
      · right; exact qmat_injective (by rw [qmat_neg_one]; exact h)

end Etingof.Problem4_12_7
