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

Part **(f)** constructs the
conjugation homomorphism `h : SU(2) → SO(3)`, proves its kernel is exactly `{1, -1}`, and
proves its surjectivity (`rotHom_surjective`) via the Euler `Z-Y-Z` decomposition of `SO(3)`
(`so3_euler_zyz`: every `R ∈ SO(3)` is `Rz α · Ry β · Rz γ`), the classical existence of Euler
angles, established here from the orthonormality and cofactor (`adjugate R = Rᵀ`) relations of `R`.

* **(a)** `V = ℂ²` as a real representation: `Fin 2 → ℂ` is an `ℝ`-module and `SU(2)` acts
  `ℝ`-linearly by `Matrix.mulVec`. Irreducibility over `ℝ` is: every `SU(2)`-invariant
  `ℝ`-submodule is `⊥` or `⊤`.
* **(b)** the commutant `ℍ = End_{SU(2)}(V)` (`commutant`, the `ℝ`-subalgebra of `End_ℝ(ℂ²)`
  commuting with the action) is closed under multiplication (it is a centralizer), is a division
  algebra (`commutant_isUnit_of_ne_zero`, via Schur and part (a)), and is `4`-dimensional
  (`finrank_commutant`, via the explicit basis `1, i, j, k` = `id, I•, J·conj, I·J·conj`).
* **(c)** the Hamilton relations `i² = j² = k² = -1`, `ij = k = -ji`, `jk = i = -kj`,
  `ki = j = -ik` on `qI, qJ, qK`; `1, i, j, k` as an `ℝ`-basis (`quaternionBasis`, hence
  `finrank ℝ ℍ[ℝ] = 4`); and `Q₈ = {±1, ±i, ±j, ±k} ⊆ ℍ[ℝ]ˣ` recorded as a set of units
  (each in `unitary ℍ[ℝ]`) closed under multiplication, inverses, and containing `1`.
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
    simp [qmat]

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

/-! ### Part (c): the Hamilton relations, the `1, i, j, k` basis, and `Q₈ ⊆ ℍ[ℝ]ˣ`

We record the standard quaternion multiplication table on `qI, qJ, qK`, exhibit `1, i, j, k`
as an `ℝ`-basis of `ℍ[ℝ]` (so `finrank ℝ ℍ[ℝ] = 4`), and record that the eight elements
`±1, ±i, ±j, ±k` are units closed under multiplication, the quaternion group `Q₈` sitting
inside `ℍ[ℝ]ˣ`. -/

-- The Hamilton relations `i² = j² = k² = -1`, `ij = k`, etc.

@[simp] lemma qI_mul_qI : qI * qI = -1 := by ext <;> simp [qI]
@[simp] lemma qJ_mul_qJ : qJ * qJ = -1 := by ext <;> simp [qJ]
@[simp] lemma qK_mul_qK : qK * qK = -1 := by ext <;> simp [qK]

@[simp] lemma qI_mul_qJ : qI * qJ = qK := by ext <;> simp [qI, qJ, qK]
@[simp] lemma qJ_mul_qI : qJ * qI = -qK := by ext <;> simp [qI, qJ, qK]
@[simp] lemma qJ_mul_qK : qJ * qK = qI := by ext <;> simp [qI, qJ, qK]
@[simp] lemma qK_mul_qJ : qK * qJ = -qI := by ext <;> simp [qI, qJ, qK]
@[simp] lemma qK_mul_qI : qK * qI = qJ := by ext <;> simp [qI, qJ, qK]
@[simp] lemma qI_mul_qK : qI * qK = -qJ := by ext <;> simp [qI, qJ, qK]

/-- The `ℝ`-basis `1, i, j, k` of `ℍ[ℝ]`.  This is Mathlib's `basisOneIJK`, whose four vectors
are exactly `1, qI, qJ, qK` (see the `quaternionBasis_*` lemmas below). -/
noncomputable def quaternionBasis : Module.Basis (Fin 4) ℝ ℍ[ℝ] :=
  QuaternionAlgebra.basisOneIJK _ _ _

@[simp] lemma quaternionBasis_zero : quaternionBasis 0 = 1 := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 0 = 1
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr]
@[simp] lemma quaternionBasis_one : quaternionBasis 1 = qI := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 1 = qI
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, qI]
@[simp] lemma quaternionBasis_two : quaternionBasis 2 = qJ := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 2 = qJ
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, qJ]
@[simp] lemma quaternionBasis_three : quaternionBasis 3 = qK := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 3 = qK
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, qK]

/-- **Part (c), dimension.** `ℍ[ℝ]` is `4`-dimensional over `ℝ`. -/
theorem finrank_quaternion : Module.finrank ℝ ℍ[ℝ] = 4 :=
  Quaternion.finrank_eq_four

-- The conjugates of the imaginary units are their negatives.

@[simp] lemma star_qI : star qI = -qI := by ext <;> simp [qI]
@[simp] lemma star_qJ : star qJ = -qJ := by ext <;> simp [qJ]
@[simp] lemma star_qK : star qK = -qK := by ext <;> simp [qK]

-- The eight unit quaternions `±1, ±i, ±j, ±k` all have norm `1`, hence lie in `unitary ℍ[ℝ]`.

lemma normSq_qI : Quaternion.normSq qI = 1 := by rw [Quaternion.normSq_def']; simp [qI]
lemma normSq_qJ : Quaternion.normSq qJ = 1 := by rw [Quaternion.normSq_def']; simp [qJ]
lemma normSq_qK : Quaternion.normSq qK = 1 := by rw [Quaternion.normSq_def']; simp [qK]

lemma qI_mem_unitary : qI ∈ unitary ℍ[ℝ] := mem_unitary_iff_normSq.mpr normSq_qI
lemma qJ_mem_unitary : qJ ∈ unitary ℍ[ℝ] := mem_unitary_iff_normSq.mpr normSq_qJ
lemma qK_mem_unitary : qK ∈ unitary ℍ[ℝ] := mem_unitary_iff_normSq.mpr normSq_qK

/-- The quaternion group `Q₈ = {±1, ±i, ±j, ±k}` as a subset of `ℍ[ℝ]`. -/
def Q8 : Set ℍ[ℝ] := {1, -1, qI, -qI, qJ, -qJ, qK, -qK}

/-- **Part (c), `Q₈ ⊆ ℍ[ℝ]ˣ`.** Every element of `Q₈` is a unit (lies in `unitary ℍ[ℝ]`,
equivalently has norm `1`). -/
lemma Q8_subset_unitary : ∀ x ∈ Q8, x ∈ unitary ℍ[ℝ] := by
  intro x hx
  simp only [Q8, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    rw [mem_unitary_iff_normSq] <;>
    simp [Quaternion.normSq_neg, normSq_qI, normSq_qJ, normSq_qK]

/-- `1 ∈ Q₈`. -/
lemma one_mem_Q8 : (1 : ℍ[ℝ]) ∈ Q8 := by simp [Q8]

/-- **Part (c), closure.** `Q₈` is closed under multiplication: the quaternion multiplication
table (the Hamilton relations) maps `{±1, ±i, ±j, ±k}` into itself. -/
lemma Q8_mul_mem : ∀ x ∈ Q8, ∀ y ∈ Q8, x * y ∈ Q8 := by
  intro x hx y hy
  simp only [Q8, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    rcases hy with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [Q8]

/-- **Part (c), inverses.** `Q₈` is closed under taking (star = ) inverses: for each unit
quaternion in `Q₈`, its conjugate (which is its inverse) is again in `Q₈`. -/
lemma Q8_star_mem : ∀ x ∈ Q8, star x ∈ Q8 := by
  intro x hx
  simp only [Q8, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [Q8]

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
    simp only [rotMat, star_neg, neg_mul, mul_neg, neg_neg,
      Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply]

/-- `rotMat` sends `1` to the identity matrix. -/
lemma rotMat_one : rotMat (1 : ℍ[ℝ]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, star_one, one_mul, mul_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, qI_imI, qI_imJ, qI_imK, qJ_imI, qJ_imJ, qJ_imK,
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
      Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
    simp <;> ring

/-- The `(0,0)` entry of `rotMat q` in closed form. -/
lemma rotMat_apply_00 (q : ℍ[ℝ]) :
    rotMat q 0 0 = q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [rotMat, Matrix.cons_val_zero, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply]
  simp ; ring

/-- The `(1,1)` entry of `rotMat q` in closed form. -/
lemma rotMat_apply_11 (q : ℍ[ℝ]) :
    rotMat q 1 1 = q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [rotMat, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  simp ; ring

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
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
        Matrix.one_apply, Fin.isValue] <;>
      simp <;>
      · first
        | linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * h4
        | linear_combination (0 : ℝ)
  · rw [Matrix.det_fin_three]
    simp only [rotMat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
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
    have e00 : rotMat q 0 0 = 1 := by rw [h]; simp
    have e11 : rotMat q 1 1 = 1 := by rw [h]; simp
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
`SO(3)` (Euler decomposition), used in the proof of `rotHom_surjective`.  Stated as exact polynomial
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

/-- The `3 × 3` matrix of the rotation of `ℝ³` by angle `θ` about the `z`-axis (the `k`-axis, i.e.
the last coordinate). -/
noncomputable def Rz (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The `3 × 3` matrix of the rotation of `ℝ³` by angle `θ` about the `y`-axis (the `j`-axis, i.e.
the middle coordinate). -/
noncomputable def Ry (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]

/-- **Half-angle rotation, `z`-axis.** The half-angle quaternion `⟨cos (θ/2), 0, 0, sin (θ/2)⟩`
conjugates to the full-angle `z`-rotation `Rz θ`, via the double-angle identities
`cos²(θ/2) - sin²(θ/2) = cos θ` and `2 cos(θ/2) sin(θ/2) = sin θ`. -/
lemma rotMat_zAxis_half (θ : ℝ) :
    rotMat (⟨Real.cos (θ / 2), 0, 0, Real.sin (θ / 2)⟩ : ℍ[ℝ]) = Rz θ := by
  have hθ : (2 : ℝ) * (θ / 2) = θ := by ring
  have hcos : Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    have h := Real.cos_two_mul' (θ / 2); rw [hθ] at h; exact h.symm
  have hsin : 2 * Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
    have h := Real.sin_two_mul (θ / 2); rw [hθ] at h; rw [h]; ring
  have hone : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  rw [rotMat_zAxis, Rz, hcos, hsin, hone]

/-- **Half-angle rotation, `y`-axis.** The half-angle quaternion `⟨cos (θ/2), 0, sin (θ/2), 0⟩`
conjugates to the full-angle `y`-rotation `Ry θ`. -/
lemma rotMat_yAxis_half (θ : ℝ) :
    rotMat (⟨Real.cos (θ / 2), 0, Real.sin (θ / 2), 0⟩ : ℍ[ℝ]) = Ry θ := by
  have hθ : (2 : ℝ) * (θ / 2) = θ := by ring
  have hcos : Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    have h := Real.cos_two_mul' (θ / 2); rw [hθ] at h; exact h.symm
  have hsin : 2 * Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
    have h := Real.sin_two_mul (θ / 2); rw [hθ] at h; rw [h]; ring
  have hone : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  rw [rotMat_yAxis, Ry, hcos, hsin, hone]

/-- Every point on the unit circle is `(cos θ, sin θ)` for some real angle `θ`. -/
private lemma exists_cos_sin_eq {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = x ∧ Real.sin θ = y := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz_def
  have hns : Complex.normSq z = 1 := by rw [hz_def, Complex.normSq_add_mul_I, h]
  have hnorm : ‖z‖ = 1 := by rw [Complex.norm_def, hns, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hnorm; simp at hnorm
  have hre : z.re = x := by rw [hz_def]; simp
  have him : z.im = y := by rw [hz_def]; simp
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hre, hnorm, div_one]
  · rw [Complex.sin_arg, him, hnorm, div_one]

/-- Two reals whose squares sum to zero are both zero. -/
private lemma sq_add_sq_eq_zero {a b : ℝ} (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 :=
  ⟨sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a)),
   sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))⟩

set_option maxHeartbeats 1000000 in
/-- **Euler `Z-Y-Z` decomposition of `SO(3)`.** Every special orthogonal `3 × 3` real matrix is a
product of a rotation about the `z`-axis, one about the `y`-axis, and one about the `z`-axis. This
is the classical existence of Euler angles; it is the remaining analytic input to
`rotHom_surjective`.

Proof: the third column `(R 0 2, R 1 2, R 2 2)` is a unit vector (columns of an orthogonal matrix
are orthonormal), so `|R 2 2| ≤ 1`; set `β := arccos (R 2 2)` so `cos β = R 2 2` and `sin β ≥ 0`.
When `sin β ≠ 0`, take `cos α = R 0 2 / sin β`, `sin α = R 1 2 / sin β`, `cos γ = -(R 2 0) / sin β`,
`sin γ = R 2 1 / sin β`; the orthonormality relations plus the cofactor identities (`adjugate R = Rᵀ`
since `det R = 1`) pin down every entry of `Rz α * Ry β * Rz γ` to equal `R`. The degenerate cases
`R 2 2 = ±1` (`sin β = 0`) reduce the top-left `2×2` block to a plane rotation/reflection. -/
theorem so3_euler_zyz (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, R = Rz α * Ry β * Rz γ := by
  -- Unpack orthogonality (`R Rᵀ = 1 = Rᵀ R`) and `det R = 1`.
  rw [mem_specialOrthogonalGroup_iff] at hR
  obtain ⟨hOrthMem, hdet⟩ := hR
  have hRRt : R * Rᵀ = 1 := by have h := hOrthMem; rwa [mem_orthogonalGroup_iff] at h
  have hRtR : Rᵀ * R = 1 := by have h := hOrthMem; rwa [mem_orthogonalGroup_iff'] at h
  -- `adjugate R = Rᵀ` (since `det R = 1` and `R` is orthogonal): the cofactor relations.
  have hadj : Rᵀ = adjugate R := by
    calc Rᵀ = Rᵀ * (R * adjugate R) := by rw [mul_adjugate, hdet, one_smul, mul_one]
      _ = Rᵀ * R * adjugate R := by rw [Matrix.mul_assoc]
      _ = adjugate R := by rw [hRtR, Matrix.one_mul]
  rw [adjugate_fin_three] at hadj
  have hC00 : R 0 0 = R 1 1 * R 2 2 - R 1 2 * R 2 1 := by
    have h := congrFun (congrFun hadj 0) 0; simpa [Matrix.transpose_apply] using h
  have hC01 : R 0 1 = -(R 1 0 * R 2 2) + R 1 2 * R 2 0 := by
    have h := congrFun (congrFun hadj 1) 0; simpa [Matrix.transpose_apply] using h
  have hC02 : R 0 2 = R 1 0 * R 2 1 - R 1 1 * R 2 0 := by
    have h := congrFun (congrFun hadj 2) 0; simpa [Matrix.transpose_apply] using h
  have hC12 : R 1 2 = -(R 0 0 * R 2 1) + R 0 1 * R 2 0 := by
    have h := congrFun (congrFun hadj 2) 1; simpa [Matrix.transpose_apply] using h
  -- Orthonormality relations (row/column dot products).
  have hO02 : R 0 0 * R 2 0 + R 0 1 * R 2 1 + R 0 2 * R 2 2 = 0 := by
    have h := congrFun (congrFun hRRt 0) 2
    simpa [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply] using h
  have hO12 : R 1 0 * R 2 0 + R 1 1 * R 2 1 + R 1 2 * R 2 2 = 0 := by
    have h := congrFun (congrFun hRRt 1) 2
    simpa [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply] using h
  have hcol2 : R 0 2 ^ 2 + R 1 2 ^ 2 + R 2 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRtR 2) 2
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hrow2 : R 2 0 ^ 2 + R 2 1 ^ 2 + R 2 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRRt 2) 2
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hcol0 : R 0 0 ^ 2 + R 1 0 ^ 2 + R 2 0 ^ 2 = 1 := by
    have h := congrFun (congrFun hRtR 0) 0
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hrow0 : R 0 0 ^ 2 + R 0 1 ^ 2 + R 0 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRRt 0) 0
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  -- The four "off-block" entries of `Rz α · Ry β · Rz γ`, forced by orthonormality + cofactors.
  have key00 : R 0 0 * (R 2 0 ^ 2 + R 2 1 ^ 2) = -(R 0 2 * R 2 2 * R 2 0) - R 1 2 * R 2 1 := by
    linear_combination R 2 0 * hO02 + R 2 1 * hC12
  have key01 : R 0 1 * (R 2 0 ^ 2 + R 2 1 ^ 2) = R 1 2 * R 2 0 - R 0 2 * R 2 1 * R 2 2 := by
    linear_combination R 2 1 * hO02 - R 2 0 * hC12
  have key10 : R 1 0 * (R 2 0 ^ 2 + R 2 1 ^ 2) = R 0 2 * R 2 1 - R 1 2 * R 2 0 * R 2 2 := by
    linear_combination R 2 0 * hO12 - R 2 1 * hC02
  have key11 : R 1 1 * (R 2 0 ^ 2 + R 2 1 ^ 2) = -(R 0 2 * R 2 0) - R 1 2 * R 2 1 * R 2 2 := by
    linear_combination R 2 1 * hO12 + R 2 0 * hC02
  -- Set `β = arccos (R 2 2)`; `cos β = R 2 2`, `sin β ≥ 0`, `sin²β = 1 - (R 2 2)²`.
  have hb1 : -1 ≤ R 2 2 := by
    nlinarith [hcol2, sq_nonneg (R 0 2), sq_nonneg (R 1 2), sq_nonneg (R 2 2 + 1)]
  have hb2 : R 2 2 ≤ 1 := by
    nlinarith [hcol2, sq_nonneg (R 0 2), sq_nonneg (R 1 2), sq_nonneg (R 2 2 - 1)]
  set β : ℝ := Real.arccos (R 2 2) with hβ_def
  have hcb : Real.cos β = R 2 2 := by rw [hβ_def]; exact Real.cos_arccos hb1 hb2
  have hsb2 : Real.sin β ^ 2 = 1 - R 2 2 ^ 2 := by
    have h := Real.sin_sq_add_cos_sq β; rw [hcb] at h; linarith
  rcases eq_or_ne (Real.sin β) 0 with hs0 | hsne
  · -- Degenerate case `sin β = 0`: `R 2 2 = ±1`, and rows/cols `0,1` are `±e₃`.
    have h22sq : R 2 2 ^ 2 = 1 := by
      have : Real.sin β ^ 2 = 0 := by rw [hs0]; ring
      linarith [hsb2]
    obtain ⟨hz02, hz12⟩ :=
      sq_add_sq_eq_zero (show R 0 2 ^ 2 + R 1 2 ^ 2 = 0 by linarith [hcol2, h22sq])
    obtain ⟨hz20, hz21⟩ :=
      sq_add_sq_eq_zero (show R 2 0 ^ 2 + R 2 1 ^ 2 = 0 by linarith [hrow2, h22sq])
    have h22 : R 2 2 = 1 ∨ R 2 2 = -1 := by
      have h := h22sq; rw [pow_two] at h; exact mul_self_eq_one_iff.mp h
    rcases h22 with h22 | h22
    · -- `R 2 2 = 1`: the top-left `2×2` block is a plane rotation `Rz α`.
      have hcol0' : R 0 0 ^ 2 + R 1 0 ^ 2 = 1 := by
        have h := hcol0; rw [hz20] at h; simpa using h
      obtain ⟨α, hca, hsa⟩ := exists_cos_sin_eq hcol0'
      have e11 : R 0 0 = R 1 1 := by have h := hC00; rw [h22, hz12, hz21] at h; linear_combination h
      have e01 : R 0 1 = -R 1 0 := by have h := hC01; rw [h22, hz20] at h; linear_combination h
      refine ⟨α, β, 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Rz, Ry, mul_apply, Fin.sum_univ_three] <;>
        simp <;>
        (try simp only [hca, hsa, hcb, hs0, h22, hz02, hz12, hz20, hz21,
          Real.cos_zero])
      all_goals
        first
          | linear_combination e01
          | linear_combination -e01
          | linear_combination e11
          | linear_combination -e11
          | linear_combination (0 : ℝ)
    · -- `R 2 2 = -1`: the top-left block is a reflection; `Ry β = Ry π` supplies the sign.
      have hrow0' : R 0 0 ^ 2 + R 0 1 ^ 2 = 1 := by
        have h := hrow0; rw [hz02] at h; simpa using h
      obtain ⟨α, hca, hsa⟩ :=
        exists_cos_sin_eq (show (-R 0 0) ^ 2 + (-R 0 1) ^ 2 = 1 by linear_combination hrow0')
      have e11 : R 1 1 = -R 0 0 := by
        have h := hC00; rw [h22, hz12, hz21] at h; linear_combination h
      have e01 : R 0 1 = R 1 0 := by have h := hC01; rw [h22, hz20] at h; linear_combination h
      refine ⟨α, β, 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Rz, Ry, mul_apply, Fin.sum_univ_three] <;>
        simp <;>
        (try simp only [hca, hsa, hcb, hs0, h22, hz02, hz12, hz20, hz21,
          Real.cos_zero])
      all_goals
        first
          | linear_combination e01
          | linear_combination -e01
          | linear_combination e11
          | linear_combination -e11
          | linear_combination (0 : ℝ)
  · -- Non-degenerate case `sin β ≠ 0`: full Euler angles.
    have hsb2col : Real.sin β ^ 2 = R 0 2 ^ 2 + R 1 2 ^ 2 := by rw [hsb2]; linarith [hcol2]
    have hsb2row : Real.sin β ^ 2 = R 2 0 ^ 2 + R 2 1 ^ 2 := by rw [hsb2]; linarith [hrow2]
    have hunitα : (R 0 2 / Real.sin β) ^ 2 + (R 1 2 / Real.sin β) ^ 2 = 1 := by
      field_simp
      first | linear_combination hsb2col | linear_combination -hsb2col
    have hunitγ : (-(R 2 0) / Real.sin β) ^ 2 + (R 2 1 / Real.sin β) ^ 2 = 1 := by
      field_simp
      first | linear_combination hsb2row | linear_combination -hsb2row
    obtain ⟨α, hca, hsa⟩ := exists_cos_sin_eq hunitα
    obtain ⟨γ, hcg, hsg⟩ := exists_cos_sin_eq hunitγ
    refine ⟨α, β, γ, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Rz, Ry, mul_apply, Fin.sum_univ_three] <;>
      simp <;>
      (try simp only [hca, hsa, hcb, hcg, hsg]) <;>
      (try field_simp)
    all_goals
      first
        | linear_combination key00 + R 0 0 * hsb2row
        | linear_combination key01 + R 0 1 * hsb2row
        | linear_combination key10 + R 1 0 * hsb2row
        | linear_combination key11 + R 1 1 * hsb2row

/-- **Surjectivity of the quaternion cover.** Every rotation of Euclidean `ℝ³` is conjugation by a
unit quaternion: the classical statement that `SU(2) → SO(3)` is the (`2:1`) universal cover.

Given `R ∈ SO(3)`, the Euler decomposition `R = Rz α · Ry β · Rz γ` (`so3_euler_zyz`) lifts, via the
half-angle rotations and multiplicativity of `rotMat`, to the unit quaternion
`q = ⟨cos(α/2),0,0,sin(α/2)⟩ · ⟨cos(β/2),0,sin(β/2),0⟩ · ⟨cos(γ/2),0,0,sin(γ/2)⟩` with
`rotMat q = R`. -/
theorem rotHom_surjective : Function.Surjective rotHom := by
  intro R
  obtain ⟨α, β, γ, hR⟩ := so3_euler_zyz (R : Matrix (Fin 3) (Fin 3) ℝ) R.2
  set qz1 : ℍ[ℝ] := ⟨Real.cos (α / 2), 0, 0, Real.sin (α / 2)⟩ with hqz1
  set qy : ℍ[ℝ] := ⟨Real.cos (β / 2), 0, Real.sin (β / 2), 0⟩ with hqy
  set qz2 : ℍ[ℝ] := ⟨Real.cos (γ / 2), 0, 0, Real.sin (γ / 2)⟩ with hqz2
  have hnz1 : Quaternion.normSq qz1 = 1 := by
    rw [hqz1, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (α / 2)
  have hny : Quaternion.normSq qy = 1 := by
    rw [hqy, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (β / 2)
  have hnz2 : Quaternion.normSq qz2 = 1 := by
    rw [hqz2, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (γ / 2)
  set q : ℍ[ℝ] := qz1 * qy * qz2 with hq
  have hnq : Quaternion.normSq q = 1 := by
    rw [hq, normSq_mul, normSq_mul, hnz1, hny, hnz2]; ring
  refine ⟨⟨q, mem_unitary_iff_normSq.mpr hnq⟩, ?_⟩
  apply Subtype.ext
  rw [rotHom_coe]
  change rotMat q = (R : Matrix (Fin 3) (Fin 3) ℝ)
  rw [hq, rotMat_mul, rotMat_mul, hqz1, hqy, hqz2, rotMat_zAxis_half, rotMat_yAxis_half,
    rotMat_zAxis_half]
  exact hR.symm

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

/-! ### Part (b): `ℍ = End_{SU(2)}(V)` is a 4-dimensional division algebra

We model `End_ℝ(V)` as `Module.End ℝ (Fin 2 → ℂ)` and let `SU(2)` act by
`A ↦ (v ↦ A.mulVec v)` (`su2Act`, an `ℝ`-linear endomorphism, matrix-vector multiplication
being `ℂ`-linear).  The *commutant* `commutant` is the `ℝ`-subalgebra of endomorphisms
commuting with every `su2Act A`, the endomorphisms of `V = ℂ²` as a real `SU(2)`-representation.
Being a centralizer, it is automatically closed under composition and contains the real scalars.

* **Division algebra** (`commutant_isUnit_of_ne_zero`): every nonzero `f ∈ commutant` is
  invertible.  Schur-style: `ker f` and `range f` are `SU(2)`-invariant, so by real
  irreducibility (part (a)) a nonzero `f` has `ker f = ⊥` and `range f = ⊤`, hence is bijective,
  with inverse again in the commutant.
* **4-dimensional** (`finrank_commutant`): evaluation at `e₀ = (1,0)` is an `ℝ`-linear
  isomorphism `commutant ≃ ℂ² = ℝ⁴`.  Injectivity is again real irreducibility (a commuting map
  killing `e₀` kills its whole `SU(2)`-orbit, hence is `0`); surjectivity is witnessed by the
  explicit basis `1, i, j, k` of `commutant`, where `i : v ↦ I • v`, `j : v ↦ J·conj v`,
  `k = i ∘ j` (`J = !![0,-1;1,0]`), whose values at `e₀` are the standard real basis
  `(1,0), (I,0), (0,1), (0,I)` of `ℂ²`. -/

section PartB

/-- The standard basis vector `e₀ = (1, 0) ∈ ℂ²`. -/
private def e0 : Fin 2 → ℂ := ![1, 0]

private lemma e0_ne_zero : e0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [e0] at h0

/-- The `SU(2)` action on `V = ℂ²` as an `ℝ`-linear endomorphism `v ↦ A.mulVec v`. -/
noncomputable def su2Act (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Module.End ℝ (Fin 2 → ℂ) :=
  (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ)).restrictScalars ℝ

@[simp] lemma su2Act_apply (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    su2Act A v = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v := by
  simp [su2Act]

/-- **Part (b), the commutant.** The `ℝ`-subalgebra of `End_ℝ(ℂ²)` of endomorphisms commuting
with the `SU(2)` action, the endomorphisms of `V = ℂ²` as a real representation.  As a
centralizer it is automatically closed under composition (multiplication) and contains the real
scalars. -/
noncomputable def commutant : Subalgebra ℝ (Module.End ℝ (Fin 2 → ℂ)) :=
  Subalgebra.centralizer ℝ (Set.range su2Act)

lemma mem_commutant_iff {f : Module.End ℝ (Fin 2 → ℂ)} :
    f ∈ commutant ↔
      ∀ (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ),
        f ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v)
          = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec (f v) := by
  rw [commutant, Subalgebra.mem_centralizer_iff, Set.forall_mem_range]
  simp only [DFunLike.ext_iff, Module.End.mul_apply, su2Act_apply]
  exact ⟨fun h A v => (h A v).symm, fun h A v => (h A v).symm⟩

/-- `ker f` is `SU(2)`-invariant for `f` in the commutant. -/
lemma commutant_ker_invariant {f : Module.End ℝ (Fin 2 → ℂ)} (hf : f ∈ commutant)
    (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) (hv : v ∈ LinearMap.ker f) :
    (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at hv ⊢
  rw [(mem_commutant_iff.mp hf) A v, hv, Matrix.mulVec_zero]

/-- A commuting endomorphism killing `e₀` is zero (real irreducibility). -/
lemma eq_zero_of_apply_e0 {f : Module.End ℝ (Fin 2 → ℂ)} (hf : f ∈ commutant)
    (h0 : f e0 = 0) : f = 0 := by
  rcases real_irreducible (LinearMap.ker f)
      (fun A v hv => commutant_ker_invariant hf A v hv) with h | h
  · exfalso
    have hmem : e0 ∈ LinearMap.ker f := LinearMap.mem_ker.mpr h0
    rw [h, Submodule.mem_bot] at hmem
    exact e0_ne_zero hmem
  · exact LinearMap.ker_eq_top.mp h

/-- **Part (b), division algebra.** Every nonzero element of the commutant is invertible: `ℍ` is a
division algebra.  By Schur: a nonzero commuting `f` has `SU(2)`-invariant `ker f` and
`range f`, which by real irreducibility (part (a)) are `⊥` and `⊤` respectively, so `f` is
bijective and its inverse is again in the commutant. -/
theorem commutant_isUnit_of_ne_zero (x : commutant) (hx : x ≠ 0) : IsUnit x := by
  set f : Module.End ℝ (Fin 2 → ℂ) := (x : Module.End ℝ (Fin 2 → ℂ)) with hfdef
  have hf : f ∈ commutant := x.2
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hfdef]
    exact h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hf0
  have hw0 : f w ≠ 0 := by simpa using hw
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    rcases real_irreducible (LinearMap.ker f)
        (fun A v hv => commutant_ker_invariant hf A v hv) with h | h
    · exact h
    · exfalso
      have : w ∈ LinearMap.ker f := h.symm ▸ Submodule.mem_top
      exact hw0 (LinearMap.mem_ker.mp this)
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    have hinv : ∀ (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ),
        v ∈ LinearMap.range f →
          (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ LinearMap.range f := by
      intro A v hv
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
      exact LinearMap.mem_range.mpr ⟨(A : Matrix (Fin 2) (Fin 2) ℂ).mulVec u,
        (mem_commutant_iff.mp hf) A u⟩
    rcases real_irreducible (LinearMap.range f) hinv with h | h
    · exfalso
      have hmem : f w ∈ LinearMap.range f := LinearMap.mem_range.mpr ⟨w, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hw0 hmem
    · exact h
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  let g : Module.End ℝ (Fin 2 → ℂ) := e.symm.toLinearMap
  have hg : g ∈ commutant := by
    rw [mem_commutant_iff]
    intro A v
    apply hinj
    rw [(mem_commutant_iff.mp hf) A (g v)]
    rw [show f (g ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v))
          = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v from e.apply_symm_apply _,
        show f (g v) = v from e.apply_symm_apply v]
  refine ⟨⟨x, ⟨g, hg⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change f * g = 1
    refine LinearMap.ext fun v => ?_
    exact e.apply_symm_apply v
  · apply Subtype.ext
    change g * f = 1
    refine LinearMap.ext fun v => ?_
    exact e.symm_apply_apply v

/-! #### The explicit basis `1, i, j, k` and 4-dimensionality -/

/-- `star (r • z) = r • star z` for a real scalar `r` and complex `z`. -/
private lemma star_realSmul (r : ℝ) (z : ℂ) : star (r • z) = r • star z := by
  rw [Complex.real_smul, Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal]

/-- The endomorphism `i : v ↦ I • v` (multiplication by `Complex.I`, `ℝ`-linear). -/
noncomputable def iMap : Module.End ℝ (Fin 2 → ℂ) where
  toFun v := Complex.I • v
  map_add' _ _ := smul_add _ _ _
  map_smul' r v := smul_comm Complex.I r v

@[simp] lemma iMap_apply (v : Fin 2 → ℂ) : iMap v = Complex.I • v := rfl

lemma iMap_mem : iMap ∈ commutant := by
  rw [mem_commutant_iff]
  intro A v
  simp only [iMap_apply, Matrix.mulVec_smul]

/-- The matrix `J = !![0,-1;1,0]` implementing the quaternionic structure `v ↦ J·conj v`. -/
noncomputable def Jmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The endomorphism `j : v ↦ J·conj(v)` (`ℝ`-linear, conjugate-`ℂ`-linear). -/
noncomputable def jMap : Module.End ℝ (Fin 2 → ℂ) where
  toFun v := Jmat.mulVec (star v)
  map_add' _ _ := by rw [star_add, Matrix.mulVec_add]
  map_smul' r v := by
    change Jmat.mulVec (star (r • v)) = r • Jmat.mulVec (star v)
    have hs : star (r • v) = r • star v := by
      funext i
      simp only [Pi.star_apply, Pi.smul_apply]
      exact star_realSmul r (v i)
    rw [hs, Matrix.mulVec_smul]

@[simp] lemma jMap_apply (v : Fin 2 → ℂ) : jMap v = Jmat.mulVec (star v) := rfl

/-- The two defining relations of an `SU(2)` matrix: `M 1 1 = conj (M 0 0)` and
`M 1 0 = -conj (M 0 1)` (unitarity plus `det = 1` via `adjugate M = Mᴴ`). -/
lemma su2_entries (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
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
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun hadj 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at h
    exact h.symm
  · have h := congrFun (congrFun hadj 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at h
    rw [h]; ring

/-- `star (A.mulVec v) = (A.map conj).mulVec (star v)`. -/
private lemma star_mulVec_eq (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    star (A.mulVec v) = (A.map (starRingEnd ℂ)).mulVec (star v) := by
  funext i
  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    star_add, star_mul', starRingEnd_apply]

/-- The quaternionic identity for `SU(2)`: `J · conj(A) = A · J`. -/
lemma su2_Jmat_comm (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Jmat * (A : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * Jmat := by
  obtain ⟨h11, h10⟩ := su2_entries A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Jmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, starRingEnd_apply] <;>
    simp [h11, h10]

lemma jMap_mem : jMap ∈ commutant := by
  rw [mem_commutant_iff]
  intro A v
  change Jmat.mulVec (star ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v))
      = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec (Jmat.mulVec (star v))
  rw [star_mulVec_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, su2_Jmat_comm]

/-- Evaluation at `e₀ = (1,0)`, as an `ℝ`-linear map `commutant → ℂ²`. -/
noncomputable def ev : commutant →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun x := (x : Module.End ℝ (Fin 2 → ℂ)) e0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ev_apply (x : commutant) : ev x = (x : Module.End ℝ (Fin 2 → ℂ)) e0 := rfl

lemma ev_injective : Function.Injective ev := by
  intro x y hxy
  have h0 : ((x : Module.End ℝ (Fin 2 → ℂ)) - y) e0 = 0 := by
    rw [LinearMap.sub_apply, ← ev_apply x, ← ev_apply y, hxy, sub_self]
  have hz : (x : Module.End ℝ (Fin 2 → ℂ)) - y = 0 :=
    eq_zero_of_apply_e0 (sub_mem x.2 y.2) h0
  exact Subtype.ext (sub_eq_zero.mp hz)

lemma ev_surjective : Function.Surjective ev := by
  intro w
  refine ⟨(w 0).re • (1 : commutant) + (w 0).im • ⟨iMap, iMap_mem⟩
      + (w 1).re • ⟨jMap, jMap_mem⟩
      + (w 1).im • ⟨iMap * jMap, mul_mem iMap_mem jMap_mem⟩, ?_⟩
  have ev1 : ev (1 : commutant) = ![1, 0] := rfl
  have evI : ev ⟨iMap, iMap_mem⟩ = ![Complex.I, 0] := by
    funext i; fin_cases i <;> simp [ev_apply, iMap_apply, e0]
  have evJ : ev ⟨jMap, jMap_mem⟩ = ![0, 1] := by
    funext i; fin_cases i <;>
      simp [ev_apply, jMap_apply, e0, Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have evK : ev ⟨iMap * jMap, mul_mem iMap_mem jMap_mem⟩ = ![0, Complex.I] := by
    funext i; fin_cases i <;>
      simp [ev_apply, Module.End.mul_apply, iMap_apply, jMap_apply, e0, Jmat,
        dotProduct, Fin.sum_univ_two]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, ev1, evI, evJ, evK]
  funext i
  fin_cases i <;> simp [Complex.real_smul, Complex.re_add_im]

/-- **Part (b), 4-dimensionality.** The commutant `ℍ = End_{SU(2)}(ℂ²)` is `4`-dimensional over
`ℝ`: evaluation at `e₀` is an `ℝ`-linear isomorphism onto `ℂ² = ℝ⁴`. -/
theorem finrank_commutant : Module.finrank ℝ commutant = 4 := by
  have hbij : Function.Bijective ev := ⟨ev_injective, ev_surjective⟩
  rw [(LinearEquiv.ofBijective ev hbij).finrank_eq]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

end PartB

end Etingof.Problem4_12_7
