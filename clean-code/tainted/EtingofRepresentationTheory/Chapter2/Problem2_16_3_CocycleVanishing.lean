import EtingofRepresentationTheory.Chapter2.Problem2_16_3_CocycleRecurrence


/-!
# Problem 2.16.3(b): imaginary cocycles vanish in characteristic zero

This file closes the scalar cocycle computation on the positive twisted loop algebra.  The
characteristic-zero hypothesis is essential: in imaginary layer `m`, the last recurrence
requires cancellation of `(m + 1 : k)`.

For an imaginary-weight cocycle `c`, its value on
`(loopFam base, loopFam (even m 2))` is the value of the cobounding functional on the unique
imaginary basis vector in layer `m`.  Jacobi with the base generator reduces all complementary
odd and even coefficients to two extreme deviations.  The recurrence from
`Problem2_16_3_CocycleRecurrence.lean`, together with skew-symmetry, makes the odd deviation an
arithmetic progression across each layer; cancellation of the layer number kills its common
difference.  Every supported basis coefficient therefore agrees with `imaginaryCoboundary`,
and bilinearity extends the equality from `loopBasis` to the whole loop algebra.
-/

namespace Etingof.Problem2_16_3

attribute [local instance] LieRing.ofAssociativeRing

section DeviationAlgebra

variable {k : Type*} [Field k] [CharZero k]

/-- The abstract scalar calculation behind the imaginary-layer recurrence. -/
private theorem deviation_eq_zero_of_recurrence
    (D E : ℕ → ℕ → k)
    (hD : ∀ a b, D a b = -D b a)
    (hE : ∀ a b, E a b = -E b a)
    (hrec : ∀ a b d,
      E (a + b) d = 2 * (D a (b + d + 1) - D (a + d + 1) b)) :
    (∀ a b, D a b = 0) ∧ ∀ a b, E a b = 0 := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hrec' : ∀ a b d,
      E (a + b) d = 2 * (D a (b + d + 1) + D b (a + d + 1)) := by
    intro a b d
    rw [hrec, hD (a + d + 1) b]
    ring
  have hstep : ∀ a d,
      D (a + 1) (d + 1) =
        D a (d + 2) + D 1 (a + d + 1) - D 0 (a + d + 2) := by
    intro a d
    have h₁ := hrec' a 1 d
    have h₂ := hrec' 0 (a + 1) d
    simp only [zero_add] at h₂
    have h := h₁.symm.trans h₂
    norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h
    linear_combination -h
  have haffine : ∀ a d,
      D a (d + 1) = D 0 (a + d + 1) +
        (a : k) * (D 1 (a + d) - D 0 (a + d + 1)) := by
    intro a
    induction a with
    | zero =>
        intro d
        simp
    | succ a ih =>
        intro d
        rw [show a + 1 = a + 1 by rfl, hstep a d, ih (d + 1)]
        push_cast
        ring_nf
  have hlayer : ∀ q : ℕ,
      D 0 (q + 1) = 0 ∧ D 1 q - D 0 (q + 1) = 0 := by
    intro q
    let z := D 0 (q + 1)
    let r := D 1 q - z
    have haf : D q 1 = z + (q : k) * r := by
      simpa [z, r] using haffine q 0
    have hs := hD 1 q
    have hzr : 2 * z + ((q + 1 : ℕ) : k) * r = 0 := by
      dsimp [r]
      push_cast
      linear_combination hs - haf
    have he := hE 0 q
    have hleft := hrec' 0 0 q
    have hright := hrec' q 0 0
    have heq : 4 * z = -(2 * (D q 1 + z)) := by
      calc
        4 * z = E 0 q := by
          rw [hleft]
          simp only [zero_add]
          dsimp [z]
          ring
        _ = -E q 0 := he
        _ = -(2 * (D q 1 + z)) := by
          simpa [z] using congrArg Neg.neg hright
    have hertwo : 2 * (4 * z + (q : k) * r) = 0 := by
      linear_combination heq - 2 * haf
    have her : 4 * z + (q : k) * r = 0 :=
      (mul_eq_zero.mp hertwo).resolve_left h2
    have hrmul : (((q + 2 : ℕ) : k)) * r = 0 := by
      push_cast at hzr ⊢
      linear_combination 2 * hzr - her
    have hn : ((q + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hr : r = 0 := (mul_eq_zero.mp hrmul).resolve_left hn
    have hzmul : 2 * z = 0 := by simpa [hr] using hzr
    have hz : z = 0 := (mul_eq_zero.mp hzmul).resolve_left h2
    exact ⟨by simpa [z] using hz, by simpa [r, z] using hr⟩
  have hDzero : ∀ a b, D a b = 0 := by
    intro a b
    obtain rfl | ha := a
    · obtain rfl | hb := b
      · have hs := hD 0 0
        have hz : 2 * D 0 0 = 0 := by linear_combination hs
        exact (mul_eq_zero.mp hz).resolve_left h2
      · exact (hlayer hb).1
    · obtain rfl | hb := b
      · rw [hD, (hlayer ha).1, neg_zero]
      · calc
          D (ha + 1) (hb + 1) =
              D 0 (ha + hb + 2) + ((ha + 1 : ℕ) : k) *
                (D 1 (ha + hb + 1) - D 0 (ha + hb + 2)) := by
            have haf := haffine (ha + 1) hb
            rw [show ha + 1 + hb + 1 = ha + hb + 2 by omega,
              show ha + 1 + hb = ha + hb + 1 by omega] at haf
            exact haf
          _ = 0 := by rw [(hlayer (ha + hb + 1)).2, (hlayer (ha + hb + 1)).1]; simp
  refine ⟨hDzero, ?_⟩
  intro a b
  have h := hrec a 0 b
  simp only [Nat.add_zero] at h
  rw [hDzero, hDzero] at h
  simpa using h

end DeviationAlgebra

section CoefficientReduction

variable {k : Type*} [Field k]

private theorem lie_loopFam_base_odd_one (a : ℕ) :
    ⁅loopFam k .base, loopFam k (.odd a 1)⁆ = (2 : k) • loopFam k (.odd a 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * a + 1) (gone k 1)⁆ =
    (2 : k) • emb k (2 * a + 1) (gone k 0)
  rw [emb_lie, lie_gzero0_gone1, map_smul]
  rw [zero_add]

private theorem lie_loopFam_base_odd_two (a : ℕ) :
    ⁅loopFam k .base, loopFam k (.odd a 2)⁆ = (-3 : k) • loopFam k (.odd a 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * a + 1) (gone k 2)⁆ =
    (-3 : k) • emb k (2 * a + 1) (gone k 1)
  rw [emb_lie, lie_gzero0_gone2, map_smul]
  rw [zero_add]

private theorem lie_loopFam_base_odd_three (a : ℕ) :
    ⁅loopFam k .base, loopFam k (.odd a 3)⁆ = loopFam k (.odd a 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * a + 1) (gone k 3)⁆ =
    emb k (2 * a + 1) (gone k 2)
  rw [emb_lie, lie_gzero0_gone3]
  simp

private theorem lie_loopFam_base_odd_four (a : ℕ) :
    ⁅loopFam k .base, loopFam k (.odd a 4)⁆ = -loopFam k (.odd a 3) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * a + 1) (gone k 4)⁆ =
    -emb k (2 * a + 1) (gone k 3)
  rw [emb_lie, lie_gzero0_gone4, map_smul]
  simp

private theorem lie_loopFam_odd_one_four (a b : ℕ) :
    ⁅loopFam k (.odd a 1), loopFam k (.odd b 4)⁆ =
      loopFam k (.even (a + b) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * a + 1) (gone k 1), emb k (2 * b + 1) (gone k 4)⁆ =
    emb k (2 * (a + b) + 2) (gzero k 2)
  rw [emb_lie, lie_gone1_gone4]
  simp only [one_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]

private theorem lie_loopFam_odd_two_three (a b : ℕ) :
    ⁅loopFam k (.odd a 2), loopFam k (.odd b 3)⁆ =
      (-3 : k) • loopFam k (.even (a + b) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * a + 1) (gone k 2), emb k (2 * b + 1) (gone k 3)⁆ =
    (-3 : k) • emb k (2 * (a + b) + 2) (gzero k 2)
  rw [emb_lie]
  have h : ⁅gone k 2, gone k 3⁆ = (-3 : k) • gzero k 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gone, gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
        Matrix.sub_apply, Matrix.smul_apply] <;> ring
  rw [h, map_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]

/-- The next odd complementary coefficient is determined by the extreme one. -/
private theorem IsTwoCocycle.odd_one_three
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b : ℕ) :
    c (loopFam k (.odd a 1)) (loopFam k (.odd b 3)) =
      2 * c (loopFam k (.odd a 0)) (loopFam k (.odd b 4)) -
        imaginaryBaseValue c (a + b) := by
  have h := hc.jacobi (loopFam k .base) (loopFam k (.odd a 1))
    (loopFam k (.odd b 4))
  rw [lie_loopFam_base_odd_one, lie_loopFam_odd_one_four,
    ← lie_skew (loopFam k (.odd b 4)) (loopFam k .base),
    lie_loopFam_base_odd_four, neg_neg, hc.smul_left] at h
  rw [hc.skew (loopFam k (.even (a + b) 2)) (loopFam k .base)] at h
  rw [hc.skew (loopFam k (.odd b 3)) (loopFam k (.odd a 1))] at h
  dsimp [imaginaryBaseValue]
  simp only [smul_eq_mul] at h
  linear_combination -h

/-- The middle odd coefficient is six times the extreme deviation. -/
private theorem IsTwoCocycle.odd_two_two_eq_deviation
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b : ℕ) :
    c (loopFam k (.odd a 2)) (loopFam k (.odd b 2)) =
      6 * oddImaginaryDeviation c a b := by
  have h := hc.jacobi (loopFam k .base) (loopFam k (.odd a 2))
    (loopFam k (.odd b 3))
  rw [lie_loopFam_base_odd_two, lie_loopFam_odd_two_three,
    ← lie_skew (loopFam k (.odd b 3)) (loopFam k .base),
    lie_loopFam_base_odd_three, hc.smul_left, hc.smul_left, hc.neg_left] at h
  rw [hc.skew (loopFam k (.even (a + b) 2)) (loopFam k .base),
    hc.skew (loopFam k (.odd b 2)) (loopFam k (.odd a 2)),
    hc.odd_one_three a b] at h
  dsimp [oddImaginaryDeviation, imaginaryBaseValue] at h ⊢
  simp only [neg_neg] at h
  linear_combination h

private theorem IsTwoCocycle.odd_deviation_skew
    [CharZero k]
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b : ℕ) :
    oddImaginaryDeviation c a b = -oddImaginaryDeviation c b a := by
  have hab := hc.odd_two_two_eq_deviation a b
  have hba := hc.odd_two_two_eq_deviation b a
  have hs := hc.skew (loopFam k (.odd a 2)) (loopFam k (.odd b 2))
  rw [hab, hba] at hs
  have h6 : (6 : k) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ h6)
  simpa [mul_neg] using hs

private theorem IsTwoCocycle.even_deviation_skew
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b : ℕ) :
    evenImaginaryDeviation c a b = -evenImaginaryDeviation c b a := by
  rw [← hc.even_middle_eq_deviation a b, ← hc.even_middle_eq_deviation b a]
  exact hc.skew _ _

/-- Both extreme deviations vanish in characteristic zero. -/
private theorem IsTwoCocycle.imaginary_deviations_eq_zero
    [CharZero k]
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) :
    (∀ a b, oddImaginaryDeviation c a b = 0) ∧
      ∀ a b, evenImaginaryDeviation c a b = 0 :=
  deviation_eq_zero_of_recurrence (oddImaginaryDeviation c) (evenImaginaryDeviation c)
    hc.odd_deviation_skew hc.even_deviation_skew hc.imaginary_deviation_recurrence

private theorem IsTwoCocycle.odd_complementary
    [CharZero k]
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c)
    (a b : ℕ) (i : Fin 5) :
    c (loopFam k (.odd a i)) (loopFam k (.odd b i.rev)) =
      oddImaginaryCoeff k i * imaginaryBaseValue c (a + b) := by
  have hodd := hc.imaginary_deviations_eq_zero.1
  fin_cases i
  · change c (loopFam k (.odd a 0)) (loopFam k (.odd b 4)) =
      (1 : k) * imaginaryBaseValue c (a + b)
    have h := hodd a b
    dsimp [oddImaginaryDeviation] at h
    simpa using sub_eq_zero.mp h
  · change c (loopFam k (.odd a 1)) (loopFam k (.odd b 3)) =
      (1 : k) * imaginaryBaseValue c (a + b)
    rw [hc.odd_one_three]
    have h := hodd a b
    dsimp [oddImaginaryDeviation] at h
    rw [sub_eq_zero.mp h]
    ring
  · change c (loopFam k (.odd a 2)) (loopFam k (.odd b 2)) =
      (0 : k) * imaginaryBaseValue c (a + b)
    rw [hc.odd_two_two_eq_deviation, hodd]
    ring
  · change c (loopFam k (.odd a 3)) (loopFam k (.odd b 1)) =
      (-1 : k) * imaginaryBaseValue c (a + b)
    rw [hc.skew, hc.odd_one_three]
    have h := hodd b a
    dsimp [oddImaginaryDeviation] at h
    rw [sub_eq_zero.mp h]
    rw [Nat.add_comm]
    ring
  · change c (loopFam k (.odd a 4)) (loopFam k (.odd b 0)) =
      (-1 : k) * imaginaryBaseValue c (a + b)
    rw [hc.skew]
    have h := hodd b a
    dsimp [oddImaginaryDeviation] at h
    rw [sub_eq_zero.mp h]
    rw [Nat.add_comm]
    ring

private theorem IsTwoCocycle.even_complementary
    [CharZero k]
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c)
    (a b : ℕ) (i : Fin 3) :
    c (loopFam k (.even a i)) (loopFam k (.even b i.rev)) =
      evenImaginaryCoeff k i * imaginaryBaseValue c (a + b + 1) := by
  have heven := hc.imaginary_deviations_eq_zero.2
  fin_cases i
  · change c (loopFam k (.even a 0)) (loopFam k (.even b 2)) =
      (1 : k) * imaginaryBaseValue c (a + b + 1)
    have h := heven a b
    dsimp [evenImaginaryDeviation] at h
    simpa using sub_eq_zero.mp h
  · change c (loopFam k (.even a 1)) (loopFam k (.even b 1)) =
      (0 : k) * imaginaryBaseValue c (a + b + 1)
    rw [hc.even_middle_eq_deviation, heven]
    ring
  · change c (loopFam k (.even a 2)) (loopFam k (.even b 0)) =
      (-1 : k) * imaginaryBaseValue c (a + b + 1)
    rw [hc.skew]
    have h := heven b a
    dsimp [evenImaginaryDeviation] at h
    rw [sub_eq_zero.mp h]
    rw [show b + a + 1 = a + b + 1 by omega]
    ring

end CoefficientReduction

section Support

variable {k : Type*} [Field k]

/-- The imaginary functional kills a homogeneous component outside the imaginary ray. -/
private theorem imaginaryFunctional_eq_zero_of_lDeg
    (h2 : (2 : k) ≠ 0) (s : ℕ → k) (p : ℕ × ℕ)
    (hp : ∀ m : ℕ, p ≠ (2 * m + 2, 4 * m + 4))
    {v : loopPos k} (hv : v ∈ lDeg k p) :
    imaginaryFunctional h2 s v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨I, hI, rfl⟩ := hv
      rw [imaginaryFunctional_loopFam]
      cases I with
      | base => rfl
      | odd m i => rfl
      | even m i =>
          by_cases hi : i = 1
          · subst i
            exfalso
            apply hp m
            rw [← hI]
            simp [Fin.rev]
          · simp [imaginaryBasisValue, hi]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- The normal-form coboundary itself has imaginary weight. -/
theorem hasImaginaryWeight_imaginaryCoboundary
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (s : ℕ → k) :
    HasImaginaryWeight (imaginaryCoboundary h2 s) := by
  intro I J hIJ
  rw [imaginaryCoboundary]
  exact imaginaryFunctional_eq_zero_of_lDeg h2 s _ hIJ
    (lie_loopFam_mem_lDeg h2 h3 h5 I J)

end Support

section Assembly

variable {k : Type*} [Field k] [CharZero k]

/-- Bundle a bilinear cocycle as a linear map into linear maps. -/
private noncomputable def IsTwoCocycle.toLinearMap
    {L M : Type*} [LieRing L] [LieAlgebra k L] [AddCommGroup M] [Module k M]
    {c : L → L → M} (hc : IsTwoCocycle k c) : L →ₗ[k] L →ₗ[k] M where
  toFun a :=
    { toFun := c a
      map_add' := hc.add_right a
      map_smul' := fun r b => by simpa using hc.smul_right r a b }
  map_add' a b := LinearMap.ext fun d => hc.add_left a b d
  map_smul' r a := LinearMap.ext fun b => hc.smul_left r a b

private theorem IsTwoCocycle.eq_imaginaryCoboundary_loopFam
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c)
    (hw : HasImaginaryWeight c) (I J : LoopIdx) :
    c (loopFam k I) (loopFam k J) =
      imaginaryCoboundary (by norm_num) (imaginaryBaseValue c)
        (loopFam k I) (loopFam k J) := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  let h3 : (3 : k) ≠ 0 := by norm_num
  let h5 : (5 : k) ≠ 0 := by norm_num
  change c (loopFam k I) (loopFam k J) =
    imaginaryCoboundary h2 (imaginaryBaseValue c) (loopFam k I) (loopFam k J)
  by_cases hIJ : IsImaginaryPair I J
  · rw [isImaginaryPair_iff] at hIJ
    rcases hIJ with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩ |
      ⟨a, b, i, j, rfl, rfl, hij⟩ | ⟨a, b, i, j, rfl, rfl, hij⟩
    · simp [imaginaryBaseValue]
    · rw [hc.skew]
      have hcb := (isTwoCoboundary_imaginaryCoboundary h2
        (imaginaryBaseValue c)).isTwoCocycle.skew
        (loopFam k (.even m 2)) (loopFam k .base)
      rw [hcb]
      simp [imaginaryBaseValue]
    · rw [fin5_eq_rev_of_add_eq_four hij, hc.odd_complementary,
        imaginaryCoboundary_odd_of_add_eq_four h2 _ a b i i.rev i.add_rev_cast]
    · rw [fin3_eq_rev_of_add_eq_two hij, hc.even_complementary,
        imaginaryCoboundary_even_of_add_eq_two h2 _ a b i i.rev i.add_rev_cast]
  · rw [hw.eq_zero_of_not_isImaginaryPair hIJ]
    exact (HasImaginaryWeight.eq_zero_of_not_isImaginaryPair
      (hasImaginaryWeight_imaginaryCoboundary h2 h3 h5 _) hIJ).symm

/-- Every imaginary-weight scalar 2-cocycle on the positive loop algebra is the canonical
imaginary coboundary in characteristic zero. -/
theorem IsTwoCocycle.eq_imaginaryCoboundary
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c)
    (hw : HasImaginaryWeight c) (a b : loopPos k) :
    c a b = imaginaryCoboundary (by norm_num)
      (imaginaryBaseValue c) a b := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  let cb := imaginaryCoboundary h2 (imaginaryBaseValue c)
  have hcb : IsTwoCocycle k cb :=
    (isTwoCoboundary_imaginaryCoboundary h2 (imaginaryBaseValue c)).isTwoCocycle
  have hmaps : hc.toLinearMap = hcb.toLinearMap := by
    apply (loopBasis k h2).ext
    intro I
    apply (loopBasis k h2).ext
    intro J
    simpa [IsTwoCocycle.toLinearMap, cb, loopBasis_apply] using
      hc.eq_imaginaryCoboundary_loopFam hw I J
  change c a b = cb a b
  exact congrArg (fun F : loopPos k →ₗ[k] loopPos k →ₗ[k] k => F a b) hmaps

/-- **Characteristic-zero imaginary cohomology vanishing.** Every scalar 2-cocycle on
`loopPos` supported in the imaginary bidegrees is a coboundary. -/
theorem twoCocycle_isTwoCoboundary
    (c : loopPos k → loopPos k → k) (hc : IsTwoCocycle k c)
    (hw : HasImaginaryWeight c) : IsTwoCoboundary k c := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  refine ⟨imaginaryFunctional h2 (imaginaryBaseValue c), ?_⟩
  intro a b
  exact hc.eq_imaginaryCoboundary hw a b

/-! ## Characteristic-zero Gabber--Kac and the explicit basis of `𝔤₄` -/

/-- Every layer defect vanishes in characteristic zero. -/
@[simp] theorem topDefect_eq_zero (m : ℕ) : topDefect k m = 0 :=
  topDefect_eq_zero_of_twoCocycle (by norm_num) (by norm_num) (by norm_num)
    (fun c hc hw ↦ twoCocycle_isTwoCoboundary c hc hw) m

/-- The full five-term odd-layer invariant in every odd degree, in characteristic zero. -/
theorem oddLayer_topOdd_charZero (m : ℕ) :
    OddLayer k (topOdd k m) (evenTower k m) :=
  oddLayer_topOdd (by norm_num) (by norm_num) (by norm_num) topDefect_eq_zero m

/-- The loop realization of `𝔤₄` is injective in characteristic zero. -/
theorem gbar_injective : Function.Injective (gbar k) :=
  (gbar_injective_iff_topDefect_eq_zero (by norm_num) (by norm_num) (by norm_num)).2
    topDefect_eq_zero

/-- The explicit `LoopIdx`-family spans `𝔤₄` in characteristic zero. -/
theorem span_range_loopFam₄_eq_top_charZero :
    Submodule.span k (Set.range (loopFam₄ k)) = ⊤ :=
  span_range_loopFam₄_eq_top (by norm_num) (by norm_num) (by norm_num) topDefect_eq_zero

/-- **The explicit basis requested in Problem 2.16.3(b).** It consists of `ȳ`, then five
vectors in every odd `t`-degree and three vectors in every positive even `t`-degree. -/
noncomputable def gFourBasis : Module.Basis LoopIdx k (g k 4) :=
  Module.Basis.mk (linearIndependent_loopFam₄ (by norm_num) (by norm_num))
    span_range_loopFam₄_eq_top_charZero.ge

/-- The basis vector is the corresponding lifted loop-family element. -/
@[simp] theorem gFourBasis_apply (I : LoopIdx) : gFourBasis (k := k) I = loopFam₄ k I :=
  Module.Basis.mk_apply _ _ _

/-- The explicit basis is infinite, recovering the infinite-dimensionality of `𝔤₄`. -/
theorem not_finiteDimensional_g_four_of_basis : ¬ Module.Finite k (g k 4) := by
  letI : Infinite LoopIdx := Infinite.of_injective (fun m : ℕ ↦ LoopIdx.odd m 0) <| by
    intro a b h
    cases h
    rfl
  exact Module.not_finite_of_infinite_basis (gFourBasis (k := k))

/-- The loop realization as an isomorphism of Lie algebras in characteristic zero. -/
noncomputable def gbarLieEquiv : g k 4 ≃ₗ⁅k⁆ loopPos k where
  toFun := gbarL k
  map_add' := map_add (gbarL k)
  map_smul' := map_smul (gbarL k)
  map_lie' := fun {u v} ↦ gbarL_lie u v
  invFun := loopSect (by norm_num)
  left_inv u := by
    apply gbar_injective (k := k)
    rw [gbar_loopSect (by norm_num) (by norm_num), coe_gbarL]
  right_inv := gbarL_loopSect (by norm_num) (by norm_num)

/-- The Lie equivalence agrees pointwise with the loop realization. -/
@[simp] theorem gbarLieEquiv_apply (u : g k 4) :
    gbarLieEquiv (k := k) u = gbarL k u := by
  change gbarL k u = gbarL k u
  rfl

end Assembly

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.gFourBasis
  Etingof.Problem2_16_3.gbarLieEquiv
