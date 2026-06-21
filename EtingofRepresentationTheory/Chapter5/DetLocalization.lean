import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.PolynomialRepEmbedding

/-!
# The determinant localization `A[det⁻¹]` and its faithful functions-on-GL model

This file builds the **faithful functions-on-`GL`** model of the localization
`A[det⁻¹]` used by the det⁻¹-elimination kernel lemma (issue #4694, route doc
`progress/kernel-lemma-K-route.md`).

Let `A := MvPolynomial (Fin N × Fin N) k` (the coordinate ring `k[Xᵢⱼ]`) and
`detPoly := Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)` the generic
determinant polynomial (the polynomial whose `eval` at a matrix is its
determinant). We work over an infinite field `k`.

The localization `A[det⁻¹] = Localization.Away detPoly` carries a ring hom into
the function ring `GL_N → k`, induced from the evaluation hom
`evalGLHom : A →+* (GL_N → k)`, `a ↦ (g ↦ eval g a)`. Because `detPoly`
evaluates to `det g ≠ 0` at every `g ∈ GL_N`, its image is a unit, so the
localization universal property (`IsLocalization.Away.lift`) produces
`evalGLAway : A[det⁻¹] →+* (GL_N → k)`. This map is **injective**: a localization
element `Q / detⁿ` vanishes as a function on `GL_N` iff `Q` vanishes on `GL_N`
iff `Q = 0` (by `MvPolynomial.eq_of_eval_eq_on_gl`, the Zariski-density of
`GL_N`).

Finally `evalAtGL` (Definition 5.23.1, the evaluation of `k[Xᵢⱼ, D]` at a matrix
with `D ↦ det⁻¹`) **factors through** `A[det⁻¹]` via the coordinate hom sending
`Xᵢⱼ ↦ Xᵢⱼ` and `D ↦ detPoly⁻¹`.

These are exactly the moves the kernel-lemma assembly needs to pass between
honest localization elements and functions on `GL`.

## The det-power normal form

Every element of `A[det⁻¹]` is `Q · det⁻ʳ` for a polynomial `Q` and an exponent
`r` (`exists_invSelf_normalForm`). Defining `detExp f` as the **least** such `r`
(`Nat.find`) gives the reduced normal form: at the minimal exponent the numerator
`Q` is coprime to `det` (`not_dvd_num_of_detExp_pos`), the pair `(detExp f, Q)`
is unique (`reduced_normalForm_unique`), and `detExp f = 0 ↔ f` is an honest
polynomial (`detExp_eq_zero_iff`, the predicate the det-power filtration
`A_r := det⁻ʳ · A` keys on). The whole development rests only on injectivity of
`A → A[det⁻¹]` (`detPoly` a nonzerodivisor) and `det · det⁻¹ = 1`; the
`detPoly`-cancellation is done by the minimal-exponent definition, so primeness
of `detPoly` is not needed here.
-/

namespace Etingof.DetLocalization

variable {k : Type*} [Field k] {N : ℕ}

/-- The generic determinant polynomial `det(Xᵢⱼ)` in `A = k[Xᵢⱼ]`: the
polynomial whose evaluation at a matrix is the matrix's determinant. -/
noncomputable def detPoly (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)

/-- `detPoly` is nonzero (`Matrix.det_mvPolynomialX_ne_zero`). -/
theorem detPoly_ne_zero : detPoly k N ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin N) k

/-- The powers of `detPoly` are non-zero-divisors: `A` is an integral domain and
`detPoly ≠ 0`. -/
theorem powers_detPoly_le_nonZeroDivisors :
    Submonoid.powers (detPoly k N) ≤ nonZeroDivisors (MvPolynomial (Fin N × Fin N) k) := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n detPoly_ne_zero)

/-- The evaluation ring hom `A →+* (GL_N → k)`, `p ↦ (g ↦ eval g p)`, where
`eval g` substitutes `Xᵢⱼ ↦ gᵢⱼ`. -/
noncomputable def evalGLHom :
    MvPolynomial (Fin N × Fin N) k →+* (Matrix.GeneralLinearGroup (Fin N) k → k) :=
  Pi.ringHom fun g =>
    MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)

@[simp]
theorem evalGLHom_apply (p : MvPolynomial (Fin N × Fin N) k)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    evalGLHom p g =
      MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p :=
  rfl

/-- Evaluating the determinant polynomial at `g ∈ GL_N` gives `det g`. -/
theorem evalGLHom_detPoly_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    evalGLHom (detPoly k N) g = (g : Matrix (Fin N) (Fin N) k).det := by
  rw [evalGLHom_apply, detPoly,
    (MvPolynomial.eval
      (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)).map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

/-- `evalGLHom` is injective: two polynomials evaluating equally at every
`g ∈ GL_N` are equal, by Zariski-density of `GL_N`
(`MvPolynomial.eq_of_eval_eq_on_gl`). Needs `k` infinite. -/
theorem evalGLHom_injective [Infinite k] :
    Function.Injective (evalGLHom (k := k) (N := N)) := by
  intro p q h
  apply MvPolynomial.eq_of_eval_eq_on_gl
  intro g
  exact congrFun h g

/-- The image of `detPoly` under `evalGLHom` is a unit in `GL_N → k`: at each
`g ∈ GL_N` it equals the unit `det g`. -/
theorem isUnit_evalGLHom_detPoly :
    IsUnit (evalGLHom (detPoly k N)) := by
  rw [Pi.isUnit_iff]
  intro g
  rw [evalGLHom_detPoly_apply]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)

/-- The induced ring hom `A[det⁻¹] →+* (GL_N → k)` from the localization
universal property: `evalGLHom detPoly` is a unit, so `evalGLHom` lifts. -/
noncomputable def evalGLAway :
    Localization.Away (detPoly k N) →+* (Matrix.GeneralLinearGroup (Fin N) k → k) :=
  IsLocalization.Away.lift (g := evalGLHom) (detPoly k N) isUnit_evalGLHom_detPoly

/-- `evalGLAway` factors `evalGLHom`: it agrees with `evalGLHom` on the image of
`A` in the localization. -/
@[simp]
theorem evalGLAway_comp_algebraMap :
    (evalGLAway (k := k) (N := N)).comp
        (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)))
      = evalGLHom :=
  IsLocalization.Away.lift_comp _ _

@[simp]
theorem evalGLAway_algebraMap (a : MvPolynomial (Fin N × Fin N) k) :
    evalGLAway (algebraMap _ (Localization.Away (detPoly k N)) a) = evalGLHom a :=
  IsLocalization.Away.lift_eq _ _ _

/-- **Faithful functions-on-`GL` model.** The induced map
`A[det⁻¹] →+* (GL_N → k)` is injective: an honest localization element is
determined by the function it defines on `GL_N`. Needs `k` infinite. -/
theorem evalGLAway_injective [Infinite k] :
    Function.Injective (evalGLAway (k := k) (N := N)) := by
  have key : ∀ x y : MvPolynomial (Fin N × Fin N) k,
      algebraMap _ (Localization.Away (detPoly k N)) x
          = algebraMap _ (Localization.Away (detPoly k N)) y
        ↔ evalGLHom x = evalGLHom y := fun x y => by
    rw [(IsLocalization.injective (Localization.Away (detPoly k N))
          powers_detPoly_le_nonZeroDivisors).eq_iff,
        evalGLHom_injective.eq_iff]
  exact (IsLocalization.lift_injective_iff _).mpr key

/-! ### `evalAtGL` factors through `A[det⁻¹]`

`evalAtGL` (Definition 5.23.1) evaluates a polynomial in `k[Xᵢⱼ, D]`
(`MvPolynomial (GLCoordVars N) k`) at a matrix with `D ↦ det⁻¹`. We exhibit the
coordinate ring hom `k[Xᵢⱼ, D] →+* A[det⁻¹]` sending `Xᵢⱼ ↦ Xᵢⱼ` and
`D ↦ detPoly⁻¹`, and show `evalAtGL g = (eval-at-g) ∘ evalGLAway ∘ coordToAway`. -/

/-- The coordinate ring hom `k[Xᵢⱼ, D] →+* A[det⁻¹]` sending the entry variables
to themselves and the formal inverse `D` to `detPoly⁻¹`
(`IsLocalization.Away.invSelf`). -/
noncomputable def coordToAway :
    MvPolynomial (Etingof.GLCoordVars N) k →+* Localization.Away (detPoly k N) :=
  MvPolynomial.eval₂Hom (algebraMap k (Localization.Away (detPoly k N)))
    (Sum.elim
      (fun ij : Fin N × Fin N =>
        algebraMap (MvPolynomial (Fin N × Fin N) k) _ (MvPolynomial.X ij))
      (fun _ : Unit => IsLocalization.Away.invSelf (detPoly k N)))

@[simp]
theorem coordToAway_C (r : k) :
    coordToAway (MvPolynomial.C r : MvPolynomial (Etingof.GLCoordVars N) k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))
          (MvPolynomial.C r) := by
  rw [coordToAway, MvPolynomial.eval₂Hom_C,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N)),
    MvPolynomial.algebraMap_eq]

@[simp]
theorem coordToAway_X_inl (ij : Fin N × Fin N) :
    coordToAway (MvPolynomial.X (Sum.inl ij) : MvPolynomial (Etingof.GLCoordVars N) k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) _ (MvPolynomial.X ij) := by
  rw [coordToAway, MvPolynomial.eval₂Hom_X', Sum.elim_inl]

@[simp]
theorem coordToAway_X_inr (u : Unit) :
    coordToAway (MvPolynomial.X (Sum.inr u) : MvPolynomial (Etingof.GLCoordVars N) k)
      = IsLocalization.Away.invSelf (detPoly k N) := by
  rw [coordToAway, MvPolynomial.eval₂Hom_X', Sum.elim_inr]

/-- Evaluating `evalGLAway` at the formal inverse `invSelf detPoly` gives the
pointwise inverse of `det` on `GL_N`: `(det g)⁻¹`. -/
theorem evalGLAway_invSelf_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    evalGLAway (IsLocalization.Away.invSelf (detPoly k N)) g
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by
  have hg_det : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hmul : evalGLAway (algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N))
      * evalGLAway (IsLocalization.Away.invSelf (detPoly k N)) = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hmul_g := congrFun hmul g
  rw [Pi.mul_apply, Pi.one_apply, evalGLAway_algebraMap, evalGLHom_detPoly_apply] at hmul_g
  calc evalGLAway (IsLocalization.Away.invSelf (detPoly k N)) g
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹
          * ((g : Matrix (Fin N) (Fin N) k).det
              * evalGLAway (IsLocalization.Away.invSelf (detPoly k N)) g) := by
        rw [← mul_assoc, inv_mul_cancel₀ hg_det, one_mul]
    _ = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by rw [hmul_g, mul_one]

/-- **`evalAtGL` factors through `A[det⁻¹]`.** For every `g ∈ GL_N` and every
`p ∈ k[Xᵢⱼ, D]`, `evalAtGL g p = evalGLAway (coordToAway p) g`. -/
theorem evalAtGL_eq_evalGLAway_coordToAway
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (Etingof.GLCoordVars N) k) :
    Etingof.evalAtGL g p = evalGLAway (coordToAway p) g := by
  -- both sides are ring homs `k[Xᵢⱼ, D] →+* k`; check equality on generators.
  have hΦΨ :
      (MvPolynomial.eval (Sum.elim
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (fun _ : Unit => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) :
        MvPolynomial (Etingof.GLCoordVars N) k →+* k)
        = (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
            ((evalGLAway).comp coordToAway) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval_C, Pi.evalRingHom_apply,
        coordToAway_C, evalGLAway_algebraMap, evalGLHom_apply]
    · intro s
      rcases s with ij | u
      · simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inl,
          Pi.evalRingHom_apply, coordToAway_X_inl, evalGLAway_algebraMap, evalGLHom_apply]
      · simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inr,
          Pi.evalRingHom_apply, coordToAway_X_inr, evalGLAway_invSelf_apply]
  have := RingHom.congr_fun hΦΨ p
  simpa [Etingof.evalAtGL] using this

/-! ### The det-power normal form `f = Q · det⁻ʳ` -/

/-- The polynomial ring `A = k[Xᵢⱼ]` injects into its localization `A[det⁻¹]`:
`detPoly` is a nonzerodivisor (domain, `detPoly ≠ 0`). -/
theorem algebraMap_away_injective :
    Function.Injective
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))) :=
  IsLocalization.injective _ powers_detPoly_le_nonZeroDivisors

/-- `detⁿ · det⁻ⁿ = 1` in `A[det⁻¹]`. -/
theorem algebraMap_detPoly_pow_mul_invSelf_pow (n : ℕ) :
    (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))
          (detPoly k N)) ^ n
        * IsLocalization.Away.invSelf (detPoly k N) ^ n = 1 := by
  rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]

/-- **Det-power normal form (existence).** Every element of `A[det⁻¹]` can be
written `Q · det⁻ʳ` for a polynomial `Q` and an exponent `r`. -/
theorem exists_invSelf_normalForm (f : Localization.Away (detPoly k N)) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k),
      f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (detPoly k N) f
  refine ⟨n, a, ?_⟩
  have key := algebraMap_detPoly_pow_mul_invSelf_pow (k := k) (N := N) n
  calc
    f = f * ((algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)) ^ n
            * IsLocalization.Away.invSelf (detPoly k N) ^ n) := by rw [key, mul_one]
    _ = (f * (algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)) ^ n)
            * IsLocalization.Away.invSelf (detPoly k N) ^ n := by ring
    _ = algebraMap _ (Localization.Away (detPoly k N)) a
            * IsLocalization.Away.invSelf (detPoly k N) ^ n := by rw [h]

open Classical in
/-- The minimal `det`-power exponent in the normal form of `f`: the least `r`
with `f = Q · det⁻ʳ` for some polynomial `Q`. The reduced normal form keys on it
(`A_r := det⁻ʳ · A`). -/
noncomputable def detExp (f : Localization.Away (detPoly k N)) : ℕ :=
  Nat.find (exists_invSelf_normalForm f)

open Classical in
/-- A numerator realising the minimal exponent `detExp f`. -/
theorem detExp_spec (f : Localization.Away (detPoly k N)) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k,
      f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ detExp f :=
  Nat.find_spec (exists_invSelf_normalForm f)

open Classical in
/-- `detExp f` is the least exponent: any normal form `f = Q · det⁻ʳ` has
`detExp f ≤ r`. -/
theorem detExp_le {f : Localization.Away (detPoly k N)} {r : ℕ}
    (h : ∃ Q : MvPolynomial (Fin N × Fin N) k,
          f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r) :
    detExp f ≤ r :=
  Nat.find_min' (exists_invSelf_normalForm f) h

/-- Clearing denominators: `Q = f · detʳ` for any normal form `f = Q · det⁻ʳ`. -/
theorem algebraMap_num_eq {f : Localization.Away (detPoly k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r) :
    algebraMap _ (Localization.Away (detPoly k N)) Q
      = f * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ r := by
  rw [hQ, mul_assoc,
    show IsLocalization.Away.invSelf (detPoly k N) ^ r
        * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ r = 1
      from by rw [mul_comm]; exact algebraMap_detPoly_pow_mul_invSelf_pow r,
    mul_one]

/-- **Uniqueness of the numerator** at a fixed exponent: the localization is a
domain, so `det⁻ʳ` cancels and `algebraMap` is injective. -/
theorem normalForm_num_unique {f : Localization.Away (detPoly k N)} {r : ℕ}
    {Q₁ Q₂ : MvPolynomial (Fin N × Fin N) k}
    (h₁ : f = algebraMap _ (Localization.Away (detPoly k N)) Q₁
            * IsLocalization.Away.invSelf (detPoly k N) ^ r)
    (h₂ : f = algebraMap _ (Localization.Away (detPoly k N)) Q₂
            * IsLocalization.Away.invSelf (detPoly k N) ^ r) :
    Q₁ = Q₂ :=
  algebraMap_away_injective (by rw [algebraMap_num_eq h₁, algebraMap_num_eq h₂])

/-- If a normal form has exponent strictly above the minimal one, its numerator
carries a `detPoly` factor (it is `Qₛ · detʳ⁻ˢ` for the minimal numerator `Qₛ`). -/
theorem dvd_num_of_detExp_lt {f : Localization.Away (detPoly k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r)
    (hlt : detExp f < r) : detPoly k N ∣ Q := by
  obtain ⟨Qs, hs⟩ := detExp_spec f
  -- freeze `detExp f` as an opaque `s`, else `rw [hs]` corrupts the exponent
  obtain ⟨s, hsdef⟩ : ∃ s, detExp f = s := ⟨_, rfl⟩
  rw [hsdef] at hs hlt
  have hQeq : algebraMap _ (Localization.Away (detPoly k N)) Q
      = algebraMap _ (Localization.Away (detPoly k N)) (Qs * detPoly k N ^ (r - s)) := by
    rw [algebraMap_num_eq hQ, hs, map_mul, map_pow,
      show algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ r
          = algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ s
            * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - s)
        from by rw [← pow_add]; congr 1; omega]
    calc
      (algebraMap _ (Localization.Away (detPoly k N)) Qs
            * IsLocalization.Away.invSelf (detPoly k N) ^ s)
          * (algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ s
            * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - s))
        = (IsLocalization.Away.invSelf (detPoly k N) ^ s
            * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ s)
          * (algebraMap _ (Localization.Away (detPoly k N)) Qs
            * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - s)) := by
          ring
      _ = algebraMap _ (Localization.Away (detPoly k N)) Qs
            * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - s) := by
          rw [show IsLocalization.Away.invSelf (detPoly k N) ^ s
                * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ s = 1
              from by rw [mul_comm]; exact algebraMap_detPoly_pow_mul_invSelf_pow _, one_mul]
  have hQ2 : Q = Qs * detPoly k N ^ (r - s) := algebraMap_away_injective hQeq
  rw [hQ2]
  exact (dvd_pow_self (detPoly k N) (by omega : r - s ≠ 0)).mul_left Qs

/-- **Reduced numerator is coprime to `det`.** At the minimal exponent (when it
is positive) the numerator is not divisible by `detPoly` — otherwise the factor
would cancel and lower the exponent. -/
theorem not_dvd_num_of_detExp_pos {f : Localization.Away (detPoly k N)}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ detExp f)
    (hpos : 1 ≤ detExp f) : ¬ detPoly k N ∣ Q := by
  intro hd
  obtain ⟨Q', rfl⟩ := hd
  -- freeze `detExp f` as an opaque `s`, else `rw [hQ]` corrupts the exponent
  obtain ⟨s, hsdef⟩ : ∃ s, detExp f = s := ⟨_, rfl⟩
  rw [hsdef] at hQ hpos
  have hlow : ∃ Q'' : MvPolynomial (Fin N × Fin N) k,
      f = algebraMap _ (Localization.Away (detPoly k N)) Q''
            * IsLocalization.Away.invSelf (detPoly k N) ^ (s - 1) := by
    refine ⟨Q', ?_⟩
    rw [hQ, map_mul,
      show IsLocalization.Away.invSelf (detPoly k N) ^ s
          = IsLocalization.Away.invSelf (detPoly k N) ^ (s - 1)
            * IsLocalization.Away.invSelf (detPoly k N)
        from by conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ]]
    calc
      algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)
            * algebraMap _ (Localization.Away (detPoly k N)) Q'
          * (IsLocalization.Away.invSelf (detPoly k N) ^ (s - 1)
            * IsLocalization.Away.invSelf (detPoly k N))
        = (algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)
            * IsLocalization.Away.invSelf (detPoly k N))
          * (algebraMap _ (Localization.Away (detPoly k N)) Q'
            * IsLocalization.Away.invSelf (detPoly k N) ^ (s - 1)) := by ring
      _ = algebraMap _ (Localization.Away (detPoly k N)) Q'
            * IsLocalization.Away.invSelf (detPoly k N) ^ (s - 1) := by
          rw [IsLocalization.Away.mul_invSelf, one_mul]
  have hle := detExp_le hlow
  rw [hsdef] at hle
  omega

/-- The minimal exponent is exactly the reduced one: any normal form whose
numerator is coprime to `det` (or whose exponent is `0`) already has the minimal
exponent. -/
theorem detExp_eq_of_reduced {f : Localization.Away (detPoly k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r)
    (hred : r = 0 ∨ ¬ detPoly k N ∣ Q) : r = detExp f := by
  refine le_antisymm ?_ (detExp_le ⟨Q, hQ⟩)
  by_contra hlt
  push_neg at hlt
  rcases hred with h0 | hnd
  · omega
  · exact hnd (dvd_num_of_detExp_lt hQ hlt)

/-- **Reduced det-power normal form.** Every `f` has a normal form
`f = Q · det⁻ʳ` with `r = detExp f` minimal and, when `r ≥ 1`, numerator `Q`
coprime to `det`. -/
theorem exists_reduced_normalForm (f : Localization.Away (detPoly k N)) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k),
      f = algebraMap _ (Localization.Away (detPoly k N)) Q
            * IsLocalization.Away.invSelf (detPoly k N) ^ r
        ∧ (1 ≤ r → ¬ detPoly k N ∣ Q)
        ∧ ∀ (r' : ℕ) (Q' : MvPolynomial (Fin N × Fin N) k),
            f = algebraMap _ (Localization.Away (detPoly k N)) Q'
                  * IsLocalization.Away.invSelf (detPoly k N) ^ r' → r ≤ r' := by
  obtain ⟨Q, hQ⟩ := detExp_spec f
  exact ⟨detExp f, Q, hQ, fun hpos => not_dvd_num_of_detExp_pos hQ hpos,
    fun _ Q' h' => detExp_le ⟨Q', h'⟩⟩

/-- **Uniqueness of the reduced normal form.** Two reduced representations of `f`
(each with exponent `0` or numerator coprime to `det`) agree in both exponent and
numerator. -/
theorem reduced_normalForm_unique {f : Localization.Away (detPoly k N)} {r₁ r₂ : ℕ}
    {Q₁ Q₂ : MvPolynomial (Fin N × Fin N) k}
    (h₁ : f = algebraMap _ (Localization.Away (detPoly k N)) Q₁
            * IsLocalization.Away.invSelf (detPoly k N) ^ r₁)
    (hred₁ : r₁ = 0 ∨ ¬ detPoly k N ∣ Q₁)
    (h₂ : f = algebraMap _ (Localization.Away (detPoly k N)) Q₂
            * IsLocalization.Away.invSelf (detPoly k N) ^ r₂)
    (hred₂ : r₂ = 0 ∨ ¬ detPoly k N ∣ Q₂) :
    r₁ = r₂ ∧ Q₁ = Q₂ := by
  have e₁ := detExp_eq_of_reduced h₁ hred₁
  have e₂ := detExp_eq_of_reduced h₂ hred₂
  refine ⟨e₁.trans e₂.symm, ?_⟩
  rw [e₁] at h₁
  rw [e₂] at h₂
  exact normalForm_num_unique h₁ h₂

/-- **`r = 0 ↔ f` is an honest polynomial.** The reduced exponent vanishes
exactly when `f` lies in the image of the polynomial subring `A` — the predicate
the det-power filtration `A_r := det⁻ʳ · A` (with `A = A_0`) keys on. -/
theorem detExp_eq_zero_iff (f : Localization.Away (detPoly k N)) :
    detExp f = 0 ↔ f ∈ Set.range
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))) := by
  constructor
  · intro h0
    obtain ⟨Q, hQ⟩ := detExp_spec f
    rw [h0, pow_zero, mul_one] at hQ
    exact ⟨Q, hQ.symm⟩
  · rintro ⟨Q, rfl⟩
    exact Nat.le_zero.mp (detExp_le (r := 0) ⟨Q, by rw [pow_zero, mul_one]⟩)

end Etingof.DetLocalization
