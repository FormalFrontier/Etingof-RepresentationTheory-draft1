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

The two remaining pieces of issue #4712 — `detPoly` irreducibility/primeness and
the det-power normal form `f = Q / detʳ` — are split off into successor issues
(they require a substantial inductive determinant-irreducibility formalization
that Mathlib lacks); see the progress entry.
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

end Etingof.DetLocalization
