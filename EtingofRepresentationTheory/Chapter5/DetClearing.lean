import EtingofRepresentationTheory.Chapter5.PolynomialWeightSaturation

/-!
# Det-clearing: a `det`-power twist of an algebraic `GL_N`-representation is polynomial

This file proves Step 1 of the assembly of `Theorem5_23_2_i` (issue #5486, sub-task of
#5478): from an algebraic representation `ρ` (matrix coefficients in
`k[Xᵢⱼ, det⁻¹]`, i.e. `Etingof.IsAlgebraicRepresentation`) we produce an exponent `s`
such that the `det^s`-twist `g ↦ (det g)^s • ρ g` is **polynomial** (det⁻¹-free, i.e.
`Etingof.IsPolynomialRepresentation`).

This formalizes the book's "every element of `R` is a polynomial of `gᵢⱼ` times a
nonpositive power of `det(g)`" (`blobs/Chapter5/Discussion_proof_of_Theorem5.23.2.md`).

## Proof idea

View a coefficient `P a c ∈ k[Xᵢⱼ, det⁻¹]` as a one-variable polynomial in the `det⁻¹`
variable `D` with coefficients in `B := k[Xᵢⱼ]` (the algebra equivalence
`glCoordToPoly`). If `P a c` corresponds to `q = ∑_j q_j · D^j` (with `q_j ∈ B`) and
`s ≥ deg_D q`, the cleared polynomial is

    clear s q := ∑_{j ≤ s} q_j · detPolyB^{s-j} ∈ B,

a genuine `det⁻¹`-free polynomial. The defining identity is

    eval g (clear s q) = (det g)^s · evalAtGL g (P a c),

which matches `(det g)^s · (a,c)`-coefficient of `ρ g`, i.e. the coefficient of the
twisted representation. Taking `s` to be the max degree over the finitely many
coefficients gives a single uniform exponent.
-/

open MvPolynomial

noncomputable section

namespace Etingof

/-! ### The determinant polynomial in the `det⁻¹`-free coordinate ring -/

/-- The determinant of the generic matrix `(Xᵢⱼ)`, as an element of the **det⁻¹-free**
coordinate ring `B = k[Xᵢⱼ]` (variables indexed by `Fin N × Fin N`). -/
def detPolyB (k : Type*) [Field k] (N : ℕ) : MvPolynomial (Fin N × Fin N) k :=
  (Matrix.of fun i j : Fin N => MvPolynomial.X (i, j)).det

@[simp]
theorem eval_detPolyB {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (detPolyB k N) = (g : Matrix (Fin N) (Fin N) k).det := by
  unfold detPolyB
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply]

/-! ### The `det⁻¹`-variable as a one-variable polynomial -/

/-- The reindexing `(Fin N × Fin N) ⊕ Unit ≃ Option (Fin N × Fin N)` sending the
`det⁻¹` variable `Sum.inr ()` to the polynomial variable `none`. -/
def glCoordOptionEquiv (N : ℕ) : Etingof.GLCoordVars N ≃ Option (Fin N × Fin N) where
  toFun := Sum.elim some fun _ => none
  invFun := fun o => o.elim (Sum.inr ()) Sum.inl
  left_inv := by rintro (ij | ⟨⟩) <;> rfl
  right_inv := by rintro (_ | ij) <;> rfl

/-- The algebra equivalence presenting `k[Xᵢⱼ, det⁻¹]` as one-variable polynomials in the
`det⁻¹` variable `D` with coefficients in `B = k[Xᵢⱼ]`. Sends `X (Sum.inl ij) ↦ C (X ij)`
and `X (Sum.inr ()) ↦ Polynomial.X`. -/
def glCoordToPoly (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Etingof.GLCoordVars N) k ≃ₐ[k]
      Polynomial (MvPolynomial (Fin N × Fin N) k) :=
  (MvPolynomial.renameEquiv k (glCoordOptionEquiv N)).trans
    (MvPolynomial.optionEquivLeft k (Fin N × Fin N))

/-- The evaluation `evalAtGL g` factors through `glCoordToPoly`: it is the one-variable
`eval₂` substituting `Xᵢⱼ ↦ gᵢⱼ` into the coefficients and `D ↦ (det g)⁻¹`. -/
theorem evalAtGL_eq_eval₂_glCoordToPoly {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (Etingof.GLCoordVars N) k) :
    Etingof.evalAtGL g p
      = Polynomial.eval₂
          (MvPolynomial.eval fun ij : Fin N × Fin N =>
            (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          ((g : Matrix (Fin N) (Fin N) k).det)⁻¹
          (glCoordToPoly k N p) := by
  -- Both sides are ring homomorphisms in `p`; check on generators.
  have hring :
      (MvPolynomial.eval (Sum.elim
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (fun _ => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) :
        MvPolynomial (Etingof.GLCoordVars N) k →+* k)
        = (Polynomial.eval₂RingHom
            (MvPolynomial.eval fun ij : Fin N × Fin N =>
              (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
            ((g : Matrix (Fin N) (Fin N) k).det)⁻¹).comp
            (glCoordToPoly k N).toAlgHom.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [glCoordToPoly, glCoordOptionEquiv]
    · intro v
      rcases v with ij | u
      · simp [glCoordToPoly, glCoordOptionEquiv]
      · simp [glCoordToPoly, glCoordOptionEquiv]
  have := RingHom.congr_fun hring p
  simpa [Etingof.evalAtGL] using this

/-! ### The clearing operation -/

/-- The cleared polynomial: from a one-variable polynomial `q = ∑_j q_j · D^j` over
`B = k[Xᵢⱼ]` and a degree bound `s`, the **det⁻¹-free** polynomial
`∑_{j ≤ s} q_j · detPolyB^{s-j}`. -/
def clearPoly (k : Type*) [Field k] (N : ℕ)
    (q : Polynomial (MvPolynomial (Fin N × Fin N) k)) (s : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  ∑ j ∈ Finset.range (s + 1), q.coeff j * detPolyB k N ^ (s - j)

/-- Defining identity of `clearPoly`: evaluating at `g ∈ GL_N` multiplies the `det⁻¹`-form
`eval₂ ... (det g)⁻¹ q` by `(det g)^s`. -/
theorem eval_clearPoly {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (q : Polynomial (MvPolynomial (Fin N × Fin N) k)) (s : ℕ)
    (hq : q.natDegree ≤ s) :
    MvPolynomial.eval (fun ij : Fin N × Fin N =>
        (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) (clearPoly k N q s)
      = (g : Matrix (Fin N) (Fin N) k).det ^ s
          * Polynomial.eval₂
              (MvPolynomial.eval fun ij : Fin N × Fin N =>
                (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
              ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ q := by
  have hD : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  unfold clearPoly
  rw [map_sum,
    Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hq) _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [map_mul, map_pow, eval_detPolyB]
  -- `evB (q.coeff j) * D^(s-j) = D^s * (evB (q.coeff j) * (D⁻¹)^j)`.
  -- Prove over abstract scalars so `ring`/`rw` do not whnf the heavy `eval`/`det` atoms.
  have key : ∀ A D : k, D ≠ 0 → A * D ^ (s - j) = D ^ s * (A * D⁻¹ ^ j) := by
    intro A D hD'
    rw [pow_sub₀ D hD' hj, inv_pow, mul_left_comm]
  exact key _ _ hD

/-! ### Main result -/

/-- **Det-clearing (Step 1 of `Theorem5_23_2_i`).** An algebraic `GL_N(k)`-representation
admits an exponent `s` such that its `det^s`-twist is polynomial (det⁻¹-free). -/
theorem IsAlgebraicRepresentation.exists_detPow_twist_isPolynomial
    {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    ∃ s : ℕ, IsPolynomialRepresentation N
      (fun g => ((Matrix.GeneralLinearGroup.det g : k) ^ s) • ρ g) := by
  classical
  obtain ⟨m, b, P, hP⟩ := h
  -- A uniform degree bound over the finitely many coefficients (nested `sup`, so each
  -- `P a c` appears literally — no `Prod.fst`/`Prod.snd` projection that would force
  -- `isDefEq` to whnf the heavy `glCoordToPoly`).
  set s := Finset.univ.sup
    (fun a : Fin m => Finset.univ.sup
      (fun c : Fin m => (glCoordToPoly k N (P a c)).natDegree)) with hs_def
  refine ⟨s, m, b, fun a c => clearPoly k N (glCoordToPoly k N (P a c)) s, fun g a c => ?_⟩
  have hdeg : (glCoordToPoly k N (P a c)).natDegree ≤ s := by
    rw [hs_def]
    refine le_trans
      (Finset.le_sup (f := fun c : Fin m => (glCoordToPoly k N (P a c)).natDegree)
        (Finset.mem_univ c))
      (Finset.le_sup (f := fun a : Fin m => Finset.univ.sup
        (fun c : Fin m => (glCoordToPoly k N (P a c)).natDegree)) (Finset.mem_univ a))
  have hdk : (Matrix.GeneralLinearGroup.det g : k) = (g : Matrix (Fin N) (Fin N) k).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  -- Reduce the LHS coefficient of the twisted rep (no heavy `glCoordToPoly` in this `rw`).
  have e1 : b.repr (((Matrix.GeneralLinearGroup.det g : k) ^ s • ρ g) (b c)) a
      = (Matrix.GeneralLinearGroup.det g : k) ^ s * Etingof.evalAtGL g (P a c) := by
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c]
  -- The cleared RHS, as a direct term application (no `rw` over the heavy `glCoordToPoly`).
  have e3 := eval_clearPoly g (glCoordToPoly k N (P a c)) s hdeg
  -- Bridge via `congrArg` with explicit motives, so no `rw`/kabstract whnf-reduces the
  -- heavy `glCoordToPoly` term while searching the goal.
  have hAB : (Matrix.GeneralLinearGroup.det g : k) ^ s * Etingof.evalAtGL g (P a c)
      = (g : Matrix (Fin N) (Fin N) k).det ^ s
        * Polynomial.eval₂
            (MvPolynomial.eval fun ij : Fin N × Fin N =>
              (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
            ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ (glCoordToPoly k N (P a c)) :=
    (congrArg (fun t : k => t ^ s * Etingof.evalAtGL g (P a c)) hdk).trans
      (congrArg
        (fun u : k => (g : Matrix (Fin N) (Fin N) k).det ^ s * u)
        (evalAtGL_eq_eval₂_glCoordToPoly g (P a c)))
  exact e1.trans (hAB.trans e3.symm)

end Etingof
