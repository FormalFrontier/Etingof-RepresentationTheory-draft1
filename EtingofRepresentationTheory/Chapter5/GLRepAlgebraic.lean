import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# General algebraicity infrastructure for `GL_N(k)`-representations

This file collects the reusable lemmas about `Etingof.IsAlgebraicRepresentation`
(Definition 5.23.1) that are independent of any particular twisted Schur module:

* `evalAtGL_mul` / `evalAtGL_sum` / `evalAtGL_prod` / `evalAtGL_C` / `evalAtGL_X_inl`
  — ring-homomorphism behaviour of evaluation `evalAtGL g`.
* `detPolyGL` and `evalAtGL_detPolyGL` — the determinant of the generic matrix as a
  polynomial in the coordinate ring, and its evaluation.
* `IsAlgebraicRepresentation.detTwist` — twisting an algebraic representation by the
  determinant character keeps it algebraic.
* `IsAlgebraicRepresentation.restrict` — the restriction of an algebraic representation
  to an invariant submodule is algebraic.
* `glTensorRep_isAlgebraic` — the diagonal action `g ↦ g^{⊗n}` on `(k^N)^{⊗n}` is
  algebraic.

These are factored out of `DetTwistAlgebraic` so that they sit *upstream* of
`Proposition5_22_2` (where the twisted Schur module `detTwistedSchurModuleRep` is
defined). That lets `schurModule_shift_iso_detTwist` supply the algebraicity hypothesis
required by `iso_of_formalCharacter_eq_schurPoly` (#4882) without an import cycle:
`detTwistedSchurModuleRep_isAlgebraic` itself lives downstream, in `DetTwistAlgebraic`.
-/

open scoped TensorProduct
open Matrix

noncomputable section

namespace Etingof

/-! ### Ring-homomorphism behaviour of `evalAtGL` -/

theorem evalAtGL_mul {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p q : MvPolynomial (Etingof.GLCoordVars N) k) :
    Etingof.evalAtGL g (p * q) = Etingof.evalAtGL g p * Etingof.evalAtGL g q := by
  simp only [Etingof.evalAtGL, map_mul]

theorem evalAtGL_sum {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (s : Finset ι) (f : ι → MvPolynomial (Etingof.GLCoordVars n) k) :
    Etingof.evalAtGL g (∑ i ∈ s, f i) = ∑ i ∈ s, Etingof.evalAtGL g (f i) := by
  simp only [Etingof.evalAtGL, map_sum]

theorem evalAtGL_prod {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (s : Finset ι) (f : ι → MvPolynomial (Etingof.GLCoordVars n) k) :
    Etingof.evalAtGL g (∏ i ∈ s, f i) = ∏ i ∈ s, Etingof.evalAtGL g (f i) := by
  simp only [Etingof.evalAtGL, map_prod]

theorem evalAtGL_C {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : k) :
    Etingof.evalAtGL g (MvPolynomial.C r) = r := by
  simp only [Etingof.evalAtGL, MvPolynomial.eval_C]

theorem evalAtGL_X_inl {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (i j : Fin N) :
    Etingof.evalAtGL g (MvPolynomial.X (Sum.inl (i, j))) = g.val i j := by
  change MvPolynomial.eval _ (MvPolynomial.X (Sum.inl (i, j))) = _
  rw [MvPolynomial.eval_X]
  rfl

/-! ### The determinant polynomial -/

/-- The determinant of the generic matrix `(Xᵢⱼ)`, as an element of the
coordinate ring `k[Xᵢⱼ, det⁻¹]`. Only the matrix-entry variables (`Sum.inl`)
appear; this is a genuine polynomial, no `det⁻¹` needed. -/
def detPolyGL (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Etingof.GLCoordVars N) k :=
  (Matrix.of fun i j : Fin N => MvPolynomial.X (R := k) (Sum.inl (i, j))).det

@[simp]
theorem evalAtGL_detPolyGL {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Etingof.evalAtGL g (detPolyGL k N) = (Matrix.GeneralLinearGroup.det g : k) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  unfold Etingof.evalAtGL detPolyGL
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply]

/-! ### Algebraicity is preserved by determinant twist -/

/-- Twisting an algebraic representation by the determinant character keeps it
algebraic: each coefficient polynomial is multiplied by `detPolyGL`. -/
theorem IsAlgebraicRepresentation.detTwist {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    Etingof.IsAlgebraicRepresentation N
      (fun g => (Matrix.GeneralLinearGroup.det g : k) • ρ g) := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b, fun a c => detPolyGL k N * P a c, fun g a c => ?_⟩
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c,
    evalAtGL_mul, evalAtGL_detPolyGL]

/-! ### Algebraicity is preserved by restriction to an invariant submodule -/

/-- The restriction of an algebraic representation `ρ` to a `ρ`-invariant
submodule `W` is algebraic. Choosing a basis of `W`, a linear projection
`π : Y → W`, and the ambient basis `B`, the new matrix coefficients expand as
`k`-linear combinations of `evalAtGL g (P e d)` with constant coefficients
coming from `B.repr (W.subtype (b' c))` and `b'.repr (π (B e))`. -/
theorem IsAlgebraicRepresentation.restrict {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : Etingof.IsAlgebraicRepresentation N ρ)
    (W : Submodule k Y) [Module.Finite k W]
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) :
    Etingof.IsAlgebraicRepresentation N (fun g => (ρ g).restrict (hW g)) := by
  classical
  obtain ⟨M, B, P, hP⟩ := h
  -- Basis of the submodule, indexed by `Fin (finrank k W)`.
  let b' : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  -- A linear projection `π : Y → W` that is a left inverse of the inclusion.
  obtain ⟨W', hWW'⟩ := W.exists_isCompl
  let π : Y →ₗ[k] W := W.linearProjOfIsCompl W' hWW'
  have hπincl : ∀ w : W, π (W.subtype w) = w := fun w =>
    W.linearProjOfIsCompl_apply_left hWW' w
  refine ⟨Module.finrank k W, b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (W.subtype (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (π (B e)) a), fun g a c => ?_⟩
  -- `φ y = b'.repr (π y) a`, a linear functional `Y → k`.
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp π)
  have hφ_apply : ∀ y, φ y = b'.repr (π y) a := fun _ => rfl
  have hcoe : (W.subtype) ((ρ g).restrict (hW g) (b' c)) = ρ g (W.subtype (b' c)) :=
    LinearMap.restrict_coe_apply (ρ g) (hW g) (b' c)
  -- Reduce the LHS coefficient to a double sum over the ambient basis.
  have hlhs : b'.repr ((ρ g).restrict (hW g) (b' c)) a
      = ∑ d, ∑ e, B.repr (W.subtype (b' c)) d
          * (Etingof.evalAtGL g (P e d) * b'.repr (π (B e)) a) := by
    have h1 : (ρ g).restrict (hW g) (b' c) = π (ρ g (W.subtype (b' c))) := by
      rw [← hcoe, hπincl]
    rw [show b'.repr ((ρ g).restrict (hW g) (b' c)) a = φ (ρ g (W.subtype (b' c))) from by
      rw [hφ_apply, h1]]
    -- expand `W.subtype (b' c)` in the ambient basis `B`
    rw [show ρ g (W.subtype (b' c))
        = ∑ d, B.repr (W.subtype (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show W.subtype (b' c) = ∑ d, B.repr (W.subtype (b' c)) d • B d from
        (B.sum_repr (W.subtype (b' c))).symm]
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [map_smul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, smul_eq_mul]
    -- compute `φ (ρ g (B d))` by expanding `ρ g (B d)` in `B`
    have hd : φ (ρ g (B d))
        = ∑ e, Etingof.evalAtGL g (P e d) * b'.repr (π (B e)) a := by
      conv_lhs => rw [show ρ g (B d) = ∑ e, B.repr (ρ g (B d)) e • B e from
        (B.sum_repr (ρ g (B d))).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, hP g e d, hφ_apply]
    rw [hd, Finset.mul_sum]
  rw [hlhs, evalAtGL_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evalAtGL_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [evalAtGL_mul, evalAtGL_mul, evalAtGL_C, evalAtGL_C]
  ring

/-! ### The diagonal action is algebraic -/

/-- The standard tensor basis of `(k^N)^{⊗n}`, indexed by `Fin n → Fin N`. -/
def tBasisAlg (k : Type*) [Field k] (N n : ℕ) :
    Module.Basis (Fin n → Fin N) k (TensorPower k (Fin N → k) n) :=
  Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun k (Fin N))

/-- Matrix coefficient of the diagonal action in the standard tensor basis:
`glTensorRep g` sends `tBasis f` to `∑ₕ (∏ₘ g_{h m, f m}) • tBasis h`. -/
theorem repr_glTensorRep_tBasisAlg {k : Type*} [Field k] {N n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (f h : Fin n → Fin N) :
    (tBasisAlg k N n).repr (glTensorRep k N n g (tBasisAlg k N n f)) h
      = ∏ m, (g.val) (h m) (f m) := by
  change (tBasisAlg k N n).repr
      (PiTensorProduct.map (fun _ => Matrix.mulVecLin (R := k) g.val)
        (tBasisAlg k N n f)) h = _
  simp only [tBasisAlg, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Pi.basisFun_repr, Matrix.mulVecLin_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  rfl

/-- The diagonal action `g ↦ g^{⊗n}` on `(k^N)^{⊗n}` is algebraic. The matrix
coefficient in the standard tensor basis is the monomial `∏ₘ X_{(h m, f m)}`. -/
theorem glTensorRep_isAlgebraic (k : Type*) [Field k] (N n : ℕ) :
    Etingof.IsAlgebraicRepresentation N (glTensorRep k N n) := by
  classical
  set ι := Fin n → Fin N
  set eqv : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with heqv
  refine ⟨Fintype.card ι, (tBasisAlg k N n).reindex eqv.symm,
    fun a c => ∏ m, MvPolynomial.X (Sum.inl (eqv a m, eqv c m)),
    fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  simp only [Equiv.symm_symm]
  rw [repr_glTensorRep_tBasisAlg, evalAtGL_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [evalAtGL_X_inl]

/-! ### Algebraicity transfers along an equivariant linear equivalence -/

/-- **Algebraicity transfers along an intertwining `k`-linear equivalence.** If `ρ` is
an algebraic `GL_N(k)`-representation on `Y` and `e : Y ≃ₗ[k] Z` intertwines `ρ` with
`σ` (`e (ρ g y) = σ g (e y)`), then `σ` is algebraic: its matrix coefficients in the
transported basis `b.map e` are the very same polynomials as those of `ρ` in `b`.

This lets the abstract simple summands produced by the equivariant decomposition of an
algebraic representation inherit algebraicity from the ambient rep. -/
theorem IsAlgebraicRepresentation.of_linearEquiv {k : Type*} [Field k] {N : ℕ}
    {Y Z : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Z] [Module k Z] [Module.Finite k Z]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {σ : Matrix.GeneralLinearGroup (Fin N) k → Z →ₗ[k] Z}
    (e : Y ≃ₗ[k] Z)
    (hcomm : ∀ g y, e (ρ g y) = σ g (e y))
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    Etingof.IsAlgebraicRepresentation N σ := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b.map e, P, fun g a c => ?_⟩
  -- The image basis `b.map e` reproduces `b`'s coordinates after pushing `e` through.
  have hbe : ∀ w, (b.map e).repr (e w) = b.repr w := by
    intro w
    rw [show (b.map e).repr = e.symm.trans b.repr from rfl, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  rw [Module.Basis.map_apply, ← hcomm g (b c), hbe (ρ g (b c))]
  exact hP g a c

/-! ### The Schur module is algebraic -/

/-- **The Schur module `L_λ` is algebraic.** `SchurModule k N lam` is the restriction of
the (algebraic) tensor power `V^{⊗n}` to the Young-symmetrizer image
`SchurModuleSubmodule`, so algebraicity is inherited from `glTensorRep_isAlgebraic` via
`IsAlgebraicRepresentation.restrict`. (The det-twisted analogue is
`detTwistedSchurModuleRep_isAlgebraic`.) -/
theorem schurModule_isAlgebraic {k : Type*} [Field k] [IsAlgClosed k] (N : ℕ)
    (lam : Fin N → ℕ) :
    Etingof.IsAlgebraicRepresentation N (SchurModule k N lam).ρ := by
  change Etingof.IsAlgebraicRepresentation N (FDRep.of (schurModuleRep k N lam)).ρ
  rw [FDRep.of_ρ']
  exact (glTensorRep_isAlgebraic k N (∑ i, lam i)).restrict
    (SchurModuleSubmodule k N lam)
    (fun g v hv => glTensorRep_mem_range k N lam g v hv)

end Etingof
