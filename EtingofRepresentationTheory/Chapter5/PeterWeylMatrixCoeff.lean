import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.AlgIrrepDualPairing
import EtingofRepresentationTheory.Chapter5.LocalizationGLBiAction
import EtingofRepresentationTheory.Chapter5.DetInvElim
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic

/-!
# The per-weight equivariant matrix-coefficient map `L*_λ ⊗ L_λ → R`

This file assembles bricks (2)+(3) of the Peter-Weyl decomposition
(Theorem 5.23.2(ii), `Theorem5_23_2_PeterWeyl.lean`): the per-summand
matrix-coefficient map

  `peterWeylSummandMap : L*_λ ⊗ L_λ →ₗ[k] R = Localization.Away (detPoly k n)`,
  `u ⊗ v ↦ (g ↦ ⟨u, g·v⟩)`,

and its `GL_n × GL_n`-equivariance.

`L_λ = AlgIrrepGL n lam k` carries the det-twisted Schur-module action
`algIrrepGLRepρ`, `L*_λ = AlgIrrepGLDual n lam k` its contragredient
`algIrrepGLRepDualρ`, and `⟨·,·⟩ = algIrrepDualPairing` is the typed
contragredient pairing (#5523), which is `GL_n`-invariant
(`algIrrepDualPairing_invariant`).

## Construction

`L_λ` is an *algebraic* representation (`algIrrepGLRepρ_isAlgebraic`, assembled from
`schurModule_isAlgebraic` plus the new `IsAlgebraicRepresentation.detInvTwist` for the
`det^{-shift}` twist): there is a basis `b` and matrix-coefficient polynomials `P` with
`b.repr (ρ(g) (b c)) a = evalAtGL g (P a c)`. The map is

  `u ⊗ v ↦ ∑_{a,c} (⟨u, b a⟩ · b.repr v c) • coordToAway (P a c)`,

genuine data built via `TensorProduct.lift`. Its defining property is the
matrix-coefficient identity (`evalGLAway_peterWeylSummandMap`)

  `evalGLAway (peterWeylSummandMap (u ⊗ v)) g = ⟨u, ρ(g) v⟩`,

read off through the faithful functions-on-`GL` model `evalGLAway`
(`DetLocalization.lean`). Equivariance (`peterWeylSummandMap_equivariant`) then
reduces, by injectivity of `evalGLAway` (`evalGLAway_injective`, needs `k`
infinite), to agreement on `GL`: the right factor uses
`evalGLAway_localRightRep` and `ρ(g)ρ(h) = ρ(gh)`; the left factor uses
`evalGLAway_localLeftRep` (post-#5536, left translation by `g⁻¹`) and the pairing
invariance `⟨ρ*(g₀)u, w⟩ = ⟨u, ρ(g₀⁻¹)w⟩`. Combining gives intertwining with
`localBiRep` exactly as in the `peterWeylRHS` summand action.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

open Etingof.DetLocalization Etingof.LocalizationGLAction Etingof.DetInvElim
  Etingof.KernelLemmaKPrime

/-! ## Two small `evalAtGL` helpers and the `det⁻¹`-twist of an algebraic rep -/

-- `evalAtGL_X_inr` (evaluation of the formal inverse variable `D` at `g`) lives upstream
-- in `GLRepAlgebraic.lean`.

/-- `evalAtGL g` is a ring hom, so it commutes with powers. -/
theorem evalAtGL_pow {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (Etingof.GLCoordVars N) k) (s : ℕ) :
    Etingof.evalAtGL g (p ^ s) = (Etingof.evalAtGL g p) ^ s := by
  simp only [Etingof.evalAtGL, map_pow]

/-- **Algebraicity is preserved by the inverse-determinant twist.** Twisting an
algebraic representation `ρ` by `det^{-s}` (i.e. `g ↦ (det g)⁻ˢ • ρ g`) keeps it
algebraic: each coefficient polynomial is multiplied by `Dˢ` (the `s`-th power of
the formal `det⁻¹` variable), which evaluates to `(det g)⁻ˢ`. -/
theorem IsAlgebraicRepresentation.detInvTwist {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : Etingof.IsAlgebraicRepresentation N ρ) (s : ℕ) :
    Etingof.IsAlgebraicRepresentation N
      (fun g : Matrix.GeneralLinearGroup (Fin N) k =>
        (((g : Matrix (Fin N) (Fin N) k).det)⁻¹) ^ s • ρ g) := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b, fun a c => (MvPolynomial.X (Sum.inr ())) ^ s * P a c, fun g a c => ?_⟩
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c,
    evalAtGL_mul, evalAtGL_pow, evalAtGL_X_inr]

/-! ## The twisting scalar `(detChar^{-r}) g = (det g)⁻ʳ` (local copy) -/

/-- A local copy of `detChar_zpow_neg_apply` (to avoid importing
`DetPowerFiltration`): the inverse determinant character `χ⁻ʳ` evaluates to
`(det g)⁻ʳ`. -/
theorem detChar_zpow_neg_apply' {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ) :
    ((detChar k N ^ (-(r : ℤ))) g : k) = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r := by
  have happ : (detChar k N ^ (-(r : ℤ))) g = (detChar k N g) ^ (-(r : ℤ)) := rfl
  rw [happ, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    ← inv_pow]
  rfl

/-! ## Algebraicity of `algIrrepGLRepρ` -/

variable (n : ℕ) (lam : DominantWeight n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- **`L_λ = algIrrepGLRepρ` is an algebraic representation.** It is the Schur
module (algebraic, `schurModule_isAlgebraic`) twisted by `det^{-λ.shift}`; the
twist keeps it algebraic by `IsAlgebraicRepresentation.detInvTwist`. -/
theorem algIrrepGLRepρ_isAlgebraic :
    Etingof.IsAlgebraicRepresentation n (fun g => algIrrepGLRepρ n lam k g) := by
  have hfun : (fun g => algIrrepGLRepρ n lam k g)
      = (fun g : Matrix.GeneralLinearGroup (Fin n) k =>
          (((g : Matrix (Fin n) (Fin n) k).det)⁻¹) ^ lam.shift •
          (SchurModule k n lam.toNatWeight).ρ g) := by
    funext g
    show ((detChar k n ^ (-(lam.shift : ℤ))) g : k) • schurModuleRep k n lam.toNatWeight g = _
    rw [detChar_zpow_neg_apply']
    rfl
  rw [hfun]
  exact (schurModule_isAlgebraic n lam.toNatWeight).detInvTwist lam.shift

/-! ## The per-summand matrix-coefficient map -/

/-- **Existence of the per-summand matrix-coefficient map together with its
defining identity.** Built explicitly from the algebraic witness of `L_λ`: with
basis `b` and coefficient polynomials `P`,
`u ⊗ v ↦ ∑_{a,c} (⟨u, b a⟩ · b.repr v c) • coordToAway (P a c)`. The defining
property is the matrix-coefficient identity
`evalGLAway (psm (u ⊗ v)) g = ⟨u, ρ(g) v⟩`. -/
theorem exists_peterWeylSummandMap :
    ∃ psm : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k →ₗ[k]
        Localization.Away (detPoly k n),
      ∀ (u : AlgIrrepGLDual n lam k) (v : AlgIrrepGL n lam k)
        (g : Matrix.GeneralLinearGroup (Fin n) k),
        evalGLAway (psm (u ⊗ₜ[k] v)) g
          = algIrrepDualPairing n lam k (u ⊗ₜ[k] algIrrepGLRepρ n lam k g v) := by
  obtain ⟨d, b, P, hP⟩ := algIrrepGLRepρ_isAlgebraic n lam k
  set B2 : AlgIrrepGLDual n lam k →ₗ[k] AlgIrrepGL n lam k →ₗ[k]
      Localization.Away (detPoly k n) :=
    ∑ a, ∑ c,
      LinearMap.smulRight
        ((algIrrepDualPairing n lam k) ∘ₗ
          (TensorProduct.mk k (AlgIrrepGLDual n lam k) (AlgIrrepGL n lam k)).flip (b a))
        (LinearMap.smulRight (b.coord c) (coordToAway (P a c))) with hB2
  refine ⟨TensorProduct.lift B2, ?_⟩
  intro u v g
  -- Reduce the localization element to the explicit double sum.
  have hmap : TensorProduct.lift B2 (u ⊗ₜ[k] v)
      = ∑ a, ∑ c,
          (algIrrepDualPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c) • coordToAway (P a c) := by
    rw [TensorProduct.lift.tmul, hB2]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      Module.Basis.coord_apply, smul_smul]
  rw [hmap]
  -- Push `evalGLAway` and evaluation at `g` through the sum, term by term.
  have hLHS : evalGLAway (∑ a, ∑ c,
        (algIrrepDualPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c) • coordToAway (P a c)) g
      = ∑ a, ∑ c,
          (algIrrepDualPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c)
            * Etingof.evalAtGL g (P a c) := by
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [evalGLAway_smul (algIrrepDualPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c)
        (coordToAway (P a c)), Pi.smul_apply, smul_eq_mul,
      ← evalAtGL_eq_evalGLAway_coordToAway]
  rw [hLHS]
  -- `Bu w = ⟨u, w⟩` as a linear functional, to push sums through cleanly.
  let Bu : AlgIrrepGL n lam k →ₗ[k] k :=
    (algIrrepDualPairing n lam k).comp
      (TensorProduct.mk k (AlgIrrepGLDual n lam k) (AlgIrrepGL n lam k) u)
  have hBu : ∀ w, Bu w = algIrrepDualPairing n lam k (u ⊗ₜ[k] w) := fun w => rfl
  have step1 : algIrrepGLRepρ n lam k g v
      = ∑ c, b.repr v c • algIrrepGLRepρ n lam k g (b c) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [map_smul]
  -- `⟨u, ρ(g)(b c)⟩` expands into `∑ a, (P a c)(g) · ⟨u, b a⟩`.
  have hBuc : ∀ c, Bu (algIrrepGLRepρ n lam k g (b c))
      = ∑ a, Etingof.evalAtGL g (P a c)
          * algIrrepDualPairing n lam k (u ⊗ₜ[k] b a) := by
    intro c
    conv_lhs => rw [← b.sum_repr (algIrrepGLRepρ n lam k g (b c))]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, hBu, hP]
  -- The right-hand pairing as the same double sum.
  have hexp : algIrrepDualPairing n lam k (u ⊗ₜ[k] algIrrepGLRepρ n lam k g v)
      = ∑ c, ∑ a, b.repr v c *
          (Etingof.evalAtGL g (P a c)
            * algIrrepDualPairing n lam k (u ⊗ₜ[k] b a)) := by
    have e1 : algIrrepDualPairing n lam k (u ⊗ₜ[k] algIrrepGLRepρ n lam k g v)
        = Bu (algIrrepGLRepρ n lam k g v) := (hBu _).symm
    rw [e1, step1, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul, hBuc, Finset.mul_sum]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The per-summand matrix-coefficient map** `L*_λ ⊗ L_λ →ₗ[k] R`,
`u ⊗ v ↦ (g ↦ ⟨u, ρ(g) v⟩)`. -/
noncomputable def peterWeylSummandMap :
    AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k →ₗ[k]
      Localization.Away (detPoly k n) :=
  (exists_peterWeylSummandMap n lam k).choose

/-- **The defining matrix-coefficient identity.** Evaluated at `g ∈ GL_n` through
the faithful functions-on-`GL` model `evalGLAway`, the per-summand map reads off the
matrix coefficient `⟨u, ρ(g) v⟩`. -/
theorem evalGLAway_peterWeylSummandMap (u : AlgIrrepGLDual n lam k)
    (v : AlgIrrepGL n lam k) (g : Matrix.GeneralLinearGroup (Fin n) k) :
    evalGLAway (peterWeylSummandMap n lam k (u ⊗ₜ[k] v)) g
      = algIrrepDualPairing n lam k (u ⊗ₜ[k] algIrrepGLRepρ n lam k g v) :=
  (exists_peterWeylSummandMap n lam k).choose_spec u v g

/-! ## `GL_n × GL_n`-equivariance -/

/-- **`GL_n × GL_n`-equivariance of the per-summand map.** For `(g, h)`, the map
intertwines the `peterWeylRHS` summand action `ρ*(g) ⊗ ρ(h)` (left contragredient
factor via the first `GL_n`, right factor via the second) with the
left/right-translation bi-action `localBiRep`. -/
theorem peterWeylSummandMap_equivariant
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (u : AlgIrrepGLDual n lam k) (v : AlgIrrepGL n lam k) :
    peterWeylSummandMap n lam k
        (algIrrepGLRepDualρ n lam k g u ⊗ₜ[k] algIrrepGLRepρ n lam k h v)
      = localBiRep k n (g, h) (peterWeylSummandMap n lam k (u ⊗ₜ[k] v)) := by
  -- Pairing invariance in the form `⟨ρ*(g₀) u, w⟩ = ⟨u, ρ(g₀⁻¹) w⟩`.
  have hinv : ∀ (g₀ : Matrix.GeneralLinearGroup (Fin n) k)
      (u' : AlgIrrepGLDual n lam k) (w : AlgIrrepGL n lam k),
      algIrrepDualPairing n lam k (algIrrepGLRepDualρ n lam k g₀ u' ⊗ₜ[k] w)
        = algIrrepDualPairing n lam k (u' ⊗ₜ[k] algIrrepGLRepρ n lam k g₀⁻¹ w) := by
    intro g₀ u' w
    have key := algIrrepDualPairing_invariant n lam k g₀ u' (algIrrepGLRepρ n lam k g₀⁻¹ w)
    have hww : algIrrepGLRepρ n lam k g₀ (algIrrepGLRepρ n lam k g₀⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rwa [hww] at key
  -- Inject into the faithful functions-on-`GL` model and compare pointwise.
  apply evalGLAway_injective
  funext y
  -- LHS: matrix coefficient at `y`.
  rw [evalGLAway_peterWeylSummandMap]
  -- `ρ(y) (ρ(h) v) = ρ(y h) v`.
  have hyh : algIrrepGLRepρ n lam k y (algIrrepGLRepρ n lam k h v)
      = algIrrepGLRepρ n lam k (y * h) v := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [hyh, hinv g u (algIrrepGLRepρ n lam k (y * h) v)]
  -- `ρ(g⁻¹) (ρ(y h) v) = ρ(g⁻¹ (y h)) v`.
  have hgyh : algIrrepGLRepρ n lam k g⁻¹ (algIrrepGLRepρ n lam k (y * h) v)
      = algIrrepGLRepρ n lam k (g⁻¹ * (y * h)) v := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [hgyh]
  -- RHS: peel off the bi-action via the one-sided intertwining lemmas.
  have hbi : localBiRep k n (g, h) (peterWeylSummandMap n lam k (u ⊗ₜ[k] v))
      = localLeftRep k n g (localRightRep k n h
          (peterWeylSummandMap n lam k (u ⊗ₜ[k] v))) := by
    rw [localBiRep_apply, localLeftRep_apply, localRightRep_apply]
  rw [hbi,
    evalGLAway_localLeftRep g y (localRightRep k n h (peterWeylSummandMap n lam k (u ⊗ₜ[k] v))),
    evalGLAway_localRightRep h (g⁻¹ * y) (peterWeylSummandMap n lam k (u ⊗ₜ[k] v)),
    evalGLAway_peterWeylSummandMap]
  -- `g⁻¹ * (y * h)` versus `(g⁻¹ * y) * h`: associativity.
  rw [mul_assoc]

/-! ## Step 4: matrix-coefficient correspondence for equivariant maps `L_λ → R` -/

/-- **Matrix-coefficient correspondence (Step 4 of §5.23(ii)).** Any `GL_n`-equivariant
`k`-linear map `ι : L_λ → R = A[det⁻¹]` intertwining the Schur-module action
`algIrrepGLRepρ` with the right-translation representation `localRightRep` realizes each
`ι v` as a matrix coefficient of the per-summand map: there is a contragredient vector
`u ∈ L*_λ` with `ι v = peterWeylSummandMap (u ⊗ v)` for every `v`.

Concretely `u = e⁻¹(ε ∘ ι)` where `ε φ = evalGLAway φ 1` is evaluation at the identity
and `e = algIrrepGLDualIso`. The matrix coefficient of `ι` at `v`,
`g ↦ ε(localRightRep g (ι v)) = evalGLAway (ι v) g`, equals `⟨u, ρ(g) v⟩` through
`evalGLAway`, and `evalGLAway`-injectivity (`evalGLAway_injective`, `k` infinite via
`CharZero`) upgrades the pointwise identity to equality in `R`. -/
theorem equivariant_eq_peterWeylSummandMap
    (ι : AlgIrrepGL n lam k →ₗ[k] Localization.Away (detPoly k n))
    (hι : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGL n lam k),
      ι (algIrrepGLRepρ n lam k g v) = localRightRep k n g (ι v))
    (v : AlgIrrepGL n lam k) :
    ∃ u : AlgIrrepGLDual n lam k,
      ι v = peterWeylSummandMap n lam k (u ⊗ₜ[k] v) := by
  -- `ε ∘ ι` as a linear functional `L_λ → k`, `w ↦ evalGLAway (ι w) 1`.
  let epsIota : AlgIrrepGL n lam k →ₗ[k] k :=
    { toFun := fun w => evalGLAway (ι w) 1
      map_add' := fun w w' => by rw [map_add, map_add]; rfl
      map_smul' := fun c w => by
        rw [map_smul, RingHom.id_apply, evalGLAway_smul, Pi.smul_apply, smul_eq_mul] }
  -- Transport this functional back through the contragredient identity to get `u`.
  refine ⟨(algIrrepGLDualIso n lam k).symm epsIota, ?_⟩
  -- The chosen `u` pairs against any `w` as `ε(ι w) = evalGLAway (ι w) 1`.
  have hpair : ∀ w, algIrrepDualPairing n lam k
      ((algIrrepGLDualIso n lam k).symm epsIota ⊗ₜ[k] w) = evalGLAway (ι w) 1 := by
    intro w
    rw [algIrrepDualPairing_tmul, LinearEquiv.apply_symm_apply, contractLeft_apply]
    rfl
  -- Compare in the faithful functions-on-`GL` model.
  apply evalGLAway_injective
  funext g
  rw [evalGLAway_peterWeylSummandMap, hpair (algIrrepGLRepρ n lam k g v), hι,
    evalGLAway_localRightRep, one_mul]

/-- **Image of an equivariant map lands in the per-summand range.** Packaging
`equivariant_eq_peterWeylSummandMap`: for any `GL_n`-equivariant `ι : L_λ → R`
intertwining `algIrrepGLRepρ` with right translation `localRightRep`, the image of `ι`
is contained in `LinearMap.range (peterWeylSummandMap n lam k)`. This is the inclusion
that, summed over all equivariant copies of `L_λ` inside `R`, drives surjectivity of the
Peter-Weyl summand map onto the `L_λ`-isotypic part of `R`. -/
theorem equivariant_range_le_peterWeylSummandMap
    (ι : AlgIrrepGL n lam k →ₗ[k] Localization.Away (detPoly k n))
    (hι : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGL n lam k),
      ι (algIrrepGLRepρ n lam k g v) = localRightRep k n g (ι v)) :
    LinearMap.range ι ≤ LinearMap.range (peterWeylSummandMap n lam k) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := equivariant_eq_peterWeylSummandMap n lam k ι hι v
  exact ⟨u ⊗ₜ[k] v, hu.symm⟩

end Etingof
