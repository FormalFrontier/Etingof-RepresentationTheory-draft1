import Mathlib
import EtingofRepresentationTheory.Chapter5.RightTranslationHull
import EtingofRepresentationTheory.Chapter5.QuotDetDegreeAlgebraic
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2

/-!
# Complete reducibility of the right-translation hull (Peter-Weyl, step 2)

This file carries out **step 2** of the Cauchy route for
`Theorem5_23_2_PeterWeyl.peterWeylSummandMap_iSup_range_eq_top` (issue #5577, a sub-issue of
#5572): the finite-dimensional right-translation hull `rightHull φ` of an element
`φ ∈ R = Localization.Away (detPoly k N)`, after a `det^r`-twist, is a polynomial (in fact
algebraic) representation, hence **completely reducible** as a `localRightRep`-representation.

The genuinely new content is the bridge `numEmbed_intertwines`: the `k`-linear numerator
embedding `numEmbed r : p ↦ algebraMap p · det⁻ʳ` intertwines the **polynomial-side** right
translation `polyRightRep` with the `det^r`-**twisted** localization action
`charTwistRep (detChar^r) (localRightRep)`. Concretely, the twist by `det^r` is exactly what
clears the denominator `det⁻ʳ`: right translation scales `det⁻ʳ` by `det(g)⁻ʳ`, and the twist
multiplies back by `det(g)^r`.

Through this bridge, all sorry-free:

* `boundedRightRep_isAlgebraic` — right translation on the finite-dimensional space of
  polynomials of bounded total degree is an algebraic representation (its matrix coefficients on
  the monomial basis are the polynomials `rightTransPoly`, exactly as for the homogeneous
  Cauchy component `polyRightDegreeFDRep_isAlgebraic`).

* `rightHull_isSemisimple` — **complete reducibility of the right-translation hull**: the hull,
  as a `localRightRep`-representation, is a semisimple `k[GL_N]`-module. The `det^r`-twist of the
  hull is algebraic (transport `boundedRightRep_isAlgebraic` across `numEmbed` via
  `IsAlgebraicRepresentation.of_linearEquiv`, restricting to the hull via
  `IsAlgebraicRepresentation.restrict`), hence completely reducible (`Theorem5_23_2_i`);
  untwisting by `det⁻ʳ` (`isSemisimpleModule_charTwistRep`) recovers the hull.

The finer statement — that the constituents are exactly the irreducibles `L_λ = algIrrepGLRepρ`,
with weights shifted by `-r·(1,…,1)` — uses the constituent characterization
`quotDetRep_irreducible_constituent_lastWeight_zero` and is tracked separately.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof.RightTranslationHull

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.LocalizationGLAction Etingof.PolyRightGrading Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The numerator embedding intertwines `polyRightRep` with the `det^r`-twisted action -/

/-- **The det-twist clears the denominator.** The numerator embedding `numEmbed r`
(`p ↦ algebraMap p · det⁻ʳ`) intertwines the polynomial-side right translation `polyRightRep`
with the `det^r`-twisted localization action `charTwistRep (detChar^r) (localRightRep)`:

`(det g)^r • localRightRep g (numEmbed r p) = numEmbed r (polyRightRep g p)`.

Right translation scales `det⁻ʳ` by `det(g)⁻ʳ` (`localRightRep_normalForm`); twisting by `det^r`
multiplies back by `det(g)^r`, exactly cancelling the denominator scaling and leaving the genuine
polynomial right translation `polyRightRep g p` on the numerator. -/
theorem numEmbed_intertwines (r : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    charTwistRep (detChar k N ^ r) (localRightRep k N) g (numEmbed r p)
      = numEmbed r (polyRightRep k N g p) := by
  have hdet : ((detChar k N) g : k) = (g : Matrix (Fin N) (Fin N) k).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  rw [charTwistRep_apply, numEmbed_apply, localRightRep_normalForm, ← numEmbed_apply, smul_smul]
  have hscal : ((detChar k N ^ r) g : k) * ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r = 1 := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdet, ← mul_pow,
      mul_inv_cancel₀ (by rw [← hdet]; exact (detChar k N g).ne_zero), one_pow]
  rw [hscal, one_smul]

/-! ### Bounded-degree right translation is an algebraic representation -/

/-- **Polynomials of total degree `≤ d` as a `polyRightRep`-subrepresentation.** Right
translation does not raise total degree (`rTransAlgHom_totalDegree_le`), so this finite-dimensional
space is `polyRightRep`-invariant. -/
def boundedSubrep (k : Type*) [Field k] (N d : ℕ) :
    Subrepresentation (polyRightRep k N) where
  toSubmodule := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d
  apply_mem_toSubmodule g f hf := by
    rw [MvPolynomial.mem_restrictTotalDegree, polyRightRep_apply]
    exact (rTransAlgHom_totalDegree_le _ _).trans
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hf)

instance boundedSubrep_finite (k : Type*) [Field k] (N d : ℕ) :
    Module.Finite k (boundedSubrep k N d).toSubmodule :=
  inferInstanceAs
    (Module.Finite k (MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d))

/-- The bounded-degree subrepresentation action, coerced back to a polynomial, is `polyRightRep`. -/
theorem boundedSubrep_toRepresentation_coe (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (w : (boundedSubrep k N d).toSubmodule) :
    ((boundedSubrep k N d).toRepresentation g w : MvPolynomial (Fin N × Fin N) k)
      = polyRightRep k N g (w : MvPolynomial (Fin N × Fin N) k) :=
  LinearMap.restrict_coe_apply (polyRightRep k N g)
    ((boundedSubrep k N d).apply_mem_toSubmodule g) w

/-- **Right translation on bounded-degree polynomials is algebraic.** On the monomial basis of
`restrictTotalDegree ≤ d`, right translation acts with matrix coefficients `rightTransPoly`,
polynomial in the entries of `g` (`evalAtGL_rightTransPoly`). Mirrors the homogeneous Cauchy
component `polyRightDegreeFDRep_isAlgebraic`, over the full `≤ d` filtration. -/
theorem boundedRightRep_isAlgebraic (k : Type*) [Field k] (N d : ℕ) :
    Etingof.IsAlgebraicRepresentation N
      ⇑(boundedSubrep k N d).toRepresentation := by
  classical
  set W := (boundedSubrep k N d).toSubmodule with hW
  -- the inclusion `W ↪ k[Xᵢⱼ]` as a single linear map, used consistently to avoid
  -- coercion/`subtype` mismatches
  let val : W →ₗ[k] MvPolynomial (Fin N × Fin N) k := W.subtype
  have hval_inj : Function.Injective val := Submodule.injective_subtype W
  have hval_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (w : W),
      val ((boundedSubrep k N d).toRepresentation g w) = polyRightRep k N g (val w) :=
    fun g w => boundedSubrep_toRepresentation_coe d g w
  -- index set: monomials of total degree `≤ d`
  set S : Finset ((Fin N × Fin N) →₀ ℕ) :=
    (Finset.range (d + 1)).biUnion (fun e => Finset.univ.finsuppAntidiag e) with hS
  have hmemS : ∀ μ : (Fin N × Fin N) →₀ ℕ, μ ∈ S ↔ (μ.sum fun _ e => e) ≤ d := by
    intro μ
    have hbridge : (μ.sum fun _ e => e) = Finset.univ.sum ⇑μ :=
      Finsupp.sum_fintype μ (fun _ n => n) (fun _ => rfl)
    rw [hS]
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_finsuppAntidiag,
      Finset.subset_univ, and_true]
    constructor
    · rintro ⟨e, he, heq⟩; omega
    · intro h; exact ⟨Finset.univ.sum ⇑μ, by omega, rfl⟩
  -- the degree-`≤ d` monomials, as elements of the carrier `W`
  have hmem : ∀ s : {s // s ∈ S},
      (MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) ∈ W := by
    intro s
    refine (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_
    rw [MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
    exact (hmemS _).mp s.2
  let v : {s // s ∈ S} → W :=
    fun s => ⟨MvPolynomial.monomial (↑s) 1, hmem s⟩
  have hvval : ∀ s, val (v s) = MvPolynomial.monomial (↑s) 1 := fun _ => rfl
  -- linear independence of the monomial family
  have hli : LinearIndependent k v := by
    have hb : LinearIndependent k
        (fun s : {s // s ∈ S} => MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
      have hcomp := (MvPolynomial.basisMonomials (Fin N × Fin N) k).linearIndependent.comp
        (fun s : {s // s ∈ S} => (↑s : (Fin N × Fin N) →₀ ℕ)) Subtype.val_injective
      simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials] using hcomp
    exact hb.of_comp val
  -- the monomials span `W`
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro w -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => MvPolynomial.coeff (↑s) (val w), hval_inj ?_⟩
    have hsupp : ∀ p ∈ (val w).support, p ∈ S := by
      intro p hp
      rw [hmemS]
      exact (MvPolynomial.le_totalDegree hp).trans
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp w.2)
    rw [map_sum]
    simp_rw [map_smul, hvval]
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach S
      (fun p => MvPolynomial.coeff p (val w) • MvPolynomial.monomial p (1 : k))]
    simp_rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
    conv_rhs => rw [(val w).as_sum]
    refine (Finset.sum_subset hsupp ?_).symm
    intro p _ hp
    rw [MvPolynomial.notMem_support_iff.mp hp]
    exact MvPolynomial.monomial_zero
  -- the monomial basis of `W`
  let b : Module.Basis {s // s ∈ S} k W :=
    Module.Basis.mk hli hsp
  have hbv : ∀ s, val (b s) = MvPolynomial.monomial (↑s) 1 := by
    intro s; rw [show b s = v s from Module.Basis.mk_apply hli hsp s]; exact hvval s
  -- reading a coordinate off `b` is reading a monomial coefficient
  have hrepr : ∀ (w : W) (a : {s // s ∈ S}),
      b.repr w a = MvPolynomial.coeff (↑a) (val w) := by
    intro w a
    have hexp : val w
        = ∑ s : {s // s ∈ S}, b.repr w s •
            MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [map_smul, hbv s]
    rw [hexp, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a
      (fun s _ hsa => by rw [if_neg (fun h => hsa (Subtype.ext h)), mul_zero])
      (fun ha => absurd (Finset.mem_univ a) ha)]
    rw [if_pos rfl, mul_one]
  -- assemble: the matrix coefficients are `rightTransPoly`
  refine ⟨Fintype.card {s // s ∈ S}, b.reindex (Fintype.equivFin {s // s ∈ S}),
    fun a c => Etingof.rightTransPoly k N
      (↑((Fintype.equivFin {s // s ∈ S}).symm c))
      (↑((Fintype.equivFin {s // s ∈ S}).symm a)), fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, hrepr, hval_rho, hbv,
    Etingof.evalAtGL_rightTransPoly]

/-! ### The twisted hull is algebraic, hence the hull is completely reducible -/

/-- **`numEmbed r` is injective.** It is `algebraMap` (injective into the localization, since the
powers of `detPoly` are non-zero-divisors) followed by multiplication by the unit `det⁻ʳ`. -/
theorem numEmbed_injective (r : ℕ) :
    Function.Injective
      (numEmbed r : MvPolynomial (Fin N × Fin N) k →ₗ[k] Localization.Away (detPoly k N)) := by
  intro p q hpq
  rw [numEmbed_apply, numEmbed_apply] at hpq
  have hu : IsUnit (IsLocalization.Away.invSelf (detPoly k N) ^ r) :=
    IsUnit.of_mul_eq_one
      ((algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))
        (detPoly k N)) ^ r)
      (by rw [mul_comm]; exact algebraMap_detPoly_pow_mul_invSelf_pow r)
  exact algebraMap_away_injective (hu.mul_right_cancel hpq)

/-- **Complete reducibility of the right-translation hull (Cauchy step 2).** The hull
`rightHull φ`, as a `localRightRep`-representation, is a semisimple `k[GL_N]`-module.

The `det^r`-twist of the hull (`r` the normal-form exponent of `φ`) is, via `numEmbed`, equivalent
to a `polyRightRep`-invariant subspace of the bounded-degree polynomials, hence algebraic
(`boundedRightRep_isAlgebraic` + `IsAlgebraicRepresentation.restrict` /
`.of_linearEquiv`); an algebraic representation is completely reducible (`Theorem5_23_2_i`), and
untwisting by `det⁻ʳ` (`isSemisimpleModule_charTwistRep`) recovers the hull. -/
theorem rightHull_isSemisimple (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}
    (φ : Localization.Away (detPoly k N)) :
    IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (rightHullSubrep φ).toRepresentation) := by
  classical
  obtain ⟨r, Q, hQ⟩ := exists_invSelf_normalForm φ
  set d := Q.totalDegree with hd
  haveI : Module.Finite k (rightHull φ) := rightHull_finiteDimensional φ
  haveI : Module.Finite k (rightHullSubrep φ).toSubmodule :=
    inferInstanceAs (Module.Finite k (rightHull φ))
  -- the numerator embedding restricted to bounded-degree polynomials, landing in `R`
  set ι : (boundedSubrep k N d).toSubmodule →ₗ[k] Localization.Away (detPoly k N) :=
    (numEmbed r).comp (boundedSubrep k N d).toSubmodule.subtype with hι
  have hι_apply : ∀ w : (boundedSubrep k N d).toSubmodule,
      ι w = numEmbed r (w : MvPolynomial (Fin N × Fin N) k) := fun _ => rfl
  have hι_inj : Function.Injective ι :=
    (numEmbed_injective r).comp (Submodule.injective_subtype _)
  -- `ι` intertwines bounded right translation with the `det^r`-twisted localization action
  have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (w : (boundedSubrep k N d).toSubmodule),
      ι ((boundedSubrep k N d).toRepresentation g w)
        = charTwistRep (detChar k N ^ r) (localRightRep k N) g (ι w) := by
    intro g w
    rw [hι_apply, boundedSubrep_toRepresentation_coe, hι_apply, numEmbed_intertwines]
  -- the hull lies in the image of `ι`
  have hIII : rightHull φ ≤ LinearMap.range ι := by
    rw [rightHull, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    refine ⟨⟨((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • polyRightRep k N g Q, ?_⟩, ?_⟩
    · refine (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_
      refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
      rw [polyRightRep_apply]
      exact rTransAlgHom_totalDegree_le _ _
    · change _ = localRightRep k N g φ
      rw [hι_apply, map_smul, numEmbed_apply, hQ, localRightRep_normalForm]
  -- the preimage subspace, invariant under bounded right translation
  set U : Submodule k (boundedSubrep k N d).toSubmodule :=
    Submodule.comap ι (rightHull φ) with hU
  have hU_inv : ∀ g, ∀ v ∈ U, (boundedSubrep k N d).toRepresentation g v ∈ U := by
    intro g v hv
    rw [hU, Submodule.mem_comap] at hv ⊢
    rw [hinter, charTwistRep_apply]
    exact Submodule.smul_mem _ _ (localRightRep_mem_rightHull φ g hv)
  haveI : Module.Finite k U := inferInstance
  -- `ι` carries `U` isomorphically onto the hull
  have hmap : U.map ι = (rightHullSubrep φ).toSubmodule := by
    show U.map ι = rightHull φ
    rw [hU, Submodule.map_comap_eq, inf_eq_right.mpr hIII]
  let e : U ≃ₗ[k] (rightHullSubrep φ).toSubmodule :=
    (Submodule.equivMapOfInjective ι hι_inj U).trans (LinearEquiv.ofEq _ _ hmap)
  have he_coe : ∀ y : U,
      (e y : Localization.Away (detPoly k N)) = ι (y : (boundedSubrep k N d).toSubmodule) := by
    intro y
    show ((LinearEquiv.ofEq _ _ hmap) (Submodule.equivMapOfInjective ι hι_inj U y) :
        Localization.Away (detPoly k N)) = _
    rw [LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply]
  have hrh_coe : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (z : (rightHullSubrep φ).toSubmodule),
      ((rightHullSubrep φ).toRepresentation g z : Localization.Away (detPoly k N))
        = localRightRep k N g (z : Localization.Away (detPoly k N)) :=
    fun g z => LinearMap.restrict_coe_apply (localRightRep k N g)
      ((rightHullSubrep φ).apply_mem_toSubmodule g) z
  -- `e` intertwines the restricted bounded action with the twisted hull action
  have hcomm : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (y : U),
      e (((boundedSubrep k N d).toRepresentation g).restrict (hU_inv g) y)
        = charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation g (e y) := by
    intro g y
    apply Subtype.ext
    have hL : (↑(e (((boundedSubrep k N d).toRepresentation g).restrict (hU_inv g) y)) :
        Localization.Away (detPoly k N))
        = charTwistRep (detChar k N ^ r) (localRightRep k N) g (ι (y : _)) := by
      rw [he_coe, LinearMap.restrict_coe_apply, hinter]
    have hR : (↑(charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation g (e y)) :
        Localization.Away (detPoly k N))
        = charTwistRep (detChar k N ^ r) (localRightRep k N) g (ι (y : _)) := by
      rw [charTwistRep_apply, Submodule.coe_smul, hrh_coe, he_coe, charTwistRep_apply]
    rw [hL, hR]
  -- the twisted hull is algebraic
  have htwAlg : Etingof.IsAlgebraicRepresentation N
      ⇑(charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation) :=
    ((boundedRightRep_isAlgebraic k N d).restrict U hU_inv).of_linearEquiv e hcomm
  -- algebraic ⟹ semisimple; untwist by `det⁻ʳ` to recover the hull
  haveI hss_tw : IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation).asModule :=
    Etingof.Theorem5_23_2_i N
      (charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation) htwAlg
  have huntwist : charTwistRep (detChar k N ^ r)⁻¹
      (charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation)
      = (rightHullSubrep φ).toRepresentation := by
    ext g v
    rw [charTwistRep_apply, charTwistRep_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  have hfin := isSemisimpleModule_charTwistRep (detChar k N ^ r)⁻¹
    (charTwistRep (detChar k N ^ r) (rightHullSubrep φ).toRepresentation)
  rwa [huntwist] at hfin

end Etingof.RightTranslationHull
