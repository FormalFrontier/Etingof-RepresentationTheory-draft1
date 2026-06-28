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

The key reusable building blocks proved here:

* `boundedRightRep_isAlgebraic` — right translation on the finite-dimensional space of
  polynomials of bounded total degree is an algebraic representation (its matrix coefficients on
  the monomial basis are the polynomials `rightTransPoly`, exactly as for the homogeneous
  Cauchy component `polyRightDegreeFDRep_isAlgebraic`).

* `numEmbed_intertwines` — the `numEmbed r` intertwining lemma above.

These feed the assembly of step 2: the `det^r`-twist of the hull is algebraic (transport
`boundedRightRep_isAlgebraic` across `numEmbed` via `IsAlgebraicRepresentation.of_linearEquiv`,
restrict to the hull via `IsAlgebraicRepresentation.restrict`), hence the hull as a
`localRightRep`-representation is semisimple/completely reducible (`Theorem5_23_2_i` plus
untwisting via `isSemisimpleModule_charTwistRep`).

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

end Etingof.RightTranslationHull
