import Mathlib
import EtingofRepresentationTheory.Chapter5.LocalizationGLRightAction
import EtingofRepresentationTheory.Chapter5.DetLocalization
import EtingofRepresentationTheory.Chapter5.PolyRightGrading

/-!
# The finite-dimensional right-translation hull (Peter-Weyl, steps 1 & 3)

This file builds the **finite-dimensional right-translation hull** of an element of the
coordinate ring `R = k[gᵢⱼ][1/det] = Localization.Away (detPoly k N)`, the first piece of the
Cauchy / abstract Peter-Weyl argument that "every regular function is a matrix coefficient"
(Etingof §5.23(ii), the intended route for
`Theorem5_23_2_PeterWeyl.peterWeylSummandMap_iSup_range_eq_top`, issue #5572).

Given `φ ∈ R`, its **right-translation hull** `rightHull φ` is the `k`-span of the orbit
`{R_g φ : g ∈ GL_N}` under the right-translation representation `localRightRep`. The two
genuinely useful facts about it, proved here sorry-free:

* **Invariance + self-membership.** `rightHull φ` is `localRightRep`-stable
  (`localRightRep_mem_rightHull`, packaged as `rightHullSubrep`) and contains `φ`
  (`self_mem_rightHull`).

* **Finite dimensionality** (`rightHull_finiteDimensional`). Writing `φ = Q · det⁻ʳ` in normal
  form (`exists_invSelf_normalForm`), the right translate is
  `R_g φ = (det g)⁻ʳ · (R_g Q) · det⁻ʳ` (`localRightRep_normalForm`), and right translation
  does not raise total degree (`rTransAlgHom_totalDegree_le`), so the whole orbit lies in the
  image under `numEmbed r : p ↦ algebraMap p · det⁻ʳ` of the finite-dimensional space of
  polynomials of total degree `≤ Q.totalDegree`. Hence the span is finite-dimensional.

* **Matrix-coefficient realization (step 3).** `evalGLAway (R_g φ) 1 = φ(g)`: through the
  faithful functions-on-`GL` model `evalGLAway`, `φ` is the matrix coefficient of its hull
  `(rightHull φ, localRightRep, ε)` with `ε` the "evaluation at the identity" functional. This is
  `Etingof.DetInvElim.evalGLAway_localRightRep` at evaluation point `1` plus `one_mul`; it is not
  repackaged here because `evalGLAway` is an `IsLocalization.Away.lift` and re-deriving the
  identity outside `DetInvElim`'s rewrite context triggers an `IsLocalization` `isDefEq` blow-up.

The remaining steps of the Cauchy route — det-twisting the hull to a polynomial representation
and applying complete reducibility (`decompose_polynomial_gl_rep`), and the
matrix-coefficient correspondence relating arbitrary `GL`-maps `L_λ → R` to
`peterWeylSummandMap` — are tracked as separate sub-issues of #5572.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof.RightTranslationHull

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.LocalizationGLAction Etingof.PolyRightGrading

variable {k : Type*} [Field k] {N : ℕ}

/-- **Right translation does not raise total degree.** The substitution endomorphism
`rTransAlgHom M` sends each variable to a homogeneous degree-`1` linear form
(`rTransAlgHom_isHomogeneous`), so applying it to the homogeneous decomposition of `Q` keeps
every component in its degree; hence `(rTransAlgHom M Q).totalDegree ≤ Q.totalDegree`. -/
theorem rTransAlgHom_totalDegree_le (M : Matrix (Fin N) (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    (rTransAlgHom M Q).totalDegree ≤ Q.totalDegree := by
  conv_lhs => rw [← Q.sum_homogeneousComponent]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  exact (rTransAlgHom_isHomogeneous M
    (MvPolynomial.homogeneousComponent_isHomogeneous i Q)).totalDegree_le.trans hi

/-- The right-translation action of `g` on the formal inverse `det⁻¹`, written through the
algebra endomorphism `localRightAlgHom`: `R_g det⁻¹ = (det g)⁻¹ · det⁻¹`. This is
`localRightRep_invSelf` transported across the definitional identity
`localRightRep g = localRightAlgHom g` so that `map_mul` / `map_pow` of the algebra
homomorphism are available alongside it. -/
theorem localRightAlgHom_invSelf (g : Matrix.GeneralLinearGroup (Fin N) k) :
    localRightAlgHom g (IsLocalization.Away.invSelf (detPoly k N))
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ •
          IsLocalization.Away.invSelf (detPoly k N) :=
  localRightRep_invSelf g

/-- **Normal form of a right translate.** For `φ = algebraMap Q · det⁻ʳ`, right translation by
`g` multiplies the denominator by the scalar `(det g)⁻ʳ` and acts on the numerator by
`polyRightRep`: `R_g φ = (det g)⁻ʳ · (algebraMap (R_g Q) · det⁻ʳ)`. This is the computation that
confines the orbit of `φ` to a finite-dimensional subspace. -/
theorem localRightRep_normalForm (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    localRightRep k N g (algebraMap _ _ Q * IsLocalization.Away.invSelf (detPoly k N) ^ r)
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
          (algebraMap _ _ (polyRightRep k N g Q)
            * IsLocalization.Away.invSelf (detPoly k N) ^ r) := by
  rw [localRightRep_apply, map_mul, localRightAlgHom_algebraMap, map_pow,
    localRightAlgHom_invSelf, smul_pow, mul_smul_comm, ← polyRightRep_apply]

/-- **The `k`-linear numerator embedding** `p ↦ algebraMap p · det⁻ʳ` at denominator exponent
`r`. Composition of the (`k`-linear) structure map `A →ₐ[k] R` with right multiplication by
`det⁻ʳ`; its image of the finite-dimensional space of bounded-degree polynomials is the
finite-dimensional subspace confining the right-translation orbit. -/
def numEmbed (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] Localization.Away (detPoly k N) :=
  (LinearMap.mulRight k (IsLocalization.Away.invSelf (detPoly k N) ^ r)).comp
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N))).toLinearMap

@[simp] theorem numEmbed_apply (r : ℕ) (p : MvPolynomial (Fin N × Fin N) k) :
    numEmbed r p
      = algebraMap _ (Localization.Away (detPoly k N)) p
          * IsLocalization.Away.invSelf (detPoly k N) ^ r :=
  rfl

/-- **The right-translation hull of `φ`.** The `k`-span of the right-translation orbit
`{R_g φ : g ∈ GL_N}` of `φ` in the coordinate ring `R = Localization.Away (detPoly k N)`. -/
def rightHull (φ : Localization.Away (detPoly k N)) :
    Submodule k (Localization.Away (detPoly k N)) :=
  Submodule.span k
    (Set.range (fun g : Matrix.GeneralLinearGroup (Fin N) k => localRightRep k N g φ))

/-- `φ` itself lies in its right-translation hull (translate by `1`). -/
theorem self_mem_rightHull (φ : Localization.Away (detPoly k N)) : φ ∈ rightHull φ := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- **`localRightRep`-invariance of the hull.** Right translation maps the orbit into itself
(`R_h (R_g φ) = R_{hg} φ`), hence maps `rightHull φ` into itself. -/
theorem localRightRep_mem_rightHull (φ : Localization.Away (detPoly k N))
    (h : Matrix.GeneralLinearGroup (Fin N) k) {x : Localization.Away (detPoly k N)}
    (hx : x ∈ rightHull φ) : localRightRep k N h x ∈ rightHull φ := by
  have hmap : Submodule.map (localRightRep k N h) (rightHull φ) ≤ rightHull φ := by
    simp only [rightHull, Submodule.map_span]
    apply Submodule.span_le.2
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨h * g, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
  exact hmap ⟨x, hx, rfl⟩

/-- **The right-translation hull as a subrepresentation** of `localRightRep`. Packages
`localRightRep_mem_rightHull` so that downstream the hull can be det-twisted to a polynomial
representation and decomposed (`decompose_polynomial_gl_rep`). -/
def rightHullSubrep (φ : Localization.Away (detPoly k N)) :
    Subrepresentation (localRightRep k N) where
  toSubmodule := rightHull φ
  apply_mem_toSubmodule g _ hv := localRightRep_mem_rightHull φ g hv

/-- **Finite dimensionality of the hull.** The orbit of `φ = algebraMap Q · det⁻ʳ` lands in the
image under `numEmbed r` of the finite-dimensional space of polynomials of total degree
`≤ Q.totalDegree` (`localRightRep_normalForm` + `rTransAlgHom_totalDegree_le`), so its span is
finite-dimensional. -/
theorem rightHull_finiteDimensional (φ : Localization.Away (detPoly k N)) :
    FiniteDimensional k (rightHull φ) := by
  obtain ⟨r, Q, hQ⟩ := exists_invSelf_normalForm φ
  set S := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k Q.totalDegree with hS
  set F : S →ₗ[k] Localization.Away (detPoly k N) := (numEmbed r).comp S.subtype with hF
  have hfd : FiniteDimensional k (LinearMap.range F) := inferInstance
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range F) ?_
  rw [rightHull]
  apply Submodule.span_le.2
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_range]
  refine ⟨⟨((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • polyRightRep k N g Q, ?_⟩, ?_⟩
  · apply Submodule.smul_mem
    rw [hS, MvPolynomial.mem_restrictTotalDegree, polyRightRep_apply]
    exact rTransAlgHom_totalDegree_le _ _
  · rw [hF, LinearMap.comp_apply]
    change numEmbed r (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • polyRightRep k N g Q)
        = localRightRep k N g φ
    rw [map_smul, numEmbed_apply, hQ, localRightRep_normalForm]

/- **Step 3 (matrix-coefficient realization), specialized.** Through the faithful
functions-on-`GL` model `evalGLAway`, every `φ` is the matrix coefficient of its own hull
`(rightHull φ, localRightRep, ε)` with `ε` the "evaluation at the identity" functional:
`evalGLAway (R_g φ) 1 = φ(g)`. This is exactly `Etingof.DetInvElim.evalGLAway_localRightRep`
specialized to evaluation point `1` (translate `g`), followed by `one_mul`. We do not repackage
it as a standalone lemma here: `evalGLAway` is an `IsLocalization.Away.lift`, and re-deriving the
identity outside the rewrite context of `DetInvElim` triggers an `IsLocalization` `isDefEq`
blow-up. Downstream consumers should invoke `evalGLAway_localRightRep` directly. -/
end Etingof.RightTranslationHull
