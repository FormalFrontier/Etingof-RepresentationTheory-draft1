import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotientDegree
import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition

/-!
# The right-`GL_N` grading of `A/det` and single-degree reduction

This file builds the **part-A** deliverable of issue #4905 (parent #4896, route
doc `progress/kernel-lemma-K-route.md`): the right-`GL_N`-equivariant grading of
the determinant quotient

  `A/det = k[Xᵢⱼ]/(det)`     (`quotDetRep`, `KernelLemmaKPrime.lean`)

into its homogeneous degree components `(A/det)_d` (`quotDetDegreeSubrep`,
`CauchyDetQuotientDegree.lean`), and the **single-degree reduction**: a
finite-dimensional *simple* `GL_N`-subrep of `A/det` lives in a single degree.

## The homogeneous projection on `A/det`

Right translation `polyRightRep` is degree preserving
(`polyRightRep_isHomogeneous`), so it commutes with the homogeneous-component
projection `MvPolynomial.homogeneousComponent d`
(`homogeneousComponent_polyRightRep`). The determinant ideal `(det)` is a *graded*
ideal — `homogeneousComponent d` maps it into itself
(`homogeneousComponent_mem_detSubmodule`), because `det` is homogeneous of degree
`N` and `(det)` is principal. Hence `homogeneousComponent d` descends through the
quotient to a `GL_N`-equivariant projection `quotDetProj d : A/det → A/det` whose
image is the degree-`d` component `(A/det)_d`.

## The grading and the single-degree reduction

* `quotDetDegreeSubrep_iSup_eq_top` / `quotDetDegreeSubrep_iSupIndep` — the
  components `(A/det)_d` span and are independent: `A/det = ⊕_d (A/det)_d` as a
  `GL_N`-representation. Independence is the graded-ideal property read through
  the projections `quotDetProj d` (which act as the identity on `(A/det)_d` and
  vanish on `(A/det)_e` for `e ≠ d`).

* `exists_degree_embedding_of_simple` — the reduction the #4905 assembly consumes.
  Given a finite-dimensional simple `GL_N`-rep `L` with a `GL_N`-equivariant
  injection `φ : L → A/det`, there is a degree `d` and a `GL_N`-equivariant
  injection `L → quotDetDegreeFDRep k N d`. Proof: each `quotDetProj d ∘ φ` is an
  equivariant map out of the simple `L`, hence (Schur) zero or injective; since
  `φ v = ∑_d quotDetProj d (φ v)` is a finite sum and `φ v ≠ 0` for `v ≠ 0`, some
  component is injective.
-/

namespace Etingof.CauchyDetQuotient

open MvPolynomial Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.KernelLemmaKPrime Etingof.DetShiftIso Etingof.DetLocalization

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The homogeneous-component projection commutes with right translation -/

/-- **Right translation commutes with the homogeneous-component projection.**
Since `polyRightRep g` preserves the total-degree grading
(`polyRightRep_isHomogeneous`), extracting the degree-`d` component before or after
translating gives the same result. -/
theorem homogeneousComponent_polyRightRep (g : Matrix.GeneralLinearGroup (Fin N) k)
    (d : ℕ) (f : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.homogeneousComponent d (polyRightRep k N g f)
      = polyRightRep k N g (MvPolynomial.homogeneousComponent d f) := by
  have key : polyRightRep k N g f
      = ∑ e ∈ Finset.range (f.totalDegree + 1),
          polyRightRep k N g (MvPolynomial.homogeneousComponent e f) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [key, map_sum]
  rw [Finset.sum_congr rfl fun e _ =>
    MvPolynomial.homogeneousComponent_of_mem (m := d) (n := e)
      ((MvPolynomial.mem_homogeneousSubmodule e _).2
        (polyRightRep_isHomogeneous g (MvPolynomial.homogeneousComponent_isHomogeneous e f)))]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · next h =>
    rw [Finset.mem_range, not_lt] at h
    rw [MvPolynomial.homogeneousComponent_eq_zero d f (by omega), map_zero]

/-! ### The determinant ideal is graded -/

/-- **The determinant ideal is graded.** The homogeneous-component projection
`homogeneousComponent d` maps the determinant submodule `(det)` into itself: every
element of `(det)` is `det · Q`, whose degree-`d` component is `det` times a
homogeneous component of `Q` (or zero), again a multiple of `det`. -/
theorem homogeneousComponent_mem_detSubmodule (d : ℕ)
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f ∈ detSubmodule k N) :
    MvPolynomial.homogeneousComponent d f ∈ detSubmodule k N := by
  rw [← range_mulDet, LinearMap.mem_range] at hf
  obtain ⟨Q, rfl⟩ := hf
  rw [mulDet_apply]
  have hexp : MvPolynomial.homogeneousComponent d (detPoly k N * Q)
      = ∑ e ∈ Finset.range (Q.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (detPoly k N * MvPolynomial.homogeneousComponent e Q) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q, Finset.mul_sum, map_sum]
  rw [hexp]
  refine Submodule.sum_mem _ fun e _ => ?_
  have hhom : (detPoly k N * MvPolynomial.homogeneousComponent e Q).IsHomogeneous (N + e) :=
    detPoly_isHomogeneous.mul (MvPolynomial.homogeneousComponent_isHomogeneous e Q)
  rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hhom)]
  split
  · rw [← range_mulDet, LinearMap.mem_range]
    exact ⟨MvPolynomial.homogeneousComponent e Q, by rw [mulDet_apply]⟩
  · exact Submodule.zero_mem _

/-! ### The homogeneous projection on `A/det` -/

/-- **The degree-`d` homogeneous projection on `A/det`.** Since `homogeneousComponent
d` maps `(det)` into itself (`homogeneousComponent_mem_detSubmodule`), it descends
through the quotient to a `k`-linear map `A/det → A/det` whose image is the
degree-`d` component `(A/det)_d`. -/
noncomputable def quotDetProj (k : Type*) [Field k] (N d : ℕ) :
    (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :=
  Submodule.mapQ (detSubmodule k N) (detSubmodule k N) (MvPolynomial.homogeneousComponent d)
    (fun _ hx => Submodule.mem_comap.2 (homogeneousComponent_mem_detSubmodule d hx))

@[simp] theorem quotDetProj_mk (d : ℕ) (f : MvPolynomial (Fin N × Fin N) k) :
    quotDetProj k N d (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (MvPolynomial.homogeneousComponent d f) :=
  rfl

/-- **`quotDetProj d` lands in the degree-`d` component `(A/det)_d`.** -/
theorem quotDetProj_mem_degreeSubrep (d : ℕ)
    (x : MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :
    quotDetProj k N d x ∈ (quotDetDegreeSubrep k N d).toSubmodule := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [quotDetProj_mk]
  exact ⟨MvPolynomial.homogeneousComponent d f, MvPolynomial.homogeneousComponent_mem d f, rfl⟩

/-- **`quotDetProj d` is right-`GL_N`-equivariant.** Immediate from
`homogeneousComponent_polyRightRep` descended through the quotient. -/
theorem quotDetProj_equivariant (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :
    quotDetProj k N d (quotDetRep k N g x) = quotDetRep k N g (quotDetProj k N d x) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [quotDetRep_mk, quotDetProj_mk, quotDetProj_mk, quotDetRep_mk,
    homogeneousComponent_polyRightRep]

/-- **`quotDetProj d` is the identity on the degree-`d` component `(A/det)_d`.** -/
theorem quotDetProj_id_on_degree (d : ℕ)
    {x : MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N}
    (hx : x ∈ (quotDetDegreeSubrep k N d).toSubmodule) : quotDetProj k N d x = x := by
  obtain ⟨f, hf, rfl⟩ := hx
  rw [Submodule.mkQ_apply, quotDetProj_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_pos rfl]

/-- **`quotDetProj d` vanishes on the degree-`e` component for `e ≠ d`.** -/
theorem quotDetProj_zero_on_degree (d e : ℕ) (hde : d ≠ e)
    {x : MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N}
    (hx : x ∈ (quotDetDegreeSubrep k N e).toSubmodule) : quotDetProj k N d x = 0 := by
  obtain ⟨f, hf, rfl⟩ := hx
  rw [Submodule.mkQ_apply, quotDetProj_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_neg hde, Submodule.Quotient.mk_zero]

/-! ### The grading of `A/det` -/

/-- **The degree components `(A/det)_d` span `A/det`.** The quotient projection is
surjective and the homogeneous submodules span `A`. -/
theorem quotDetDegreeSubrep_iSup_eq_top :
    ⨆ d, (quotDetDegreeSubrep k N d).toSubmodule = ⊤ := by
  have hA : ⨆ d, MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Submodule.sum_mem _ fun d _ =>
      Submodule.mem_iSup_of_mem d (MvPolynomial.homogeneousComponent_mem d f)
  have hfun : (fun d => (quotDetDegreeSubrep k N d).toSubmodule)
      = (fun d => (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
          (Submodule.mkQ (detSubmodule k N))) := rfl
  rw [hfun, ← Submodule.map_iSup, hA, Submodule.map_top, Submodule.range_mkQ]

/-- **The degree components `(A/det)_d` are independent.** This is the graded-ideal
property: applying the projection `quotDetProj d` to a relation `∑ x_e = 0`
(`x_e ∈ (A/det)_e`) kills every term but `x_d`, forcing `x_d = 0`. -/
theorem quotDetDegreeSubrep_iSupIndep :
    iSupIndep (fun d => (quotDetDegreeSubrep k N d).toSubmodule) := by
  rw [iSupIndep_def]
  intro d
  rw [Submodule.disjoint_def]
  intro x hxd hxsup
  have h1 : quotDetProj k N d x = x := quotDetProj_id_on_degree d hxd
  have h2 : quotDetProj k N d x = 0 := by
    have hle : (⨆ (e) (_ : e ≠ d), (quotDetDegreeSubrep k N e).toSubmodule)
        ≤ LinearMap.ker (quotDetProj k N d) := by
      refine iSup_le fun e => iSup_le fun hed => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      exact quotDetProj_zero_on_degree d e (Ne.symm hed) hy
    exact (LinearMap.mem_ker).1 (hle hxsup)
  rw [← h1, h2]

/-! ### Single-degree reduction for a simple finite-dimensional subrep -/

/-- **Single-degree reduction (issue #4905 part-A).** A finite-dimensional *simple*
`GL_N`-representation `L` with a `GL_N`-equivariant injection `φ : L → A/det` admits,
for some degree `d`, a `GL_N`-equivariant injection into the degree-`d` component
`quotDetDegreeFDRep k N d`.

The maps `quotDetProj d ∘ φ : L → (A/det)_d` are `GL_N`-equivariant out of the simple
`L`, hence (Schur) each is zero or injective. Since `φ v = ∑_d quotDetProj d (φ v)`
is a finite sum and `φ v ≠ 0` for some `v`, at least one component is injective. -/
theorem exists_degree_embedding_of_simple
    (k : Type*) [Field k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N))
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = quotDetRep k N g (φ v)) :
    ∃ (d : ℕ) (ψ : L →ₗ[k] quotDetDegreeFDRep k N d),
      Function.Injective ψ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        ψ (L.ρ g v) = (quotDetDegreeFDRep k N d).ρ g (ψ v)) := by
  classical
  haveI := hLsimp
  -- For each degree `d`, the equivariant map `ψ d : L → (A/det)_d`.
  let ψ : ∀ d, L →ₗ[k] quotDetDegreeFDRep k N d := fun d =>
    LinearMap.codRestrict (quotDetDegreeSubrep k N d).toSubmodule
      (quotDetProj k N d ∘ₗ φ) (fun v => quotDetProj_mem_degreeSubrep d (φ v))
  -- carrier value of `ψ d`
  have hψ_val : ∀ d (v : L),
      (quotDetDegreeSubrep k N d).toSubmodule.subtype (ψ d v) = quotDetProj k N d (φ v) :=
    fun _ _ => rfl
  -- equivariance of `ψ d`
  have hψ_equiv : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      ψ d (L.ρ g v) = (quotDetDegreeFDRep k N d).ρ g (ψ d v) := by
    intro d g v
    apply Subtype.val_injective
    change quotDetProj k N d (φ (L.ρ g v)) = quotDetRep k N g (quotDetProj k N d (φ v))
    rw [hφ_equiv, quotDetProj_equivariant]
  -- Schur: each `ψ d` is zero or injective
  have hschur : ∀ d, Function.Injective (ψ d) ∨ ψ d = 0 := by
    intro d
    let Ψ : Representation.asModule L.ρ →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (quotDetDegreeFDRep k N d).ρ :=
      Representation.asModuleHomOfIntertwiner (ψ d) (hψ_equiv d)
    rcases eq_bot_or_eq_top (LinearMap.ker Ψ) with hker | hker
    · exact Or.inl fun a b h => LinearMap.ker_eq_bot.1 hker h
    · refine Or.inr ?_
      have hΨ0 : Ψ = 0 := LinearMap.ker_eq_top.1 hker
      ext v
      change Ψ v = 0
      rw [hΨ0, LinearMap.zero_apply]
  -- some `ψ d` is injective
  haveI : Nontrivial L :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (M := Representation.asModule L.ρ)
  obtain ⟨v, hv0⟩ := exists_ne (0 : L)
  have hexists : ∃ d, Function.Injective (ψ d) := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ d, ψ d = 0 := fun d => (hschur d).resolve_left (hcon d)
    obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective (detSubmodule k N) (φ v)
    -- `φ v = ∑_d quotDetProj d (φ v)`
    have hdecomp : (∑ d ∈ Finset.range (p.totalDegree + 1), quotDetProj k N d (φ v)) = φ v := by
      have hstep : ∀ d, quotDetProj k N d (φ v)
          = (detSubmodule k N).mkQ (MvPolynomial.homogeneousComponent d p) := by
        intro d
        rw [← hp, Submodule.mkQ_apply, quotDetProj_mk]
      simp_rw [hstep]
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent, Submodule.mkQ_apply, hp]
    -- but every term vanishes
    have hzeroterm : ∀ d, quotDetProj k N d (φ v) = 0 := by
      intro d
      rw [← hψ_val d v, hzero d, LinearMap.zero_apply, map_zero]
    have hφv0 : φ v = 0 := by
      rw [← hdecomp]; exact Finset.sum_eq_zero fun d _ => hzeroterm d
    exact hv0 (hφ_inj (by rw [hφv0, map_zero]))
  obtain ⟨d, hd⟩ := hexists
  exact ⟨d, ψ d, hd, hψ_equiv d⟩

end Etingof.CauchyDetQuotient
