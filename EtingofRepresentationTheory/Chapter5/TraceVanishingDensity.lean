import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.DetLocalization
import EtingofRepresentationTheory.Chapter5.DistinctEigenvalueDensity
import EtingofRepresentationTheory.Chapter5.DiagonalizableConj
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace

/-!
# Torus-trace vanishing forces full-group trace vanishing (geometric density core)

This file proves the genuinely geometric step of the character-independence seam
(#4925, sub-issue #4932): a `ℂ`-combination of the characters of finitely many
**algebraic** `GL_N(ℂ)`-representations `L i` that vanishes at every diagonal
torus element `diag(t)` vanishes at *every* group element `g`.

The character `g ↦ trace_ℂ ((L i).ρ g)` of an algebraic representation is a
*regular* (polynomial-in-the-entries-with-`det⁻¹`) function of `g`
(`trace_eq_evalAtGL_of_algebraic`), and it is conjugation-invariant (the trace
is a class function). Every matrix with `N` distinct eigenvalues is conjugate to
a diagonal torus element (`gl_conj_diagTorus_of_distinct_eigenvalues`, #4930), so
the combination already vanishes on all distinct-eigenvalue matrices, and these
are Zariski-dense — their complement is the zero locus of `det · discr`
(`discrPoly`, #4931). Clearing the `det⁻¹` denominator yields a genuine
polynomial vanishing off `{det · discr ≠ 0}`, which `MvPolynomial`'s density
engine (`eq_zero_of_eval_eq_zero_off_zeroLocus`) forces to be identically zero.

The hypothesis is `IsAlgebraicRepresentation` (regularity of the character), not
merely `hLtop` (spanning `ℕ`-weight spaces): the latter is strictly weaker for
abstract-group representations and does not by itself make the character regular.
At the genuine call site each `L i` is a summand of the polynomial representation
`V^{⊗n}`, hence algebraic.
-/

open Matrix MvPolynomial
open Etingof.DetLocalization

namespace Etingof

variable {N : ℕ}

/-- **The character of an algebraic representation is a regular function.** For an
algebraic `GL_N`-representation `M`, the character `g ↦ trace_ℂ (M.ρ g)` equals
`evalAtGL g T` for the polynomial `T = ∑ₐ P a a` (the trace of the
matrix-coefficient polynomials in any algebraic-rep basis). -/
theorem trace_eq_evalAtGL_of_algebraic
    (M : FDRep ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
    (hM : Etingof.IsAlgebraicRepresentation N M.ρ) :
    ∃ T : MvPolynomial (Etingof.GLCoordVars N) ℂ,
      ∀ g, LinearMap.trace ℂ M (M.ρ g) = Etingof.evalAtGL g T := by
  obtain ⟨m, b, P, hP⟩ := hM
  refine ⟨∑ a, P a a, fun g => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b (M.ρ g)]
  have hsum : Etingof.evalAtGL g (∑ a, P a a) = ∑ a, Etingof.evalAtGL g (P a a) := by
    simp only [Etingof.evalAtGL, map_sum]
  rw [hsum, Matrix.trace]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hP g a a]

/-- **Geometric density core (algebraic version).** A `ℂ`-combination of the
characters of finitely many *algebraic* `GL_N(ℂ)`-representations `L i` that
vanishes at every diagonal torus element vanishes at every group element. -/
theorem trace_combination_vanishes_of_torus_vanishes_of_algebraic
    (N : ℕ) {ι : Type} [Fintype ι]
    (L : ι → FDRep ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
    (hLalg : ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ)
    (c : ι → ℂ)
    (htorus : ∀ t : Fin N → ℂˣ,
        ∑ i, c i • LinearMap.trace ℂ (L i) ((L i).ρ (diagTorus ℂ N t)) = 0)
    (g : Matrix.GeneralLinearGroup (Fin N) ℂ) :
    ∑ i, c i • LinearMap.trace ℂ (L i) ((L i).ρ g) = 0 := by
  classical
  -- Abbreviation for the character combination `χ`.
  set χ : Matrix.GeneralLinearGroup (Fin N) ℂ → ℂ :=
    fun g => ∑ i, c i • LinearMap.trace ℂ (L i) ((L i).ρ g) with hχdef
  -- `N = 0`: `GL_0` is trivial, so `g` is a diagonal torus element and `htorus` applies.
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hg : g = diagTorus ℂ 0 (fun _ => 1) := by
      apply Units.ext; ext i; exact i.elim0
    rw [hg]; exact htorus (fun _ => 1)
  -- Conjugation invariance of each character: trace is a class function.
  have hconj : ∀ (i : ι) (h gg : Matrix.GeneralLinearGroup (Fin N) ℂ),
      LinearMap.trace ℂ (L i) ((L i).ρ (h * gg * h⁻¹))
        = LinearMap.trace ℂ (L i) ((L i).ρ gg) := by
    intro i h gg
    have hρ : (L i).ρ (h * gg * h⁻¹) = (L i).ρ h * (L i).ρ gg * (L i).ρ h⁻¹ := by
      rw [map_mul, map_mul]
    have hinv : (L i).ρ h⁻¹ * (L i).ρ h = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [hρ, LinearMap.trace_mul_comm, ← mul_assoc, hinv, one_mul]
  -- `χ` vanishes at every matrix conjugate to a torus element.
  have hχconj : ∀ (h gg : Matrix.GeneralLinearGroup (Fin N) ℂ),
      χ (h * gg * h⁻¹) = χ gg := by
    intro h gg
    simp only [hχdef]
    exact Finset.sum_congr rfl (fun i _ => by rw [hconj i h gg])
  -- The character combination is regular: `χ g = evalAtGL g T` for a polynomial `T`.
  choose T hT using fun i => trace_eq_evalAtGL_of_algebraic (L i) (hLalg i)
  set Tsum : MvPolynomial (Etingof.GLCoordVars N) ℂ := ∑ i, c i • T i with hTsum
  have hχeval : ∀ gg, χ gg = Etingof.evalAtGL gg Tsum := by
    intro gg
    simp only [hχdef, hTsum, Etingof.evalAtGL, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, smul_eq_mul,
      ← Etingof.evalAtGL, ← hT i gg]
  -- Realise `χ` through the localization `A[det⁻¹]`.
  set F : Localization.Away (detPoly ℂ N) := coordToAway Tsum with hF
  have hχF : ∀ gg, χ gg = evalGLAway F gg := by
    intro gg
    rw [hχeval gg, hF, evalAtGL_eq_evalGLAway_coordToAway]
  -- Det-power normal form `F = Q · det⁻ʳ`, then clear the denominator.
  obtain ⟨r, Q, hQ⟩ := exists_invSelf_normalForm F
  have hnum : (algebraMap _ (Localization.Away (detPoly ℂ N)) Q)
      = F * (algebraMap _ (Localization.Away (detPoly ℂ N)) (detPoly ℂ N)) ^ r :=
    algebraMap_num_eq hQ
  -- The cleared-denominator identity: `eval(entries g) Q = χ g · (det g)^r`.
  have hstar : ∀ gg : Matrix.GeneralLinearGroup (Fin N) ℂ,
      MvPolynomial.eval (fun ij : Fin N × Fin N => (gg : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2) Q
        = χ gg * (gg : Matrix (Fin N) (Fin N) ℂ).det ^ r := by
    intro gg
    have hfun := congrArg evalGLAway hnum
    rw [map_mul, map_pow] at hfun
    have hpt := congrFun hfun gg
    simp only [Pi.mul_apply, Pi.pow_apply, evalGLAway_algebraMap, evalGLHom_apply] at hpt
    rw [hpt, hχF gg, ← evalGLHom_apply, evalGLHom_detPoly_apply]
  -- Evaluating `detPoly` at the entries of a matrix returns its determinant.
  have eval_detPoly : ∀ x : Fin N × Fin N → ℂ,
      MvPolynomial.eval x (detPoly ℂ N) = (Matrix.of fun i j => x (i, j)).det := by
    intro x
    rw [detPoly, (MvPolynomial.eval x).map_det]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  -- The numerator polynomial vanishes everywhere (Zariski density).
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero_off_zeroLocus
      (Q := detPoly ℂ N * Matrix.discrPoly N) (mul_ne_zero detPoly_ne_zero
        (Matrix.discrPoly_ne_zero N hN)) ?_
    intro x hx
    rw [map_mul, mul_ne_zero_iff] at hx
    obtain ⟨hdet, hdiscr⟩ := hx
    -- `x` is the entry-list of an invertible matrix `g ∈ GL_N`.
    rw [eval_detPoly] at hdet
    set Mx : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => x (i, j) with hMx
    set g : Matrix.GeneralLinearGroup (Fin N) ℂ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Mx hdet with hg
    have hgcoe : (g : Matrix (Fin N) (Fin N) ℂ) = Mx := by
      rw [hg]; rfl
    have hentries : (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2) = x := by
      funext ij; rw [hgcoe, hMx]; simp
    -- `g` has `N` distinct eigenvalues, hence is conjugate to a torus element.
    rw [Matrix.eval_discrPoly] at hdiscr
    have hcard : (g : Matrix (Fin N) (Fin N) ℂ).charpoly.roots.toFinset.card = N := by
      rw [hgcoe]
      exact Matrix.card_roots_charpoly_of_discr_ne_zero Mx hN hdiscr
    obtain ⟨t, h, hgconj⟩ := gl_conj_diagTorus_of_distinct_eigenvalues N g hcard
    have hχg : χ g = 0 := by
      rw [hgconj, hχconj h (diagTorus ℂ N t)]
      simp only [hχdef]; exact htorus t
    -- Therefore `eval x Q = χ g · (det g)^r = 0`.
    rw [← hentries, hstar g, hχg, zero_mul]
  -- Conclude: for the given `g`, `χ g · (det g)^r = 0` with `det g ≠ 0`.
  have hgdet : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hfinal := hstar g
  rw [hQ0, map_zero] at hfinal
  have hzero : χ g * (g : Matrix (Fin N) (Fin N) ℂ).det ^ r = 0 := hfinal.symm
  have hχg0 : χ g = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero r hgdet)
  simpa only [hχdef] using hχg0

end Etingof
