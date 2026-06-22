import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaK
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.Definition5_23_1

/-!
# det⁻¹ elimination proper (assembly of the kernel lemma) — issue #4695

This file closes the lone `sorry` of `detInv_elim_of_polynomial`
(`PolynomialRepEmbedding.lean`) by assembling the **kernel lemma (K)**
(`Etingof.KernelLemmaK.kernelLemmaK_evalAtGL`, issue #4694).

## The assembly

For an algebraic `GL_N`-representation `M` whose `ℕ`-indexed weight spaces span
(`h_span`, i.e. `M` is genuinely *polynomial*) we:

1. build a **weight eigenbasis** `v` of `M` from `h_span` via the internal
   direct-sum decomposition into weight spaces (`exists_weight_eigenbasis`);
2. express the matrix coefficients `v.repr (M.ρ g (v c)) a` in that basis as
   `evalAtGL`-values of polynomials `R a c ∈ k[Xᵢⱼ, D]` (change of basis from the
   algebraic data `halg`);
3. observe that `coordToAway (R a c) ∈ O = A[det⁻¹]` is a **right-torus weight
   vector** of weight `wt c ∈ ℕ^N` (`hRweight`) — using the right-translation
   intertwining `evalGLAway (localRightRep h x) g = evalGLAway x (g·h)`
   (`evalGLAway_localRightRep`) and that `v` is a weight basis — and that their
   span is right-`GL_N`-stable (`hstable`);
4. feed `(R, wt)` to `kernelLemmaK_evalAtGL`, which eliminates the `D = det⁻¹`
   variable: each `evalAtGL g (R a c)` equals `eval g (Q a c)` for a bare-entry
   polynomial `Q a c ∈ k[Xᵢⱼ]`.

The output basis `b := v` and polynomials `Q` are exactly the data
`detInv_elim_of_polynomial` produces.
-/

namespace Etingof.DetInvElim

open MvPolynomial Etingof Etingof.DetLocalization Etingof.PolynomialGLAction
  Etingof.LocalizationGLAction Etingof.KernelLemmaKPrime Etingof.KernelLemmaK

variable {k : Type*} [Field k] {N : ℕ}

/-! ### Right-translation intertwining -/

/-- Evaluating `rTransAlgHom M p` at `g` coincides with evaluating `p` at the
product matrix `g · M`: the substitution `X_{ij} ↦ ∑_l M_{lj} X_{il}` followed by
`X ↦ g` gives `(g·M)_{ij}`. -/
lemma eval_rTransAlgHom (M g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2) (rTransAlgHom M p)
      = MvPolynomial.eval (fun ij : Fin N × Fin N => (g * M) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => g ij.1 ij.2)).comp
          (rTransAlgHom M) =
        (MvPolynomial.aeval (fun ij : Fin N × Fin N => (g * M) ij.1 ij.2) :
          MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, rTransAlgHom_X, map_sum, MvPolynomial.aeval_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, MvPolynomial.aeval_X, smul_eq_mul, mul_comm]

/-- **Right-translation intertwining for `evalGLAway`.** Right translation of the
localization element `x ∈ O = A[det⁻¹]` by `h ∈ GL_N`, evaluated at `g`, is `x`
evaluated at `g · h`: `evalGLAway (localRightRep h x) g = evalGLAway x (g · h)`. -/
lemma evalGLAway_localRightRep (h g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (detPoly k N)) :
    evalGLAway (localRightRep k N h x) g = evalGLAway x (g * h) := by
  -- both sides are ring homs `O →+* k` in `x`; check on `algebraMap A O`.
  have key : ∀ a : MvPolynomial (Fin N × Fin N) k,
      evalGLAway (localRightRep k N h
          (algebraMap (MvPolynomial (Fin N × Fin N) k) _ a)) g
        = evalGLAway (algebraMap _ _ a) (g * h) := by
    intro a
    rw [localRightRep_algebraMap, evalGLAway_algebraMap, evalGLAway_algebraMap,
      evalGLHom_apply, evalGLHom_apply]
    show MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (rTransAlgHom (h : Matrix (Fin N) (Fin N) k) a) = _
    rw [eval_rTransAlgHom]
    rfl
  -- package as ring homs and use the localization extension principle.
  let F : Localization.Away (detPoly k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
      (evalGLAway.comp (localRightAlgHom h).toRingHom)
  let G : Localization.Away (detPoly k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) (g * h)).comp evalGLAway
  have hFG : F = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (detPoly k N))
    apply RingHom.ext
    intro a
    simp only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [← localRightRep_apply]
    exact key a
  have hx := RingHom.congr_fun hFG x
  simpa only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, ← localRightRep_apply] using hx

/-- **`evalGLAway` is `k`-linear in the scalar.** For `c : k`,
`evalGLAway (c • x) = c • evalGLAway x` (pointwise on `GL_N`). -/
lemma evalGLAway_smul (c : k) (x : Localization.Away (detPoly k N)) :
    evalGLAway (c • x) = c • evalGLAway x := by
  rw [Algebra.smul_def, map_mul]
  have hc : evalGLAway (algebraMap k (Localization.Away (detPoly k N)) c)
      = Function.const _ c := by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (detPoly k N)), evalGLAway_algebraMap]
    funext g
    rw [evalGLHom_apply, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]
    rfl
  rw [hc]
  funext g
  simp [Function.const_apply, smul_eq_mul]

/-! ### Weight eigenbasis from `h_span` -/

/-- **Weight eigenbasis.** A polynomial `GL_N`-representation `M` (whose `ℕ`-indexed
weight spaces span, `h_span`) has a basis `v` of torus eigenvectors with weights
`wt c ∈ ℕ^N`: `M.ρ (diagUnit i t) (v c) = t ^ (wt c i) • v c`. Built from the
internal direct-sum decomposition into weight spaces
(`glWeightSpace_iSupIndep` + `h_span`) via `IsInternal.collectedBasis`. -/
theorem exists_weight_eigenbasis [IsAlgClosed k] [CharZero k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (v : Module.Basis (Fin d) k M) (wt : Fin d → (Fin N → ℕ)),
      ∀ (c : Fin d) (i : Fin N) (t : kˣ),
        M.ρ (diagUnit k N i t) (v c) = ((t : k) ^ wt c i) • v c := by
  classical
  set p : (Fin N →₀ ℕ) → Submodule k M :=
    fun μ => glWeightSpace k N M (fun i => μ i) with hp_def
  have h_indep : iSupIndep p := glWeightSpace_iSupIndep k N M
  have hs_fin : {μ | p μ ≠ ⊥}.Finite := glWeightSpace_finite_support k N M
  haveI : Fintype {μ // p μ ≠ ⊥} := hs_fin.fintype
  have h_internal : DirectSum.IsInternal (fun μ : {μ // p μ ≠ ⊥} => p μ.val) := by
    rw [DirectSum.isInternal_ne_bot_iff]
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨h_indep, h_span⟩
  let bb := h_internal.collectedBasis (fun μ => Module.finBasis k (p μ.val))
  let e := Fintype.equivFin (Σ μ : {μ // p μ ≠ ⊥}, Fin (Module.finrank k (p μ.val)))
  refine ⟨Fintype.card (Σ μ : {μ // p μ ≠ ⊥}, Fin (Module.finrank k (p μ.val))),
    bb.reindex e, fun c i => (e.symm c).1.val i, ?_⟩
  intro c i t
  have hmem : (bb.reindex e) c ∈ glWeightSpace k N M (fun j => (e.symm c).1.val j) := by
    rw [Module.Basis.reindex_apply]
    have hcb := h_internal.collectedBasis_mem (fun μ => Module.finBasis k (p μ.val)) (e.symm c)
    simpa only [hp_def] using hcb
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero] at hmem
  exact hmem i t

/-! ### The assembly -/

/-- **det⁻¹ elimination proper (issue #4695).** An algebraic `GL_N`-representation
`M` whose `ℕ`-indexed weight spaces span (`h_span`, i.e. `M` is genuinely
*polynomial*) has its matrix coefficients given, in a weight eigenbasis, by
**bare-entry** polynomials `Q ∈ k[Xᵢⱼ]`: the `det⁻¹` variable is eliminated.

Assembled from the kernel lemma `kernelLemmaK_evalAtGL` (#4694): the
matrix-coefficient polynomials `R a c`, regarded in the localization `A[det⁻¹]`,
are right-torus weight vectors (weight `wt c ∈ ℕ^N`) spanning a right-`GL_N`-stable
subspace, so the kernel lemma lands each `evalAtGL g (R a c)` in `k[Xᵢⱼ]`. -/
theorem detInv_elim [CharZero k] [IsAlgClosed k] (n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c) := by
  classical
  -- Weight eigenbasis `v` and the algebraic data `(b₀, P₀)` in some basis.
  obtain ⟨d, v, wt, hv⟩ := exists_weight_eigenbasis M h_span
  obtain ⟨m, b₀, P₀, hP₀⟩ := halg
  -- Matrix-coefficient polynomials in the weight basis `v` (change of basis from `b₀`).
  set R : Fin d → Fin d → MvPolynomial (Etingof.GLCoordVars N) k :=
    fun a c => ∑ a₀ : Fin m, ∑ c₀ : Fin m,
      (v.repr (b₀ a₀) a * b₀.repr (v c) c₀) • P₀ a₀ c₀ with hR
  -- `evalAtGL g (R a c)` is the `(a,c)` matrix coefficient of `M.ρ g` in basis `v`.
  have hReval : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      Etingof.evalAtGL g (R a c) = v.repr (M.ρ g (v c)) a := by
    intro g a c
    have hP₀' : ∀ a₀ c₀, Etingof.evalAtGL g (P₀ a₀ c₀) = b₀.repr (M.ρ g (b₀ c₀)) a₀ :=
      fun a₀ c₀ => (hP₀ g a₀ c₀).symm
    have hlin : Etingof.evalAtGL g (R a c)
        = ∑ a₀ : Fin m, ∑ c₀ : Fin m,
            (v.repr (b₀ a₀) a * b₀.repr (v c) c₀) * Etingof.evalAtGL g (P₀ a₀ c₀) := by
      rw [hR]
      simp only [Etingof.evalAtGL, map_sum, MvPolynomial.smul_eval]
    rw [hlin]
    simp_rw [hP₀']
    -- Reassemble the change-of-basis double sum into `v.repr (M.ρ g (v c)) a`.
    have expand_col : M.ρ g (v c) = ∑ c₀ : Fin m, b₀.repr (v c) c₀ • M.ρ g (b₀ c₀) := by
      conv_lhs => rw [show v c = ∑ c₀, b₀.repr (v c) c₀ • b₀ c₀ from (b₀.sum_repr (v c)).symm]
      rw [map_sum]; simp_rw [map_smul]
    rw [expand_col, map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c₀ _ => ?_
    -- inner: ∑ a₀, (v.repr (b₀ a₀) a * s_c₀) * b₀.repr (M.ρ g (b₀ c₀)) a₀
    --        = s_c₀ * v.repr (M.ρ g (b₀ c₀)) a
    have hrow : v.repr (M.ρ g (b₀ c₀)) a
        = ∑ a₀ : Fin m, b₀.repr (M.ρ g (b₀ c₀)) a₀ * v.repr (b₀ a₀) a := by
      conv_lhs => rw [show M.ρ g (b₀ c₀)
        = ∑ a₀, b₀.repr (M.ρ g (b₀ c₀)) a₀ • b₀ a₀ from (b₀.sum_repr _).symm]
      rw [map_sum]
      simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₀ _ => ?_
    ring
  -- The matrix-coefficient function attached to `coordToAway (R a c)`.
  have hcoeff : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      evalGLAway (coordToAway (R a c)) g = v.repr (M.ρ g (v c)) a :=
    fun g a c => by rw [← evalAtGL_eq_evalGLAway_coordToAway, hReval]
  -- The localization elements `coordToAway (R a c)` are right-torus weight vectors.
  have hRweight : ∀ a c, coordToAway (R a c)
      ∈ glWeightSpaceℤ k N (localRightRep k N) (fun j => (wt c j : ℤ)) := by
    intro a c
    rw [mem_glWeightSpaceℤ_iff]
    intro i s
    apply evalGLAway_injective
    funext g
    have hscal : ((s ^ (wt c i : ℤ) : kˣ) : k) = (s : k) ^ wt c i := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hscal, evalGLAway_localRightRep, hcoeff (g * diagUnit k N i s) a c,
      map_mul, Module.End.mul_apply, hv c i s, map_smul, map_smul, Finsupp.smul_apply,
      smul_eq_mul, evalGLAway_smul, Pi.smul_apply, hcoeff g a c, smul_eq_mul]
  -- Their span is right-`GL_N`-stable.
  have hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Submodule.span k (Set.range fun j : Fin d × Fin d => coordToAway (R j.1 j.2)),
        localRightRep k N g x
          ∈ Submodule.span k (Set.range fun j : Fin d × Fin d => coordToAway (R j.1 j.2)) := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨⟨a, c⟩, rfl⟩ := hy
        -- `localRightRep g (coordToAway (R a c)) = ∑ c', (v.repr (M.ρ g (v c)) c') • coordToAway (R a c')`.
        have hexp : localRightRep k N g (coordToAway (R a c))
            = ∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') • coordToAway (R a c') := by
          apply evalGLAway_injective
          funext hh
          have hLHS : evalGLAway (localRightRep k N g (coordToAway (R a c))) hh
              = ∑ c' : Fin d, v.repr (M.ρ g (v c)) c' * v.repr (M.ρ hh (v c')) a := by
            rw [evalGLAway_localRightRep, hcoeff (hh * g) a c, map_mul, Module.End.mul_apply]
            conv_lhs => rw [show M.ρ g (v c)
              = ∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') • v c' from (v.sum_repr _).symm]
            rw [map_sum, map_sum]
            simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
              Pi.smul_apply, smul_eq_mul]
          have hRHS : evalGLAway (∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') • coordToAway (R a c')) hh
              = ∑ c' : Fin d, v.repr (M.ρ g (v c)) c' * v.repr (M.ρ hh (v c')) a := by
            rw [map_sum, Finset.sum_apply]
            refine Finset.sum_congr rfl fun c' _ => ?_
            rw [evalGLAway_smul, Pi.smul_apply, hcoeff hh a c', smul_eq_mul]
          rw [hLHS, hRHS]
        rw [hexp]
        exact Submodule.sum_mem _ fun c' _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, c'), rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
    | smul c a _ iha => rw [map_smul]; exact Submodule.smul_mem _ _ iha
  -- Apply the kernel lemma to eliminate `det⁻¹` from each matrix coefficient.
  have hQex : ∀ j : Fin d × Fin d, ∃ Q : MvPolynomial (Fin N × Fin N) k,
      ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
        Etingof.evalAtGL g (R j.1 j.2)
          = MvPolynomial.eval
              (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q :=
    fun j => kernelLemmaK_evalAtGL (fun j : Fin d × Fin d => R j.1 j.2)
      (fun j => wt j.2) (fun j => hRweight j.1 j.2) hstable j
  choose Qf hQf using hQex
  refine ⟨d, v, fun a c => Qf (a, c), ?_⟩
  intro g a c
  rw [← hReval g a c]
  exact hQf (a, c) g

end Etingof.DetInvElim
