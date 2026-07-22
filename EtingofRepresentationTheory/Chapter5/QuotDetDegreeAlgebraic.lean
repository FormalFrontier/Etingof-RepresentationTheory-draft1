import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotientDegree
import EtingofRepresentationTheory.Chapter5.CauchyWeightSpaceDimension

/-!
# Algebraicity of the determinant-quotient degree component `quotDetDegreeFDRep`

The final assembly of #4905
(`quotDetRep_irreducible_constituent_lastWeight_zero`) feeds the degree-`d`
component `(A/det)_d = quotDetDegreeFDRep k N d` into the part-C ingredient
`Etingof.simple_constituent_formalCharacter_eq_schurPoly_mem`, which requires the
hypothesis `Etingof.IsAlgebraicRepresentation N M.ρ`. This file supplies that
hypothesis for `quotDetDegreeFDRep`.

The route has three steps:

* `IsAlgebraicRepresentation.of_surjective_equivariant` — a general transport
  lemma: algebraicity passes along a **surjective** `GL_N`-equivariant `k`-linear
  map onto a finite-dimensional target. (The dual of
  `IsAlgebraicRepresentation.restrict`, which handles invariant *sub*modules.)
* `polyRightDegreeFDRep_isAlgebraic` — the degree-`d` component `A_d` of the
  coordinate ring under right translation is algebraic. On the monomial basis the
  right translation `R_g X_{ij} = ∑_l g_{lj} X_{il}` has matrix coefficients that
  are polynomials in the entries of `g`.
* `quotDetDegreeFDRep_isAlgebraic` — combine the two via the surjective
  equivariant quotient map `A_d → (A/det)_d`.
-/

open scoped TensorProduct
open MvPolynomial Matrix

noncomputable section

namespace Etingof

/-! ### Algebraicity transfers along a surjective equivariant map -/

/-- **Algebraicity transfers along a surjective intertwining `k`-linear map.** If
`ρ` is an algebraic `GL_N(k)`-representation on `Y` and `π : Y → Z` is a surjective
`k`-linear map onto a finite-dimensional `Z` intertwining `ρ` with `σ`
(`π (ρ g y) = σ g (π y)`), then `σ` is algebraic.

Choosing a `k`-linear section `s : Z → Y` of `π`, a basis `b'` of `Z`, and the
algebraicity basis `B` of `Y`, the new matrix coefficient `b'.repr (σ g (b' c)) a`
expands as a `k`-linear combination of `evalAtGL g (P e d)` with constant
coefficients from `B.repr (s (b' c))` and `b'.repr (π (B e))`. This mirrors
`IsAlgebraicRepresentation.restrict`, with the invariant-submodule inclusion
replaced by the section `s` and the projection replaced by `π`. -/
theorem IsAlgebraicRepresentation.of_surjective_equivariant {k : Type*} [Field k] {N : ℕ}
    {Y Z : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Z] [Module k Z] [Module.Finite k Z]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {σ : Matrix.GeneralLinearGroup (Fin N) k → Z →ₗ[k] Z}
    (π : Y →ₗ[k] Z) (hπ_surj : Function.Surjective π)
    (hcomm : ∀ g y, π (ρ g y) = σ g (π y))
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    Etingof.IsAlgebraicRepresentation N σ := by
  classical
  obtain ⟨M, B, P, hP⟩ := h
  -- Basis of the target, indexed by `Fin (finrank k Z)`.
  let b' : Module.Basis (Fin (Module.finrank k Z)) k Z := Module.finBasis k Z
  -- A `k`-linear section `s : Z → Y` of `π`.
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ_surj)
  have hsec : ∀ z, π (s z) = z := fun z => by
    have := LinearMap.congr_fun hs z; simpa using this
  refine ⟨Module.finrank k Z, b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (s (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (π (B e)) a), fun g a c => ?_⟩
  -- `φ y = b'.repr (π y) a`, a linear functional `Y → k`.
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp π)
  have hφ_apply : ∀ y, φ y = b'.repr (π y) a := fun _ => rfl
  -- `σ g (b' c) = π (ρ g (s (b' c)))`, from equivariance and the section property.
  have hkey : π (ρ g (s (b' c))) = σ g (b' c) := by rw [hcomm, hsec]
  -- Reduce the LHS coefficient to a double sum over the algebraicity basis `B`.
  have hlhs : b'.repr (σ g (b' c)) a
      = ∑ d, ∑ e, B.repr (s (b' c)) d
          * (Etingof.evalAtGL g (P e d) * b'.repr (π (B e)) a) := by
    rw [show b'.repr (σ g (b' c)) a = φ (ρ g (s (b' c))) from by rw [hφ_apply, hkey]]
    -- expand `s (b' c)` in the algebraicity basis `B`
    rw [show ρ g (s (b' c))
        = ∑ d, B.repr (s (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show s (b' c) = ∑ d, B.repr (s (b' c)) d • B d from
        (B.sum_repr (s (b' c))).symm]
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

/-! ### The right-translation matrix coefficient as a polynomial in `g` -/

open Etingof.PolynomialGLAction Etingof.CauchyCharacterRight Etingof.CauchyWeightSpaceDimension

/-- The `(t, s)` matrix coefficient of right translation on the monomial basis, as a
polynomial in the coordinate ring `k[Xᵢⱼ, det⁻¹]`. It is obtained by running the
right-translation substitution over the *generic* matrix `(X_{(l,j)})` of coordinate
variables and reading off the `X^t`-coefficient of the image of `X^s`. -/
noncomputable def rightTransPoly (k : Type*) [Field k] (N : ℕ)
    (s t : (Fin N × Fin N) →₀ ℕ) : MvPolynomial (Etingof.GLCoordVars N) k :=
  MvPolynomial.coeff t
    (rTransAlgHom (Matrix.of fun l j : Fin N => MvPolynomial.X (R := k) (Sum.inl (l, j)))
      (MvPolynomial.monomial s (1 : MvPolynomial (Etingof.GLCoordVars N) k)))

/-- **Evaluating `rightTransPoly` at `g` recovers the actual matrix coefficient.** The
generic-matrix substitution is natural in the entries: mapping coefficients through
`evalAtGL g` turns the generic right translation into the genuine one. -/
theorem evalAtGL_rightTransPoly {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (s t : (Fin N × Fin N) →₀ ℕ) :
    Etingof.evalAtGL g (rightTransPoly k N s t)
      = MvPolynomial.coeff t (polyRightRep k N g (MvPolynomial.monomial s (1 : k))) := by
  classical
  set R := MvPolynomial (Etingof.GLCoordVars N) k with hR
  -- the coefficient-evaluation ring hom `R → k` underlying `evalAtGL g`
  set eHom : R →+* k :=
    MvPolynomial.eval (Sum.elim (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
      (fun _ => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) with heHom
  set Ggen : Matrix (Fin N) (Fin N) R :=
    Matrix.of fun l j => MvPolynomial.X (Sum.inl (l, j)) with hGgen
  -- naturality: pushing `eHom` through the generic right translation gives the genuine one
  have hnat : ∀ p : MvPolynomial (Fin N × Fin N) R,
      MvPolynomial.map eHom (rTransAlgHom Ggen p)
        = rTransAlgHom (g : Matrix (Fin N) (Fin N) k) (MvPolynomial.map eHom p) := by
    have hring :
        (MvPolynomial.map eHom).comp (rTransAlgHom Ggen).toRingHom
          = (rTransAlgHom (g : Matrix (Fin N) (Fin N) k)).toRingHom.comp
              (MvPolynomial.map eHom) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rTransAlgHom,
          MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
      · intro ij
        obtain ⟨i, j⟩ := ij
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          rTransAlgHom_X, MvPolynomial.map_X, hGgen, Matrix.of_apply,
          MvPolynomial.smul_eq_C_mul, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 2
        rw [heHom, MvPolynomial.eval_X, Sum.elim_inl]
    have := RingHom.congr_fun hring
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using this
  -- rewrite the genuine action as a coefficient-map of the generic one
  rw [polyRightRep_apply]
  have hmon : (MvPolynomial.monomial s (1 : k))
      = MvPolynomial.map eHom (MvPolynomial.monomial s (1 : R)) := by
    rw [MvPolynomial.map_monomial]
    congr 1
    exact (map_one eHom).symm
  rw [hmon, ← hnat, MvPolynomial.coeff_map]
  rfl

/-- **The degree-`d` component `A_d` of the coordinate ring is algebraic.** Its carrier
is the span of the degree-`d` monomials; right translation acts on this monomial basis
with matrix coefficients `rightTransPoly`, polynomial in the entries of `g`. -/
theorem polyRightDegreeFDRep_isAlgebraic (k : Type*) [Field k] (N d : ℕ) :
    Etingof.IsAlgebraicRepresentation N (polyRightDegreeFDRep k N d).ρ := by
  classical
  set S : Finset ((Fin N × Fin N) →₀ ℕ) := Finset.univ.finsuppAntidiag d with hS
  -- degree-`d` monomials, as elements of the carrier `A_d`
  have hmem : ∀ s : {s // s ∈ S},
      (MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k))
        ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d := by
    intro s
    exact monomial_mem_homog d _ (Finset.mem_finsuppAntidiag.mp (hS ▸ s.2)).1
  let v : {s // s ∈ S} → polyRightDegreeFDRep k N d :=
    fun s => ⟨MvPolynomial.monomial (↑s) 1, by
      rw [Etingof.PolyRightGrading.polyRightHomogeneousSubrep_toSubmodule]; exact hmem s⟩
  have hpolyv : ∀ s, polyOf d (v s) = MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) :=
    fun _ => rfl
  -- linear independence of the monomial family
  have hli : LinearIndependent k v := by
    have hb : LinearIndependent k (fun s : {s // s ∈ S} =>
        MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
      have hcomp := (basisMonomials (Fin N × Fin N) k).linearIndependent.comp
        (fun s : {s // s ∈ S} => (↑s : (Fin N × Fin N) →₀ ℕ)) Subtype.val_injective
      -- v4.31: use `Function.comp_def` (bare `Function.comp` no longer unfolds the composition).
      simpa only [Function.comp_def, coe_basisMonomials] using hcomp
    exact hb.of_comp (polyOf d)
  -- the monomials span the homogeneous component
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro w -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => MvPolynomial.coeff (↑s) (polyOf d w), polyOf_injective d ?_⟩
    have hsupp : ∀ p ∈ (polyOf d w).support, p ∈ S := by
      intro p hp
      rw [hS, Finset.mem_finsuppAntidiag]
      refine ⟨?_, Finset.subset_univ _⟩
      have hH : (polyOf d w).IsHomogeneous d := polyOf_mem d w
      have hd := hH (MvPolynomial.mem_support_iff.mp hp)
      calc ∑ i, p i = p.degree := (Finsupp.degree_eq_sum p).symm
        _ = Finsupp.weight (fun _ => 1) p := by rw [Finsupp.degree_eq_weight_one]
        _ = d := hd
    rw [map_sum]
    simp_rw [map_smul, hpolyv]
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach S
      (fun p => MvPolynomial.coeff p (polyOf d w) • MvPolynomial.monomial p (1 : k))]
    simp_rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
    conv_rhs => rw [(polyOf d w).as_sum]
    refine (Finset.sum_subset hsupp ?_).symm
    intro p _ hp
    rw [MvPolynomial.notMem_support_iff.mp hp]
    exact MvPolynomial.monomial_zero
  -- the monomial basis of `A_d`
  let b : Module.Basis {s // s ∈ S} k (polyRightDegreeFDRep k N d) := Module.Basis.mk hli hsp
  have hbv : ∀ s, polyOf d (b s) = MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) := by
    intro s; rw [show b s = v s from Module.Basis.mk_apply hli hsp s]; exact hpolyv s
  -- reading a coordinate off `b` is reading a monomial coefficient
  have hrepr : ∀ (w : polyRightDegreeFDRep k N d) (a : {s // s ∈ S}),
      b.repr w a = MvPolynomial.coeff (↑a) (polyOf d w) := by
    intro w a
    have hexp : polyOf d w
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
    fun a c => rightTransPoly k N (↑((Fintype.equivFin {s // s ∈ S}).symm c))
      (↑((Fintype.equivFin {s // s ∈ S}).symm a)), fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, hrepr, polyOf_rho, hbv,
    evalAtGL_rightTransPoly]

/-! ### The determinant-quotient degree component is algebraic -/

/-- **`(A/det)_d` is algebraic.** It is the image of the algebraic `A_d` under the
surjective `GL_N`-equivariant quotient map `A_d → (A/det)_d`, so algebraicity transfers
by `IsAlgebraicRepresentation.of_surjective_equivariant`. This is the part-C hypothesis
the #4905 assembly requires. -/
theorem quotDetDegreeFDRep_isAlgebraic (k : Type*) [Field k] (N d : ℕ) :
    Etingof.IsAlgebraicRepresentation N
      (Etingof.CauchyDetQuotient.quotDetDegreeFDRep k N d).ρ := by
  have hmem_π : ∀ x ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d,
      Submodule.mkQ (Etingof.KernelLemmaKPrime.detSubmodule k N) x
        ∈ (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
            (Submodule.mkQ (Etingof.KernelLemmaKPrime.detSubmodule k N)) :=
    fun x hx => Submodule.mem_map_of_mem hx
  let πmap : polyRightDegreeFDRep k N d →ₗ[k]
      Etingof.CauchyDetQuotient.quotDetDegreeFDRep k N d :=
    (Submodule.mkQ (Etingof.KernelLemmaKPrime.detSubmodule k N)).restrict hmem_π
  refine IsAlgebraicRepresentation.of_surjective_equivariant πmap ?_ ?_
    (polyRightDegreeFDRep_isAlgebraic k N d)
  · -- surjectivity: every element of `(A/det)_d` is `mk` of a degree-`d` polynomial
    rintro ⟨_, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, Subtype.ext rfl⟩
  · -- equivariance: from `quotDetRep_mk`
    intro g v
    apply Subtype.ext
    change Submodule.mkQ _ (polyRightRep k N g (polyOf d v))
      = Etingof.KernelLemmaKPrime.quotDetRep k N g (Submodule.mkQ _ (polyOf d v))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Etingof.KernelLemmaKPrime.quotDetRep_mk]

end Etingof
