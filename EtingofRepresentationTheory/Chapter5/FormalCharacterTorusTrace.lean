import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

/-!
# Formal character evaluated at a torus element is a trace

For a polynomial `GL_N(k)`-representation `M` (one whose `ℕ`-valued weight spaces
span the whole module), the formal character `formalCharacter k N M`, regarded as
a polynomial in `N` variables, evaluates at a diagonal torus matrix `diag(t)` to
the trace of `M.ρ (diag(t))`:

```
aeval (fun i => (t i : k)) (formalCharacter k N M) = trace (M.ρ (diag(t)))
```

Both sides equal `∑_μ dim(M_μ) · ∏_i (t i)^(μ i)`, the sum over weights `μ` of the
weight-space dimension times the torus character `∏ t_i^{μ_i}`.

This is the `(B)` `formalCharacter ↔ torus-trace` connection requested in issue
#4886 (sub-issue of #4875). The hypothesis is the span condition
`⨆_μ glWeightSpace = ⊤` rather than `IsAlgebraicRepresentation` directly — this is
the form every downstream weight-space theorem in the project takes (cf.
`FormalCharacterIso.finrank_eq_sum_glWeightSpace`, `DetInvElim`,
`PolynomialRepEmbedding`), and is exactly what the assembly sub-issue consumes.
For algebraic representations the span condition holds.

## Main results

* `diagTorus` — the diagonal torus element `diag(t) ∈ GL_N(k)` for `t : Fin N → kˣ`.
* `glWeightSpace_diagTorus_apply` — on the weight space `M_μ`, `diag(t)` acts by the
  scalar `∏_i (t i)^(μ i)`.
* `aeval_formalCharacter_eq_trace` — the headline trace identity.
* `trace_combination_eq_zero_of_formalCharacter_combination_eq_zero` — payload `(B2)`:
  a vanishing ℚ-combination of formal characters forces the corresponding
  combination of torus traces to vanish.
-/

open MvPolynomial Matrix

namespace Etingof

noncomputable section

variable (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)

/-! ### The diagonal torus element -/

/-- The diagonal matrix `diag(t₁, …, t_N) ∈ GL_N(k)` for a tuple of units
`t : Fin N → kˣ`. This is the image of the maximal torus `(kˣ)^N ↪ GL_N(k)`. -/
noncomputable def diagTorus (t : Fin N → kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (fun i => (t i : k))
  inv := Matrix.diagonal (fun i => ((t i)⁻¹ : k))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; simp

/-- The partial diagonal torus element: `t i` at positions `i ∈ s` and `1`
elsewhere. Interpolates between `diagTorusOn ∅ = 1` and `diagTorusOn univ = diag(t)`,
multiplying one coordinate at a time. -/
noncomputable def diagTorusOn (s : Finset (Fin N)) (t : Fin N → kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (fun i => if i ∈ s then (t i : k) else 1)
  inv := Matrix.diagonal (fun i => if i ∈ s then ((t i)⁻¹ : k) else 1)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i ∈ s <;> simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i ∈ s <;> simp [h]

omit [IsAlgClosed k] in
theorem diagTorusOn_univ (t : Fin N → kˣ) :
    diagTorusOn k N Finset.univ t = diagTorus k N t := by
  apply Units.ext
  change Matrix.diagonal (fun i => if i ∈ Finset.univ then (t i : k) else 1) =
    Matrix.diagonal (fun i => (t i : k))
  simp

omit [IsAlgClosed k] in
theorem diagTorusOn_empty (t : Fin N → kˣ) :
    diagTorusOn k N ∅ t = 1 := by
  apply Units.ext
  change Matrix.diagonal (fun i => if i ∈ (∅ : Finset (Fin N)) then (t i : k) else 1) =
    (1 : Matrix (Fin N) (Fin N) k)
  simp

omit [IsAlgClosed k] in
theorem diagTorusOn_insert (a : Fin N) (s : Finset (Fin N)) (t : Fin N → kˣ)
    (ha : a ∉ s) :
    diagTorusOn k N (insert a s) t = diagUnit k N a (t a) * diagTorusOn k N s t := by
  apply Units.ext
  rw [Units.val_mul]
  change Matrix.diagonal (fun i => if i ∈ insert a s then (t i : k) else 1) =
    Matrix.diagonal (Function.update (1 : Fin N → k) a ((t a : k))) *
      Matrix.diagonal (fun i => if i ∈ s then (t i : k) else 1)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases hia : i = a
  · subst hia; simp [Finset.mem_insert, ha, Function.update_self]
  · simp [Finset.mem_insert, hia]

/-! ### Torus action on weight spaces -/

variable {k N}

/-- A single-coordinate torus element acts on the weight space `M_μ` by the scalar
`(t i)^{μ i}`. -/
theorem glWeightSpace_diagUnit_apply
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (i : Fin N) (s : kˣ)
    {v : M} (hv : v ∈ glWeightSpace k N M μ) :
    M.ρ (diagUnit k N i s) v = (s : k) ^ μ i • v := by
  have h1 : glWeightSpace k N M μ ≤ ⨅ (u : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i u) - ((u : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ i
  have h2 : (⨅ (u : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i u) - ((u : k) ^ μ i) • LinearMap.id)) ≤
      LinearMap.ker (M.ρ (diagUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ s
  have hker := LinearMap.mem_ker.mp (h2 (h1 hv))
  rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hker

/-- The partial diagonal torus element acts on the weight space `M_μ` by the scalar
`∏_{i ∈ s} (t i)^{μ i}`. -/
theorem glWeightSpace_diagTorusOn_apply
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (t : Fin N → kˣ) (s : Finset (Fin N))
    {v : M} (hv : v ∈ glWeightSpace k N M μ) :
    M.ρ (diagTorusOn k N s t) v = (∏ i ∈ s, (t i : k) ^ μ i) • v := by
  induction s using Finset.induction with
  | empty => rw [diagTorusOn_empty, map_one]; simp
  | insert a s ha ih =>
    rw [diagTorusOn_insert k N a s t ha, map_mul, Module.End.mul_apply, ih, map_smul,
      glWeightSpace_diagUnit_apply M μ a (t a) hv, Finset.prod_insert ha, smul_smul,
      mul_comm ((t a : k) ^ μ a) (∏ i ∈ s, (t i : k) ^ μ i)]

/-- The diagonal torus element acts on the weight space `M_μ` by the scalar
`∏_i (t i)^{μ i}`. -/
theorem glWeightSpace_diagTorus_apply
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (t : Fin N → kˣ)
    {v : M} (hv : v ∈ glWeightSpace k N M μ) :
    M.ρ (diagTorus k N t) v = (∏ i, (t i : k) ^ μ i) • v := by
  rw [← diagTorusOn_univ k N t]
  exact glWeightSpace_diagTorusOn_apply M μ t Finset.univ hv

/-! ### Formal character at a torus element is the trace -/

variable (k N)
variable [CharZero k]

/-- **`formalCharacter` ↔ torus trace.** For a polynomial `GL_N(k)`-representation
`M` (weight spaces spanning `M`), evaluating the formal character at a diagonal
torus matrix `diag(t)` recovers the trace of `M.ρ (diag(t))`. Both sides equal
`∑_μ dim(M_μ) · ∏_i (t i)^{μ i}`. -/
theorem aeval_formalCharacter_eq_trace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (t : Fin N → kˣ) :
    MvPolynomial.aeval (fun i => (t i : k)) (formalCharacter k N M) =
      LinearMap.trace k M (M.ρ (diagTorus k N t)) := by
  have h_indep : iSupIndep (fun μ : Fin N →₀ ℕ => glWeightSpace k N M (fun i => μ i)) :=
    glWeightSpace_iSupIndep k N M
  have hfin : {μ : Fin N →₀ ℕ | glWeightSpace k N M (fun i => μ i) ≠ ⊥}.Finite :=
    glWeightSpace_finite_support k N M
  have h_internal :
      DirectSum.IsInternal (fun μ : Fin N →₀ ℕ => glWeightSpace k N M (fun i => μ i)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨h_indep, h_top⟩
  -- The torus element preserves every weight space (it acts by a scalar there).
  have hmaps : ∀ μ : Fin N →₀ ℕ,
      Set.MapsTo (M.ρ (diagTorus k N t)) (glWeightSpace k N M (fun i => μ i))
        (glWeightSpace k N M (fun i => μ i)) := by
    intro μ v hv
    rw [glWeightSpace_diagTorus_apply M (fun i => μ i) t hv]
    exact Submodule.smul_mem _ _ hv
  -- Right side: trace splits over the internal direct sum of weight spaces.
  rw [LinearMap.trace_eq_sum_trace_restrict' h_internal hfin hmaps]
  -- Each weight-space restriction is the scalar `∏ (t i)^{μ i}`, so its trace is
  -- `dim(M_μ) · ∏ (t i)^{μ i}`.
  have hsummand : ∀ μ ∈ hfin.toFinset,
      LinearMap.trace k _ ((M.ρ (diagTorus k N t)).restrict (hmaps μ)) =
        (Module.finrank k (glWeightSpace k N M (fun i => μ i)) : k) *
          ∏ i, (t i : k) ^ (μ i) := by
    intro μ _
    have hrestrict : (M.ρ (diagTorus k N t)).restrict (hmaps μ) =
        (∏ i, (t i : k) ^ (μ i)) • LinearMap.id := by
      ext ⟨w, hw⟩
      simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        SetLike.val_smul]
      exact glWeightSpace_diagTorus_apply M (fun i => μ i) t hw
    rw [hrestrict, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hsummand]
  -- Left side: expand the formal character and evaluate term by term.
  unfold formalCharacter
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [map_smul, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Algebra.smul_def, map_natCast]

/-! ### Payload (B2): vanishing character combination ⟹ vanishing trace combination -/

/-- **Payload `(B2)`.** A vanishing ℚ-linear combination of formal characters of
polynomial representations forces the corresponding combination of torus traces to
vanish at every diagonal torus element. This is the form the Dedekind/Artin
assembly for #4875 consumes. -/
theorem trace_combination_eq_zero_of_formalCharacter_combination_eq_zero
    {ι : Type*} (s : Finset ι) (c : ι → ℚ)
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ∀ i ∈ s, ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (L i) (fun j => μ j) = ⊤)
    (h_char : ∑ i ∈ s, c i • formalCharacter k N (L i) = 0)
    (t : Fin N → kˣ) :
    ∑ i ∈ s, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (diagTorus k N t)) = 0 := by
  have key : ∑ i ∈ s, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (diagTorus k N t)) =
      MvPolynomial.aeval (fun j => (t j : k))
        (∑ i ∈ s, c i • formalCharacter k N (L i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [map_smul, aeval_formalCharacter_eq_trace k N (L i) (h_top i hi) t, Rat.smul_def,
      Algebra.smul_def, map_ratCast]
  rw [key, h_char, map_zero]

end

end Etingof
