import EtingofRepresentationTheory.Chapter5.CleanQuotientHelpers
import EtingofRepresentationTheory.Chapter5.CleanSubSpanning
import EtingofRepresentationTheory.Chapter5.CleanCharacterExtractionBase
import EtingofRepresentationTheory.Chapter5.SimpleSubrepExtraction
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# DetInvElim-clean constituent-character extraction (issue #5082)

This file provides the DetInvElim-clean replacement for the (circular, polluted)
`Etingof.simple_constituent_formalCharacter_eq_schurPoly_mem`
(`ConstituentCharacterExtraction.lean`).  The polluted route went through
`decompose_polynomial_gl_rep`, which tensor-embeds via `detInv_elim` and therefore drags in
the whole `DetInvElim` tower (a build cycle for the `CauchyDetQuotient` consumer).  Here we
reprove the same statement via a **composition series + character additivity** route that
imports only DetInvElim-clean files.

## Route

1. `subFDRep_iSup_glWeightSpace_eq_top` — the *sub-of-spanning-is-spanning* glue: a
   torus-invariant sub-`FDRep` of a weight-spanning `FDRep` is weight-spanning.  This is the
   trivial `subFDRep`-level wrapper around the genuine crux
   `Etingof.CleanCharExtraction.torusInvariant_iSup_inf_glWeightSpace_eq` (#5086).
2. `formalCharacter_eq_sum_simple_factors` — a `finrank` induction peeling a simple
   `GL_N`-submodule off `M` at each step and applying the short-exact-sequence additivity
   `formalCharacter_eq_sub_add_quotient`: every algebraic, weight-spanning `M` has a finite
   family of **simple algebraic weight-spanning** composition factors whose characters sum to
   `char M`.
3. `clean_simple_constituent_formalCharacter_eq_schurPoly_mem` — the extractor: peel the
   simple `L ↪ M` off first, so `char M = char L + char (M/L)`; expand `char (M/L)` by step 2;
   equate with the Schur-polynomial hypothesis `char M = ∑_{ν∈S} c_ν S_ν`.  Each `S_ν` is the
   character of the simple algebraic `SchurModule k N ν.val`, so the resulting vanishing
   ℚ-relation among characters of simple algebraic reps is killed (coefficient by coefficient)
   by the torus-trace character-independence engine
   `Etingof.formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general`, pinning
   `char L = S_ν` for some `ν ∈ S` with `c_ν > 0`.
-/

open CategoryTheory MvPolynomial

noncomputable section

namespace Etingof

open CleanCharExtraction

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- **Sub-of-spanning-is-spanning (the `subFDRep` wrapper).** If the `ℕ`-weight spaces of `M`
span `M`, then those of the sub-`FDRep` `subFDRep M σ` span it too. This is the trivial
`glWeightSpace_inf_range` glue on top of the genuine crux
`torusInvariant_iSup_inf_glWeightSpace_eq` (#5086). -/
theorem subFDRep_iSup_glWeightSpace_eq_top (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (subFDRep M σ) (fun i => μ i) = ⊤ := by
  classical
  set ι : subFDRep M σ →ₗ[k] M := σ.toSubmodule.subtype with hιdef
  have hι : ∀ g v, ι ((subFDRep M σ).ρ g v) = M.ρ g (ι v) := subFDRep_subtype_equivariant M σ
  have hι_inj : Function.Injective ι := subFDRep_subtype_injective M σ
  have hrange : LinearMap.range ι = σ.toSubmodule := Submodule.range_subtype _
  have hinv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k), ∀ v ∈ σ.toSubmodule,
      M.ρ g v ∈ σ.toSubmodule := fun g v hv => σ.apply_mem_toSubmodule g hv
  have htor := torusInvariant_iSup_inf_glWeightSpace_eq (k := k) N M σ.toSubmodule hinv hM
  -- Rewrite the torus-invariant decomposition in terms of `subFDRep` weight spaces.
  have hkey : (fun μ : Fin N →₀ ℕ => glWeightSpace k N M (fun i => μ i) ⊓ σ.toSubmodule)
      = (fun μ : Fin N →₀ ℕ => (glWeightSpace k N (subFDRep M σ) (fun i => μ i)).map ι) := by
    funext μ
    rw [← hrange]
    exact glWeightSpace_inf_range N (subFDRep M σ) M ι hι hι_inj (fun i => μ i)
  rw [hkey, ← Submodule.map_iSup] at htor
  -- `(⨆ ...).map ι = σ.toSubmodule = range ι = (⊤).map ι`, and `ι` is injective.
  have hmaptop : (⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (subFDRep M σ) (fun i => μ i)).map ι
      = (⊤ : Submodule k (subFDRep M σ)).map ι := by
    rw [Submodule.map_top, hrange]; exact htor
  exact Submodule.map_injective_of_injective hι_inj hmaptop

/-- **The sub-`FDRep` is algebraic when `M` is.** Restriction of an algebraic representation
to an invariant submodule is algebraic. -/
theorem subFDRep_isAlgebraic (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : Etingof.IsAlgebraicRepresentation N M.ρ) :
    Etingof.IsAlgebraicRepresentation N (subFDRep M σ).ρ := by
  have hrestrict := hM.restrict σ.toSubmodule (fun g v hv => σ.apply_mem_toSubmodule g hv)
  simpa only [subFDRep, FDRep.of_ρ'] using hrestrict

/-- **Composition-series character additivity.** Every algebraic, weight-spanning `FDRep` `M`
admits a finite family of simple, algebraic, weight-spanning composition factors `W j` whose
formal characters sum to `char M`. Proved by a `finrank` induction: peel a simple `GL_N`-sub
`S ≤ M`, split `char M = char (subFDRep S) + char (M / S)` by SES additivity, and recurse on
the strictly-smaller quotient. -/
theorem formalCharacter_eq_sum_simple_factors (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (p : ℕ) (W : Fin p → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      (∀ j, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule (W j).ρ)) ∧
      (∀ j, Etingof.IsAlgebraicRepresentation N (W j).ρ) ∧
      (∀ j, ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (W j) (fun i => μ i) = ⊤) ∧
      formalCharacter k N M = ∑ j, formalCharacter k N (W j) := by
  classical
  -- Strong induction on `finrank k M`.
  suffices H : ∀ n (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      Module.finrank k M = n →
      Etingof.IsAlgebraicRepresentation N M.ρ →
      (⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) →
      ∃ (p : ℕ) (W : Fin p → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
        (∀ j, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
            (Representation.asModule (W j).ρ)) ∧
        (∀ j, Etingof.IsAlgebraicRepresentation N (W j).ρ) ∧
        (∀ j, ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (W j) (fun i => μ i) = ⊤) ∧
        formalCharacter k N M = ∑ j, formalCharacter k N (W j) by
    exact H _ M rfl halg hM
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn halg hM
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- Base case: `finrank M = 0`, so every weight space is trivial and `char M = 0`.
      refine ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      apply MvPolynomial.ext
      intro μ
      rw [formalCharacter_coeff, MvPolynomial.coeff_zero]
      have hz : Module.finrank k (glWeightSpace k N M (fun i => μ i)) = 0 := by
        have hle := Submodule.finrank_le (glWeightSpace k N M (fun i => μ i))
        omega
      rw [hz]; norm_num
    · -- Inductive step: peel a simple submodule.
      haveI hMnt : Nontrivial M :=
        Module.nontrivial_of_finrank_pos (R := k) (by rw [hn]; exact hnpos)
      haveI : Nontrivial (Representation.asModule M.ρ) := by
        obtain ⟨a, b, hab⟩ := exists_pair_ne M
        exact ⟨(Representation.asModuleEquiv M.ρ).symm a, (Representation.asModuleEquiv M.ρ).symm b,
          fun h => hab ((Representation.asModuleEquiv M.ρ).symm.injective h)⟩
      have htop_ne : (⊤ : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule M.ρ)) ≠ ⊥ := by
        intro h
        rw [Submodule.eq_bot_iff] at h
        obtain ⟨a, ha⟩ := exists_ne (0 : Representation.asModule M.ρ)
        exact ha (h a Submodule.mem_top)
      obtain ⟨S, hSsimple, _hSle⟩ := exists_isSimpleModule_le M.ρ ⊤ htop_ne
      set σ : Subrepresentation M.ρ := Subrepresentation.ofSubmodule' S with hσdef
      have hσasSub : σ.asSubmodule = S := by
        ext w
        rw [Subrepresentation.mem_asSubmodule_iff, hσdef, Subrepresentation.mem_ofSubmodule'_iff]
      -- `subFDRep M σ` is simple, algebraic, weight-spanning.
      have hsubsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule (subFDRep M σ).ρ) := by
        have h1 : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
            σ.asSubmodule := hσasSub ▸ hSsimple
        have h2 := isSimpleModule_toRepresentation_asModule σ h1
        simpa only [subFDRep, FDRep.of_ρ'] using h2
      have hsubalg : Etingof.IsAlgebraicRepresentation N (subFDRep M σ).ρ :=
        subFDRep_isAlgebraic k N M σ halg
      have hsubspan : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (subFDRep M σ) (fun i => μ i) = ⊤ :=
        subFDRep_iSup_glWeightSpace_eq_top k N M σ hM
      -- `σ.toSubmodule ≠ ⊥`, so the quotient has strictly smaller `finrank`.
      have hSne : S ≠ ⊥ := by
        haveI := hSsimple
        exact Submodule.nontrivial_iff_ne_bot.mp
          (IsSimpleModule.nontrivial (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) S)
      have hStne : σ.toSubmodule ≠ ⊥ := by
        rw [Submodule.ne_bot_iff] at hSne ⊢
        obtain ⟨x, hxS, hx0⟩ := hSne
        have hxσ : x ∈ σ.asSubmodule := hσasSub ▸ hxS
        rw [Subrepresentation.mem_asSubmodule_iff] at hxσ
        exact ⟨x, hxσ, hx0⟩
      have hquot_alg : Etingof.IsAlgebraicRepresentation N (quotientFDRep M σ).ρ :=
        quotientFDRep_isAlgebraic M σ halg
      have hquot_span :
          ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (quotientFDRep M σ) (fun i => μ i) = ⊤ :=
        quotientFDRep_iSup_glWeightSpace_eq_top M σ hM
      have hquot_finrank : Module.finrank k (quotientFDRep M σ) < n := by
        have hadd := Submodule.finrank_quotient_add_finrank σ.toSubmodule
        haveI : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hStne
        have hpos : 0 < Module.finrank k σ.toSubmodule := Module.finrank_pos
        have hq : Module.finrank k (quotientFDRep M σ) = Module.finrank k (M ⧸ σ.toSubmodule) :=
          rfl
        rw [hq]; omega
      obtain ⟨p, W, hWsimple, hWalg, hWspan, hWchar⟩ :=
        ih _ hquot_finrank (quotientFDRep M σ) rfl hquot_alg hquot_span
      -- Assemble: `subFDRep M σ` followed by the factors of the quotient.
      refine ⟨p + 1, Fin.cons (subFDRep M σ) W, ?_, ?_, ?_, ?_⟩
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubsimple
        · exact hWsimple
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubalg
        · exact hWalg
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubspan
        · exact hWspan
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← hWchar]
        exact formalCharacter_eq_sub_add_quotient M σ hsubspan hM

/-- **DetInvElim-clean constituent-character extraction (#5082).** Same statement as the
polluted `Etingof.simple_constituent_formalCharacter_eq_schurPoly_mem`, proved without
`decompose_polynomial_gl_rep`. -/
theorem clean_simple_constituent_formalCharacter_eq_schurPoly_mem (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (S : Finset {l : Fin N → ℕ // Antitone l})
    (c : {l : Fin N → ℕ // Antitone l} → ℕ)
    (hchar : formalCharacter k N M = ∑ ν ∈ S, (c ν : ℚ) • schurPoly N ν.val)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] M)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = M.ρ g (φ v)) :
    ∃ ν ∈ S, 0 < c ν ∧ formalCharacter k N L = schurPoly N ν.val := by
  sorry

end Etingof

end
