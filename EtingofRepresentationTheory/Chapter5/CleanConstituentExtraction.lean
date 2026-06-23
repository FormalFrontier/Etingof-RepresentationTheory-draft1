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

/-- **Clean `SchurModule` weight-spanning.** The `ℕ`-weight spaces of `SchurModule k N lam`
span it. This is the DetInvElim-clean replacement for the banned
`glWeightSpace_schurModule_iSup_eq_top` (which lives in the polluted
`SchurWeylFormalCharacterIso`): `SchurModule` is the image of the GL-equivariant
`youngSymEndomorphism` applied to the weight-spanning `glTensorRep`, so spanning transfers
through the equivariant surjection `LinearMap.rangeRestrict`. The proof body uses only clean
infrastructure (`glTensorRep_iSup_glWeightSpace_eq_top`, `glTensor_comm_youngSym`). -/
theorem schurModule_iSup_glWeightSpace_eq_top_clean (N : ℕ) (lam : Fin N → ℕ) :
    ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (SchurModule k N lam) (fun i => μ i) = ⊤ := by
  refine glWeightSpace_iSup_eq_top_of_equivariant_surjective N
    (FDRep.of (glTensorRep k N (∑ i, lam i))) (SchurModule k N lam)
    (LinearMap.rangeRestrict (youngSymEndomorphism k N lam)) ?_
    (LinearMap.surjective_rangeRestrict _)
    (glTensorRep_iSup_glWeightSpace_eq_top k N (∑ i, lam i))
  intro g v
  apply Subtype.ext
  change youngSymEndomorphism k N lam ((FDRep.of (glTensorRep k N (∑ i, lam i))).ρ g v)
     = (glTensorRep k N (∑ i, lam i) g) (youngSymEndomorphism k N lam v)
  rw [FDRep.of_ρ']
  exact (LinearMap.ext_iff.mp (glTensor_comm_youngSym k N lam g) v).symm

/-- **Isomorphic `FDRep`s have equal formal characters.** Extracts the `k`-linear intertwiner of
a categorical `FDRep` isomorphism and feeds it to `formalCharacter_eq_of_rep_iso`. The
contrapositive (distinct characters ⟹ non-isomorphic) is what supplies the pairwise-distinctness
hypothesis of the torus-trace engine after dedup-by-character. -/
theorem formalCharacter_eq_of_FDRep_iso (N : ℕ)
    (X Y : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (e : X ≅ Y) :
    formalCharacter k N X = formalCharacter k N Y := by
  have hint : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : X),
      (FDRep.isoToLinearEquiv e) (X.ρ g v) = Y.ρ g ((FDRep.isoToLinearEquiv e) v) := by
    intro g v
    have h := FDRep.Iso.conj_ρ e g
    have hconj : (FDRep.isoToLinearEquiv e).conj (X.ρ g) ((FDRep.isoToLinearEquiv e) v)
        = (FDRep.isoToLinearEquiv e) (X.ρ g v) := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [(FDRep.isoToLinearEquiv e).symm_apply_apply]
    rw [h, hconj]
  have h0 := formalCharacter_eq_of_rep_iso k N X.ρ Y.ρ (FDRep.isoToLinearEquiv e) hint
  rwa [formalCharacter_FDRep_of_ρ, formalCharacter_FDRep_of_ρ] at h0

/-- **Torus-trace character-independence engine (combined wrapper).** A vanishing ℚ-linear
combination of formal characters of a finite family of *pairwise non-isomorphic*, simple,
algebraic, weight-spanning `GL_N(k)`-representations forces every coefficient to vanish. Chains
`trace_combination_eq_zero_of_formalCharacter_combination_eq_zero` (character ⟹ torus-trace
combination) into `formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general`
(torus-trace ⟹ coefficients zero). -/
theorem coeff_zero_of_char_combination_zero (N : ℕ) {ι : Type} [Fintype ι]
    (R : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hRalg : ∀ i, Etingof.IsAlgebraicRepresentation N (R i).ρ)
    (hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (R i).ρ))
    (hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (R i) (fun j => μ j) = ⊤)
    (hRdist : Pairwise (fun i j => ¬ Nonempty ((R i) ≅ (R j))))
    (a : ι → ℚ)
    (hcomb : ∑ i, a i • formalCharacter k N (R i) = 0) :
    ∀ i, a i = 0 := by
  classical
  refine formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general
    (k := k) N R hRalg hRsimp hRdist a (fun t => ?_)
  have hchar0 : ∑ i ∈ Finset.univ, a i • formalCharacter k N (R i) = 0 := by simpa using hcomb
  have h := trace_combination_eq_zero_of_formalCharacter_combination_eq_zero
    (k := k) (N := N) Finset.univ a R (fun i _ => hRspan i) hchar0 t
  simpa using h

/-- **Net coefficient at each character value vanishes (dedup-by-character).** For a finite family
of simple, algebraic, weight-spanning `GL_N(k)`-representations with a vanishing ℚ-linear
combination of formal characters, the *net* coefficient at every character value `w` — the sum of
`a i` over all indices `i` whose representation has character `w` — is zero. Proved by deduplicating
the family by character value into pairwise non-isomorphic representatives (distinct characters ⟹
non-isomorphic, via `formalCharacter_eq_of_FDRep_iso`) and feeding the regrouped combination to
`coeff_zero_of_char_combination_zero`. Kept generic in `R` so the dedup machinery never sees the
caller's concrete `Sum.elim` family (which otherwise triggers a `whnf` defeq blowup). -/
theorem net_coeff_zero_of_char_combination_zero (N : ℕ) {ι : Type} [Fintype ι]
    (R : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hRalg : ∀ i, Etingof.IsAlgebraicRepresentation N (R i).ρ)
    (hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (R i).ρ))
    (hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (R i) (fun j => μ j) = ⊤)
    (a : ι → ℚ)
    (hcomb : ∑ i, a i • formalCharacter k N (R i) = 0)
    (w : MvPolynomial (Fin N) ℚ) :
    ∑ i ∈ Finset.univ.filter (fun i => formalCharacter k N (R i) = w), a i = 0 := by
  classical
  let χ : ι → MvPolynomial (Fin N) ℚ := fun i => formalCharacter k N (R i)
  let reps : Finset (MvPolynomial (Fin N) ℚ) := Finset.image χ Finset.univ
  by_cases hw : w ∈ reps
  · have hpickex : ∀ w : {w // w ∈ reps}, ∃ i, χ i = w.1 := by
      intro w
      have hw := w.2
      simp only [reps, Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨i, hi⟩ := hw
      exact ⟨i, hi⟩
    choose pick hpick using hpickex
    let Rep : {w // w ∈ reps} → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
      fun w => R (pick w)
    let b : {w // w ∈ reps} → ℚ :=
      fun w => ∑ i ∈ Finset.univ.filter (fun i => χ i = w.1), a i
    have hRepchar : ∀ w, formalCharacter k N (Rep w) = w.1 := fun w => hpick w
    have hzero : ∑ w ∈ reps, (∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i) • w = 0 := by
      have h1 : ∑ w ∈ reps, (∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i) • w
          = ∑ w ∈ reps, ∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i • χ i := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_filter] at hi
        rw [hi.2]
      rw [h1, Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i)) (fun i => a i • χ i)]
      exact hcomb
    have hRepcomb : ∑ w : {w // w ∈ reps}, b w • formalCharacter k N (Rep w) = 0 := by
      have hstep : ∀ w : {w // w ∈ reps}, b w • formalCharacter k N (Rep w)
          = (fun w0 => (∑ i ∈ Finset.univ.filter (fun i => χ i = w0), a i) • w0) w.1 := by
        intro w; rw [hRepchar w]
      rw [Finset.sum_congr rfl (fun w _ => hstep w),
        Finset.sum_coe_sort reps
          (fun w0 => (∑ i ∈ Finset.univ.filter (fun i => χ i = w0), a i) • w0)]
      exact hzero
    have hRepdist :
        Pairwise (fun w w' : {w // w ∈ reps} => ¬ Nonempty ((Rep w) ≅ (Rep w'))) := by
      intro w w' hww'
      rintro ⟨e⟩
      apply hww'
      apply Subtype.ext
      have h3 := formalCharacter_eq_of_FDRep_iso k N (Rep w) (Rep w') e
      rw [hRepchar w, hRepchar w'] at h3
      exact h3
    have hb0 := coeff_zero_of_char_combination_zero k N Rep
      (fun w => hRalg (pick w)) (fun w => hRsimp (pick w)) (fun w => hRspan (pick w))
      hRepdist b hRepcomb
    exact hb0 ⟨w, hw⟩
  · have hempty : Finset.univ.filter (fun i => formalCharacter k N (R i) = w) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hi
      have hmem : formalCharacter k N (R i) ∈ reps :=
        Finset.mem_image_of_mem χ (Finset.mem_univ i)
      rw [hi] at hmem
      exact hw hmem
    rw [hempty, Finset.sum_empty]

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
  classical
  -- ### Step A: the image subrepresentation `σL ≅ L` (algebraic, weight-spanning).
  let σL : Subrepresentation M.ρ :=
    ⟨LinearMap.range φ, by
      rintro g v ⟨w, rfl⟩
      exact ⟨L.ρ g w, hφ_equiv g w⟩⟩
  let e' : L ≃ₗ[k] (subFDRep M σL) := LinearEquiv.ofInjective φ hφ_inj
  have he' : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      e' (L.ρ g v) = (subFDRep M σL).ρ g (e' v) := by
    intro g v
    apply subFDRep_subtype_injective M σL
    rw [subFDRep_subtype_equivariant]
    exact hφ_equiv g v
  have he'symm : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : subFDRep M σL),
      e'.symm ((subFDRep M σL).ρ g v) = L.ρ g (e'.symm v) := by
    intro g v
    apply e'.injective
    rw [e'.apply_symm_apply, he', e'.apply_symm_apply]
  have hsubalg : Etingof.IsAlgebraicRepresentation N (subFDRep M σL).ρ :=
    subFDRep_isAlgebraic k N M σL halg
  have hsubspan : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (subFDRep M σL) (fun i => μ i) = ⊤ :=
    subFDRep_iSup_glWeightSpace_eq_top k N M σL h_span
  have hcharL : formalCharacter k N L = formalCharacter k N (subFDRep M σL) := by
    have h0 := formalCharacter_eq_of_rep_iso k N L.ρ (subFDRep M σL).ρ e' he'
    rwa [formalCharacter_FDRep_of_ρ, formalCharacter_FDRep_of_ρ] at h0
  -- ### Step B: short-exact-sequence split `char M = char L + ∑_j char (W j)`.
  have hquotalg : Etingof.IsAlgebraicRepresentation N (quotientFDRep M σL).ρ :=
    quotientFDRep_isAlgebraic M σL halg
  have hquotspan :
      ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (quotientFDRep M σL) (fun i => μ i) = ⊤ :=
    quotientFDRep_iSup_glWeightSpace_eq_top M σL h_span
  obtain ⟨p, W, hWsimp, hWalg, hWspan, hWchar⟩ :=
    formalCharacter_eq_sum_simple_factors k N (quotientFDRep M σL) hquotalg hquotspan
  have hMdecomp : formalCharacter k N M
      = formalCharacter k N L + ∑ j, formalCharacter k N (W j) := by
    rw [formalCharacter_eq_sub_add_quotient M σL hsubspan h_span, ← hcharL, hWchar]
  -- ### Step C: assemble the raw family `{L} ∪ {W j} ∪ {SchurModule ν}ᵥ` with coefficients.
  let R : Unit ⊕ Fin p ⊕ {ν // ν ∈ S} → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
    Sum.elim (fun _ => L) (Sum.elim W (fun ν => SchurModule k N ν.1.val))
  let a : Unit ⊕ Fin p ⊕ {ν // ν ∈ S} → ℚ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (fun ν => -(c ν.1 : ℚ)))
  have hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (R i).ρ) := by
    rintro (_ | j | ν)
    · exact hLsimp
    · exact hWsimp j
    · exact schurModule_isSimple_general k N ν.1.val ν.1.property
  have hRalg : ∀ i, Etingof.IsAlgebraicRepresentation N (R i).ρ := by
    rintro (_ | j | ν)
    · exact IsAlgebraicRepresentation.of_linearEquiv e'.symm he'symm hsubalg
    · exact hWalg j
    · exact schurModule_isAlgebraic (k := k) N ν.1.val
  have hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (R i) (fun j => μ j) = ⊤ := by
    rintro (_ | j | ν)
    · exact glWeightSpace_iSup_eq_top_of_equivariant_surjective N (subFDRep M σL) L
        e'.symm.toLinearMap he'symm e'.symm.surjective hsubspan
    · exact hWspan j
    · exact schurModule_iSup_glWeightSpace_eq_top_clean k N ν.1.val
  -- The vanishing character combination `char L + ∑_j char (W j) - ∑_{ν∈S} c_ν S_ν = char M - char M`.
  have hcomb : ∑ i, a i • formalCharacter k N (R i) = 0 := by
    have hsplit : ∑ i, a i • formalCharacter k N (R i)
        = (formalCharacter k N L + ∑ j, formalCharacter k N (W j))
          + (-∑ ν ∈ S, (c ν : ℚ) • schurPoly N ν.val) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hUnit : ∑ _x : Unit, a (Sum.inl _x) • formalCharacter k N (R (Sum.inl _x))
          = formalCharacter k N L := by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        show (1 : ℚ) • formalCharacter k N L = formalCharacter k N L
        rw [one_smul]
      have hW : ∑ j : Fin p, a (Sum.inr (Sum.inl j)) • formalCharacter k N (R (Sum.inr (Sum.inl j)))
          = ∑ j, formalCharacter k N (W j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        show (1 : ℚ) • formalCharacter k N (W j) = formalCharacter k N (W j)
        rw [one_smul]
      have hV : ∑ ν : {ν // ν ∈ S},
            a (Sum.inr (Sum.inr ν)) • formalCharacter k N (R (Sum.inr (Sum.inr ν)))
          = -∑ ν ∈ S, (c ν : ℚ) • schurPoly N ν.val := by
        rw [← Finset.sum_neg_distrib,
          ← Finset.sum_coe_sort S (fun ν => -((c ν : ℚ) • schurPoly N ν.val))]
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        show (-(c ν.1 : ℚ)) • formalCharacter k N (SchurModule k N ν.1.val)
            = -((c ν.1 : ℚ) • schurPoly N ν.1.val)
        rw [formalCharacter_schurModule_eq_schurPoly k N ν.1.val ν.1.property, neg_smul]
      rw [hUnit, hW, hV, ← add_assoc]
    rw [hsplit, ← hMdecomp, ← hchar, add_neg_cancel]
  -- ### Step D: the net coefficient at every character value vanishes (dedup-by-character engine).
  have hnet := net_coeff_zero_of_char_combination_zero k N R hRalg hRsimp hRspan a hcomb
  -- ### Step E: read off the conclusion from the net coefficient at `char L`.
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ ν ∈ S, 0 < c ν → formalCharacter k N L ≠ schurPoly N ν.val`
  have hcν0 : ∀ ν ∈ S, schurPoly N ν.val = formalCharacter k N L → c ν = 0 := by
    intro ν hν heq
    by_contra hc
    exact hcon ν hν (Nat.pos_of_ne_zero hc) heq.symm
  have hbw0 := hnet (formalCharacter k N L)
  -- Every term in the net coefficient at `char L` is nonnegative, and `L` itself contributes `1`.
  have hnonneg : ∀ i ∈ Finset.univ.filter (fun i => formalCharacter k N (R i) = formalCharacter k N L),
      0 ≤ a i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨_, hχi⟩ := hi
    match i with
    | Sum.inl () => show (0 : ℚ) ≤ 1; norm_num
    | Sum.inr (Sum.inl j) => show (0 : ℚ) ≤ 1; norm_num
    | Sum.inr (Sum.inr ν) =>
        have hchareq : formalCharacter k N (SchurModule k N ν.1.val) = schurPoly N ν.1.val :=
          formalCharacter_schurModule_eq_schurPoly k N ν.1.val ν.1.property
        rw [show formalCharacter k N (R (Sum.inr (Sum.inr ν)))
            = formalCharacter k N (SchurModule k N ν.1.val) from rfl, hchareq] at hχi
        have hc0 : c ν.1 = 0 := hcν0 ν.1 ν.2 hχi
        show (0 : ℚ) ≤ -(c ν.1 : ℚ)
        rw [hc0]; norm_num
  have hmem0 : (Sum.inl () : Unit ⊕ Fin p ⊕ {ν // ν ∈ S})
      ∈ Finset.univ.filter (fun i => formalCharacter k N (R i) = formalCharacter k N L) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hone : (1 : ℚ)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => formalCharacter k N (R i) = formalCharacter k N L), a i := by
    have hle := Finset.single_le_sum hnonneg hmem0
    simpa using hle
  rw [hbw0] at hone
  exact absurd hone (by norm_num)

end Etingof

end
