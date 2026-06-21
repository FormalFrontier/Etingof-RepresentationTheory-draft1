import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification

/-!
# Schur-Weyl #6: the formal character determines the isomorphism class

This file hosts `iso_of_formalCharacter_eq_schurPoly` (Etingof §5.22, issue
#2483): a finite-dimensional polynomial `GL_N(k)`-representation whose formal
character equals a Schur polynomial `S_λ` is isomorphic to the Schur module
`L_λ`.

## Why this lives here (not in `FormalCharacterIso`)

The theorem's essential dependency `decompose_polynomial_gl_rep`
(`PolynomialGLDecomposition`) sits **downstream** of `FormalCharacterIso`:
`PolynomialGLDecomposition` imports `FormalCharacterIso`. Proving the theorem in
`FormalCharacterIso` would therefore create an import cycle. It is relocated here,
downstream of both `PolynomialGLDecomposition` (the equivariant decomposition)
and `SchurWeylSimplesClassification` (#4698, linear independence of the abstract
simple characters). See issue #4699.

## Proof route (abstract-simple form)

Let `n := ∑ i, lam i`.

1. **`M` is homogeneous of degree `n`.** `weight_magnitude_of_formalCharacter_eq_schurPoly`
   turns `formalCharacter M = schurPoly N lam` into the `h_homog` hypothesis
   `decompose_polynomial_gl_rep` expects.
2. **Decompose `M`.** `decompose_polynomial_gl_rep` gives
   `M.asModule ≃ ⨁_{j:Fin p} (L (f j)).asModule` for abstract simples `L i`.
3. **Character match.** Push `formalCharacter` through the decomposition
   (`formalCharacter_directSum` + `formalCharacter_eq_of_rep_iso`):
   `schurPoly N lam = formalCharacter M = ∑_j formalCharacter (L (f j))`.
4. **Conclude via #4698.** The abstract simples each have `formalCharacter` a
   distinct Schur polynomial, so their characters are linearly independent
   (`SchurWeylSimplesClassification`). The single-`schurPoly` left side then
   forces `p = 1` with `f 0` the class of `L_λ`, hence
   `M ≃ L_λ` at the `asModule` level; rebuild the categorical `≅`.

## Status

The assembly `iso_of_formalCharacter_eq_schurPoly` is **sorry-free in its own proof**.
It takes the algebraicity (`halg`) and spanning (`h_span`) hypotheses explicitly — both
are what make `M` genuinely polynomial — and routes the decomposition through
`decompose_polynomial_gl_rep`, whose schurPoly-classification of the abstract simples it
matches against `S_λ` via `schurPoly_linearIndependent` to force a single summand.

Two pieces of deferred (Tier-4) content are isolated as `sorry`s and consumed
transitively:

* `simpleRep_iso_schurModule_of_formalCharacter_eq` (this file): the iso-strength
  highest-weight uniqueness "a simple polynomial `GL_N`-rep with character `S_λ` is `L_λ`".
  This is the natural strengthening of `schurWeyl_simples_formalCharacter_classification_core`
  (#4721), which only classifies characters.
* The classification crux itself (#4721) and pairwise distinctness (#4731), reached
  through `decompose_polynomial_gl_rep`.

The reusable glue `Representation.kEquivOfAsModuleEquiv` (the reverse of
`asModuleEquivOfIntertwiner`) bridges the module-level `≃ₗ[MonoidAlgebra]` output of the
decomposition to a `k`-linear GL-equivariant equivalence, feeding both the character
computation (via `formalCharacter_eq_of_rep_iso`) and the categorical iso (via
`Action.mkIso`). (The ℂ-side file `SchurWeylSimplesClassificationComplex` independently
packages the character half as `formalCharacter_eq_of_asModule_linearEquiv`.)
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct

noncomputable section

universe u

namespace Representation

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {V W : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- **Reverse glue (the `k`-linear equivalence underlying a `MonoidAlgebra`-linear
equivalence of `asModule`s).** A `MonoidAlgebra k G`-linear equivalence between the
`asModule`s of two representations restricts, via `asModuleEquiv`, to a `k`-linear
equivalence between their carriers. This is the inverse direction of
`asModuleEquivOfIntertwiner`: it extracts the carrier-level equivalence from the
module-level one. -/
def kEquivOfAsModuleEquiv {ρ : Representation k G V} {σ : Representation k G W}
    (φ : Representation.asModule ρ ≃ₗ[MonoidAlgebra k G] Representation.asModule σ) :
    V ≃ₗ[k] W :=
  ρ.asModuleEquiv.symm ≪≫ₗ φ.restrictScalars k ≪≫ₗ σ.asModuleEquiv

/-- The `k`-linear equivalence `kEquivOfAsModuleEquiv φ` intertwines `ρ` and `σ`.
The `MonoidAlgebra` action records the group action (`asModuleEquiv_symm_map_rho`,
`asModuleEquiv_map_smul`), so transporting `φ`'s `MonoidAlgebra`-linearity back to the
carriers turns it into `G`-equivariance. -/
theorem kEquivOfAsModuleEquiv_intertwines {ρ : Representation k G V}
    {σ : Representation k G W}
    (φ : Representation.asModule ρ ≃ₗ[MonoidAlgebra k G] Representation.asModule σ)
    (g : G) (v : V) :
    kEquivOfAsModuleEquiv φ (ρ g v) = σ g (kEquivOfAsModuleEquiv φ v) := by
  simp only [kEquivOfAsModuleEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [ρ.asModuleEquiv_symm_map_rho, map_smul, σ.asModuleEquiv_map_smul,
    MonoidAlgebra.of_apply, σ.asAlgebraHom_single, one_smul]

end Representation

namespace Etingof

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- The formal character only depends on the underlying representation: rebuilding
`M` as `FDRep.of M.ρ` does not change its character. -/
theorem formalCharacter_FDRep_of_ρ (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    formalCharacter k N (FDRep.of M.ρ) = formalCharacter k N M :=
  formalCharacter_eq_of_rep_iso k N M.ρ M.ρ (LinearEquiv.refl k M) (fun _ _ => rfl)


/-- **Highest-weight uniqueness (isolated `sorry`, issue #4721).** A *simple* polynomial
`GL_N(k)`-representation whose formal character is the Schur polynomial `S_λ` (for an
antitone `λ`) is isomorphic to the Schur module `L_λ`.

This is the iso-strength form of the highest-weight classification. The existing
`schurWeyl_simples_formalCharacter_classification_core` (#4721) only pins the *character*
of an abstract simple to a Schur polynomial; identifying the simple itself with the
concrete `SchurModule` is the same deferred Tier-4 content ("a simple polynomial
`GL_N`-rep is determined by its character"), isolated here as a single `sorry` so the
assembly `iso_of_formalCharacter_eq_schurPoly` below is otherwise sorry-free. -/
theorem simpleRep_iso_schurModule_of_formalCharacter_eq (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (h : formalCharacter k N L = schurPoly N lam) :
    Nonempty (L ≅ SchurModule k N lam) := by
  sorry

/-- A polynomial `GL_N(k)`-representation whose formal character equals a Schur
polynomial `S_λ` is isomorphic to the Schur module `L_λ`.

The hypotheses `halg` (algebraicity) and `h_span` (the `ℕ`-valued weight spaces span all
of `M`) are what make `M` genuinely *polynomial*: together they exclude the would-be
counterexample `M = L_λ ⊕ det⁻¹` (whose `det⁻¹`-summand contributes no `ℕ`-valued weight
space, so it is invisible to `formalCharacter` and violates `h_span`). The dimension
hypothesis (`_h_dim`) is retained for the consumer's interface and the historical
statement, but is not needed for the proof: `h_span` already pins `M` down.

Proof: `decompose_polynomial_gl_rep` (GL_N-equivariant complete reducibility) writes
`M.asModule` as a direct sum of abstract simples `L (f j)`, each with character a Schur
polynomial `schurPoly N (lam_cl (f j))` along an injective assignment `lam_cl`. Pushing
`formalCharacter` through the decomposition and matching against `S_λ`, linear independence
of the Schur polynomials (`schurPoly_linearIndependent`) forces a single summand whose
class is `λ`. The resulting simple `L (f 0)` is then identified with `L_λ` via the
highest-weight uniqueness `simpleRep_iso_schurModule_of_formalCharacter_eq`.

The downstream use is in `schurModule_shift_iso_detTwist` (Proposition 5.22.2). -/
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h : formalCharacter k N M = schurPoly N lam)
    (_h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)) :
    Nonempty (M ≅ SchurModule k N lam) := by
  classical
  set n := ∑ i, lam i with hn
  -- (1) `M` is homogeneous of degree `n`: any nonzero `ℕ`-weight space has `∑ μ = ∑ lam`.
  have h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n := by
    intro μ hμ
    have hpos : 0 < Module.finrank k (glWeightSpace k N M μ) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hμ)
    exact weight_magnitude_of_formalCharacter_eq_schurPoly k N lam M h μ hpos
  -- (2) Decompose `M.asModule` into abstract simples, schurPoly-classified.
  obtain ⟨ι, hιFin, hιDec, L, hLsimp, ⟨lam_cl, lam_inj, hchar⟩, p, f, ⟨eM⟩⟩ :=
    Etingof.PolynomialGLDecomposition.decompose_polynomial_gl_rep k N n M halg h_span h_homog
  -- (3) Character match: `S_λ = ∑_j schurPoly N (lam_cl (f j))`.
  have hφ : Representation.asModule M.ρ ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
      Representation.asModule (Representation.directSum (fun j : Fin p => (L (f j)).ρ)) :=
    eM ≪≫ₗ (Representation.asModule_directSum_equiv (fun j : Fin p => (L (f j)).ρ)).symm
  have hM_sum : formalCharacter k N M = ∑ j : Fin p, schurPoly N (lam_cl (f j)).val := by
    -- Push `formalCharacter` through the decomposition: bridge the `MonoidAlgebra`-linear
    -- `asModule` equivalence `hφ` to a `k`-linear GL-equivariant equivalence, then split
    -- the resulting direct sum and read off each Schur-polynomial character via `hchar`.
    have hchar_eq : formalCharacter k N M
        = formalCharacter k N
          (FDRep.of (Representation.directSum (fun j : Fin p => (L (f j)).ρ))) := by
      have h0 := formalCharacter_eq_of_rep_iso k N M.ρ
        (Representation.directSum (fun j : Fin p => (L (f j)).ρ))
        (Representation.kEquivOfAsModuleEquiv hφ)
        (fun g v => Representation.kEquivOfAsModuleEquiv_intertwines hφ g v)
      rwa [formalCharacter_FDRep_of_ρ] at h0
    rw [hchar_eq,
      formalCharacter_directSum k N (fun j : Fin p => (L (f j) : Type u))
        (fun j : Fin p => (L (f j)).ρ)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [formalCharacter_FDRep_of_ρ, hchar (f j)]
  have hrel : schurPoly N lam = ∑ j : Fin p, schurPoly N (lam_cl (f j)).val := by
    rw [← h, hM_sum]
  -- (4) Linear independence of Schur polynomials forces a single summand of class `λ`.
  have hsum_eq : Finsupp.single (⟨lam, hlam⟩ : {l : Fin N → ℕ // Antitone l}) (1 : ℚ)
      = ∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ) := by
    apply schurPoly_linearIndependent N
    rw [Finsupp.linearCombination_single, map_sum]
    simp only [Finsupp.linearCombination_single, one_smul]
    exact hrel
  -- The total coefficient mass: `1 = p`, hence `p = 1`.
  have hp1 : p = 1 := by
    have hmass := congrArg
      (Finsupp.linearCombination ℚ (fun _ : {l : Fin N → ℕ // Antitone l} => (1 : ℚ))) hsum_eq
    simp only [map_sum, Finsupp.linearCombination_single, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmass
    exact_mod_cast hmass.symm
  subst hp1
  -- The single class is `λ`.
  have hclass0 : lam_cl (f 0) = (⟨lam, hlam⟩ : {l : Fin N → ℕ // Antitone l}) := by
    rw [Fin.sum_univ_one] at hsum_eq
    exact (Finsupp.single_left_inj (by norm_num)).mp hsum_eq.symm
  -- (5) Collapse the `Fin 1` direct sum onto its single summand and rebuild the iso.
  let e_collapse :
      DirectSum (Fin 1) (fun j : Fin 1 => Representation.asModule (L (f j)).ρ)
        ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
          Representation.asModule (L (f 0)).ρ :=
    LinearEquiv.ofLinear
      (DirectSum.component (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (Fin 1)
        (fun j : Fin 1 => Representation.asModule (L (f j)).ρ) 0)
      (DirectSum.lof (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (Fin 1)
        (fun j : Fin 1 => Representation.asModule (L (f j)).ρ) 0)
      (by ext x; simp [DirectSum.component.lof_self])
      (by
        refine DirectSum.linearMap_ext
          (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (fun i => ?_)
        fin_cases i
        ext b
        simp [DirectSum.component.lof_self])
  have hφ' : Representation.asModule M.ρ
      ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (L (f 0)).ρ :=
    eM ≪≫ₗ e_collapse
  -- `M ≅ L (f 0)` as `GL_N`-representations.
  have hML : Nonempty (M ≅ L (f 0)) :=
    ⟨Action.mkIso (Representation.kEquivOfAsModuleEquiv hφ').toFGModuleCatIso (fun g => by
      ext x
      exact Representation.kEquivOfAsModuleEquiv_intertwines hφ' g x)⟩
  -- `L (f 0) ≅ L_λ` by highest-weight uniqueness.
  have hchar0 : formalCharacter k N (L (f 0)) = schurPoly N lam := by
    rw [hchar (f 0), hclass0]
  have hLS : Nonempty (L (f 0) ≅ SchurModule k N lam) :=
    simpleRep_iso_schurModule_of_formalCharacter_eq k N lam hlam (L (f 0)) (hLsimp (f 0)) hchar0
  obtain ⟨isoML⟩ := hML
  obtain ⟨isoLS⟩ := hLS
  exact ⟨isoML ≪≫ isoLS⟩

end Etingof
