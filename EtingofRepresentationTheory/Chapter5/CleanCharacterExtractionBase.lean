import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.SchurModuleSimple
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace
import EtingofRepresentationTheory.Chapter5.CharacterIndependence
import EtingofRepresentationTheory.Chapter5.TraceVanishingDensity
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic

/-!
# DetInvElim-clean base for constituent-character extraction (issue #5075)

This file is the **DetInvElim-clean** home of the reusable glue and the two character
ingredients underlying the constituent-character extraction step of the `#4905`/`#4896`
part-(a) assembly. They previously lived in `SchurWeylFormalCharacterIso.lean`, which is
*polluted* — it transitively imports `DetInvElim` via `PolynomialGLDecomposition`. Because
the `#4896` assembly (`KernelLemmaKPrimeAssembly`) feeds back into `DetInvElim`, using the
polluted extractor to prove part-(a) is a genuine build cycle (#5072). The proofs here use
**only** DetInvElim-clean dependencies (`FormalCharacterIso`, `SchurModuleSimple`,
`CharacterIndependence`, `TraceVanishingDensity`, `FormalCharacterTorusTrace`,
`GLRepAlgebraic`), so the clean extractor built on top (`CleanConstituentExtraction.lean`)
avoids the cycle.

The five relocated items (identical statements and proofs to the former
`SchurWeylFormalCharacterIso` versions):

* `Representation.kEquivOfAsModuleEquiv` / `_intertwines` — the reverse glue extracting the
  `k`-linear `GL`-equivariant equivalence underlying a `MonoidAlgebra`-linear equivalence of
  `asModule`s.
* `Etingof.formalCharacter_FDRep_of_ρ` — rebuilding `M` as `FDRep.of M.ρ` does not change its
  character.
* `Etingof.schurModule_isSimple_general` — general-`k` Schur-module simplicity (#4946, #5054).
* `Etingof.formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general` — the
  general-`k` torus→full-group Zariski-density character-independence seam (#4947, #4983).

`SchurWeylFormalCharacterIso.lean` now `import`s this file and re-exports these names, so its
own downstream theorems are unchanged.
-/

open CategoryTheory MvPolynomial

noncomputable section

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

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- The formal character only depends on the underlying representation: rebuilding
`M` as `FDRep.of M.ρ` does not change its character. -/
theorem formalCharacter_FDRep_of_ρ (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    formalCharacter k N (FDRep.of M.ρ) = formalCharacter k N M :=
  formalCharacter_eq_of_rep_iso k N M.ρ M.ρ (LinearEquiv.refl k M) (fun _ _ => rfl)

/-- **Ingredient (a): general-`k` Schur-module simplicity (issue #4946, #5054).**
The Schur module `L_λ = SchurModule k N lam` is a simple
`MonoidAlgebra k (GL_N(k))`-module for any antitone `lam`.

The centralizer-level core is proved over a general algebraically-closed
characteristic-zero field as `schurModuleSubmodule_isSimple_centralizer_general`
(`SchurModuleSimple.lean`), and the `hN : (∑ i, lam i) ≤ N` guard is **not** needed.
This assembly is a one-line mirror of the ℂ `schurModule_isSimple` final
assembly: `schurModuleSubmodule_isSimple_centralizer_general` + the generic GL transfer
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`. -/
theorem schurModule_isSimple_general (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (SchurModule k N lam).ρ) := by
  -- One-line mirror of the ℂ `schurModule_isSimple` assembly, driven by the
  -- general-`k` centralizer core (`SchurModuleSimple.lean`). No `hN` guard needed.
  haveI := schurModuleSubmodule_isSimple_centralizer_general (k := k) N lam hlam
  refine isSimpleModule_monoidAlgebra_GL_of_centralizer_simple k
    (N := N) (n := ∑ i, lam i)
    (M := ↥(SchurModuleSubmodule k N lam))
    (schurModuleRep k N lam) ?_
  intro g x
  apply Subtype.ext
  rfl

/-- **Ingredient (b): general-`k` torus→full-group character independence (issue #4947,
algebraicity bridge #4983).** For a finite family of pairwise non-isomorphic simple
**algebraic** `GL_N(k)`-representations `L i`, a `ℚ`-combination `c` of their characters
whose corresponding combination of *torus* traces vanishes at every diagonal torus element
has all coefficients zero.

This is the general algebraically-closed characteristic-zero `k` analogue of the ℂ
seam `formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero` (#4908): same proof
(Dedekind/Artin independence of characters + the Zariski-density bridge), now driven by the
general-`k` density core `trace_combination_vanishes_of_torus_vanishes_of_algebraic`
(`TraceVanishingDensity.lean`). -/
theorem formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general
    (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLalg : ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ)
    (hLsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
    (c : ι → ℚ)
    (htorus : ∀ t : Fin N → kˣ,
        ∑ i, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (diagTorus k N t)) = 0) :
    ∀ i, c i = 0 := by
  classical
  -- (a) Pairwise non-isomorphic as `A := MonoidAlgebra k (GL_N k)`-modules.
  have hdist : Pairwise (fun i j => ¬ Nonempty (Representation.asModule (L i).ρ
      ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (L j).ρ)) := by
    intro i j hij hcon
    obtain ⟨φ⟩ := hcon
    exact hLdist hij ⟨Action.mkIso (Representation.kEquivOfAsModuleEquiv φ).toFGModuleCatIso
      (fun g => by ext x; exact Representation.kEquivOfAsModuleEquiv_intertwines φ g x)⟩
  -- (b) Dedekind/Artin: the trace functionals are `k`-independent.
  have hLI := traceCharacter_linearIndependent (𝕜 := k)
    (A := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
    (fun i => Representation.asModule (L i).ρ) hLsimp hdist
  -- (c) Trace functional at a group element evaluates to the representation trace.
  have hbridge : ∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k),
      traceChar (fun i => Representation.asModule (L i).ρ) i (MonoidAlgebra.of k _ g)
        = LinearMap.trace k (L i) ((L i).ρ g) := by
    intro i g
    have hmap : (repEnd (fun i => Representation.asModule (L i).ρ) i
        (MonoidAlgebra.of k _ g) :
          Representation.asModule (L i).ρ →ₗ[k] Representation.asModule (L i).ρ)
          = (L i).ρ g := by
      ext v
      rw [repEnd_apply, ← Representation.asAlgebraHom_of (L i).ρ g]
      rfl
    rw [traceChar_apply, hmap]
    rfl
  -- (d) The functional combination vanishes on every group element by the density core.
  have hF0 : ∀ a, (∑ i, (c i : k) • (traceChar (fun i => Representation.asModule (L i).ρ) i :
      MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k) →ₗ[k] k)) a = 0 := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
        have hg0 := trace_combination_vanishes_of_torus_vanishes_of_algebraic N L hLalg
          (fun i => (c i : k)) htorus g
        rw [LinearMap.sum_apply]
        simpa only [LinearMap.smul_apply, hbridge] using hg0
    | hadd x y hx hy => simp only [map_add, hx, hy, add_zero]
    | hsmul r x hx => simp only [map_smul, hx, smul_zero]
  have hfun : (∑ i, (c i : k) • (traceChar (fun i => Representation.asModule (L i).ρ) i :
      MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k) →ₗ[k] k)) = 0 :=
    LinearMap.ext hF0
  -- (e) Independence forces every coefficient to vanish.
  intro i
  have : (c i : k) = 0 := Fintype.linearIndependent_iff.mp hLI (fun i => (c i : k)) hfun i
  exact_mod_cast this

end Etingof

end
