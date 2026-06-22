import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification
import EtingofRepresentationTheory.Chapter5.SchurModuleSimple
import EtingofRepresentationTheory.Chapter5.SemisimpleIsotypic
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace
import EtingofRepresentationTheory.Chapter5.CharacterIndependence
import EtingofRepresentationTheory.Chapter5.TraceVanishingDensity
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic

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

The iso-strength highest-weight uniqueness `simpleRep_iso_schurModule_of_formalCharacter_eq`
(this file) — "a simple polynomial `GL_N`-rep with character `S_λ` is `L_λ`", the natural
strengthening of `schurWeyl_simples_formalCharacter_classification_core` (#4721, which only
classifies characters) — is itself now **sorry-free in its own proof** (route B, #4901). It
takes the polynomiality (weight saturation) of `L` as a hypothesis `hLtop` and its algebraicity
as `hLalg`, and runs the two-element-family `{L, L_λ}` character-independence argument, reducing
to two isolated, genuinely-deep ingredients:

* (a) `schurModule_isSimple_general` — general-`k` Schur-module simplicity (#4946, #5054);
* (b) `formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general` — the general-`k`
  torus→full-group Zariski-density character-independence seam (#4947, shares the density core
  with the ℂ seam #4908). **Now sorry-free** (algebraicity bridge #4983): it takes algebraicity
  of each `L i` as a hypothesis (matching the ℂ seam), supplied at the call sites from the
  polynomial source via `schurModule_isAlgebraic` and `IsAlgebraicRepresentation.of_linearEquiv`.

There is no third "weight saturation from character" ingredient: the original (c)
`glWeightSpace_top_of_simple_formalCharacter_eq_schurPoly` was **false** (`formalCharacter`
does not see non-`ℕ` weights, so it cannot certify polynomiality of a simple — counterexample
`det⁻¹ ⊗ Sym³(std)` at `N = 2`) and is retired (#4969). Both polynomiality (`hLtop`) and
algebraicity (`hLalg`) are instead threaded as hypotheses and discharged at the real caller
`iso_of_formalCharacter_eq_schurPoly`, where the simple summand `L (f 0)` is the equivariant
image of the polynomial, algebraic `M`; the `L_λ`-side uses the true
`glWeightSpace_schurModule_iSup_eq_top` and `schurModule_isAlgebraic`. Weight saturation rests
on the elementary `glWeightSpace_iSup_eq_top_of_equivariant_surjective`, algebraicity on the
analogous `IsAlgebraicRepresentation.of_linearEquiv`.

The classification crux (#4721) and pairwise distinctness (#4731), reached through
`decompose_polynomial_gl_rep`, are consumed transitively by the assembly below.

The reusable glue `Representation.kEquivOfAsModuleEquiv` (the reverse of
`asModuleEquivOfIntertwiner`) bridges the module-level `≃ₗ[MonoidAlgebra]` output of the
decomposition to a `k`-linear GL-equivariant equivalence, feeding both the character
computation (via `formalCharacter_eq_of_rep_iso`) and the categorical iso (via
`Action.mkIso`). The character half is packaged below as
`formalCharacter_eq_of_asModule_linearEquiv` (relocated from the former leaf file
`SchurWeylSimplesClassificationComplex` in #5023, alongside the general-`k`
highest-weight classification core).
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct

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

omit [CharZero k] in
/-- **Weight saturation transfers along equivariant surjections.** A `GL_N`-equivariant
surjection `φ : M → P` sends each `ℕ`-weight vector of `M` to an `ℕ`-weight vector of `P`
of the same weight (equivariance commutes `φ` past the torus action), so the image of a
weight space lands in the matching weight space. Hence if the `ℕ`-weight spaces of `M`
span all of `M`, those of `P` span all of `P`.

(`omit [CharZero k]`: the statement and proof never use it.)

This is the single elementary fact behind both polynomiality facts the highest-weight
uniqueness assembly needs: the Schur module is the equivariant image of the tensor power
(below), and a direct summand of a polynomial representation is its equivariant image. -/
theorem glWeightSpace_iSup_eq_top_of_equivariant_surjective (N : ℕ)
    (M P : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (φ : M →ₗ[k] P)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M), φ (M.ρ g v) = P.ρ g (φ v))
    (hsurj : Function.Surjective φ)
    (hM : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N P (fun i => μ i) = ⊤ := by
  have hmap : ∀ μ : Fin N →₀ ℕ,
      Submodule.map φ (glWeightSpace k N M (fun i => μ i))
        ≤ glWeightSpace k N P (fun i => μ i) := by
    intro μ
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    simp only [Submodule.mem_comap, glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
    intro i t
    rw [← hφ, hv i t, map_smul]
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hsurj, ← Submodule.map_top, ← hM,
    Submodule.map_iSup]
  exact iSup_mono hmap

/-- **The `ℕ`-weight spaces of the Schur module span.** `L_λ = SchurModule k N lam` is the
equivariant image of the tensor power `V^{⊗n}` under (the corestriction of) the Young
symmetrizer (`glTensor_comm_youngSym`), and the tensor power's `ℕ`-weight spaces span
(`glTensorRep_iSup_glWeightSpace_eq_top`), so weight saturation transfers via
`glWeightSpace_iSup_eq_top_of_equivariant_surjective`. -/
theorem glWeightSpace_schurModule_iSup_eq_top (N : ℕ) (lam : Fin N → ℕ) :
    ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (SchurModule k N lam) (fun i => μ i) = ⊤ := by
  refine glWeightSpace_iSup_eq_top_of_equivariant_surjective k N
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

/-- **Ingredient (a): general-`k` Schur-module simplicity (issue #4946, #5054).**
The Schur module `L_λ = SchurModule k N lam` is a simple
`MonoidAlgebra k (GL_N(k))`-module for any antitone `lam`.

The centralizer-level core is proved over a general algebraically-closed
characteristic-zero field as `schurModuleSubmodule_isSimple_centralizer_general`
(`SchurModuleSimple.lean`), and the `hN : (∑ i, lam i) ≤ N` guard is **not** needed.
This assembly is a one-line mirror of the ℂ `schurModule_isSimple` final
assembly: `schurModuleSubmodule_isSimple_centralizer_general` + the generic GL transfer
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`.

**Universe note:** that general-`k` core lives in `Type` (universe `0`). It factors
through the general-`k` Specht classification
(`Theorem5_12_2_classification_general` → `IrrepDecomp k (Equiv.Perm (Fin n))`), and
Mathlib's `Rep`/`FDRep` pin field and group to one common universe; since
`S_n = Equiv.Perm (Fin n)` is `Type 0`, the whole Schur-Weyl/Specht core is intrinsically
`Type 0`. Consuming the proof therefore forces the entire simplicity-dependent chain in
this file (this theorem, `schurWeyl_simples_isotypic_matching_general`,
`schurWeyl_simples_formalCharacter_classification_core_general`,
`simpleRep_iso_schurModule_of_formalCharacter_eq`, `iso_of_formalCharacter_eq_schurPoly`)
and its external consumers across Ch 5/6/9 down to `Type 0`; the section variable here is
accordingly `k : Type` (#5054). -/
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
(Dedekind/Artin
independence of characters + the Zariski-density bridge), now driven by the general-`k`
density core `trace_combination_vanishes_of_torus_vanishes_of_algebraic`
(`TraceVanishingDensity.lean`). The `ℂ` seam is the `k = ℂ` specialisation.

The hypothesis is `hLalg` (regularity of each character), **not** `hLtop` (spanning
`ℕ`-weight spaces): the density step requires the character combination to be a *regular*
function, which `hLtop` does not provide for an abstract-group representation. This matches
the ℂ seam exactly. At the genuine call site (`simpleRep_iso_schurModule_of_formalCharacter_eq`
below) each `L i` is supplied from its polynomial source — the Schur module via
`schurModule_isAlgebraic`, the abstract simple via `IsAlgebraicRepresentation.of_linearEquiv`
transport from the algebraic ambient rep — rather than manufactured from `hLtop` alone
(which would be strictly stronger, hence false; see #4983). -/
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

/-- **Numerical identity for the Schur-Weyl decomposition (sorry-free).**

For any equivariant decomposition `e : V^{⊗n} ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ` of `V = Fin N → k`
(`n ≤ N`), the multiplicity-weighted sum of the abstract characters equals the
Specht-weighted sum of Schur polynomials:
`∑ᵢ dim(Sᵢ)·char(Lᵢ) = ∑_λ dim_ℂ(Specht_λ)·schurPoly N λ`,
where `λ` ranges over `BoundedPartition N n` (antitone weights of degree `n`,
length `≤ N`).

This is the field-independent numerical input to the highest-weight classification:
the left side comes from the abstract decomposition, the right side from
`(∑ Xᵢ)^n = ∑_λ dim(Specht_λ)·schurPoly λ`. It does **not** by itself pin each
`char(Lᵢ)` to a single Schur polynomial — that requires the isotypic geometry. -/
theorem schurWeyl_decomposition_numerical_identity
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v)) :
    ∑ i : ι, (Module.finrank k (S i) : ℚ) • formalCharacter k N (L i) =
      ∑ lam : BoundedPartition N n,
        (Module.finrank ℂ (SpechtModule n
          (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) •
        schurPoly N lam.parts := by
  have h1 : formalCharacter k N (FDRep.of (glTensorRep k N n)) =
      ∑ i : ι, (Module.finrank k (S i) : ℚ) • formalCharacter k N (L i) := by
    rw [formalCharacter_eq_of_rep_iso k N (glTensorRep k N n)
        (Representation.directSum (fun i =>
          (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
            (S i)).tprod (L i).ρ)) e he,
      formalCharacter_directSum]
    exact Finset.sum_congr rfl (fun i _ => formalCharacter_trivialTensor k N (S i) (L i))
  rw [← h1, formalCharacter_glTensorRep_eq_pow, sum_X_pow_eq_sum_finrank_smul_schurPoly]

/-- **`R`-linear flattening of the Schur-Weyl decomposition (sorry-free `def`).**

For any equivariant decomposition `e : V^{⊗n} ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ`, the `asModule` of
`glTensorRep` is `MonoidAlgebra k GL_N`-linearly the direct sum, over
`ν : Σ i, Fin (dim Sᵢ)`, of copies of the simple modules `asModule (L ν.1).ρ`.

Each `Sᵢ ⊗ Lᵢ` (with `Sᵢ` carrying the trivial action) splits, via a basis of
`Sᵢ`, into `dim Sᵢ` copies of `Lᵢ`; assembling these over `i` and flattening the
`Σ` gives the stated isotypic form. This is the extraction of the `Einner`
construction of `polynomial_homog_rep_asModule_embeds_directSum_simple`
(`PolynomialGLDecomposition.lean`) for arbitrary decomposition data, packaging the
ambient `V^{⊗n}` as a finite direct sum of simple `R`-modules — the input shape
required by `SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum`. -/
noncomputable def schurWeyl_decomposition_asModule_flatten
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v)) :
    Representation.asModule (glTensorRep k N n) ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)]
      DirectSum (Σ i : ι, Fin (Module.finrank k (S i)))
        (fun ν => Representation.asModule (L ν.1).ρ) :=
  (Representation.asModuleEquivOfIntertwiner e he) ≪≫ₗ
    (Representation.asModule_directSum_equiv
      (fun i => (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (S i)).tprod (L i).ρ)) ≪≫ₗ
    (DFinsupp.mapRange.linearEquiv (fun i =>
      Representation.asModule_trivial_tprod_equiv (Module.finBasis k (S i)) (L i).ρ)) ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (R := MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k))
      (δ := fun (i : ι) (_ : Fin (Module.finrank k (S i))) =>
        Representation.asModule (L i).ρ)).symm

/-- **Equal formal characters from a `MonoidAlgebra`-linear `asModule` equivalence
(sorry-free).** A `MonoidAlgebra k GL_N`-linear equivalence between the `asModule`s
of two representations `ρ`, `σ` produces equal formal characters.

The `R`-linear `Φ` is upgraded to a `GL_N`-equivariant `k`-linear equivalence
`ek := σ.asModuleEquiv ∘ Φ ∘ ρ.asModuleEquiv.symm`; equivariance follows from
`asModuleEquiv_symm_map_rho` (turning `ρ g` into the `of g` action), `Φ`'s
`R`-linearity, and `asModuleEquiv_map_smul` / `asAlgebraHom_of` (turning the `of g`
action back into `σ g`). Then `formalCharacter_eq_of_rep_iso` applies. -/
theorem formalCharacter_eq_of_asModule_linearEquiv
    (k : Type) [Field k] [IsAlgClosed k] (N : ℕ)
    {V W : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (Φ : Representation.asModule ρ ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)] Representation.asModule σ) :
    formalCharacter k N (FDRep.of ρ) = formalCharacter k N (FDRep.of σ) := by
  set ek : V ≃ₗ[k] W :=
    ρ.asModuleEquiv.symm ≪≫ₗ Φ.restrictScalars k ≪≫ₗ σ.asModuleEquiv with hek
  refine formalCharacter_eq_of_rep_iso k N ρ σ ek ?_
  intro g v
  simp only [hek, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

open DirectSum in
/-- **A simple module embedding into a finite direct sum of simple modules is
isomorphic to one of the summands (sorry-free).**

If `W ≃ₗ[R] ⨁_κ Lsum` with each `Lsum c` simple and `T` is a simple `R`-module
with an injective `R`-linear map into `W`, then `T ≃ₗ[R] Lsum c` for some `c`.

This is the simple-module specialization of the isotypic-extraction step: `T`
transports to a simple submodule `T'` of `⨁_κ Lsum`, which lies in the supremum
of the (simple) coordinate lines, so `Submodule.linearEquiv_of_le_sSup` matches it
to one line `range (lof c) ≅ Lsum c`. -/
theorem simpleModule_iso_component_of_embeds
    {R : Type*} [Ring R] {W : Type*} [AddCommGroup W] [Module R W]
    {κ : Type*} [Finite κ] (Lsum : κ → Type*)
    [∀ c, AddCommGroup (Lsum c)] [∀ c, Module R (Lsum c)]
    (hsimp : ∀ c, IsSimpleModule R (Lsum c))
    (eW : W ≃ₗ[R] DirectSum κ Lsum)
    {T : Type*} [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    (incl : T →ₗ[R] W) (hincl : Function.Injective incl) :
    ∃ c, Nonempty (T ≃ₗ[R] Lsum c) := by
  classical
  -- Realize `T` as a simple submodule `T'` of the direct sum.
  set f : T →ₗ[R] DirectSum κ Lsum := eW.toLinearMap ∘ₗ incl with hf
  have hfinj : Function.Injective f := eW.injective.comp hincl
  set T' : Submodule R (DirectSum κ Lsum) := LinearMap.range f with hT'
  have eTT' : T ≃ₗ[R] T' := LinearEquiv.ofInjective f hfinj
  haveI : IsSimpleModule R T' := (LinearEquiv.isSimpleModule_iff eTT').mp ‹_›
  -- The coordinate lines `range (lof c)`, each simple, spanning the whole sum.
  set cs : Set (Submodule R (DirectSum κ Lsum)) :=
    Set.range (fun c => LinearMap.range (DirectSum.lof R κ Lsum c)) with hcs
  have hlof_inj : ∀ c, Function.Injective (DirectSum.lof R κ Lsum c) := fun c =>
    Function.LeftInverse.injective (g := DirectSum.component R κ Lsum c)
      (fun b => DirectSum.component.lof_self R c b)
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (DirectSum κ Lsum)) := by
    rintro ⟨m, c, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj c)).symm
  haveI := hcs_simple
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]; exact DFinsupp.iSup_range_lsingle
  have hTle : T' ≤ sSup cs := by rw [hcs_top]; exact le_top
  obtain ⟨m, hm, ⟨e'⟩⟩ := T'.linearEquiv_of_le_sSup cs hTle
  obtain ⟨c, rfl⟩ := hm
  exact ⟨c, ⟨eTT'.trans (e'.trans (LinearEquiv.ofInjective _ (hlof_inj c)).symm)⟩⟩

/-- **Isotypic matching half of the classification (general `k`, sorry-free modulo #4946).**

Given the equivariant decomposition data of `V^{⊗n}` (`V = Fin N → k`, `n ≤ N`),
there is an *injective* assignment `φ : BoundedPartition N n → ι` such that
`char(L (φ λ)) = schurPoly N λ.parts` for every antitone partition `λ` of `n`
(length `≤ N`).

For each such `λ`, `SchurModule k N λ.parts` is a simple `GL_N(k)`-module
(`schurModule_isSimple_general`) sitting inside `V^{⊗n}` as the submodule
`SchurModuleSubmodule`; transporting it through the `R`-linear flattening
(`schurWeyl_decomposition_asModule_flatten`) and matching it to a single simple
component (`simpleModule_iso_component_of_embeds`) yields `SchurModule k N λ.parts
≅ L (φ λ)`, hence `char(L (φ λ)) = char(SchurModule k N λ.parts) = schurPoly N
λ.parts` (`formalCharacter_eq_of_asModule_linearEquiv`,
`formalCharacter_schurModule_eq_schurPoly`). Injectivity of `φ` follows from
`schurPoly_injective`.

This is steps 1–2,4 of route 1; the surjectivity `|ι| = |P|` (the counting step)
is the remaining content of `schurWeyl_simples_formalCharacter_classification_core_complex`. -/
theorem schurWeyl_simples_isotypic_matching_general
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)) :
    ∃ φ : BoundedPartition N n → ι,
      Function.Injective φ ∧
      ∀ lam : BoundedPartition N n,
        formalCharacter k N (L (φ lam)) = schurPoly N lam.parts := by
  classical
  -- Per-partition matching: each Schur module is isomorphic to a single `L i`.
  have hmatch : ∀ lam : BoundedPartition N n,
      ∃ i : ι, formalCharacter k N (L i) = schurPoly N lam.parts := by
    rintro ⟨parts, hdecr, hsum⟩
    subst hsum
    -- Inclusion `SchurModuleSubmodule ↪ V^{⊗(∑parts)}` intertwines the two actions.
    have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
        (x : SchurModuleSubmodule k N parts),
        (SchurModuleSubmodule k N parts).subtype (schurModuleRep k N parts g x)
          = glTensorRep k N (∑ i, parts i) g
              ((SchurModuleSubmodule k N parts).subtype x) := by
      intro g x
      rfl
    -- `R`-linear injection of the simple Schur module into `V^{⊗n}`.
    haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (schurModuleRep k N parts)) :=
      schurModule_isSimple_general k N parts hdecr
    obtain ⟨ν, ⟨Φ⟩⟩ := simpleModule_iso_component_of_embeds
      (Lsum := fun ν : Σ i : ι, Fin (Module.finrank k (S i)) =>
        Representation.asModule (L ν.1).ρ)
      (fun ν => hLsimp ν.1)
      (schurWeyl_decomposition_asModule_flatten k N (∑ i, parts i) L e he)
      (Representation.asModuleHomOfIntertwiner
        (SchurModuleSubmodule k N parts).subtype hinter)
      (by
        intro a b hab
        exact Subtype.coe_injective hab)
    refine ⟨ν.1, ?_⟩
    have hchar := formalCharacter_eq_of_asModule_linearEquiv k N
      (schurModuleRep k N parts) (L ν.1).ρ Φ
    have hbridge : formalCharacter k N (FDRep.of (L ν.1).ρ) = formalCharacter k N (L ν.1) := rfl
    have hschur : formalCharacter k N (FDRep.of (schurModuleRep k N parts))
        = schurPoly N parts := formalCharacter_schurModule_eq_schurPoly k N parts hdecr
    rw [hbridge, hschur] at hchar
    exact hchar.symm
  -- Skolemize to a function and prove injectivity via `schurPoly_injective`.
  choose φ hφ using hmatch
  refine ⟨φ, ?_, hφ⟩
  intro lam lam' heq
  have h1 : schurPoly N lam.parts = schurPoly N lam'.parts := by
    rw [← hφ lam, ← hφ lam', heq]
  have h2 : lam.parts = lam'.parts :=
    schurPoly_injective N _ _ lam.decreasing lam'.decreasing h1
  obtain ⟨p, d, s⟩ := lam
  obtain ⟨p', d', s'⟩ := lam'
  obtain rfl : p = p' := h2
  rfl

/-- **Linear independence of the Schur-Weyl simple characters (sub-issue of #4870 /
#4887).**

The formal characters of the pairwise non-isomorphic simple *polynomial* summands
`L i` of `V^{⊗n}` (`V = Fin N → k`, `n ≤ N`) produced by the equivariant
decomposition are `ℚ`-linearly independent.

This is the classical fact "characters of pairwise non-isomorphic irreducible
representations are linearly independent" (Dedekind/Artin independence of
characters, specialised to the formal `GL_N` character). It is the genuine
remaining content of the counting step `|ι| = |P|`: combined with the numerical
identity `schurWeyl_decomposition_numerical_identity` and the injective isotypic
matching `φ`, it forces every abstract simple `L i` to be a Schur module, i.e.
`φ` surjective (see `schurWeyl_simples_formalCharacter_classification_core_general`).

**Spec resolution (#4887, option C-a).** As stated originally (only `hLsimp`,
`hLdist`) the statement is **false**: a "ghost" index whose abstract simple `L i` is
not algebraic can have `formalCharacter k N (L i) = 0` (empty weight-space
decomposition), and two such ghosts make the family linearly dependent. The fix is
to thread both the weight-space-spanning hypothesis `hLtop` (feeding the torus-trace
connection `Etingof.trace_combination_eq_zero_of_formalCharacter_combination_eq_zero`)
and the algebraicity hypothesis `hLalg`. At the genuine call site each `L i` is a
summand of the polynomial representation `V^{⊗n}`, hence both spanning
(`schurWeyl_simple_summand_glWeightSpace_top`) and algebraic
(`schurWeyl_simple_summand_isAlgebraic`).

**Important — not circular.** The *existing*
`glTensorRep_schurWeyl_simples_formalCharacter_linearIndependent`
(`SchurWeylSimplesClassification.lean`) derives the same conclusion, but *through*
the still-sorried highest-weight classification core; using it here would make the
classification depend on the very sorry it is meant to discharge. This lemma is
instead proved **directly** from `hLtop`/`hLalg`/`hLsimp`/`hLdist` (character
independence), independently of the classification.

The assembly here is `sorry`-free; it reduces to the isolated general-`k` seam lemma
`formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general`
(#4947) via the torus-trace connection (B). -/
theorem schurWeyl_simples_formalCharacter_linearIndependent_general
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLtop : ∀ i, ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (L i) (fun j => μ j) = ⊤)
    (hLalg : ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ)
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j)))) :
    LinearIndependent ℚ (fun i => formalCharacter k N (L i)) := by
  -- Reduce to coefficient-vanishing for an arbitrary vanishing ℚ-combination.
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Sub-issue (B): the relation `∑ cᵢ • char(Lᵢ) = 0` forces the corresponding
  -- combination of torus traces to vanish at every diagonal torus element.
  have htorus : ∀ t : Fin N → kˣ,
      ∑ i, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (diagTorus k N t)) = 0 := by
    intro t
    have h := trace_combination_eq_zero_of_formalCharacter_combination_eq_zero
      k N Finset.univ c L (fun i _ => hLtop i) (by simpa using hc) t
    simpa using h
  -- The seam (#4947): torus-trace vanishing ⟹ every coefficient vanishes (general `k`,
  -- driven by the algebraicity of each summand `hLalg`).
  exact formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general
    k N L hLalg hLsimp hLdist c htorus

/-- A `GL_N(k)`-equivariant `k`-linear map sends the `μ`-weight space of its source
into the `μ`-weight space of its target: weight vectors map to weight vectors. -/
private theorem glWeightSpace_map_le_of_equivariant
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] (W : Type))
    (hf : ∀ g v, f (ρV g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (glWeightSpace k N (FDRep.of ρV) μ).map f ≤ glWeightSpace k N W μ := by
  intro w hw
  rw [Submodule.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, FDRep.of_ρ',
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  intro a t
  have hvit : ρV (diagUnit k N a t) v = (↑t : k) ^ μ a • v := sub_eq_zero.mp (hv a t)
  have hwit : W.ρ (diagUnit k N a t) (f v) = (↑t : k) ^ μ a • f v := by
    rw [← hf, hvit, map_smul]
  rw [sub_eq_zero]; exact hwit

/-- **Spanning weight spaces of the simple summands (sub-issue #4909 of #4887).**

Each simple summand `L i` of `V^{⊗n}` (`V = Fin N → k`) carrying a nonzero
multiplicity space (`0 < dim(S i)`) is a *polynomial* representation: its weight
spaces span. This supplies the `hLtop` hypothesis of
`schurWeyl_simples_formalCharacter_linearIndependent_complex` at the call site from
the equivariant decomposition data.

Proof: pick a basis vector `s = b i0` of `S i` (exists since `dim(S i) > 0`) and the
dual coordinate `φ = b.coord i0`, so `φ s = 1`. These build a `GL_N(k)`-equivariant
*surjection* `q : V^{⊗n} → L i`, namely `v ↦ φ ((e v)ᵢ.1) • (e v)ᵢ.2` — project `e v`
to the `i`-th summand `S i ⊗ L i` and evaluate the `S i`-factor against `φ`
(equivariance from `he` and the trivial `S i`-action; surjectivity since
`q (e⁻¹ (of i (s ⊗ x))) = x`). The full tensor power has spanning weight spaces
(`glTensorRep_iSup_glWeightSpace_eq_top`), and an equivariant map sends weight vectors
to weight vectors (`glWeightSpace_map_le_of_equivariant`), so
`⊤ = q ⊤ = q (⨆_μ wtₘ V^{⊗n}) = ⨆_μ q (wtₘ V^{⊗n}) ≤ ⨆_μ wtₘ (L i)`.

Note: this routes through the *polynomial* embedding into `glTensorRep`, not through a
general "algebraic ⟹ spanning ℕ-weight spaces" lemma, which is false (det⁻¹ twists are
algebraic but carry negative weights). -/
theorem schurWeyl_simple_summand_glWeightSpace_top
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∀ i, ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (L i) (fun j => μ j) = ⊤ := by
  classical
  intro i
  -- A nonzero functional `φ : S i → k` with `φ (b i0) = 1` (exists since `dim (S i) > 0`).
  let b : Module.Basis (Fin (Module.finrank k (S i))) k (S i) := Module.finBasis k (S i)
  let i0 : Fin (Module.finrank k (S i)) := ⟨0, hSne i⟩
  let φ : (S i) →ₗ[k] k := b.coord i0
  have hφ : φ (b i0) = 1 := by
    show b.coord i0 (b i0) = 1
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  -- The "evaluate the `S i`-factor against `φ`" map `r : S i ⊗ L i → L i`, `a ⊗ x ↦ φ a • x`.
  let r : (S i ⊗[k] (L i : Type)) →ₗ[k] (L i : Type) :=
    (TensorProduct.lid k (L i : Type)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type)), r (a ⊗ₜ x) = φ a • x := by
    intro a x
    simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  -- `r` is `GL_N`-equivariant for `(trivial ⊗ ρ_{L i})` and `ρ_{L i}` (trivial action on `S i`).
  have hr_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (y : S i ⊗[k] (L i : Type)),
      r (((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
            (L i).ρ) g y) = (L i).ρ g (r y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        simp only [Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.trivial_apply, hr_tmul, map_smul]
    | add y z hy hz => simp only [map_add, hy, hz]
  -- The equivariant surjection `q : V^{⊗n} → L i`: project `e` to the `i`-th summand, eval `φ`.
  let q : TensorPower k (Fin N → k) n →ₗ[k] (L i : Type) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ (e.toLinearMap)
  -- Coordinate formula for the direct-sum representation.
  have coord : ∀ (x : DirectSum ι (fun j => S j ⊗[k] (L j : Type)))
      (g : Matrix.GeneralLinearGroup (Fin N) k),
      DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i
          (Representation.directSum (fun j =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (S j)).tprod (L j).ρ) g x)
        = ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
            (L i).ρ) g
            (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i x) := by
    intro x g
    change (DirectSum.lmap (fun m =>
      ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S m)).tprod
        (L m).ρ) g) x) i
      = ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
          (L i).ρ) g (x i)
    rw [DirectSum.lmap_apply]
  -- `q` is `GL_N`-equivariant for `glTensorRep` and `ρ_{L i}`.
  have hq : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (v : TensorPower k (Fin N → k) n),
      q (glTensorRep k N n g v) = (L i).ρ g (q v) := by
    intro g v
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [he, coord, hr_equiv]
  -- `q` is surjective: `e.symm (of i (b i0 ⊗ x))` is a preimage of `x`.
  have hsurj : Function.Surjective q := by
    intro x
    refine ⟨e.symm (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i (b i0 ⊗ₜ x)), ?_⟩
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]
    rw [hr_tmul, hφ, one_smul]
  -- Assemble: `⊤ = q ⊤ = q (⨆ wt sp of V^{⊗n}) = ⨆ q(wt sp) ≤ ⨆ wt sp of L i`.
  have hmap_top : Submodule.map q ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  refine le_antisymm le_top ?_
  calc (⊤ : Submodule k (L i : Type))
      = Submodule.map q ⊤ := hmap_top.symm
    _ = Submodule.map q (⨆ μ : Fin N →₀ ℕ,
          glWeightSpace k N (FDRep.of (glTensorRep k N n)) (fun j => μ j)) := by
          rw [glTensorRep_iSup_glWeightSpace_eq_top]
    _ = ⨆ μ : Fin N →₀ ℕ, Submodule.map q
          (glWeightSpace k N (FDRep.of (glTensorRep k N n)) (fun j => μ j)) :=
          Submodule.map_iSup _ _
    _ ≤ ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (L i) (fun j => μ j) :=
          iSup_mono fun μ =>
            glWeightSpace_map_le_of_equivariant N (glTensorRep k N n) (L i) q hq (fun j => μ j)

/-- **Algebraicity transfers across an equivariant linear equivalence.** If `φ : Y ≃ₗ Y'`
intertwines `ρ` and `ρ'`, then `ρ'` is algebraic whenever `ρ` is: the matrix coefficients
in the transported basis `b.map φ` coincide with those of `ρ` in `b`. -/
private theorem isAlgebraic_of_equivariant_linearEquiv
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}
    {Y Y' : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Y'] [Module k Y'] [Module.Finite k Y']
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {ρ' : Matrix.GeneralLinearGroup (Fin N) k → Y' →ₗ[k] Y'}
    (φ : Y ≃ₗ[k] Y')
    (hφ : ∀ g y, φ (ρ g y) = ρ' g (φ y))
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    Etingof.IsAlgebraicRepresentation N ρ' := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b.map φ, P, fun g a c => ?_⟩
  have h2 : (b.map φ).repr (φ (ρ g (b c))) = b.repr (ρ g (b c)) := by
    change (φ.symm.trans b.repr) (φ (ρ g (b c))) = b.repr (ρ g (b c))
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  show (b.map φ).repr (ρ' g ((b.map φ) c)) a = evalAtGL g (P a c)
  rw [show ((b.map φ) c) = φ (b c) from rfl, ← hφ, h2, hP g a c]

/-- **The simple summands `L i` of `V^{⊗n}` are algebraic representations (#4932).**

Each summand `L i` with nonzero multiplicity space (`0 < dim (S i)`) embeds
`GL_N`-equivariantly into the polynomial representation `glTensorRep k N n` (which is
algebraic, `glTensorRep_isAlgebraic`), via `x ↦ e⁻¹ (lof i (s ⊗ x))` for a fixed
`s ∈ S i`; a left inverse is the equivariant projection used in
`schurWeyl_simple_summand_glWeightSpace_top`. Restricting the algebraic structure to the
(invariant) image and transporting it back through the embedding gives algebraicity of
`(L i).ρ`. This supplies the `IsAlgebraicRepresentation` hypothesis of
`schurWeyl_simples_formalCharacter_linearIndependent_complex`. -/
theorem schurWeyl_simple_summand_isAlgebraic
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ := by
  classical
  intro i
  -- A basis vector `s₀ = bS i0 ∈ S i` and the dual coordinate `φ` with `φ s₀ = 1`.
  let bS : Module.Basis (Fin (Module.finrank k (S i))) k (S i) := Module.finBasis k (S i)
  let i0 : Fin (Module.finrank k (S i)) := ⟨0, hSne i⟩
  let φ : (S i) →ₗ[k] k := bS.coord i0
  have hφ1 : φ (bS i0) = 1 := by
    show bS.coord i0 (bS i0) = 1
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  -- The equivariant embedding `s : L i ↪ V^{⊗n}`, `x ↦ e⁻¹ (lof i (s₀ ⊗ x))`.
  let s : (L i : Type) →ₗ[k] TensorPower k (Fin N → k) n :=
    e.symm.toLinearMap ∘ₗ
      (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ
      (TensorProduct.mk k (S i) (L i : Type) (bS i0))
  have hs_apply : ∀ x : (L i : Type),
      s x = e.symm (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i (bS i0 ⊗ₜ x)) :=
    fun _ => rfl
  -- Equivariance of `s`.
  have hs_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : (L i : Type)),
      glTensorRep k N n g (s x) = s ((L i).ρ g x) := by
    intro g x
    apply e.injective
    rw [he, hs_apply, hs_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      Representation.directSum_apply, DirectSum.lmap_lof, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.trivial_apply]
  -- The equivariant retraction `r : S i ⊗ L i → L i`, `a ⊗ x ↦ φ a • x`.
  let r : (S i ⊗[k] (L i : Type)) →ₗ[k] (L i : Type) :=
    (TensorProduct.lid k (L i : Type)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type)), r (a ⊗ₜ x) = φ a • x := by
    intro a x; simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  -- `q := r ∘ component i ∘ e` is a left inverse of `s`, so `s` is injective.
  let q : TensorPower k (Fin N → k) n →ₗ[k] (L i : Type) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ (e.toLinearMap)
  have hqs : ∀ x : (L i : Type), q (s x) = x := by
    intro x
    simp only [q, s, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self, TensorProduct.mk_apply]
    rw [hr_tmul, hφ1, one_smul]
  have hs_inj : Function.Injective s := Function.LeftInverse.injective hqs
  -- `W = range s` is `glTensorRep`-invariant.
  set W : Submodule k (TensorPower k (Fin N → k) n) := LinearMap.range s with hW
  have hWinv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k), ∀ v ∈ W, glTensorRep k N n g v ∈ W := by
    intro g v hv
    obtain ⟨x, rfl⟩ := hv
    exact ⟨(L i).ρ g x, (hs_equiv g x).symm⟩
  -- `glTensorRep` restricted to `W` is algebraic (`glTensorRep_isAlgebraic` + `restrict`).
  have hWalg : Etingof.IsAlgebraicRepresentation N
      (fun g => (glTensorRep k N n g).restrict (hWinv g)) :=
    (Etingof.glTensorRep_isAlgebraic k N n).restrict W hWinv
  -- Transport algebraicity back through `s : L i ≃ W`.
  let φW : (L i : Type) ≃ₗ[k] W := LinearEquiv.ofInjective s hs_inj
  have hφWval : ∀ y : (L i : Type), (φW y : TensorPower k (Fin N → k) n) = s y :=
    fun _ => rfl
  refine isAlgebraic_of_equivariant_linearEquiv φW.symm ?_ hWalg
  intro g w
  apply φW.injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearMap.restrict_coe_apply, hφWval, ← hs_equiv, ← hφWval, LinearEquiv.apply_symm_apply]

/-- **Highest-weight classification of the Schur-Weyl simples (general `k`, issue #4993).**

The general algebraically-closed characteristic-zero `k` form of
`schurWeyl_simples_formalCharacter_classification_core`:
given the equivariant decomposition data of `V^{⊗n}` (`V = Fin N → k`, `n ≤ N`),
there is an injective antitone-partition assignment `lam` with
`char(Lᵢ) = schurPoly N (lam i)`.

The proof routes through the numerical identity
(`schurWeyl_decomposition_numerical_identity`) and the isotypic matching
(`schurWeyl_simples_isotypic_matching_complex`, an injective
`φ : BoundedPartition N n ↪ ι` with `char(L (φ λ)) = schurPoly N λ.parts`). The
counting step `|ι| = |P|` (i.e. `φ` surjective, so `lam := φ⁻¹` is total) is
obtained here sorry-free *as a reduction*: the numerical identity rewrites to a
vanishing `ℚ`-combination of the characters `char(L i)`, whose linear independence
(`schurWeyl_simples_formalCharacter_linearIndependent_complex`, the one remaining
isolated `sorry`) forces every coefficient to vanish; the empty-fibre coefficients
are `dim(Sᵢ)`, so the nonzero-multiplicity hypothesis `hSne` (each `S i ≠ 0`,
supplied by simplicity at the call site) rules out indices outside `im φ`.

`hSne` is necessary, not cosmetic: without it a degenerate decomposition with
`S i₀ = 0` carries an unconstrained "ghost" simple `L i₀`, for which
`char(L i₀) = schurPoly N λ` fails — so the classification is genuinely false for
such data. The source decomposition
`glTensorRep_equivariant_schurWeyl_decomposition` has each `S i` a *simple*
`Sₙ`-module, hence `0 < dim(S i)`. -/
theorem schurWeyl_simples_formalCharacter_classification_core_general
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∃ lam : ι → {l : Fin N → ℕ // Antitone l},
      Function.Injective lam ∧
      ∀ i, formalCharacter k N (L i) = schurPoly N (lam i).val := by
  -- Two BoundedPartitions with equal `parts` are equal (proof-irrelevant fields).
  have hBP : ∀ {a b : BoundedPartition N n}, a.parts = b.parts → a = b := by
    rintro ⟨p, d, s⟩ ⟨p', d', s'⟩ h
    obtain rfl : p = p' := h
    rfl
  -- Isotypic matching (sorry-free): injective `φ : P ↪ ι`, `char(L (φ λ)) = schurPoly λ`.
  obtain ⟨φ, hφinj, hφchar⟩ :=
    schurWeyl_simples_isotypic_matching_general k N n L e he hLsimp
  -- Surjectivity of `φ` (the counting equality `|ι| = |P|`) via the numerical
  -- identity and linear independence of the simple characters. With each `L i`
  -- pairwise non-isomorphic and simple, the characters `char(L i)` are
  -- `ℚ`-independent (`schurWeyl_simples_formalCharacter_linearIndependent_complex`,
  -- the isolated remaining content). The numerical identity
  -- `∑ᵢ dim(Sᵢ)·char(Lᵢ) = ∑_λ dim(Specht_λ)·schurPoly λ` rewrites, via
  -- `char(L (φ λ)) = schurPoly λ` and the injectivity of `φ`, to a single
  -- vanishing `ℚ`-combination `∑ᵢ (dim(Sᵢ) - Cᵢ)·char(Lᵢ) = 0`, where `Cᵢ` is the
  -- total Specht-multiplicity over the `φ`-fibre of `i`. Independence forces every
  -- coefficient to vanish; for `i ∉ im φ` the fibre is empty so `dim(Sᵢ) = 0`,
  -- contradicting `hSne`. Hence `φ` is surjective.
  have hφsurj : Function.Surjective φ := by
    -- Each `L i` is a summand of the polynomial representation `V^{⊗n}` (with `S i ≠ 0`
    -- by `hSne`), hence algebraic: its weight spaces span (`hLtop`).
    have hLtop : ∀ i, ⨆ (μ : Fin N →₀ ℕ),
        glWeightSpace k N (L i) (fun j => μ j) = ⊤ :=
      schurWeyl_simple_summand_glWeightSpace_top k N n L e he hSne
    have hLalg : ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ :=
      schurWeyl_simple_summand_isAlgebraic k N n L e he hSne
    have hLI := schurWeyl_simples_formalCharacter_linearIndependent_general
      k N n L e he hLtop hLalg hLsimp hLdist
    have hnum := schurWeyl_decomposition_numerical_identity k N n L e he
    set v : ι → MvPolynomial (Fin N) ℚ := fun i => formalCharacter k N (L i) with hvdef
    -- Abstract the Specht-multiplicity coefficient on the partition side.
    obtain ⟨mfun, hmeq⟩ : ∃ mfun : BoundedPartition N n → ℚ,
        ∑ i, (Module.finrank k (S i) : ℚ) • v i
          = ∑ lam : BoundedPartition N n, mfun lam • schurPoly N lam.parts :=
      ⟨_, hnum⟩
    -- Pull the multiplicities back along `φ` and identify `schurPoly λ = char(L (φ λ))`.
    have hfib : ∑ i : ι,
          (∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) • v i
        = ∑ lam : BoundedPartition N n, mfun lam • schurPoly N lam.parts := by
      rw [← Finset.sum_fiberwise Finset.univ φ
        (fun lam => mfun lam • schurPoly N lam.parts)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun lam hlam => ?_
      have hli : φ lam = i := (Finset.mem_filter.mp hlam).2
      rw [← hli]
      simp only [hvdef]
      rw [hφchar lam]
    -- The vanishing `ℚ`-combination of the (independent) characters.
    have hkey : ∑ i, ((Module.finrank k (S i) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) • v i = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib, hfib, ← hmeq, sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hLI)
      (fun i => (Module.finrank k (S i) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) hkey
    -- Empty `φ`-fibre would force `dim(Sᵢ) = 0`, contradicting `hSne`.
    intro i₀
    by_contra hni
    have hempty : Finset.univ.filter (fun lam => φ lam = i₀)
        = (∅ : Finset (BoundedPartition N n)) := by
      rw [Finset.filter_eq_empty_iff]
      intro lam _ h
      exact hni ⟨lam, h⟩
    have hd0 : (Module.finrank k (S i₀) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i₀), mfun lam = 0 := hcoeff i₀
    rw [hempty, Finset.sum_empty, sub_zero] at hd0
    have hz : Module.finrank k (S i₀) = 0 := by exact_mod_cast hd0
    exact (hSne i₀).ne' hz
  -- `φ` is bijective, so `lam := φ⁻¹` is a total injective antitone assignment.
  let φequiv : BoundedPartition N n ≃ ι := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  refine ⟨fun i => ⟨(φequiv.symm i).parts, (φequiv.symm i).decreasing⟩, ?_, ?_⟩
  · intro i j hij
    exact φequiv.symm.injective (hBP (congrArg Subtype.val hij))
  · intro i
    have hi : L (φ (φequiv.symm i)) = L i := congrArg L (φequiv.apply_symm_apply i)
    rw [← hi]
    exact hφchar (φequiv.symm i)

/-- **Highest-weight uniqueness (issue #4901/#4721, route B).** A *simple* polynomial
`GL_N(k)`-representation whose formal character is the Schur polynomial `S_λ` (for an
antitone `λ`) is isomorphic to the Schur module `L_λ`.

This is the iso-strength form of the highest-weight classification, one notch stronger than
`schurWeyl_simples_formalCharacter_classification_core` (#4721, which only pins the
*character* of an abstract simple). The proof is the **two-element-family character
independence** argument: were `L` and `L_λ` non-isomorphic, the pair `{L, L_λ}` would be two
pairwise non-isomorphic simple polynomial representations (simplicity of `L_λ` is ingredient
(a)) whose equal formal characters force the torus-trace combination `trace(L) − trace(L_λ)`
to vanish, contradicting character independence (ingredient (b)) with the nonzero coefficient
vector `(1, -1)`. Hence `L ≅ L_λ`.

Polynomiality (weight saturation) of `L` is genuinely available at the real call site and is
threaded in as the hypothesis `hLtop`, not manufactured from the character: weight saturation
is *not* determined by `formalCharacter` for non-polynomial simples (e.g. `det⁻¹ ⊗ Sym³(std)`
at `N = 2` has character `schurPoly 2 (1,0)` but does not saturate), so the would-be ingredient
(c) `glWeightSpace_top_of_simple_formalCharacter_eq_schurPoly` was false and is retired (#4969).
The `L_λ`-side saturation is the true `glWeightSpace_schurModule_iSup_eq_top`. The two remaining
deep ingredients are isolated as the `sorry`s above (#4946 simplicity, #4947 independence).

Algebraicity of `L` is likewise threaded in as the hypothesis `hLalg` (the genuine input to
ingredient (b), which now takes algebraicity rather than the false `hLtop ⟹ regular` bridge;
see #4983): the `L_λ`-side is supplied internally by `schurModule_isAlgebraic`. Like weight
saturation, algebraicity is not determined by `formalCharacter`, so it must come from `L`'s
polynomial source; at the genuine call site (`iso_of_formalCharacter_eq_schurPoly`) it
transports from the algebraic ambient rep via `IsAlgebraicRepresentation.of_linearEquiv`. -/
theorem simpleRep_iso_schurModule_of_formalCharacter_eq (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (hLtop : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N L (fun i => μ i) = ⊤)
    (hLalg : Etingof.IsAlgebraicRepresentation N L.ρ)
    (h : formalCharacter k N L = schurPoly N lam) :
    Nonempty (L ≅ SchurModule k N lam) := by
  by_contra hno
  set S := SchurModule k N lam with hSdef
  -- `S = L_λ` is a simple polynomial representation with the same formal character as `L`.
  have hSchar : formalCharacter k N S = schurPoly N lam :=
    formalCharacter_schurModule_eq_schurPoly k N lam hlam
  have hSsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule S.ρ) := schurModule_isSimple_general k N lam hlam
  -- The two-element family `{L, S}` with coefficient vector `(1, -1)`.
  have htop : ∀ i, ⨆ (μ : Fin N →₀ ℕ),
      glWeightSpace k N (![L, S] i) (fun j => μ j) = ⊤ := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simpa using hLtop
    · simpa using glWeightSpace_schurModule_iSup_eq_top k N lam
  have hsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (![L, S] i).ρ) := by
    rw [Fin.forall_fin_two]; exact ⟨hLsimp, hSsimp⟩
  -- Both members of the family are algebraic: `L` by hypothesis, `S = L_λ` by
  -- `schurModule_isAlgebraic`. This is the genuine #4983 input to character independence.
  have hSalg : Etingof.IsAlgebraicRepresentation N S.ρ := by
    rw [hSdef]; exact schurModule_isAlgebraic N lam
  have halg : ∀ i, Etingof.IsAlgebraicRepresentation N (![L, S] i).ρ := by
    rw [Fin.forall_fin_two]; exact ⟨by simpa using hLalg, by simpa using hSalg⟩
  have hdist : Pairwise (fun i j => ¬ Nonempty ((![L, S] i) ≅ (![L, S] j))) := by
    have hsym : ¬ Nonempty (S ≅ L) := fun ⟨e⟩ => hno ⟨e.symm⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simpa using hno
        | simpa using hsym
  -- Equal formal characters ⟹ the `(1, -1)`-combination of characters vanishes.
  have hcharsum : ∑ i, (![(1 : ℚ), -1] i) • formalCharacter k N (![L, S] i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [h, hSchar, one_smul, neg_one_smul, add_neg_cancel]
  -- ⟹ the corresponding torus-trace combination vanishes at every diagonal torus element.
  have htorus : ∀ t : Fin N → kˣ,
      ∑ i, ((![(1 : ℚ), -1] i : ℚ) : k) •
        LinearMap.trace k (![L, S] i) ((![L, S] i).ρ (diagTorus k N t)) = 0 := by
    intro t
    exact trace_combination_eq_zero_of_formalCharacter_combination_eq_zero k N Finset.univ
      ![(1 : ℚ), -1] ![L, S] (fun i _ => htop i) hcharsum t
  -- Character independence (ingredient (b)) forces the coefficient `1` to vanish: absurd.
  have hzero := formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general
    k N ![L, S] halg hsimp hdist ![(1 : ℚ), -1] htorus
  simpa using hzero 0

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
  -- (2) Decompose `M.asModule` into abstract simples and the Schur-Weyl witnesses,
  -- then read the schurPoly-classification off the (relocated) classification core.
  obtain ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he,
      p, f, ⟨eM⟩⟩ :=
    Etingof.PolynomialGLDecomposition.decompose_polynomial_gl_rep k N n M halg h_span h_homog
  letI := hιFin; letI := hιDec
  letI : ∀ i, AddCommGroup (S i) := hSacg
  letI : ∀ i, Module k (S i) := hSmod
  letI : ∀ i, Module.Finite k (S i) := hSfin
  obtain ⟨lam_cl, lam_inj, hchar⟩ :=
    schurWeyl_simples_formalCharacter_classification_core_general k N n L e he hLsimp hLdist hSne
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
      formalCharacter_directSum k N (fun j : Fin p => (L (f j) : Type))
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
  -- Polynomiality of the simple summand `L (f 0)`: it is the equivariant image of the
  -- polynomial `M` under the `k`-linear GL-equivariant equivalence `hφ'`, so weight
  -- saturation transfers from `h_span` (`M`'s `ℕ`-weight spaces span).
  have hLf0top : ⨆ (μ : Fin N →₀ ℕ),
      glWeightSpace k N (L (f 0)) (fun i => μ i) = ⊤ :=
    glWeightSpace_iSup_eq_top_of_equivariant_surjective k N M (L (f 0))
      (Representation.kEquivOfAsModuleEquiv hφ').toLinearMap
      (fun g v => Representation.kEquivOfAsModuleEquiv_intertwines hφ' g v)
      (Representation.kEquivOfAsModuleEquiv hφ').surjective h_span
  -- Algebraicity of `L (f 0)` transports from the algebraic ambient rep `M` along the
  -- `k`-linear GL-equivariant equivalence `hφ'` (`IsAlgebraicRepresentation.of_linearEquiv`, #4983).
  have hLf0alg : Etingof.IsAlgebraicRepresentation N (L (f 0)).ρ :=
    Etingof.IsAlgebraicRepresentation.of_linearEquiv
      (Representation.kEquivOfAsModuleEquiv hφ')
      (fun g v => Representation.kEquivOfAsModuleEquiv_intertwines hφ' g v) halg
  have hLS : Nonempty (L (f 0) ≅ SchurModule k N lam) :=
    simpleRep_iso_schurModule_of_formalCharacter_eq k N lam hlam (L (f 0)) (hLsimp (f 0))
      hLf0top hLf0alg hchar0
  obtain ⟨isoML⟩ := hML
  obtain ⟨isoLS⟩ := hLS
  exact ⟨isoML ≪≫ isoLS⟩

end Etingof
