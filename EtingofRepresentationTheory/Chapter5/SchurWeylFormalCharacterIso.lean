import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification
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

* (a) `schurModule_isSimple_general` — general-`k` Schur-module simplicity (#4946, `sorry`);
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

/-- **Ingredient (a): general-`k` Schur-module simplicity (isolated `sorry`, issue #4946).**
The Schur module `L_λ = SchurModule k N lam` is a simple
`MonoidAlgebra k (GL_N(k))`-module for any antitone `lam`. This is proven for `k = ℂ` as
`schurModule_isSimple` (`SchurModuleSimple.lean`, via ℂ-specific Young-symmetrizer
infrastructure); lifting it to a general algebraically-closed characteristic-zero field is
the deliverable of #4946. -/
theorem schurModule_isSimple_general (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (SchurModule k N lam).ρ) := by
  sorry

/-- **Ingredient (b): general-`k` torus→full-group character independence (issue #4947,
algebraicity bridge #4983).** For a finite family of pairwise non-isomorphic simple
**algebraic** `GL_N(k)`-representations `L i`, a `ℚ`-combination `c` of their characters
whose corresponding combination of *torus* traces vanishes at every diagonal torus element
has all coefficients zero.

This is the general algebraically-closed characteristic-zero `k` analogue of the ℂ
seam `formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero`
(`SchurWeylSimplesClassificationComplex.lean`, #4908): same proof (Dedekind/Artin
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
