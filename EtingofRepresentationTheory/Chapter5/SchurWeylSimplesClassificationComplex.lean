import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification
import EtingofRepresentationTheory.Chapter5.SchurModuleSimple
import EtingofRepresentationTheory.Chapter5.SemisimpleIsotypic
import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace
import EtingofRepresentationTheory.Chapter5.CharacterIndependence
import EtingofRepresentationTheory.Chapter5.SchurWeylFormalCharacterIso
import EtingofRepresentationTheory.Chapter5.TraceVanishingDensity
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic

/-!
# Highest-weight classification of the Schur-Weyl simples (issue #4862 / #4993)

This file delivers the highest-weight classification crux
`schurWeyl_simples_formalCharacter_classification_core` over a general algebraically
closed characteristic-zero field `k` (issue #4993; the original ℂ-only version was
issue #4862). It is a leaf file — its theorems are consumed nowhere else in the tree.

Given the equivariant decomposition `e : V^{⊗n} ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ` of `V = Fin N → k`
into abstract simple polynomial `GL_N(k)`-reps `Lᵢ` (pairwise non-isomorphic), the
goal is an injective antitone-partition assignment `lam` with
`char(Lᵢ) = schurPoly N (lam i)`.

## Route (decomposition doc `progress/schur-weyl-crux-4732-decomposition.md`, route 1)

The proof factors into two halves, both directly over `k`:

1. **Numerical identity** (`schurWeyl_decomposition_numerical_identity`, sorry-free,
   stated over a general field): chaining
   `formalCharacter_eq_of_rep_iso` / `formalCharacter_directSum` /
   `formalCharacter_trivialTensor` (giving `char(V^{⊗n}) = ∑ᵢ dim(Sᵢ)·char(Lᵢ)`),
   `formalCharacter_glTensorRep_eq_pow` (`char(V^{⊗n}) = (∑ Xᵢ)^n`), and
   `sum_X_pow_eq_sum_finrank_smul_schurPoly` (`(∑ Xᵢ)^n = ∑_λ dim(Specht_λ)·schurPoly λ`)
   yields `∑ᵢ dim(Sᵢ)·char(Lᵢ) = ∑_λ dim(Specht_λ)·schurPoly λ`.

2. **Isotypic matching** (injective `φ : P ↪ ι`): each `SchurModule k N λ`
   (`schurModule_isSimple_general`) is a simple `GL_N(k)`-submodule of `V^{⊗n}`;
   uniqueness of the isotypic decomposition against the abstract `e`-decomposition (via
   `SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum`) gives
   `SchurModule k N λ ≅ L_{φλ}`, with `φ` injective by `schurPoly_injective`.

3. **Counting / surjectivity `|ι| = |P|`** (the deep step): reduced sorry-free via the
   numerical identity and linear independence of the simple characters
   (`schurWeyl_simples_formalCharacter_linearIndependent_general`).

The classification is sorry-free **modulo the already-isolated general-`k` seam
sorries #4946 (`schurModule_isSimple_general`) and #4947
(`formalCharacter_simples_coeff_eq_zero_of_torus_trace_eq_zero_general`)**, both in
`SchurWeylFormalCharacterIso.lean`.
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct DirectSum

namespace Etingof

universe u

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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
    (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ)
    {V W : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] (W : Type u))
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
  let r : (S i ⊗[k] (L i : Type u)) →ₗ[k] (L i : Type u) :=
    (TensorProduct.lid k (L i : Type u)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type u)), r (a ⊗ₜ x) = φ a • x := by
    intro a x
    simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  -- `r` is `GL_N`-equivariant for `(trivial ⊗ ρ_{L i})` and `ρ_{L i}` (trivial action on `S i`).
  have hr_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (y : S i ⊗[k] (L i : Type u)),
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
  let q : TensorPower k (Fin N → k) n →ₗ[k] (L i : Type u) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type u)) i) ∘ₗ (e.toLinearMap)
  -- Coordinate formula for the direct-sum representation.
  have coord : ∀ (x : DirectSum ι (fun j => S j ⊗[k] (L j : Type u)))
      (g : Matrix.GeneralLinearGroup (Fin N) k),
      DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type u)) i
          (Representation.directSum (fun j =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (S j)).tprod (L j).ρ) g x)
        = ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
            (L i).ρ) g
            (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type u)) i x) := by
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
    refine ⟨e.symm (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type u)) i (b i0 ⊗ₜ x)), ?_⟩
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]
    rw [hr_tmul, hφ, one_smul]
  -- Assemble: `⊤ = q ⊤ = q (⨆ wt sp of V^{⊗n}) = ⨆ q(wt sp) ≤ ⨆ wt sp of L i`.
  have hmap_top : Submodule.map q ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  refine le_antisymm le_top ?_
  calc (⊤ : Submodule k (L i : Type u))
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
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
  let s : (L i : Type u) →ₗ[k] TensorPower k (Fin N → k) n :=
    e.symm.toLinearMap ∘ₗ
      (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type u)) i) ∘ₗ
      (TensorProduct.mk k (S i) (L i : Type u) (bS i0))
  have hs_apply : ∀ x : (L i : Type u),
      s x = e.symm (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type u)) i (bS i0 ⊗ₜ x)) :=
    fun _ => rfl
  -- Equivariance of `s`.
  have hs_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : (L i : Type u)),
      glTensorRep k N n g (s x) = s ((L i).ρ g x) := by
    intro g x
    apply e.injective
    rw [he, hs_apply, hs_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      Representation.directSum_apply, DirectSum.lmap_lof, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.trivial_apply]
  -- The equivariant retraction `r : S i ⊗ L i → L i`, `a ⊗ x ↦ φ a • x`.
  let r : (S i ⊗[k] (L i : Type u)) →ₗ[k] (L i : Type u) :=
    (TensorProduct.lid k (L i : Type u)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type u)), r (a ⊗ₜ x) = φ a • x := by
    intro a x; simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  -- `q := r ∘ component i ∘ e` is a left inverse of `s`, so `s` is injective.
  let q : TensorPower k (Fin N → k) n →ₗ[k] (L i : Type u) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type u)) i) ∘ₗ (e.toLinearMap)
  have hqs : ∀ x : (L i : Type u), q (s x) = x := by
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
  let φW : (L i : Type u) ≃ₗ[k] W := LinearEquiv.ofInjective s hs_inj
  have hφWval : ∀ y : (L i : Type u), (φW y : TensorPower k (Fin N → k) n) = s y :=
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
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
    schurWeyl_simples_isotypic_matching_general k N n hN L e he hLsimp
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
      schurWeyl_simple_summand_glWeightSpace_top k N n hN L e he hSne
    have hLalg : ∀ i, Etingof.IsAlgebraicRepresentation N (L i).ρ :=
      schurWeyl_simple_summand_isAlgebraic k N n L e he hSne
    have hLI := schurWeyl_simples_formalCharacter_linearIndependent_general
      k N n hN L e he hLtop hLalg hLsimp hLdist
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

end Etingof
