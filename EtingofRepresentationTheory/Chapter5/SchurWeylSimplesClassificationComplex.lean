import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification
import EtingofRepresentationTheory.Chapter5.SchurModuleSimple
import EtingofRepresentationTheory.Chapter5.SemisimpleIsotypic
import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition

/-!
# ℂ-side highest-weight classification of the Schur-Weyl simples (issue #4862)

This file delivers the **base-field-`ℂ`** half of the highest-weight classification
crux `schurWeyl_simples_formalCharacter_classification_core`
(`Chapter5/SchurWeylSimplesClassification.lean`, the isolated Tier-4 `sorry`).

Given the equivariant decomposition `e : V^{⊗n} ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ` of `V = Fin N → ℂ`
into abstract simple polynomial `GL_N(ℂ)`-reps `Lᵢ` (pairwise non-isomorphic), the
goal is an injective antitone-partition assignment `lam` with
`char(Lᵢ) = schurPoly N (lam i)`.

## Route (decomposition doc `progress/schur-weyl-crux-4732-decomposition.md`, route 1)

The proof factors into two halves, both directly over `ℂ`:

1. **Numerical identity** (`schurWeyl_decomposition_numerical_identity`, sorry-free,
   stated over a general field): chaining
   `formalCharacter_eq_of_rep_iso` / `formalCharacter_directSum` /
   `formalCharacter_trivialTensor` (giving `char(V^{⊗n}) = ∑ᵢ dim(Sᵢ)·char(Lᵢ)`),
   `formalCharacter_glTensorRep_eq_pow` (`char(V^{⊗n}) = (∑ Xᵢ)^n`), and
   `sum_X_pow_eq_sum_finrank_smul_schurPoly` (`(∑ Xᵢ)^n = ∑_λ dim(Specht_λ)·schurPoly λ`)
   yields `∑ᵢ dim(Sᵢ)·char(Lᵢ) = ∑_λ dim(Specht_λ)·schurPoly λ`.

2. **Isotypic matching** (injective `φ : P ↪ ι`): each `SchurModule ℂ N λ`
   (`schurModule_isSimple`) is a simple `GL_N(ℂ)`-submodule of `V^{⊗n}`; uniqueness of
   the isotypic decomposition against the abstract `e`-decomposition (via
   `SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum`) gives
   `SchurModule ℂ N λ ≅ L_{φλ}`, with `φ` injective by `schurPoly_injective`.

3. **Counting / surjectivity `|ι| = |P|`** (the deep step, double-centralizer):
   tracked separately; needed to define `lam := φ⁻¹` on all of `ι`.

This file currently lands half 1 sorry-free and isolates the remaining content in
`schurWeyl_simples_formalCharacter_classification_core_complex`.
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

/-- **Isotypic matching half of the ℂ-side classification (sorry-free).**

Given the equivariant decomposition data of `V^{⊗n}` (`V = Fin N → ℂ`, `n ≤ N`),
there is an *injective* assignment `φ : BoundedPartition N n → ι` such that
`char(L (φ λ)) = schurPoly N λ.parts` for every antitone partition `λ` of `n`
(length `≤ N`).

For each such `λ`, `SchurModule ℂ N λ.parts` is a simple `GL_N(ℂ)`-module
(`schurModule_isSimple`) sitting inside `V^{⊗n}` as the submodule
`SchurModuleSubmodule`; transporting it through the `R`-linear flattening
(`schurWeyl_decomposition_asModule_flatten`) and matching it to a single simple
component (`simpleModule_iso_component_of_embeds`) yields `SchurModule ℂ N λ.parts
≅ L (φ λ)`, hence `char(L (φ λ)) = char(SchurModule ℂ N λ.parts) = schurPoly N
λ.parts` (`formalCharacter_eq_of_asModule_linearEquiv`,
`formalCharacter_schurModule_eq_schurPoly`). Injectivity of `φ` follows from
`schurPoly_injective`.

This is steps 1–2,4 of route 1; the surjectivity `|ι| = |P|` (the counting step)
is the remaining content of `schurWeyl_simples_formalCharacter_classification_core_complex`. -/
theorem schurWeyl_simples_isotypic_matching_complex
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    [∀ i, Module.Finite ℂ (S i)]
    (L : ι → FDRep ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
    (e : TensorPower ℂ (Fin N → ℂ) n ≃ₗ[ℂ]
        (DirectSum ι (fun i => S i ⊗[ℂ] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) ℂ)
          (v : TensorPower ℂ (Fin N → ℂ) n),
          e (glTensorRep ℂ N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
        (Representation.asModule (L i).ρ)) :
    ∃ φ : BoundedPartition N n → ι,
      Function.Injective φ ∧
      ∀ lam : BoundedPartition N n,
        formalCharacter ℂ N (L (φ lam)) = schurPoly N lam.parts := by
  classical
  -- Per-partition matching: each Schur module is isomorphic to a single `L i`.
  have hmatch : ∀ lam : BoundedPartition N n,
      ∃ i : ι, formalCharacter ℂ N (L i) = schurPoly N lam.parts := by
    rintro ⟨parts, hdecr, hsum⟩
    subst hsum
    -- Inclusion `SchurModuleSubmodule ↪ V^{⊗(∑parts)}` intertwines the two actions.
    have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin N) ℂ)
        (x : SchurModuleSubmodule ℂ N parts),
        (SchurModuleSubmodule ℂ N parts).subtype (schurModuleRep ℂ N parts g x)
          = glTensorRep ℂ N (∑ i, parts i) g
              ((SchurModuleSubmodule ℂ N parts).subtype x) := by
      intro g x
      rfl
    -- `R`-linear injection of the simple Schur module into `V^{⊗n}`.
    haveI : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
        (Representation.asModule (schurModuleRep ℂ N parts)) :=
      schurModule_isSimple N parts hdecr hN
    obtain ⟨ν, ⟨Φ⟩⟩ := simpleModule_iso_component_of_embeds
      (Lsum := fun ν : Σ i : ι, Fin (Module.finrank ℂ (S i)) =>
        Representation.asModule (L ν.1).ρ)
      (fun ν => hLsimp ν.1)
      (schurWeyl_decomposition_asModule_flatten ℂ N (∑ i, parts i) L e he)
      (Representation.asModuleHomOfIntertwiner
        (SchurModuleSubmodule ℂ N parts).subtype hinter)
      (by
        intro a b hab
        exact Subtype.coe_injective hab)
    refine ⟨ν.1, ?_⟩
    have hchar := formalCharacter_eq_of_asModule_linearEquiv ℂ N
      (schurModuleRep ℂ N parts) (L ν.1).ρ Φ
    have hbridge : formalCharacter ℂ N (FDRep.of (L ν.1).ρ) = formalCharacter ℂ N (L ν.1) := rfl
    have hschur : formalCharacter ℂ N (FDRep.of (schurModuleRep ℂ N parts))
        = schurPoly N parts := formalCharacter_schurModule_eq_schurPoly ℂ N parts hdecr
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

/-- **ℂ-side highest-weight classification of the Schur-Weyl simples (issue #4862).**

The `ℂ`-specialization of `schurWeyl_simples_formalCharacter_classification_core`:
given the equivariant decomposition data of `V^{⊗n}` (`V = Fin N → ℂ`, `n ≤ N`),
there is an injective antitone-partition assignment `lam` with
`char(Lᵢ) = schurPoly N (lam i)`.

The proof routes through the numerical identity
(`schurWeyl_decomposition_numerical_identity`) and the isotypic matching
(`schurWeyl_simples_isotypic_matching_complex`, an injective
`φ : BoundedPartition N n ↪ ι` with `char(L (φ λ)) = schurPoly N λ.parts`); the
residual content is the counting step `|ι| = |P|` (double-centralizer), which makes
`φ` surjective so that `lam := φ⁻¹` is total. -/
theorem schurWeyl_simples_formalCharacter_classification_core_complex
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    [∀ i, Module.Finite ℂ (S i)]
    (L : ι → FDRep ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
    (e : TensorPower ℂ (Fin N → ℂ) n ≃ₗ[ℂ]
        (DirectSum ι (fun i => S i ⊗[ℂ] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) ℂ)
          (v : TensorPower ℂ (Fin N → ℂ) n),
          e (glTensorRep ℂ N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j)))) :
    ∃ lam : ι → {l : Fin N → ℕ // Antitone l},
      Function.Injective lam ∧
      ∀ i, formalCharacter ℂ N (L i) = schurPoly N (lam i).val := by
  -- Two BoundedPartitions with equal `parts` are equal (proof-irrelevant fields).
  have hBP : ∀ {a b : BoundedPartition N n}, a.parts = b.parts → a = b := by
    rintro ⟨p, d, s⟩ ⟨p', d', s'⟩ h
    obtain rfl : p = p' := h
    rfl
  -- Isotypic matching (sorry-free): injective `φ : P ↪ ι`, `char(L (φ λ)) = schurPoly λ`.
  obtain ⟨φ, hφinj, hφchar⟩ :=
    schurWeyl_simples_isotypic_matching_complex N n hN L e he hLsimp
  -- The ONLY remaining content: the counting equality `|ι| = |P|`, i.e. `φ` is
  -- surjective (every abstract simple `L i` is a Schur module). By the
  -- double-centralizer pairing (`Theorem5_18_4`), the number of simple GL-types in
  -- `V^{⊗n}` equals the number of antitone partitions `λ` of `n` with `ℓ(λ) ≤ N`.
  -- Deferred to a sub-issue; everything else below is sorry-free.
  have hφsurj : Function.Surjective φ := by
    sorry
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
