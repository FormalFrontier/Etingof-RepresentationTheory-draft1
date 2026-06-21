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

/-- **ℂ-side highest-weight classification of the Schur-Weyl simples (issue #4862).**

The `ℂ`-specialization of `schurWeyl_simples_formalCharacter_classification_core`:
given the equivariant decomposition data of `V^{⊗n}` (`V = Fin N → ℂ`, `n ≤ N`),
there is an injective antitone-partition assignment `lam` with
`char(Lᵢ) = schurPoly N (lam i)`.

The proof routes through the numerical identity
(`schurWeyl_decomposition_numerical_identity`) and the isotypic matching against
the concrete simple submodules `SchurModule ℂ N λ`; the residual content is the
counting step `|ι| = |P|` (double-centralizer). -/
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
  -- Half 1 (numerical identity) is available sorry-free as
  -- `schurWeyl_decomposition_numerical_identity ℂ N n L e he`.
  -- Remaining: isotypic matching `φ : P ↪ ι` and counting `|ι| = |P|` (sub-issues).
  sorry

end Etingof
