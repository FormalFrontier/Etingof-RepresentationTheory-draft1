import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Ideal.Quotient.Defs
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.Proposition9_2_3
import EtingofRepresentationTheory.Chapter9.Problem9_3_2
import EtingofRepresentationTheory.Chapter9.TruncatedPolynomial

/-!
# Problem 9.4.5: Cartan determinant and some homological dimensions

Etingof Problem 9.4.5 has two parts.

* **(i)** If a finite dimensional algebra `A` has finite homological dimension `d`, and `C` is
  the Cartan matrix of `A`, then `det(C) = ±1`.

* **(ii)** Compute the homological dimension of `k[t]/tⁿ` (`n > 1`) and of the algebra of
  Problem 9.3.2. Both are **infinite**: `k[t]/tⁿ` with `n > 1` is a self-injective but
  non-semisimple algebra, so it has infinite global dimension; the four dimensional algebra
  `A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 (which contains `k[x]/x²` and is likewise
  non-semisimple with a nonsplit self-extension) also has infinite homological dimension.

## Statement-pass note

Part (i) uses `Etingof.algebraCartanMatrix` (Definition 9.3.1) for the Cartan matrix and
`Etingof.homologicalDimension` (Definition 9.4.3) for the homological dimension; the entries
of the Cartan matrix are natural numbers, so `det(C) = ±1` is stated after casting the matrix
into `ℤ`. Part (ii) records the two concrete values as `homologicalDimension = ⊤`.

## Correct hypotheses for part (i)

The Cartan determinant is `±1` **only** when `C` is the genuine Cartan matrix of `A`, i.e.
`P` really is the family of projective covers of a complete, irredundant set of
representatives `M` of the simple `A`-modules. An earlier statement quantified over an
arbitrary family `P : ι → Type*` with only `homologicalDimension A ≠ ⊤`; that statement is
false (take `A = k`, `ι = Unit`, `P 0 = k²`: then `C = (4)` and `det = 4`). The restated
theorem below carries the full §9.3/§9.4.5 setup, mirroring the hypotheses of Proposition
9.2.3 (`Etingof.projective_cover_hom_multiplicity`):

* `A` is finite dimensional over `k`;
* `M : ι → Type*` is a complete (`hM_complete`), irredundant (`hM_distinct`) family of simple
  `A`-modules;
* each `P i` is an indecomposable projective (`hP_indec`) covering `M i`, encoded by the
  essential-cover dimension identity `dim_k Hom_A(Pᵢ, Mⱼ) = δᵢⱼ` (`hP_cover`);
* `A` has finite homological dimension (`hfin`).
-/

universe u

open scoped Polynomial

namespace Etingof.Problem945

/-- **Matrix-algebra reduction.** An integer square matrix with an integer right inverse has
determinant `±1`: from `C * D = 1` we get `det C * det D = 1` in `ℤ`, and the only units of
`ℤ` are `±1`. This is the elementary half of Problem 9.4.5(i); the mathematical content is
producing an integer right inverse `D` of the Cartan matrix from finite homological
dimension. -/
theorem det_eq_pm_one_of_mul_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C D : Matrix ι ι ℤ) (h : C * D = 1) :
    C.det = 1 ∨ C.det = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← Matrix.det_mul, h, Matrix.det_one])

/-- **Matrix assembly.** If every standard basis vector `eⱼ = Pi.single j 1` lies in the
`ℤ`-column span of `C` (i.e. `C.mulVec d = eⱼ` for some integer vector `d`), then `C` has an
integer right inverse `D`. Assemble `D` column by column from the witnessing vectors: column
`j` of `D` is the vector `d` with `C.mulVec d = eⱼ`, so column `j` of `C * D` is `eⱼ`, giving
`C * D = 1`. This packages the `K₀` change-of-basis identity `C · D = 1` into the elementary
`∃ D, C * D = 1` consumed by `det_eq_pm_one_of_mul_eq_one`. -/
theorem exists_right_inverse_of_forall_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ)
    (h : ∀ j, ∃ d : ι → ℤ, C.mulVec d = Pi.single j 1) :
    ∃ D : Matrix ι ι ℤ, C * D = 1 := by
  choose d hd using h
  refine ⟨Matrix.of fun i j => d j i, ?_⟩
  ext i j
  have hcol : (C * Matrix.of fun i j => d j i) i j = C.mulVec (d j) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.of_apply, dotProduct]
  rw [hcol, hd j]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

/-- **Composition-multiplicity class vector.** For an `A`-module `N`, the vector in `ℤ^ι`
whose `i`-th entry is `dim_k Hom_A(Pᵢ, N)`. By Proposition 9.2.3
(`Etingof.projective_cover_hom_multiplicity`) this equals the Jordan–Hölder multiplicity
vector `([N : Mᵢ])ᵢ`, but the `Hom`-dimension form is manifestly independent of any choice
of composition series and is additive on short exact sequences by
`finrank_hom_additive_of_projective`. This is the concrete `K₀`-class function the Cartan
determinant argument runs on. -/
noncomputable def homClassVector
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    (N : Type*) [AddCommGroup N] [Module A N] [Module k N] [SMulCommClass A k N] : ι → ℤ :=
  fun i => (Module.finrank k (P i →ₗ[A] N) : ℤ)

/-- The class vector of the projective indecomposable `Pⱼ` is column `j` of the Cartan matrix:
`homClassVector P (P j) i = Cᵢⱼ`. This is immediate from the definition of the Cartan matrix
(`Etingof.algebraCartanMatrix`), whose `(i, j)` entry is exactly `dim_k Hom_A(Pᵢ, Pⱼ)`. -/
theorem homClassVector_proj_eq_cartan_col
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, SMulCommClass A k (P i)] (i j : ι) :
    homClassVector (k := k) (A := A) P (P j) i =
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i j := by
  simp [homClassVector, Etingof.algebraCartanMatrix]

/-- The class vector of the simple module `Mⱼ` is the standard basis vector `eⱼ`, from the
essential-cover identity `dim_k Hom_A(Pᵢ, Mⱼ) = δᵢⱼ` (`hP_cover`). -/
theorem homClassVector_simple_eq_single
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [DecidableEq ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, Module k (M i)]
    [∀ i, SMulCommClass A k (M i)]
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) (j : ι) :
    homClassVector (k := k) (A := A) P (M j) = Pi.single j 1 := by
  funext i
  simp only [homClassVector, hP_cover i j, Pi.single_apply]
  split <;> simp_all [eq_comm]

/-- **Problem 9.4.5 (i).** If the finite dimensional algebra `A` has finite homological
dimension, then the determinant of its Cartan matrix `C` is `±1`.

The Cartan matrix `Etingof.algebraCartanMatrix P` (Definition 9.3.1) is built from the family
`P` of projective covers of the simple modules; its `ℕ`-entries are cast to `ℤ` to take the
determinant. The hypotheses fix `M` as a complete, irredundant family of simple `A`-modules
and `P i` as the indecomposable projective cover of `M i` (encoded by the essential-cover
identity `dim_k Hom_A(Pᵢ, Mⱼ) = δᵢⱼ`), so that `C` is genuinely the change-of-basis matrix in
`K₀` between the simples `[Mᵢ]` and the projective indecomposables `[Pᵢ]`. -/
theorem cartan_det_eq_pm_one
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_distinct : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (hfin : Etingof.homologicalDimension A ≠ ⊤) :
    ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = 1 ∨
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = -1 := by
  set C := (Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ) with hC
  -- It suffices to produce an integer right inverse `D` of the Cartan matrix `C`.
  suffices h : ∃ D : Matrix ι ι ℤ, C * D = 1 by
    obtain ⟨D, hD⟩ := h
    exact det_eq_pm_one_of_mul_eq_one C D hD
  -- By the matrix assembly lemma, it suffices to express each standard basis vector `eⱼ` in
  -- the `ℤ`-column span of `C`. Since `homClassVector P (M j) = eⱼ` (essential cover, `hP_cover`)
  -- and the columns of `C` are the class vectors `homClassVector P (P i)`
  -- (`homClassVector_proj_eq_cartan_col`), this is exactly the statement that the class of the
  -- simple `Mⱼ` is an **integer** combination of the classes of the projective indecomposables.
  refine exists_right_inverse_of_forall_mulVec C (fun j => ?_)
  -- It suffices to express the class vector of the simple `Mⱼ` (which is `eⱼ` by `hP_cover`,
  -- via `homClassVector_simple_eq_single`) as `C.mulVec d` for an integer vector `d`.
  suffices hEuler : ∃ d : ι → ℤ, C.mulVec d = homClassVector (k := k) (A := A) P (M j) by
    obtain ⟨d, hd⟩ := hEuler
    exact ⟨d, by rw [hd, homClassVector_simple_eq_single P M hP_cover j]⟩
  -- Remaining content (Euler characteristic of a finite projective resolution). Finite
  -- homological dimension (`hfin`) gives each simple `Mⱼ` a finite projective resolution
  -- `0 → Q_d → … → Q₀ → Mⱼ → 0` with each `Q_k` a finitely generated projective, hence
  -- (Krull–Schmidt) a direct sum of the `Pᵢ` with multiplicity vector `aₖ : ι → ℤ`. Additivity
  -- of `homClassVector` on short exact sequences (`finrank_hom_additive_of_projective`) gives
  --   `homClassVector P (M j) = Σₖ (-1)ᵏ homClassVector P (Q_k) = Σₖ (-1)ᵏ C.mulVec aₖ`
  --                          `= C.mulVec (Σₖ (-1)ᵏ aₖ)`,
  -- so `d := Σₖ (-1)ᵏ aₖ` is the required integer vector. This needs finite projective
  -- resolutions of simples (from `hfin`), Krull–Schmidt decomposition of f.g. projectives into
  -- the `Pᵢ`, and the direct-sum additivity `homClassVector P (⊕ᵢ Pᵢ^{aᵢ}) = C.mulVec a`; it is
  -- deferred to a dedicated sub-issue (see the PR description).
  sorry

/-- **Problem 9.4.5 (ii), first algebra.** For `n > 1`, the truncated polynomial algebra
`k[t]/tⁿ` has infinite homological dimension. -/
theorem homologicalDimension_polynomial_quotient_eq_top
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    Etingof.homologicalDimension (k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ n}) = ⊤ :=
  Etingof.TruncatedPoly.homologicalDimension_eq_top_truncated k n hn

/-- **Problem 9.4.5 (ii), second algebra.** The four dimensional algebra
`A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 has infinite homological dimension. -/
theorem homologicalDimension_problem932_eq_top :
    Etingof.homologicalDimension Etingof.Problem932.A = ⊤ := by
  sorry

end Etingof.Problem945
