import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionReduction
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import EtingofRepresentationTheory.Chapter3.Theorem3_8_1
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
  Problem 9.3.2. Both are infinite: `k[t]/tⁿ` with `n > 1` is a self-injective but
  non-semisimple algebra, so it has infinite global dimension; the four dimensional algebra
  `A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 (which contains `k[x]/x²` and is likewise
  non-semisimple with a nonsplit self-extension) also has infinite homological dimension.

## Formalization notes

Part (i) uses `Etingof.algebraCartanMatrix` (Definition 9.3.1) for the Cartan matrix and
`Etingof.homologicalDimension` (Definition 9.4.3) for the homological dimension; the entries
of the Cartan matrix are natural numbers, so `det(C) = ±1` is stated after casting the matrix
into `ℤ`. Part (ii) gives both homological dimensions as `homologicalDimension = ⊤`.

## Correct hypotheses for part (i)

The Cartan determinant is `±1` only when `C` is the Cartan matrix of `A`, i.e.
`P` really is the family of projective covers of a complete, irredundant set of
representatives `M` of the simple `A`-modules. Quantifying over an arbitrary family
`P : ι → Type*` with only `homologicalDimension A ≠ ⊤` gives a false statement (take
`A = k`, `ι = Unit`, `P 0 = k²`: then `C = (4)` and `det = 4`). The theorem below therefore
carries the full §9.3/§9.4.5 setup, mirroring the hypotheses of Proposition
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

open CategoryTheory

/-- **Reduction to unbounded projective dimension.** If a ring `R` has homological dimension
`≤ d` for *no* `d`, then its homological dimension is `⊤`. Each inner infimum in
`homologicalDimension R = ⨅ d (_ : HasHomologicalDimensionLE R d), (d : ℕ∞)` ranges over a
false proposition, so the whole infimum is `⊤`. -/
theorem Etingof.homologicalDimension_eq_top_of_forall {R : Type u} [Ring R]
    (h : ∀ d, ¬ Etingof.HasHomologicalDimensionLE R d) :
    Etingof.homologicalDimension R = ⊤ := by
  refine le_antisymm le_top ?_
  unfold Etingof.homologicalDimension
  exact le_iInf₂ (fun d hd => absurd hd (h d))

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

/-- **Building the right inverse.** If every standard basis vector `eⱼ = Pi.single j 1` lies in
the `ℤ`-column span of `C` (i.e. `C.mulVec d = eⱼ` for some integer vector `d`), then `C` has an
integer right inverse `D`. Build `D` column by column from the witnessing vectors: column
`j` of `D` is the vector `d` with `C.mulVec d = eⱼ`, so column `j` of `C * D` is `eⱼ`, giving
`C * D = 1`. This packages the `K₀` change-of-basis identity `C · D = 1` into the elementary
`∃ D, C * D = 1` used by `det_eq_pm_one_of_mul_eq_one`. -/
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
  simp [Pi.single_apply, Matrix.one_apply]

/-- **Composition-multiplicity class vector.** For an `A`-module `N`, the vector in `ℤ^ι`
whose `i`-th entry is `dim_k Hom_A(Pᵢ, N)`. By Proposition 9.2.3
(`Etingof.projective_cover_hom_multiplicity`) this equals the Jordan–Hölder multiplicity
vector `([N : Mᵢ])ᵢ`, but the `Hom`-dimension form is manifestly independent of any choice
of composition series and is additive on short exact sequences by
`finrank_hom_additive_of_projective`. This is the concrete `K₀`-class function underlying the
Cartan determinant argument. -/
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

/-- **Class-vector additivity on short exact sequences.** For a submodule `N' ≤ N`,
`homClassVector P N = homClassVector P N' + homClassVector P (N ⧸ N')`. Entrywise this is
`finrank_hom_additive_of_projective` (Hom_A(Pᵢ, −) is exact on the short exact sequence
`0 → N' → N → N/N' → 0` because each `Pᵢ` is projective), cast to `ℤ`. -/
theorem homClassVector_add_quotient
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (N : Type*) [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] [SMulCommClass A k N] [Module.Finite k N]
    (N' : Submodule A N) :
    homClassVector (k := k) (A := A) P N =
      homClassVector (k := k) (A := A) P N' + homClassVector (k := k) (A := A) P (N ⧸ N') := by
  funext i
  simp only [homClassVector, Pi.add_apply]
  rw [finrank_hom_additive_of_projective (P := P i) N']
  push_cast
  ring

section DirectSum

open scoped DirectSum

attribute [local instance] Module.Free.of_divisionRing

/-- **Class-vector is a linear-isomorphism invariant.** If `M ≃ₗ[A] N` then `homClassVector P`
agrees on `M` and `N`: post-composition with the `A`-linear isomorphism is a `k`-linear
isomorphism `Hom_A(Pᵢ, M) ≃ₗ[k] Hom_A(Pᵢ, N)`, so the two `Hom`-dimensions coincide. -/
theorem homClassVector_congr
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [SMulCommClass A k M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N]
    (e : M ≃ₗ[A] N) :
    homClassVector (k := k) (A := A) P M = homClassVector (k := k) (A := A) P N := by
  funext i
  simp only [homClassVector]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun f => e.toLinearMap.comp f
      invFun := fun f => e.symm.toLinearMap.comp f
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by
        ext x; simpa using LinearMapClass.map_smul_of_tower e c (f x)
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp }

/-- **Class-vector additivity over finite products.** For a finite family `Q : σ → Type*` of
`A`-modules that are finite `k`-vector spaces, `homClassVector P (∀ s, Q s) = ∑ s, homClassVector
P (Q s)`. `Hom_A(Pᵢ, ∏ₛ Qₛ) ≃ₗ[k] ∏ₛ Hom_A(Pᵢ, Qₛ)` (products commute with `Hom` in the second
argument), and `finrank` of a finite product is the sum of the `finrank`s. -/
theorem homClassVector_pi
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, Module.Finite k (P i)]
    {σ : Type*} [Fintype σ] (Q : σ → Type*)
    [∀ s, AddCommGroup (Q s)] [∀ s, Module A (Q s)] [∀ s, Module k (Q s)]
    [∀ s, IsScalarTower k A (Q s)] [∀ s, SMulCommClass A k (Q s)] [∀ s, Module.Finite k (Q s)] :
    homClassVector (k := k) (A := A) P (∀ s, Q s) =
      ∑ s, homClassVector (k := k) (A := A) P (Q s) := by
  funext l
  rw [Finset.sum_apply]
  simp only [homClassVector]
  rw [← Nat.cast_sum]
  congr 1
  rw [LinearEquiv.finrank_eq
    (show (P l →ₗ[A] ∀ s, Q s) ≃ₗ[k] ∀ s, (P l →ₗ[A] Q s) from
      { toFun := fun f s => (LinearMap.proj s).comp f
        invFun := fun g => LinearMap.pi g
        map_add' := fun f g => by funext s; ext x; simp
        map_smul' := fun c f => by funext s; ext x; simp
        left_inv := fun f => by
          refine LinearMap.ext fun x => ?_; funext s; simp
        right_inv := fun g => by funext s; ext x; simp })]
  exact Module.finrank_pi_fintype k

/-- **Class-vector additivity over finite direct sums.** Same statement as `homClassVector_pi`
for the internal direct sum `⨁ s, Q s`, which is `A`-linearly isomorphic to the product for a
finite index type. -/
theorem homClassVector_directSum
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, Module.Finite k (P i)]
    {σ : Type*} [Fintype σ] (Q : σ → Type*)
    [∀ s, AddCommGroup (Q s)] [∀ s, Module A (Q s)] [∀ s, Module k (Q s)]
    [∀ s, IsScalarTower k A (Q s)] [∀ s, SMulCommClass A k (Q s)] [∀ s, Module.Finite k (Q s)] :
    homClassVector (k := k) (A := A) P (⨁ s, Q s) =
      ∑ s, homClassVector (k := k) (A := A) P (Q s) := by
  rw [homClassVector_congr P (DirectSum.linearEquivFunOnFintype A σ Q)]
  exact homClassVector_pi P Q

/-- **Cartan-matrix class vector of a `Pᵢ`-isotypic projective.** For a multiplicity vector
`a : ι → ℕ`, the direct sum `⨁ᵢ Pᵢ^{aᵢ}` (encoded as `⨁ (p : Σ i, Fin (a i)), P p.1`) has class
vector `C.mulVec a`, where `C` is the (`ℤ`-cast) Cartan matrix. This is `homClassVector_directSum`
combined with `homClassVector_proj_eq_cartan_col` (each `Pⱼ` contributes column `j` of `C`) and
the reindexing `∑_{p : Σ i, Fin (a i)} f p.1 = ∑ᵢ (a i) • f i`. -/
theorem homClassVector_isotypic
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (a : ι → ℕ) :
    homClassVector (k := k) (A := A) P (⨁ p : (Σ i, Fin (a i)), P p.1) =
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
        (fun i => (a i : ℤ)) := by
  rw [homClassVector_directSum P (fun p : (Σ i, Fin (a i)) => P p.1)]
  funext l
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp only [homClassVector_proj_eq_cartan_col, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul, mul_comm]

/-- **Class vector of a projective isomorphic to `⨁ᵢ Pᵢ^{aᵢ}`.** Krull–Schmidt-friendly form of
`homClassVector_isotypic`: if `N` is `A`-linearly isomorphic to `⨁ᵢ Pᵢ^{aᵢ}` then its class
vector is `C.mulVec a`. This is the form the Euler-characteristic step of Problem 9.4.5(i)
consumes for each projective in a finite resolution of a simple module. -/
theorem homClassVector_eq_mulVec_of_equiv
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (a : ι → ℕ) {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N] (e : N ≃ₗ[A] ⨁ p : (Σ i, Fin (a i)), P p.1) :
    homClassVector (k := k) (A := A) P N =
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
        (fun i => (a i : ℤ)) := by
  rw [homClassVector_congr P e, homClassVector_isotypic]

/-- **Every indecomposable f.g. projective `A`-module is one of the `Pᵢ`.** Given the §9.3/§9.4.5
setup (a complete family `M` of simple modules (`hM_complete`) and their indecomposable projective
covers `P` (`hP_indec`, `hP_cover`)), any indecomposable finitely generated projective `A`-module
`Q` is `A`-linearly isomorphic to some `P i`. This is the module-level PIM classification: `Q` has a
simple quotient `Q ↠ M j₀` (`Q` nonzero and f.g. over the artinian `A`, so it has a maximal
submodule), and `P j₀` also maps onto `M j₀` (`hP_cover` gives `dim_k Hom_A(P j₀, M j₀) = 1`), so
by `Etingof.indecomposable_projective_iso_of_hom` (two indecomposable projectives with nonzero
`Hom` to the same simple are isomorphic) `Q ≃ₗ[A] P j₀`. This mirrors `Etingof.Theorem_9_2_1_iii`
but drops the `IsAlgClosed k` hypothesis, which that argument does not use. -/
theorem indecProjective_iso_some_P
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
    [SMulCommClass A k Q] [Module.Projective A Q] [Module.Finite A Q]
    (hQ_indec : Etingof.IsIndecomposable A Q) :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : Nontrivial Q := hQ_indec.1
  haveI : Module.Finite k Q := Module.Finite.trans A Q
  haveI : FiniteDimensional k Q := ‹Module.Finite k Q›
  -- `Q` has a maximal submodule `N`, so `Q ⧸ N` is simple; it is `≃ₗ[A]` some `M j₀`.
  obtain ⟨N, hN_coatom⟩ := Etingof.Theorem921.exists_isCoatom_submodule (R := A) (M := Q)
  haveI : IsSimpleModule A (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom
  obtain ⟨j₀, ⟨e⟩⟩ := hM_complete (Q ⧸ N) inferInstance
  refine ⟨j₀, ?_⟩
  -- The composition `Q → Q ⧸ N ≅ M j₀` is a nonzero map.
  set φ : Q →ₗ[A] M j₀ := e.toLinearMap.comp N.mkQ with hφdef
  have hφ : φ ≠ 0 := by
    intro h
    apply hN_coatom.1
    rw [Submodule.eq_top_iff']
    intro q
    have h1 : e (N.mkQ q) = 0 := by
      have := LinearMap.congr_fun h q; simpa [hφdef] using this
    have h2 : N.mkQ q = 0 := e.injective (by rw [h1, map_zero])
    exact (Submodule.Quotient.mk_eq_zero N).mp h2
  -- `P j₀` also has a nonzero map to `M j₀`, since `dim_k Hom_A(P j₀, M j₀) = 1`.
  haveI : FiniteDimensional k (P j₀) := Module.Finite.trans A (P j₀)
  haveI : Module.Finite A (M j₀) := Module.Finite.equiv e
  haveI : Module.Finite k (M j₀) := Module.Finite.trans A (M j₀)
  haveI : Module.Finite k (P j₀ →ₗ[A] M j₀) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (P j₀) (M j₀) k)
      (LinearMap.restrictScalars_injective k)
  have hPdim : Module.finrank k (P j₀ →ₗ[A] M j₀) = 1 := by
    have := hP_cover j₀ j₀; simpa using this
  have hP_nt : Nontrivial (P j₀ →ₗ[A] M j₀) := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : P j₀ →ₗ[A] M j₀)
  exact Etingof.indecomposable_projective_iso_of_hom (k := k) hQ_indec (hP_indec j₀) φ hφ ψ hψ

/-- **Class vector of an f.g. projective is an `ℕ`-combination of Cartan columns.** For any finitely
generated projective `A`-module `N`, the multiplicity class vector `homClassVector P N` equals
`C.mulVec a` for some `a : ι → ℕ`, where `C` is the (`ℤ`-cast) Cartan matrix. This is the
Krull–Schmidt piece of Problem 9.4.5(i): by module-level Krull–Schmidt existence
(`Etingof.krull_schmidt_existence`) the finite-dimensional `N` decomposes internally as
`⨁ᵢ Wᵢ` with each `Wᵢ` indecomposable; each `Wᵢ` is a direct summand of the projective `N`, hence
projective, and therefore (`indecProjective_iso_some_P`) `≃ₗ[A]` some `P (g i)`. Additivity of
`homClassVector` over the finite direct sum (`homClassVector_directSum`) and the identification of
`homClassVector P (P j)` with column `j` of `C` (`homClassVector_proj_eq_cartan_col`) give
`homClassVector P N = ∑ᵢ (column (g i) of C) = C.mulVec a`, where `a j` counts the summands
isomorphic to `P j`. -/
theorem homClassVector_projective_eq_mulVec
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (N : Type u) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N] [Module.Projective A N] [Module.Finite A N] :
    ∃ a : ι → ℕ,
      homClassVector (k := k) (A := A) P N =
        ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
          (fun i => (a i : ℤ)) := by
  classical
  set C := (Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ) with hC
  haveI : ∀ i, Module.Finite k (P i) := fun i => Module.Finite.trans A (P i)
  haveI : Module.Finite k N := Module.Finite.trans A N
  haveI : FiniteDimensional k N := ‹Module.Finite k N›
  -- Krull–Schmidt existence: `N = ⨁ᵢ Wᵢ` internally, each `Wᵢ` indecomposable.
  obtain ⟨n, W, hW_indec, hW_sup, hW_indep⟩ := Etingof.krull_schmidt_existence k A N
  have hInt : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hW_indep hW_sup
  -- `N ≃ₗ[A] ⨁ᵢ Wᵢ`.
  let e : N ≃ₗ[A] ⨁ i, (W i) := (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hInt).symm
  -- `⨁ᵢ Wᵢ` is projective (transfer from `N`); each `Wᵢ` is a summand, hence projective.
  haveI : Module.Projective A (⨁ i, (W i)) := Module.Projective.of_equiv e
  haveI hWproj : ∀ i, Module.Projective A (W i) := fun i =>
    Module.Projective.of_split
      (DirectSum.lof A (Fin n) (fun j => (W j)) i)
      (DirectSum.component A (Fin n) (fun j => (W j)) i)
      (DirectSum.component_comp_lof_same A i)
  -- each `Wᵢ` is finite over `k`, hence over `A`.
  haveI hWfin : ∀ i, Module.Finite k (W i) := fun i =>
    Module.Finite.of_injective ((W i).restrictScalars k).subtype Subtype.val_injective
  haveI hWfinA : ∀ i, Module.Finite A (W i) := fun i =>
    Module.Finite.of_restrictScalars_finite k A (W i)
  -- each `Wᵢ ≃ₗ[A]` some `P (g i)`.
  have hWiso : ∀ i, ∃ j, Nonempty ((W i) ≃ₗ[A] P j) := fun i =>
    indecProjective_iso_some_P M hM_complete P hP_indec hP_cover (W i) (hW_indec i)
  choose g hg using hWiso
  refine ⟨fun j => (Finset.univ.filter (fun i => g i = j)).card, ?_⟩
  rw [homClassVector_congr P e, homClassVector_directSum P (fun i => (W i))]
  funext l
  rw [Finset.sum_apply]
  have step : ∀ i, homClassVector (k := k) (A := A) P (W i) l = C l (g i) := by
    intro i
    rw [homClassVector_congr P (hg i).some, homClassVector_proj_eq_cartan_col]
  simp_rw [step]
  -- `∑ i, C l (g i) = ∑ j, C l j * (a j)` by fibering over `g`.
  simp only [Matrix.mulVec, dotProduct]
  have hRHS : ∀ j : ι,
      C l j * ((Finset.univ.filter (fun i => g i = j)).card : ℤ)
        = ∑ i ∈ Finset.univ.filter (fun i => g i = j), C l (g i) := by
    intro j
    rw [Finset.sum_congr rfl
      (fun i hi => (by rw [(Finset.mem_filter.mp hi).2] : C l (g i) = C l j))]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hRHS]
  rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (g i)) (fun i => C l (g i))]

end DirectSum

/-- A simple module over any ring is cyclic, hence finitely generated: any nonzero element
generates a nonzero submodule, which by simplicity is everything. -/
private theorem simpleModule_finite {A : Type*} [Ring A] (N : Type*) [AddCommGroup N]
    [Module A N] [IsSimpleModule A N] : Module.Finite A N := by
  haveI := IsSimpleModule.nontrivial A N
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hspan : Submodule.span A {x} = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span A {x}) with h | h
    · rw [Submodule.span_singleton_eq_bot] at h; exact absurd h hx
    · exact h
  exact Module.finite_def.mpr ⟨{x}, by rw [Finset.coe_singleton]; exact hspan⟩

/-- **Euler-characteristic induction for Problem 9.4.5 (i).** In the §9.3/§9.4.5 setup (a complete
family `M` of simple modules with indecomposable projective covers `P`), every finitely generated
`A`-module `N` of finite projective dimension `≤ d` has class vector `homClassVector P N` lying in
the `ℤ`-column span of the Cartan matrix `C`: `homClassVector P N = C.mulVec e` for some
`e : ι → ℤ`.

The proof is induction on `d`. The base case `d = 0` is `N` projective, handled by
`homClassVector_projective_eq_mulVec`. The step takes a finite free cover `Aⁿ ↠ N`
(`Module.Finite.exists_fin'`) with kernel `K = ker f`; the syzygy sequence `0 → K → Aⁿ → N → 0`
(`LinearMap.shortExact_shortComplexKer`) has projective middle term, so `K` has projective
dimension `≤ d` (`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`). Additivity of the
class vector on this short exact sequence (`homClassVector_add_quotient`, with `Aⁿ ⧸ K ≃ₗ[A] N`)
gives `homClassVector P N = homClassVector P Aⁿ − homClassVector P K = C.mulVec a₀ − C.mulVec eₖ`,
so `e := a₀ − eₖ` works. -/
private theorem homClassVector_eq_mulVec_of_projectiveDimensionLE
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (d : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
      [SMulCommClass A k N] [Module.Finite k N],
      HasProjectiveDimensionLE (ModuleCat.of A N) d →
      ∃ e : ι → ℤ,
        homClassVector (k := k) (A := A) P N =
          ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec e := by
  haveI : ∀ i, Module.Finite k (P i) := fun i => Module.Finite.trans A (P i)
  induction d with
  | zero =>
    intro N _ _ _ _ _ _ hpd
    haveI hproj : Projective (ModuleCat.of A N) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).mpr hpd
    haveI : Module.Projective A N := ModuleCat.projective_of_module_projective (ModuleCat.of A N)
    haveI : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    obtain ⟨a, ha⟩ := homClassVector_projective_eq_mulVec M hM_complete P hP_indec hP_cover N
    exact ⟨fun i => (a i : ℤ), ha⟩
  | succ d ih =>
    intro N _ _ _ _ _ _ hpd
    haveI : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
    -- Finite free cover `Aⁿ ↠ N` with kernel `K = ker f`, and the syzygy short exact sequence.
    haveI : Module.Projective A (Fin n → A) := Module.Projective.of_basis (Pi.basisFun A (Fin n))
    haveI : Module.Finite k (Fin n → A) := inferInstance
    haveI : Module.Finite k (LinearMap.ker f) :=
      Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars k)
        (LinearMap.ker f).injective_subtype
    have hSE := LinearMap.shortExact_shortComplexKer hf
    have hKpd : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) d :=
      (hSE.hasProjectiveDimensionLT_X₃_iff d (inferInstance : Projective (ModuleCat.of A _))).mp hpd
    obtain ⟨eK, hKvec⟩ := ih (LinearMap.ker f) hKpd
    obtain ⟨a0, ha0⟩ :=
      homClassVector_projective_eq_mulVec M hM_complete P hP_indec hP_cover (Fin n → A)
    -- Class-vector additivity on `0 → K → Aⁿ → N → 0`, with `Aⁿ ⧸ K ≃ₗ[A] N`.
    have hadd := homClassVector_add_quotient (k := k) (A := A) P (Fin n → A) (LinearMap.ker f)
    rw [homClassVector_congr P (f.quotKerEquivOfSurjective hf)] at hadd
    refine ⟨(fun i => (a0 i : ℤ)) - eK, ?_⟩
    rw [Matrix.mulVec_sub, ← ha0, ← hKvec, hadd]
    abel

/-- **Problem 9.4.5 (i).** If the finite dimensional algebra `A` has finite homological
dimension, then the determinant of its Cartan matrix `C` is `±1`.

The Cartan matrix `Etingof.algebraCartanMatrix P` (Definition 9.3.1) is built from the family
`P` of projective covers of the simple modules; its `ℕ`-entries are cast to `ℤ` to take the
determinant. The hypotheses fix `M` as a complete, irredundant family of simple `A`-modules
and `P i` as the indecomposable projective cover of `M i` (encoded by the essential-cover
identity `dim_k Hom_A(Pᵢ, Mⱼ) = δᵢⱼ`), so that `C` is the change-of-basis matrix in
`K₀` between the simples `[Mᵢ]` and the projective indecomposables `[Pᵢ]`. -/
theorem cartan_det_eq_pm_one
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
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
  -- By the right-inverse lemma above, it suffices to express each standard basis vector `eⱼ` in
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
  -- so `d := Σₖ (-1)ᵏ aₖ` is the required integer vector. Finite homological dimension gives some
  -- `d₀` bounding every module's projective dimension;
  -- `homClassVector_eq_mulVec_of_projectiveDimensionLE` packages the Euler-characteristic
  -- induction over such a finite resolution.
  obtain ⟨d₀, hd₀⟩ : ∃ d, Etingof.HasHomologicalDimensionLE A d := by
    by_contra h
    rw [not_exists] at h
    exact hfin (Etingof.homologicalDimension_eq_top h)
  haveI : Module.Finite A (M j) := simpleModule_finite (M j)
  haveI : Module.Finite k (M j) := Module.Finite.trans A (M j)
  obtain ⟨e, he⟩ := homClassVector_eq_mulVec_of_projectiveDimensionLE M hM_complete P hP_indec
    hP_cover d₀ (M j) (hd₀ (ModuleCat.of A (M j)))
  exact ⟨e, he.symm⟩

/-- **Problem 9.4.5 (ii), first algebra.** For `n > 1`, the truncated polynomial algebra
`k[t]/tⁿ` has infinite homological dimension. -/
theorem homologicalDimension_polynomial_quotient_eq_top
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    Etingof.homologicalDimension (k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ n}) = ⊤ :=
  Etingof.TruncatedPoly.homologicalDimension_eq_top_truncated k n hn

open Etingof.Problem932 in
/-- **Dimension shift (non-vanishing step).** For a short exact sequence
`0 → S.X₁ → S.X₂ → S.X₃ → 0` of `A`-modules with projective middle term `S.X₂`, precomposition
with the extension class is injective on `Extⁱ(S.X₁, Y)` for `i ≥ 1`: it sends a nonzero class
to a nonzero class in `Extⁱ⁺¹(S.X₃, Y)`. This is the contravariant `Ext` long exact sequence
together with the vanishing of `Extⁱ(S.X₂, Y)` for `i ≥ 1`. -/
private theorem ext_extClass_comp_ne_zero
    {S : ShortComplex (ModuleCat.{0} Etingof.Problem932.A)} (hS : S.ShortExact)
    (hP : Projective S.X₂) {Y : ModuleCat.{0} Etingof.Problem932.A} {i : ℕ} (hi : 1 ≤ i)
    (e : Abelian.Ext S.X₁ Y i) (he : e ≠ 0) {n : ℕ} (hn : 1 + i = n) :
    hS.extClass.comp e hn ≠ 0 := by
  haveI := hP
  intro hzero
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y e hn hzero
  have hx₂0 : x₂ = 0 := Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x₂ 1 hi
  rw [hx₂0, Abelian.Ext.comp_zero] at hx₂
  exact he hx₂.symm

open Etingof.Problem932 in
/-- **2-periodic non-vanishing.** `Ext^{2j+1}(S₊, S₋) ≠ 0` for every `j`. The base case is the
nonsplit extension `Ext¹(S₊, S₋) ≠ 0` (`extClass_ne_zero`); the inductive step composes the
extension classes of the two short exact sequences `0 → S₊ → P₋ → S₋ → 0` and
`0 → S₋ → P₊ → S₊ → 0`, whose middle terms `P₋`, `P₊` are projective. -/
private theorem ext_odd_ne_zero (j : ℕ) :
    ∃ e : Abelian.Ext (ModuleCat.of Etingof.Problem932.A Etingof.Problem932.Splus)
      (ModuleCat.of Etingof.Problem932.A Etingof.Problem932.Sminus) (2 * j + 1), e ≠ 0 := by
  induction j with
  | zero => exact ⟨ses_shortExact.extClass, extClass_ne_zero⟩
  | succ j ih =>
    obtain ⟨e, he⟩ := ih
    have hPm : Projective sesm.X₂ := projective_sesm_X₂
    have hPp : Projective ses.X₂ := projective_ses_X₂
    have h1 := ext_extClass_comp_ne_zero sesm_shortExact hPm (i := 2 * j + 1) (by omega) e he
      (n := 2 * j + 2) (by ring)
    exact ⟨_, ext_extClass_comp_ne_zero ses_shortExact hPp (i := 2 * j + 2) (by omega) _ h1
      (n := 2 * (j + 1) + 1) (by ring)⟩

/-- **Problem 9.4.5 (ii), second algebra.** The four dimensional algebra
`A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 has infinite homological dimension.

`S₊` has infinite projective dimension: `Ext^{2d+1}(S₊, S₋) ≠ 0` for every `d`
(`ext_odd_ne_zero`), so `S₊` cannot have projective dimension `≤ d`, and no `d` bounds the
homological dimension of `A`. -/
theorem homologicalDimension_problem932_eq_top :
    Etingof.homologicalDimension Etingof.Problem932.A = ⊤ := by
  refine Etingof.homologicalDimension_eq_top_of_forall (fun d hd => ?_)
  obtain ⟨e, he⟩ := ext_odd_ne_zero d
  haveI hpd : HasProjectiveDimensionLE
      (ModuleCat.of Etingof.Problem932.A Etingof.Problem932.Splus) d := hd _
  exact he (Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e (d + 1) (by omega))

end Etingof.Problem945
