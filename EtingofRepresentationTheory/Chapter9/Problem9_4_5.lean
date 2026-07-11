import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.ENat.Lattice
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
  -- Book argument. In `K₀(A)`, the classes `[Mⱼ]` of the simples and `[Pᵢ]` of the projective
  -- indecomposables are two bases of the free abelian group `ℤ^ι`. The Cartan matrix `C`
  -- expresses `[Pⱼ] = Σᵢ Cᵢⱼ [Mᵢ]` (its columns are the composition-multiplicity vectors,
  -- Proposition 9.2.3). Finite homological dimension (`hfin`) gives each simple `Mⱼ` a finite
  -- projective resolution `0 → Q_d → … → Q₀ → Mⱼ → 0` with each `Q_k` a finitely generated
  -- projective, hence (Krull–Schmidt) a direct sum of the `Pᵢ`. Additivity of the class
  -- function on short exact sequences gives `[Mⱼ] = Σₖ (-1)ᵏ [Q_k] = Σᵢ Dᵢⱼ [Pᵢ]` with an
  -- **integer** matrix `D` (the Euler characteristic). Substituting shows `C * D = 1`.
  -- Producing this `D` needs a `K₀`/Euler-characteristic invariant that does not yet exist in
  -- the project; it is deferred to a dedicated sub-issue (see the PR description).
  sorry

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
