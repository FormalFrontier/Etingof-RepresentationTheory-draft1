import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.ENat.Lattice
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.Problem9_3_2

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
into `ℤ`. Part (ii) records the two concrete values as `homologicalDimension = ⊤`. Proofs are
deferred (`sorry`).
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

/-- **Problem 9.4.5 (i).** If the finite dimensional algebra `A` has finite homological
dimension, then the determinant of its Cartan matrix `C` is `±1`. The Cartan matrix
`Etingof.algebraCartanMatrix P` (Definition 9.3.1) is built from the family `P` of projective
covers of the simple modules; its `ℕ`-entries are cast to `ℤ` to take the determinant. -/
theorem cartan_det_eq_pm_one
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (hfin : Etingof.homologicalDimension A ≠ ⊤) :
    ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = 1 ∨
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = -1 := by
  sorry

/-- **Problem 9.4.5 (ii), first algebra.** For `n > 1`, the truncated polynomial algebra
`k[t]/tⁿ` has infinite homological dimension. -/
theorem homologicalDimension_polynomial_quotient_eq_top
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    Etingof.homologicalDimension (k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ n}) = ⊤ := by
  sorry

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
