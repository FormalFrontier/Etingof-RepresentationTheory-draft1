import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import EtingofRepresentationTheory.Chapter9.Definition9_4_1

/-!
# Problem 9.4.2: Projective dimension via Ext, and dimension shifting

Etingof Problem 9.4.2 collects three facts about projective dimension `pd(M)` of a left
`A`-module `M`.

* **(i)** `pd(M) ≤ d` if and only if `Extⁱ(M, N) = 0` for all `i > d` and all left modules `N`.
  (Hint: induction on `d` and the long exact sequence of Ext groups.)

* **(ii)** If `0 → M → P → N → 0` is a *nonsplit* short exact sequence with `P` projective,
  then `pd(N) = pd(M) + 1`.

* **(iii)** If `pd(M) = d > 0` and `P_•` is any projective resolution of `M`, then the
  syzygy `K_d = ker(P_{d-1} → P_{d-2})` is projective; so the resolution can be truncated to
  length `d`. (Its one-step mechanism is dimension shifting: for a projective presentation
  `0 → K → P → M → 0`, the syzygy `K` satisfies `pd(K) = pd(M) - 1` when `pd(M) > 0`.)

## Statement-pass note

We work in `ModuleCat R` for a ring `R` (left `R`-modules). Part (i) is the defining Ext
characterization of `HasProjectiveDimensionLE`: `HasProjectiveDimensionLE M d` unfolds to
`HasProjectiveDimensionLT M (d+1)`, i.e. vanishing of `Extⁱ(M, N)` for `d < i`, which is
exactly "`Extⁱ(M, N) = 0` for `i > d`". Parts (ii) and (iii) are stated with
`CategoryTheory.ShortComplex.ShortExact` short exact sequences; "nonsplit" is `IsEmpty` of the
splitting type. All three parts are proved by reduction to the Mathlib
`HasProjectiveDimensionLT`/`Ext` API and the short-exact dimension-shifting lemmas
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`/`hasProjectiveDimensionLT_X₃_iff`.
-/

universe u

open CategoryTheory

namespace Etingof.Problem942

variable (R : Type u) [Ring R]

/-- **Problem 9.4.2 (i).** `pd(M) ≤ d` if and only if `Extⁱ(M, N) = 0` for every left module
`N` and every `i > d`. Here `pd(M) ≤ d` is `HasProjectiveDimensionLE M d`, and `Extⁱ(M, N) = 0`
is `Subsingleton (Abelian.Ext M N i)` (the group `Extⁱ(M, N)` is trivial). -/
theorem hasProjectiveDimensionLE_iff_ext_vanishing (M : ModuleCat.{u} R) (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∀ (N : ModuleCat.{u} R) (i : ℕ), d < i → Subsingleton (Abelian.Ext M N i) := by
  constructor
  · intro h N i hi
    haveI : HasProjectiveDimensionLT M (d + 1) := h
    exact HasProjectiveDimensionLT.subsingleton M (d + 1) i (by omega) N
  · intro h
    apply HasProjectiveDimensionLT.mk
    intro i hi Y e
    exact (h Y i (by omega)).elim e 0

/-- **Problem 9.4.2 (ii).** For a nonsplit short exact sequence `0 → M → P → N → 0` with `P`
projective, the projective dimension of `N` is one more than that of `M`:
`pd(N) = pd(M) + 1`. In the `ShortComplex` `S`, `M = S.X₁`, `P = S.X₂`, `N = S.X₃`. -/
theorem projectiveDimension_succ_of_nonsplit
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hP : Projective S.X₂) (hns : IsEmpty S.Splitting) :
    Etingof.projectiveDimension R S.X₃ = Etingof.projectiveDimension R S.X₁ + 1 := by
  haveI : Projective S.X₂ := hP
  -- A nonsplit sequence with `S.X₂` projective forces `S.X₃` to be non-projective and
  -- both `S.X₁`, `S.X₃` to be nonzero (else the sequence would split).
  have hX3proj : ¬ Projective S.X₃ := fun h => by
    haveI := h; exact hns.false hS.splittingOfProjective
  have hX3ne : ¬ Limits.IsZero S.X₃ := fun h => hX3proj h.projective
  have hX1ne : ¬ Limits.IsZero S.X₁ := fun h => by
    haveI := h.injective; exact hns.false hS.splittingOfInjective
  change CategoryTheory.projectiveDimension S.X₃ = CategoryTheory.projectiveDimension S.X₁ + 1
  have aux (n : ℕ) : CategoryTheory.projectiveDimension S.X₃ ≤ (n : WithBot ℕ∞) ↔
      CategoryTheory.projectiveDimension S.X₁ + 1 ≤ (n : WithBot ℕ∞) := by
    match n with
    | 0 =>
      rw [projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero,
        Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff]
      exact iff_of_false hX3proj hX1ne
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      simp only [ENat.WithBot.add_le_add_natCast_right_iff, projectiveDimension_le_iff]
      exact hS.hasProjectiveDimensionLT_X₃_iff n hP
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, WithBot.add_eq_bot, WithBot.one_ne_bot,
      or_false]
    exact iff_of_false hX3ne hX1ne
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

/-- **Problem 9.4.2 (iii), dimension shifting.** Given a projective presentation
`0 → K → P → M → 0` (short exact with `P` projective), if `pd(M) ≤ d` with `0 < d`, then the
syzygy `K` satisfies `pd(K) ≤ d - 1`. Iterating this `d` times shows that the `d`-th syzygy
`K_d` of a module with `pd(M) = d` is projective (`pd = 0`), which is the content of (iii):
here `M = S.X₃`, `P = S.X₂`, `K = S.X₁`. -/
theorem hasProjectiveDimensionLE_syzygy
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hP : Projective S.X₂) (d : ℕ) (hd : 0 < d)
    (hM : HasProjectiveDimensionLE S.X₃ d) :
    HasProjectiveDimensionLE S.X₁ (d - 1) := by
  haveI : Projective S.X₂ := hP
  haveI : HasProjectiveDimensionLT S.X₂ d :=
    hasProjectiveDimensionLT_of_ge S.X₂ 1 d hd
  have h : HasProjectiveDimensionLT S.X₁ d :=
    hS.hasProjectiveDimensionLT_X₁ d inferInstance hM
  change HasProjectiveDimensionLT S.X₁ (d - 1 + 1)
  rwa [Nat.sub_add_cancel hd]

end Etingof.Problem942
