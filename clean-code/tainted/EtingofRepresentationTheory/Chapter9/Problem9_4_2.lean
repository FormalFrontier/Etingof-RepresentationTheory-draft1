import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import EtingofRepresentationTheory.Chapter7.Example7_7_2
import EtingofRepresentationTheory.Chapter9.Definition9_4_1
import EtingofRepresentationTheory.Chapter9.FiniteProjectiveResolution
import EtingofRepresentationTheory.Chapter9.ProjectiveResolutionSyzygy

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
open scoped ModuleCat

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
  -- On the nonzero modules `S.X₁`, `S.X₃` the book projective dimension agrees with the raw
  -- Mathlib value, so the book statement reduces to the raw dimension-shifting identity.
  rw [Etingof.projectiveDimension_eq_raw_of_not_isZero S.X₃ hX3ne,
    Etingof.projectiveDimension_eq_raw_of_not_isZero S.X₁ hX1ne]
  change CategoryTheory.projectiveDimension S.X₃ = CategoryTheory.projectiveDimension S.X₁ + 1
  have aux (n : ℕ) : CategoryTheory.projectiveDimension S.X₃ ≤ (n : WithBot ℕ∞) ↔
      CategoryTheory.projectiveDimension S.X₁ + 1 ≤ (n : WithBot ℕ∞) := by
    match n with
    | 0 =>
      rw [CategoryTheory.projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero,
        Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff]
      exact iff_of_false hX3proj hX1ne
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      simp only [ENat.WithBot.add_le_add_natCast_right_iff,
        CategoryTheory.projectiveDimension_le_iff]
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

open Etingof.ProjectiveResolution in
/-- **Problem 9.4.2 (iii), the arbitrary-resolution statement.** Let `M` be a left `R`-module
with `pd(M) ≤ d`, and let `P` be *any* projective resolution of `M`. Then the `d`-th syzygy
`Ω^d M = syzygy P d` (the kernel `K_d = ker(P_{d-1} → P_{d-2})`, with the convention `P_{-1} = M`)
is projective.

The proof iterates the one-step dimension shift `hasProjectiveDimensionLE_syzygy` along the
syzygy short exact sequences `0 → Ωⁿ⁺¹M → Pₙ → ΩⁿM → 0` (all short exact with projective middle
term, from `syzygySES_shortExact`): by induction `pd(ΩⁿM) ≤ d - n` for `n ≤ d`, and at `n = d`
this reads `pd(Ω^d M) ≤ 0`, i.e. `Ω^d M` is projective. -/
theorem projective_syzygy_of_hasProjectiveDimensionLE
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (d : ℕ)
    (hM : HasProjectiveDimensionLE M d) :
    Projective (syzygy P d) := by
  -- Iterated dimension shift: the `n`-th syzygy has projective dimension `≤ d - n`.
  have key : ∀ n, n ≤ d → HasProjectiveDimensionLE (syzygy P n) (d - n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hM
    | succ n ih =>
      intro hn
      have hpos : 0 < d - n := by omega
      -- Apply the one-step shift to `syzygySES P n : 0 → Ωⁿ⁺¹M → Pₙ → ΩⁿM → 0`.
      have hstep := hasProjectiveDimensionLE_syzygy R (syzygySES P n)
        (syzygySES_shortExact P n) inferInstance (d - n) hpos
        (by rw [syzygySES_X₃]; exact ih (by omega))
      -- `(syzygySES P n).X₁ = syzygy P (n+1)` and `d - n - 1 = d - (n+1)`.
      simpa only [syzygySES_X₁, Nat.sub_sub] using hstep
  have hd0 := key d (le_refl d)
  rw [Nat.sub_self] at hd0
  rw [projective_iff_hasProjectiveDimensionLE_zero]
  exact hd0

open Etingof.ProjectiveResolution in
/-- **Problem 9.4.2 (iii), truncated projective resolution.** For a module `M` of projective
dimension `≤ d` and *any* projective resolution `P`, the resolution truncates to length `d`.

This packages the truncated exact sequence `0 → Ω^d M → P_{d-1} → ⋯ → P₀ → M → 0`: the syzygy
short exact sequences `0 → Ωⁿ⁺¹M → Pₙ → ΩⁿM → 0` for `n < d` splice along their common syzygy
terms, the bottom syzygy is `Ω⁰ M = M` (`syzygy_zero`), and the top term `Ω^d M = syzygy P d`
is projective (so, replacing `P_d` by `K_d = Ω^d M` and everything to its left by `0`, we obtain
a genuine projective resolution of `M` of length `d`). -/
theorem truncated_projective_resolution
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (d : ℕ)
    (hM : HasProjectiveDimensionLE M d) :
    Projective (syzygy P d) ∧ syzygy P 0 = M ∧ ∀ n, (syzygySES P n).ShortExact :=
  ⟨projective_syzygy_of_hasProjectiveDimensionLE R M P d hM, syzygy_zero P,
    syzygySES_shortExact P⟩

/-!
## Finite-dimensional refinement of Problem 9.4.2(iii)

The final clause of Problem 9.4.2(iii) states that when the algebra `A` and the module `M`
are finite dimensional, the truncated resolution can be chosen with finite-dimensional terms.

Over a left-Noetherian ring `R`, the key step is that every syzygy of a finitely generated
module stays finitely generated: each `Ωⁿ⁺¹ M = ker(Pₙ ↠ Ωⁿ M)` embeds into the finitely
generated module `Pₙ`, and a submodule of a finitely generated module over a Noetherian ring is
again finitely generated. Finite generation over a finite-dimensional algebra is exactly finite
dimensionality over the ground field (`finite_of_finiteDimensional_algebra`), so combining the
syzygy-finiteness with the truncation yields a length-`d` resolution
`0 → Ω^d M → P_{d-1} → ⋯ → P₀ → M → 0` all of whose terms are finite dimensional.

The remaining input — that a finitely generated module over a left-Noetherian ring admits a
projective resolution whose terms are finitely generated (a resolution by finitely generated
free modules) — is a separate construction; the results here propagate finiteness through any
such resolution and package the truncation.
-/

open Etingof.ProjectiveResolution in
/-- **Syzygies of a finitely generated module stay finitely generated.** Let `R` be a left
Noetherian ring, `M` a finitely generated left `R`-module, and `P` a projective resolution of `M`
all of whose terms `Pₙ = P.complex.X n` are finitely generated. Then every syzygy
`Ωⁿ M = syzygy P n` is finitely generated.

The bottom syzygy is `Ω⁰ M = M`, which is finitely generated by hypothesis; the inductive step
uses that `Ωⁿ⁺¹ M` is (via the mono `(syzygySES P n).f`) a submodule of the finitely generated
module `Pₙ`, and a submodule of a finitely generated module over a Noetherian ring is finitely
generated (`Module.Finite.of_injective`). -/
theorem finite_syzygy [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hM : Module.Finite R ↥M) (hP : ∀ n, Module.Finite R ↥(P.complex.X n)) :
    ∀ n, Module.Finite R ↥(syzygy P n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    -- `Ωⁿ⁺¹ M = (syzygySES P n).X₁` is a submodule of `Pₙ = (syzygySES P n).X₂`.
    haveI : Module.Finite R ↥((syzygySES P n).X₂) := by rw [syzygySES_X₂]; exact hP n
    have hinj : Function.Injective (syzygySES P n).f :=
      (ModuleCat.mono_iff_injective _).1 (syzygySES_shortExact P n).mono_f
    have hfin : Module.Finite R ↥(syzygy P (n + 1)) := by
      have := Module.Finite.of_injective (syzygySES P n).f.hom hinj
      simpa only [syzygySES_X₁] using this
    exact hfin

open Etingof.ProjectiveResolution in
/-- **Problem 9.4.2(iii), finite-dimensional truncation.** For a finitely generated module `M`
over a left-Noetherian ring `R` with `pd(M) ≤ d`, and *any* projective resolution `P` of `M`
whose terms are finitely generated, the truncated resolution
`0 → Ω^d M → P_{d-1} → ⋯ → P₀ → M → 0` has finitely generated terms:

* the top syzygy `Ω^d M = syzygy P d` is projective (so the resolution truncates at length `d`);
* every syzygy `Ωⁿ M` — in particular the truncation term `Ω^d M` — is finitely generated;
* the bottom syzygy is `Ω⁰ M = M`, and the syzygy short exact sequences splice the truncation.

Over a finite-dimensional algebra, finite generation is finite dimensionality over the ground
field (`finite_of_finiteDimensional_algebra`), which is the book's finite-dimensional
conclusion. -/
theorem finite_truncated_projective_resolution [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hM : Module.Finite R ↥M) (hP : ∀ n, Module.Finite R ↥(P.complex.X n))
    (d : ℕ) (hd : HasProjectiveDimensionLE M d) :
    Projective (syzygy P d) ∧ (∀ n, Module.Finite R ↥(syzygy P n)) ∧
      syzygy P 0 = M ∧ ∀ n, (syzygySES P n).ShortExact :=
  ⟨projective_syzygy_of_hasProjectiveDimensionLE R M P d hd,
    finite_syzygy R M P hM hP, syzygy_zero P, syzygySES_shortExact P⟩

/-- **Finite generation over a finite-dimensional algebra is finite dimensionality.** If `R` is a
finite-dimensional algebra over a field (more generally a commutative ring) `k`, i.e.
`Module.Finite k R`, then a finitely generated `R`-module `N` is finitely generated — hence, over
a field, finite dimensional — over `k`. This is the step "f.g. over a finite-dimensional algebra
⟹ finite dimensional over `k`" used to translate the syzygy-finiteness of
`finite_syzygy`/`finite_truncated_projective_resolution` into the book's finite-dimensional
statement. -/
theorem finite_of_finiteDimensional_algebra {k : Type*} [CommRing k] [Algebra k R]
    [Module.Finite k R] (N : Type*) [AddCommGroup N] [Module R N] [Module k N]
    [IsScalarTower k R N] [Module.Finite R N] : Module.Finite k N :=
  Module.Finite.trans R N

/-- **Problem 9.4.2(iii), finite-dimensional conclusion.** If `R` is a finite-dimensional
algebra over a field `k`, `M` is finite dimensional over `k`, and `pd(M) ≤ d`, then one can
choose a projective resolution with finite-dimensional terms and truncate it at degree `d`.

The returned data are the source's finite resolution: the finite-dimensional projective terms
`P₀, …, P_{d-1}`, the finite-dimensional projective top syzygy `Ω^d M`, and the short exact
syzygy sequences that splice them into a length-`d` resolution of `M`. -/
theorem exists_finiteDimensional_truncated_projective_resolution
    {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
    (M : ModuleCat.{u} R) [Module k M] [IsScalarTower k R M] [Module.Finite k M]
    (d : ℕ) (hd : HasProjectiveDimensionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ n, Module.Finite k ↥(P.complex.X n)) ∧
      Projective (Etingof.ProjectiveResolution.syzygy P d) ∧
      Module.Finite k ↥(Etingof.ProjectiveResolution.syzygy P d) ∧
      Etingof.ProjectiveResolution.syzygy P 0 = M ∧
      ∀ n, (Etingof.ProjectiveResolution.syzygySES P n).ShortExact := by
  letI : IsNoetherianRing R := isNoetherianRing_of_finiteDimensional k R
  letI : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  obtain ⟨P, hP⟩ :=
    Etingof.FiniteProjectiveResolution.exists_finite_projectiveResolution M
  have hPk : ∀ n, Module.Finite k ↥(P.complex.X n) := by
    intro n
    exact Module.Finite.trans R (P.complex.X n)
  obtain ⟨hproj, hsyzygy, hzero, hses⟩ :=
    finite_truncated_projective_resolution R M P inferInstance hP d hd
  have htop : Module.Finite k ↥(Etingof.ProjectiveResolution.syzygy P d) := by
    letI : Module.Finite R ↥(Etingof.ProjectiveResolution.syzygy P d) := hsyzygy d
    exact Module.Finite.trans R
      ↥(Etingof.ProjectiveResolution.syzygy (C := ModuleCat R) P d)
  exact ⟨P, hPk, hproj, htop, hzero, hses⟩

end Etingof.Problem942
