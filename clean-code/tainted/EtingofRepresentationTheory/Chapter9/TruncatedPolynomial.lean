import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionReduction
import EtingofRepresentationTheory.Chapter9.Problem9_4_2

/-!
# Infinite homological dimension of `k[t]/tⁿ` (`n > 1`)

For a field `k` and `n > 1`, the truncated polynomial algebra `R = k[X]/(Xⁿ)` has
**infinite** homological dimension (Problem 9.4.5 (ii), first algebra).

## Strategy

`R` is self-injective and non-semisimple; the residue module has a `2`-periodic minimal
free resolution. Concretely, write `t` for the image of `X` in `R`, and consider the two
cyclic modules

* `A = (t)   = range(·t : R → R)`,
* `B = (tⁿ⁻¹) = range(·tⁿ⁻¹ : R → R)`.

Multiplication by `t` and by `tⁿ⁻¹` gives two short exact sequences (using that `R` is free,
hence projective, and `Ann(t) = (tⁿ⁻¹)`, `Ann(tⁿ⁻¹) = (t)`):

* `0 → B → R → A → 0`   (`·t`),
* `0 → A → R → B → 0`   (`·tⁿ⁻¹`).

By dimension shifting (`Etingof.Problem942.hasProjectiveDimensionLE_syzygy`) `pd(A) ≤ d`
(`d > 0`) forces `pd(B) ≤ d - 1`, and symmetrically. Since neither `A` nor `B` is projective
(a splitting would force `tⁿ⁻¹ = 0`), a symmetric induction shows `pd(A) = pd(B) = ∞`, so `A`
witnesses `¬ HasHomologicalDimensionLE R d` for every `d`, whence
`homologicalDimension R = ⊤` by `Etingof.homologicalDimension_eq_top`.
-/

universe u

open Polynomial CategoryTheory

namespace Etingof.TruncatedPoly

variable (k : Type u) [Field k] (n : ℕ)

/-- The truncated polynomial algebra `R = k[X]/(Xⁿ)`. -/
abbrev Rq : Type u := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

/-- The image `t` of `X` in `R = k[X]/(Xⁿ)`. -/
noncomputable def tq : Rq k n := Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) X

/-- `tⁿ = 0` in `R = k[X]/(Xⁿ)`. -/
theorem tq_pow_n : (tq k n) ^ n = 0 := by
  rw [tq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- `tⁿ⁻¹ ≠ 0` in `R = k[X]/(Xⁿ)` (for `n ≥ 1`). -/
theorem tq_pow_pred_ne (hn : 0 < n) : (tq k n) ^ (n - 1) ≠ 0 := by
  rw [tq, ← map_pow]
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  -- h : X^n ∣ X^(n-1)
  have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have := Polynomial.natDegree_le_of_dvd h hne
  simp only [Polynomial.natDegree_X_pow] at this
  omega

/-- `Ann(t) = (tⁿ⁻¹)`: the kernel of `·t` equals the range of `·tⁿ⁻¹`. -/
theorem ker_mulLeft_t (hn : 0 < n) :
    LinearMap.ker (LinearMap.mulLeft (Rq k n) (tq k n)) =
      LinearMap.range (LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1))) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (tq k n) * (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p)
        = Ideal.Quotient.mk _ (X * p) := by rw [tq]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X * X ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    rw [hsplit, mul_dvd_mul_iff_left (Polynomial.X_ne_zero)] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, tq, ← map_pow, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ', show (n - 1) + 1 = n by omega, tq_pow_n, zero_mul]

/-- `Ann(tⁿ⁻¹) = (t)`: the kernel of `·tⁿ⁻¹` equals the range of `·t`. -/
theorem ker_mulLeft_t_pow (hn : 0 < n) :
    LinearMap.ker (LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1))) =
      LinearMap.range (LinearMap.mulLeft (Rq k n) (tq k n)) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (tq k n) ^ (n - 1) * (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p)
        = Ideal.Quotient.mk _ (X ^ (n - 1) * p) := by
      rw [tq, ← map_pow]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X ^ (n - 1) * X := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    rw [hsplit, mul_dvd_mul_iff_left hne] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, tq, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ, show (n - 1) + 1 = n by omega, tq_pow_n, zero_mul]

/-- `tⁿ⁻¹ · tⁿ⁻¹ = 0` for `n > 1` (since `2(n-1) ≥ n`). -/
theorem tq_pow_pred_mul_self (hn : 1 < n) :
    (tq k n) ^ (n - 1) * (tq k n) ^ (n - 1) = 0 := by
  rw [← pow_add]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show n ≤ (n - 1) + (n - 1) by omega)
  rw [hm, pow_add, tq_pow_n, zero_mul]

/-- The cyclic module `A = (t) = range(·t)` is not projective over `R = k[X]/(Xⁿ)` (`n > 1`).
A splitting section `σ` of `·t : R ↠ (t)` would give `e = σ(t)` with `t·e = t` and
`tⁿ⁻¹·e = 0`; multiplying the first by `tⁿ⁻²` yields `tⁿ⁻¹·e = tⁿ⁻¹`, forcing `tⁿ⁻¹ = 0`. -/
theorem not_projective_A (hn : 1 < n) :
    ¬ Projective (ModuleCat.of (Rq k n)
      ↥(LinearMap.range (LinearMap.mulLeft (Rq k n) (tq k n)))) := by
  letI : Small.{u} (Rq k n) := ⟨⟨Rq k n, ⟨Equiv.refl _⟩⟩⟩
  intro hProj
  set ft := LinearMap.mulLeft (Rq k n) (tq k n) with hft
  haveI : Projective (ModuleCat.of (Rq k n) ↥(LinearMap.range ft)) := hProj
  haveI : Module.Projective (Rq k n) ↥(LinearMap.range ft) :=
    (IsProjective.iff_projective _).mpr hProj
  have hy0mem : (tq k n) ∈ LinearMap.range ft :=
    LinearMap.mem_range.mpr ⟨1, by rw [hft, LinearMap.mulLeft_apply, mul_one]⟩
  set y₀ : ↥(LinearMap.range ft) := ⟨tq k n, hy0mem⟩ with hy0
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ft.rangeRestrict
    (LinearMap.id) ft.surjective_rangeRestrict
  set e := σ y₀ with he_def
  have hgen : (tq k n) * e = tq k n := by
    have h1 := LinearMap.congr_fun hσ y₀
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h1
    have h2 : ft e = tq k n := congrArg Subtype.val h1
    rwa [hft, LinearMap.mulLeft_apply] at h2
  have hann : (tq k n) ^ (n - 1) * e = 0 := by
    have hz : ((tq k n) ^ (n - 1)) • y₀ = 0 := by
      apply Subtype.ext
      change (tq k n) ^ (n - 1) • (tq k n) = (0 : Rq k n)
      rw [smul_eq_mul, ← pow_succ, show (n - 1) + 1 = n by omega, tq_pow_n]
    have hmap : ((tq k n) ^ (n - 1)) • e = σ (((tq k n) ^ (n - 1)) • y₀) := (map_smul σ _ _).symm
    rw [hz, map_zero] at hmap
    rw [← smul_eq_mul]; exact hmap
  apply tq_pow_pred_ne k n (by omega)
  have key : (tq k n) ^ (n - 1) * e = (tq k n) ^ (n - 1) := by
    have h3 : (tq k n) ^ (n - 2) * ((tq k n) * e) = (tq k n) ^ (n - 2) * (tq k n) := by rw [hgen]
    rw [← mul_assoc, ← pow_succ, show (n - 2) + 1 = n - 1 by omega] at h3
    exact h3
  rw [hann] at key
  exact key.symm

/-- The cyclic module `B = (tⁿ⁻¹) = range(·tⁿ⁻¹)` is not projective over `R = k[X]/(Xⁿ)`
(`n > 1`). A splitting section `σ` of `·tⁿ⁻¹ : R ↠ (tⁿ⁻¹)` would give `e = σ(tⁿ⁻¹)` with
`tⁿ⁻¹·e = tⁿ⁻¹` and `t·e = 0`; multiplying the second by `tⁿ⁻²` yields `tⁿ⁻¹·e = 0`,
forcing `tⁿ⁻¹ = 0`. -/
theorem not_projective_B (hn : 1 < n) :
    ¬ Projective (ModuleCat.of (Rq k n)
      ↥(LinearMap.range (LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1))))) := by
  letI : Small.{u} (Rq k n) := ⟨⟨Rq k n, ⟨Equiv.refl _⟩⟩⟩
  intro hProj
  set fs := LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1)) with hfs
  haveI : Projective (ModuleCat.of (Rq k n) ↥(LinearMap.range fs)) := hProj
  haveI : Module.Projective (Rq k n) ↥(LinearMap.range fs) :=
    (IsProjective.iff_projective _).mpr hProj
  have hy1mem : (tq k n) ^ (n - 1) ∈ LinearMap.range fs :=
    LinearMap.mem_range.mpr ⟨1, by rw [hfs, LinearMap.mulLeft_apply, mul_one]⟩
  set y₁ : ↥(LinearMap.range fs) := ⟨(tq k n) ^ (n - 1), hy1mem⟩ with hy1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property fs.rangeRestrict
    (LinearMap.id) fs.surjective_rangeRestrict
  set e := σ y₁ with he_def
  have hgen : (tq k n) ^ (n - 1) * e = (tq k n) ^ (n - 1) := by
    have h1 := LinearMap.congr_fun hσ y₁
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h1
    have h2 : fs e = (tq k n) ^ (n - 1) := congrArg Subtype.val h1
    rwa [hfs, LinearMap.mulLeft_apply] at h2
  have hann : (tq k n) * e = 0 := by
    have hz : (tq k n) • y₁ = 0 := by
      apply Subtype.ext
      change (tq k n) • (tq k n) ^ (n - 1) = (0 : Rq k n)
      rw [smul_eq_mul, ← pow_succ', show (n - 1) + 1 = n by omega, tq_pow_n]
    have hmap : (tq k n) • e = σ ((tq k n) • y₁) := (map_smul σ _ _).symm
    rw [hz, map_zero] at hmap
    rw [← smul_eq_mul]; exact hmap
  apply tq_pow_pred_ne k n (by omega)
  have key : (tq k n) ^ (n - 1) * e = 0 := by
    have h3 : (tq k n) ^ (n - 2) * ((tq k n) * e) = (tq k n) ^ (n - 2) * 0 := by rw [hann]
    rw [← mul_assoc, ← pow_succ, show (n - 2) + 1 = n - 1 by omega, mul_zero] at h3
    exact h3
  exact hgen.symm.trans key

/-- **Problem 9.4.5 (ii), first algebra.** For `n > 1`, `homologicalDimension (k[X]/(Xⁿ)) = ⊤`. -/
theorem homologicalDimension_eq_top_truncated (hn : 1 < n) :
    Etingof.homologicalDimension (Rq k n) = ⊤ := by
  letI : Small.{u} (Rq k n) := ⟨⟨Rq k n, ⟨Equiv.refl _⟩⟩⟩
  set ft := LinearMap.mulLeft (Rq k n) (tq k n) with hft
  set fs := LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1)) with hfs
  set MA := ModuleCat.of (Rq k n) ↥(LinearMap.range ft) with hMA
  set MB := ModuleCat.of (Rq k n) ↥(LinearMap.range fs) with hMB
  haveI hRproj : Projective (ModuleCat.of (Rq k n) (Rq k n)) := inferInstance
  -- The two short exact sequences `0 → ker(rangeRestrict) → R → M{A,B} → 0`.
  have sesA : (ft.rangeRestrict).shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer ft.surjective_rangeRestrict
  have sesB : (fs.rangeRestrict).shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer fs.surjective_rangeRestrict
  -- Dimension shifting: pd(MA) ≤ d+1 ⟹ pd(MB) ≤ d, and symmetrically.
  have shiftA : ∀ d, HasProjectiveDimensionLE MA (d + 1) → HasProjectiveDimensionLE MB d := by
    intro d hA
    have hker : HasProjectiveDimensionLT
        (ModuleCat.of (Rq k n) ↥(LinearMap.ker ft.rangeRestrict)) (d + 1) := by
      have := Etingof.Problem942.hasProjectiveDimensionLE_syzygy (Rq k n)
        ft.rangeRestrict.shortComplexKer sesA hRproj (d + 1) (Nat.succ_pos d) hA
      simpa only [Nat.add_sub_cancel] using this
    haveI := hker
    have heq : LinearMap.ker ft.rangeRestrict = LinearMap.range fs := by
      rw [LinearMap.ker_rangeRestrict, hft, hfs]; exact ker_mulLeft_t k n (by omega)
    exact hasProjectiveDimensionLT_of_iso ((LinearEquiv.ofEq _ _ heq).toModuleIso) (d + 1)
  have shiftB : ∀ d, HasProjectiveDimensionLE MB (d + 1) → HasProjectiveDimensionLE MA d := by
    intro d hB
    have hker : HasProjectiveDimensionLT
        (ModuleCat.of (Rq k n) ↥(LinearMap.ker fs.rangeRestrict)) (d + 1) := by
      have := Etingof.Problem942.hasProjectiveDimensionLE_syzygy (Rq k n)
        fs.rangeRestrict.shortComplexKer sesB hRproj (d + 1) (Nat.succ_pos d) hB
      simpa only [Nat.add_sub_cancel] using this
    haveI := hker
    have heq : LinearMap.ker fs.rangeRestrict = LinearMap.range ft := by
      rw [LinearMap.ker_rangeRestrict, hft, hfs]; exact ker_mulLeft_t_pow k n (by omega)
    exact hasProjectiveDimensionLT_of_iso ((LinearEquiv.ofEq _ _ heq).toModuleIso) (d + 1)
  -- Symmetric induction: neither MA nor MB has finite projective dimension.
  have hQ : ∀ d, ¬ HasProjectiveDimensionLE MA d ∧ ¬ HasProjectiveDimensionLE MB d := by
    intro d
    induction d with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [← projective_iff_hasProjectiveDimensionLE_zero]; exact not_projective_A k n hn
      · rw [← projective_iff_hasProjectiveDimensionLE_zero]; exact not_projective_B k n hn
    | succ d ih => exact ⟨fun hA => ih.2 (shiftA d hA), fun hB => ih.1 (shiftB d hB)⟩
  -- MA witnesses `¬ HasHomologicalDimensionLE R d` for every `d`.
  apply Etingof.homologicalDimension_eq_top
  intro d hAll
  exact (hQ d).1 (hAll MA)

end Etingof.TruncatedPoly
