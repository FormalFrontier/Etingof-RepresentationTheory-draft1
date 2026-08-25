/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.ULift
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import RepresentationTheory.Alignment.Attribute

/-! # Lifting properties for finite modules -/

namespace RepresentationTheory.Algebra.Module.Lifting

universe u

/-- A finite additive commutative group is subsingleton if every homomorphism from it to a finite
additive commutative group lifts along every surjective homomorphism between finite additive
commutative groups. -/
@[source_ref "Chapter8/Exercise8.2.9" (role := primary)]
theorem subsingleton_of_lifts_along_surjective_addMonoidHoms
    (P : Type u) [AddCommGroup P] [Finite P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Finite Q₁] [AddCommGroup Q₂] [Finite Q₂]
      (f : Q₁ →+ Q₂) (g : P →+ Q₂), Function.Surjective f →
        ∃ h : P →+ Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · exact hsub
  exfalso
  haveI : Fintype P := Fintype.ofFinite P
  -- Pick a prime `q` dividing `|P|` and, by Cauchy, an element `x` of additive order `q`.
  have hcard1 : Nat.card P ≠ 1 := by
    have := Finite.one_lt_card (α := P); omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd' : q ∣ Fintype.card P := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hxord⟩ := exists_prime_addOrderOf_dvd_card q hqdvd'
  have hx0 : q • x = 0 := by rw [← hxord]; exact addOrderOf_nsmul_eq_zero x
  have hxne : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hxord; exact hq.one_lt.ne hxord
  -- Multiplication by `q` on `P`, and the subgroup `H = qP`.
  let μ : P →+ P := AddMonoidHom.mk' (fun y => q • y) (fun a b => smul_add q a b)
  have μapp : ∀ y, μ y = q • y := fun _ => rfl
  let H : AddSubgroup P := μ.range
  have hHmem : ∀ y, q • y ∈ H := fun y => ⟨y, rfl⟩
  -- `μ` is not injective (kills `x ≠ 0`), hence (P finite) not surjective, so `H ≠ ⊤`.
  have hμ_ninj : ¬ Function.Injective μ := by
    intro hinj
    exact hxne (hinj (by rw [μapp, hx0, map_zero]))
  have hμ_nsurj : ¬ Function.Surjective μ := fun hsurj =>
    hμ_ninj ((Finite.injective_iff_surjective).2 hsurj)
  obtain ⟨y₀, hy₀⟩ := not_forall.mp hμ_nsurj
  have hy₀H : y₀ ∉ H := fun hmem => hy₀ (AddMonoidHom.mem_range.mp hmem)
  -- The quotient `P/qP` is a nonzero `ZMod q`-vector space.
  letI : Module (ZMod q) (P ⧸ H) := QuotientAddGroup.zmodModule (n := q) hHmem
  set ybar : P ⧸ H := QuotientAddGroup.mk' H y₀ with hybar
  have hybarne : ybar ≠ 0 := by
    rw [hybar, QuotientAddGroup.mk'_apply, Ne, QuotientAddGroup.eq_zero_iff]
    exact hy₀H
  -- Choose a basis of `P/qP` as a `ZMod q`-vector space; some coordinate functional is
  -- nonzero on `ybar`, giving a nonzero additive character `φ : P →+ ZMod q`.
  let b := Module.Basis.ofVectorSpace (ZMod q) (P ⧸ H)
  obtain ⟨i, hi⟩ :
      ∃ i, ((b.coord i).toAddMonoidHom.comp (QuotientAddGroup.mk' H)) y₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hybarne
    apply b.forall_coord_eq_zero_iff.mp
    intro j
    simpa [hybar] using hcon j
  let φ : P →+ ZMod q := (b.coord i).toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  have hφy₀ : φ y₀ ≠ 0 := hi
  -- Now lift `φ` through the reduction `ZMod (q^N) ↠ ZMod q` with `N = |P|`.  The finite
  -- `ZMod` groups live in `Type 0`, so transport them into `Type u` via `ULift`.
  set N := Nat.card P with hNdef
  have hN0 : N ≠ 0 := by rw [hNdef]; exact Nat.card_pos.ne'
  haveI : NeZero (q ^ N) := ⟨pow_ne_zero N hq.ne_zero⟩
  have hdvd : q ∣ q ^ N := dvd_pow_self q hN0
  let f0 : ZMod (q ^ N) →+ ZMod q := (ZMod.castHom hdvd (ZMod q)).toAddMonoidHom
  have hf0surj : Function.Surjective f0 := ZMod.castHom_surjective hdvd
  let e1 : ULift.{u} (ZMod (q ^ N)) ≃+ ZMod (q ^ N) := AddEquiv.ulift
  let e2 : ULift.{u} (ZMod q) ≃+ ZMod q := AddEquiv.ulift
  let f0' : ULift.{u} (ZMod (q ^ N)) →+ ULift.{u} (ZMod q) :=
    (e2.symm.toAddMonoidHom).comp (f0.comp e1.toAddMonoidHom)
  have hf0'surj : Function.Surjective f0' := by
    intro y
    obtain ⟨z, hz⟩ := hf0surj (e2 y)
    refine ⟨e1.symm z, ?_⟩
    change e2.symm (f0 (e1 (e1.symm z))) = y
    rw [e1.apply_symm_apply, hz, e2.symm_apply_apply]
  let φ' : P →+ ULift.{u} (ZMod q) := (e2.symm.toAddMonoidHom).comp φ
  obtain ⟨h', hh'⟩ := hP (ULift.{u} (ZMod (q ^ N))) (ULift.{u} (ZMod q)) f0' φ' hf0'surj
  let h : P →+ ZMod (q ^ N) := e1.toAddMonoidHom.comp h'
  have key : ∀ z, f0 (h z) = φ z := fun z => e2.symm.injective (hh' z)
  have hne0 : f0 (h y₀) ≠ 0 := by rw [key y₀]; exact hφy₀
  -- The lift `h y₀` reduces to a nonzero residue mod `q`, so it is a unit of `ZMod (q^N)`:
  -- its additive order is `q^N`.
  have hcast : f0 (h y₀) = (((h y₀).val : ℕ) : ZMod q) := by
    change ZMod.castHom hdvd (ZMod q) (h y₀) = _
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  have hnotdvd : ¬ (q ∣ (h y₀).val) := by
    intro hd
    apply hne0
    rw [hcast, ZMod.natCast_eq_zero_iff]
    exact hd
  have hcop : Nat.Coprime (q ^ N) (h y₀).val :=
    ((hq.coprime_iff_not_dvd).mpr hnotdvd).pow_left N
  have hord : addOrderOf (h y₀) = q ^ N := by
    have h1 := ZMod.addOrderOf_coe (h y₀).val (pow_ne_zero N hq.ne_zero)
    rw [ZMod.natCast_rightInverse (h y₀)] at h1
    rw [h1, hcop, Nat.div_one]
  -- But the additive order divides `|P|`, giving `q^N ≤ N < q^N`.
  have hdvd1 : addOrderOf (h y₀) ∣ addOrderOf y₀ := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  have hdvd2 : addOrderOf y₀ ∣ Nat.card P := addOrderOf_dvd_natCard y₀
  have hle : addOrderOf (h y₀) ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (hdvd1.trans hdvd2)
  rw [hord] at hle
  have hlt : Nat.card P < q ^ Nat.card P :=
    calc Nat.card P < 2 ^ Nat.card P := Nat.lt_two_pow_self
      _ ≤ q ^ Nat.card P := Nat.pow_le_pow_left hq.two_le _
  exact absurd hle (not_le.mpr hlt)

open scoped Pointwise in
open Polynomial in
/-- A nonzero finite dimensional `k[x]`-module `P` admits a monic irreducible polynomial `p`
such that multiplication by `p` is not surjective on `P` (equivalently `p • P ≠ P`). The witness
comes from a nonzero element `v`: its annihilator in `k[x]` is a proper nonzero ideal `(g)`, and
a monic irreducible factor `p ∣ g` kills the nonzero element `(g / p) • v`, so multiplication by
`p` is not injective, hence (finite dimension) not surjective. -/
private theorem exists_monic_irreducible_smul_ne_top
    (k : Type u) [Field k] (P : Type u) [AddCommGroup P] [Module (Polynomial k) P] [Module k P]
    [IsScalarTower k (Polynomial k) P] [FiniteDimensional k P] [Nontrivial P] :
    ∃ p : Polynomial k, p.Monic ∧ Irreducible p ∧
      p • (⊤ : Submodule (Polynomial k) P) ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  set L := LinearMap.toSpanSingleton (Polynomial k) P v with hL
  set I : Ideal (Polynomial k) := LinearMap.ker L with hI
  -- `I ≠ ⊤`, since `L 1 = v ≠ 0`.
  have hItop : I ≠ ⊤ := by
    intro h
    have hmem : (1 : Polynomial k) ∈ I := by rw [h]; exact Submodule.mem_top
    have h1 : L 1 = 0 := LinearMap.mem_ker.mp hmem
    rw [hL, LinearMap.toSpanSingleton_apply_one] at h1
    exact hv h1
  -- `I ≠ ⊥`, else `L` is an injective `k`-linear map `k[x] ↪ P` and `k[x]` would be finite
  -- dimensional over `k`.
  have hIbot : I ≠ ⊥ := by
    intro h
    have hkerL : LinearMap.ker L = ⊥ := hI ▸ h
    have hinjL : Function.Injective L := LinearMap.ker_eq_bot.mp hkerL
    have : Module.Finite k (Polynomial k) :=
      Module.Finite.of_injective (L.restrictScalars k) hinjL
    exact Polynomial.not_finite this
  -- `I = (g)` with `g ≠ 0` and `g` not a unit.
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  have hgne : g ≠ 0 := by
    rintro rfl
    apply hIbot
    rw [hg]; simp
  have hgnu : ¬ IsUnit g := by
    intro hu
    exact hItop (by rw [hg]; exact Ideal.span_singleton_eq_top.mpr hu)
  -- a monic irreducible factor `p ∣ g`.
  obtain ⟨p, hpmonic, hpirr, hpdvd⟩ := Polynomial.exists_monic_irreducible_factor g hgnu
  obtain ⟨g', hg'⟩ := hpdvd
  have hg'ne : g' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hg'; exact hgne hg'
  -- `w := g' • v ≠ 0` but `p • w = g • v = 0`.
  have hgmem : g ∈ I := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hgv : g • v = 0 := by
    have hker := LinearMap.mem_ker.mp hgmem
    rwa [hL, LinearMap.toSpanSingleton_apply] at hker
  have hw : g' • v ≠ 0 := by
    intro hcontra
    have hLg' : L g' = 0 := by rw [hL, LinearMap.toSpanSingleton_apply]; exact hcontra
    have hmem : g' ∈ I := LinearMap.mem_ker.mpr hLg'
    rw [hg] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    -- `c • g = g'` and `g = p * g'` give `p * g' ∣ g'`, so `p` is a unit, a contradiction.
    have hdvd : g ∣ g' := ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
    rw [hg'] at hdvd
    have hp1 : p ∣ 1 := by
      have h2 : p * g' ∣ 1 * g' := by rwa [one_mul]
      exact (mul_dvd_mul_iff_right hg'ne).mp h2
    exact hpirr.not_isUnit (isUnit_of_dvd_one hp1)
  have hpw : p • (g' • v) = 0 := by rw [← mul_smul, ← hg']; exact hgv
  refine ⟨p, hpmonic, hpirr, ?_⟩
  -- If `p • ⊤ = ⊤` then `p • ·` is surjective, hence injective (finite dim), contradicting
  -- `p • w = 0` with `w ≠ 0`.
  intro htop
  set fp : P →ₗ[k] P := (LinearMap.lsmul (Polynomial k) P p).restrictScalars k with hfp
  have hfp_apply : ∀ y, fp y = p • y := fun y => rfl
  have hfp_surj : Function.Surjective fp := by
    intro z
    have hz : z ∈ p • (⊤ : Submodule (Polynomial k) P) := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨y, -, hy⟩ := hz
    exact ⟨y, hy⟩
  have hfp_inj : Function.Injective fp := LinearMap.injective_iff_surjective.mpr hfp_surj
  apply hw
  have : fp (g' • v) = fp 0 := by rw [hfp_apply, hfp_apply, hpw, smul_zero]
  exact hfp_inj this

open scoped Pointwise in
open Polynomial in
/-- A module over a polynomial ring that is finite-dimensional over the coefficient field is
subsingleton if every polynomial-linear map from it to another such module lifts along every
surjective polynomial-linear map between such modules. -/
@[source_ref "Chapter8/Exercise8.2.9" (role := primary)]
theorem subsingleton_of_lifts_along_surjective_polynomialLinearMaps
    (k : Type u) [Field k]
    (P : Type u) [AddCommGroup P] [Module (Polynomial k) P] [Module k P]
      [IsScalarTower k (Polynomial k) P] [FiniteDimensional k P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Module (Polynomial k) Q₁] [Module k Q₁]
        [IsScalarTower k (Polynomial k) Q₁] [FiniteDimensional k Q₁]
        [AddCommGroup Q₂] [Module (Polynomial k) Q₂] [Module k Q₂]
        [IsScalarTower k (Polynomial k) Q₂] [FiniteDimensional k Q₂]
        (f : Q₁ →ₗ[Polynomial k] Q₂) (g : P →ₗ[Polynomial k] Q₂), Function.Surjective f →
          ∃ h : P →ₗ[Polynomial k] Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · exact hsub
  exfalso
  -- Step 1: monic irreducible `p` with `p • ⊤ ≠ ⊤`.
  obtain ⟨p, hpmonic, hpirr, hptop⟩ := exists_monic_irreducible_smul_ne_top k P
  -- The quotient `P / (p • P)` is a nonzero vector space over the field `K = k[x]/(p)`.
  -- `Ideal.Quotient.field` (a `fast_instance%`) and the `IsTorsionBy…module` structure carry
  -- syntactically different but defeq semirings on `K`, so we pass both explicitly to
  -- `ofVectorSpace` (instance search would fail; explicit passing succeeds up to defeq).
  haveI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpirr
  haveI : Module.Finite k (Polynomial k ⧸ Ideal.span {p}) := hpmonic.finite_quotient
  haveI : Nontrivial (P ⧸ (p • (⊤ : Submodule (Polynomial k) P))) :=
    Submodule.Quotient.nontrivial_iff.mpr hptop
  -- a coordinate functional gives a nonzero `k[x]`-linear map `φ : P → K`.
  set b := @Module.Basis.ofVectorSpace (Polynomial k ⧸ Ideal.span {p})
    (P ⧸ (p • (⊤ : Submodule (Polynomial k) P)))
    (Ideal.Quotient.field _).toDivisionRing _
    (Module.isTorsionBy_quotient_element_smul P p).module with hb
  obtain ⟨z, hz⟩ := exists_ne (0 : P ⧸ (p • (⊤ : Submodule (Polynomial k) P)))
  obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨i, hi⟩ : ∃ i, b.coord i z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hz (b.forall_coord_eq_zero_iff.mp hcon)
  -- `φ : P →ₗ[k[x]] k[x]/(p)`, built by hand from the `K`-linear coordinate `b.coord i`.
  set φ : P →ₗ[Polynomial k] (Polynomial k ⧸ Ideal.span {p}) :=
    { toFun := fun x => b.coord i (Submodule.Quotient.mk x)
      map_add' := fun x y => by rw [Submodule.Quotient.mk_add]; exact map_add _ _ _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [Submodule.Quotient.mk_smul,
          ← Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul P p) a
            (Submodule.Quotient.mk x), map_smul,
          ← IsScalarTower.algebraMap_smul (Polynomial k ⧸ Ideal.span {p}) a
            (b.coord i (Submodule.Quotient.mk x)),
          Ideal.Quotient.algebraMap_eq] } with hφ
  have hφy₀ : φ y₀ ≠ 0 := by
    change b.coord i (Submodule.Quotient.mk y₀) ≠ 0
    rw [hy₀]; exact hi
  -- Step 3: lift `φ` through the reduction `k[x]/(p^N) ↠ k[x]/(p)` with `N` large.
  set N : ℕ := Module.finrank k P + 1 with hN
  have hNne : N ≠ 0 := by omega
  haveI : Module.Finite k (Polynomial k ⧸ Ideal.span {p ^ N}) := (hpmonic.pow N).finite_quotient
  have hle : Ideal.span {p ^ N} ≤ Ideal.span {p} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self p hNne)
  set red : (Polynomial k ⧸ Ideal.span {p ^ N}) →ₗ[Polynomial k]
      (Polynomial k ⧸ Ideal.span {p}) :=
    (Ideal.Quotient.factorₐ (Polynomial k) hle).toLinearMap with hred
  have hred_surj : Function.Surjective red := Ideal.Quotient.factor_surjective hle
  obtain ⟨h, hh⟩ := hP (Polynomial k ⧸ Ideal.span {p ^ N}) (Polynomial k ⧸ Ideal.span {p})
    red φ hred_surj
  -- `red (h y₀) = φ y₀ ≠ 0`, so `h y₀` is a unit of `k[x]/(p^N)`.
  have hru : red (h y₀) ≠ 0 := by rw [hh y₀]; exact hφy₀
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (h y₀)
  have hpa : ¬ p ∣ a := by
    intro hdvd
    apply hru
    rw [← ha, hred]
    change Ideal.Quotient.factor hle (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hcoprime : IsCoprime a (p ^ N) := (hpirr.coprime_iff_not_dvd.mpr hpa).symm.pow_right
  -- from coprimality, `mk a = h y₀` is a unit.
  obtain ⟨s, t, hst⟩ := hcoprime
  have huy : IsUnit (h y₀) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ s) ?_
    rw [← ha, ← map_mul]
    have hone : a * s = 1 - t * p ^ N := by linear_combination hst
    rw [hone, map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _), mul_zero, sub_zero]
  -- Step 4: `h y₀` is a unit, so `h` is surjective, hence `finrank k P ≥ finrank k (k[x]/(p^N))`.
  have hsurj : Function.Surjective h := by
    intro w
    obtain ⟨v, hv⟩ := huy.exists_right_inv
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w * v)
    refine ⟨c • y₀, ?_⟩
    rw [map_smul, ← IsScalarTower.algebraMap_smul (Polynomial k ⧸ Ideal.span {p ^ N}) c (h y₀),
      smul_eq_mul, Ideal.Quotient.algebraMap_eq, hc, mul_assoc,
      show v * h y₀ = 1 by rw [mul_comm]; exact hv, mul_one]
  -- dimension contradiction.
  have hfin : Module.finrank k (Polynomial k ⧸ Ideal.span {p ^ N}) ≤ Module.finrank k P := by
    exact LinearMap.finrank_le_finrank_of_surjective (f := h.restrictScalars k)
      (by exact hsurj)
  have hdim : Module.finrank k (Polynomial k ⧸ Ideal.span {p ^ N}) = N * p.natDegree := by
    rw [finrank_quotient_span_eq_natDegree, natDegree_pow]
  have hpdeg : 1 ≤ p.natDegree := hpirr.natDegree_pos
  rw [hdim] at hfin
  have : Module.finrank k P + 1 ≤ Module.finrank k P := by
    calc Module.finrank k P + 1 = N := by rw [hN]
      _ = N * 1 := (mul_one N).symm
      _ ≤ N * p.natDegree := Nat.mul_le_mul_left N hpdeg
      _ ≤ Module.finrank k P := hfin
  omega

open scoped Pointwise in
open Polynomial in
/-- A finite module over a commutative ring of finite type over the integers admits a surjective
linear map from a finite free module. -/
@[source_ref "Chapter8/Exercise8.2.9" (role := supporting)]
theorem exists_surjective_finFreeLinearMap_of_finite
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (f : (Fin n → A) →ₗ[A] M), Function.Surjective f :=
  Module.Finite.exists_fin' A M

end RepresentationTheory.Algebra.Module.Lifting
