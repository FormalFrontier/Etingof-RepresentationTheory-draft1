/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.ModularPGroup

open Representation MonoidAlgebra

/-- A nontrivial representation in characteristic `p` of a finite `p`-group has a nonzero vector fixed by every group element. -/
theorem eq_id_of_isSimpleModule_of_card_eq_primePow.exists_ne_zero_fixedVector
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] :
    ∀ (N : ℕ) {G : Type*} [Group G] [Finite G], IsPGroup p G → Nat.card G = N →
      ∀ {V : Type*} [AddCommGroup V] [Module k V], Nontrivial V →
        ∀ (ρ : Representation k G V), ∃ x : V, x ≠ 0 ∧ ∀ g : G, ρ g x = x := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro G _ _ hG hN V _ _ hVnt ρ
    rcases eq_or_ne (Nat.card G) 1 with hcard1 | hcard1
    ·
      have hsub : Subsingleton G := Nat.card_eq_one_iff_unique.mp hcard1 |>.1
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      refine ⟨x, hx, fun g => ?_⟩
      rw [Subsingleton.elim g 1, map_one]
      rfl
    ·
      have hpos : 0 < Nat.card G := Nat.card_pos
      haveI hNtriv : Nontrivial G := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        omega
      haveI : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hG
      obtain ⟨z₀, hz₀⟩ := exists_ne (1 : Subgroup.center G)
      set z : G := (z₀ : G) with hzdef
      have hzcentral : ∀ g : G, g * z = z * g := by
        rw [hzdef]; exact Subgroup.mem_center_iff.mp z₀.2
      have hz1 : z ≠ 1 := by
        rw [hzdef]
        exact fun h => hz₀ (Subtype.ext (h.trans (OneMemClass.coe_one _).symm))
      have hSnormal : (Subgroup.zpowers z).Normal := by
        constructor
        intro x hx g
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hcomm : Commute (z ^ n) g := Commute.zpow_left (h := (hzcentral g).symm) n
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨n, by rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]⟩
      set S : Subgroup G := Subgroup.zpowers z with hSdef
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hG) z
      have htorsion : ∃ x : V, Ideal.torsionOf k V x = ⊥ := by
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        refine ⟨x, ?_⟩
        rw [Submodule.eq_bot_iff]
        intro r hr
        rw [Ideal.mem_torsionOf_iff] at hr
        exact (smul_eq_zero.mp hr).resolve_right hx
      haveI : CharP (Module.End k V) p := Module.charP_end htorsion
      have hσpow : (ρ z) ^ (orderOf z) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have hnil : IsNilpotent (ρ z - 1) := by
        refine ⟨p ^ j, ?_⟩
        rw [sub_pow_expChar_pow_of_commute _ _ (Commute.one_right (ρ z)), one_pow, ← hj,
          hσpow, sub_self]
      have hWne : LinearMap.ker (ρ z - 1) ≠ ⊥ := by
        intro hbot
        obtain ⟨m, hm⟩ := hnil
        have hbase : Function.Injective ⇑(ρ z - 1) := LinearMap.ker_eq_bot.mp hbot
        have hpow : Function.Injective ⇑(((ρ z - 1) : Module.End k V) ^ m) := by
          rw [Module.End.coe_pow]
          exact hbase.iterate m
        rw [hm] at hpow
        obtain ⟨a, b, hab⟩ := exists_pair_ne V
        exact hab (hpow (a₁ := a) (a₂ := b) (by simp))
      haveI hWnt : Nontrivial (LinearMap.ker (ρ z - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr hWne
      have hle : ∀ g : G, LinearMap.ker (ρ z - 1) ≤
          (LinearMap.ker (ρ z - 1)).comap (ρ g) := by
        intro g w hw
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
        rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
          sub_eq_zero, ← Module.End.mul_apply, ← map_mul, ← hzcentral g, map_mul,
          Module.End.mul_apply, hw]
      set ρW : Representation k G (LinearMap.ker (ρ z - 1)) :=
        ρ.subrepresentation _ hle with hρW
      have hztriv : ρW z = 1 := by
        ext w
        have hw2 : ρ z (w : V) = (w : V) := by
          have := LinearMap.mem_ker.mp w.2
          rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
          exact this
        simpa [hρW, Representation.subrepresentation_apply, LinearMap.coe_restrict_apply]
          using hw2
      haveI : IsTrivial (ρW.comp S.subtype) := by
        refine ⟨fun s => ?_⟩
        have hz_ker : z ∈ (ρW : G →* Module.End k (LinearMap.ker (ρ z - 1))).ker :=
          MonoidHom.mem_ker.mpr hztriv
        exact MonoidHom.mem_ker.mp ((Subgroup.zpowers_le.mpr hz_ker) s.2)
      set ρQ : Representation k (G ⧸ S) (LinearMap.ker (ρ z - 1)) :=
        ρW.ofQuotient S with hρQ
      have hGQ : IsPGroup p (G ⧸ S) := hG.to_quotient S
      have hcardS : 1 < Nat.card S := by
        have hSnt : Nontrivial S := by
          rw [Subgroup.nontrivial_iff_ne_bot, hSdef, Ne, Subgroup.zpowers_eq_bot]
          exact hz1
        exact Finite.one_lt_card_iff_nontrivial.mpr hSnt
      have hcardlt : Nat.card (G ⧸ S) < N := by
        have hmul : Nat.card G = Nat.card (G ⧸ S) * Nat.card S :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup S
        have hqpos : 0 < Nat.card (G ⧸ S) := Nat.card_pos
        rw [← hN, hmul]
        exact (Nat.lt_mul_iff_one_lt_right hqpos).mpr hcardS
      obtain ⟨w, hw_ne, hw_fix⟩ :=
        IH (Nat.card (G ⧸ S)) hcardlt hGQ rfl hWnt ρQ
      refine ⟨(w : V), ?_, fun g => ?_⟩
      · exact fun h => hw_ne (Submodule.coe_eq_zero.mp h)
      · have hfix := hw_fix (g : G ⧸ S)
        rw [hρQ, Representation.ofQuotient_coe_apply] at hfix
        have hval := congrArg (Subtype.val) hfix
        simpa [hρW, Representation.subrepresentation_apply, LinearMap.coe_restrict_apply]
          using hval

/-- A simple representation in characteristic `p` of a finite group whose cardinality is a power of `p` sends every group element to the identity. -/
@[source_ref "Chapter4/Problem4.1.4" (role := primary)]
theorem eq_id_of_isSimpleModule_of_card_eq_primePow {p n : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = p ^ n)
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρ.asModule) :
    ∀ g : G, ρ g = LinearMap.id := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  have hGp : IsPGroup p G := IsPGroup.of_card (by rw [Nat.card_eq_fintype_card]; exact hG)
  obtain ⟨v, hv0, hvfix⟩ :=
    eq_id_of_isSimpleModule_of_card_eq_primePow.exists_ne_zero_fixedVector
      (Nat.card G) hGp rfl inferInstance ρ
  have key : ∀ r : MonoidAlgebra k G, ∃ c : k, ρ.asAlgebraHom r v = c • v := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | hM g =>
        refine ⟨1, ?_⟩
        change ρ.asAlgebraHom (single g 1) v = (1 : k) • v
        rw [Representation.asAlgebraHom_single, LinearMap.smul_apply, one_smul, hvfix g, one_smul]
    | hadd f h hf hh =>
        obtain ⟨c1, h1⟩ := hf
        obtain ⟨c2, h2⟩ := hh
        exact ⟨c1 + c2, by rw [map_add, LinearMap.add_apply, h1, h2, add_smul]⟩
    | hsmul s f hf =>
        obtain ⟨c1, h1⟩ := hf
        exact ⟨s * c1, by rw [map_smul, LinearMap.smul_apply, h1, smul_smul]⟩
  set vM : ρ.asModule := ρ.asModuleEquiv.symm v with hvM
  have hvM0 : vM ≠ 0 := by rw [hvM]; simpa using hv0
  have hspan : Submodule.span (MonoidAlgebra k G) {vM} = ⊤ :=
    IsSimpleModule.span_singleton_eq_top (MonoidAlgebra k G) hvM0
  intro g
  ext w
  have hx : ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra k G) {vM} := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨r, hr⟩ := hx
  obtain ⟨c, hc⟩ := key r
  have hrV : ρ.asAlgebraHom r v = w := by
    have hh := congrArg ρ.asModuleEquiv hr
    rw [Representation.asModuleEquiv_map_smul, hvM] at hh
    simpa using hh
  have hwc : w = c • v := by rw [← hrV, hc]
  rw [LinearMap.id_apply, hwc, map_smul, hvfix g]

end RepresentationTheory.ModularPGroup
