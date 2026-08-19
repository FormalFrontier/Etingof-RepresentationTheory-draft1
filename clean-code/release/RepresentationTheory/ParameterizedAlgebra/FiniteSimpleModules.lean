/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.QuantumTorus.Representations
import RepresentationTheory.Alignment.Attribute

/-!
# Finite simple modules for a parameterized algebra

Centers, simplicity, and finite-dimensional simple modules for the displayed parameterized algebra.
-/

namespace RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules

open RepresentationTheory.Algebra.Module.TwistedLatticeShifts RepresentationTheory.QuantumTorus.Representations Finsupp

variable (q : ℂˣ)


private theorem linearCombination_qMono_apply_zero (c : (ℤ × ℤ) →₀ ℂ) :
    (Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) c) (single (0, 0) 1) = c := by
  rw [Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply]
  rw [show (c.sum fun p a => (a • twistedLatticeShift ℂ q p) (single (0, 0) 1)) = c.sum fun p a => single p a by
    refine Finsupp.sum_congr fun p _ => ?_
    rw [LinearMap.smul_apply, twistedLatticeShift_apply_single]; simp]
  exact Finsupp.sum_single c


private theorem mem_qWeyl_eq_linearCombination {f : Module.End ℂ (Auxiliary ℂ)}
    (hf : f ∈ twistedLatticeShiftSubalgebra ℂ q) :
    f = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (f (single (0, 0) 1)) := by
  rw [← Subalgebra.mem_toSubmodule, twistedLatticeShiftSubalgebra_toSubmodule,
    Finsupp.mem_span_range_iff_exists_finsupp] at hf
  obtain ⟨c, rfl⟩ := hf
  have hconv : (c.sum fun i a => a • twistedLatticeShift ℂ q i) = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) c :=
    (Finsupp.linearCombination_apply _ _).symm
  rw [hconv, linearCombination_qMono_apply_zero]


private theorem finsupp_sum_single_emb_apply {ι : Type*} (c : ι →₀ ℂ)
    (e : ι → ℤ × ℤ) (he : Function.Injective e) (ψ : ι → ℂ → ℂ) (hψ : ∀ i, ψ i 0 = 0)
    (i₀ : ι) :
    (c.sum fun i a => Finsupp.single (e i) (ψ i a)) (e i₀) = ψ i₀ (c i₀) := by
  classical
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply, he.eq_iff]
  rw [Finsupp.sum_ite_eq' c i₀ fun i a => ψ i a]
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, hψ]


private theorem zpow_eq_one_imp (hq : ¬ IsOfFinOrder q) {n : ℤ} (h : (↑(q ^ n) : ℂ) = 1) :
    n = 0 := by
  have hqinj : Function.Injective (fun m : ℤ => q ^ m) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hq
  have hqn : q ^ n = 1 := by apply Units.ext; simpa using h
  simpa using hqinj (show (fun m : ℤ => q ^ m) n = (fun m : ℤ => q ^ m) 0 by simpa using hqn)


/-- If the parameter has infinite multiplicative order, the center of the displayed subalgebra is trivial. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]
theorem center_eq_bot_of_not_isOfFinOrder (hq : ¬ IsOfFinOrder q) :
    Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) = ⊥ := by
  refine le_antisymm ?_ ?_
  ·
    rintro z hz
    rw [Subalgebra.mem_center_iff] at hz

    set X : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (1, 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hX
    set Y : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (0, 1), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hY

    set f : Module.End ℂ (Auxiliary ℂ) := z.val with hf
    set c : (ℤ × ℤ) →₀ ℂ := f (single (0, 0) 1) with hc
    have hfc : f = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) c := mem_qWeyl_eq_linearCombination q z.2

    have hcomX : ∀ p : ℤ × ℤ, c p * (↑(q ^ p.2) : ℂ) = c p := by
      have hop : f * twistedLatticeShift ℂ q (1, 0) = twistedLatticeShift ℂ q (1, 0) * f := by
        have := hz X
        exact congrArg Subtype.val this.symm
      intro p

      have hval := congrArg (fun g : Module.End ℂ (Auxiliary ℂ) => g (single (0, 0) 1)) hop
      simp only [Module.End.mul_apply] at hval
      rw [show twistedLatticeShift ℂ q (1, 0) (single (0, 0) 1) = single (1, 0) 1 by rw [twistedLatticeShift_apply_single]; simp,
        ← hc] at hval

      have hL : f (single (1, 0) 1) =
          c.sum fun p a => single (p.1 + 1, p.2) (a * (↑(q ^ p.2) : ℂ)) := by
        rw [hfc, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply]
        refine Finsupp.sum_congr fun p _ => ?_
        rw [LinearMap.smul_apply, twistedLatticeShift_apply_single, Finsupp.smul_single]
        simp only [zero_add, mul_one, smul_eq_mul, add_comm 1 p.1]
      have hR : twistedLatticeShift ℂ q (1, 0) c = c.sum fun p a => single (p.1 + 1, p.2) a := by
        conv_lhs => rw [← Finsupp.sum_single c]
        rw [map_finsuppSum]
        refine Finsupp.sum_congr fun p _ => ?_
        rw [twistedLatticeShift_apply_single, add_zero, zero_mul, zpow_zero, Units.val_one, one_mul]
      rw [hL, hR] at hval
      have hval' := DFunLike.congr_fun hval (p.1 + 1, p.2)
      rw [finsupp_sum_single_emb_apply c (fun p => (p.1 + 1, p.2))
          (fun a b h => by simpa [Prod.ext_iff] using h) _ (fun i => by simp) p,
        finsupp_sum_single_emb_apply c (fun p => (p.1 + 1, p.2))
          (fun a b h => by simpa [Prod.ext_iff] using h) _ (fun i => by simp) p] at hval'
      exact hval'

    have hcomY : ∀ p : ℤ × ℤ, c p * (↑(q ^ p.1) : ℂ) = c p := by
      have hop : f * twistedLatticeShift ℂ q (0, 1) = twistedLatticeShift ℂ q (0, 1) * f := by
        have := hz Y
        exact congrArg Subtype.val this.symm
      intro p
      have hval := congrArg (fun g : Module.End ℂ (Auxiliary ℂ) => g (single (0, 0) 1)) hop
      simp only [Module.End.mul_apply] at hval
      rw [show twistedLatticeShift ℂ q (0, 1) (single (0, 0) 1) = single (0, 1) 1 by rw [twistedLatticeShift_apply_single]; simp,
        ← hc] at hval
      have hL : f (single (0, 1) 1) =
          c.sum fun p a => single (p.1, p.2 + 1) a := by
        rw [hfc, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply]
        refine Finsupp.sum_congr fun p _ => ?_
        rw [LinearMap.smul_apply, twistedLatticeShift_apply_single, Finsupp.smul_single]
        simp only [zero_add, mul_zero, zpow_zero, Units.val_one, mul_one, smul_eq_mul,
          add_comm 1 p.2]
      have hR : twistedLatticeShift ℂ q (0, 1) c =
          c.sum fun p a => single (p.1, p.2 + 1) (a * (↑(q ^ p.1) : ℂ)) := by
        conv_lhs => rw [← Finsupp.sum_single c]
        rw [map_finsuppSum]
        refine Finsupp.sum_congr fun p _ => ?_
        rw [twistedLatticeShift_apply_single, add_zero, one_mul, mul_comm]
      rw [hL, hR] at hval
      have hval' := DFunLike.congr_fun hval (p.1, p.2 + 1)
      rw [finsupp_sum_single_emb_apply c (fun p => (p.1, p.2 + 1))
          (fun a b h => by simpa [Prod.ext_iff] using h) _ (fun i => by simp) p,
        finsupp_sum_single_emb_apply c (fun p => (p.1, p.2 + 1))
          (fun a b h => by simpa [Prod.ext_iff] using h) _ (fun i => by simp) p] at hval'
      exact hval'.symm

    have hsupp : ∀ p : ℤ × ℤ, p ≠ (0, 0) → c p = 0 := by
      intro p hp
      by_cases h2 : p.2 = 0
      ·
        have h1 : p.1 ≠ 0 := by
          intro h1; apply hp; ext <;> simp [h1, h2]
        have := hcomY p
        have hne : (↑(q ^ p.1) : ℂ) - 1 ≠ 0 := by
          intro hcontra
          exact h1 (zpow_eq_one_imp q hq (by linear_combination hcontra))
        have : c p * ((↑(q ^ p.1) : ℂ) - 1) = 0 := by linear_combination this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hne
      · have := hcomX p
        have hne : (↑(q ^ p.2) : ℂ) - 1 ≠ 0 := by
          intro hcontra
          exact h2 (zpow_eq_one_imp q hq (by linear_combination hcontra))
        have : c p * ((↑(q ^ p.2) : ℂ) - 1) = 0 := by linear_combination this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hne

    have hcsingle : c = single (0, 0) (c (0, 0)) := by
      ext p
      by_cases hp : p = (0, 0)
      · subst hp; simp
      · rw [hsupp p hp, Finsupp.single_apply, if_neg (by simpa [eq_comm] using hp)]
    have hfscalar : f = (c (0, 0)) • (1 : Module.End ℂ (Auxiliary ℂ)) := by
      rw [hfc]
      conv_lhs => rw [hcsingle]
      rw [Finsupp.linearCombination_single, twistedLatticeShift_zero_zero]

    rw [Algebra.mem_bot]
    refine ⟨c (0, 0), ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
    exact hfscalar.symm
  ·
    intro x hx
    rw [Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [Subalgebra.mem_center_iff]
    intro b
    exact (Algebra.commutes r b).symm


private noncomputable def gX : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (1, 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩

private noncomputable def gX' : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (-1, 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩

private noncomputable def gY : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (0, 1), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩

private noncomputable def gY' : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (0, -1), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩

private noncomputable def gMono (p : ℤ × ℤ) : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q p, twistedLatticeShift_mem_generatedSubalgebra ℂ q p⟩

@[simp] private theorem coe_gX :
    ((gX q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) = twistedLatticeShift ℂ q (1, 0) := rfl
@[simp] private theorem coe_gX' :
    ((gX' q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) = twistedLatticeShift ℂ q (-1, 0) := rfl
@[simp] private theorem coe_gY :
    ((gY q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) = twistedLatticeShift ℂ q (0, 1) := rfl
@[simp] private theorem coe_gY' :
    ((gY' q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) = twistedLatticeShift ℂ q (0, -1) := rfl
@[simp] private theorem coe_gMono (p : ℤ × ℤ) :
    ((gMono q p : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) = twistedLatticeShift ℂ q p := rfl


private noncomputable def kappa (a : twistedLatticeShiftSubalgebra ℂ q) : Auxiliary ℂ :=
  (a : Module.End ℂ (Auxiliary ℂ)) (single (0, 0) 1)


private theorem kappa_eq_zero_iff (a : twistedLatticeShiftSubalgebra ℂ q) : kappa q a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hval : (a : Module.End ℂ (Auxiliary ℂ))
        = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q a) :=
      mem_qWeyl_eq_linearCombination q a.2
    rw [h, map_zero] at hval
    exact Subtype.ext hval
  · rintro rfl
    simp [kappa]


private theorem kappa_sub (a b : twistedLatticeShiftSubalgebra ℂ q) :
    kappa q (a - b) = kappa q a - kappa q b := by
  change ((a - b : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) (single (0, 0) 1) = _
  rw [AddSubgroupClass.coe_sub, LinearMap.sub_apply]
  rfl


private theorem kappa_smul (s : ℂ) (a : twistedLatticeShiftSubalgebra ℂ q) :
    kappa q (s • a) = s • kappa q a := by
  change ((s • a : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) (single (0, 0) 1) = _
  rw [show ((s • a : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ))
      = s • (a : Module.End ℂ (Auxiliary ℂ)) from map_smul (Subalgebra.val _) s a,
    LinearMap.smul_apply]
  rfl


private theorem kappa_conjX (a : twistedLatticeShiftSubalgebra ℂ q) (r : ℤ × ℤ) :
    kappa q (gX q * a * gX' q) r = ↑(q ^ (-r.2)) * kappa q a r := by
  have hval : (a : Module.End ℂ (Auxiliary ℂ))
      = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q a) :=
    mem_qWeyl_eq_linearCombination q a.2
  have key : kappa q (gX q * a * gX' q)
      = (kappa q a).sum fun p aa => single p (aa * ↑(q ^ (-p.2))) := by
    change ((gX q * a * gX' q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) (single (0, 0) 1)
      = _
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_gX, coe_gX',
      Module.End.mul_apply, Module.End.mul_apply,
      show twistedLatticeShift ℂ q (-1, 0) (single (0, 0) 1) = single (-1, 0) 1 by rw [twistedLatticeShift_apply_single]; simp,
      hval, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply, map_finsuppSum]
    refine Finsupp.sum_congr fun p _ => ?_
    rw [LinearMap.smul_apply, twistedLatticeShift_apply_single, Finsupp.smul_single, twistedLatticeShift_apply_single,
      show ((-1 + p.1) + 1, (0 + p.2) + 0) = p by
        obtain ⟨p1, p2⟩ := p; simp only [Prod.mk.injEq]; omega]
    congr 1
    simp only [zero_mul, zpow_zero, Units.val_one, one_mul, mul_one, smul_eq_mul, mul_neg_one]
  rw [key, finsupp_sum_single_emb_apply (kappa q a) (fun p => p) (fun _ _ h => h)
    (fun p aa => aa * ↑(q ^ (-p.2))) (fun p => by simp) r]
  ring


private theorem kappa_conjY (a : twistedLatticeShiftSubalgebra ℂ q) (r : ℤ × ℤ) :
    kappa q (gY q * a * gY' q) r = ↑(q ^ r.1) * kappa q a r := by
  have hval : (a : Module.End ℂ (Auxiliary ℂ))
      = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q a) :=
    mem_qWeyl_eq_linearCombination q a.2
  have key : kappa q (gY q * a * gY' q)
      = (kappa q a).sum fun p aa => single p (↑(q ^ p.1) * aa) := by
    change ((gY q * a * gY' q : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ)) (single (0, 0) 1)
      = _
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_gY, coe_gY',
      Module.End.mul_apply, Module.End.mul_apply,
      show twistedLatticeShift ℂ q (0, -1) (single (0, 0) 1) = single (0, -1) 1 by rw [twistedLatticeShift_apply_single]; simp,
      hval, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply, map_finsuppSum]
    refine Finsupp.sum_congr fun p _ => ?_
    rw [LinearMap.smul_apply, twistedLatticeShift_apply_single, Finsupp.smul_single, twistedLatticeShift_apply_single,
      show ((0 + p.1) + 0, (-1 + p.2) + 1) = p by
        obtain ⟨p1, p2⟩ := p; simp only [Prod.mk.injEq]; omega]
    congr 1
    simp only [mul_zero, zpow_zero, Units.val_one, mul_one, one_mul, zero_add, smul_eq_mul]
  rw [key, finsupp_sum_single_emb_apply (kappa q a) (fun p => p) (fun _ _ h => h)
    (fun p aa => ↑(q ^ p.1) * aa) (fun p => by simp) r]


/-- The displayed subalgebra is a simple ring when the parameter is not of finite order. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]
theorem isSimpleRing_of_not_isOfFinOrder (hq : ¬ IsOfFinOrder q) :
    IsSimpleRing (twistedLatticeShiftSubalgebra ℂ q) := by

  haveI : Nontrivial (twistedLatticeShiftSubalgebra ℂ q) := by
    refine ⟨1, 0, fun h => one_ne_zero (α := Module.End ℂ (Auxiliary ℂ)) ?_⟩
    simpa using congrArg Subtype.val h

  have hpow_ne : ∀ m n : ℤ, m ≠ n → (↑(q ^ m) : ℂ) ≠ ↑(q ^ n) := by
    intro m n hmn hcontra
    exact hmn ((injective_zpow_iff_not_isOfFinOrder.mpr hq) (Units.ext hcontra))
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  rw [or_iff_not_imp_left]
  intro hIbot
  obtain ⟨a₀, ha₀I, ha₀ne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hIbot : ⊥ < I)
  rw [TwoSidedIdeal.mem_bot] at ha₀ne

  suffices H : ∀ n : ℕ, ∀ a : twistedLatticeShiftSubalgebra ℂ q, a ∈ I → a ≠ 0 →
      (kappa q a).support.card = n → I = ⊤ from H _ a₀ ha₀I ha₀ne rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a haI ha0 hcard
    have hne0 : kappa q a ≠ 0 := fun h => ha0 ((kappa_eq_zero_iff q a).mp h)
    have hpos : 0 < n := by
      rw [← hcard]; exact Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr hne0)
    rcases Nat.lt_or_ge n 2 with hlt2 | hge2
    ·
      have hn1 : n = 1 := by omega
      obtain ⟨p₀, hsupp⟩ := Finset.card_eq_one.mp (by rw [hcard, hn1])
      obtain ⟨hκ0, hκeq⟩ := Finsupp.support_eq_singleton.mp hsupp
      have hval : (a : Module.End ℂ (Auxiliary ℂ))
          = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q a) :=
        mem_qWeyl_eq_linearCombination q a.2
      have haval : (a : Module.End ℂ (Auxiliary ℂ)) = kappa q a p₀ • twistedLatticeShift ℂ q p₀ := by
        conv_lhs => rw [hval, hκeq]
        rw [Finsupp.linearCombination_single]
      set κ := kappa q a p₀ with hκ
      set w : ℂ := ↑(q ^ ((-p₀).2 * p₀.1)) with hw
      have hwne : w ≠ 0 := by rw [hw]; exact Units.ne_zero _
      have hinv : ((κ⁻¹ * w⁻¹) • twistedLatticeShift ℂ q (-p₀)) * (κ • twistedLatticeShift ℂ q p₀)
          = (1 : Module.End ℂ (Auxiliary ℂ)) := by
        rw [smul_mul_smul_comm, twistedLatticeShift_mul, smul_smul,
          show ((-p₀).1 + p₀.1, (-p₀).2 + p₀.2) = ((0 : ℤ), (0 : ℤ)) by
            obtain ⟨a, b⟩ := p₀; simp only [Prod.neg_mk, Prod.mk.injEq]; omega,
          twistedLatticeShift_zero_zero, ← hw,
          show ((κ⁻¹ * w⁻¹) * κ) * w = 1 by
            rw [show ((κ⁻¹ * w⁻¹) * κ) * w = (κ⁻¹ * κ) * (w⁻¹ * w) by ring,
              inv_mul_cancel₀ hκ0, inv_mul_cancel₀ hwne, mul_one],
          one_smul]
      have hva : ((κ⁻¹ * w⁻¹) • gMono q (-p₀)) * a = 1 := by
        apply Subtype.ext
        rw [MulMemClass.coe_mul, OneMemClass.coe_one,
          show (((κ⁻¹ * w⁻¹) • gMono q (-p₀) : twistedLatticeShiftSubalgebra ℂ q) : Module.End ℂ (Auxiliary ℂ))
            = (κ⁻¹ * w⁻¹) • twistedLatticeShift ℂ q (-p₀) from Subalgebra.coe_smul _ _ _,
          haval]
        exact hinv
      exact (TwoSidedIdeal.one_mem_iff I).mp (hva ▸ I.mul_mem_left _ _ haI)
    ·
      obtain ⟨p, hpmem, p', hp'mem, hpp'⟩ :=
        Finset.one_lt_card.mp (by rw [hcard]; omega : 1 < (kappa q a).support.card)
      have hcp' : kappa q a p' ≠ 0 := Finsupp.mem_support_iff.mp hp'mem
      by_cases hcoord : p.2 = p'.2
      ·
        have hp1 : p.1 ≠ p'.1 := fun h => hpp' (Prod.ext_iff.mpr ⟨h, hcoord⟩)
        set b : twistedLatticeShiftSubalgebra ℂ q := gY q * a * gY' q - (↑(q ^ p.1) : ℂ) • a with hb
        have hbI : b ∈ I :=
          I.sub_mem (I.mul_mem_right _ _ (I.mul_mem_left _ _ haI))
            (by rw [Algebra.smul_def]; exact I.mul_mem_left _ _ haI)
        have hbr : ∀ r, kappa q b r = (↑(q ^ r.1) - ↑(q ^ p.1)) * kappa q a r := by
          intro r
          rw [hb, kappa_sub, kappa_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
            kappa_conjY]
          ring
        have hbp : kappa q b p = 0 := by rw [hbr]; simp
        have hbp' : kappa q b p' ≠ 0 := by
          rw [hbr]
          exact mul_ne_zero (sub_ne_zero.mpr (hpow_ne _ _ (by omega))) hcp'
        have hbne : b ≠ 0 := by
          intro h; apply hbp'; rw [h]; simp [kappa]
        have hsub : (kappa q b).support ⊆ (kappa q a).support.erase p := by
          intro r hr
          rw [Finsupp.mem_support_iff] at hr
          rw [Finset.mem_erase]
          refine ⟨fun hrp => hr (by rw [hrp, hbp]), ?_⟩
          rw [Finsupp.mem_support_iff]
          intro hcontra
          exact hr (by rw [hbr, hcontra, mul_zero])
        have hcardlt : (kappa q b).support.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hpmem)
        exact ih _ hcardlt b hbI hbne rfl
      ·
        set b : twistedLatticeShiftSubalgebra ℂ q := gX q * a * gX' q - (↑(q ^ (-p.2)) : ℂ) • a with hb
        have hbI : b ∈ I :=
          I.sub_mem (I.mul_mem_right _ _ (I.mul_mem_left _ _ haI))
            (by rw [Algebra.smul_def]; exact I.mul_mem_left _ _ haI)
        have hbr : ∀ r, kappa q b r = (↑(q ^ (-r.2)) - ↑(q ^ (-p.2))) * kappa q a r := by
          intro r
          rw [hb, kappa_sub, kappa_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
            kappa_conjX]
          ring
        have hbp : kappa q b p = 0 := by rw [hbr]; simp
        have hbp' : kappa q b p' ≠ 0 := by
          rw [hbr]
          exact mul_ne_zero (sub_ne_zero.mpr (hpow_ne _ _ (by omega))) hcp'
        have hbne : b ≠ 0 := by
          intro h; apply hbp'; rw [h]; simp [kappa]
        have hsub : (kappa q b).support ⊆ (kappa q a).support.erase p := by
          intro r hr
          rw [Finsupp.mem_support_iff] at hr
          rw [Finset.mem_erase]
          refine ⟨fun hrp => hr (by rw [hrp, hbp]), ?_⟩
          rw [Finsupp.mem_support_iff]
          intro hcontra
          exact hr (by rw [hbr, hcontra, mul_zero])
        have hcardlt : (kappa q b).support.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hpmem)
        exact ih _ hcardlt b hbI hbne rfl


/-- Raising the parameter to the complex dimension of the module gives one. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]
theorem pow_finrank_eq_one
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V] :
    (q : ℂ) ^ (Module.finrank ℂ V) = 1 := by

  set ρ := Algebra.lsmul ℂ ℂ V (A := twistedLatticeShiftSubalgebra ℂ q) with hρ

  set X : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (1, 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hX
  set Y : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (0, 1), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hY
  set X' : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (-1, 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hX'
  set Y' : twistedLatticeShiftSubalgebra ℂ q := ⟨twistedLatticeShift ℂ q (0, -1), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ with hY'

  have hXX' : X * X' = 1 := by apply Subtype.ext; simpa using twistedLatticeShift_auxiliary_identity_three ℂ q
  have hYY' : Y * Y' = 1 := by apply Subtype.ext; simpa using twistedLatticeShift_auxiliary_identity_four ℂ q

  have hrel : Y * X = (q : ℂ) • (X * Y) := by
    apply Subtype.ext; simpa using twistedLatticeShift_generators_commute_up_to_unit ℂ q

  have hdetX : LinearMap.det (ρ X) ≠ 0 := by
    have h : LinearMap.det (ρ X) * LinearMap.det (ρ X') = 1 := by
      rw [← map_mul LinearMap.det, ← map_mul ρ, hXX', map_one, map_one]
    exact left_ne_zero_of_mul_eq_one h
  have hdetY : LinearMap.det (ρ Y) ≠ 0 := by
    have h : LinearMap.det (ρ Y) * LinearMap.det (ρ Y') = 1 := by
      rw [← map_mul LinearMap.det, ← map_mul ρ, hYY', map_one, map_one]
    exact left_ne_zero_of_mul_eq_one h

  have hρrel : ρ Y * ρ X = (q : ℂ) • (ρ X * ρ Y) := by
    rw [← map_mul, hrel, map_smul, map_mul]
  have hdet := congrArg LinearMap.det hρrel
  rw [map_mul, LinearMap.det_smul, map_mul] at hdet

  have hne : LinearMap.det (ρ X) * LinearMap.det (ρ Y) ≠ 0 := mul_ne_zero hdetX hdetY
  have key : (q : ℂ) ^ Module.finrank ℂ V * (LinearMap.det (ρ X) * LinearMap.det (ρ Y)) =
      1 * (LinearMap.det (ρ X) * LinearMap.det (ρ Y)) := by
    rw [one_mul, ← hdet]; ring
  exact mul_right_cancel₀ hne key


/-- A nontrivial finite-dimensional module forces the parameter to have finite order. -/
theorem isOfFinOrder_of_nontrivial_finiteModule
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V] [Nontrivial V] :
    IsOfFinOrder q := by

  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hpow : (q : ℂ) ^ Module.finrank ℂ V = 1 := pow_finrank_eq_one q V

  have hqpow : q ^ Module.finrank ℂ V = 1 := by
    apply Units.ext; push_cast; simpa using hpow
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨Module.finrank ℂ V, hpos, hqpow⟩


private theorem gMono_one : gMono q (0, 0) = 1 := by
  apply Subtype.ext; rw [coe_gMono, OneMemClass.coe_one, twistedLatticeShift_zero_zero]


private theorem gMono_mul' (p r : ℤ × ℤ) :
    gMono q p * gMono q r
      = (↑(q ^ (p.2 * r.1)) : ℂ) • gMono q (p.1 + r.1, p.2 + r.2) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_gMono, coe_gMono, Subalgebra.coe_smul, coe_gMono, twistedLatticeShift_mul]


private theorem mem_center_of_comm_qMono (a : twistedLatticeShiftSubalgebra ℂ q)
    (h : ∀ p : ℤ × ℤ, (a : Module.End ℂ (Auxiliary ℂ)) * twistedLatticeShift ℂ q p
        = twistedLatticeShift ℂ q p * (a : Module.End ℂ (Auxiliary ℂ))) :
    a ∈ Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  set f := (a : Module.End ℂ (Auxiliary ℂ)) with hf
  have hb : (b : Module.End ℂ (Auxiliary ℂ))
      = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q b) :=
    mem_qWeyl_eq_linearCombination q b.2
  rw [hb, Finsupp.linearCombination_apply, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← h p]


private theorem gMono_mem_center_of (a b : ℤ) (ha : q ^ a = 1) (hb : q ^ b = 1) :
    gMono q (a, b) ∈ Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) := by
  apply mem_center_of_comm_qMono
  intro p
  obtain ⟨p1, p2⟩ := p
  simp only [coe_gMono]
  rw [twistedLatticeShift_mul, twistedLatticeShift_mul]
  have h1 : (↑(q ^ ((a, b).2 * (p1, p2).1)) : ℂ) = 1 := by
    change (↑(q ^ (b * p1)) : ℂ) = 1
    rw [zpow_mul, hb, one_zpow, Units.val_one]
  have h2 : (↑(q ^ ((p1, p2).2 * (a, b).1)) : ℂ) = 1 := by
    change (↑(q ^ (p2 * a)) : ℂ) = 1
    rw [mul_comm, zpow_mul, ha, one_zpow, Units.val_one]
  rw [h1, h2, one_smul, one_smul]
  congr 1
  simp only [Prod.mk.injEq]
  omega


private theorem gMono_natpow_x (m : ℤ) (k : ℕ) :
    gMono q (m, 0) ^ k = gMono q (m * (k : ℤ), 0) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, gMono_one]
  | succ k ih =>
    have hk : m * (↑(k + 1) : ℤ) = m * ↑k + m := by push_cast; ring
    rw [pow_succ, ih, gMono_mul', hk]
    simp


private theorem gMono_natpow_y (m : ℤ) (k : ℕ) :
    gMono q (0, m) ^ k = gMono q (0, m * (k : ℤ)) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, gMono_one]
  | succ k ih =>
    have hk : m * (↑(k + 1) : ℤ) = m * ↑k + m := by push_cast; ring
    rw [pow_succ, ih, gMono_mul', hk]
    simp


private theorem eq_finsupp_sum_gMono (a : twistedLatticeShiftSubalgebra ℂ q) :
    a = (kappa q a).sum (fun p c => c • gMono q p) := by
  apply Subtype.ext
  have hval : (a : Module.End ℂ (Auxiliary ℂ))
      = Finsupp.linearCombination ℂ (twistedLatticeShift ℂ q) (kappa q a) :=
    mem_qWeyl_eq_linearCombination q a.2
  rw [hval, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, coe_gMono]


/-- For a finite-order parameter, the center is generated by the four displayed elements. -/
@[source_ref "Chapter2/Problem2.7.5" (role := primary)]
theorem center_eq_adjoin_generators_of_isOfFinOrder (_hq : IsOfFinOrder q) :
    Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) =
      Algebra.adjoin ℂ
        { (⟨twistedLatticeShift ℂ q ((orderOf q : ℤ), 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ : twistedLatticeShiftSubalgebra ℂ q),
          ⟨twistedLatticeShift ℂ q (-(orderOf q : ℤ), 0), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩,
          ⟨twistedLatticeShift ℂ q (0, (orderOf q : ℤ)), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩,
          ⟨twistedLatticeShift ℂ q (0, -(orderOf q : ℤ)), twistedLatticeShift_mem_generatedSubalgebra ℂ q _⟩ } := by
  set n : ℕ := orderOf q with hn
  have hqn : q ^ (n : ℤ) = 1 := by rw [zpow_natCast, hn]; exact pow_orderOf_eq_one q

  change Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) =
      Algebra.adjoin ℂ
        {gMono q ((n : ℤ), 0), gMono q (-(n : ℤ), 0),
         gMono q (0, (n : ℤ)), gMono q (0, -(n : ℤ))}
  set S : Set (twistedLatticeShiftSubalgebra ℂ q) :=
    {gMono q ((n : ℤ), 0), gMono q (-(n : ℤ), 0),
     gMono q (0, (n : ℤ)), gMono q (0, -(n : ℤ))} with hS

  have hx_pos : gMono q ((n : ℤ), 0) ∈ Algebra.adjoin ℂ S :=
    Algebra.subset_adjoin (by rw [hS]; simp)
  have hx_neg : gMono q (-(n : ℤ), 0) ∈ Algebra.adjoin ℂ S :=
    Algebra.subset_adjoin (by rw [hS]; simp)
  have hy_pos : gMono q (0, (n : ℤ)) ∈ Algebra.adjoin ℂ S :=
    Algebra.subset_adjoin (by rw [hS]; simp)
  have hy_neg : gMono q (0, -(n : ℤ)) ∈ Algebra.adjoin ℂ S :=
    Algebra.subset_adjoin (by rw [hS]; simp)

  have hx_mul : ∀ a : ℤ, gMono q ((n : ℤ) * a, 0) ∈ Algebra.adjoin ℂ S := by
    intro a
    rcases le_or_gt 0 a with ha | ha
    · have he : gMono q ((n : ℤ), 0) ^ a.toNat = gMono q ((n : ℤ) * a, 0) := by
        rw [gMono_natpow_x, Int.toNat_of_nonneg ha]
      rw [← he]; exact pow_mem hx_pos _
    · have harg : -(n : ℤ) * (-a) = (n : ℤ) * a := by ring
      have he : gMono q (-(n : ℤ), 0) ^ (-a).toNat = gMono q ((n : ℤ) * a, 0) := by
        rw [gMono_natpow_x, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -a), harg]
      rw [← he]; exact pow_mem hx_neg _
  have hy_mul : ∀ b : ℤ, gMono q (0, (n : ℤ) * b) ∈ Algebra.adjoin ℂ S := by
    intro b
    rcases le_or_gt 0 b with hb | hb
    · have he : gMono q (0, (n : ℤ)) ^ b.toNat = gMono q (0, (n : ℤ) * b) := by
        rw [gMono_natpow_y, Int.toNat_of_nonneg hb]
      rw [← he]; exact pow_mem hy_pos _
    · have harg : -(n : ℤ) * (-b) = (n : ℤ) * b := by ring
      have he : gMono q (0, -(n : ℤ)) ^ (-b).toNat = gMono q (0, (n : ℤ) * b) := by
        rw [gMono_natpow_y, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -b), harg]
      rw [← he]; exact pow_mem hy_neg _

  have gMono_mem_adjoin : ∀ p : ℤ × ℤ, (n : ℤ) ∣ p.1 → (n : ℤ) ∣ p.2 →
      gMono q p ∈ Algebra.adjoin ℂ S := by
    rintro ⟨p1, p2⟩ ⟨a, rfl⟩ ⟨b, rfl⟩
    have hprod : gMono q ((n : ℤ) * a, 0) * gMono q (0, (n : ℤ) * b)
        = gMono q ((n : ℤ) * a, (n : ℤ) * b) := by
      rw [gMono_mul']; simp
    rw [← hprod]
    exact mul_mem (hx_mul a) (hy_mul b)
  refine le_antisymm ?_ ?_
  ·
    intro z hz
    have hXX' : gX q * gX' q = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, coe_gX, coe_gX', OneMemClass.coe_one]
      exact twistedLatticeShift_auxiliary_identity_three ℂ q
    have hYY' : gY q * gY' q = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, coe_gY, coe_gY', OneMemClass.coe_one]
      exact twistedLatticeShift_auxiliary_identity_four ℂ q

    have hconjX : gX q * z * gX' q = z := by
      rw [Subalgebra.mem_center_iff.mp hz (gX q), mul_assoc, hXX', mul_one]
    have hconjY : gY q * z * gY' q = z := by
      rw [Subalgebra.mem_center_iff.mp hz (gY q), mul_assoc, hYY', mul_one]

    have hrelX : ∀ r : ℤ × ℤ, (↑(q ^ (-r.2)) : ℂ) * kappa q z r = kappa q z r := by
      intro r; have h := kappa_conjX q z r; rw [hconjX] at h; exact h.symm
    have hrelY : ∀ r : ℤ × ℤ, (↑(q ^ r.1) : ℂ) * kappa q z r = kappa q z r := by
      intro r; have h := kappa_conjY q z r; rw [hconjY] at h; exact h.symm
    rw [eq_finsupp_sum_gMono q z]
    simp only [Finsupp.sum]
    refine sum_mem ?_
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    apply Subalgebra.smul_mem

    have hq1 : q ^ p.1 = 1 := by
      have h := hrelY p
      have h0 : ((↑(q ^ p.1) : ℂ) - 1) * kappa q z p = 0 := by linear_combination h
      rcases mul_eq_zero.mp h0 with h' | h'
      · apply Units.ext; simpa using sub_eq_zero.mp h'
      · exact absurd h' hp
    have hq2 : q ^ p.2 = 1 := by
      have h := hrelX p
      have h0 : ((↑(q ^ (-p.2)) : ℂ) - 1) * kappa q z p = 0 := by linear_combination h
      rcases mul_eq_zero.mp h0 with h' | h'
      · have hneg : q ^ (-p.2) = 1 := by apply Units.ext; simpa using sub_eq_zero.mp h'
        rw [zpow_neg] at hneg
        exact inv_eq_one.mp hneg
      · exact absurd h' hp
    have hd1 : (n : ℤ) ∣ p.1 := by rw [hn]; exact orderOf_dvd_iff_zpow_eq_one.mpr hq1
    have hd2 : (n : ℤ) ∣ p.2 := by rw [hn]; exact orderOf_dvd_iff_zpow_eq_one.mpr hq2
    exact gMono_mem_adjoin p hd1 hd2
  ·
    apply Algebra.adjoin_le
    intro g hg
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact gMono_mem_center_of q (n : ℤ) 0 hqn (zpow_zero q)
    · exact gMono_mem_center_of q (-(n : ℤ)) 0 (by rw [zpow_neg, hqn, inv_one]) (zpow_zero q)
    · exact gMono_mem_center_of q 0 (n : ℤ) (zpow_zero q) hqn
    · exact gMono_mem_center_of q 0 (-(n : ℤ)) (zpow_zero q) (by rw [zpow_neg, hqn, inv_one])


private lemma mem_of_invariant (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V] [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] (Wk : Submodule ℂ V)
    (hstab : ∀ (a : twistedLatticeShiftSubalgebra ℂ q) (z : V), z ∈ Wk → a • z ∈ Wk)
    (hne : ∃ z ∈ Wk, z ≠ 0) : ∀ z : V, z ∈ Wk := by
  let WA : Submodule (twistedLatticeShiftSubalgebra ℂ q) V :=
    { carrier := Wk
      add_mem' := fun ha hb => Wk.add_mem ha hb
      zero_mem' := Wk.zero_mem
      smul_mem' := fun a z hz => hstab a z hz }
  have hbot : WA ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := hne
    intro hh
    apply hz0
    have hzWA : z ∈ WA := hz
    rw [hh, Submodule.mem_bot] at hzWA
    exact hzWA
  let hSimple : IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V := inferInstance
  have hWA : WA = ⊤ := (hSimple.eq_bot_or_eq_top WA).resolve_left hbot
  intro z
  have : z ∈ WA := hWA ▸ Submodule.mem_top
  exact this


private lemma central_smul_scalar (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V] [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V]
    [FiniteDimensional ℂ V] [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V]
    (z : twistedLatticeShiftSubalgebra ℂ q) (hz : z ∈ Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q)) :
    ∃ μ : ℂ, ∀ w : V, z • w = μ • w := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (twistedLatticeShiftSubalgebra ℂ q) V
  obtain ⟨μ, hμ⟩ := (Algebra.lsmul ℂ ℂ V z).exists_eigenvalue
  refine ⟨μ, ?_⟩
  have hstab : ∀ (a : twistedLatticeShiftSubalgebra ℂ q) (w : V),
      w ∈ Module.End.eigenspace (Algebra.lsmul ℂ ℂ V z) μ →
      a • w ∈ Module.End.eigenspace (Algebra.lsmul ℂ ℂ V z) μ := by
    intro a w hw
    rw [Module.End.mem_eigenspace_iff, Algebra.lsmul_apply] at hw ⊢
    calc z • (a • w) = (a * z) • w := by
              rw [← mul_smul, ← Subalgebra.mem_center_iff.mp hz a]
      _ = a • (z • w) := by rw [mul_smul]
      _ = a • (μ • w) := by rw [hw]
      _ = μ • (a • w) := by rw [smul_comm]
  obtain ⟨w0, hw0⟩ := hμ.exists_hasEigenvector
  have hmem := mem_of_invariant q V (Module.End.eigenspace (Algebra.lsmul ℂ ℂ V z) μ)
    hstab ⟨w0, hw0.1, hw0.2⟩
  intro w
  have hw := hmem w
  rw [Module.End.mem_eigenspace_iff, Algebra.lsmul_apply] at hw
  exact hw


/-- A finite simple module of the specified dimension has a basis with the displayed generator actions. -/
theorem exists_generator_eigenbasis
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] (N : ℕ) [NeZero N] (hqorder : orderOf q = N) :
    ∃ (α β : ℂˣ) (b : Module.Basis (Fin N) ℂ V),
      (∀ i : Fin N, monomial q (0, 1) • b i = ((β : ℂ) * (q : ℂ) ^ (i : ℕ)) • b i) ∧
      (∀ i : Fin N, monomial q (1, 0) • b i
        = (if (i + 1 : Fin N) = 0 then (α : ℂ) else 1) • b (i + 1)) := by
  subst hqorder
  haveI : Nontrivial V := IsSimpleModule.nontrivial (twistedLatticeShiftSubalgebra ℂ q) V

  have hn_pos : 0 < orderOf q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hqn : q ^ ((orderOf q : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact pow_orderOf_eq_one q
  set n : ℕ := orderOf q with hn

  set ρ := Algebra.lsmul ℂ ℂ V (A := twistedLatticeShiftSubalgebra ℂ q) with hρ

  obtain ⟨lam, hlam⟩ := (ρ (gMono q (0, 1))).exists_eigenvalue
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hYv : gMono q (0, 1) • v = lam • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv.1
    rw [hρ, Algebra.lsmul_apply] at h; exact h

  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hv0
    have h1 : gMono q (0, 1) • v = 0 := by rw [hYv, h0, zero_smul]
    have h2 : v = gMono q (0, -1) • (gMono q (0, 1) • v) := by
      rw [← mul_smul, gMono_mul']; simp [gMono_one]
    rw [h1, smul_zero] at h2; exact h2

  set w : ℤ → V := fun m => gMono q (m, 0) • v with hw
  have hw0 : w 0 = v := by
    change gMono q ((0 : ℤ), 0) • v = v
    rw [gMono_one, one_smul]

  have hshiftX : ∀ (a m : ℤ), gMono q (a, 0) • w m = w (a + m) := by
    intro a m
    change gMono q (a, 0) • (gMono q (m, 0) • v) = gMono q (a + m, 0) • v
    rw [← mul_smul, gMono_mul']; simp

  have hYw : ∀ m : ℤ, gMono q (0, 1) • w m = (↑(q ^ m) * lam) • w m := by
    intro m
    have e1 : gMono q (0, 1) * gMono q (m, 0) = (↑(q ^ m) : ℂ) • gMono q (m, 1) := by
      rw [gMono_mul']; simp
    have e2 : gMono q (m, 1) • v = lam • w m := by
      have e3 : gMono q (m, 0) * gMono q (0, 1) = gMono q (m, 1) := by rw [gMono_mul']; simp
      calc gMono q (m, 1) • v = (gMono q (m, 0) * gMono q (0, 1)) • v := by rw [e3]
        _ = gMono q (m, 0) • (gMono q (0, 1) • v) := by rw [mul_smul]
        _ = gMono q (m, 0) • (lam • v) := by rw [hYv]
        _ = lam • w m := by rw [smul_comm]
    change gMono q (0, 1) • (gMono q (m, 0) • v) = (↑(q ^ m) * lam) • w m
    rw [← mul_smul, e1, smul_assoc, e2, smul_smul]

  have hY'v : gMono q (0, -1) • v = lam⁻¹ • v := by
    have einv : gMono q (0, -1) * gMono q (0, 1) = 1 := by rw [gMono_mul']; simp [gMono_one]
    have key : lam • (gMono q (0, -1) • v) = v := by
      rw [smul_comm, ← hYv, ← mul_smul, einv, one_smul]
    calc gMono q (0, -1) • v = lam⁻¹ • (lam • (gMono q (0, -1) • v)) := by
          rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      _ = lam⁻¹ • v := by rw [key]
  have hY'w : ∀ m : ℤ, gMono q (0, -1) • w m = (↑(q ^ (-m)) * lam⁻¹) • w m := by
    intro m
    have e1 : gMono q (0, -1) * gMono q (m, 0) = (↑(q ^ (-m)) : ℂ) • gMono q (m, -1) := by
      rw [gMono_mul']; simp
    have e2 : gMono q (m, -1) • v = lam⁻¹ • w m := by
      have e3 : gMono q (m, 0) * gMono q (0, -1) = gMono q (m, -1) := by rw [gMono_mul']; simp
      calc gMono q (m, -1) • v = (gMono q (m, 0) * gMono q (0, -1)) • v := by rw [e3]
        _ = gMono q (m, 0) • (gMono q (0, -1) • v) := by rw [mul_smul]
        _ = gMono q (m, 0) • (lam⁻¹ • v) := by rw [hY'v]
        _ = lam⁻¹ • w m := by rw [smul_comm]
    change gMono q (0, -1) • (gMono q (m, 0) • v) = (↑(q ^ (-m)) * lam⁻¹) • w m
    rw [← mul_smul, e1, smul_assoc, e2, smul_smul]

  have hwne : ∀ m : ℤ, w m ≠ 0 := by
    intro m hcontra
    apply hv0
    have hinv : gMono q (-m, 0) * gMono q (m, 0) = 1 := by rw [gMono_mul']; simp [gMono_one]
    have hvw : v = gMono q (-m, 0) • w m := by
      change v = gMono q (-m, 0) • (gMono q (m, 0) • v)
      rw [← mul_smul, hinv, one_smul]
    rw [hcontra, smul_zero] at hvw; exact hvw

  have hcenter : gMono q ((n : ℤ), 0) ∈ Subalgebra.center ℂ (twistedLatticeShiftSubalgebra ℂ q) := by
    apply mem_center_of_comm_qMono
    intro p
    simp only [coe_gMono]
    rw [twistedLatticeShift_mul, twistedLatticeShift_mul, zero_mul, zpow_zero, Units.val_one, one_smul, zero_add,
      show (q ^ (p.2 * (n : ℤ)) : ℂˣ) = 1 by rw [mul_comm, zpow_mul, hqn, one_zpow],
      Units.val_one, one_smul, add_zero, add_comm p.1 (n : ℤ)]
  obtain ⟨μ, hμ⟩ := central_smul_scalar q V (gMono q ((n : ℤ), 0)) hcenter
  have hperiod : ∀ m : ℤ, w ((n : ℤ) + m) = μ • w m := by
    intro m
    have hs := hshiftX (n : ℤ) m
    rw [hμ (w m)] at hs; exact hs.symm
  have hμne : μ ≠ 0 := by
    intro h0
    apply hwne (n : ℤ)
    have hs : w ((n : ℤ) + 0) = μ • w 0 := hperiod 0
    rw [add_zero, h0, zero_smul] at hs; exact hs

  set Wk : Submodule ℂ V := Submodule.span ℂ (Set.range (fun i : Fin n => w ((i : ℕ) : ℤ)))
    with hWk
  have hbasis_mem : ∀ i : Fin n, w ((i : ℕ) : ℤ) ∈ Wk := fun i => Submodule.subset_span ⟨i, rfl⟩

  have hpos : ∀ j : ℕ, w (j : ℤ) ∈ Wk := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < n
      · simpa using hbasis_mem ⟨j, hj⟩
      · have hjeq : (j : ℤ) = (n : ℤ) + ((j - n : ℕ) : ℤ) := by
          have : n ≤ j := not_lt.mp hj
          push_cast [this]; omega
        rw [hjeq, hperiod]
        exact Wk.smul_mem μ (ih (j - n) (by omega))
  have hneg : ∀ j : ℕ, w (-(j : ℤ)) ∈ Wk := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j ≤ n
      · have hnj : (n : ℤ) + (-(j : ℤ)) = ((n - j : ℕ) : ℤ) := by push_cast [hj]; omega
        have key := hperiod (-(j : ℤ))
        rw [hnj] at key
        have hwj : w (-(j : ℤ)) = μ⁻¹ • w ((n - j : ℕ) : ℤ) := by
          rw [key, smul_smul, inv_mul_cancel₀ hμne, one_smul]
        rw [hwj]; exact Wk.smul_mem _ (hpos (n - j))
      · have hjn : n < j := not_le.mp hj
        have hnj : (n : ℤ) + (-(j : ℤ)) = -((j - n : ℕ) : ℤ) := by omega
        have key := hperiod (-(j : ℤ))
        rw [hnj] at key
        have hwj : w (-(j : ℤ)) = μ⁻¹ • w (-((j - n : ℕ) : ℤ)) := by
          rw [key, smul_smul, inv_mul_cancel₀ hμne, one_smul]
        rw [hwj]; exact Wk.smul_mem _ (ih (j - n) (by omega))
  have hallmem : ∀ m : ℤ, w m ∈ Wk := by
    intro m
    rcases lt_or_ge m 0 with hm | hm
    · have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -m by omega)
      have hmeq : m = -((-m).toNat : ℤ) := by rw [h]; ring
      rw [hmeq]; exact hneg (-m).toNat
    · have h := Int.toNat_of_nonneg hm
      rw [← h]; exact hpos m.toNat

  have hstabX : ∀ z ∈ Wk, gMono q (1, 0) • z ∈ Wk := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; rw [hshiftX 1 _]; exact hallmem _
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have hstabX' : ∀ z ∈ Wk, gMono q (-1, 0) • z ∈ Wk := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; rw [hshiftX (-1) _]; exact hallmem _
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have hstabY : ∀ z ∈ Wk, gMono q (0, 1) • z ∈ Wk := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; rw [hYw _]; exact Wk.smul_mem _ (hallmem _)
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have hstabY' : ∀ z ∈ Wk, gMono q (0, -1) • z ∈ Wk := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; rw [hY'w _]; exact Wk.smul_mem _ (hallmem _)
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have hstab : ∀ (a : twistedLatticeShiftSubalgebra ℂ q) (z : V), z ∈ Wk → a • z ∈ Wk := by
    intro a
    obtain ⟨f, hf⟩ := a
    change f ∈ Algebra.adjoin ℂ
      {twistedLatticeShift ℂ q (1, 0), twistedLatticeShift ℂ q (-1, 0), twistedLatticeShift ℂ q (0, 1), twistedLatticeShift ℂ q (0, -1)} at hf
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact hstabX z hz
        · exact hstabX' z hz
        · exact hstabY z hz
        · exact hstabY' z hz
    | algebraMap r =>
        intro z hz
        change (algebraMap ℂ (twistedLatticeShiftSubalgebra ℂ q) r) • z ∈ Wk
        rw [algebraMap_smul]; exact Wk.smul_mem r hz
    | add x y hx hy ihx ihy =>
        intro z hz
        change ((⟨x, hx⟩ + ⟨y, hy⟩ : twistedLatticeShiftSubalgebra ℂ q)) • z ∈ Wk
        rw [add_smul]; exact Wk.add_mem (ihx z hz) (ihy z hz)
    | mul x y hx hy ihx ihy =>
        intro z hz
        change ((⟨x, hx⟩ * ⟨y, hy⟩ : twistedLatticeShiftSubalgebra ℂ q)) • z ∈ Wk
        rw [mul_smul]; exact ihx _ (ihy z hz)

  have hvWk : v ∈ Wk := by rw [← hw0]; exact hallmem 0
  have htop : ∀ z : V, z ∈ Wk := mem_of_invariant q V Wk hstab ⟨v, hvWk, hv0⟩

  have hinj : Function.Injective (fun i : Fin n => (↑(q ^ ((i : ℕ) : ℤ)) : ℂ) * lam) := by
    intro i j hij
    simp only at hij
    have h1 : (↑(q ^ ((i : ℕ) : ℤ)) : ℂ) = ↑(q ^ ((j : ℕ) : ℤ)) := mul_right_cancel₀ hlam0 hij
    rw [zpow_natCast, zpow_natCast] at h1
    have h3 : (i : ℕ) ≡ (j : ℕ) [MOD orderOf q] := pow_eq_pow_iff_modEq.mp (Units.ext h1)
    have hi : (i : ℕ) % orderOf q = (i : ℕ) := Nat.mod_eq_of_lt (by rw [← hn]; exact i.isLt)
    have hj : (j : ℕ) % orderOf q = (j : ℕ) := Nat.mod_eq_of_lt (by rw [← hn]; exact j.isLt)
    exact Fin.ext (by rw [← hi, ← hj]; exact h3)
  have heig : ∀ i : Fin n,
      (ρ (gMono q (0, 1))).HasEigenvector ((↑(q ^ ((i : ℕ) : ℤ)) : ℂ) * lam) (w ((i : ℕ) : ℤ)) := by
    intro i
    refine ⟨?_, hwne _⟩
    rw [Module.End.mem_eigenspace_iff, hρ, Algebra.lsmul_apply]
    exact hYw ((i : ℕ) : ℤ)
  have hli : LinearIndependent ℂ (fun i : Fin n => w ((i : ℕ) : ℤ)) :=
    Module.End.eigenvectors_linearIndependent' _ _ hinj _ heig

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range (fun i : Fin n => w ((i : ℕ) : ℤ))) := by
    rw [← hWk]; intro z _; exact htop z

  have hb : ∀ j : Fin n, (Module.Basis.mk hli hsp) j = w ((j : ℕ) : ℤ) := fun j => by
    rw [Module.Basis.coe_mk]
  have hzero : ((0 : Fin n) : ℕ) = 0 := by simp
  refine ⟨Units.mk0 μ hμne, Units.mk0 lam hlam0, Module.Basis.mk hli hsp, ?_, ?_⟩
  · intro i
    rw [hb i]
    change gMono q (0, 1) • w ((i : ℕ) : ℤ) = _
    rw [hYw ((i : ℕ) : ℤ), zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, mul_comm]
  · intro i
    have hvadd : ((i + 1 : Fin n) : ℕ) = ((i : ℕ) + 1) % n := by
      rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [hb i, hb (i + 1)]
    change gMono q (1, 0) • w ((i : ℕ) : ℤ) = _
    rw [hshiftX 1 ((i : ℕ) : ℤ)]
    by_cases hlast : (i : ℕ) + 1 = n
    ·
      have h0 : (i + 1 : Fin n) = 0 := by
        refine Fin.ext ?_
        rw [hvadd, hlast, Nat.mod_self, hzero]
      have hcast : ((i : ℕ) : ℤ) + 1 = (n : ℤ) := by exact_mod_cast hlast
      have heq : (1 : ℤ) + ((i : ℕ) : ℤ) = (n : ℤ) + 0 := by omega
      rw [if_pos h0, h0, hzero, heq, hperiod 0, Units.val_mk0, Nat.cast_zero]
    ·
      have hlt : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have hval : ((i + 1 : Fin n) : ℕ) = (i : ℕ) + 1 := by rw [hvadd, Nat.mod_eq_of_lt hlt]
      have h0 : (i + 1 : Fin n) ≠ 0 := by
        intro h
        rw [h, hzero] at hval
        omega
      have hcast : (1 : ℤ) + ((i : ℕ) : ℤ) = (((i : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [if_neg h0, hval, ← hcast, one_smul]


/-- The complex dimension of the finite simple module equals the multiplicative order of the parameter. -/
@[source_ref "Chapter2/Problem2.7.5" (role := primary)]
theorem finrank_eq_orderOf
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] :
    Module.finrank ℂ V = orderOf q := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (twistedLatticeShiftSubalgebra ℂ q) V
  haveI : NeZero (orderOf q) :=
    ⟨(orderOf_pos_iff.mpr (isOfFinOrder_of_nontrivial_finiteModule q V)).ne'⟩
  obtain ⟨-, -, b, -, -⟩ := exists_generator_eigenbasis q V (orderOf q) rfl
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

end RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules
