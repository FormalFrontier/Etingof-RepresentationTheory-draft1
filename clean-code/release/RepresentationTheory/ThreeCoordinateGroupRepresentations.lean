/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.PermutationDegreeThree
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences

noncomputable section

namespace RepresentationTheory.ThreeCoordinateGroupRepresentations

/-- A family of types indexed by a natural number. -/
@[ext]
structure ThreeCoordinateGroup (p : ℕ) where
  /-- Returns the first coordinate as an element of the residue ring. -/
  firstCoordinate : ZMod p
  /-- Returns the second coordinate as an element of the residue ring. -/
  secondCoordinate : ZMod p
  /-- Returns the third coordinate as an element of the residue ring. -/
  thirdCoordinate : ZMod p

namespace ThreeCoordinateGroup

variable {p : ℕ}

/-- Provides multiplication on the carrier. -/
instance instMul : Mul (ThreeCoordinateGroup p) :=
  ⟨fun x y => ⟨x.firstCoordinate + y.firstCoordinate, x.secondCoordinate + y.secondCoordinate, x.thirdCoordinate + y.thirdCoordinate + x.firstCoordinate * y.secondCoordinate⟩⟩

/-- Provides the identity element on the carrier. -/
instance instOne : One (ThreeCoordinateGroup p) := ⟨⟨0, 0, 0⟩⟩

/-- Provides inversion on the carrier. -/
instance instInv : Inv (ThreeCoordinateGroup p) :=
  ⟨fun x => ⟨-x.firstCoordinate, -x.secondCoordinate, -x.thirdCoordinate + x.firstCoordinate * x.secondCoordinate⟩⟩

/-- Computes the first coordinate of a product. -/
@[simp] theorem mul_firstCoordinate (x y : ThreeCoordinateGroup p) : (x * y).firstCoordinate = x.firstCoordinate + y.firstCoordinate := rfl
/-- Computes the second coordinate of a product. -/
@[simp] theorem mul_secondCoordinate (x y : ThreeCoordinateGroup p) : (x * y).secondCoordinate = x.secondCoordinate + y.secondCoordinate := rfl
/-- Computes the third coordinate of a product. -/
@[simp] theorem mul_thirdCoordinate (x y : ThreeCoordinateGroup p) : (x * y).thirdCoordinate = x.thirdCoordinate + y.thirdCoordinate + x.firstCoordinate * y.secondCoordinate := rfl
/-- The first coordinate of the identity is zero. -/
@[simp] theorem firstCoordinate_one : (1 : ThreeCoordinateGroup p).firstCoordinate = 0 := rfl
/-- The second coordinate of the identity is zero. -/
@[simp] theorem secondCoordinate_one : (1 : ThreeCoordinateGroup p).secondCoordinate = 0 := rfl
/-- The third coordinate of the identity is zero. -/
@[simp] theorem thirdCoordinate_one : (1 : ThreeCoordinateGroup p).thirdCoordinate = 0 := rfl
/-- Computes the first coordinate of an inverse. -/
@[simp] theorem inv_firstCoordinate (x : ThreeCoordinateGroup p) : x⁻¹.firstCoordinate = -x.firstCoordinate := rfl
/-- Computes the second coordinate of an inverse. -/
@[simp] theorem inv_secondCoordinate (x : ThreeCoordinateGroup p) : x⁻¹.secondCoordinate = -x.secondCoordinate := rfl
/-- Computes the third coordinate of an inverse. -/
@[simp] theorem inv_thirdCoordinate (x : ThreeCoordinateGroup p) : x⁻¹.thirdCoordinate = -x.thirdCoordinate + x.firstCoordinate * x.secondCoordinate := rfl

/-- Provides the group structure on the carrier. -/
instance instGroup : Group (ThreeCoordinateGroup p) where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp

/-- Selects a distinguished group element indexed by the modulus. -/
def firstGenerator (p : ℕ) : ThreeCoordinateGroup p := ⟨1, 0, 0⟩

/-- Selects a second distinguished group element indexed by the modulus. -/
def secondGenerator (p : ℕ) : ThreeCoordinateGroup p := ⟨0, 1, 0⟩

/-- Equates the carrier with a product of three residue rings. -/
def equivCoordinates (p : ℕ) : ThreeCoordinateGroup p ≃ ZMod p × ZMod p × ZMod p where
  toFun x := (x.firstCoordinate, x.secondCoordinate, x.thirdCoordinate)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv x := by cases x; rfl
  right_inv t := by rfl

instance : DecidableEq (ThreeCoordinateGroup p) := (equivCoordinates p).decidableEq

/-- Provides a finite enumeration when the index is nonzero. -/
instance instFintype [NeZero p] : Fintype (ThreeCoordinateGroup p) := Fintype.ofEquiv _ (equivCoordinates p).symm

/-- The carrier has cardinality equal to the cube of the index. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem card_eq_cube [NeZero p] : Fintype.card (ThreeCoordinateGroup p) = p ^ 3 := by
  rw [Fintype.card_congr (equivCoordinates p)]
  simp only [Fintype.card_prod, ZMod.card]
  ring

/-- Computes powers of the first distinguished element. -/
theorem firstGenerator_pow (n : ℕ) : (firstGenerator p) ^ n = ⟨(n : ZMod p), 0, 0⟩ := by
  induction n with
  | zero => ext <;> simp [firstGenerator]
  | succ k ih =>
    rw [pow_succ, ih]
    refine ThreeCoordinateGroup.ext ?_ ?_ ?_ <;> simp [firstGenerator]

/-- Computes powers of the second distinguished element. -/
theorem secondGenerator_pow (n : ℕ) : (secondGenerator p) ^ n = ⟨0, (n : ZMod p), 0⟩ := by
  induction n with
  | zero => ext <;> simp [secondGenerator]
  | succ k ih =>
    rw [pow_succ, ih]
    refine ThreeCoordinateGroup.ext ?_ ?_ ?_ <;> simp [secondGenerator]

/-- Computes powers of the element whose first two coordinates are zero and whose third coordinate is one. -/
theorem centralGenerator_pow (n : ℕ) :
    (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) ^ n = ⟨0, 0, (n : ZMod p)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    refine ThreeCoordinateGroup.ext ?_ ?_ ?_ <;> simp

/-- States a product relation among the displayed group elements. -/
theorem generator_relation [Fact p.Prime] :
    (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
      = firstGenerator p * secondGenerator p * firstGenerator p ^ (p - 1) * secondGenerator p ^ (p - 1) := by
  have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_pred (Fact.out : p.Prime).pos, ZMod.natCast_self]; ring
  rw [firstGenerator_pow, secondGenerator_pow, hp1]
  refine ThreeCoordinateGroup.ext ?_ ?_ ?_ <;> simp [firstGenerator, secondGenerator]

/-- Expresses every group element in terms of the displayed powers. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem normalForm [NeZero p] (g : ThreeCoordinateGroup p) :
    g = firstGenerator p ^ g.firstCoordinate.val * secondGenerator p ^ g.secondCoordinate.val
          * (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) ^ (g.thirdCoordinate - g.firstCoordinate * g.secondCoordinate).val := by
  rw [firstGenerator_pow, secondGenerator_pow, centralGenerator_pow]
  have hc : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse
  refine ThreeCoordinateGroup.ext ?_ ?_ ?_
  · simp [hc]
  · simp [hc]
  · simp only [mul_firstCoordinate, mul_thirdCoordinate, hc, mul_zero, add_zero, zero_add]; ring

/-- The displayed two elements generate the whole group. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem closure_generators_eq_top [Fact p.Prime] :
    Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) = ⊤ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine eq_top_iff.mpr fun g _ => ?_
  have hx : firstGenerator p ∈ Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) :=
    Submonoid.subset_closure (by simp)
  have hy : secondGenerator p ∈ Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) :=
    Submonoid.subset_closure (by simp)
  have hcentral : (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) ∈
      Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) := by
    rw [generator_relation]
    exact mul_mem (mul_mem (mul_mem hx hy) (pow_mem hx _)) (pow_mem hy _)
  rw [normalForm g]
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hcentral _)

end ThreeCoordinateGroup

open ThreeCoordinateGroup
open _root_.CategoryTheory

variable {p : ℕ}

/-- Reduces an exponent modulo the root order in the displayed power expression. -/
theorem root_pow_mod {z : ℂ} (hz : z ^ p = 1) (k : ℕ) : z ^ (k % p) = z ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hz, one_pow, mul_one]

/-- A root satisfying the displayed equation turns addition of residue exponents into multiplication. -/
theorem root_pow_add {z : ℂ} (hz : z ^ p = 1) [NeZero p] (m n : ZMod p) :
    z ^ (m + n).val = z ^ m.val * z ^ n.val := by
  rw [ZMod.val_add, root_pow_mod hz, pow_add]

/-- Defines a linear action on functions from a residue ring. -/
def shiftScaleAction (z : ℂ) (g : ThreeCoordinateGroup p) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun f := fun t => z ^ (g.secondCoordinate * t - g.thirdCoordinate).val * f (t - g.firstCoordinate)
  map_add' f₁ f₂ := by funext t; simp only [Pi.add_apply]; ring
  map_smul' r f := by
    funext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Computes the shift-scale action on a function value. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting), simp]
theorem shiftScaleAction_apply (z : ℂ) (g : ThreeCoordinateGroup p) (f : ZMod p → ℂ) (t : ZMod p) :
    shiftScaleAction z g f t = z ^ (g.secondCoordinate * t - g.thirdCoordinate).val * f (t - g.firstCoordinate) := rfl

/-- Defines a representation from a complex root of the displayed power equation. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
def shiftScaleRepresentation [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    Representation ℂ (ThreeCoordinateGroup p) (ZMod p → ℂ) where
  toFun := shiftScaleAction z
  map_one' := by
    refine LinearMap.ext fun f => funext fun t => ?_
    simp [shiftScaleAction_apply]
  map_mul' g g' := by
    refine LinearMap.ext fun f => funext fun t => ?_
    simp only [Module.End.mul_apply, shiftScaleAction_apply, mul_firstCoordinate, mul_secondCoordinate, mul_thirdCoordinate]
    rw [← mul_assoc, ← root_pow_add hz,
      show (g.secondCoordinate + g'.secondCoordinate) * t - (g.thirdCoordinate + g'.thirdCoordinate + g.firstCoordinate * g'.secondCoordinate)
          = (g.secondCoordinate * t - g.thirdCoordinate) + (g'.secondCoordinate * (t - g.firstCoordinate) - g'.thirdCoordinate) from by ring,
      show t - (g.firstCoordinate + g'.firstCoordinate) = t - g.firstCoordinate - g'.firstCoordinate from by ring]

/-- Computes the action of the shift-scale representation at a group element. -/
@[simp] theorem shiftScaleRepresentation_apply [NeZero p] (z : ℂ) (hz : z ^ p = 1) (g : ThreeCoordinateGroup p) :
    shiftScaleRepresentation z hz g = shiftScaleAction z g := rfl

/-- Computes the action of the first distinguished generator. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem shiftScaleRepresentation_firstGenerator_apply [NeZero p] (z : ℂ) (hz : z ^ p = 1) (f : ZMod p → ℂ) (t : ZMod p) :
    shiftScaleRepresentation z hz (firstGenerator p) f t = f (t - 1) := by
  simp [shiftScaleRepresentation_apply, shiftScaleAction_apply, firstGenerator]

/-- Computes the action of the second distinguished generator. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem shiftScaleRepresentation_secondGenerator_apply [NeZero p] (z : ℂ) (hz : z ^ p = 1) (f : ZMod p → ℂ) (t : ZMod p) :
    shiftScaleRepresentation z hz (secondGenerator p) f t = z ^ t.val * f t := by
  simp [shiftScaleRepresentation_apply, shiftScaleAction_apply, secondGenerator]

/-- There is a unique representation satisfying the displayed shift and scaling action formulas. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem existsUnique_shift_scale_representation [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) :
    ∃! ρ : Representation ℂ (ThreeCoordinateGroup p) (ZMod p → ℂ),
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (firstGenerator p) f) t = f (t - 1)) ∧
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (secondGenerator p) f) t = z ^ t.val * f t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨shiftScaleRepresentation z hz, ⟨fun f t => shiftScaleRepresentation_firstGenerator_apply z hz f t, fun f t => shiftScaleRepresentation_secondGenerator_apply z hz f t⟩, ?_⟩
  rintro ρ' ⟨hx', hy'⟩
  have ex : ρ' (firstGenerator p) = shiftScaleRepresentation z hz (firstGenerator p) := by
    refine LinearMap.ext fun f => funext fun t => ?_
    rw [hx' f t, shiftScaleRepresentation_firstGenerator_apply]
  have ey : ρ' (secondGenerator p) = shiftScaleRepresentation z hz (secondGenerator p) := by
    refine LinearMap.ext fun f => funext fun t => ?_
    rw [hy' f t, shiftScaleRepresentation_secondGenerator_apply]
  have ez : ρ' (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) = shiftScaleRepresentation z hz ⟨0, 0, 1⟩ := by
    rw [generator_relation]
    simp only [map_mul, map_pow, ex, ey]
  refine MonoidHom.ext fun g => ?_
  rw [normalForm g]
  simp only [map_mul, map_pow, ex, ey, ez]

/-- Characterizes simplicity of a representation satisfying the displayed action formulas. -/
@[source_ref "Chapter4/Problem4.12.2" (role := primary)]
theorem shiftScaleRepresentation_simple_iff [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (ThreeCoordinateGroup p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (firstGenerator p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (secondGenerator p) f) t = z ^ t.val * f t) :
    IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) ρ.asModule ↔ z ≠ 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hNTV : Nontrivial (ZMod p → ℂ) :=
    ⟨fun _ => 0, fun _ => 1, fun h => zero_ne_one (congrFun h (0 : ZMod p))⟩
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isSimpleOrder_iff]
  have X_single : ∀ s : ZMod p,
      ρ (firstGenerator p) (Pi.single s (1 : ℂ)) = Pi.single (s + 1) (1 : ℂ) := by
    intro s
    funext t
    rw [hx]
    simp only [Pi.single_apply]
    by_cases h : t - 1 = s
    · rw [if_pos h, if_pos (sub_eq_iff_eq_add.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (sub_eq_iff_eq_add.mpr hc))]
  constructor
  ·
    intro hsimple hz1
    set c0 : ZMod p → ℂ := fun _ => 1 with hc0
    have hXc : ρ (firstGenerator p) c0 = c0 := by funext t; simp [hx, hc0]
    have hYc : ρ (secondGenerator p) c0 = c0 := by funext t; simp [hy, hz1, hc0]
    set W₀ : Submodule ℂ (ZMod p → ℂ) := Submodule.span ℂ {c0} with hW₀
    have hfix : ∀ (op : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)), op c0 = c0 →
        ∀ v ∈ W₀, op v ∈ W₀ := by
      intro op hop v hv
      have hle : W₀ ≤ W₀.comap op := by
        rw [hW₀, Submodule.span_le]
        intro x hx'
        rw [Set.mem_singleton_iff] at hx'; subst hx'
        simp only [SetLike.mem_coe, Submodule.mem_comap, hop]
        exact Submodule.mem_span_singleton_self c0
      exact hle hv
    have hXW := hfix (ρ (firstGenerator p)) hXc
    have hYW := hfix (ρ (secondGenerator p)) hYc
    have hinv : ∀ (g : ThreeCoordinateGroup p) ⦃v : ZMod p → ℂ⦄, v ∈ W₀ → ρ g v ∈ W₀ := by
      let S : Submonoid (ThreeCoordinateGroup p) :=
        { carrier := {g | ∀ v ∈ W₀, ρ g v ∈ W₀}
          one_mem' := by intro v hv; rw [map_one]; simpa using hv
          mul_mem' := by
            intro a b ha hb v hv
            rw [map_mul]
            exact ha _ (hb v hv) }
      have hSle : Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) ≤ S :=
        Submonoid.closure_le.mpr (by
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact hXW
          · exact hYW)
      intro g v hv
      have hgS : g ∈ S :=
        hSle (by rw [ThreeCoordinateGroup.closure_generators_eq_top]; exact Submonoid.mem_top g)
      exact hgS v hv
    let σ₀ : Subrepresentation ρ := ⟨W₀, hinv⟩
    rcases hsimple.eq_bot_or_eq_top σ₀ with hbot | htop
    ·
      have h0 : W₀ = ⊥ := congrArg Subrepresentation.toSubmodule hbot
      have hc0mem : c0 ∈ W₀ := Submodule.mem_span_singleton_self c0
      rw [h0, Submodule.mem_bot] at hc0mem
      have : (1 : ℂ) = 0 := by simpa [hc0] using congrFun hc0mem 0
      exact one_ne_zero this
    ·
      have hW₀top : W₀ = ⊤ := congrArg Subrepresentation.toSubmodule htop
      have hmem : Pi.single (0 : ZMod p) (1 : ℂ) ∈ W₀ := by rw [hW₀top]; exact Submodule.mem_top
      rw [hW₀, Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      have e0 : a = 1 := by
        simpa [hc0, Pi.smul_apply, smul_eq_mul, Pi.single_apply] using congrFun ha 0
      have e1 : a = 0 := by
        have h := congrFun ha 1
        simp only [hc0, Pi.smul_apply, smul_eq_mul, mul_one, Pi.single_apply] at h
        rwa [if_neg (one_ne_zero : (1 : ZMod p) ≠ 0)] at h
      rw [e0] at e1
      exact one_ne_zero e1
  ·
    intro hzne
    have hc : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse
    have hdist : ∀ s t : ZMod p, z ^ s.val = z ^ t.val → s = t := by
      intro s t hst
      have horder : orderOf z = p := by
        rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf z)
            (orderOf_dvd_of_pow_eq_one hz) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hzne
        · exact h
      have hs : s.val < orderOf z := by rw [horder]; exact ZMod.val_lt s
      have ht : t.val < orderOf z := by rw [horder]; exact ZMod.val_lt t
      exact ZMod.val_injective p
        (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr ht) hst)
    have keySingle : ∀ (W : Submodule ℂ (ZMod p → ℂ)),
        (∀ v ∈ W, ρ (secondGenerator p) v ∈ W) → ∀ f ∈ W, f ≠ 0 →
        ∃ t, Pi.single t (1 : ℂ) ∈ W := by
      intro W hYW
      suffices H : ∀ n, ∀ f : ZMod p → ℂ, f ∈ W → f ≠ 0 →
          (Finset.univ.filter (fun t => f t ≠ 0)).card = n → ∃ t, Pi.single t (1 : ℂ) ∈ W by
        intro f hfW hf0; exact H _ f hfW hf0 rfl
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro f hfW hf0 hcard
        set S := Finset.univ.filter (fun t => f t ≠ 0) with hS
        have hSne : S.Nonempty := by
          rw [hS, Finset.filter_nonempty_iff]
          by_contra hcon
          push Not at hcon
          exact hf0 (funext fun t => hcon t (Finset.mem_univ t))
        rcases eq_or_lt_of_le (Finset.one_le_card.mpr hSne) with h1 | h2
        ·
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1.symm
          refine ⟨a, ?_⟩
          have hfa : f a ≠ 0 := by
            have : a ∈ S := ha ▸ Finset.mem_singleton_self a
            rw [hS, Finset.mem_filter] at this; exact this.2
          have hfeq : Pi.single a (1 : ℂ) = (f a)⁻¹ • f := by
            funext t
            by_cases h : t = a
            · subst h; simp [inv_mul_cancel₀ hfa]
            · have ht0 : f t = 0 := by
                by_contra hne
                have : t ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ t, hne⟩
                rw [ha, Finset.mem_singleton] at this; exact h this
              simp [h, ht0]
          rw [hfeq]
          exact Submodule.smul_mem _ _ hfW
        ·
          obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp h2
          set g : ZMod p → ℂ := ρ (secondGenerator p) f - (z ^ t₂.val) • f with hgdef
          have hgval : ∀ t, g t = (z ^ t.val - z ^ t₂.val) * f t := by
            intro t
            simp only [hgdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hy]
            ring
          have hgW : g ∈ W := Submodule.sub_mem _ (hYW f hfW) (Submodule.smul_mem _ _ hfW)
          have hft₁ : f t₁ ≠ 0 := by rw [hS, Finset.mem_filter] at ht₁; exact ht₁.2
          have hg0 : g ≠ 0 := by
            intro hcon
            have hval : g t₁ = 0 := congrFun hcon t₁
            rw [hgval] at hval
            have hz12 : z ^ t₁.val - z ^ t₂.val ≠ 0 :=
              fun he => hne (hdist _ _ (sub_eq_zero.mp he))
            exact mul_ne_zero hz12 hft₁ hval
          have hsub : Finset.univ.filter (fun t => g t ≠ 0) ⊆ S := by
            intro t ht
            rw [Finset.mem_filter] at ht
            rw [hS, Finset.mem_filter]
            refine ⟨Finset.mem_univ t, fun hf0' => ht.2 ?_⟩
            rw [hgval, hf0', mul_zero]
          have ht₂notin : t₂ ∉ Finset.univ.filter (fun t => g t ≠ 0) := by
            rw [Finset.mem_filter]; push Not
            intro _
            rw [hgval, sub_self, zero_mul]
          have hlt : (Finset.univ.filter (fun t => g t ≠ 0)).card < n := by
            rw [← hcard]
            exact Finset.card_lt_card
              ((Finset.ssubset_iff_of_subset hsub).mpr ⟨t₂, ht₂, ht₂notin⟩)
          exact ih _ hlt g hgW hg0 rfl
    have hNT : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, ?_⟩
      intro h
      exact absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top
    refine { toNontrivial := hNT, eq_bot_or_eq_top := fun σ => ?_ }
    rcases eq_or_ne σ.toSubmodule ⊥ with hbot | hne
    · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
    · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
      change σ.toSubmodule = ⊤
      obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff _).mp hne
      obtain ⟨t₀, ht₀⟩ :=
        keySingle σ.toSubmodule (fun v hv => σ.apply_mem_toSubmodule (secondGenerator p) hv) f hfW hf0
      have hall : ∀ s : ZMod p, Pi.single s (1 : ℂ) ∈ σ.toSubmodule := by
        have hpow : ∀ n : ℕ, Pi.single (t₀ + (n : ZMod p)) (1 : ℂ) ∈ σ.toSubmodule := by
          intro n
          induction n with
          | zero => simpa using ht₀
          | succ k ih =>
            have hstep := σ.apply_mem_toSubmodule (firstGenerator p) ih
            rw [X_single] at hstep
            have heq : t₀ + ((k + 1 : ℕ) : ZMod p) = t₀ + (k : ZMod p) + 1 := by push_cast; ring
            rw [heq]; exact hstep
        intro s
        have h := hpow (s - t₀).val
        have heq : t₀ + (s - t₀) = s := by abel
        rwa [hc (s - t₀), heq] at h
      rw [eq_top_iff]
      intro f' _
      have hf'eq : f' = ∑ s : ZMod p, f' s • Pi.single s (1 : ℂ) := by
        funext t
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
          mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ t f']
        simp
      rw [hf'eq]
      exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (hall s))

/-- Maps a three-coordinate group to the multiplicative form of a pair of residue-ring coordinates. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
def coordinateQuotientHom (p : ℕ) : ThreeCoordinateGroup p →* Multiplicative (ZMod p × ZMod p) where
  toFun g := Multiplicative.ofAdd (g.firstCoordinate, g.secondCoordinate)
  map_one' := rfl
  map_mul' x y := rfl

/-- Computes the coordinate quotient homomorphism. -/
@[simp] theorem coordinateQuotientHom_apply (p : ℕ) (g : ThreeCoordinateGroup p) :
    coordinateQuotientHom p g = Multiplicative.ofAdd (g.firstCoordinate, g.secondCoordinate) := rfl

/-- The coordinate quotient homomorphism is surjective. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem coordinateQuotientHom_surjective (p : ℕ) : Function.Surjective (coordinateQuotientHom p) := by
  intro y
  exact ⟨⟨(Multiplicative.toAdd y).1, (Multiplicative.toAdd y).2, 0⟩, rfl⟩

/-- The displayed central element belongs to the commutator subgroup. -/
theorem centralGenerator_mem_commutator [Fact p.Prime] :
    (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) ∈ commutator (ThreeCoordinateGroup p) := by
  have hcomm : (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
      = firstGenerator p * secondGenerator p * (firstGenerator p)⁻¹ * (secondGenerator p)⁻¹ := by
    refine ThreeCoordinateGroup.ext ?_ ?_ ?_ <;> simp [firstGenerator, secondGenerator]
  rw [commutator_def, hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The kernel of the coordinate quotient map lies in the kernel of each displayed character. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem ker_coordinateQuotient_le_ker [Fact p.Prime] (ρ : ThreeCoordinateGroup p →* ℂˣ) :
    (coordinateQuotientHom p).ker ≤ ρ.ker := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine le_trans ?_ (Abelianization.commutator_subset_ker ρ)
  intro g hg
  rw [MonoidHom.mem_ker, coordinateQuotientHom_apply] at hg
  have hab : (g.firstCoordinate, g.secondCoordinate) = (0, 0) := ofAdd_eq_one.mp hg
  have hga : g.firstCoordinate = 0 := (Prod.ext_iff.mp hab).1
  have hgb : g.secondCoordinate = 0 := (Prod.ext_iff.mp hab).2
  have hg_eq : g = (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) ^ g.thirdCoordinate.val := by
    rw [centralGenerator_pow]
    refine ThreeCoordinateGroup.ext hga hgb ?_
    exact (ZMod.natCast_rightInverse g.thirdCoordinate).symm
  rw [hg_eq]
  exact pow_mem centralGenerator_mem_commutator _

/-- Equates characters on the coordinate quotient with characters on the group. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
noncomputable def characterPrecompositionEquiv (p : ℕ) [Fact p.Prime] :
    (Multiplicative (ZMod p × ZMod p) →* ℂˣ) ≃ (ThreeCoordinateGroup p →* ℂˣ) :=
  (MonoidHom.liftOfSurjective (coordinateQuotientHom p) (coordinateQuotientHom_surjective p)).symm.trans
    (Equiv.subtypeUnivEquiv (fun ρ => ker_coordinateQuotient_le_ker ρ))

/-- Computes character transport along the coordinate quotient map. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting), simp]
theorem characterPrecompositionEquiv_apply [Fact p.Prime]
    (χ : Multiplicative (ZMod p × ZMod p) →* ℂˣ) :
    characterPrecompositionEquiv p χ = χ.comp (coordinateQuotientHom p) := rfl

/-- The displayed character space has cardinality equal to the square of the index. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem character_card_eq_square [Fact p.Prime] :
    Nat.card (ThreeCoordinateGroup p →* ℂˣ) = p ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero ((Monoid.exponent (Multiplicative (ZMod p × ZMod p)) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← Nat.card_congr (characterPrecompositionEquiv p),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative (ZMod p × ZMod p)) ℂ,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  ring

/-- Produces an invariant direct-sum decomposition into one-dimensional submodules under the stated action formulas. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem exists_invariant_line_decomposition [Fact p.Prime]
    (ρ : Representation ℂ (ThreeCoordinateGroup p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (firstGenerator p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (secondGenerator p) f) t = f t) :
    ∃ S : Fin p → Submodule ℂ (ZMod p → ℂ),
      (∀ i, ∀ (g : ThreeCoordinateGroup p), ∀ v ∈ S i, ρ g v ∈ S i) ∧
      (∀ i, Module.finrank ℂ (S i) = 1) ∧
      DirectSum.IsInternal S ∧
      ∃ χ : Fin p → (ThreeCoordinateGroup p →* ℂˣ),
        Function.Injective χ ∧
        ∀ i, ∀ (g : ThreeCoordinateGroup p), ∀ w ∈ S i, ρ g w = (χ i g : ℂ) • w := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  set chi : ZMod p → (ZMod p → ℂ) := fun j t => ζ ^ (j * t).val with hchi
  have chi_ne_zero : ∀ j : ZMod p, chi j ≠ 0 := by
    intro j hcon
    have h0 : chi j 0 = 0 := by rw [hcon]; rfl
    have h1 : (1 : ℂ) = 0 := by
      calc (1 : ℂ) = ζ ^ (j * 0).val := by rw [mul_zero, ZMod.val_zero, pow_zero]
        _ = chi j 0 := rfl
        _ = 0 := h0
    exact one_ne_zero h1
  have hxeig : ∀ j : ZMod p, ρ (firstGenerator p) (chi j) = (ζ ^ ((-j).val)) • chi j := by
    intro j
    funext t
    rw [hx, Pi.smul_apply, smul_eq_mul]
    change ζ ^ (j * (t - 1)).val = ζ ^ ((-j).val) * ζ ^ (j * t).val
    have he : j * (t - 1) = (-j) + j * t := by ring
    rw [he, root_pow_add hζp]
  have hyeig : ∀ j : ZMod p, ρ (secondGenerator p) (chi j) = chi j := by
    intro j; funext t; rw [hy]
  have hinv : ∀ j : ZMod p, ∀ (g : ThreeCoordinateGroup p), ∀ v ∈ Submodule.span ℂ {chi j},
      ρ g v ∈ Submodule.span ℂ {chi j} := by
    intro j
    have hline : ∀ (op : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)),
        op (chi j) ∈ Submodule.span ℂ {chi j} →
        ∀ v ∈ Submodule.span ℂ {chi j}, op v ∈ Submodule.span ℂ {chi j} := by
      intro op hop v hv
      have hle : Submodule.span ℂ {chi j} ≤ (Submodule.span ℂ {chi j}).comap op := by
        rw [Submodule.span_le]
        intro x hx'
        rw [Set.mem_singleton_iff] at hx'; subst hx'
        simpa using hop
      exact hle hv
    have hX : ρ (firstGenerator p) (chi j) ∈ Submodule.span ℂ {chi j} := by
      rw [hxeig]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hY : ρ (secondGenerator p) (chi j) ∈ Submodule.span ℂ {chi j} := by
      rw [hyeig]; exact Submodule.mem_span_singleton_self _
    let Sm : Submonoid (ThreeCoordinateGroup p) :=
      { carrier := {g | ∀ v ∈ Submodule.span ℂ {chi j}, ρ g v ∈ Submodule.span ℂ {chi j}}
        one_mem' := by intro v hv; rw [map_one]; simpa using hv
        mul_mem' := by intro a b ha hb v hv; rw [map_mul]; exact ha _ (hb v hv) }
    have hSle : Submonoid.closure ({firstGenerator p, secondGenerator p} : Set (ThreeCoordinateGroup p)) ≤ Sm :=
      Submonoid.closure_le.mpr (by
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact hline _ hX
        · exact hline _ hY)
    intro g v hv
    exact hSle (by rw [ThreeCoordinateGroup.closure_generators_eq_top]; exact Submonoid.mem_top g) v hv
  set v : Fin p → (ZMod p → ℂ) := fun i => chi ((i : ℕ) : ZMod p) with hv_def
  set μ : Fin p → ℂ := fun i => ζ ^ ((-((i : ℕ) : ZMod p)).val) with hμ_def
  have horder : orderOf ζ = p := hζ.eq_orderOf.symm
  have hpow_inj : ∀ s t : ZMod p, ζ ^ s.val = ζ ^ t.val → s = t := by
    intro s t hst
    apply ZMod.val_injective p
    have hs : s.val < orderOf ζ := by rw [horder]; exact ZMod.val_lt s
    have ht : t.val < orderOf ζ := by rw [horder]; exact ZMod.val_lt t
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr ht) hst
  have hμinj : Function.Injective μ := by
    intro i i' h
    have h2 : -(((i : ℕ) : ZMod p)) = -(((i' : ℕ) : ZMod p)) := hpow_inj _ _ h
    have h3 : (((i : ℕ) : ZMod p)) = (((i' : ℕ) : ZMod p)) := neg_injective h2
    apply Fin.ext
    have e1 : (((i : ℕ) : ZMod p)).val = (i : ℕ) := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt i.isLt
    have e2 : (((i' : ℕ) : ZMod p)).val = (i' : ℕ) := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt i'.isLt
    rw [← e1, ← e2, h3]
  have hli : LinearIndependent ℂ v := by
    apply Module.End.eigenvectors_linearIndependent' (ρ (firstGenerator p)) μ hμinj v
    intro i
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (hxeig _), chi_ne_zero _⟩
  have hv0 : ∀ i : Fin p, v i 0 = 1 := by
    intro i
    change ζ ^ (((i : ℕ) : ZMod p) * 0).val = 1
    rw [mul_zero, ZMod.val_zero, pow_zero]
  have hxeig' : ∀ i : Fin p, ρ (firstGenerator p) (v i) = μ i • v i :=
    fun i => hxeig ((i : ℕ) : ZMod p)
  have hρinj : ∀ (g : ThreeCoordinateGroup p), Function.Injective (ρ g) := by
    intro g
    have hlinv : Function.LeftInverse (ρ g⁻¹) (ρ g) := by
      intro w
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hlinv.injective
  have hscale : ∀ (i : Fin p) (g : ThreeCoordinateGroup p), ρ g (v i) = (ρ g (v i) 0) • v i := by
    intro i g
    have hmem : ρ g (v i) ∈ Submodule.span ℂ {v i} :=
      hinv ((i : ℕ) : ZMod p) g (v i) (Submodule.mem_span_singleton_self _)
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hval : ρ g (v i) 0 = a := by rw [← ha, Pi.smul_apply, smul_eq_mul, hv0 i, mul_one]
    rw [hval]; exact ha.symm
  have hc_ne : ∀ (i : Fin p) (g : ThreeCoordinateGroup p), ρ g (v i) 0 ≠ 0 := by
    intro i g h0
    have hz : ρ g (v i) = 0 := by rw [hscale i g, h0, zero_smul]
    exact chi_ne_zero ((i : ℕ) : ZMod p) (hρinj g (hz.trans (map_zero (ρ g)).symm))
  have hmul : ∀ (i : Fin p) (g h : ThreeCoordinateGroup p),
      ρ (g * h) (v i) 0 = ρ g (v i) 0 * ρ h (v i) 0 := by
    intro i g h
    have hgh : ρ (g * h) (v i) = ρ h (v i) 0 • ρ g (v i) := by
      rw [map_mul, Module.End.mul_apply]
      nth_rewrite 1 [hscale i h]
      rw [map_smul]
    rw [hgh, Pi.smul_apply, smul_eq_mul]; ring
  let χ : Fin p → (ThreeCoordinateGroup p →* ℂˣ) := fun i =>
    { toFun := fun g => Units.mk0 (ρ g (v i) 0) (hc_ne i g)
      map_one' := by
        apply Units.ext
        change ρ (1 : ThreeCoordinateGroup p) (v i) 0 = 1
        rw [map_one, Module.End.one_apply]; exact hv0 i
      map_mul' := fun g h => by
        apply Units.ext
        change ρ (g * h) (v i) 0 = ρ g (v i) 0 * ρ h (v i) 0
        exact hmul i g h }
  have hχx : ∀ i : Fin p, (χ i (firstGenerator p) : ℂ) = μ i := by
    intro i
    change ρ (firstGenerator p) (v i) 0 = μ i
    rw [hxeig' i, Pi.smul_apply, smul_eq_mul, hv0 i, mul_one]
  refine ⟨fun i => Submodule.span ℂ {v i}, ?_, ?_, ?_, χ, ?_, ?_⟩
  · intro i g w hw
    exact hinv ((i : ℕ) : ZMod p) g w hw
  · intro i
    exact finrank_span_singleton (chi_ne_zero _)
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hli.iSupIndep_span_singleton
    · have hcard : Fintype.card (Fin p) = Module.finrank ℂ (ZMod p → ℂ) := by
        rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, ZMod.card]
      have hspan_top := hli.span_eq_top_of_card_eq_finrank hcard
      rw [← hspan_top, ← Set.iUnion_singleton_eq_range, Submodule.span_iUnion]
  ·
    intro i i' hii
    apply hμinj
    have key : (χ i (firstGenerator p) : ℂ) = (χ i' (firstGenerator p) : ℂ) := by rw [hii]
    rwa [hχx i, hχx i'] at key
  ·
    intro i g w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    have hg : ρ g (v i) = (χ i g : ℂ) • v i := hscale i g
    rw [map_smul, hg, smul_comm]

/-- An auxiliary assertion with unavailable formal rendering. -/
theorem auxiliaryRepresentationAssertion [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    shiftScaleRepresentation z hz (⟨0, 0, 1⟩ : ThreeCoordinateGroup p) = z ^ ((-1 : ZMod p).val) • LinearMap.id := by
  refine LinearMap.ext fun f => funext fun t => ?_
  rw [shiftScaleRepresentation_apply, shiftScaleAction_apply]
  simp only [zero_mul, zero_sub, sub_zero, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    Pi.smul_apply, smul_eq_mul]

/-- Computes the dimension of the displayed shift-scale representation. -/
theorem shiftScaleRepresentation_finrank [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    Module.finrank ℂ (FDRep.of (shiftScaleRepresentation z hz)) = p := by
  change Module.finrank ℂ (ZMod p → ℂ) = p
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card]

/-- An auxiliary assertion with unavailable formal rendering. -/
theorem auxiliaryCharacterAssertion [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    (FDRep.of (shiftScaleRepresentation z hz)).character (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
      = z ^ ((-1 : ZMod p).val) * (p : ℂ) := by
  have hc : (FDRep.of (shiftScaleRepresentation z hz)).character (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
      = LinearMap.trace ℂ _ (shiftScaleRepresentation z hz (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)) := rfl
  rw [hc, auxiliaryRepresentationAssertion z hz, map_smul, LinearMap.trace_id, smul_eq_mul, shiftScaleRepresentation_finrank z hz]

/-- An auxiliary assertion with unavailable formal rendering. -/
theorem auxiliaryRootAssertion [NeZero p] {w₁ w₂ : ℂ} (h₁ : w₁ ^ p = 1) (h₂ : w₂ ^ p = 1)
    (h : w₁ ^ ((-1 : ZMod p).val) = w₂ ^ ((-1 : ZMod p).val)) : w₁ = w₂ := by
  have hval : (-1 : ZMod p).val + 1 = p := by
    have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_pred hpos, ZMod.natCast_self]; ring
    have hv : (-1 : ZMod p).val = p - 1 := by
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  have e₁ : w₁ ^ ((-1 : ZMod p).val) * w₁ = 1 := by rw [← pow_succ, hval, h₁]
  have e₂ : w₂ ^ ((-1 : ZMod p).val) * w₂ = 1 := by rw [← pow_succ, hval, h₂]
  rw [h] at e₁
  have hne : w₂ ^ ((-1 : ZMod p).val) ≠ 0 := by
    intro hz; rw [hz, zero_mul] at e₂; exact one_ne_zero e₂.symm
  exact mul_left_cancel₀ hne (e₁.trans e₂.symm)

/-- An injective map between finite index types is surjective when the displayed positive sums agree. -/
theorem surjective_of_injective_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → ℕ) (hf : ∀ j, 0 < f j) (c : ι → Fin n) (hcinj : Function.Injective c)
    (hsum : ∑ i, f (c i) = ∑ j, f j) : Function.Surjective c := by
  classical
  have himg : ∑ j ∈ Finset.image c Finset.univ, f j = ∑ i, f (c i) :=
    Finset.sum_image (fun a _ b _ hab => hcinj hab)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ (Finset.image c Finset.univ))
  rw [himg, hsum] at hsplit
  have hzero : ∑ j ∈ Finset.univ \ Finset.image c Finset.univ, f j = 0 := by omega
  intro j
  have hjmem : j ∈ Finset.image c Finset.univ := by
    by_contra hj
    exact absurd ((Finset.sum_eq_zero_iff.mp hzero) j
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)) (hf j).ne'
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjmem
  exact ⟨i, hi⟩

/-- Every displayed simple representation is isomorphic to one of the two stated forms. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem simple_representation_iso_character_or_shiftScale [Fact p.Prime]
    (U : FDRep ℂ (ThreeCoordinateGroup p)) [hUsimple : Simple U] :
    (∃ χ : ThreeCoordinateGroup p →* ℂˣ,
        Nonempty (U ≅ FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))) ∨
    (∃ z : ℂ, ∃ (hz : z ^ p = 1), z ≠ 1 ∧
        Nonempty (U ≅ FDRep.of (shiftScaleRepresentation z hz))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  haveI hNe : NeZero (Nat.card (ThreeCoordinateGroup p) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, ThreeCoordinateGroup.card_eq_cube]
    push_cast
    exact pow_ne_zero 3 hpℂ
  obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ (ThreeCoordinateGroup p)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let zof : {k : ZMod p // k ≠ 0} → ℂ := fun k => ζ ^ (k.1).val
  have hzof_p : ∀ k, (zof k) ^ p = 1 := fun k => by
    change (ζ ^ (k.1).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hzof_ne1 : ∀ k, zof k ≠ 1 := by
    intro k h
    have h' : ζ ^ (k.1).val = 1 := h
    have hdvd : (p : ℕ) ∣ (k.1).val := (hζ.pow_eq_one_iff_dvd _).mp h'
    have hz0 : (k.1).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k.1)
    exact k.2 (ZMod.val_injective p (by rw [hz0, ZMod.val_zero]))
  haveI : Finite (ThreeCoordinateGroup p →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [character_card_eq_square]; exact pow_ne_zero 2 (by omega))
  haveI : Fintype (ThreeCoordinateGroup p →* ℂˣ) := Fintype.ofFinite _
  have hcardChar : Fintype.card (ThreeCoordinateGroup p →* ℂˣ) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact character_card_eq_square
  have hcardJ : Fintype.card {k : ZMod p // k ≠ 0} = p - 1 := by
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl (fun k : ZMod p => k = 0), Fintype.card_subtype_eq, ZMod.card]
  let E : (ThreeCoordinateGroup p →* ℂˣ) ⊕ {k : ZMod p // k ≠ 0} → FDRep ℂ (ThreeCoordinateGroup p) :=
    Sum.elim (fun χ => FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))
      (fun k => FDRep.of (shiftScaleRepresentation (zof k) (hzof_p k)))
  have hEfinL : ∀ χ : ThreeCoordinateGroup p →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 := by
    intro χ
    change Module.finrank ℂ ℂ = 1
    exact Module.finrank_self ℂ
  have hEfinR : ∀ k : {k : ZMod p // k ≠ 0}, Module.finrank ℂ (E (Sum.inr k)) = p := by
    intro k
    exact shiftScaleRepresentation_finrank (zof k) (hzof_p k)
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | k)
    · exact RepresentationTheory.PermutationDegreeThree.simple_representationOfUnitCharacter χ
    · haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p))
          (shiftScaleRepresentation (zof k) (hzof_p k)).asModule :=
        (shiftScaleRepresentation_simple_iff (zof k) (hzof_p k) (shiftScaleRepresentation (zof k) (hzof_p k))
          (shiftScaleRepresentation_firstGenerator_apply (zof k) (hzof_p k)) (shiftScaleRepresentation_secondGenerator_apply (zof k) (hzof_p k))).mpr (hzof_ne1 k)
      exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (shiftScaleRepresentation (zof k) (hzof_p k))
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | k) (χ' | k') ⟨α⟩
    ·
      have hχ : χ = χ' := by
        ext g
        have hg := congrFun (FDRep.char_iso α) g
        rw [show E (Sum.inl χ) = FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) from rfl,
            show E (Sum.inl χ') = FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ') from rfl,
            RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter,
            RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter] at hg
        exact hg
      rw [hχ]
    ·
      exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinL χ, hEfinR k'] at hfr
      omega
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinR k, hEfinL χ'] at hfr
      omega
    ·
      have hg := congrFun (FDRep.char_iso α) (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
      rw [show E (Sum.inr k) = FDRep.of (shiftScaleRepresentation (zof k) (hzof_p k)) from rfl,
          show E (Sum.inr k') = FDRep.of (shiftScaleRepresentation (zof k') (hzof_p k')) from rfl,
          auxiliaryCharacterAssertion, auxiliaryCharacterAssertion] at hg
      have hpow := mul_right_cancel₀ hpℂ hg
      have hzz : zof k = zof k' := auxiliaryRootAssertion (hzof_p k) (hzof_p k') hpow
      have hzz' : ζ ^ (k.1).val = ζ ^ (k'.1).val := hzz
      have hvv : (k.1).val = (k'.1).val :=
        hζ.pow_inj (ZMod.val_lt k.1) (ZMod.val_lt k'.1) hzz'
      have : k.1 = k'.1 := ZMod.val_injective p hvv
      exact congrArg Sum.inr (Subtype.ext this)
  choose c hc using fun i => hVsurj (E i) (hEsimple i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
    exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
  have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
    LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
  have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = p ^ 3 := by
    rw [Fintype.sum_sum_type]
    have hL : ∑ χ : ThreeCoordinateGroup p →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = p ^ 2 := by
      have hone : ∀ χ : ThreeCoordinateGroup p →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 := by
        intro χ; rw [hEfinL χ, one_pow]
      rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
        hcardChar, smul_eq_mul, mul_one]
    have hR : ∑ k : {k : ZMod p // k ≠ 0}, (Module.finrank ℂ (E (Sum.inr k))) ^ 2
        = (p - 1) * p ^ 2 := by
      have hpk : ∀ k : {k : ZMod p // k ≠ 0}, (Module.finrank ℂ (E (Sum.inr k))) ^ 2 = p ^ 2 := by
        intro k; rw [hEfinR k]
      rw [Finset.sum_congr rfl (fun k _ => hpk k), Finset.sum_const, Finset.card_univ, hcardJ,
        smul_eq_mul]
    rw [hL, hR]
    have hp1le : 1 ≤ p := hp1.le
    have hstep : (p - 1) * p ^ 2 + p ^ 2 = p * p ^ 2 := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1le]
    rw [add_comm, hstep]; ring
  have hVsum3 : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = p ^ 3 := by
    rw [hVsum, ThreeCoordinateGroup.card_eq_cube]
  have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2 = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
    rw [hVsum3, ← hEsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
  have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
    intro j
    haveI : Simple (V j) := hVsimple j
    haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (Representation.asModule (V j).ρ) :=
      RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep (V j)
    haveI : Nontrivial (Representation.asModule (V j).ρ) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (Representation.asModule (V j).ρ)
    haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
    have hpos : 0 < Module.finrank ℂ (V j) := Module.finrank_pos
    exact pow_pos hpos 2
  have hcsurj : Function.Surjective c :=
    surjective_of_injective_sum_eq _ hVpos c hc_inj hmatch
  obtain ⟨j, hjU⟩ := hVsurj U hUsimple
  obtain ⟨i, hci⟩ := hcsurj j
  have hUEi : Nonempty (U ≅ E i) :=
    ⟨hjU.some ≪≫ eqToIso (congrArg V hci).symm ≪≫ (hc i).some.symm⟩
  rcases i with χ | k
  · exact Or.inl ⟨χ, hUEi⟩
  · exact Or.inr ⟨zof k, hzof_p k, hzof_ne1 k, hUEi⟩

/-- Two displayed character representations are isomorphic exactly when their characters agree. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem character_iso_iff (χ χ' : ThreeCoordinateGroup p →* ℂˣ) :
    Nonempty (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ≅
        FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ')) ↔ χ = χ' := by
  constructor
  · rintro ⟨α⟩
    ext g
    have hg := congrFun (FDRep.char_iso α) g
    rw [RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter, RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter] at hg
    exact hg
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- Two displayed shift-scale representations are isomorphic exactly when their parameters agree. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem shiftScaleRepresentation_iso_iff [Fact p.Prime] {z z' : ℂ} (hz : z ^ p = 1) (hz' : z' ^ p = 1) :
    Nonempty (FDRep.of (shiftScaleRepresentation z hz) ≅ FDRep.of (shiftScaleRepresentation z' hz')) ↔ z = z' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  constructor
  · rintro ⟨α⟩
    have hg := congrFun (FDRep.char_iso α) (⟨0, 0, 1⟩ : ThreeCoordinateGroup p)
    rw [auxiliaryCharacterAssertion, auxiliaryCharacterAssertion] at hg
    exact auxiliaryRootAssertion hz hz' (mul_right_cancel₀ hpℂ hg)
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- States nonisomorphism between the displayed character representation and an auxiliary representation. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem character_representation_not_iso_auxiliary [Fact p.Prime] (χ : ThreeCoordinateGroup p →* ℂˣ) {z : ℂ} (hz : z ^ p = 1) :
    ¬ Nonempty (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ≅ FDRep.of (shiftScaleRepresentation z hz)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rintro ⟨α⟩
  have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
  rw [show Module.finrank ℂ (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ)) = 1 from
      Module.finrank_self ℂ, shiftScaleRepresentation_finrank z hz] at hfr
  omega

/-- A simple representation has dimension one or the index under the stated hypotheses. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem simple_representation_finrank_eq_one_or_index [Fact p.Prime]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (ThreeCoordinateGroup p) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = p := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI M := Representation.asModule σ
  haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) M := hσ
  haveI : Module.Finite ℂ M := Module.Finite.equiv (Representation.asModuleEquiv σ).symm
  haveI : Module.Free ℂ M := Module.Free.of_divisionRing ℂ M
  set dM := Module.finrank ℂ M with hdM
  let eM : M ≃ₗ[ℂ] (Fin dM → ℂ) := (Module.finBasis ℂ M).equivFun
  letI modN : Module (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.moduleTransportAlongLinearEquiv (R := MonoidAlgebra ℂ (ThreeCoordinateGroup p)) eM
  haveI towN : IsScalarTower ℂ (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.isScalarTower_moduleTransportAlongLinearEquiv eM
  let eR : M ≃ₗ[MonoidAlgebra ℂ (ThreeCoordinateGroup p)] (Fin dM → ℂ) :=
    RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.linearEquiv_transportModule eM
  haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (Fin dM → ℂ) :=
    IsSimpleModule.congr eR.symm
  haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p))
      (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (Fin dM → ℂ)).asModule :=
    IsSimpleModule.congr (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.asModuleRepresentationOfMonoidAlgebraModule (Fin dM → ℂ))
  let U : FDRep ℂ (ThreeCoordinateGroup p) := FDRep.of (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (Fin dM → ℂ))
  haveI hUsimple : Simple U :=
    RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.representationOfMonoidAlgebraModule (Fin dM → ℂ))
  have hWU : Module.finrank ℂ W = Module.finrank ℂ U := by
    have h1 : Module.finrank ℂ U = dM := by
      change Module.finrank ℂ (Fin dM → ℂ) = dM
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have h2 : dM = Module.finrank ℂ W := by
      rw [hdM]; exact (Representation.asModuleEquiv σ).finrank_eq
    rw [h1, h2]
  rw [hWU]
  rcases simple_representation_iso_character_or_shiftScale U with ⟨χ, hχ⟩ | ⟨z, hz, _, hziso⟩
  · left
    rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hχ.some)]
    change Module.finrank ℂ ℂ = 1
    exact Module.finrank_self ℂ
  · right
    rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hziso.some)]
    exact shiftScaleRepresentation_finrank z hz

/-- An auxiliary family of types indexed by a natural number. -/
abbrev AuxiliaryTypeFamily (p : ℕ) : Type :=
  (ThreeCoordinateGroup p →* ℂˣ) ⊕ {z : ℂ // z ^ p = 1 ∧ z ≠ 1}

/-- Computes the number of nonidentity roots satisfying the displayed power equation. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem nontrivialRoots_card [Fact p.Prime] :
    Nat.card {z : ℂ // z ^ p = 1 ∧ z ≠ 1} = p - 1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  set S : Finset ℂ := (Polynomial.nthRootsFinset p (1 : ℂ)).erase 1 with hS
  have hmem : ∀ z : ℂ, (z ^ p = 1 ∧ z ≠ 1) ↔ z ∈ S := by
    intro z
    rw [hS, Finset.mem_erase, Polynomial.mem_nthRootsFinset hp0]
    tauto
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_erase_of_mem (Polynomial.one_mem_nthRootsFinset hp0),
      hζ.card_nthRootsFinset]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_finsetCard, hcard]

/-- The subtype of nonidentity roots satisfying the displayed power equation is finite. -/
instance finite_nontrivialRoots [Fact p.Prime] : Finite {z : ℂ // z ^ p = 1 ∧ z ≠ 1} := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  refine Finite.of_injective (β := (Polynomial.nthRootsFinset p (1 : ℂ)))
    (fun z => ⟨z.1, (Polynomial.mem_nthRootsFinset hp0 1).mpr z.2.1⟩) ?_
  intro a b h
  exact Subtype.ext (congrArg (fun s : (Polynomial.nthRootsFinset p (1 : ℂ)) => (s : ℂ)) h)

/-- Asserts a nonempty equivalence between the displayed character type and an auxiliary family. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem characterType_nonempty_equiv_auxiliary [Fact p.Prime] :
    Nonempty (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ (ThreeCoordinateGroup p) ≃ AuxiliaryTypeFamily p) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let 𝒮 : ObjectProperty (FDRep ℂ (ThreeCoordinateGroup p)) := fun V => Simple V
  let E : AuxiliaryTypeFamily p → FDRep ℂ (ThreeCoordinateGroup p) :=
    Sum.elim (fun χ => FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))
      (fun z => FDRep.of (shiftScaleRepresentation z.1 z.2.1))
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | ⟨z, hz, hz1⟩)
    · exact RepresentationTheory.PermutationDegreeThree.simple_representationOfUnitCharacter χ
    · haveI : IsSimpleModule (MonoidAlgebra ℂ (ThreeCoordinateGroup p)) (shiftScaleRepresentation z hz).asModule :=
        (shiftScaleRepresentation_simple_iff z hz (shiftScaleRepresentation z hz) (shiftScaleRepresentation_firstGenerator_apply z hz) (shiftScaleRepresentation_secondGenerator_apply z hz)).mpr hz1
      exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (shiftScaleRepresentation z hz)
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | ⟨z, hz, hz1⟩) (χ' | ⟨z', hz', hz1'⟩) hiso
    · exact congrArg Sum.inl ((character_iso_iff χ χ').mp hiso)
    · exact absurd hiso (character_representation_not_iso_auxiliary χ hz')
    · exact absurd (hiso.map Iso.symm) (character_representation_not_iso_auxiliary χ' hz)
    · exact congrArg Sum.inr (Subtype.ext ((shiftScaleRepresentation_iso_iff hz hz').mp hiso))
  let P : AuxiliaryTypeFamily p → 𝒮.FullSubcategory := fun i => ⟨E i, hEsimple i⟩
  let f : AuxiliaryTypeFamily p → RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ (ThreeCoordinateGroup p) :=
    fun i => Quotient.mk (isIsomorphicSetoid _) (P i)
  have hf : Function.Bijective f := by
    constructor
    ·
      intro i j hij
      obtain ⟨iso⟩ := Quotient.exact hij
      exact hEinj i j ⟨𝒮.ι.mapIso iso⟩
    ·
      intro c
      induction c using Quotient.inductionOn with
      | h Q =>
        haveI : Simple Q.obj := Q.property
        rcases simple_representation_iso_character_or_shiftScale Q.obj with ⟨χ, ⟨α⟩⟩ | ⟨z, hz, hz1, ⟨α⟩⟩
        · exact ⟨Sum.inl χ, Quotient.sound ⟨𝒮.fullyFaithfulι.preimageIso α.symm⟩⟩
        · exact ⟨Sum.inr ⟨z, hz, hz1⟩, Quotient.sound ⟨𝒮.fullyFaithfulι.preimageIso α.symm⟩⟩
  exact ⟨(Equiv.ofBijective f hf).symm⟩

/-- Computes the cardinality of the displayed character type. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem characterType_card [Fact p.Prime] :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ (ThreeCoordinateGroup p)) = p ^ 2 + (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (ThreeCoordinateGroup p →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by
      rw [character_card_eq_square]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ := characterType_nonempty_equiv_auxiliary (p := p)
  rw [Nat.card_congr e]
  change Nat.card ((ThreeCoordinateGroup p →* ℂˣ) ⊕ {z : ℂ // z ^ p = 1 ∧ z ≠ 1}) = p ^ 2 + (p - 1)
  rw [Nat.card_sum, character_card_eq_square, nontrivialRoots_card]

/-- Relates the carrier cardinality to the displayed character-count expression. -/
@[source_ref "Chapter4/Problem4.12.2" (role := supporting)]
theorem card_eq_character_count [Fact p.Prime] :
    p ^ 2 * 1 ^ 2 + (p - 1) * p ^ 2 = Fintype.card (ThreeCoordinateGroup p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [ThreeCoordinateGroup.card_eq_cube, one_pow, mul_one, add_comm]
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1]; ring

end RepresentationTheory.ThreeCoordinateGroupRepresentations
