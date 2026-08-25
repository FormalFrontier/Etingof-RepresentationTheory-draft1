/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.ModuleCat.Auxiliary
import RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions
import RepresentationTheory.Alignment.Attribute

/-! Characteristic-two permutation representation constructions. -/

open CategoryTheory
open scoped MonoidAlgebra
open RepresentationTheory.ModuleCat.Auxiliary
open RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions

namespace RepresentationTheory.PermutationRepresentation.CharTwo


/-- The ambient type of acting permutations used in the constructions below. -/
abbrev ActingPermutationType : Type := Equiv.Perm (Fin 3)

variable (k : Type) [Field k] [CharP k 2]




/-- A representation of the acting permutation type on the base field. -/
def oneDimensionalRepresentation : Representation k ActingPermutationType k := Representation.trivial k ActingPermutationType k


/-- The representation on functions with three coordinates. -/
def coordinatePermutationRepresentation : Representation k ActingPermutationType (Fin 3 → k) where
  toFun σ := LinearMap.funLeft k k (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

omit [CharP k 2] in
/-- Acting on a coordinate function evaluates it at the inverse image of the coordinate. -/
@[simp] lemma coordinatePermutationRepresentation_apply (σ : ActingPermutationType) (f : Fin 3 → k) (i : Fin 3) :
    coordinatePermutationRepresentation k σ f i = f (σ⁻¹ i) := rfl


/-- The linear map from three-coordinate functions to the sum of their coordinates. -/
def coordinateSum : (Fin 3 → k) →ₗ[k] k := ∑ i, LinearMap.proj i

omit [CharP k 2] in
/-- The coordinate-sum map evaluates to the sum over all three coordinates. -/
@[simp] lemma coordinateSum_apply (f : Fin 3 → k) : coordinateSum k f = ∑ i, f i := by
  simp [coordinateSum, Finset.sum_apply]


/-- A distinguished subrepresentation of the three-coordinate permutation representation. -/
def distinguishedSubrepresentation : Subrepresentation (coordinatePermutationRepresentation k) where
  toSubmodule := LinearMap.ker (coordinateSum k)
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, coordinateSum_apply] at hf ⊢
    calc ∑ i, coordinatePermutationRepresentation k σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [coordinatePermutationRepresentation_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf


/-- The representation obtained on the carrier of the distinguished subrepresentation. -/
def restrictedRepresentation : Representation k ActingPermutationType (distinguishedSubrepresentation k).toSubmodule := (distinguishedSubrepresentation k).toRepresentation




/-- A module object over the monoid algebra associated with the one-dimensional representation. -/
noncomputable def oneDimensionalModuleObject : ModuleCat (MonoidAlgebra k ActingPermutationType) :=
  ModuleCat.of (MonoidAlgebra k ActingPermutationType) (oneDimensionalRepresentation k).asModule


/-- A distinguished module object over the monoid algebra. -/
noncomputable def distinguishedModuleObject : ModuleCat (MonoidAlgebra k ActingPermutationType) :=
  ModuleCat.of (MonoidAlgebra k ActingPermutationType) (restrictedRepresentation k).asModule




/-- An auxiliary type depending on a field. -/
abbrev AuxiliaryAlgebra : Type := Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}



omit [CharP k 2] in

/-- The module underlying the one-dimensional representation is simple. -/
theorem oneDimensionalRepresentation_isSimpleModule : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (oneDimensionalRepresentation k).asModule :=
  { toIsSimpleOrder := is_simple_module_of_finrank_eq_one (K := k)
      (by rw [(oneDimensionalRepresentation k).asModuleEquiv.finrank_eq, Module.finrank_self]) }

omit [CharP k 2] in
open Module in

private lemma stdRepr_val (g : ActingPermutationType) (x : ↥(distinguishedSubrepresentation k).toSubmodule) :
    ((restrictedRepresentation k g x : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) = coordinatePermutationRepresentation k g (x : Fin 3 → k) :=
  rfl

open Module in

private lemma finrank_stdSub : finrank k ↥(distinguishedSubrepresentation k).toSubmodule = 2 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hpi : finrank k (Fin 3 → k) = 3 := by
    simp
  have hrange : finrank k ↥(LinearMap.range (coordinateSum k)) = 1 := by
    have hr : LinearMap.range (coordinateSum k) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨Pi.single 0 c, by simp [coordinateSum_apply, Finset.sum_pi_single']⟩
    rw [hr, finrank_top, Module.finrank_self]
  have hsum := LinearMap.finrank_range_add_finrank_ker (coordinateSum k)
  rw [hrange, hpi] at hsum
  change finrank k ↥(LinearMap.ker (coordinateSum k)) = 2
  omega


/-- In characteristic two, the module underlying the restricted representation is simple. -/
theorem restrictedRepresentation_isSimpleModule : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (restrictedRepresentation k).asModule := by
  classical
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  set V := ↥(distinguishedSubrepresentation k).toSubmodule with hV
  have hdimV : Module.finrank k V = 2 := finrank_stdSub k
  have hnt : Nontrivial V := by
    refine ⟨⟨![1, 1, 0], ?_⟩, 0, ?_⟩
    · have hmem : ![1, 1, 0] ∈ LinearMap.ker (coordinateSum k) := by
        rw [LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, add_zero]
        rw [one_add_one_eq_two, h2]
      exact hmem
    · intro h
      have := congrArg (fun x : V => (x : Fin 3 → k) 0) h
      simp only [Matrix.cons_val_zero, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      exact one_ne_zero this
  haveI : Nontrivial V := hnt
  suffices hSO : IsSimpleOrder (restrictedRepresentation k).invtSubmodule by
    exact { toIsSimpleOrder := (restrictedRepresentation k).mapSubmodule.isSimpleOrder_iff.mp hSO }
  refine ⟨fun a => ?_⟩
  have hinv : ∀ (g : ActingPermutationType) (x : V), x ∈ (a : Submodule k V) → restrictedRepresentation k g x ∈ (a : Submodule k V) :=
    fun g => (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (restrictedRepresentation k g)).mp
      ((restrictedRepresentation k).mem_invtSubmodule.mp a.2 g)
  rcases eq_or_ne (a : Submodule k V) ⊥ with hbot | hbot
  · left; exact Subtype.ext (hbot.trans (Representation.invtSubmodule.coe_bot _).symm)
  obtain ⟨w, hw_mem, hw_ne⟩ := (Submodule.ne_bot_iff _).mp hbot
  right
  refine Subtype.ext ?_
  rw [Representation.invtSubmodule.coe_top]
  have topOfIndep : ∀ u : V, u ∈ (a : Submodule k V) → u ∉ Submodule.span k {w} →
      (a : Submodule k V) = ⊤ := by
    intro u hu hunotin
    by_contra htop
    have hlt : (a : Submodule k V) < ⊤ := lt_of_le_of_ne le_top htop
    have hfa : Module.finrank k ↥(a : Submodule k V) < 2 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rwa [finrank_top, hdimV] at this
    have hwle : Submodule.span k {w} ≤ (a : Submodule k V) :=
      (Submodule.span_singleton_le_iff_mem w _).mpr hw_mem
    have h1 : Module.finrank k ↥(Submodule.span k {w}) = 1 := finrank_span_singleton hw_ne
    have hmono := Submodule.finrank_mono hwle
    rw [h1] at hmono
    have hfa1 : Module.finrank k ↥(a : Submodule k V) = 1 := by omega
    have hspaneq : Submodule.span k {w} = (a : Submodule k V) :=
      Submodule.eq_of_le_of_finrank_eq hwle (by rw [h1, hfa1])
    rw [← hspaneq] at hu
    exact hunotin hu
  have key : ∀ (s : ActingPermutationType), s * s = 1 → restrictedRepresentation k s w ∈ Submodule.span k {w} →
      restrictedRepresentation k s w = w := by
    intro s hs hmem
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    have hss : restrictedRepresentation k s (restrictedRepresentation k s w) = w := by
      have hmm : restrictedRepresentation k (s * s) = restrictedRepresentation k s * restrictedRepresentation k s := map_mul _ _ _
      rw [hs, map_one] at hmm
      have := LinearMap.congr_fun hmm.symm w
      simpa [Module.End.mul_apply] using this
    have e1 : restrictedRepresentation k s (restrictedRepresentation k s w) = (μ * μ) • w := by
      conv_lhs => rw [← hμ]
      rw [map_smul, ← hμ, smul_smul]
    rw [hss] at e1
    have hmuw : (μ * μ) • w = w := e1.symm
    have hmm : μ * μ = 1 := by
      have hz : ((μ * μ) - 1) • w = 0 :=
        (sub_smul (μ * μ) 1 w).trans ((congrArg₂ (· - ·) hmuw (one_smul k w)).trans
          (sub_self w))
      rcases smul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw_ne
    have hsq : (μ - 1) * (μ - 1) = 0 := by linear_combination hmm + (1 - μ) * h2
    have hμ1 : μ = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
    rw [← hμ, hμ1, one_smul]
  by_cases hτ : restrictedRepresentation k (Equiv.swap (0 : Fin 3) 1) w ∈ Submodule.span k {w}
  · by_cases hτ' : restrictedRepresentation k (Equiv.swap (1 : Fin 3) 2) w ∈ Submodule.span k {w}
    · -- both fix `w` ⟹ `w` is constant ⟹ `w = 0`, contradiction
      exfalso
      have hfτ : restrictedRepresentation k (Equiv.swap (0 : Fin 3) 1) w = w := key _ (by decide) hτ
      have hfτ' : restrictedRepresentation k (Equiv.swap (1 : Fin 3) 2) w = w := key _ (by decide) hτ'
      have e0 : coordinatePermutationRepresentation k (Equiv.swap (0 : Fin 3) 1) (w : Fin 3 → k) = (w : Fin 3 → k) := by
        rw [← stdRepr_val]; exact congrArg (fun x : V => (x : Fin 3 → k)) hfτ
      have e1' : coordinatePermutationRepresentation k (Equiv.swap (1 : Fin 3) 2) (w : Fin 3 → k) = (w : Fin 3 → k) := by
        rw [← stdRepr_val]; exact congrArg (fun x : V => (x : Fin 3 → k)) hfτ'
      have h01 : (w : Fin 3 → k) 1 = (w : Fin 3 → k) 0 := by
        have := congr_fun e0 0
        rwa [coordinatePermutationRepresentation_apply, show (Equiv.swap (0 : Fin 3) 1)⁻¹ 0 = 1 from by decide] at this
      have h12 : (w : Fin 3 → k) 2 = (w : Fin 3 → k) 1 := by
        have := congr_fun e1' 1
        rwa [coordinatePermutationRepresentation_apply, show (Equiv.swap (1 : Fin 3) 2)⁻¹ 1 = 2 from by decide] at this
      have hz : coordinateSum k (w : Fin 3 → k) = 0 := w.2
      rw [coordinateSum_apply, Fin.sum_univ_three, h12, h01] at hz
      have hw0 : (w : Fin 3 → k) 0 = 0 := by
        have hsum3 : (w : Fin 3 → k) 0 + (w : Fin 3 → k) 0 + (w : Fin 3 → k) 0 = 0 := hz
        linear_combination hsum3 - (w : Fin 3 → k) 0 * h2
      have hw1 : (w : Fin 3 → k) 1 = 0 := h01.trans hw0
      have hw2 : (w : Fin 3 → k) 2 = 0 := h12.trans hw1
      apply hw_ne
      refine Subtype.ext ?_
      rw [ZeroMemClass.coe_zero]
      funext i
      simp only [Pi.zero_apply]
      fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    · exact topOfIndep _ (hinv _ w hw_mem) hτ'
  · exact topOfIndep _ (hinv _ w hw_mem) hτ





/-- A distinguished element of the acting permutation type. -/
def distinguishedPermutation : ActingPermutationType := finRotate 3


/-- A distinguished element of the monoid algebra. -/
noncomputable def distinguishedAlgebraElement : MonoidAlgebra k ActingPermutationType :=
  MonoidAlgebra.single distinguishedPermutation 1 + MonoidAlgebra.single (distinguishedPermutation ^ 2) 1


/-- In characteristic two, the distinguished algebra element is idempotent. -/
lemma isIdempotentElem_distinguishedAlgebraElement : IsIdempotentElem (distinguishedAlgebraElement k) := by
  have p1 : (distinguishedPermutation * distinguishedPermutation : ActingPermutationType) = distinguishedPermutation ^ 2 := by rw [← sq]
  have p2 : (distinguishedPermutation * distinguishedPermutation ^ 2 : ActingPermutationType) = 1 := by decide
  have p3 : (distinguishedPermutation ^ 2 * distinguishedPermutation : ActingPermutationType) = 1 := by decide
  have p4 : (distinguishedPermutation ^ 2 * distinguishedPermutation ^ 2 : ActingPermutationType) = distinguishedPermutation := by decide
  have h0 : MonoidAlgebra.single (1 : ActingPermutationType) (1 : k) + MonoidAlgebra.single (1 : ActingPermutationType) 1 = 0 := by
    rw [← MonoidAlgebra.single_add, CharTwo.add_self_eq_zero, MonoidAlgebra.single_zero]
  change distinguishedAlgebraElement k * distinguishedAlgebraElement k = distinguishedAlgebraElement k
  have expand : distinguishedAlgebraElement k * distinguishedAlgebraElement k =
      MonoidAlgebra.single (distinguishedPermutation * distinguishedPermutation) (1 : k) + MonoidAlgebra.single (distinguishedPermutation * distinguishedPermutation ^ 2) 1
        + (MonoidAlgebra.single (distinguishedPermutation ^ 2 * distinguishedPermutation) 1
          + MonoidAlgebra.single (distinguishedPermutation ^ 2 * distinguishedPermutation ^ 2) 1) := by
    rw [distinguishedAlgebraElement, add_mul, mul_add, mul_add, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single]
    simp only [mul_one]
  rw [expand, p1, p2, p3, p4, distinguishedAlgebraElement]
  calc MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) + MonoidAlgebra.single 1 1
          + (MonoidAlgebra.single 1 1 + MonoidAlgebra.single distinguishedPermutation 1)
        = MonoidAlgebra.single distinguishedPermutation 1 + MonoidAlgebra.single (distinguishedPermutation ^ 2) 1
          + (MonoidAlgebra.single (1 : ActingPermutationType) 1 + MonoidAlgebra.single 1 1) := by abel
    _ = MonoidAlgebra.single distinguishedPermutation 1 + MonoidAlgebra.single (distinguishedPermutation ^ 2) 1 + 0 := by rw [h0]
    _ = MonoidAlgebra.single distinguishedPermutation 1 + MonoidAlgebra.single (distinguishedPermutation ^ 2) 1 := by rw [add_zero]

omit [CharP k 2] in

/-- The distinguished algebra element commutes with every single basis element. -/
lemma distinguishedAlgebraElement_mul_single_comm (g : ActingPermutationType) :
    distinguishedAlgebraElement k * MonoidAlgebra.single g 1 = MonoidAlgebra.single g 1 * distinguishedAlgebraElement k := by
  have hcomm : ∀ g : ActingPermutationType,
      (distinguishedPermutation * g = g * distinguishedPermutation ∧ distinguishedPermutation ^ 2 * g = g * distinguishedPermutation ^ 2) ∨
      (distinguishedPermutation * g = g * distinguishedPermutation ^ 2 ∧ distinguishedPermutation ^ 2 * g = g * distinguishedPermutation) := by decide
  rw [distinguishedAlgebraElement, add_mul, mul_add, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  simp only [mul_one]
  rcases hcomm g with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

omit [CharP k 2] in

/-- The distinguished algebra element commutes with every element of the monoid algebra. -/
lemma distinguishedAlgebraElement_mul_comm (y : MonoidAlgebra k ActingPermutationType) : distinguishedAlgebraElement k * y = y * distinguishedAlgebraElement k := by
  induction y using MonoidAlgebra.induction_on with
  | hM g => rw [MonoidAlgebra.of_apply]; exact distinguishedAlgebraElement_mul_single_comm k g
  | hadd a b ha hb => rw [mul_add, add_mul, ha, hb]
  | hsmul r a ha => rw [mul_smul_comm, ha, smul_mul_assoc]


/-- Data associated with the monoid algebra when the field has characteristic two. -/
noncomputable def monoidAlgebraCharacteristicTwoData : ringAuxiliaryType (MonoidAlgebra k ActingPermutationType) :=
  ⟨distinguishedAlgebraElement k, isIdempotentElem_distinguishedAlgebraElement k, distinguishedAlgebraElement_mul_comm k⟩


/-- The distinguished algebra element acts as zero on the one-dimensional representation. -/
lemma distinguishedAlgebraElement_smul_oneDimensionalRepresentation (m : (oneDimensionalRepresentation k).asModule) : distinguishedAlgebraElement k • m = 0 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hg : ∀ g : ActingPermutationType, MonoidAlgebra.single g (1 : k) • m = m := by
    intro g
    rw [Representation.single_smul, one_smul, oneDimensionalRepresentation, Representation.trivial_apply]
    rfl
  rw [distinguishedAlgebraElement, add_smul, hg, hg, ← two_smul k m, h2, zero_smul]


set_option backward.isDefEq.respectTransparency false in
/-- The distinguished algebra element acts as the identity on the restricted representation. -/
lemma distinguishedAlgebraElement_smul_restrictedRepresentation (m : (restrictedRepresentation k).asModule) : distinguishedAlgebraElement k • m = m := by
  set v : (distinguishedSubrepresentation k).toSubmodule := m with hv
  have hsum : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
    have hm := v.2
    simpa only [distinguishedSubrepresentation, LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three] using hm
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have key : ∀ g : ActingPermutationType, MonoidAlgebra.single g (1 : k) • m = restrictedRepresentation k g v := by
    intro g; rw [Representation.single_smul, one_smul]; rfl
  have coe_std : ∀ (g : ActingPermutationType) (i : Fin 3),
      ((restrictedRepresentation k g v : (distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) i
        = (v : Fin 3 → k) (g⁻¹ i) := fun g i => rfl
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ :
      distinguishedPermutation⁻¹ (0 : Fin 3) = 2 ∧ distinguishedPermutation⁻¹ (1 : Fin 3) = 0 ∧ distinguishedPermutation⁻¹ (2 : Fin 3) = 1 ∧
      (distinguishedPermutation ^ 2)⁻¹ (0 : Fin 3) = 1 ∧ (distinguishedPermutation ^ 2)⁻¹ (1 : Fin 3) = 2 ∧
      (distinguishedPermutation ^ 2)⁻¹ (2 : Fin 3) = 0 := by decide
  rw [distinguishedAlgebraElement, add_smul, key, key]
  refine Subtype.ext (funext fun i => ?_)
  rw [Submodule.coe_add, Pi.add_apply, coe_std, coe_std]
  fin_cases i
  · change (v : Fin 3 → k) (distinguishedPermutation⁻¹ 0) + (v : Fin 3 → k) ((distinguishedPermutation ^ 2)⁻¹ 0) = (v : Fin 3 → k) 0
    rw [a0, b0]; linear_combination hsum - (v : Fin 3 → k) 0 * h2
  · change (v : Fin 3 → k) (distinguishedPermutation⁻¹ 1) + (v : Fin 3 → k) ((distinguishedPermutation ^ 2)⁻¹ 1) = (v : Fin 3 → k) 1
    rw [a1, b1]; linear_combination hsum - (v : Fin 3 → k) 1 * h2
  · change (v : Fin 3 → k) (distinguishedPermutation⁻¹ 2) + (v : Fin 3 → k) ((distinguishedPermutation ^ 2)⁻¹ 2) = (v : Fin 3 → k) 2
    rw [a2, b2]; linear_combination hsum - (v : Fin 3 → k) 2 * h2

/-- The displayed relation does not hold between the two distinguished module objects in characteristic two. -/
theorem distinguishedModuleObjects_not_related :
    ¬ auxiliaryModuleRelation (MonoidAlgebra k ActingPermutationType) (oneDimensionalModuleObject k) (distinguishedModuleObject k) := by
  intro h
  have key := auxiliaryElement_actsAsIdentity_iff_of_condition (MonoidAlgebra k ActingPermutationType) (monoidAlgebraCharacteristicTwoData k) h
  have hstd : ∀ m : (distinguishedModuleObject k : Type), (monoidAlgebraCharacteristicTwoData k).1 • m = m := distinguishedAlgebraElement_smul_restrictedRepresentation k
  have htriv : ∀ m : (oneDimensionalModuleObject k : Type), (monoidAlgebraCharacteristicTwoData k).1 • m = m := key.mpr hstd
  haveI : Nontrivial (oneDimensionalModuleObject k : Type) := inferInstanceAs (Nontrivial k)
  obtain ⟨x, hx⟩ := exists_ne (0 : (oneDimensionalModuleObject k : Type))
  exact hx ((htriv x).symm.trans (distinguishedAlgebraElement_smul_oneDimensionalRepresentation k x))


/-- A second distinguished element of the acting permutation type. -/
def secondDistinguishedPermutation : ActingPermutationType := Equiv.swap 0 1

omit [CharP k 2] in

private lemma nonempty_iso_of_genEquivariant
    {V : Type} [AddCommGroup V] [Module k V]
    [Module (MonoidAlgebra k ActingPermutationType) V] [IsScalarTower k (MonoidAlgebra k ActingPermutationType) V]
    [IsSimpleModule (MonoidAlgebra k ActingPermutationType) V]
    {S : ModuleCat.{0} (MonoidAlgebra k ActingPermutationType)}
    [IsSimpleModule (MonoidAlgebra k ActingPermutationType) (S : Type)]
    [Module k (S : Type)] [IsScalarTower k (MonoidAlgebra k ActingPermutationType) (S : Type)]
    (f₀ : V →ₗ[k] (S : Type)) (hne : f₀ ≠ 0)
    (hc : ∀ x : V, f₀ (MonoidAlgebra.single distinguishedPermutation (1 : k) • x)
        = MonoidAlgebra.single distinguishedPermutation (1 : k) • f₀ x)
    (ht : ∀ x : V, f₀ (MonoidAlgebra.single (secondDistinguishedPermutation) (1 : k) • x)
        = MonoidAlgebra.single (secondDistinguishedPermutation) (1 : k) • f₀ x) :
    Nonempty (S ≅ ModuleCat.of (MonoidAlgebra k ActingPermutationType) V) := by
  classical
  set Q : ActingPermutationType → Prop := fun g => ∀ x : V,
    f₀ (MonoidAlgebra.single g (1 : k) • x) = MonoidAlgebra.single g (1 : k) • f₀ x with hQ
  have Qone : Q 1 := by
    intro x; simp only [← MonoidAlgebra.one_def, one_smul]
  have Qmul : ∀ g h : ActingPermutationType, Q g → Q h → Q (g * h) := by
    intro g h Qg Qh x
    have hsplit : MonoidAlgebra.single (g * h) (1 : k)
        = MonoidAlgebra.single g (1 : k) * MonoidAlgebra.single h 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hsplit, mul_smul, Qg (MonoidAlgebra.single h (1 : k) • x), Qh x, ← mul_smul]
  have Qsq : Q (distinguishedPermutation ^ 2) := by
    have := Qmul distinguishedPermutation distinguishedPermutation hc hc
    rwa [show distinguishedPermutation * distinguishedPermutation = distinguishedPermutation ^ 2 from by decide] at this
  have Qall : ∀ g : ActingPermutationType, Q g := by
    have henum : ∀ g : ActingPermutationType, g = 1 ∨ g = distinguishedPermutation ∨ g = distinguishedPermutation ^ 2 ∨ g = secondDistinguishedPermutation ∨
        g = distinguishedPermutation * secondDistinguishedPermutation ∨ g = distinguishedPermutation ^ 2 * secondDistinguishedPermutation := by decide
    intro g
    rcases henum g with h | h | h | h | h | h <;> subst h
    · exact Qone
    · exact hc
    · exact Qsq
    · exact ht
    · exact Qmul distinguishedPermutation secondDistinguishedPermutation hc ht
    · exact Qmul (distinguishedPermutation ^ 2) secondDistinguishedPermutation Qsq ht
  let F : V →ₗ[MonoidAlgebra k ActingPermutationType] (S : Type) :=
    { toFun := f₀
      map_add' := f₀.map_add
      map_smul' := by
        intro r x
        induction r using MonoidAlgebra.induction_on with
        | hM g => simpa [MonoidAlgebra.of_apply] using Qall g x
        | hadd a b ha hb =>
            simp only [add_smul, map_add, RingHom.id_apply] at ha hb ⊢
            rw [ha, hb]
        | hsmul c a ha =>
            simp only [RingHom.id_apply] at ha ⊢
            rw [smul_assoc, map_smul, ha, smul_assoc] }
  have hFapp : ∀ x, F x = f₀ x := fun _ => rfl
  have hFne : F ≠ 0 := by
    intro h; apply hne; ext x
    have := LinearMap.congr_fun h x
    rwa [hFapp, LinearMap.zero_apply] at this
  have hbij := LinearMap.bijective_of_ne_zero (M := V) (N := (S : Type)) hFne
  exact ⟨((LinearEquiv.ofBijective F hbij).toModuleIso).symm⟩


/-- Every simple module object over the monoid algebra is isomorphic to one of the two distinguished module objects. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
theorem simpleModule_iso_distinguished_or_oneDimensional (S : ModuleCat.{0} (MonoidAlgebra k ActingPermutationType))
    (hS : IsSimpleModule (MonoidAlgebra k ActingPermutationType) S) :
    Nonempty (S ≅ oneDimensionalModuleObject k) ∨ Nonempty (S ≅ distinguishedModuleObject k) := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type) := IsSimpleModule.nontrivial (MonoidAlgebra k ActingPermutationType) (S : Type)
  letI : Module k (S : Type) :=
    Module.compHom (S : Type) (algebraMap k (MonoidAlgebra k ActingPermutationType))
  haveI htower : IsScalarTower k (MonoidAlgebra k ActingPermutationType) (S : Type) := by
    refine ⟨fun c a m => ?_⟩
    have hc : (c • a) • m = (algebraMap k (MonoidAlgebra k ActingPermutationType) c * a) • m := by
      rw [Algebra.smul_def]
    rw [hc, mul_smul]; rfl
  haveI hcomm : SMulCommClass k (MonoidAlgebra k ActingPermutationType) (S : Type) := by
    refine ⟨fun c a m => ?_⟩
    have h1 : (c • a • m : (S : Type)) = (algebraMap k (MonoidAlgebra k ActingPermutationType) c) • a • m := rfl
    have h2 : (c • m : (S : Type)) = (algebraMap k (MonoidAlgebra k ActingPermutationType) c) • m := rfl
    rw [h1, h2, smul_smul, smul_smul, Algebra.commutes]
  have hchar2S : ∀ x : (S : Type), x + x = 0 := by
    intro x
    have h2 : (2 : k) • x = x + x := two_smul k x
    rw [← h2, show (2 : k) = 0 from by exact_mod_cast CharP.cast_eq_zero k 2, zero_smul]
  have hTr2 : ∀ m : (S : Type),
      MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • (MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • m) = m := by
    intro m
    rw [smul_smul, MonoidAlgebra.single_mul_single, mul_one, show secondDistinguishedPermutation * secondDistinguishedPermutation = 1 from by decide,
      ← MonoidAlgebra.one_def, one_smul]
  have smul_single : ∀ a b : ActingPermutationType,
      MonoidAlgebra.single a (1 : k) * MonoidAlgebra.single b 1
        = MonoidAlgebra.single (a * b) 1 := by
    intro a b; rw [MonoidAlgebra.single_mul_single, mul_one]
  obtain ⟨w, hw⟩ := exists_ne (0 : (S : Type))
  obtain ⟨u, hu_ne, hTu⟩ : ∃ u : (S : Type), u ≠ 0 ∧ MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • u = u := by
    by_cases hwfix : MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • w = w
    · exact ⟨w, hw, hwfix⟩
    · refine ⟨w + MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • w, ?_, ?_⟩
      · intro h
        apply hwfix
        have h1 : -w = MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • w := add_eq_zero_iff_neg_eq.mp h
        have h2 : -w = w := neg_eq_of_add_eq_zero_left (hchar2S w)
        exact h1.symm.trans h2
      · rw [smul_add, hTr2 w]; abel
  rcases centralIdempotent_actsAsZero_or_identity (MonoidAlgebra k ActingPermutationType) (M := (S : Type))
      (isIdempotentElem_distinguishedAlgebraElement k) (distinguishedAlgebraElement_mul_comm k) with h0 | h1
  · -- `e` acts as `0`: the trivial module.
    left
    have hCall : ∀ m : (S : Type), MonoidAlgebra.single distinguishedPermutation (1 : k) • m = m := by
      intro m
      have hN : (1 + distinguishedAlgebraElement k) • m = m := by
        rw [add_smul, one_smul, h0 m, add_zero]
      have e1 : MonoidAlgebra.single distinguishedPermutation (1 : k) * MonoidAlgebra.single distinguishedPermutation (1 : k)
          = MonoidAlgebra.single (distinguishedPermutation ^ 2) 1 := by
        rw [MonoidAlgebra.single_mul_single, mul_one, show distinguishedPermutation * distinguishedPermutation = distinguishedPermutation ^ 2 from by decide]
      have e2 : MonoidAlgebra.single distinguishedPermutation (1 : k) * MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) = 1 := by
        rw [MonoidAlgebra.single_mul_single, mul_one, show distinguishedPermutation * distinguishedPermutation ^ 2 = 1 from by decide,
          ← MonoidAlgebra.one_def]
      have hCN : MonoidAlgebra.single distinguishedPermutation (1 : k) * (1 + distinguishedAlgebraElement k) = 1 + distinguishedAlgebraElement k := by
        rw [distinguishedAlgebraElement, mul_add, mul_add, mul_one, e1, e2]; abel
      calc MonoidAlgebra.single distinguishedPermutation (1 : k) • m
            = MonoidAlgebra.single distinguishedPermutation (1 : k) • ((1 + distinguishedAlgebraElement k) • m) := by rw [hN]
        _ = (MonoidAlgebra.single distinguishedPermutation (1 : k) * (1 + distinguishedAlgebraElement k)) • m := by rw [mul_smul]
        _ = (1 + distinguishedAlgebraElement k) • m := by rw [hCN]
        _ = m := hN
    have hCu : MonoidAlgebra.single distinguishedPermutation (1 : k) • u = u := hCall u
    haveI : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (oneDimensionalRepresentation k).asModule :=
      oneDimensionalRepresentation_isSimpleModule k
    let f₀ : (oneDimensionalRepresentation k).asModule →ₗ[k] (S : Type) :=
      (LinearMap.toSpanSingleton k (S : Type) u).comp (oneDimensionalRepresentation k).asModuleEquiv.toLinearMap
    have hf₀ : ∀ x, f₀ x = ((oneDimensionalRepresentation k).asModuleEquiv x) • u := fun _ => rfl
    have hgen : ∀ (g : ActingPermutationType), MonoidAlgebra.single g (1 : k) • u = u := by
      have henum : ∀ g : ActingPermutationType, g = 1 ∨ g = distinguishedPermutation ∨ g = distinguishedPermutation ^ 2 ∨ g = secondDistinguishedPermutation ∨
          g = distinguishedPermutation * secondDistinguishedPermutation ∨ g = distinguishedPermutation ^ 2 * secondDistinguishedPermutation := by decide
      have hCu2 : MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u = u := by
        rw [show (distinguishedPermutation : ActingPermutationType) ^ 2 = distinguishedPermutation * distinguishedPermutation from by decide, ← smul_single, mul_smul, hCu, hCu]
      intro g
      rcases henum g with h | h | h | h | h | h <;> subst h
      · rw [← MonoidAlgebra.one_def, one_smul]
      · exact hCu
      · exact hCu2
      · exact hTu
      · rw [← smul_single distinguishedPermutation secondDistinguishedPermutation, mul_smul, hTu, hCu]
      · rw [← smul_single (distinguishedPermutation ^ 2) secondDistinguishedPermutation, mul_smul, hTu, hCu2]
    have hequiv : ∀ (g : ActingPermutationType) (x : (oneDimensionalRepresentation k).asModule),
        f₀ (MonoidAlgebra.single g (1 : k) • x)
        = MonoidAlgebra.single g (1 : k) • f₀ x := by
      intro g x
      rw [hf₀, hf₀, Representation.single_smul, oneDimensionalRepresentation, Representation.trivial_apply, one_smul,
        smul_comm]
      congr 1
      rw [hgen g]
    have hne : f₀ ≠ 0 := by
      intro h
      apply hu_ne
      have hval := LinearMap.congr_fun h ((oneDimensionalRepresentation k).asModuleEquiv.symm 1)
      rw [hf₀, LinearMap.zero_apply, LinearEquiv.apply_symm_apply, one_smul] at hval
      exact hval
    have hiso := nonempty_iso_of_genEquivariant k f₀ hne (hequiv distinguishedPermutation) (hequiv secondDistinguishedPermutation)
    exact ⟨hiso.some⟩
  · -- `e` acts as the identity: the standard module.
    right
    have hCC : MonoidAlgebra.single distinguishedPermutation (1 : k) • (MonoidAlgebra.single distinguishedPermutation (1 : k) • u)
        = MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u := by
      rw [smul_smul, MonoidAlgebra.single_mul_single, mul_one,
        show distinguishedPermutation * distinguishedPermutation = distinguishedPermutation ^ 2 from by decide]
    have hCsq2 : MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u
        = u + MonoidAlgebra.single distinguishedPermutation (1 : k) • u := by
      have hE : (MonoidAlgebra.single distinguishedPermutation (1 : k) + MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k)) • u
          = u := by have := h1 u; rwa [distinguishedAlgebraElement] at this
      have hsum : MonoidAlgebra.single distinguishedPermutation (1 : k) • u
          + MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u = u := by rw [← add_smul]; exact hE
      have hstep : (MonoidAlgebra.single distinguishedPermutation (1 : k) • u
          + MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u)
          + MonoidAlgebra.single distinguishedPermutation (1 : k) • u = MonoidAlgebra.single (distinguishedPermutation ^ 2) (1 : k) • u := by
        rw [add_right_comm, hchar2S, zero_add]
      rw [hsum] at hstep
      exact hstep.symm
    have hCsq : MonoidAlgebra.single distinguishedPermutation (1 : k) • (MonoidAlgebra.single distinguishedPermutation (1 : k) • u)
        = u + MonoidAlgebra.single distinguishedPermutation (1 : k) • u := hCC.trans hCsq2
    have hTC : MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • (MonoidAlgebra.single distinguishedPermutation (1 : k) • u)
        = u + MonoidAlgebra.single distinguishedPermutation (1 : k) • u := by
      rw [smul_smul, smul_single secondDistinguishedPermutation distinguishedPermutation, show secondDistinguishedPermutation * distinguishedPermutation = distinguishedPermutation ^ 2 * secondDistinguishedPermutation from by decide,
        ← smul_single (distinguishedPermutation ^ 2) secondDistinguishedPermutation, mul_smul, hTu, hCsq2]
    haveI : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (restrictedRepresentation k).asModule :=
      restrictedRepresentation_isSimpleModule k
    let g₀ : ↥(distinguishedSubrepresentation k).toSubmodule →ₗ[k] (S : Type) :=
      { toFun := fun v => ((v : Fin 3 → k) 0) • u + ((v : Fin 3 → k) 2)
          • (MonoidAlgebra.single distinguishedPermutation (1 : k) • u)
        map_add' := by
          intro v w
          simp only [Submodule.coe_add, Pi.add_apply, add_smul]
          abel
        map_smul' := by
          intro c v
          simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
            smul_add] }
    let f₀ : (restrictedRepresentation k).asModule →ₗ[k] (S : Type) :=
      g₀.comp (restrictedRepresentation k).asModuleEquiv.toLinearMap
    have hf₀ : ∀ x, f₀ x = (((restrictedRepresentation k).asModuleEquiv x : Fin 3 → k) 0) • u
        + (((restrictedRepresentation k).asModuleEquiv x : Fin 3 → k) 2) • (MonoidAlgebra.single distinguishedPermutation (1 : k) • u) :=
      fun _ => rfl
    have coord : ∀ (g : ActingPermutationType) (v : ↥(distinguishedSubrepresentation k).toSubmodule) (i : Fin 3),
        ((restrictedRepresentation k g v : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) i = (v : Fin 3 → k) (g⁻¹ i) := by
      intro g v i; rw [stdRepr_val, coordinatePermutationRepresentation_apply]
    have hc : ∀ x : (restrictedRepresentation k).asModule,
        f₀ (MonoidAlgebra.single distinguishedPermutation (1 : k) • x)
        = MonoidAlgebra.single distinguishedPermutation (1 : k) • f₀ x := by
      intro x
      set v : ↥(distinguishedSubrepresentation k).toSubmodule := (restrictedRepresentation k).asModuleEquiv x with hv
      have hvsum : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
        have hm := v.2
        simpa only [distinguishedSubrepresentation, LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three] using hm
      rw [hf₀, hf₀]
      have hEq : ((restrictedRepresentation k).asModuleEquiv (MonoidAlgebra.single distinguishedPermutation (1 : k) • x))
          = restrictedRepresentation k distinguishedPermutation v := by
        rw [(restrictedRepresentation k).asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one, ← hv]
      rw [hEq]
      have c0 : ((restrictedRepresentation k distinguishedPermutation v : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) 0
          = (v : Fin 3 → k) 2 := by
        rw [coord]; norm_num [show (distinguishedPermutation : ActingPermutationType)⁻¹ 0 = 2 from by decide]
      have c2 : ((restrictedRepresentation k distinguishedPermutation v : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) 2
          = (v : Fin 3 → k) 1 := by
        rw [coord]; norm_num [show (distinguishedPermutation : ActingPermutationType)⁻¹ 2 = 1 from by decide]
      rw [c0, c2, smul_add, smul_comm (MonoidAlgebra.single distinguishedPermutation (1 : k)) ((v : Fin 3 → k) 0),
        smul_comm (MonoidAlgebra.single distinguishedPermutation (1 : k)) ((v : Fin 3 → k) 2), hCsq]
      have hv1 : (v : Fin 3 → k) 1 = (v : Fin 3 → k) 0 + (v : Fin 3 → k) 2 := by
        have : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := hvsum
        have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
        linear_combination this - ((v : Fin 3 → k) 0 + (v : Fin 3 → k) 2) * h2
      rw [hv1, smul_add, add_smul]
      abel
    have ht : ∀ x : (restrictedRepresentation k).asModule,
        f₀ (MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • x)
        = MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • f₀ x := by
      intro x
      set v : ↥(distinguishedSubrepresentation k).toSubmodule := (restrictedRepresentation k).asModuleEquiv x with hv
      have hvsum : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
        have hm := v.2
        simpa only [distinguishedSubrepresentation, LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three] using hm
      rw [hf₀, hf₀]
      have hEq : ((restrictedRepresentation k).asModuleEquiv (MonoidAlgebra.single secondDistinguishedPermutation (1 : k) • x))
          = restrictedRepresentation k secondDistinguishedPermutation v := by
        rw [(restrictedRepresentation k).asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one, ← hv]
      rw [hEq]
      have t0 : ((restrictedRepresentation k secondDistinguishedPermutation v : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) 0
          = (v : Fin 3 → k) 1 := by
        rw [coord]; norm_num [show (secondDistinguishedPermutation : ActingPermutationType)⁻¹ 0 = 1 from by decide]
      have t2 : ((restrictedRepresentation k secondDistinguishedPermutation v : ↥(distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) 2
          = (v : Fin 3 → k) 2 := by
        rw [coord]; norm_num [show (secondDistinguishedPermutation : ActingPermutationType)⁻¹ 2 = 2 from by decide]
      rw [t0, t2, smul_add, smul_comm (MonoidAlgebra.single secondDistinguishedPermutation (1 : k)) ((v : Fin 3 → k) 0),
        smul_comm (MonoidAlgebra.single secondDistinguishedPermutation (1 : k)) ((v : Fin 3 → k) 2), hTu, hTC]
      have hv1 : (v : Fin 3 → k) 1 = (v : Fin 3 → k) 0 + (v : Fin 3 → k) 2 := by
        have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
        linear_combination hvsum - ((v : Fin 3 → k) 0 + (v : Fin 3 → k) 2) * h2
      rw [hv1, add_smul, smul_add]
      abel
    have hne : f₀ ≠ 0 := by
      intro h
      apply hu_ne
      have hmem : (![1, 1, 0] : Fin 3 → k) ∈ LinearMap.ker (coordinateSum k) := by
        rw [LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, add_zero]
        rw [one_add_one_eq_two, show (2 : k) = 0 from by exact_mod_cast CharP.cast_eq_zero k 2]
      have hval := LinearMap.congr_fun h ((restrictedRepresentation k).asModuleEquiv.symm ⟨![1, 1, 0], hmem⟩)
      rw [LinearMap.zero_apply, hf₀, LinearEquiv.apply_symm_apply] at hval
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        one_smul, zero_smul, add_zero] at hval
      exact hval
    have hiso := nonempty_iso_of_genEquivariant (V := (restrictedRepresentation k).asModule)
      (S := S) k f₀ hne hc ht
    exact ⟨hiso.some⟩


/-- The associated type for the monoid algebra has cardinality two. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
theorem associatedType_card_eq_two :
    Nat.card (AuxiliaryModuleType.{0} (MonoidAlgebra k ActingPermutationType)) = 2 := by
  classical
  have htriv : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (oneDimensionalModuleObject k) := oneDimensionalRepresentation_isSimpleModule k
  have hstd : IsSimpleModule (MonoidAlgebra k ActingPermutationType) (distinguishedModuleObject k) := restrictedRepresentation_isSimpleModule k
  have cc_triv :
      simpleModuleAuxiliaryBool (MonoidAlgebra k ActingPermutationType) htriv (monoidAlgebraCharacteristicTwoData k) = false := by
    rw [simpleModuleAuxiliaryBool_eq_false_iff_actsAsZero]; exact distinguishedAlgebraElement_smul_oneDimensionalRepresentation k
  have cc_std :
      simpleModuleAuxiliaryBool (MonoidAlgebra k ActingPermutationType) hstd (monoidAlgebraCharacteristicTwoData k) = true := by
    rw [simpleModuleAuxiliaryBool_eq_true_iff_actsAsIdentity]; exact distinguishedAlgebraElement_smul_restrictedRepresentation k
  have cc_iso : ∀ {X Y : ModuleCat.{0} (MonoidAlgebra k ActingPermutationType)}
      (hX : IsSimpleModule (MonoidAlgebra k ActingPermutationType) X) (hY : IsSimpleModule (MonoidAlgebra k ActingPermutationType) Y),
      Nonempty (X ≅ Y) →
      simpleModuleAuxiliaryBool (MonoidAlgebra k ActingPermutationType) hX (monoidAlgebraCharacteristicTwoData k)
        = simpleModuleAuxiliaryBool (MonoidAlgebra k ActingPermutationType) hY (monoidAlgebraCharacteristicTwoData k) := by
    rintro X Y hX hY ⟨e⟩
    exact simpleModuleAuxiliaryBool_eq_of_condition (MonoidAlgebra k ActingPermutationType) hX hY _
      (auxiliaryModuleRelation_of_iso (MonoidAlgebra k ActingPermutationType) hX hY e)
  set g : AuxiliaryType.{0} (MonoidAlgebra k ActingPermutationType) → Bool := fun S =>
    simpleModuleAuxiliaryBool (MonoidAlgebra k ActingPermutationType) S.2 (monoidAlgebraCharacteristicTwoData k) with hg_def
  have hg : ∀ a b : AuxiliaryType.{0} (MonoidAlgebra k ActingPermutationType),
      (auxiliaryTypeSetoid (MonoidAlgebra k ActingPermutationType)).r a b → g a = g b :=
    fun a b hab =>
      simpleModuleAuxiliaryBool_eq_of_condition (MonoidAlgebra k ActingPermutationType) a.2 b.2 _ hab
  set f : AuxiliaryModuleType.{0} (MonoidAlgebra k ActingPermutationType) → Bool := Quotient.lift g hg with hf_def
  have hsurj : Function.Surjective f := by
    intro b
    cases b
    · exact ⟨Quotient.mk _ ⟨oneDimensionalModuleObject k, htriv⟩, cc_triv⟩
    · exact ⟨Quotient.mk _ ⟨distinguishedModuleObject k, hstd⟩, cc_std⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    refine Quotient.sound (show auxiliaryModuleRelation (MonoidAlgebra k ActingPermutationType) a.1 b.1 from ?_)
    have hab' : g a = g b := hxy
    rcases simpleModule_iso_distinguished_or_oneDimensional k a.1 a.2 with ha | ha <;>
      rcases simpleModule_iso_distinguished_or_oneDimensional k b.1 b.2 with hb | hb
    · exact auxiliaryModuleRelation_of_iso _ a.2 b.2 (ha.some ≪≫ hb.some.symm)
    · exact absurd (((cc_iso a.2 htriv ha).trans cc_triv).symm.trans
        (hab'.trans ((cc_iso b.2 hstd hb).trans cc_std))) (by decide)
    · exact absurd (((cc_iso a.2 hstd ha).trans cc_std).symm.trans
        (hab'.trans ((cc_iso b.2 htriv hb).trans cc_triv))) (by decide)
    · exact auxiliaryModuleRelation_of_iso _ a.2 b.2 (ha.some ≪≫ hb.some.symm)
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_bool]




/-- A distinguished element of the auxiliary algebra. -/
noncomputable def distinguishedNilpotent : AuxiliaryAlgebra k := AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 2)


/-- In characteristic two, the square of the distinguished auxiliary element is zero. -/
lemma distinguishedNilpotent_sq : (distinguishedNilpotent k) ^ 2 = 0 := by
  have h : AdjoinRoot.mk ((Polynomial.X : Polynomial k) ^ 2)
      ((Polynomial.X : Polynomial k) ^ 2) = 0 := AdjoinRoot.mk_self
  rwa [map_pow, AdjoinRoot.mk_X] at h


/-- Over a field of characteristic two, one plus one is zero. -/
lemma one_add_one_eq_zero : (1 : AuxiliaryAlgebra k) + 1 = 0 := by
  have hk : (1 : k) + 1 = 0 := by
    have := CharTwo.two_eq_zero (R := k); rw [← one_add_one_eq_two] at this; exact this
  rw [← map_one (algebraMap k (AuxiliaryAlgebra k)), ← map_add, hk, map_zero]


/-- In characteristic two, the square of one plus the distinguished auxiliary element is one. -/
lemma one_add_distinguishedNilpotent_sq : (1 + distinguishedNilpotent k) * (1 + distinguishedNilpotent k) = 1 := by
  have ht := distinguishedNilpotent_sq k
  have hk := one_add_one_eq_zero k
  linear_combination (distinguishedNilpotent k) * hk + ht


/-- A monoid homomorphism from the units of the integers to the auxiliary algebra in characteristic two. -/
noncomputable def unitsToAuxiliaryAlgebra : ℤˣ →* AuxiliaryAlgebra k where
  toFun s := if s = 1 then 1 else 1 + distinguishedNilpotent k
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with ha | ha <;> rcases Int.units_eq_one_or b with hb | hb
    · subst ha; subst hb; simp
    · subst ha; subst hb; simp [show (-1 : ℤˣ) ≠ 1 from by decide]
    · subst ha; subst hb; simp [show (-1 : ℤˣ) ≠ 1 from by decide]
    · subst ha; subst hb
      rw [show ((-1 : ℤˣ) * -1) = 1 from by decide, if_pos rfl,
        if_neg (show (-1 : ℤˣ) ≠ 1 from by decide)]
      exact (one_add_distinguishedNilpotent_sq k).symm

/-- The units homomorphism sends one to one. -/
@[simp] lemma unitsToAuxiliaryAlgebra_one : unitsToAuxiliaryAlgebra k 1 = 1 := by simp [unitsToAuxiliaryAlgebra]

/-- A property of the units-to-auxiliary-algebra homomorphism in characteristic two. -/
@[simp] lemma unitsToAuxiliaryAlgebra_property : unitsToAuxiliaryAlgebra k (-1) = 1 + distinguishedNilpotent k := by
  change (if (-1 : ℤˣ) = 1 then (1 : AuxiliaryAlgebra k) else 1 + distinguishedNilpotent k) = 1 + distinguishedNilpotent k
  rw [if_neg (show (-1 : ℤˣ) ≠ 1 from by decide)]


/-- A monoid homomorphism from the acting permutation type to the auxiliary algebra in characteristic two. -/
noncomputable def auxiliaryMonoidHom : ActingPermutationType →* AuxiliaryAlgebra k := (unitsToAuxiliaryAlgebra k).comp (Equiv.Perm.sign)


/-- An algebra homomorphism from the monoid algebra to the auxiliary algebra in characteristic two. -/
noncomputable def auxiliaryAlgebraHom : MonoidAlgebra k ActingPermutationType →ₐ[k] AuxiliaryAlgebra k :=
  MonoidAlgebra.lift k (AuxiliaryAlgebra k) ActingPermutationType (auxiliaryMonoidHom k)

/-- On a single basis element, the auxiliary algebra homomorphism agrees with the units homomorphism evaluated at its sign. -/
@[simp] lemma auxiliaryAlgebraHom_single (g : ActingPermutationType) :
    auxiliaryAlgebraHom k (MonoidAlgebra.single g 1) = unitsToAuxiliaryAlgebra k (Equiv.Perm.sign g) := by
  rw [auxiliaryAlgebraHom, MonoidAlgebra.lift_single, one_smul]; rfl


set_option backward.isDefEq.respectTransparency false in
/-- The auxiliary algebra homomorphism is surjective. -/
lemma auxiliaryAlgebraHom_surjective : Function.Surjective (auxiliaryAlgebraHom k) := by
  intro y
  have hmem : y ∈ (⊤ : Subalgebra k (AuxiliaryAlgebra k)) := Algebra.mem_top
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := (Polynomial.X : Polynomial k) ^ 2)] at hmem
  have hle : Algebra.adjoin k {AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 2)}
      ≤ (auxiliaryAlgebraHom k).range := by
    rw [Algebra.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    change distinguishedNilpotent k ∈ (auxiliaryAlgebraHom k).range
    have ht1 : (1 + distinguishedNilpotent k) ∈ (auxiliaryAlgebraHom k).range :=
      (auxiliaryAlgebraHom k).mem_range.mpr ⟨MonoidAlgebra.single (Equiv.swap 0 1) 1, by
        rw [auxiliaryAlgebraHom_single, Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide), unitsToAuxiliaryAlgebra_property]⟩
    have hsub := sub_mem ht1 (one_mem (auxiliaryAlgebraHom k).range)
    simpa using hsub
  obtain ⟨x, hx⟩ := hle hmem
  exact ⟨x, hx⟩




/-- The distinguished subrepresentation is linearly equivalent to functions on two indices. -/
def distinguishedSubrepresentationEquiv : (distinguishedSubrepresentation k).toSubmodule ≃ₗ[k] (Fin 2 → k) where
  toFun v := ![(v : Fin 3 → k) 0, (v : Fin 3 → k) 2]
  map_add' a b := by
    ext i; fin_cases i <;> simp [Submodule.coe_add]
  map_smul' r a := by
    ext i; fin_cases i <;> simp
  invFun c := ⟨![c 0, c 0 + c 1, c 1], by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    simp only [distinguishedSubrepresentation, LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination (c 0 + c 1) * h2⟩
  left_inv v := by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    have hv : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
      have := v.2
      simpa only [distinguishedSubrepresentation, LinearMap.mem_ker, coordinateSum_apply, Fin.sum_univ_three] using this
    apply Subtype.ext; funext i; fin_cases i
    · rfl
    · change (v : Fin 3 → k) 0 + (v : Fin 3 → k) 2 = (v : Fin 3 → k) 1
      linear_combination hv - (v : Fin 3 → k) 1 * h2
    · rfl
  right_inv c := by
    funext i; fin_cases i <;> rfl

/-- The first coordinate of the linear equivalence is the value of the vector at index zero. -/
@[simp] lemma distinguishedSubrepresentationEquiv_apply_zero (v : (distinguishedSubrepresentation k).toSubmodule) :
    distinguishedSubrepresentationEquiv k v 0 = (v : Fin 3 → k) 0 := rfl

/-- The second coordinate of the linear equivalence is the value of the vector at index two. -/
@[simp] lemma distinguishedSubrepresentationEquiv_apply_one (v : (distinguishedSubrepresentation k).toSubmodule) :
    distinguishedSubrepresentationEquiv k v 1 = (v : Fin 3 → k) 2 := rfl


/-- A basis indexed by two coordinates for the distinguished subrepresentation. -/
noncomputable def distinguishedSubrepresentationBasis : Module.Basis (Fin 2) k (distinguishedSubrepresentation k).toSubmodule :=
  Module.Basis.ofEquivFun (distinguishedSubrepresentationEquiv k)


/-- An algebra homomorphism from the monoid algebra to two-by-two matrices in characteristic two. -/
noncomputable def matrixAlgebraHom : MonoidAlgebra k ActingPermutationType →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  (LinearMap.toMatrixAlgEquiv (distinguishedSubrepresentationBasis k)).toAlgHom.comp (restrictedRepresentation k).asAlgebraHom

/-- The image of a single basis element is the matrix of its action on the distinguished subrepresentation. -/
lemma matrixAlgebraHom_single_eq_toMatrix (g : ActingPermutationType) :
    matrixAlgebraHom k (MonoidAlgebra.single g 1) = LinearMap.toMatrix (distinguishedSubrepresentationBasis k) (distinguishedSubrepresentationBasis k) (restrictedRepresentation k g) := by
  rw [matrixAlgebraHom, AlgHom.comp_apply, Representation.asAlgebraHom_single, one_smul]
  rfl


/-- A matrix entry of the image of a single basis element is computed from its action on the corresponding basis vector. -/
lemma matrixAlgebraHom_single_apply (g : ActingPermutationType) (i j : Fin 2) :
    matrixAlgebraHom k (MonoidAlgebra.single g 1) i j
      = distinguishedSubrepresentationEquiv k (restrictedRepresentation k g ((distinguishedSubrepresentationEquiv k).symm (Pi.single j 1))) i := by
  rw [matrixAlgebraHom_single_eq_toMatrix, LinearMap.toMatrix_apply]
  simp only [distinguishedSubrepresentationBasis, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]

/-- The inverse equivalence sends two coordinates to the vector whose entries are the first coordinate, their sum, and the second coordinate. -/
@[simp] lemma distinguishedSubrepresentationEquiv_symm_apply (c : Fin 2 → k) :
    (((distinguishedSubrepresentationEquiv k).symm c : (distinguishedSubrepresentation k).toSubmodule) : Fin 3 → k) = ![c 0, c 0 + c 1, c 1] := rfl

/-- The single basis element at the identity maps to the identity matrix. -/
lemma matrixAlgebraHom_single_one : matrixAlgebraHom k (MonoidAlgebra.single (1 : ActingPermutationType) 1) = 1 := by
  ext i j
  rw [matrixAlgebraHom_single_apply, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply,
    Pi.single_apply, Matrix.one_apply]

/-- The distinguished permutation maps to the displayed two-by-two matrix. -/
lemma matrixAlgebraHom_single_distinguishedPermutation : matrixAlgebraHom k (MonoidAlgebra.single distinguishedPermutation 1) = !![0, 1; 1, 1] := by
  have e0 : distinguishedPermutation⁻¹ (0 : Fin 3) = 2 := by decide
  have e2 : distinguishedPermutation⁻¹ (2 : Fin 3) = 1 := by decide
  ext i j
  rw [matrixAlgebraHom_single_apply]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]

/-- The transposition of indices zero and one maps to the displayed two-by-two matrix. -/
lemma matrixAlgebraHom_single_swap_zero_one : matrixAlgebraHom k (MonoidAlgebra.single (Equiv.swap 0 1) 1) = !![1, 1; 0, 1] := by
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  ext i j
  rw [matrixAlgebraHom_single_apply]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]

/-- The transposition of indices zero and two maps to the displayed two-by-two matrix. -/
lemma matrixAlgebraHom_single_swap_zero_two : matrixAlgebraHom k (MonoidAlgebra.single (Equiv.swap 0 2) 1) = !![0, 1; 1, 0] := by
  have e0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  ext i j
  rw [matrixAlgebraHom_single_apply]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]


/-- The matrix algebra homomorphism is surjective. -/
lemma matrixAlgebraHom_surjective : Function.Surjective (matrixAlgebraHom k) := by
  have m1 : (1 : Matrix (Fin 2) (Fin 2) k) ∈ (matrixAlgebraHom k).range :=
    matrixAlgebraHom_single_one k ▸ (matrixAlgebraHom k).mem_range_self _
  have mA : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) k) ∈ (matrixAlgebraHom k).range :=
    matrixAlgebraHom_single_distinguishedPermutation k ▸ (matrixAlgebraHom k).mem_range_self _
  have mC : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) ∈ (matrixAlgebraHom k).range :=
    matrixAlgebraHom_single_swap_zero_one k ▸ (matrixAlgebraHom k).mem_range_self _
  have mE : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k) ∈ (matrixAlgebraHom k).range :=
    matrixAlgebraHom_single_swap_zero_two k ▸ (matrixAlgebraHom k).mem_range_self _
  have u00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k) ∈ (matrixAlgebraHom k).range := by
    have h : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k)
        = 1 + !![0, 1; 1, 1] + !![0, 1; 1, 0] := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem (add_mem m1 mA) mE
  have u01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) ∈ (matrixAlgebraHom k).range := by
    have h : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) = !![1, 1; 0, 1] + 1 := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem mC m1
  have u10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : k) ∈ (matrixAlgebraHom k).range := by
    have h : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : k)
        = !![0, 1; 1, 0] + !![1, 1; 0, 1] + 1 := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem (add_mem mE mC) m1
  have u11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : k) ∈ (matrixAlgebraHom k).range := by
    have h : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : k) = !![0, 1; 1, 1] + !![0, 1; 1, 0] := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem mA mE
  have huniv : ∀ (i j : Fin 2) (x : k), Matrix.single i j x ∈ (matrixAlgebraHom k).range := by
    intro i j x
    have hsmul : Matrix.single i j x = x • Matrix.single i j (1 : k) := by
      ext a b; simp [Matrix.single_apply, Matrix.smul_apply, mul_ite, mul_one, mul_zero]
    rw [hsmul]
    refine Subalgebra.smul_mem _ ?_ x
    fin_cases i <;> fin_cases j <;> assumption
  intro m
  refine (matrixAlgebraHom k).mem_range.mp ?_
  rw [Matrix.matrix_eq_sum_single m]
  exact sum_mem fun i _ => sum_mem fun j _ => huniv i j (m i j)

/-- The square of the distinguished permutation maps to the displayed two-by-two matrix. -/
lemma matrixAlgebraHom_single_distinguishedPermutation_sq : matrixAlgebraHom k (MonoidAlgebra.single (distinguishedPermutation ^ 2) 1) = !![1, 1; 1, 0] := by
  have e0 : (distinguishedPermutation ^ 2)⁻¹ (0 : Fin 3) = 1 := by decide
  have e2 : (distinguishedPermutation ^ 2)⁻¹ (2 : Fin 3) = 0 := by decide
  ext i j
  rw [matrixAlgebraHom_single_apply]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2, -map_pow]




/-- The matrix algebra homomorphism sends the distinguished algebra element to the identity matrix. -/
lemma matrixAlgebraHom_distinguishedAlgebraElement : matrixAlgebraHom k (distinguishedAlgebraElement k) = 1 := by
  rw [distinguishedAlgebraElement]
  simp only [map_add, matrixAlgebraHom_single_distinguishedPermutation, matrixAlgebraHom_single_distinguishedPermutation_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, CharTwo.add_self_eq_zero]


/-- The auxiliary algebra homomorphism sends the distinguished algebra element to zero. -/
lemma auxiliaryAlgebraHom_distinguishedAlgebraElement : auxiliaryAlgebraHom k (distinguishedAlgebraElement k) = 0 := by
  have hs1 : Equiv.Perm.sign distinguishedPermutation = 1 := by decide
  have hs2 : Equiv.Perm.sign (distinguishedPermutation ^ 2) = 1 := by decide
  rw [distinguishedAlgebraElement]
  simp only [map_add, auxiliaryAlgebraHom_single, hs1, hs2, unitsToAuxiliaryAlgebra_one]
  exact one_add_one_eq_zero k


/-- In characteristic two, the monoid algebra is algebra-equivalent to a product of two-by-two matrices and the auxiliary algebra. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
theorem nonempty_algEquiv_matrix_prod_auxiliaryAlgebra :
    Nonempty (MonoidAlgebra k ActingPermutationType ≃ₐ[k] Matrix (Fin 2) (Fin 2) k × AuxiliaryAlgebra k) := by
  classical
  have hne : (Polynomial.X : Polynomial k) ^ 2 ≠ 0 := pow_ne_zero 2 Polynomial.X_ne_zero
  haveI hfinR : FiniteDimensional k (AuxiliaryAlgebra k) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (f := (Polynomial.X : Polynomial k) ^ 2) hne).basis
  set φ := (matrixAlgebraHom k).prod (auxiliaryAlgebraHom k) with hφ
  have hsurj : Function.Surjective φ := by
    rintro ⟨m, y⟩
    obtain ⟨a, ha⟩ := matrixAlgebraHom_surjective k m
    obtain ⟨b, hb⟩ := auxiliaryAlgebraHom_surjective k y
    refine ⟨distinguishedAlgebraElement k * a + (1 - distinguishedAlgebraElement k) * b, ?_⟩
    have hr : matrixAlgebraHom k (distinguishedAlgebraElement k * a + (1 - distinguishedAlgebraElement k) * b) = m := by
      simp only [map_add, map_mul, map_sub, map_one, matrixAlgebraHom_distinguishedAlgebraElement, one_mul, sub_self, zero_mul,
        add_zero, ha]
    have hp : auxiliaryAlgebraHom k (distinguishedAlgebraElement k * a + (1 - distinguishedAlgebraElement k) * b) = y := by
      simp only [map_add, map_mul, map_sub, map_one, auxiliaryAlgebraHom_distinguishedAlgebraElement, zero_mul, zero_add, sub_zero,
        one_mul, hb]
    rw [hφ, AlgHom.prod_apply, Prod.mk.injEq]
    exact ⟨hr, hp⟩
  have hfL : Module.finrank k (MonoidAlgebra k ActingPermutationType) = 6 := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis ActingPermutationType k)]
    decide
  have hfR : Module.finrank k (Matrix (Fin 2) (Fin 2) k × AuxiliaryAlgebra k) = 6 := by
    rw [Module.finrank_prod, Module.finrank_matrix, finrank_quotient_span_eq_natDegree,
      Polynomial.natDegree_X_pow, Module.finrank_self, Fintype.card_fin]
  have H : Module.finrank k (MonoidAlgebra k ActingPermutationType)
      = Module.finrank k (Matrix (Fin 2) (Fin 2) k × AuxiliaryAlgebra k) := by rw [hfL, hfR]
  have hsurj' : Function.Surjective φ.toLinearMap := hsurj
  have hinj' : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mpr hsurj'
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj', hsurj⟩⟩

end RepresentationTheory.PermutationRepresentation.CharTwo

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.PermutationRepresentation.CharTwo.Auxiliary.statement014084 := _root_.RepresentationTheory.PermutationRepresentation.CharTwo.unitsToAuxiliaryAlgebra_property
