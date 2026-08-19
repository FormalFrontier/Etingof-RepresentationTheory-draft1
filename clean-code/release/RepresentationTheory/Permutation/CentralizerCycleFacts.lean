/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.Equiv.Perm.CycleShiftCentralizer

/-!
# Centralizer cycle facts for finite permutations

This module constructs auxiliary cycle-indexed equivalences for a finite permutation, describes
its singleton centralizer through the corresponding cycle-shift centralizer, and compares the
resulting auxiliary counts with the permutation's cycle type.
-/

namespace RepresentationTheory.Permutation.CentralizerCycleFacts

open _root_.Equiv _root_.Function _root_.Subgroup _root_.MulAction
  _root_.RepresentationTheory.Equiv.Perm.CycleShiftCentralizer

namespace Equiv.Perm

variable {α : Type*} [Finite α] (g : _root_.Equiv.Perm α)

/-- An auxiliary type associated with a permutation. -/
abbrev AuxiliaryIndex : Type _ := orbitRel.Quotient (_root_.Subgroup.zpowers g) α

/-- An auxiliary natural number attached to a permutation and an auxiliary index. -/
noncomputable def auxiliaryIndexValue (q : AuxiliaryIndex g) : ℕ := minimalPeriod (g • ·) q.out

variable {g} in
/-- Every auxiliary index value of a permutation of a finite type is nonzero. -/
theorem auxiliaryIndexValue_ne_zero (q : AuxiliaryIndex g) : auxiliaryIndexValue g q ≠ 0 :=
  (MulAction.minimalPeriod_pos (a := g) (b := q.out)).ne

/-- An auxiliary natural-number-indexed type family associated with a permutation. -/
abbrev AuxiliaryIndexedType (m : ℕ) : Type _ :=
  {q : AuxiliaryIndex g // auxiliaryIndexValue g q = m}

/-- For a permutation of a finite type, the auxiliary indexed type at zero is empty. -/
instance isEmpty_auxiliaryIndexedType_zero : IsEmpty (AuxiliaryIndexedType g 0) :=
  ⟨fun q => auxiliaryIndexValue_ne_zero q.val q.property⟩

/-- An auxiliary definition. -/
noncomputable def auxiliaryDefinition :
    α ≃ Σ q : AuxiliaryIndex g, ZMod (auxiliaryIndexValue g q) :=
  (selfEquivSigmaOrbits (_root_.Subgroup.zpowers g) α).trans
    (_root_.Equiv.sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

omit [Finite α] in
/-- The inverse auxiliary map on the displayed sigma input agrees with the indicated permutation-power action. -/
theorem auxiliaryDefinition_symm_apply
    (q : AuxiliaryIndex g) (k : ZMod (auxiliaryIndexValue g q)) :
    (auxiliaryDefinition g).symm ⟨q, k⟩ = g ^ (ZMod.cast k : ℤ) • q.out := rfl

/-- An auxiliary equivalence from the underlying type of a permutation. -/
noncomputable def auxiliaryEquiv : α ≃ CycleIndexSpace (AuxiliaryIndexedType g) :=
  (auxiliaryDefinition g).trans
    { toFun := fun p => ⟨auxiliaryIndexValue g p.1, (⟨p.1, rfl⟩, p.2)⟩
      invFun := fun s => ⟨s.2.1.val, cast (congrArg ZMod s.2.1.property.symm) s.2.2⟩
      left_inv := fun p => by simp
      right_inv := fun s => by
        obtain ⟨m, ⟨q, h⟩, x⟩ := s
        subst h
        simp }

omit [Finite α] in
/-- An auxiliary equality. -/
theorem auxiliaryEquality (m : ℕ) (q : AuxiliaryIndexedType g m) (x : ZMod m) :
    (auxiliaryEquiv g).symm ⟨m, (q, x)⟩ =
      (auxiliaryDefinition g).symm
        ⟨q.val, cast (congrArg ZMod q.property.symm) x⟩ := rfl

omit [Finite α] in
variable {g} in
/-- Integer powers with equal casts act identically on the quotient output at an auxiliary index. -/
theorem zpow_smul_auxiliaryOut_eq_of_cast_eq {q : AuxiliaryIndex g} {a b : ℤ}
    (h : (a : ZMod (auxiliaryIndexValue g q)) =
      (b : ZMod (auxiliaryIndexValue g q))) :
    g ^ a • q.out = g ^ b • q.out := by
  rw [← MulAction.zpow_smul_mod_minimalPeriod g q.out a,
    ← MulAction.zpow_smul_mod_minimalPeriod g q.out b]
  exact congrArg (fun j : ℤ => g ^ j • q.out) ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)

omit [Finite α] in
/-- Applying the inverse auxiliary equivalence after the auxiliary permutation agrees with applying the original permutation afterward. -/
theorem auxiliaryEquiv_symm_apply_auxiliaryPermutation
    (s : CycleIndexSpace (AuxiliaryIndexedType g)) :
    (auxiliaryEquiv g).symm (cycleShift (AuxiliaryIndexedType g) s) =
      g • (auxiliaryEquiv g).symm s := by
  obtain ⟨m, ⟨q, h⟩, x⟩ := s
  subst h
  rw [cycleShift_apply, auxiliaryEquality, auxiliaryEquality]
  simp only [cast_eq, auxiliaryDefinition_symm_apply]
  rw [smul_smul, ← zpow_one_add]
  refine zpow_smul_auxiliaryOut_eq_of_cast_eq ?_
  push_cast
  rw [add_comm]

omit [Finite α] in
/-- The auxiliary equivalence intertwines the original permutation action with the displayed auxiliary permutation. -/
theorem auxiliaryEquiv_apply_perm (x : α) :
    auxiliaryEquiv g (g • x) =
      cycleShift (AuxiliaryIndexedType g) (auxiliaryEquiv g x) := by
  apply (auxiliaryEquiv g).symm.injective
  rw [_root_.Equiv.symm_apply_apply, auxiliaryEquiv_symm_apply_auxiliaryPermutation,
    _root_.Equiv.symm_apply_apply]

omit [Finite α] in
/-- Transporting a permutation through the auxiliary equivalence yields the displayed auxiliary permutation. -/
theorem permCongrHom_auxiliaryEquiv_apply :
    (auxiliaryEquiv g).permCongrHom g = cycleShift (AuxiliaryIndexedType g) := by
  refine _root_.Equiv.ext fun s => ?_
  change (auxiliaryEquiv g) (g ((auxiliaryEquiv g).symm s)) = _
  rw [← _root_.Equiv.Perm.smul_def, auxiliaryEquiv_apply_perm,
    _root_.Equiv.apply_symm_apply]

end Equiv.Perm

namespace Subgroup

/-- A multiplicative equivalence maps the centralizer of a singleton onto the centralizer of the image singleton. -/
theorem map_centralizer_singleton_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (a : G) :
    (_root_.Subgroup.centralizer {a}).map (e : G →* G') =
      _root_.Subgroup.centralizer {e a} := by
  ext x
  simp only [_root_.Subgroup.mem_map, _root_.Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

end Subgroup

namespace Equiv.Perm

variable {α : Type*} [Finite α] (g : _root_.Equiv.Perm α)

/-- The singleton centralizer of a permutation is multiplicatively equivalent to the singleton centralizer of the displayed auxiliary permutation. -/
noncomputable def centralizerMulEquivAuxiliaryPermutation :
    _root_.Subgroup.centralizer {g} ≃*
      _root_.Subgroup.centralizer {cycleShift (AuxiliaryIndexedType g)} :=
  ((auxiliaryEquiv g).permCongrHom.subgroupMap (_root_.Subgroup.centralizer {g})).trans
    (MulEquiv.subgroupCongr (by
      rw [_root_.RepresentationTheory.Permutation.CentralizerCycleFacts.Subgroup.map_centralizer_singleton_mulEquiv,
        permCongrHom_auxiliaryEquiv_apply]))

/-- The singleton centralizer of a finite permutation is multiplicatively equivalent to an indexed family of auxiliary groups. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := supporting)]
noncomputable def centralizerMulEquivAuxiliaryProduct :
    _root_.Subgroup.centralizer {g} ≃*
      ∀ m : ℕ, CentralizerFactor (AuxiliaryIndexedType g m) m :=
  (centralizerMulEquivAuxiliaryPermutation g).trans centralizerDataEquiv.symm

/-- An auxiliary natural-number-valued function of a permutation and an index. -/
noncomputable def auxiliaryNatValue (m : ℕ) : ℕ := Nat.card (AuxiliaryIndexedType g m)

/-- The singleton centralizer of a finite permutation is multiplicatively equivalent to a product of auxiliary groups on finite types. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := supporting)]
noncomputable def centralizerMulEquivFinAuxiliaryProduct :
    _root_.Subgroup.centralizer {g} ≃*
      ∀ m : ℕ, CentralizerFactor (Fin (auxiliaryNatValue g m)) m :=
  (centralizerMulEquivAuxiliaryProduct g).trans
    (MulEquiv.piCongrRight fun m => centralizerFactorCongr (Finite.equivFin _) m)

/-- Every auxiliary index value of a permutation of a finite type is at most the type's cardinality. -/
theorem auxiliaryIndexValue_le_card (q : AuxiliaryIndex g) :
    auxiliaryIndexValue g q ≤ Nat.card α := by
  have hinj : Function.Injective fun k : ZMod (auxiliaryIndexValue g q) =>
      (auxiliaryDefinition g).symm ⟨q, k⟩ :=
    (auxiliaryDefinition g).symm.injective.comp sigma_mk_injective
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

/-- An auxiliary indexed type is empty when its index exceeds the cardinality of the underlying finite type. -/
theorem isEmpty_auxiliaryIndexedType_of_card_lt {m : ℕ} (h : Nat.card α < m) :
    IsEmpty (AuxiliaryIndexedType g m) :=
  ⟨fun q => by
    have hq := auxiliaryIndexValue_le_card g q.val
    rw [q.property] at hq
    omega⟩

omit [Finite α] in
/-- An auxiliary index has value one exactly when the permutation fixes its quotient output. -/
theorem auxiliaryIndexValue_eq_one_iff_fixed (q : AuxiliaryIndex g) :
    auxiliaryIndexValue g q = 1 ↔ g q.out = q.out :=
  minimalPeriod_eq_one_iff_isFixedPt

omit [Finite α] in
/-- At a fixed point, taking a quotient output after the canonical quotient insertion returns that point. -/
theorem quotientOut_mk_eq_of_fixed {x : α} (hx : g x = x) :
    (Quotient.mk'' x : AuxiliaryIndex g).out = x := by
  have hmem : (Quotient.mk'' x : AuxiliaryIndex g).out ∈
      MulAction.orbit (_root_.Subgroup.zpowers g) x :=
    Quotient.mk_out (s := orbitRel (_root_.Subgroup.zpowers g) α) x
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨n, hn⟩ := c.property
  rw [← hc]
  change (c : _root_.Equiv.Perm α) x = x
  rw [← hn]
  exact _root_.Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx n

/-- The auxiliary indexed type at one is equivalent to the fixed-point type of the permutation. -/
noncomputable def auxiliaryIndexedTypeOneEquivFixedPoints :
    AuxiliaryIndexedType g 1 ≃ Function.fixedPoints (g : α → α) where
  toFun q := ⟨q.val.out, (auxiliaryIndexValue_eq_one_iff_fixed g q.val).mp q.property⟩
  invFun x := ⟨Quotient.mk'' x.val, by
    rw [auxiliaryIndexValue_eq_one_iff_fixed, quotientOut_mk_eq_of_fixed g x.property]
    exact x.property⟩
  left_inv q := Subtype.ext (Quotient.out_eq' q.val)
  right_inv x := Subtype.ext (quotientOut_mk_eq_of_fixed g x.property)

omit [Finite α] in
/-- At index one, the auxiliary value is the cardinality of the fixed-point type. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := primary)]
theorem auxiliaryNatValue_one_eq_card_fixedPoints :
    auxiliaryNatValue g 1 = Nat.card (Function.fixedPoints (g : α → α)) :=
  Nat.card_congr (auxiliaryIndexedTypeOneEquivFixedPoints g)

/-- The cardinality of a finite permutation's singleton centralizer is a product determined by its auxiliary natural values. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := supporting)]
theorem card_centralizer_eq_prod_auxiliaryNatValue :
    Nat.card (_root_.Subgroup.centralizer {g}) =
      ∏ m ∈ Finset.range (Nat.card α + 1),
        m ^ auxiliaryNatValue g m * Nat.factorial (auxiliaryNatValue g m) := by
  have hsub : ∀ m, Nat.card α < m →
      Subsingleton (CentralizerFactor (AuxiliaryIndexedType g m) m) := by
    intro m hm
    haveI := isEmpty_auxiliaryIndexedType_of_card_lt g hm
    infer_instance
  rw [Nat.card_congr (centralizerMulEquivAuxiliaryProduct g).toEquiv,
    Nat.card_congr (piEquivFin (Nat.card α) hsub), Nat.card_pi,
    ← Fin.prod_univ_eq_prod_range
      (fun m => m ^ auxiliaryNatValue g m * Nat.factorial (auxiliaryNatValue g m))
      (Nat.card α + 1)]
  exact Finset.prod_congr rfl fun m _ => card_centralizerFactor _ _

/-- The product formed from the auxiliary natural values agrees with the displayed expression in the cycle type. -/
theorem prod_auxiliaryNatValue_eq_cycleType_expression [Fintype α] [DecidableEq α] :
    ∏ m ∈ Finset.range (Fintype.card α + 1),
        m ^ auxiliaryNatValue g m * Nat.factorial (auxiliaryNatValue g m) =
      Nat.factorial (Fintype.card α - g.cycleType.sum) * g.cycleType.prod *
        ∏ n ∈ g.cycleType.toFinset, Nat.factorial (g.cycleType.count n) := by
  rw [← _root_.Equiv.Perm.nat_card_centralizer g,
    card_centralizer_eq_prod_auxiliaryNatValue g,
    Nat.card_eq_fintype_card]

section CycleType

open scoped Finset

variable {α : Type*} [Fintype α] [DecidableEq α] (g : _root_.Equiv.Perm α)

/-- For a moved point, its orbit under the powers subgroup is the support of the cycle through that point. -/
theorem orbit_zpowers_eq_support_cycleOf {x : α} (hx : g x ≠ x) :
    orbit (zpowers g) x = ↑(g.cycleOf x).support := by
  ext y
  rw [Finset.mem_coe, _root_.Equiv.Perm.mem_support_cycleOf_iff' hx]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨i, hi⟩ := c.property
    exact ⟨i, by rw [show g ^ i = (c : _root_.Equiv.Perm α) from hi]; exact hc⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨g ^ i, _root_.Subgroup.zpow_mem_zpowers g i⟩, hi⟩

/-- At a moved point, the minimal period of a permutation action is the support cardinality of the cycle through that point. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := supporting)]
theorem minimalPeriod_eq_card_support_cycleOf {x : α} (hx : g x ≠ x) :
    minimalPeriod (g • ·) x = #(g.cycleOf x).support := by
  have horb : Nat.card (orbit (zpowers g) x) = minimalPeriod (g • ·) x := by
    rw [Nat.card_congr (orbitZPowersEquiv g x), Nat.card_zmod]
  rw [← horb,
    Nat.card_congr (_root_.Equiv.setCongr (orbit_zpowers_eq_support_cycleOf g hx))]
  simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard]

variable {g}

/-- A non-one auxiliary index value equals the support cardinality of the cycle through the corresponding quotient output. -/
theorem auxiliaryIndexValue_eq_card_support_cycleOf_of_ne_one
    {q : AuxiliaryIndex g} (hq : auxiliaryIndexValue g q ≠ 1) :
    auxiliaryIndexValue g q = #(g.cycleOf q.out).support :=
  minimalPeriod_eq_card_support_cycleOf g
    fun h => hq ((auxiliaryIndexValue_eq_one_iff_fixed g q).mpr h)

omit [Fintype α] [DecidableEq α] in
/-- The quotient output at an auxiliary index is moved when its auxiliary value is not one. -/
theorem auxiliaryOut_ne_of_auxiliaryIndexValue_ne_one
    {q : AuxiliaryIndex g} (hq : auxiliaryIndexValue g q ≠ 1) : g q.out ≠ q.out :=
  fun h => hq ((auxiliaryIndexValue_eq_one_iff_fixed g q).mpr h)

variable (g)

/-- For an index at least two, the auxiliary indexed type is equivalent to the cycle factors whose supports have that cardinality. -/
noncomputable def auxiliaryIndexedTypeEquivCycleFactorsOfSupportCard {m : ℕ} (hm : 2 ≤ m) :
    AuxiliaryIndexedType g m ≃
      {c : _root_.Equiv.Perm α // c ∈ g.cycleFactorsFinset ∧ #c.support = m} := by
  have hne : ∀ q : AuxiliaryIndexedType g m, g q.val.out ≠ q.val.out := fun q =>
    auxiliaryOut_ne_of_auxiliaryIndexValue_ne_one (by rw [q.property]; omega)
  refine _root_.Equiv.ofBijective
    (fun q => ⟨g.cycleOf q.val.out,
      _root_.Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (_root_.Equiv.Perm.mem_support.mpr (hne q)),
      (auxiliaryIndexValue_eq_card_support_cycleOf_of_ne_one
        (by rw [q.property]; omega)).symm.trans q.property⟩)
    ⟨fun q₁ q₂ h => ?_, fun c => ?_⟩
  · have hsame : (g.SameCycle · ·) q₁.val.out q₂.val.out :=
      (_root_.Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        (_root_.Equiv.Perm.mem_support.mpr (hne q₁))
        (_root_.Equiv.Perm.mem_support.mpr (hne q₂))).mpr
        (Subtype.ext_iff.mp h)
    obtain ⟨i, hi⟩ := hsame.symm
    refine Subtype.ext ?_
    rw [← Quotient.out_eq' q₁.val, ← Quotient.out_eq' q₂.val]
    exact Quotient.sound' ⟨⟨g ^ i, _root_.Subgroup.zpow_mem_zpowers g i⟩, hi⟩
  · obtain ⟨c, hc, hcard⟩ := c
    obtain ⟨x, hx⟩ :=
      (_root_.Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    have hgx : g x ≠ x :=
      _root_.Equiv.Perm.mem_support.mp
        (_root_.Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx)
    set q : AuxiliaryIndex g := Quotient.mk'' x with hq
    obtain ⟨d, hd⟩ : q.out ∈ orbit (zpowers g) x :=
      Quotient.mk_out (s := orbitRel (zpowers g) α) x
    obtain ⟨i, hi⟩ := d.property
    have hsame : g.SameCycle x q.out :=
      ⟨i, by rw [show g ^ i = (d : _root_.Equiv.Perm α) from hi]; exact hd⟩
    have hcyc : g.cycleOf q.out = c := by
      rw [← hsame.cycleOf_eq, _root_.Equiv.Perm.cycle_is_cycleOf hx hc]
    have hout : g q.out ≠ q.out := fun h => hgx (hsame.apply_eq_self_iff.mpr h)
    have hlen : auxiliaryIndexValue g q = m := by
      rw [auxiliaryIndexValue_eq_card_support_cycleOf_of_ne_one
        (fun h => hout ((auxiliaryIndexValue_eq_one_iff_fixed g q).mp h)), hcyc, hcard]
    exact ⟨⟨q, hlen⟩, Subtype.ext hcyc⟩

/-- For an index at least two, the auxiliary value is the multiplicity of that index in the permutation's cycle type. -/
@[source_ref "Chapter5/Theorem5.14.3" (role := primary)]
theorem auxiliaryNatValue_eq_cycleType_count_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    auxiliaryNatValue g m = g.cycleType.count m := by
  classical
  rw [auxiliaryNatValue,
    Nat.card_congr (auxiliaryIndexedTypeEquivCycleFactorsOfSupportCard g hm),
    Nat.card_eq_fintype_card, Fintype.card_subtype, _root_.Equiv.Perm.cycleType_def,
    Multiset.count_map]
  have : (Finset.univ.filter fun c : _root_.Equiv.Perm α =>
      c ∈ g.cycleFactorsFinset ∧ #c.support = m) =
      g.cycleFactorsFinset.filter fun c =>
        m = (Finset.card ∘ _root_.Equiv.Perm.support) c := by
    ext c
    simp [eq_comm]
  rw [this, ← Finset.filter_val]
  rfl

omit [DecidableEq α] in
/-- The weighted sum of the auxiliary natural values is the cardinality of the finite underlying type. -/
theorem sum_mul_auxiliaryNatValue_eq_card :
    ∑ m ∈ Finset.range (Fintype.card α + 1),
      m * auxiliaryNatValue g m = Fintype.card α := by
  classical
  have hmaps : ∀ q : AuxiliaryIndex g,
      auxiliaryIndexValue g q ∈ Finset.range (Fintype.card α + 1) := fun q => by
    rw [Finset.mem_range, Nat.lt_succ_iff, ← Nat.card_eq_fintype_card]
    exact auxiliaryIndexValue_le_card g q
  haveI : ∀ q : AuxiliaryIndex g, NeZero (auxiliaryIndexValue g q) :=
    fun q => ⟨auxiliaryIndexValue_ne_zero q⟩
  have hsum : Fintype.card α = ∑ q : AuxiliaryIndex g, auxiliaryIndexValue g q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (auxiliaryDefinition g), Nat.card_sigma]
    exact Finset.sum_congr rfl fun q _ => Nat.card_zmod _
  refine Eq.trans ?_ hsum.symm
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun q _ => hmaps q) (fun q => auxiliaryIndexValue g q)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun q hq => (Finset.mem_filter.mp hq).2,
    Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [auxiliaryNatValue, Nat.card_eq_fintype_card, Fintype.card_subtype]

end CycleType

end Equiv.Perm

end RepresentationTheory.Permutation.CentralizerCycleFacts
