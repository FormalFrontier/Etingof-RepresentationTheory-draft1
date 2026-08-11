import Mathlib
import EtingofRepresentationTheory.Infrastructure.WreathCentralizer

/-!
# The centralizer of a permutation (Theorem 5.14.3)

In the proof of Theorem 5.14.3 the book asserts that the centralizer `Z_g` of a permutation
`g` with `i_m` cycles of length `m` is

`∏_m S_{i_m} ⋉ (ℤ/mℤ)^{i_m}`,

and reads off `|Z_g| = ∏_m m^{i_m} i_m!` from it. This file formalizes that group isomorphism.

The cycles are the orbits of `g`, so fixed points are counted as cycles of length `1`; this is
the convention of the book (`i_1` is the number of fixed points), whereas Mathlib's
`Equiv.Perm.cycleType` lists only the cycles of length `≥ 2`.

## Main definitions

* `Etingof.CycleIdx g` : the set of cycles (= `g`-orbits) of `g`.
* `Etingof.cycleLen g q` : the length of the cycle `q`.
* `Etingof.CyclesOfLen g m` : the cycles of length `m`.
* `Etingof.cycleCount g m` : the number `i_m` of cycles of length `m`.

## Main results

* `Etingof.stdEquiv_smul` : `g` is conjugate to the standard shift on
  `Σ m, CyclesOfLen g m × ZMod m`.
* `Etingof.centralizerMulEquiv` :
  `centralizer {g} ≃* ∀ m, (CyclesOfLen g m → Multiplicative (ZMod m)) ⋊ Perm (CyclesOfLen g m)`.
* `Etingof.minimalPeriod_eq_card_support_cycleOf` : the length of the orbit of a non-fixed point
  is the size of the support of its `Equiv.Perm.cycleOf`.
* `Etingof.cycleCount_eq_cycleType_count` : `iₘ` is the multiplicity of `m` in
  `Equiv.Perm.cycleType g`, for every `m ≥ 2`.
-/

namespace Etingof

open Equiv Function Subgroup MulAction Wreath

variable {α : Type*} [Finite α] (g : Perm α)

/-- The cycles of a permutation: its orbits. Unlike `Equiv.Perm.cycleFactorsFinset` this counts
each fixed point as a cycle (of length `1`), as the book does. -/
abbrev CycleIdx : Type _ := orbitRel.Quotient (Subgroup.zpowers g) α

/-- The length of a cycle of `g`. -/
noncomputable def cycleLen (q : CycleIdx g) : ℕ := minimalPeriod (g • ·) q.out

variable {g} in
theorem cycleLen_ne_zero (q : CycleIdx g) : cycleLen g q ≠ 0 :=
  (MulAction.minimalPeriod_pos (a := g) (b := q.out)).ne

/-- The cycles of `g` of length `m`. -/
abbrev CyclesOfLen (m : ℕ) : Type _ := {q : CycleIdx g // cycleLen g q = m}

instance : IsEmpty (CyclesOfLen g 0) := ⟨fun q => cycleLen_ne_zero q.val q.property⟩

/-- The decomposition of `α` into the cycles of `g`, each cycle being a copy of `ZMod` of its
length. -/
noncomputable def cycleEquiv : α ≃ Σ q : CycleIdx g, ZMod (cycleLen g q) :=
  (selfEquivSigmaOrbits (Subgroup.zpowers g) α).trans
    (Equiv.sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

omit [Finite α] in
theorem cycleEquiv_symm_apply (q : CycleIdx g) (k : ZMod (cycleLen g q)) :
    (cycleEquiv g).symm ⟨q, k⟩ = g ^ (ZMod.cast k : ℤ) • q.out := rfl

/-- Grouping the cycles of `g` by length. -/
noncomputable def stdEquiv : α ≃ Std (CyclesOfLen g) :=
  (cycleEquiv g).trans
    { toFun := fun p => ⟨cycleLen g p.1, (⟨p.1, rfl⟩, p.2)⟩
      invFun := fun s => ⟨s.2.1.val, cast (congrArg ZMod s.2.1.property.symm) s.2.2⟩
      left_inv := fun p => by simp
      right_inv := fun s => by
        obtain ⟨m, ⟨q, h⟩, x⟩ := s
        subst h
        simp }

omit [Finite α] in
theorem stdEquiv_symm_apply (m : ℕ) (q : CyclesOfLen g m) (x : ZMod m) :
    (stdEquiv g).symm ⟨m, (q, x)⟩ =
      (cycleEquiv g).symm ⟨q.val, cast (congrArg ZMod q.property.symm) x⟩ := rfl

omit [Finite α] in
variable {g} in
/-- Two integer powers of `g` agree on a point of the cycle `q` as soon as they agree modulo
the length of `q`. -/
theorem zpow_smul_out_congr {q : CycleIdx g} {a b : ℤ}
    (h : (a : ZMod (cycleLen g q)) = (b : ZMod (cycleLen g q))) :
    g ^ a • q.out = g ^ b • q.out := by
  rw [← MulAction.zpow_smul_mod_minimalPeriod g q.out a,
    ← MulAction.zpow_smul_mod_minimalPeriod g q.out b]
  exact congrArg (fun j : ℤ => g ^ j • q.out) ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)

omit [Finite α] in
/-- `g` is carried to the standard shift by `stdEquiv`. -/
theorem stdEquiv_symm_stdShift (s : Std (CyclesOfLen g)) :
    (stdEquiv g).symm (stdShift (CyclesOfLen g) s) = g • (stdEquiv g).symm s := by
  obtain ⟨m, ⟨q, h⟩, x⟩ := s
  subst h
  rw [stdShift_apply, stdEquiv_symm_apply, stdEquiv_symm_apply]
  simp only [cast_eq, cycleEquiv_symm_apply]
  rw [smul_smul, ← zpow_one_add]
  refine zpow_smul_out_congr ?_
  push_cast
  rw [add_comm]

omit [Finite α] in
theorem stdEquiv_smul (x : α) :
    stdEquiv g (g • x) = stdShift (CyclesOfLen g) (stdEquiv g x) := by
  apply (stdEquiv g).symm.injective
  rw [Equiv.symm_apply_apply, stdEquiv_symm_stdShift, Equiv.symm_apply_apply]

omit [Finite α] in
/-- The standard shift is the image of `g` under conjugation by `stdEquiv`. -/
theorem permCongrHom_stdEquiv : (stdEquiv g).permCongrHom g = stdShift (CyclesOfLen g) := by
  refine Equiv.ext fun s => ?_
  change (stdEquiv g) (g ((stdEquiv g).symm s)) = _
  rw [← Perm.smul_def, stdEquiv_smul, Equiv.apply_symm_apply]

/-- A group isomorphism carries the centralizer of an element to the centralizer of its image. -/
theorem map_centralizer_singleton {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (a : G) :
    (centralizer {a}).map (e : G →* G') = centralizer {e a} := by
  ext x
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MonoidHom.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

/-- Conjugating by `stdEquiv` identifies the centralizer of `g` with the centralizer of the
standard shift. -/
noncomputable def centralizerMulEquivStd :
    centralizer {g} ≃* centralizer {stdShift (CyclesOfLen g)} :=
  ((stdEquiv g).permCongrHom.subgroupMap (centralizer {g})).trans
    (MulEquiv.subgroupCongr (by
      rw [map_centralizer_singleton, permCongrHom_stdEquiv]))

/-- **The centralizer of a permutation is the product of its wreath blocks.**

This is the isomorphism `Z_g ≅ ∏ₘ S_{iₘ} ⋉ (ℤ/mℤ)^{iₘ}` displayed in the proof of
Theorem 5.14.3, with `S_{iₘ}` realised as the permutations of the set `CyclesOfLen g m` of
length-`m` cycles of `g`. Fixed points are the cycles of length `1`, and the factors with
`CyclesOfLen g m` empty are trivial. -/
noncomputable def centralizerMulEquiv :
    centralizer {g} ≃* ∀ m : ℕ, WreathBlock (CyclesOfLen g m) m :=
  (centralizerMulEquivStd g).trans stdCentralizerMulEquiv.symm

/-- The number `iₘ` of cycles of `g` of length `m`, counting fixed points as cycles of
length `1`. -/
noncomputable def cycleCount (m : ℕ) : ℕ := Nat.card (CyclesOfLen g m)

/-- **The centralizer of a permutation**, with the cycles of each length indexed by
`Fin iₘ`: `Z_g ≅ ∏ₘ (ℤ/mℤ)^{iₘ} ⋊ S_{iₘ}`. -/
noncomputable def centralizerMulEquivFin :
    centralizer {g} ≃* ∀ m : ℕ, WreathBlock (Fin (cycleCount g m)) m :=
  (centralizerMulEquiv g).trans
    (MulEquiv.piCongrRight fun m => wreathBlockCongr (Finite.equivFin _) m)

/-! ### The order of the centralizer

`|Z_g| = ∏ₘ m^{iₘ} iₘ!`, the formula the book reads off from the displayed isomorphism.
-/

theorem cycleLen_le (q : CycleIdx g) : cycleLen g q ≤ Nat.card α := by
  have hinj : Function.Injective fun k : ZMod (cycleLen g q) => (cycleEquiv g).symm ⟨q, k⟩ :=
    (cycleEquiv g).symm.injective.comp sigma_mk_injective
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem isEmpty_cyclesOfLen {m : ℕ} (h : Nat.card α < m) : IsEmpty (CyclesOfLen g m) :=
  ⟨fun q => by
    have hq := cycleLen_le g q.val
    rw [q.property] at hq
    omega⟩

omit [Finite α] in
/-- A cycle has length `1` exactly when its representative is a fixed point. -/
theorem cycleLen_eq_one_iff (q : CycleIdx g) : cycleLen g q = 1 ↔ g q.out = q.out :=
  minimalPeriod_eq_one_iff_isFixedPt

omit [Finite α] in
/-- The chosen representative of the orbit of a fixed point is that fixed point. -/
theorem out_mk_of_fixed {x : α} (hx : g x = x) : (Quotient.mk'' x : CycleIdx g).out = x := by
  have hmem : (Quotient.mk'' x : CycleIdx g).out ∈ MulAction.orbit (Subgroup.zpowers g) x :=
    Quotient.mk_out (s := orbitRel (Subgroup.zpowers g) α) x
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨n, hn⟩ := c.property
  rw [← hc]
  change (c : Perm α) x = x
  rw [← hn]
  exact Perm.zpow_apply_eq_self_of_apply_eq_self hx n

/-- The cycles of length `1` are the fixed points: `i₁` is the number of fixed points of `g`,
which is what makes `cycleCount` the *full* cycle count (Mathlib's `Equiv.Perm.cycleType`
omits the length-`1` cycles). -/
noncomputable def cyclesOfLenOneEquiv : CyclesOfLen g 1 ≃ Function.fixedPoints (g : α → α) where
  toFun q := ⟨q.val.out, (cycleLen_eq_one_iff g q.val).mp q.property⟩
  invFun x := ⟨Quotient.mk'' x.val, by
    rw [cycleLen_eq_one_iff, out_mk_of_fixed g x.property]
    exact x.property⟩
  left_inv q := Subtype.ext (Quotient.out_eq' q.val)
  right_inv x := Subtype.ext (out_mk_of_fixed g x.property)

omit [Finite α] in
/-- `i₁` is the number of fixed points. -/
theorem cycleCount_one : cycleCount g 1 = Nat.card (Function.fixedPoints (g : α → α)) :=
  Nat.card_congr (cyclesOfLenOneEquiv g)

/-- **The order of the centralizer**: `|Z_g| = ∏ₘ m^{iₘ} iₘ!`. -/
theorem nat_card_centralizer_eq_prod :
    Nat.card (centralizer {g}) =
      ∏ m ∈ Finset.range (Nat.card α + 1),
        m ^ cycleCount g m * Nat.factorial (cycleCount g m) := by
  have hsub : ∀ m, Nat.card α < m → Subsingleton (WreathBlock (CyclesOfLen g m) m) := by
    intro m hm
    haveI := isEmpty_cyclesOfLen g hm
    infer_instance
  rw [Nat.card_congr (centralizerMulEquiv g).toEquiv,
    Nat.card_congr (piTruncEquiv (Nat.card α) hsub), Nat.card_pi,
    ← Fin.prod_univ_eq_prod_range
      (fun m => m ^ cycleCount g m * Nat.factorial (cycleCount g m)) (Nat.card α + 1)]
  exact Finset.prod_congr rfl fun m _ => nat_card_wreathBlock _ _

/-- The order formula of the book agrees with Mathlib's `Equiv.Perm.nat_card_centralizer`,
which is expressed through `Equiv.Perm.cycleType` (so with the fixed points split off). -/
theorem prod_cycleCount_eq_cycleType_formula [Fintype α] [DecidableEq α] :
    ∏ m ∈ Finset.range (Fintype.card α + 1),
        m ^ cycleCount g m * Nat.factorial (cycleCount g m) =
      Nat.factorial (Fintype.card α - g.cycleType.sum) * g.cycleType.prod *
        ∏ n ∈ g.cycleType.toFinset, Nat.factorial (g.cycleType.count n) := by
  rw [← Equiv.Perm.nat_card_centralizer g, nat_card_centralizer_eq_prod g,
    Nat.card_eq_fintype_card]

/-! ### Comparison with `Equiv.Perm.cycleType`, length by length

The previous theorem reconciles the book's cycle counts with Mathlib's `Equiv.Perm.cycleType`
only *in aggregate*, through the order of the centralizer. This section identifies the two
notions of cycle themselves: a cycle of `g` in the sense used here is a `g`-orbit, whereas
Mathlib's `Equiv.Perm.cycleFactorsFinset` lists the nontrivial cyclic factors of `g`. The two
agree in every length `m ≥ 2` (`cycleCount_eq_cycleType_count`); the length-`1` cycles are the
fixed points, which `cycleType` omits and `cycleCount_one` counts.

The link is `minimalPeriod_eq_card_support_cycleOf`, which says that the length of the orbit of
a non-fixed point `x` is the size of the support of `Equiv.Perm.cycleOf g x`. Mathlib does not
have this: `Mathlib/GroupTheory/Perm/Cycle/*.lean` never mentions `Function.minimalPeriod`.
-/

section CycleType

open scoped Finset

variable {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α)

/-- The `⟨g⟩`-orbit of a non-fixed point `x` is the support of the cycle of `g` through `x`.
This is the set-level form of the identification of the two notions of "cycle". -/
theorem orbit_zpowers_eq_support_cycleOf {x : α} (hx : g x ≠ x) :
    orbit (zpowers g) x = ↑(g.cycleOf x).support := by
  ext y
  rw [Finset.mem_coe, Equiv.Perm.mem_support_cycleOf_iff' hx]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨i, hi⟩ := c.property
    exact ⟨i, by rw [show g ^ i = (c : Perm α) from hi]; exact hc⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨g ^ i, Subgroup.zpow_mem_zpowers g i⟩, hi⟩

/-- **The length of an orbit is the size of the corresponding cycle's support.**

For a point `x` that `g` does not fix, the minimal period of `x` under `g` equals
`#(g.cycleOf x).support`. This is the bridge between the orbit description of cycles used in
this file and Mathlib's `Equiv.Perm.cycleOf` / `Equiv.Perm.cycleType`. -/
theorem minimalPeriod_eq_card_support_cycleOf {x : α} (hx : g x ≠ x) :
    minimalPeriod (g • ·) x = #(g.cycleOf x).support := by
  have horb : Nat.card (orbit (zpowers g) x) = minimalPeriod (g • ·) x := by
    rw [Nat.card_congr (orbitZPowersEquiv g x), Nat.card_zmod]
  rw [← horb, Nat.card_congr (Equiv.setCongr (orbit_zpowers_eq_support_cycleOf g hx))]
  simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard]

variable {g}

/-- A cycle of length `≠ 1` is a cycle in Mathlib's sense too, of the same length. -/
theorem cycleLen_eq_card_support_cycleOf {q : CycleIdx g} (hq : cycleLen g q ≠ 1) :
    cycleLen g q = #(g.cycleOf q.out).support :=
  minimalPeriod_eq_card_support_cycleOf g fun h => hq ((cycleLen_eq_one_iff g q).mpr h)

omit [Fintype α] [DecidableEq α] in
/-- The chosen representative of a cycle of length `≠ 1` is not a fixed point. -/
theorem apply_out_ne_self {q : CycleIdx g} (hq : cycleLen g q ≠ 1) : g q.out ≠ q.out :=
  fun h => hq ((cycleLen_eq_one_iff g q).mpr h)

variable (g)

/-- **The cycles of length `m ≥ 2` are exactly Mathlib's cyclic factors with support of size
`m`.** The map sends an orbit to the cycle of `g` through any of its points. -/
noncomputable def cyclesOfLenEquivCycleFactors {m : ℕ} (hm : 2 ≤ m) :
    CyclesOfLen g m ≃ {c : Perm α // c ∈ g.cycleFactorsFinset ∧ #c.support = m} := by
  have hne : ∀ q : CyclesOfLen g m, g q.val.out ≠ q.val.out := fun q =>
    apply_out_ne_self (by rw [q.property]; omega)
  refine Equiv.ofBijective
    (fun q => ⟨g.cycleOf q.val.out,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr (hne q)),
      (cycleLen_eq_card_support_cycleOf (by rw [q.property]; omega)).symm.trans q.property⟩)
    ⟨fun q₁ q₂ h => ?_, fun c => ?_⟩
  · -- Injectivity: equal cycles means the representatives lie in the same orbit.
    have hsame : (g.SameCycle · ·) q₁.val.out q₂.val.out :=
      (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        (Equiv.Perm.mem_support.mpr (hne q₁)) (Equiv.Perm.mem_support.mpr (hne q₂))).mpr
        (Subtype.ext_iff.mp h)
    obtain ⟨i, hi⟩ := hsame.symm
    refine Subtype.ext ?_
    rw [← Quotient.out_eq' q₁.val, ← Quotient.out_eq' q₂.val]
    exact Quotient.sound' ⟨⟨g ^ i, Subgroup.zpow_mem_zpowers g i⟩, hi⟩
  · -- Surjectivity: every cyclic factor is the cycle through a point of its support.
    obtain ⟨c, hc, hcard⟩ := c
    obtain ⟨x, hx⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    have hgx : g x ≠ x :=
      Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx)
    -- `q` is the orbit of `x`; its chosen representative lies in the same orbit.
    set q : CycleIdx g := Quotient.mk'' x with hq
    obtain ⟨d, hd⟩ : q.out ∈ orbit (zpowers g) x :=
      Quotient.mk_out (s := orbitRel (zpowers g) α) x
    obtain ⟨i, hi⟩ := d.property
    have hsame : g.SameCycle x q.out := ⟨i, by rw [show g ^ i = (d : Perm α) from hi]; exact hd⟩
    have hcyc : g.cycleOf q.out = c := by
      rw [← hsame.cycleOf_eq, Equiv.Perm.cycle_is_cycleOf hx hc]
    have hout : g q.out ≠ q.out := fun h => hgx (hsame.apply_eq_self_iff.mpr h)
    have hlen : cycleLen g q = m := by
      rw [cycleLen_eq_card_support_cycleOf fun h => hout ((cycleLen_eq_one_iff g q).mp h),
        hcyc, hcard]
    exact ⟨⟨q, hlen⟩, Subtype.ext hcyc⟩

/-- **The book's cycle count agrees with Mathlib's `cycleType`, length by length.**

For `m ≥ 2`, the number `iₘ` of cycles of `g` of length `m` is the multiplicity of `m` in
`Equiv.Perm.cycleType g`. (For `m = 1` the two disagree: `cycleCount g 1` is the number of
fixed points, while `cycleType` omits them; see `cycleCount_one`.) -/
theorem cycleCount_eq_cycleType_count {m : ℕ} (hm : 2 ≤ m) :
    cycleCount g m = g.cycleType.count m := by
  classical
  rw [cycleCount, Nat.card_congr (cyclesOfLenEquivCycleFactors g hm), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Equiv.Perm.cycleType_def, Multiset.count_map]
  have : (Finset.univ.filter fun c : Perm α => c ∈ g.cycleFactorsFinset ∧ #c.support = m) =
      g.cycleFactorsFinset.filter fun c => m = (Finset.card ∘ Equiv.Perm.support) c := by
    ext c
    simp [eq_comm]
  rw [this, ← Finset.filter_val]
  rfl

omit [DecidableEq α] in
/-- The lengths of the cycles of `g` add up to the size of the underlying set:
`∑ₘ m · iₘ = |α|`. -/
theorem sum_cycleCount_mul_eq_card :
    ∑ m ∈ Finset.range (Fintype.card α + 1), m * cycleCount g m = Fintype.card α := by
  classical
  have hmaps : ∀ q : CycleIdx g, cycleLen g q ∈ Finset.range (Fintype.card α + 1) := fun q => by
    rw [Finset.mem_range, Nat.lt_succ_iff, ← Nat.card_eq_fintype_card]
    exact cycleLen_le g q
  haveI : ∀ q : CycleIdx g, NeZero (cycleLen g q) := fun q => ⟨cycleLen_ne_zero q⟩
  have hsum : Fintype.card α = ∑ q : CycleIdx g, cycleLen g q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (cycleEquiv g), Nat.card_sigma]
    exact Finset.sum_congr rfl fun q _ => Nat.card_zmod _
  refine Eq.trans ?_ hsum.symm
  rw [← Finset.sum_fiberwise_of_maps_to (fun q _ => hmaps q) (fun q => cycleLen g q)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun q hq => (Finset.mem_filter.mp hq).2, Finset.sum_const,
    smul_eq_mul, mul_comm]
  congr 1
  rw [cycleCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

end CycleType

end Etingof
