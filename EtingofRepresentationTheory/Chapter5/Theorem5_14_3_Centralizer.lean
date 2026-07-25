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

end Etingof
