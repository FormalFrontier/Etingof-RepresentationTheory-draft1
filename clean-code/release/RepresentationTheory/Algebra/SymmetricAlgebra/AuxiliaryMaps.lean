/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis
import Mathlib.Data.Finsupp.Order

set_option backward.isDefEq.respectTransparency false

universe u v w

open scoped TensorProduct

namespace RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

section Exponent

variable {κ : Type w}

/-- If a coefficient is at least one, subtracting and then adding its unit singleton recovers the finitely supported function. -/
theorem Finsupp.sub_single_add_single {α : κ →₀ ℕ} {a : κ} (h : 1 ≤ α a) :
    α - Finsupp.single a 1 + Finsupp.single a 1 = α := by
  ext x
  rcases eq_or_ne a x with rfl | hne
  · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · have h0 : (Finsupp.single a (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Under positivity at the subtracted index, adding one singleton commutes with subtracting another singleton. -/
theorem Finsupp.sub_single_add_single_comm {α : κ →₀ ℕ} {p a : κ} (h : 1 ≤ α p) :
    α - Finsupp.single p 1 + Finsupp.single a 1 =
      α + Finsupp.single a 1 - Finsupp.single p 1 := by
  ext x
  rcases eq_or_ne p x with rfl | hne
  · rcases eq_or_ne a p with rfl | hne'
    · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single a (1 : ℕ)) p = 0 := Finsupp.single_eq_of_ne hne'.symm
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
  · have h0 : (Finsupp.single p (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Adding and then subtracting the same unit singleton leaves a natural-valued finitely supported function unchanged. -/
theorem Finsupp.add_single_sub_single {α : κ →₀ ℕ} {a : κ} :
    α + Finsupp.single a 1 - Finsupp.single a 1 = α := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

/-- An index belongs to the support after adding a unit singleton exactly when it is the singleton index or belonged to the original support. -/
theorem Finsupp.mem_support_add_single {α : κ →₀ ℕ} {a m : κ} :
    m ∈ (α + Finsupp.single a 1).support ↔ m = a ∨ m ∈ α.support := by
  rcases eq_or_ne m a with rfl | hne
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply]
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne]

end Exponent

section Insert

variable {κ : Type w} [DecidableEq κ]

/-- Adjoin an absent element to a subset of fixed finite cardinality, producing a subset whose cardinality is one larger. -/
def Set.PowersetCard.insert {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    Set.powersetCard κ (i + 1) :=
  ⟨Insert.insert a (s : Finset κ), Set.powersetCard.mem_iff.mpr (by
    rw [Finset.card_insert_of_notMem ha, Set.powersetCard.card_eq])⟩

/-- The underlying set obtained by adjoining a fresh element to a fixed-cardinality subset is its set insertion. -/
@[simp]
theorem Set.PowersetCard.coe_insert {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    (Set.PowersetCard.insert s ha : Finset κ) = Insert.insert a (s : Finset κ) := rfl

end Insert

section Position

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- Under the displayed order hypothesis, the shown natural-valued function has value zero at the inserted element. -/
theorem Finset.auxiliaryNatFunction_insert_self_of_lt {s : Finset κ} {p : κ} (hp : ∀ c ∈ s, p < c) :
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (insert p s) p = 0 := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_irrefl _
  · exact not_lt.mpr (hp x hx).le

/-- Under the displayed order hypothesis, the shown natural-valued function increases by one on each original member after insertion. -/
theorem Finset.auxiliaryNatFunction_insert_of_lt {s : Finset κ} {p c : κ} (hp : ∀ c' ∈ s, p < c') (hc : c ∈ s) :
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (insert p s) c = _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank s c + 1 := by
  have hpn : p ∉ s := fun h => absurd (hp p h) (lt_irrefl p)
  have hfil : (insert p s).filter (· < c) = insert p (s.filter (· < c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx | hx, hlt⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hx, hlt⟩
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨Or.inl rfl, hp c hc⟩
      · exact ⟨Or.inr hx, hlt⟩
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, hfil, Finset.card_insert_of_notMem fun h => hpn (Finset.mem_filter.mp h).1,
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank]

omit [DecidableEq κ] in

/-- The shown natural-valued function has value zero at the minimum of a nonempty finite set. -/
theorem Finset.auxiliaryNatFunction_min' {s : Finset κ} (h : s.Nonempty) : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank s (s.min' h) = 0 := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x hx => not_lt.mpr (s.min'_le x hx)

end Position

section Pivot

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- A predicate on a finitely supported natural-valued function, a finite set, and an index. -/
def Finsupp.IndexPredicate (α : κ →₀ ℕ) (s : Finset κ) (a : κ) : Prop :=
  a ∈ α.support ∧ (∀ m ∈ α.support, a ≤ m) ∧ ∀ c ∈ s, a < c

/-- The displayed predicate for a natural-valued finitely supported function and finite set is decidable. -/
instance Finsupp.decidablePredIndexPredicate (α : κ →₀ ℕ) (s : Finset κ) : DecidablePred (Finsupp.IndexPredicate α s) := fun a => by
  unfold Finsupp.IndexPredicate; infer_instance

omit [DecidableEq κ] in
/-- An index satisfying the predicate lies outside the given finite set. -/
theorem Finsupp.IndexPredicate.not_mem {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : Finsupp.IndexPredicate α s a) :
    a ∉ s := fun ha => absurd (h.2.2 a ha) (lt_irrefl a)

omit [DecidableEq κ] in

/-- Any two indices satisfying the predicate for the same function and finite set are equal. -/
theorem Finsupp.IndexPredicate.eq {α : κ →₀ ℕ} {s : Finset κ} {a a' : κ} (h : Finsupp.IndexPredicate α s a)
    (h' : Finsupp.IndexPredicate α s a') : a = a' :=
  le_antisymm (h.2.1 a' h'.1) (h'.2.1 a h.1)

omit [DecidableEq κ] in
/-- The coefficient at an index satisfying the predicate is at least one. -/
theorem Finsupp.IndexPredicate.one_le {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : Finsupp.IndexPredicate α s a) :
    1 ≤ α a :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h.1)

end Pivot

section Homotopy

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- A basis-dependent value in the displayed module at a successor index, determined by a finitely supported function and fixed-cardinality subset. -/
noncomputable def Module.Basis.pairToSucc (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1) :=
  ∑ a ∈ P.1.support,
    if h : Finsupp.IndexPredicate P.1 (P.2 : Finset κ) a then
      -_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (P.1 - Finsupp.single a 1, Set.PowersetCard.insert P.2 h.not_mem)
    else 0

/-- When an index satisfies the predicate, the displayed basis-dependent value is the negation of the shown successor-index value. -/
theorem Module.Basis.pairToSucc_eq_neg (b : Module.Basis κ k V) {i : ℕ} (α : κ →₀ ℕ)
    (s : Set.powersetCard κ i) {a : κ} (h : Finsupp.IndexPredicate α (s : Finset κ) a) :
    Module.Basis.pairToSucc b i (α, s) =
      -_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α - Finsupp.single a 1, Set.PowersetCard.insert s h.not_mem) := by
  rw [Module.Basis.pairToSucc,
    Finset.sum_eq_single_of_mem a h.1 fun c _ hc => dif_neg fun h' => hc (h'.eq h),
    dif_pos h]

/-- The displayed basis-dependent value is zero when no index satisfies the predicate. -/
theorem Module.Basis.pairToSucc_eq_zero (b : Module.Basis κ k V) {i : ℕ} (α : κ →₀ ℕ)
    (s : Set.powersetCard κ i) (h : ∀ a, ¬Finsupp.IndexPredicate α (s : Finset κ) a) :
    Module.Basis.pairToSucc b i (α, s) = 0 :=
  Finset.sum_eq_zero fun a _ => dif_neg (h a)

/-- A basis-dependent linear map from the displayed module at an index to the displayed module at its successor. -/
noncomputable def Module.Basis.linearMapToSucc (b : Module.Basis κ k V) (i : ℕ) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[k] _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1) :=
  (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i).constr k (Module.Basis.pairToSucc b i)

/-- The displayed linear map applied to the given pair equals the displayed basis-dependent value. -/
@[simp]
theorem Module.Basis.linearMapToSucc_apply_pair (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) :
    Module.Basis.linearMapToSucc b i (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i P) = Module.Basis.pairToSucc b i P :=
  Module.Basis.constr_basis _ _ _ _

/-- The scalar actions of the base ring and its symmetric algebra on the displayed third module form a scalar tower. -/
instance instIsScalarTowerSymmetricAlgebraAuxiliary : IsScalarTower k (SymmetricAlgebra k V) (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) where
  smul_assoc c s x := by
    apply (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
    have h1 : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V ((c • s) • x) =
        SymmetricAlgebra.algebraMapInv (c • s) * _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V x :=
      _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul _ _
    have h2 : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V (c • (s • x)) =
        c • _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V (s • x) := map_smul _ _ _
    rw [h1, h2, _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

variable (k V) in

/-- A linear map from the displayed source module to the displayed module at index zero. -/
noncomputable def auxiliaryLinearMapToIndexZero : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V →ₗ[k] _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V 0 :=
  ((TensorProduct.mk k (SymmetricAlgebra k V) (⋀[k]^0 V)).flip
      ((exteriorPower.zeroEquiv k V).symm 1)).comp
    ((Algebra.linearMap k (SymmetricAlgebra k V)).comp
      (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).toLinearMap)

/-- The linear map sends an element to the displayed tensor of its image with the displayed inverse-equivalence value. -/
theorem auxiliaryLinearMapToIndexZero_apply (c : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) :
    auxiliaryLinearMapToIndexZero k V c =
      algebraMap k (SymmetricAlgebra k V) (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V c) ⊗ₜ[k]
        (exteriorPower.zeroEquiv k V).symm 1 :=
  rfl

/-- The displayed composite of two maps fixes every element of the displayed source type. -/
theorem auxiliaryMap_leftInverse (c : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) :
    _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V (auxiliaryLinearMapToIndexZero k V c) = c := by
  apply (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
  rw [auxiliaryLinearMapToIndexZero_apply, _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.equivBaseRing_tensorToDegreeZero_tmul]
  simp

/-- An auxiliary value determined by a basis, an index, a finitely supported function, a fixed-cardinality subset, and an element. -/
noncomputable def Module.Basis.auxiliaryTerm (b : Module.Basis κ k V) (i : ℕ) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ (i + 1)) (a : κ) : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i :=
  if h : a ∈ (s : Finset κ) then
    ((-1 : k) ^ (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (s : Finset κ) a + 1)) •
      _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i (α + Finsupp.single a 1, _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, h⟩)
  else 0

variable [Fintype κ]

/-- The displayed map applied to the displayed auxiliary value is a finite sum of the associated terms. -/
theorem Module.Basis.auxiliaryMap_apply_auxiliary_eq_sum (b : Module.Basis κ k V) (i : ℕ) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ (i + 1)) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s)) =
      ∑ a ∈ (s : Finset κ), Module.Basis.auxiliaryTerm b i α s a := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_reindex, ← Finset.sum_attach (s := (s : Finset κ)) (Module.Basis.auxiliaryTerm b i α s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Module.Basis.auxiliaryTerm, dif_pos a.2]

/-- The successor-index composite identity holds on the displayed auxiliary value. -/
theorem Module.Basis.succComposite_add_prevComposite_eq_id_apply_auxiliary (b : Module.Basis κ k V) (i : ℕ)
    (α : κ →₀ ℕ) (s : Set.powersetCard κ (i + 1)) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b (i + 1) (Module.Basis.linearMapToSucc b (i + 1) (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s))) +
        Module.Basis.linearMapToSucc b i (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s))) =
      _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s) := by
  have hne : (s : Finset κ).Nonempty := by
    rw [← Finset.card_pos, Set.powersetCard.card_eq]; omega
  rw [Module.Basis.linearMapToSucc_apply_pair, Module.Basis.auxiliaryMap_apply_auxiliary_eq_sum b i α s, map_sum]
  by_cases hpiv : ∃ p, Finsupp.IndexPredicate α (s : Finset κ) p
  · -- **Case A.** A pivot `p` exists; `p` is below every element of `s`, so `h` is nonzero on
    -- `x^α ⊗ e_s` and the `a = p` term of `d h` reproduces `x^α ⊗ e_s` while the remaining
    -- terms cancel against `h d` one by one.
    obtain ⟨p, hp⟩ := hpiv
    rw [Module.Basis.pairToSucc_eq_neg b α s hp, map_neg,
      Module.Basis.auxiliaryMap_apply_auxiliary_eq_sum b (i + 1) (α - Finsupp.single p 1) (Set.PowersetCard.insert s hp.not_mem),
      Set.PowersetCard.coe_insert, Finset.sum_insert hp.not_mem]
    have hpt : p ∈ (Set.PowersetCard.insert s hp.not_mem : Finset κ) := by
      rw [Set.PowersetCard.coe_insert]; exact Finset.mem_insert_self _ _
    have h1 : Module.Basis.auxiliaryTerm b (i + 1) (α - Finsupp.single p 1) (Set.PowersetCard.insert s hp.not_mem) p =
        -_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (α, s) := by
      have hpos : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (Set.PowersetCard.insert s hp.not_mem : Finset κ) p = 0 :=
        Finset.auxiliaryNatFunction_insert_self_of_lt hp.2.2
      have herase : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase (Set.PowersetCard.insert s hp.not_mem) ⟨p, hpt⟩ = s :=
        Subtype.ext (Finset.erase_insert hp.not_mem)
      rw [Module.Basis.auxiliaryTerm, dif_pos hpt, hpos, Finsupp.sub_single_add_single hp.one_le, herase]
      rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_apply, pow_one]
      change (((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k]
          (Module.Basis.exteriorPower (i + 1) b) s :
          SymmetricAlgebra k V ⊗[k] (⋀[k]^(i + 1) V)) =
        (-b.symmetricAlgebra α) ⊗ₜ[k] (Module.Basis.exteriorPower (i + 1) b) s
      set_option backward.isDefEq.respectTransparency true in
        simpa only [TensorProduct.neg_tmul] using
          congrArg (fun z : SymmetricAlgebra k V =>
            z ⊗ₜ[k] (Module.Basis.exteriorPower (i + 1) b) s)
            (neg_one_smul k (b.symmetricAlgebra α))
    have h2 : ∀ a ∈ (s : Finset κ), Module.Basis.linearMapToSucc b i (Module.Basis.auxiliaryTerm b i α s a) =
        Module.Basis.auxiliaryTerm b (i + 1) (α - Finsupp.single p 1) (Set.PowersetCard.insert s hp.not_mem) a := by
      intro a ha
      have hpa : p < a := hp.2.2 a ha
      have hat : a ∈ (Set.PowersetCard.insert s hp.not_mem : Finset κ) := by
        rw [Set.PowersetCard.coe_insert]; exact Finset.mem_insert_of_mem ha
      -- `p` is still the pivot after `d` has moved `xₐ` into the monomial and deleted `a` from `s`.
      have hpiv2 : Finsupp.IndexPredicate (α + Finsupp.single a 1)
          ((_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, ha⟩ : Finset κ)) p := by
        refine ⟨Finsupp.mem_support_add_single.mpr (Or.inr hp.1), fun m hm => ?_, fun c hc => ?_⟩
        · rcases Finsupp.mem_support_add_single.mp hm with rfl | hm
          · exact hpa.le
          · exact hp.2.1 m hm
        · rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase_val] at hc
          exact hp.2.2 c (Finset.mem_of_mem_erase hc)
      have hset : Set.PowersetCard.insert (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, ha⟩) hpiv2.not_mem =
          _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase (Set.PowersetCard.insert s hp.not_mem) ⟨a, hat⟩ :=
        Subtype.ext (Finset.erase_insert_of_ne (ne_of_lt hpa)).symm
      have hpos2 : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (Set.PowersetCard.insert s hp.not_mem : Finset κ) a =
          _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (s : Finset κ) a + 1 := Finset.auxiliaryNatFunction_insert_of_lt hp.2.2 ha
      rw [Module.Basis.auxiliaryTerm, dif_pos ha, map_smul, Module.Basis.linearMapToSucc_apply_pair,
        Module.Basis.pairToSucc_eq_neg b _ _ hpiv2, Module.Basis.auxiliaryTerm, dif_pos hat, hpos2,
        ← Finsupp.sub_single_add_single_comm hp.one_le, hset, smul_neg, ← neg_smul]
      congr 1
      ring
    rw [h1, Finset.sum_congr rfl h2]
    abel
  · -- **Case B.** No pivot; `h` kills `x^α ⊗ e_s`, and in `h d` only the term deleting the least
    -- element `q` of `s` survives, contributing `x^α ⊗ e_s` back.
    have hpiv' : ∀ a, ¬Finsupp.IndexPredicate α (s : Finset κ) a := fun a h => hpiv ⟨a, h⟩
    rw [Module.Basis.pairToSucc_eq_zero b α s hpiv', map_zero, zero_add]
    have hqs : (s : Finset κ).min' hne ∈ (s : Finset κ) := Finset.min'_mem _ _
    rw [Finset.sum_eq_single_of_mem ((s : Finset κ).min' hne) hqs]
    · -- The `a = q` term.
      have hpivq : Finsupp.IndexPredicate (α + Finsupp.single ((s : Finset κ).min' hne) 1)
          ((_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨(s : Finset κ).min' hne, hqs⟩ : Finset κ)) ((s : Finset κ).min' hne) := by
        refine ⟨Finsupp.mem_support_add_single.mpr (Or.inl rfl), fun m hm => ?_, fun c hc => ?_⟩
        · rcases Finsupp.mem_support_add_single.mp hm with rfl | hm
          · exact le_rfl
          · -- If some exponent sat below `q`, the least one would already be a pivot of `(α, s)`.
            rcases le_or_gt ((s : Finset κ).min' hne) m with hle | hcon
            · exact hle
            · have hsupp : α.support.Nonempty := ⟨m, hm⟩
              refine absurd ?_ (hpiv' (α.support.min' hsupp))
              refine ⟨Finset.min'_mem _ _, fun m' hm' => Finset.min'_le _ _ hm', fun c hc => ?_⟩
              calc α.support.min' hsupp ≤ m := Finset.min'_le _ _ hm
                _ < (s : Finset κ).min' hne := hcon
                _ ≤ c := Finset.min'_le _ _ hc
        · rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase_val] at hc
          exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_of_mem_erase hc))
            (Ne.symm (Finset.ne_of_mem_erase hc))
      have hset : Set.PowersetCard.insert (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨(s : Finset κ).min' hne, hqs⟩) hpivq.not_mem = s := by
        apply Subtype.ext
        rw [Set.PowersetCard.coe_insert, _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase_val]
        exact Finset.insert_erase hqs
      rw [Module.Basis.auxiliaryTerm, dif_pos hqs, map_smul, Module.Basis.linearMapToSucc_apply_pair,
        Module.Basis.pairToSucc_eq_neg b _ _ hpivq, Finsupp.add_single_sub_single, hset,
        Finset.auxiliaryNatFunction_min' hne]
      simp
    · -- Every other term of `d` leaves `q` behind in the subset, so `h` kills it.
      intro a ha hane
      have hnp : ∀ c, ¬Finsupp.IndexPredicate (α + Finsupp.single a 1)
          ((_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, ha⟩ : Finset κ)) c := by
        intro c hc
        have hqe : (s : Finset κ).min' hne ∈ (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, ha⟩ : Finset κ) := by
          rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase_val]; exact Finset.mem_erase.mpr ⟨Ne.symm hane, hqs⟩
        have hcq : c < (s : Finset κ).min' hne := hc.2.2 _ hqe
        have hqa : (s : Finset κ).min' hne ≤ a := Finset.min'_le _ _ ha
        have hcα : c ∈ α.support := by
          rcases Finsupp.mem_support_add_single.mp hc.1 with rfl | h
          · exact absurd (lt_of_lt_of_le hcq hqa) (lt_irrefl _)
          · exact h
        exact hpiv' c ⟨hcα, fun m hm => hc.2.1 m (Finsupp.mem_support_add_single.mpr (Or.inr hm)),
          fun c' hc' => lt_of_lt_of_le hcq (Finset.min'_le _ _ hc')⟩
      rw [Module.Basis.auxiliaryTerm, dif_pos ha, map_smul, Module.Basis.linearMapToSucc_apply_pair,
        Module.Basis.pairToSucc_eq_zero b _ _ hnp, smul_zero]

/-- The successor-index composite identity holds after evaluation at an arbitrary element. -/
theorem Module.Basis.succComposite_add_prevComposite_eq_id_apply (b : Module.Basis κ k V) (i : ℕ)
    (x : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1)) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b (i + 1) (Module.Basis.linearMapToSucc b (i + 1) x) + Module.Basis.linearMapToSucc b i (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i x) = x := by
  have hlin : ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b (i + 1)).restrictScalars k).comp (Module.Basis.linearMapToSucc b (i + 1)) +
      (Module.Basis.linearMapToSucc b i).comp ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i).restrictScalars k) = LinearMap.id := by
    refine (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1)).ext fun P => ?_
    obtain ⟨α, s⟩ := P
    simpa using Module.Basis.succComposite_add_prevComposite_eq_id_apply_auxiliary b i α s
  simpa using LinearMap.congr_fun hlin x

omit [LinearOrder κ] [DecidableEq κ] [Fintype κ] in
/-- The symmetric-algebra basis sends the zero finitely supported exponent to one. -/
theorem Module.Basis.symmetricAlgebra_zero (b : Module.Basis κ k V) : b.symmetricAlgebra 0 = 1 := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricAlgebra_apply_eq_monomial, MvPolynomial.monomial_zero', MvPolynomial.C_1, map_one]

omit [DecidableEq κ] [Fintype κ] in
/-- The degree-zero exterior-power basis evaluates at a zero-cardinality subset as the inverse zero-degree equivalence applied to one. -/
theorem Module.Basis.exteriorPower_zero_apply (b : Module.Basis κ k V) (s : Set.powersetCard κ 0) :
    b.exteriorPower 0 s = (exteriorPower.zeroEquiv k V).symm 1 := by
  apply (exteriorPower.zeroEquiv k V).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact exteriorPower.zeroEquiv_ιMulti _

/-- The index-zero composite identity holds on the displayed auxiliary value. -/
theorem Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply_auxiliary (b : Module.Basis κ k V) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ 0) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b 0 (Module.Basis.linearMapToSucc b 0 (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0 (α, s))) +
        auxiliaryLinearMapToIndexZero k V (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0 (α, s))) =
      _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0 (α, s) := by
  have hs : (s : Finset κ) = ∅ := Finset.card_eq_zero.mp (Set.powersetCard.card_eq s)
  rw [Module.Basis.linearMapToSucc_apply_pair]
  by_cases hα : α = 0
  · -- `x^0 ⊗ 1` is the one basis vector the homotopy misses; the splitting `η ε` catches it.
    subst hα
    rw [Module.Basis.pairToSucc_eq_zero b _ _ fun a h => by simpa using h.1, map_zero, zero_add]
    have haug : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0 (0, s)) =
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).symm 1 := by
      apply (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
      rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_counit_apply, LinearEquiv.apply_symm_apply, if_pos rfl]
    rw [haug, auxiliaryLinearMapToIndexZero_apply, LinearEquiv.apply_symm_apply, map_one, _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_apply,
      Module.Basis.symmetricAlgebra_zero, Module.Basis.exteriorPower_zero_apply]
  · -- Otherwise the pivot is the least variable of `x^α`, the condition on `s = ∅` being vacuous.
    have hsupp : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
    have hp : Finsupp.IndexPredicate α (s : Finset κ) (α.support.min' hsupp) :=
      ⟨Finset.min'_mem _ _, fun m hm => Finset.min'_le _ _ hm, fun c hc => by
        rw [hs] at hc; exact absurd hc (Finset.notMem_empty c)⟩
    have haug : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0 (α, s)) = 0 := by
      apply (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
      rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_counit_apply, if_neg hα, map_zero]
    have hpt : α.support.min' hsupp ∈ (Set.PowersetCard.insert s hp.not_mem : Finset κ) := by
      rw [Set.PowersetCard.coe_insert]; exact Finset.mem_insert_self _ _
    have hins : (Set.PowersetCard.insert s hp.not_mem : Finset κ) = {α.support.min' hsupp} := by
      rw [Set.PowersetCard.coe_insert, hs]; rfl
    have herase : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase (Set.PowersetCard.insert s hp.not_mem) ⟨α.support.min' hsupp, hpt⟩ = s :=
      Subtype.ext (Finset.erase_insert hp.not_mem)
    have hpos : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (Set.PowersetCard.insert s hp.not_mem : Finset κ) (α.support.min' hsupp) = 0 :=
      Finset.auxiliaryNatFunction_insert_self_of_lt hp.2.2
    rw [Module.Basis.pairToSucc_eq_neg b α s hp, map_neg,
      Module.Basis.auxiliaryMap_apply_auxiliary_eq_sum b 0 (α - Finsupp.single (α.support.min' hsupp) 1)
        (Set.PowersetCard.insert s hp.not_mem),
      hins, Finset.sum_singleton, Module.Basis.auxiliaryTerm, dif_pos hpt, hpos,
      Finsupp.sub_single_add_single hp.one_le, herase, haug, map_zero, add_zero]
    rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor_apply, pow_one]
    change -((((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k]
        (Module.Basis.exteriorPower 0 b) s :
        SymmetricAlgebra k V ⊗[k] (⋀[k]^0 V))) =
      b.symmetricAlgebra α ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s
    have hsign :
        ((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s =
          -(b.symmetricAlgebra α ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s) := by
      simpa only [TensorProduct.neg_tmul] using
        congrArg (fun z : SymmetricAlgebra k V =>
          z ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s)
          (neg_one_smul k (b.symmetricAlgebra α))
    set_option backward.isDefEq.respectTransparency true in
      exact (congrArg Neg.neg hsign).trans (neg_neg _)

/-- The index-zero composite identity holds after evaluation at an arbitrary element. -/
theorem Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply (b : Module.Basis κ k V) (x : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V 0) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b 0 (Module.Basis.linearMapToSucc b 0 x) + auxiliaryLinearMapToIndexZero k V (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V x) = x := by
  have hlin : ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b 0).restrictScalars k).comp (Module.Basis.linearMapToSucc b 0) +
      (auxiliaryLinearMapToIndexZero k V).comp ((_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V).restrictScalars k) = LinearMap.id := by
    refine (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b 0).ext fun P => ?_
    obtain ⟨α, s⟩ := P
    simpa using Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply_auxiliary b α s
  simpa using LinearMap.congr_fun hlin x

/-- At a successor index, the displayed sum of two composites is the identity linear map. -/
theorem Module.Basis.succComposite_add_prevComposite_eq_id (b : Module.Basis κ k V) (i : ℕ) :
    ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b (i + 1)).restrictScalars k).comp (Module.Basis.linearMapToSucc b (i + 1)) +
      (Module.Basis.linearMapToSucc b i).comp ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i).restrictScalars k) = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using Module.Basis.succComposite_add_prevComposite_eq_id_apply b i x

/-- At index zero, the displayed sum of two composites is the identity linear map. -/
theorem Module.Basis.composite_add_auxiliaryComposite_eq_id_zero (b : Module.Basis κ k V) :
    ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b 0).restrictScalars k).comp (Module.Basis.linearMapToSucc b 0) +
      (auxiliaryLinearMapToIndexZero k V).comp ((_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V).restrictScalars k) = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply b x

end Homotopy

end RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps
