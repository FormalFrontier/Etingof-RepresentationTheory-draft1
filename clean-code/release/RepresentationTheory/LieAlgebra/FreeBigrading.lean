/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.ExplicitConstructions
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.DirectSum.Decomposition
import RepresentationTheory.Alignment.Attribute

/-! # Free bigrading -/


namespace RepresentationTheory.LieAlgebra.FreeBigrading

open FreeLieAlgebra TensorProduct

variable (k : Type*) [CommRing k]


/-- An auxiliary commutative-ring construction carrying monomials indexed by pairs of natural numbers. -/
abbrev BidegreeAlgebra : Type _ := AddMonoidAlgebra k (ℕ × ℕ)


/-- The displayed element of the auxiliary algebra associated with a pair of natural numbers. -/
noncomputable def bidegreeMonomial (p : ℕ × ℕ) : BidegreeAlgebra k := AddMonoidAlgebra.single p 1


/-- Multiplying two displayed bidegree monomials gives the monomial indexed by the sum of their bidegrees. -/
theorem bidegreeMonomial_mul (p q : ℕ × ℕ) : bidegreeMonomial k p * bidegreeMonomial k q = bidegreeMonomial k (p + q) := by
  simp [bidegreeMonomial, AddMonoidAlgebra.single_mul_single]


/-- The bidegree assigned to each of the two free generators. -/
def generatorBidegree : Fin 2 → ℕ × ℕ := ![(1, 0), (0, 1)]


/-- The generator indexed by zero has bidegree `(1, 0)`. -/
@[simp] theorem generatorBidegree_zero : generatorBidegree 0 = (1, 0) := rfl

/-- The generator indexed by one has bidegree `(0, 1)`. -/
@[simp] theorem generatorBidegree_one : generatorBidegree 1 = (0, 1) := rfl


/-- A Lie homomorphism from the free Lie algebra to its tensor product with the auxiliary bidegree algebra. -/
noncomputable def bidegreeCoaction :
    FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ BidegreeAlgebra k ⊗[k] FreeLieAlgebra k (Fin 2) :=
  FreeLieAlgebra.lift k fun i => bidegreeMonomial k (generatorBidegree i) ⊗ₜ[k] FreeLieAlgebra.of k i


/-- The bidegree coaction sends a canonical free generator to the tensor of its assigned bidegree monomial with that generator. -/
@[simp] theorem bidegreeCoaction_of (i : Fin 2) :
    bidegreeCoaction k (FreeLieAlgebra.of k i) = bidegreeMonomial k (generatorBidegree i) ⊗ₜ[k] FreeLieAlgebra.of k i :=
  FreeLieAlgebra.lift_of_apply _ _


/-- The linear functional extracting the coefficient at a specified bidegree from the displayed auxiliary algebra. -/
noncomputable def bidegreeCoefficient (p : ℕ × ℕ) : BidegreeAlgebra k →ₗ[k] k :=
  Finsupp.lapply p ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap


/-- The bidegree coefficient of a displayed monomial is one at the same bidegree and zero otherwise. -/
theorem bidegreeCoefficient_monomial (p q : ℕ × ℕ) :
    bidegreeCoefficient k p (bidegreeMonomial k q) = if q = p then 1 else 0 := by
  classical
  simp [bidegreeCoefficient, bidegreeMonomial, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.single_apply]


/-- The linear map from the bidegree-algebra tensor product to the free Lie algebra determined by a specified bidegree coefficient. -/
noncomputable def bidegreeTensorProjection (p : ℕ × ℕ) :
    BidegreeAlgebra k ⊗[k] FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  (TensorProduct.lid k (FreeLieAlgebra k (Fin 2))).toLinearMap ∘ₗ
    TensorProduct.map (bidegreeCoefficient k p) LinearMap.id


/-- On a pure tensor, the bidegree tensor projection scales the free Lie algebra factor by the selected coefficient of the auxiliary-algebra factor. -/
@[simp] theorem bidegreeTensorProjection_tmul (p : ℕ × ℕ) (a : BidegreeAlgebra k) (u : FreeLieAlgebra k (Fin 2)) :
    bidegreeTensorProjection k p (a ⊗ₜ[k] u) = bidegreeCoefficient k p a • u := rfl


/-- The linear projection of the free Lie algebra onto a specified bidegree. -/
noncomputable def freeLieBidegreeProjection (p : ℕ × ℕ) :
    FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  bidegreeTensorProjection k p ∘ₗ (bidegreeCoaction k).toLinearMap


/-- The free-Lie bidegree projection is obtained by applying the displayed tensor projection after the displayed Lie homomorphism. -/
theorem freeLieBidegreeProjection_apply (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    freeLieBidegreeProjection k p u = bidegreeTensorProjection k p (bidegreeCoaction k u) := rfl


/-- An inductively generated predicate asserting that a free Lie algebra element has a specified bidegree. -/
inductive FreeLieIsBihomogeneous : ℕ × ℕ → FreeLieAlgebra k (Fin 2) → Prop
  | of (i : Fin 2) : FreeLieIsBihomogeneous (generatorBidegree i) (FreeLieAlgebra.of k i)
  | lie {p q : ℕ × ℕ} {u v : FreeLieAlgebra k (Fin 2)} :
      FreeLieIsBihomogeneous p u → FreeLieIsBihomogeneous q v → FreeLieIsBihomogeneous (p + q) ⁅u, v⁆


/-- The submodule of the free Lie algebra associated with a pair of natural-number degrees. -/
noncomputable def freeLieBidegree (p : ℕ × ℕ) : Submodule k (FreeLieAlgebra k (Fin 2)) :=
  Submodule.span k {u | FreeLieIsBihomogeneous k p u}


/-- Every element satisfying the displayed bihomogeneity predicate belongs to the corresponding free-Lie bidegree submodule. -/
theorem mem_freeLieBidegree_of_freeLieIsBihomogeneous {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : FreeLieIsBihomogeneous k p u) :
    u ∈ freeLieBidegree k p :=
  Submodule.subset_span h


/-- Each canonical free generator belongs to the free-Lie submodule at its assigned bidegree. -/
theorem of_mem_freeLieBidegree (i : Fin 2) :
    FreeLieAlgebra.of k i ∈ freeLieBidegree k (generatorBidegree i) :=
  mem_freeLieBidegree_of_freeLieIsBihomogeneous k (.of i)


/-- The displayed element belongs to free-Lie bidegree `(1, 0)`. -/
theorem degree10Element_mem_freeLieBidegree : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux3 k ∈ freeLieBidegree k (1, 0) := of_mem_freeLieBidegree k 0


/-- The displayed element belongs to free-Lie bidegree `(0, 1)`. -/
theorem degree01Element_mem_freeLieBidegree : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux4 k ∈ freeLieBidegree k (0, 1) := of_mem_freeLieBidegree k 1


/-- The bracket of free Lie algebra elements of bidegrees `p` and `q` has bidegree `p + q`. -/
theorem bracket_mem_freeLieBidegree_add {p q : ℕ × ℕ} {u v : FreeLieAlgebra k (Fin 2)}
    (hu : u ∈ freeLieBidegree k p) (hv : v ∈ freeLieBidegree k q) : ⁅u, v⁆ ∈ freeLieBidegree k (p + q) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv => exact mem_freeLieBidegree_of_freeLieIsBihomogeneous k (hu.lie hv)
      | zero => simp
      | add v w _ _ hv hw => simpa [lie_add] using (freeLieBidegree k (p + q)).add_mem hv hw
      | smul c v _ hv => simpa [lie_smul] using (freeLieBidegree k (p + q)).smul_mem c hv
  | zero => simp
  | add u w _ _ hu hw => simpa [add_lie] using (freeLieBidegree k (p + q)).add_mem hu hw
  | smul c u _ hu => simpa [smul_lie] using (freeLieBidegree k (p + q)).smul_mem c hu


/-- An element satisfying the displayed bihomogeneity predicate is sent to the tensor of its bidegree monomial with itself. -/
theorem bidegreeCoaction_eq_tmul_of_freeLieIsBihomogeneous {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : FreeLieIsBihomogeneous k p u) : bidegreeCoaction k u = bidegreeMonomial k p ⊗ₜ[k] u := by
  induction h with
  | of i => exact bidegreeCoaction_of k i
  | @lie p q u v _ _ hu hv =>
      rw [LieHom.map_lie, hu, hv, LieAlgebra.ExtendScalars.bracket_tmul, bidegreeMonomial_mul]


/-- A free Lie algebra element in bidegree `p` is sent to the tensor of the monomial at `p` with that element. -/
theorem bidegreeCoaction_eq_tmul_of_mem {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : u ∈ freeLieBidegree k p) :
    bidegreeCoaction k u = bidegreeMonomial k p ⊗ₜ[k] u := by
  induction h using Submodule.span_induction with
  | mem u hu => exact bidegreeCoaction_eq_tmul_of_freeLieIsBihomogeneous k hu
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, hu, hv, TensorProduct.tmul_add]
  | smul c u _ hu => rw [map_smul, hu, TensorProduct.tmul_smul]


/-- On a free Lie algebra element of bidegree `p`, projection to bidegree `q` is the element itself when `p = q` and zero otherwise. -/
theorem freeLieBidegreeProjection_apply_of_mem {p q : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : u ∈ freeLieBidegree k p) :
    freeLieBidegreeProjection k q u = if p = q then u else 0 := by
  classical
  rw [freeLieBidegreeProjection_apply, bidegreeCoaction_eq_tmul_of_mem k h, bidegreeTensorProjection_tmul, bidegreeCoefficient_monomial]
  split <;> simp


/-- Projection to a bidegree fixes every free Lie algebra element in the corresponding bidegree submodule. -/
theorem freeLieBidegreeProjection_apply_eq_self {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : u ∈ freeLieBidegree k p) : freeLieBidegreeProjection k p u = u := by
  simp [freeLieBidegreeProjection_apply_of_mem k h]


/-- The projection to bidegree `q` vanishes on a free Lie algebra element of bidegree `p` when `p` and `q` are distinct. -/
theorem freeLieBidegreeProjection_eq_zero_of_mem {p q : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : u ∈ freeLieBidegree k p) (hpq : p ≠ q) : freeLieBidegreeProjection k q u = 0 := by
  simp [freeLieBidegreeProjection_apply_of_mem k h, hpq]


/-- The supremum of all free-Lie bidegree submodules is the top submodule. -/
theorem iSup_freeLieBidegree_eq_top : ⨆ p : ℕ × ℕ, freeLieBidegree k p = ⊤ := by
  set S : Submodule k (FreeLieAlgebra k (Fin 2)) := ⨆ p : ℕ × ℕ, freeLieBidegree k p with hS
  have hmem : ∀ (p : ℕ × ℕ) {u}, u ∈ freeLieBidegree k p → u ∈ S := fun p _ hu =>
    (le_iSup (fun p : ℕ × ℕ => freeLieBidegree k p) p) hu

  have hlie : ∀ u ∈ S, ∀ v ∈ S, ⁅u, v⁆ ∈ S := by
    intro u hu v hv
    induction hu using Submodule.iSup_induction' with
    | mem p u hu =>
        induction hv using Submodule.iSup_induction' with
        | mem q v hv => exact hmem (p + q) (bracket_mem_freeLieBidegree_add k hu hv)
        | zero => simp
        | add v w _ _ hv hw => simpa [lie_add] using S.add_mem hv hw
    | zero => simp
    | add u w _ _ hu hw => simpa [add_lie] using S.add_mem hu hw
  let H : LieSubalgebra k (FreeLieAlgebra k (Fin 2)) :=
    { S with lie_mem' := fun {u v} hu hv => hlie u hu v hv }
  have hgen : Set.range (FreeLieAlgebra.of k) ⊆ (H : Set (FreeLieAlgebra k (Fin 2))) := by
    rintro _ ⟨i, rfl⟩
    exact hmem (generatorBidegree i) (of_mem_freeLieBidegree k i)
  have : (⊤ : LieSubalgebra k (FreeLieAlgebra k (Fin 2))) ≤ H := by
    rw [← _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLie_eq k]
    exact LieSubalgebra.lieSpan_le.2 hgen
  rw [eq_top_iff]
  intro u _
  exact this (LieSubalgebra.mem_top u)


/-- The value of a free-Lie bidegree projection belongs to the corresponding bidegree submodule. -/
theorem freeLieBidegreeProjection_mem (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    freeLieBidegreeProjection k p u ∈ freeLieBidegree k p := by
  have hu : u ∈ ⨆ q : ℕ × ℕ, freeLieBidegree k q := by rw [iSup_freeLieBidegree_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      rw [freeLieBidegreeProjection_apply_of_mem k hv]
      split
      · subst ‹q = p›; exact hv
      · exact (freeLieBidegree k p).zero_mem
  | zero => simp
  | add v w _ _ hv hw => simpa using (freeLieBidegree k p).add_mem hv hw


/-- Every free Lie algebra element is a finite sum of its displayed bidegree projections, and all projections outside the chosen finite set vanish. -/
theorem exists_finite_bidegree_decomposition (u : FreeLieAlgebra k (Fin 2)) :
    ∃ s : Finset (ℕ × ℕ), (∀ p ∉ s, freeLieBidegreeProjection k p u = 0) ∧ ∑ p ∈ s, freeLieBidegreeProjection k p u = u := by
  classical
  have hu : u ∈ ⨆ q : ℕ × ℕ, freeLieBidegree k q := by rw [iSup_freeLieBidegree_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      refine ⟨{q}, fun p hp => freeLieBidegreeProjection_eq_zero_of_mem k hv (Ne.symm (by simpa using hp)), ?_⟩
      simp [freeLieBidegreeProjection_apply_eq_self k hv]
  | zero => exact ⟨∅, by simp, by simp⟩
  | add v w _ _ hv hw =>
      obtain ⟨s, hs0, hs⟩ := hv
      obtain ⟨t, ht0, ht⟩ := hw
      refine ⟨s ∪ t, fun p hp => by simp [hs0 p (fun h => hp (Finset.mem_union_left _ h)),
        ht0 p (fun h => hp (Finset.mem_union_right _ h))], ?_⟩
      have hs' : ∑ p ∈ s ∪ t, freeLieBidegreeProjection k p v = v :=
        (Finset.sum_subset Finset.subset_union_left (fun p _ hp => hs0 p hp)).symm.trans hs
      have ht' : ∑ p ∈ s ∪ t, freeLieBidegreeProjection k p w = w :=
        (Finset.sum_subset Finset.subset_union_right (fun p _ hp => ht0 p hp)).symm.trans ht
      simp only [map_add, Finset.sum_add_distrib, hs', ht']


/-- The free-Lie bidegree projection vanishes on every element of the displayed supremum of bidegree submodules. -/
theorem freeLieBidegreeProjection_eq_zero_of_mem_iSup {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (hu : u ∈ ⨆ q, ⨆ (_ : q ≠ p), freeLieBidegree k q) : freeLieBidegreeProjection k p u = 0 := by
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      by_cases hq : q = p
      · subst hq
        rw [iSup_neg (by simp)] at hv
        simp [(Submodule.mem_bot k).1 hv]
      · rw [iSup_pos hq] at hv
        exact freeLieBidegreeProjection_eq_zero_of_mem k hv hq
  | zero => simp
  | add v w _ _ hv hw => simp [hv, hw]


/-- The family of free-Lie bidegree submodules is independent under indexed suprema. -/
theorem iSupIndep_freeLieBidegree : iSupIndep (freeLieBidegree k) := by
  intro p
  rw [Submodule.disjoint_def]
  intro u hu hu'
  rw [← freeLieBidegreeProjection_apply_eq_self k hu, freeLieBidegreeProjection_eq_zero_of_mem_iSup k hu']


/-- The free-Lie bidegree submodules form an internal direct sum. -/
theorem freeLieBidegree_isInternal : DirectSum.IsInternal (freeLieBidegree k) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_freeLieBidegree k, iSup_freeLieBidegree_eq_top k⟩


/-- The direct-sum decomposition of the free Lie algebra by the displayed bidegree submodules. -/
noncomputable instance freeLieBidegreeDecomposition : DirectSum.Decomposition (freeLieBidegree k) :=
  (freeLieBidegree_isInternal k).chooseDecomposition


/-- The bracket of the degree-`(1, 0)` element with its bracket with the degree-`(0, 1)` element has bidegree `(2, 1)`. -/
theorem iteratedBracket_mem_bidegree_two_one : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux3 k, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux3 k, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux4 k⁆⁆ ∈ freeLieBidegree k (2, 1) := by
  have hdeg : ((1, 0) + ((1, 0) + (0, 1)) : ℕ × ℕ) = (2, 1) := rfl
  exact hdeg ▸
    bracket_mem_freeLieBidegree_add k (degree10Element_mem_freeLieBidegree k) (bracket_mem_freeLieBidegree_add k (degree10Element_mem_freeLieBidegree k) (degree01Element_mem_freeLieBidegree k))


/-- Applying bracket with the degree-`(0, 1)` element `n + 1` times to the degree-`(1, 0)` element produces an element of bidegree `(1, n + 1)`. -/
theorem iterate_bracket_mem_bidegree_one_succ (n : ℕ) :
    (fun z => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux4 k, z⁆)^[n + 1] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux3 k) ∈ freeLieBidegree k (1, n + 1) := by
  induction n with
  | zero => simpa using bracket_mem_freeLieBidegree_add k (degree01Element_mem_freeLieBidegree k) (degree10Element_mem_freeLieBidegree k)
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [Prod.ext_iff, add_comm] using bracket_mem_freeLieBidegree_add k (degree01Element_mem_freeLieBidegree k) ih


/-- A natural-number-indexed auxiliary Lie ideal of the free Lie algebra on two generators. -/
noncomputable def auxiliaryLieIdeal (n : ℕ) : LieIdeal k (FreeLieAlgebra k (Fin 2)) where
  carrier := {u | ∀ p, freeLieBidegreeProjection k p u ∈ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n}
  add_mem' hu hv p := by simpa using (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).add_mem (hu p) (hv p)
  zero_mem' p := by simp
  smul_mem' c _ hu p := by simpa using (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).smul_mem c (hu p)
  lie_mem {v u} hu p := by
    classical
    obtain ⟨s, _, hs⟩ := exists_finite_bidegree_decomposition k v
    obtain ⟨t, _, ht⟩ := exists_finite_bidegree_decomposition k u
    have hvu : ⁅v, u⁆ = ∑ q ∈ s, ∑ r ∈ t, ⁅freeLieBidegreeProjection k q v, freeLieBidegreeProjection k r u⁆ := by
      conv_lhs => rw [← hs, ← ht]
      exact sum_lie_sum _ _ _ _
    rw [hvu, map_sum]
    refine (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).sum_mem fun q _ => ?_
    rw [map_sum]
    refine (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).sum_mem fun r _ => ?_
    have hmem : ⁅freeLieBidegreeProjection k q v, freeLieBidegreeProjection k r u⁆ ∈ freeLieBidegree k (q + r) :=
      bracket_mem_freeLieBidegree_add k (freeLieBidegreeProjection_mem k q v) (freeLieBidegreeProjection_mem k r u)
    rw [freeLieBidegreeProjection_apply_of_mem k hmem]
    split
    · exact (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).lie_mem (hu r)
    · exact (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).zero_mem


/-- Every bidegree projection preserves membership in the displayed auxiliary submodule. -/
theorem freeLieBidegreeProjection_mem_auxiliarySubmodule {n : ℕ} {u : FreeLieAlgebra k (Fin 2)} (hu : u ∈ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n)
    (p : ℕ × ℕ) : freeLieBidegreeProjection k p u ∈ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n := by
  have hle : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n ≤ auxiliaryLieIdeal k n := by
    rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal, LieSubmodule.lieSpan_le]
    rintro a (rfl | rfl) q
    · rw [freeLieBidegreeProjection_apply_of_mem k (iteratedBracket_mem_bidegree_two_one k)]
      split
      · exact LieSubmodule.subset_lieSpan (by simp)
      · exact (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).zero_mem
    · rw [freeLieBidegreeProjection_apply_of_mem k (iterate_bracket_mem_bidegree_one_succ k n)]
      split
      · exact LieSubmodule.subset_lieSpan (by simp)
      · exact (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).zero_mem
  exact hle hu p


/-- The bidegree submodule of the displayed target Lie algebra at a pair of natural-number degrees. -/
noncomputable def targetBidegree (n : ℕ) (p : ℕ × ℕ) : Submodule k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n) :=
  (freeLieBidegree k p).map (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n).toLinearMap


/-- The displayed map sends a free Lie algebra element of bidegree `p` to a target element of the same bidegree. -/
theorem map_mem_targetBidegree {n : ℕ} {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (hu : u ∈ freeLieBidegree k p) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n u ∈ targetBidegree k n p :=
  ⟨u, hu, rfl⟩


/-- A target element has bidegree `p` exactly when it is the image of a free Lie algebra element of bidegree `p`. -/
theorem mem_targetBidegree_iff_exists_freeLieBidegree_preimage {n : ℕ} {p : ℕ × ℕ} {a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n} :
    a ∈ targetBidegree k n p ↔ ∃ u ∈ freeLieBidegree k p, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n u = a := Iff.rfl


/-- The displayed indexed target element belongs to target bidegree `(1, 0)`. -/
theorem degree10TargetElement_mem_targetBidegree (n : ℕ) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux7 k n ∈ targetBidegree k n (1, 0) := map_mem_targetBidegree k (degree10Element_mem_freeLieBidegree k)


/-- The displayed indexed target element belongs to target bidegree `(0, 1)`. -/
theorem degree01TargetElement_mem_targetBidegree (n : ℕ) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux8 k n ∈ targetBidegree k n (0, 1) := map_mem_targetBidegree k (degree01Element_mem_freeLieBidegree k)


/-- The bracket of target elements of bidegrees `p` and `q` has bidegree `p + q`. -/
theorem bracket_mem_targetBidegree_add {n : ℕ} {p q : ℕ × ℕ} {a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n} (ha : a ∈ targetBidegree k n p)
    (hb : b ∈ targetBidegree k n q) : ⁅a, b⁆ ∈ targetBidegree k n (p + q) := by
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  exact ⟨⁅u, v⁆, bracket_mem_freeLieBidegree_add k hu hv, by simp⟩


/-- The linear projection of the displayed target Lie algebra onto a specified bidegree. -/
noncomputable def targetBidegreeProjection (n : ℕ) (p : ℕ × ℕ) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n →ₗ[k] _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n :=
  Submodule.liftQ (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n).toSubmodule ((_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n).toLinearMap ∘ₗ freeLieBidegreeProjection k p)
    (by
      intro a ha
      have : freeLieBidegreeProjection k p a ∈ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal k n := freeLieBidegreeProjection_mem_auxiliarySubmodule k ha p
      simpa using ((_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.mem_submodule_aux13 k n _).2 this))


/-- Projecting the image of a free Lie algebra element to a target bidegree equals the image of its free-Lie bidegree projection. -/
theorem targetBidegreeProjection_map (n : ℕ) (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    targetBidegreeProjection k n p (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n u) = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n (freeLieBidegreeProjection k p u) := rfl


/-- On an element of bidegree `p`, projection to bidegree `q` is the element itself when `p = q` and zero otherwise. -/
theorem targetBidegreeProjection_apply_of_mem {n : ℕ} {p q : ℕ × ℕ} {a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n} (ha : a ∈ targetBidegree k n p) :
    targetBidegreeProjection k n q a = if p = q then a else 0 := by
  obtain ⟨u, hu, rfl⟩ := ha
  change targetBidegreeProjection k n q (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n u) = if p = q then _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n u else 0
  rw [targetBidegreeProjection_map, freeLieBidegreeProjection_apply_of_mem k hu]
  split
  · simp
  · rfl


/-- Projection to a bidegree fixes every element of the corresponding target bidegree submodule. -/
theorem targetBidegreeProjection_apply_eq_self {n : ℕ} {p : ℕ × ℕ} {a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n} (ha : a ∈ targetBidegree k n p) :
    targetBidegreeProjection k n p a = a := by simp [targetBidegreeProjection_apply_of_mem k ha]


/-- The value of a target bidegree projection belongs to the corresponding bidegree submodule. -/
theorem targetBidegreeProjection_mem (n : ℕ) (p : ℕ × ℕ) (a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n) : targetBidegreeProjection k n p a ∈ targetBidegree k n p := by
  obtain ⟨u, rfl⟩ := _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_surjective k n a
  rw [targetBidegreeProjection_map]
  exact map_mem_targetBidegree k (freeLieBidegreeProjection_mem k p u)


/-- The range of the target projection at bidegree `p` is exactly the target bidegree submodule at `p`. -/
theorem range_targetBidegreeProjection (n : ℕ) (p : ℕ × ℕ) : LinearMap.range (targetBidegreeProjection k n p) = targetBidegree k n p := by
  refine le_antisymm ?_ fun a ha => ⟨a, targetBidegreeProjection_apply_eq_self k ha⟩
  rintro _ ⟨a, rfl⟩
  exact targetBidegreeProjection_mem k n p a


/-- If a set spans the target, then each target bidegree is spanned by the image of that set under the corresponding bidegree projection. -/
theorem targetBidegree_eq_span_image_of_span_eq_top {n : ℕ} (p : ℕ × ℕ) {S : Set (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n)} (hS : Submodule.span k S = ⊤) :
    targetBidegree k n p = Submodule.span k (targetBidegreeProjection k n p '' S) := by
  rw [← range_targetBidegreeProjection k n p, ← Submodule.map_top, ← hS, Submodule.map_span]


/-- The projection to bidegree `q` vanishes on an element of bidegree `p` when `p` and `q` are distinct. -/
theorem targetBidegreeProjection_eq_zero_of_mem {n : ℕ} {p q : ℕ × ℕ} {a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n} (ha : a ∈ targetBidegree k n p)
    (hpq : p ≠ q) : targetBidegreeProjection k n q a = 0 := by simp [targetBidegreeProjection_apply_of_mem k ha, hpq]


/-- The supremum of all target bidegree submodules is the top submodule. -/
theorem iSup_targetBidegree_eq_top (n : ℕ) : ⨆ p : ℕ × ℕ, targetBidegree k n p = ⊤ := by
  have hmap : ⨆ p : ℕ × ℕ, targetBidegree k n p
      = (⨆ p : ℕ × ℕ, freeLieBidegree k p).map (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n).toLinearMap :=
    (Submodule.map_iSup _ _).symm
  have hsurj : Function.Surjective ⇑(_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k n).toLinearMap := _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_surjective k n
  rw [hmap, iSup_freeLieBidegree_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]


/-- The target bidegree projection vanishes on every element of the displayed supremum of bidegree submodules. -/
theorem targetBidegreeProjection_eq_zero_of_mem_iSup {n : ℕ} {p : ℕ × ℕ} {a : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k n}
    (ha : a ∈ ⨆ q, ⨆ (_ : q ≠ p), targetBidegree k n q) : targetBidegreeProjection k n p a = 0 := by
  induction ha using Submodule.iSup_induction' with
  | mem q b hb =>
      by_cases hq : q = p
      · subst hq
        rw [iSup_neg (by simp)] at hb
        simp [(Submodule.mem_bot k).1 hb]
      · rw [iSup_pos hq] at hb
        exact targetBidegreeProjection_eq_zero_of_mem k hb hq
  | zero => simp
  | add b c _ _ hb hc => simp [hb, hc]


/-- The family of target bidegree submodules is independent under indexed suprema. -/
theorem iSupIndep_targetBidegree (n : ℕ) : iSupIndep (targetBidegree k n) := by
  intro p
  rw [Submodule.disjoint_def]
  intro a ha ha'
  rw [← targetBidegreeProjection_apply_eq_self k ha, targetBidegreeProjection_eq_zero_of_mem_iSup k ha']


/-- The target bidegree submodules form an internal direct sum. -/
theorem targetBidegree_isInternal (n : ℕ) : DirectSum.IsInternal (targetBidegree k n) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_targetBidegree k n, iSup_targetBidegree_eq_top k n⟩


/-- The direct-sum decomposition of the displayed target Lie algebra by its bidegree submodules. -/
noncomputable instance targetBidegreeDecomposition (n : ℕ) : DirectSum.Decomposition (targetBidegree k n) :=
  (targetBidegree_isInternal k n).chooseDecomposition


/-- The displayed indexed element belongs to the target bidegree `(1, i)`. -/
theorem auxiliaryElement_mem_targetBidegree (n i : ℕ) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k n i ∈ targetBidegree k n (1, i) := by
  induction i with
  | zero => simpa using degree10TargetElement_mem_targetBidegree k n
  | succ i ih =>
      rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq]
      simpa [Prod.ext_iff, add_comm] using bracket_mem_targetBidegree_add k (degree01TargetElement_mem_targetBidegree k n) ih

end RepresentationTheory.LieAlgebra.FreeBigrading


attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.FreeBigrading.BidegreeAlgebra
  RepresentationTheory.LieAlgebra.FreeBigrading.bidegreeMonomial
  RepresentationTheory.LieAlgebra.FreeBigrading.generatorBidegree
  RepresentationTheory.LieAlgebra.FreeBigrading.bidegreeCoaction
  RepresentationTheory.LieAlgebra.FreeBigrading.bidegreeCoefficient
  RepresentationTheory.LieAlgebra.FreeBigrading.bidegreeTensorProjection
  RepresentationTheory.LieAlgebra.FreeBigrading.freeLieBidegreeProjection
  RepresentationTheory.LieAlgebra.FreeBigrading.freeLieBidegree
  RepresentationTheory.LieAlgebra.FreeBigrading.freeLieBidegreeDecomposition
  RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryLieIdeal
  RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree
  RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeProjection
  RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeDecomposition
