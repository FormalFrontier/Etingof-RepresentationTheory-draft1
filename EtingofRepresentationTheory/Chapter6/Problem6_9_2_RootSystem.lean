import EtingofRepresentationTheory.Chapter6.Problem6_9_2

/-!
# Root-system structure on the E8, E7, and E6 lattice roots

`Problem6_9_2.lean` constructs the three lattice root sets, identifies the E8 simple-root
Gram graph, and counts the roots.  This file supplies the missing root-system axioms:
integrality and closure under the orthogonal reflections in roots.

The predicate `IsSimplyLacedCrystallographicRootSystem` is the subset-level formulation suited
to the book: a finite set of norm-two vectors, closed under negation and the reflections
`x ↦ x - inner x a • a`, with integral pairings.  Such a set is a reduced crystallographic root
system in its linear span.  Using the span rather than the ambient `Q^8` is essential for E7 and
E6, whose roots lie in proper subspaces.
-/

namespace Etingof.Problem6_9_2

open Finset

/-- Reflection in a norm-two vector `a`.  Since `inner a a = 2`, the usual formula
`x - 2 inner(x,a)/inner(a,a) a` reduces to this expression. -/
def rootReflection (a x : Fin 8 → ℚ) : Fin 8 → ℚ :=
  x - inner x a • a

/-- A faithful subset-level predicate for a finite, reduced, simply-laced crystallographic
root system in its linear span. -/
structure IsSimplyLacedCrystallographicRootSystem (R : Set (Fin 8 → ℚ)) : Prop where
  finite : R.Finite
  norm_two : ∀ a ∈ R, inner a a = 2
  neg_mem : ∀ a ∈ R, -a ∈ R
  reduced : ∀ a ∈ R, ∀ q : ℚ, q • a ∈ R → q = 1 ∨ q = -1
  integral_pairing : ∀ a ∈ R, ∀ b ∈ R, ∃ z : ℤ, inner a b = z
  reflection_mem : ∀ a ∈ R, ∀ b ∈ R, rootReflection a b ∈ R

/-! ## Bilinearity of the coordinate inner product -/

theorem inner_comm (x y : Fin 8 → ℚ) : inner x y = inner y x := by
  simp only [inner]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inner_sub_left (x y z : Fin 8 → ℚ) :
    inner (x - y) z = inner x z - inner y z := by
  simp only [inner, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem inner_sub_right (x y z : Fin 8 → ℚ) :
    inner x (y - z) = inner x y - inner x z := by
  simp only [inner, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inner_smul_left (q : ℚ) (x y : Fin 8 → ℚ) :
    inner (q • x) y = q * inner x y := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem inner_smul_right (q : ℚ) (x y : Fin 8 → ℚ) :
    inner x (q • y) = q * inner x y := by
  rw [inner_comm, inner_smul_left, inner_comm x y]

/-- Equal-length nonzero roots cannot be nontrivial scalar multiples. -/
theorem scalar_eq_one_or_neg_one_of_norm_two {a : Fin 8 → ℚ} {q : ℚ}
    (ha : inner a a = 2) (hqa : inner (q • a) (q • a) = 2) :
    q = 1 ∨ q = -1 := by
  rw [inner_smul_left, inner_smul_right, ha] at hqa
  apply sq_eq_one_iff.mp
  nlinarith

/-- Reflections in norm-two vectors preserve the norm. -/
theorem inner_rootReflection_self {a x : Fin 8 → ℚ} (ha : inner a a = 2) :
    inner (rootReflection a x) (rootReflection a x) = inner x x := by
  simp only [rootReflection, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_comm a x, ha]
  ring

/-! ## Integrality of the E8 lattice -/

/-- The integral Gram matrix of the chosen E8 lattice basis. -/
def αGramZ (i j : Fin 8) : ℤ := if i = j then 2 else -gramAdj i j

theorem αGramZ_cast (i j : Fin 8) : (αGramZ i j : ℚ) = inner (α i) (α j) := by
  by_cases h : i = j
  · subst j
    simp only [αGramZ, if_pos, Int.cast_ofNat]
    exact (α_norm_two i).symm
  · rcases α_inner_offdiag i j h with hij | hij
    · simp [αGramZ, gramAdj, h, hij]
    · simp [αGramZ, gramAdj, h, hij]

/-- The E8 lattice is closed under integral linear combinations `x - z y`. -/
theorem e8Lattice_sub_zsmul_mem {x y : Fin 8 → ℚ}
    (hx : x ∈ E8Lattice) (hy : y ∈ E8Lattice) (z : ℤ) :
    x - (z : ℚ) • y ∈ E8Lattice := by
  obtain ⟨c, hc⟩ := α_isBasis.1 x hx
  obtain ⟨d, hd⟩ := α_isBasis.1 y hy
  have hmem := α_isBasis.2 (fun i => c i - z * d i)
  convert hmem using 1
  rw [hc, hd]
  simp only [Int.cast_sub, Int.cast_mul, Finset.sum_sub_distrib, sub_smul,
    mul_smul, Finset.smul_sum]

/-- The E8 lattice is closed under negation. -/
theorem e8Lattice_neg_mem {x : Fin 8 → ℚ} (hx : x ∈ E8Lattice) : -x ∈ E8Lattice := by
  simpa using e8Lattice_sub_zsmul_mem (α_isBasis.2 0) hx (1 : ℤ)

/-- The standard inner product of any two E8 lattice vectors is integral. -/
theorem inner_e8Lattice_isInt {x y : Fin 8 → ℚ}
    (hx : x ∈ E8Lattice) (hy : y ∈ E8Lattice) :
    ∃ z : ℤ, inner x y = z := by
  obtain ⟨c, rfl⟩ := α_isBasis.1 x hx
  obtain ⟨d, rfl⟩ := α_isBasis.1 y hy
  refine ⟨∑ i, ∑ j, c i * d j * αGramZ i j, ?_⟩
  simp only [inner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp_rw [αGramZ_cast, inner]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## Reflection closure -/

/-- The E8 lattice is closed under reflection in any of its norm-two vectors. -/
theorem rootReflection_mem_E8Lattice {a x : Fin 8 → ℚ}
    (ha : a ∈ rootsOf E8Lattice) (hx : x ∈ E8Lattice) :
    rootReflection a x ∈ E8Lattice := by
  obtain ⟨z, hz⟩ := inner_e8Lattice_isInt hx ha.1
  rw [rootReflection, hz]
  exact e8Lattice_sub_zsmul_mem hx ha.1 z

/-- The E8 root set is closed under every root reflection. -/
theorem rootReflection_mem_rootsOf_E8 {a x : Fin 8 → ℚ}
    (ha : a ∈ rootsOf E8Lattice) (hx : x ∈ rootsOf E8Lattice) :
    rootReflection a x ∈ rootsOf E8Lattice := by
  refine ⟨rootReflection_mem_E8Lattice ha hx.1, ?_⟩
  rw [inner_rootReflection_self ha.2, hx.2]

/-- Reflection closure descends to E7 because both root and reflected vector satisfy
the coordinate equation `x 0 = x 1`. -/
theorem rootReflection_mem_rootsOf_E7 {a x : Fin 8 → ℚ}
    (ha : a ∈ rootsOf E7Lattice) (hx : x ∈ rootsOf E7Lattice) :
    rootReflection a x ∈ rootsOf E7Lattice := by
  have ha8 : a ∈ rootsOf E8Lattice := ⟨ha.1.1, ha.2⟩
  have hx8 : x ∈ rootsOf E8Lattice := ⟨hx.1.1, hx.2⟩
  refine ⟨⟨(rootReflection_mem_rootsOf_E8 ha8 hx8).1, ?_⟩,
    (rootReflection_mem_rootsOf_E8 ha8 hx8).2⟩
  simp only [rootReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ha.1.2, hx.1.2]

/-- Reflection closure descends to E6 because its two coordinate equations are linear. -/
theorem rootReflection_mem_rootsOf_E6 {a x : Fin 8 → ℚ}
    (ha : a ∈ rootsOf E6Lattice) (hx : x ∈ rootsOf E6Lattice) :
    rootReflection a x ∈ rootsOf E6Lattice := by
  have ha8 : a ∈ rootsOf E8Lattice := ⟨ha.1.1, ha.2⟩
  have hx8 : x ∈ rootsOf E8Lattice := ⟨hx.1.1, hx.2⟩
  refine ⟨⟨(rootReflection_mem_rootsOf_E8 ha8 hx8).1, ?_, ?_⟩,
    (rootReflection_mem_rootsOf_E8 ha8 hx8).2⟩
  · simp only [rootReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha.1.2.1, hx.1.2.1]
  · simp only [rootReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha.1.2.2, hx.1.2.2]

/-! ## Explicit compatible simple systems and their Dynkin types -/

/-- Seven explicit E7 roots. Their Gram graph below is the standard E7 Dynkin graph. -/
def E7Simple : Fin 7 → (Fin 8 → ℚ)
  | 0 => intVec 3 5 true true
  | 1 => halfVec ![true, true, false, false, false, false, false, false]
  | 2 => intVec 0 1 false false
  | 3 => halfVec ![true, true, false, false, true, true, true, true]
  | 4 => intVec 2 6 true false
  | 5 => intVec 6 7 true false
  | 6 => halfVec ![true, true, true, true, false, false, true, true]

/-- Six explicit E6 roots. Their Gram graph below is the standard E6 Dynkin graph. -/
def E6Simple : Fin 6 → (Fin 8 → ℚ)
  | 0 => halfVec ![false, false, false, true, false, true, true, true]
  | 1 => intVec 4 5 true false
  | 2 => intVec 3 4 false false
  | 3 => intVec 4 5 true true
  | 4 => halfVec ![true, true, true, true, false, false, true, true]
  | 5 => intVec 3 6 true false

set_option maxRecDepth 4000 in
/-- Every member of `E7Simple` is a root of the E7 lattice. -/
theorem E7Simple_mem (i : Fin 7) : E7Simple i ∈ rootsOf E7Lattice := by
  fin_cases i
  all_goals
    simp only [E7Simple]
    refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (intVec'_mem_rootsOf_E8 (3, 5, true, true) (by decide)).1
  · decide
  · exact inner_intVec 3 5 true true (by decide)
  · exact (halfVec_mem_rootsOf_E8 _ (by decide)).1
  · rw [halfVec_eq_iff]
    decide
  · exact inner_halfVec _
  · exact (intVec'_mem_rootsOf_E8 (0, 1, false, false) (by decide)).1
  · decide
  · exact inner_intVec 0 1 false false (by decide)
  · exact (halfVec_mem_rootsOf_E8 _ (by decide)).1
  · rw [halfVec_eq_iff]
    decide
  · exact inner_halfVec _
  · exact (intVec'_mem_rootsOf_E8 (2, 6, true, false) (by decide)).1
  · decide
  · exact inner_intVec 2 6 true false (by decide)
  · exact (intVec'_mem_rootsOf_E8 (6, 7, true, false) (by decide)).1
  · decide
  · exact inner_intVec 6 7 true false (by decide)
  · exact (halfVec_mem_rootsOf_E8 _ (by decide)).1
  · rw [halfVec_eq_iff]
    decide
  · exact inner_halfVec _

set_option maxRecDepth 4000 in
/-- Every member of `E6Simple` is a root of the E6 lattice. -/
theorem E6Simple_mem (i : Fin 6) : E6Simple i ∈ rootsOf E6Lattice := by
  fin_cases i
  all_goals
    simp only [E6Simple]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (halfVec_mem_rootsOf_E8 _ (by decide)).1
  · rw [halfVec_eq_iff]
    decide
  · rw [halfVec_eq_iff]
    decide
  · exact inner_halfVec _
  · exact (intVec'_mem_rootsOf_E8 (4, 5, true, false) (by decide)).1
  · decide
  · decide
  · exact inner_intVec 4 5 true false (by decide)
  · exact (intVec'_mem_rootsOf_E8 (3, 4, false, false) (by decide)).1
  · decide
  · decide
  · exact inner_intVec 3 4 false false (by decide)
  · exact (intVec'_mem_rootsOf_E8 (4, 5, true, true) (by decide)).1
  · decide
  · decide
  · exact inner_intVec 4 5 true true (by decide)
  · exact (halfVec_mem_rootsOf_E8 _ (by decide)).1
  · rw [halfVec_eq_iff]
    decide
  · rw [halfVec_eq_iff]
    decide
  · exact inner_halfVec _
  · exact (intVec'_mem_rootsOf_E8 (3, 6, true, false) (by decide)).1
  · decide
  · decide
  · exact inner_intVec 3 6 true false (by decide)

/-- Adjacency matrix extracted from a norm-two simple-root family. -/
def simpleRootAdj {n : ℕ} (b : Fin n → (Fin 8 → ℚ)) (i j : Fin n) : ℤ :=
  if i = j then 0 else -(inner (b i) (b j)).num

/-- Expand the coordinate inner product so the finite Gram computations below are checked by
the kernel rather than by a native-code evaluator. -/
private lemma inner_eq_eight (x y : Fin 8 → ℚ) :
    inner x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3
      + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7 := by
  simp only [inner, Fin.sum_univ_eight]

set_option maxRecDepth 10000 in
/-- The explicit E7 simple roots have exactly the standard E7 Dynkin Gram graph. -/
theorem E7Simple_gram_type :
    ∀ i j, simpleRootAdj E7Simple i j = DynkinType.E7.adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [simpleRootAdj, E7Simple, intVec, coordZ, halfVec, inner_eq_eight,
      DynkinType.adj, Fin.reduceEq, reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    norm_num

set_option maxRecDepth 10000 in
/-- The explicit E6 simple roots have exactly the standard E6 Dynkin Gram graph. -/
theorem E6Simple_gram_type :
    ∀ i j, simpleRootAdj E6Simple i j = DynkinType.E6.adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [simpleRootAdj, E6Simple, intVec, coordZ, halfVec, inner_eq_eight,
      DynkinType.adj, Fin.reduceEq, reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    norm_num

/-- Each of the original eight basis vectors `alpha_i` is an E8 root. -/
theorem α_mem_rootsOf_E8 (i : Fin 8) : α i ∈ rootsOf E8Lattice := by
  refine ⟨?_, α_norm_two i⟩
  have hmem := α_isBasis.2 (fun j => if j = i then 1 else 0)
  simpa only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using hmem

/-! ## The three root-system endpoints -/

private theorem neg_mem_rootsOf_E8 {a : Fin 8 → ℚ} (ha : a ∈ rootsOf E8Lattice) :
    -a ∈ rootsOf E8Lattice := by
  refine ⟨e8Lattice_neg_mem ha.1, ?_⟩
  simpa only [inner, Pi.neg_apply, neg_mul_neg] using ha.2

private theorem neg_mem_rootsOf_E7 {a : Fin 8 → ℚ} (ha : a ∈ rootsOf E7Lattice) :
    -a ∈ rootsOf E7Lattice := by
  refine ⟨⟨e8Lattice_neg_mem ha.1.1, ?_⟩, ?_⟩
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2
  · simpa only [inner, Pi.neg_apply, neg_mul_neg] using ha.2

private theorem neg_mem_rootsOf_E6 {a : Fin 8 → ℚ} (ha : a ∈ rootsOf E6Lattice) :
    -a ∈ rootsOf E6Lattice := by
  refine ⟨⟨e8Lattice_neg_mem ha.1.1, ?_, ?_⟩, ?_⟩
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2.1
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2.2
  · simpa only [inner, Pi.neg_apply, neg_mul_neg] using ha.2

/-- The 240 norm-two vectors of the E8 lattice form a finite reduced simply-laced
crystallographic root system. -/
theorem rootsOf_E8_isRootSystem :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E8Lattice) where
  finite := Set.finite_of_ncard_ne_zero (by rw [E8_root_count]; norm_num)
  norm_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E8 ha
  reduced := fun _ ha q hqa => scalar_eq_one_or_neg_one_of_norm_two ha.2 hqa.2
  integral_pairing := fun _ ha _ hb => inner_e8Lattice_isInt ha.1 hb.1
  reflection_mem := fun _ ha _ hb => rootReflection_mem_rootsOf_E8 ha hb

/-- The 126 norm-two vectors of the E7 sublattice form a finite reduced simply-laced
crystallographic root system. -/
theorem rootsOf_E7_isRootSystem :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E7Lattice) where
  finite := Set.finite_of_ncard_ne_zero (by rw [E7_root_count]; norm_num)
  norm_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E7 ha
  reduced := fun _ ha q hqa => scalar_eq_one_or_neg_one_of_norm_two ha.2 hqa.2
  integral_pairing := fun _ ha _ hb => inner_e8Lattice_isInt ha.1.1 hb.1.1
  reflection_mem := fun _ ha _ hb => rootReflection_mem_rootsOf_E7 ha hb

/-- The 72 norm-two vectors of the E6 sublattice form a finite reduced simply-laced
crystallographic root system. -/
theorem rootsOf_E6_isRootSystem :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E6Lattice) where
  finite := Set.finite_of_ncard_ne_zero (by rw [E6_root_count]; norm_num)
  norm_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E6 ha
  reduced := fun _ ha q hqa => scalar_eq_one_or_neg_one_of_norm_two ha.2 hqa.2
  integral_pairing := fun _ ha _ hb => inner_e8Lattice_isInt ha.1.1 hb.1.1
  reflection_mem := fun _ ha _ hb => rootReflection_mem_rootsOf_E6 ha hb

/-! ## Type-identification capstones -/

/-- **Problem 6.9.2(b), full root-system endpoint.** The norm-two vectors in the E8 lattice
form a root system, contain the chosen lattice basis as simple roots, and that simple family has
the E8 Dynkin Gram graph. -/
theorem rootsOf_E8_type_E8 :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E8Lattice) ∧
      (∀ i, α i ∈ rootsOf E8Lattice) ∧
      IsDynkinDiagram 8 gramAdj ∧
      ∃ σ : Fin 8 ≃ Fin 8,
        ∀ i j, gramAdj (σ i) (σ j) = DynkinType.E8.adj i j :=
  ⟨rootsOf_E8_isRootSystem, α_mem_rootsOf_E8, α_gram_is_E8⟩

/-- **Problem 6.9.2(c), E7 type endpoint.** The E7 coordinate-equality sublattice has a
reflection-closed root system with the explicit `E7Simple` family and standard E7 Gram graph. -/
theorem rootsOf_E7_type_E7 :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E7Lattice) ∧
      (∀ i, E7Simple i ∈ rootsOf E7Lattice) ∧
      simpleRootAdj E7Simple = DynkinType.E7.adj ∧
      IsDynkinDiagram 7 (simpleRootAdj E7Simple) := by
  have hAdj : simpleRootAdj E7Simple = DynkinType.E7.adj := by
    funext i j
    exact E7Simple_gram_type i j
  exact ⟨rootsOf_E7_isRootSystem, E7Simple_mem, hAdj,
    hAdj.symm ▸ isDynkinDiagram_of_type .E7⟩

/-- **Problem 6.9.2(c), E6 type endpoint.** The E6 coordinate-equality sublattice has a
reflection-closed root system with the explicit `E6Simple` family and standard E6 Gram graph. -/
theorem rootsOf_E6_type_E6 :
    IsSimplyLacedCrystallographicRootSystem (rootsOf E6Lattice) ∧
      (∀ i, E6Simple i ∈ rootsOf E6Lattice) ∧
      simpleRootAdj E6Simple = DynkinType.E6.adj ∧
      IsDynkinDiagram 6 (simpleRootAdj E6Simple) := by
  have hAdj : simpleRootAdj E6Simple = DynkinType.E6.adj := by
    funext i j
    exact E6Simple_gram_type i j
  exact ⟨rootsOf_E6_isRootSystem, E6Simple_mem, hAdj,
    hAdj.symm ▸ isDynkinDiagram_of_type .E6⟩

end Etingof.Problem6_9_2
