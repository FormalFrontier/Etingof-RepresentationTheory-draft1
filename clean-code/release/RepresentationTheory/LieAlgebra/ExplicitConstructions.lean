/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import RepresentationTheory.Alignment.Attribute

/-! # Explicit constructions -/


namespace RepresentationTheory.LieAlgebra.ExplicitConstructions

open FreeLieAlgebra

variable (k : Type*) [CommRing k]


/-- A distinguished element of the displayed free Lie algebra. -/
noncomputable def freeLieElement_aux3 : FreeLieAlgebra k (Fin 2) := FreeLieAlgebra.of k 0


/-- A distinguished element of the displayed free Lie algebra. -/
noncomputable def freeLieElement_aux4 : FreeLieAlgebra k (Fin 2) := FreeLieAlgebra.of k 1


/-- An indexed Lie ideal in the displayed free Lie algebra. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
noncomputable def indexedLieIdeal (n : ℕ) : LieIdeal k (FreeLieAlgebra k (Fin 2)) :=
  LieSubmodule.lieSpan k (FreeLieAlgebra k (Fin 2))
    {⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆, (fun z => ⁅freeLieElement_aux4 k, z⁆)^[n + 1] (freeLieElement_aux3 k)}


/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
noncomputable def AuxiliaryType (n : ℕ) : Type _ := FreeLieAlgebra k (Fin 2) ⧸ indexedLieIdeal k n

/-- Provides the indicated LieRing structure on the specified type. -/
noncomputable instance instLieRing (n : ℕ) : LieRing (AuxiliaryType k n) :=
  inferInstanceAs (LieRing (_ ⧸ indexedLieIdeal k n))

/-- Provides the indicated LieAlgebra structure on the specified type. -/
noncomputable instance instLieAlgebra (n : ℕ) : LieAlgebra k (AuxiliaryType k n) :=
  inferInstanceAs (LieAlgebra k (_ ⧸ indexedLieIdeal k n))


open FreeLieAlgebra in

/-- The displayed expressions in the free Lie algebra are equal. -/
theorem freeLie_eq :
    LieSubalgebra.lieSpan k (FreeLieAlgebra k (Fin 2)) (Set.range (FreeLieAlgebra.of k)) = ⊤ := by
  set H := LieSubalgebra.lieSpan k (FreeLieAlgebra k (Fin 2)) (Set.range (FreeLieAlgebra.of k))
    with hH
  rw [eq_top_iff]
  intro a _

  let ι : Fin 2 → H := fun i => ⟨FreeLieAlgebra.of k i, LieSubalgebra.subset_lieSpan ⟨i, rfl⟩⟩
  let φ : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ H := FreeLieAlgebra.lift k ι
  have hcomp : H.incl.comp φ = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp only [LieHom.comp_apply, φ, FreeLieAlgebra.lift_of_apply, LieHom.id_apply]
    rfl
  have ha : a = H.incl (φ a) := (LieHom.congr_fun hcomp a).symm
  rw [ha]
  exact (φ a).2


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
noncomputable def lieHom_aux5 (n : ℕ) : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ AuxiliaryType k n :=
  { (LieSubmodule.Quotient.mk' (indexedLieIdeal k n)).toLinearMap with
    map_lie' := fun {_ _} => rfl }


/-- The Lie homomorphism agrees on every free-Lie element with the quotient map by the displayed Lie ideal. -/
@[simp] theorem lieHom_apply_eq_quotient_mk (n : ℕ) (a : FreeLieAlgebra k (Fin 2)) :
    lieHom_aux5 k n a = LieSubmodule.Quotient.mk' (indexedLieIdeal k n) a := rfl


/-- The displayed map is surjective. -/
theorem map_surjective (n : ℕ) : Function.Surjective (lieHom_aux5 k n) :=
  LieSubmodule.Quotient.surjective_mk' _


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux7 (n : ℕ) : AuxiliaryType k n := lieHom_aux5 k n (freeLieElement_aux3 k)

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux8 (n : ℕ) : AuxiliaryType k n := lieHom_aux5 k n (freeLieElement_aux4 k)

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux9 (n : ℕ) : AuxiliaryType k n := ⁅distinguishedElement_aux7 k n, distinguishedElement_aux8 k n⁆


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux71 (n : ℕ) : distinguishedElement_aux9 k n = lieHom_aux5 k n ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆ := by
  simp only [distinguishedElement_aux9, distinguishedElement_aux7, distinguishedElement_aux8, LieHom.map_lie]


/-- The two displayed expressions are equal. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
theorem displayed_eq_aux4 (n : ℕ) :
    LieSubalgebra.lieSpan k (AuxiliaryType k n) {distinguishedElement_aux7 k n, distinguishedElement_aux8 k n} = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  obtain ⟨b, rfl⟩ := map_surjective k n a
  have hb : b ∈ LieSubalgebra.lieSpan k (FreeLieAlgebra k (Fin 2))
      (Set.range (FreeLieAlgebra.of k)) := by
    rw [freeLie_eq]; trivial
  induction hb using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    fin_cases i
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  | zero => rw [map_zero]; exact LieSubalgebra.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact LieSubalgebra.add_mem _ hu hv
  | smul t u _ hu => rw [map_smul]; exact LieSubalgebra.smul_mem _ t hu
  | lie u v _ _ hu hv => rw [LieHom.map_lie]; exact LieSubalgebra.lie_mem _ hu hv


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux3 (n : ℕ) (M : Submodule k (AuxiliaryType k n))
    (hx : distinguishedElement_aux7 k n ∈ M) (hy : distinguishedElement_aux8 k n ∈ M)
    (hadx : ∀ m ∈ M, ⁅distinguishedElement_aux7 k n, m⁆ ∈ M) (hady : ∀ m ∈ M, ⁅distinguishedElement_aux8 k n, m⁆ ∈ M) :
    M = ⊤ := by
  have hall : ∀ a : AuxiliaryType k n, ∀ m ∈ M, ⁅a, m⁆ ∈ M := by
    let N : LieSubalgebra k (AuxiliaryType k n) :=
      { carrier := {a | ∀ m ∈ M, ⁅a, m⁆ ∈ M}
        add_mem' := fun ha hb m hm => by rw [add_lie]; exact M.add_mem (ha m hm) (hb m hm)
        zero_mem' := fun m _ => by rw [zero_lie]; exact M.zero_mem
        smul_mem' := fun c _ ha m hm => by rw [smul_lie]; exact M.smul_mem c (ha m hm)
        lie_mem' := fun ha hb m hm => by
          rw [lie_lie]; exact M.sub_mem (ha _ (hb m hm)) (hb _ (ha m hm)) }
    have hN : N = ⊤ := by
      rw [← top_le_iff, ← displayed_eq_aux4 k n, LieSubalgebra.lieSpan_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hadx
      · exact hady
    intro a
    have ha : a ∈ N := by rw [hN]; trivial
    exact ha
  let W : LieSubalgebra k (AuxiliaryType k n) := { M with lie_mem' := fun {u v} _ hv => hall u v hv }
  have hW : W = ⊤ := by
    rw [← top_le_iff, ← displayed_eq_aux4 k n, LieSubalgebra.lieSpan_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hy
  have := congrArg LieSubalgebra.toSubmodule hW
  simpa [W] using this


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux2 (n : ℕ) (S : Set (AuxiliaryType k n))
    (hx : distinguishedElement_aux7 k n ∈ S) (hy : distinguishedElement_aux8 k n ∈ S)
    (hadx : ∀ s ∈ S, ⁅distinguishedElement_aux7 k n, s⁆ ∈ Submodule.span k S)
    (hady : ∀ s ∈ S, ⁅distinguishedElement_aux8 k n, s⁆ ∈ Submodule.span k S) :
    Submodule.span k S = ⊤ := by
  refine displayed_eq_aux3 k n _ (Submodule.subset_span hx) (Submodule.subset_span hy)
    ?_ ?_
  · intro m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact hadx s hs
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [lie_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha
  · intro m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact hady s hs
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [lie_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux13 (n : ℕ) (a : FreeLieAlgebra k (Fin 2)) :
    lieHom_aux5 k n a = 0 ↔ a ∈ indexedLieIdeal k n := by
  rw [lieHom_apply_eq_quotient_mk]; exact LieSubmodule.Quotient.mk_eq_zero _


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux15 (n : ℕ) : ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ ∈ indexedLieIdeal k n :=
  LieSubmodule.subset_lieSpan (Set.mem_insert _ _)


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux43 (n : ℕ) : ⁅distinguishedElement_aux7 k n, distinguishedElement_aux9 k n⁆ = 0 := by
  have h : ⁅distinguishedElement_aux7 k n, distinguishedElement_aux9 k n⁆ = lieHom_aux5 k n ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ := by
    simp only [distinguishedElement_aux7, distinguishedElement_aux8, distinguishedElement_aux9, LieHom.map_lie]
  rw [h, mem_submodule_aux13]
  exact mem_submodule_aux15 k n


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux49 : ⁅distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1⁆ = lieHom_aux5 k 1 ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ := by
    simp only [distinguishedElement_aux7, distinguishedElement_aux8, distinguishedElement_aux9, LieHom.map_lie]
  rw [h, mem_submodule_aux13]
  have hmem : (fun z => ⁅freeLieElement_aux4 k, z⁆)^[1 + 1] (freeLieElement_aux3 k) ∈ indexedLieIdeal k 1 :=
    LieSubmodule.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  have heq : ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = -(fun z => ⁅freeLieElement_aux4 k, z⁆)^[1 + 1] (freeLieElement_aux3 k) := by
    change ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = -⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆
    rw [← lie_skew (x := freeLieElement_aux3 k) (y := freeLieElement_aux4 k), lie_neg]
  rw [heq]; exact neg_mem hmem

section Matrix
attribute [local instance] LieRing.ofAssociativeRing


private noncomputable def E01 : Matrix (Fin 3) (Fin 3) k := Matrix.single 0 1 1

private noncomputable def E12 : Matrix (Fin 3) (Fin 3) k := Matrix.single 1 2 1

private noncomputable def E02 : Matrix (Fin 3) (Fin 3) k := Matrix.single 0 2 1


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ Matrix (Fin 3) (Fin 3) k :=
  FreeLieAlgebra.lift k ![E01 k, E12 k]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux8 : lieHom k (freeLieElement_aux3 k) = E01 k := by
  simp only [lieHom, freeLieElement_aux3, FreeLieAlgebra.lift_of_apply]; rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux9 : lieHom k (freeLieElement_aux4 k) = E12 k := by
  simp only [lieHom, freeLieElement_aux4, FreeLieAlgebra.lift_of_apply]; rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux1 : ⁅E01 k, E12 k⁆ = E02 k := by
  simp only [E01, E12, E02, LieRing.of_associative_ring_bracket]
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux56 : lieHom k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = 0 := by
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux8, map_apply_aux9, bracket_eq_aux1]
  simp only [E01, E02, LieRing.of_associative_ring_bracket]
  simp [Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux57 : lieHom k ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[1 + 1] (freeLieElement_aux3 k)) = 0 := by
  change lieHom k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆ = 0
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux8, map_apply_aux9]
  have hbr : ⁅E12 k, E01 k⁆ = -E02 k := by
    simp only [E01, E12, E02, LieRing.of_associative_ring_bracket]
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]
  rw [hbr]
  simp only [E12, E02, LieRing.of_associative_ring_bracket]
  simp [Matrix.single_mul_single_of_ne, mul_neg, neg_mul]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le_aux1 : indexedLieIdeal k 1 ≤ (lieHom k).ker := by
  rw [indexedLieIdeal, LieSubmodule.lieSpan_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux56 k
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux57 k


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family : LinearIndependent k ![distinguishedElement_aux7 k 1, distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hc

  have hpw : lieHom_aux5 k 1 (c 0 • freeLieElement_aux3 k + c 1 • freeLieElement_aux4 k + c 2 • ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆) = 0 := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, LieHom.map_lie]
    exact hc
  have hmem := (mem_submodule_aux13 k 1 _).mp hpw
  have hker := submodule_le_aux1 k hmem
  rw [LieHom.mem_ker, map_add, map_add, map_smul, map_smul, map_smul, LieHom.map_lie,
    map_apply_aux8, map_apply_aux9, bracket_eq_aux1] at hker

  simp only [E01, E12, E02] at hker
  intro i
  fin_cases i
  · have := congrFun (congrFun hker 0) 1
    simpa [Matrix.add_apply, Matrix.smul_apply] using this
  · have := congrFun (congrFun hker 1) 2
    simpa [Matrix.add_apply, Matrix.smul_apply] using this
  · have := congrFun (congrFun hker 0) 2
    simpa [Matrix.add_apply, Matrix.smul_apply] using this

end Matrix


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux3 :
    Submodule.span k {distinguishedElement_aux7 k 1, distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1} = ⊤ := by
  have hz : distinguishedElement_aux9 k 1 ∈ ({distinguishedElement_aux7 k 1, distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1} : Set (AuxiliaryType k 1)) := by simp
  refine submodule_eq_aux2 k 1 _ (by simp) (by simp) ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [lie_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hz
    · rw [bracket_eq_aux43]; exact Submodule.zero_mem _
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [← lie_skew (x := distinguishedElement_aux8 k 1) (y := distinguishedElement_aux7 k 1)]
      exact neg_mem (Submodule.subset_span hz)
    · rw [lie_self]; exact Submodule.zero_mem _
    · rw [bracket_eq_aux49]; exact Submodule.zero_mem _


/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.16.3" (role := primary)]
theorem finrank_eq (k : Type*) [Field k] : Module.finrank k (AuxiliaryType k 1) = 3 := by
  have hspan : ⊤ ≤ Submodule.span k (Set.range ![distinguishedElement_aux7 k 1, distinguishedElement_aux8 k 1, distinguishedElement_aux9 k 1]) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union,
      Set.singleton_union, submodule_eq_aux3]
  let b : Module.Basis (Fin 3) k (AuxiliaryType k 1) := Module.Basis.mk (linearIndependent_family k) hspan
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux6 (n : ℕ) : AuxiliaryType k n := ⁅distinguishedElement_aux8 k n, distinguishedElement_aux9 k n⁆


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux48 : ⁅distinguishedElement_aux8 k 2, distinguishedElement_aux6 k 2⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 2, distinguishedElement_aux6 k 2⁆ = lieHom_aux5 k 2 ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆ := by
    simp only [distinguishedElement_aux6, distinguishedElement_aux7, distinguishedElement_aux8, distinguishedElement_aux9, LieHom.map_lie]
  rw [h, mem_submodule_aux13]
  have hmem : (fun z => ⁅freeLieElement_aux4 k, z⁆)^[2 + 1] (freeLieElement_aux3 k) ∈ indexedLieIdeal k 2 :=
    LieSubmodule.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  have heq : ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆ = -(fun z => ⁅freeLieElement_aux4 k, z⁆)^[2 + 1] (freeLieElement_aux3 k) := by
    change ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆ = -⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆
    rw [← lie_skew (x := freeLieElement_aux3 k) (y := freeLieElement_aux4 k), lie_neg, lie_neg]
  rw [heq]; exact neg_mem hmem


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux42 : ⁅distinguishedElement_aux7 k 2, distinguishedElement_aux6 k 2⁆ = 0 := by
  have hz : ⁅distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2⁆ = distinguishedElement_aux9 k 2 := rfl
  rw [distinguishedElement_aux6, leibniz_lie, hz, lie_self, bracket_eq_aux43, lie_zero, add_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux54 : ⁅distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2⁆ = 0 := by
  have hz : distinguishedElement_aux9 k 2 = ⁅distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2⁆ := rfl
  rw [hz, lie_lie, bracket_eq_aux48, bracket_eq_aux42, lie_zero, lie_zero, sub_zero]

section Matrix2
attribute [local instance] LieRing.ofAssociativeRing


private noncomputable def MX : Matrix (Fin 5) (Fin 5) k :=
  Matrix.single 0 1 1 - Matrix.single 3 4 1

private noncomputable def MY : Matrix (Fin 5) (Fin 5) k :=
  Matrix.single 1 2 1 - Matrix.single 2 3 1

private noncomputable def MZ : Matrix (Fin 5) (Fin 5) k :=
  Matrix.single 0 2 1 - Matrix.single 2 4 1

private noncomputable def MW : Matrix (Fin 5) (Fin 5) k :=
  Matrix.single 0 3 1 - Matrix.single 1 4 1


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux1 : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ Matrix (Fin 5) (Fin 5) k :=
  FreeLieAlgebra.lift k ![MX k, MY k]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux10 : lieHom_aux1 k (freeLieElement_aux3 k) = MX k := by
  simp only [lieHom_aux1, freeLieElement_aux3, FreeLieAlgebra.lift_of_apply]; rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux11 : lieHom_aux1 k (freeLieElement_aux4 k) = MY k := by
  simp only [lieHom_aux1, freeLieElement_aux4, FreeLieAlgebra.lift_of_apply]; rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux8 : ⁅MX k, MY k⁆ = MZ k := by
  simp only [MX, MY, MZ, LieRing.of_associative_ring_bracket, sub_mul, mul_sub]
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux11 : ⁅MY k, MZ k⁆ = MW k := by
  simp only [MY, MZ, MW, LieRing.of_associative_ring_bracket, sub_mul, mul_sub]
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux9 : ⁅MX k, MZ k⁆ = 0 := by
  simp only [MX, MZ, LieRing.of_associative_ring_bracket, sub_mul, mul_sub]
  simp [Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux10 : ⁅MY k, MW k⁆ = 0 := by
  simp only [MY, MW, LieRing.of_associative_ring_bracket, sub_mul, mul_sub]
  simp [Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux58 : lieHom_aux1 k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = 0 := by
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux10, map_apply_aux11, bracket_eq_aux8, bracket_eq_aux9]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux59 : lieHom_aux1 k ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[2 + 1] (freeLieElement_aux3 k)) = 0 := by
  change lieHom_aux1 k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆ = 0
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, map_apply_aux10, map_apply_aux11]
  have h1 : ⁅MY k, MX k⁆ = -MZ k := by rw [← lie_skew, bracket_eq_aux8]
  rw [h1, lie_neg, bracket_eq_aux11, lie_neg, bracket_eq_aux10, neg_zero]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le_aux2 : indexedLieIdeal k 2 ≤ (lieHom_aux1 k).ker := by
  rw [indexedLieIdeal, LieSubmodule.lieSpan_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux58 k
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux59 k


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux2 : LinearIndependent k ![distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2, distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_four] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons] at hc

  have hpw : lieHom_aux5 k 2 (c 0 • freeLieElement_aux3 k + c 1 • freeLieElement_aux4 k + c 2 • ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆ +
      c 3 • ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆) = 0 := by
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      LieHom.map_lie, LieHom.map_lie, LieHom.map_lie]
    exact hc
  have hmem := (mem_submodule_aux13 k 2 _).mp hpw
  have hker := submodule_le_aux2 k hmem
  rw [LieHom.mem_ker, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, map_apply_aux10, map_apply_aux11,
    bracket_eq_aux8, bracket_eq_aux11] at hker

  simp only [MX, MY, MZ, MW] at hker
  intro i
  fin_cases i
  · have := congrFun (congrFun hker 0) 1
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] using this
  · have := congrFun (congrFun hker 1) 2
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] using this
  · have := congrFun (congrFun hker 0) 2
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] using this
  · have := congrFun (congrFun hker 0) 3
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] using this

end Matrix2


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux5 :
    Submodule.span k {distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2, distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2} = ⊤ := by
  have hz : distinguishedElement_aux9 k 2 ∈ ({distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2, distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2} : Set (AuxiliaryType k 2)) := by simp
  have hw : distinguishedElement_aux6 k 2 ∈ ({distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2, distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2} : Set (AuxiliaryType k 2)) := by simp
  refine submodule_eq_aux2 k 2 _ (by simp) (by simp) ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [lie_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hz
    · rw [bracket_eq_aux43]; exact Submodule.zero_mem _
    · rw [bracket_eq_aux42]; exact Submodule.zero_mem _
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [← lie_skew (x := distinguishedElement_aux8 k 2) (y := distinguishedElement_aux7 k 2)]
      exact neg_mem (Submodule.subset_span hz)
    · rw [lie_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hw
    · rw [bracket_eq_aux48]; exact Submodule.zero_mem _


/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.16.3" (role := primary)]
theorem finrank_eq_aux2 (k : Type*) [Field k] : Module.finrank k (AuxiliaryType k 2) = 4 := by
  have hspan : ⊤ ≤ Submodule.span k (Set.range ![distinguishedElement_aux7 k 2, distinguishedElement_aux8 k 2, distinguishedElement_aux9 k 2, distinguishedElement_aux6 k 2]) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons_empty,
      Set.singleton_union, Set.singleton_union, Set.singleton_union, submodule_eq_aux5]
  let b : Module.Basis (Fin 4) k (AuxiliaryType k 2) := Module.Basis.mk (linearIndependent_family_aux2 k) hspan
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]


section Matrix4
attribute [local instance] LieRing.ofAssociativeRing

open Polynomial


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux4 : Matrix (Fin 3) (Fin 3) (Polynomial k) := Matrix.single 2 0 Polynomial.X

/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux6 : Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  Matrix.single 0 1 1 - Matrix.single 1 2 1


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux3 :
    FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  FreeLieAlgebra.lift k ![matrix_aux4 k, matrix_aux6 k]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux14 : lieHom_aux3 k (freeLieElement_aux3 k) = matrix_aux4 k := by
  simp only [lieHom_aux3, freeLieElement_aux3, FreeLieAlgebra.lift_of_apply]; rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux15 : lieHom_aux3 k (freeLieElement_aux4 k) = matrix_aux6 k := by
  simp only [lieHom_aux3, freeLieElement_aux4, FreeLieAlgebra.lift_of_apply]; rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux62 : lieHom_aux3 k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = 0 := by
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux14, map_apply_aux15]
  simp [matrix_aux4, matrix_aux6, LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_add, add_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux63 : lieHom_aux3 k ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[4 + 1] (freeLieElement_aux3 k)) = 0 := by
  change lieHom_aux3 k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆⁆ = 0
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
    map_apply_aux14, map_apply_aux15]
  simp [matrix_aux4, matrix_aux6, LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_add, add_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le_aux4 : indexedLieIdeal k 4 ≤ (lieHom_aux3 k).ker := by
  rw [indexedLieIdeal, LieSubmodule.lieSpan_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux62 k
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux63 k


/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux2 : AuxiliaryType k 4 →ₗ[k] Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  Submodule.liftQ (indexedLieIdeal k 4).toSubmodule (lieHom_aux3 k).toLinearMap
    (fun a ha => by
      rw [LinearMap.mem_ker]
      have hmem : a ∈ indexedLieIdeal k 4 := ha
      have := submodule_le_aux4 k hmem
      rwa [LieHom.mem_ker] at this)


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux7 :
    LinearMap.range (linearMap_aux2 k) = LinearMap.range (lieHom_aux3 k).toLinearMap :=
  Submodule.range_liftQ _ _ _


/-- Finite generation of the domain implies finite generation of the displayed linear-map range. -/
theorem range_finite_of_domain_finite (h : Module.Finite k (AuxiliaryType k 4)) :
    Module.Finite k (LinearMap.range (lieHom_aux3 k).toLinearMap) := by
  rw [← displayed_eq_aux7]
  exact Module.Finite.range (linearMap_aux2 k)


/-- Non-finiteness of the displayed linear-map range implies non-finiteness of the ambient module. -/
theorem not_moduleFinite_of_range
    (h : ¬ Module.Finite k (LinearMap.range (lieHom_aux3 k).toLinearMap)) :
    ¬ Module.Finite k (AuxiliaryType k 4) :=
  fun hfin => h (range_finite_of_domain_finite k hfin)

end Matrix4


section Matrix4c
attribute [local instance] LieRing.ofAssociativeRing

open Polynomial


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux5 : Matrix (Fin 4) (Fin 4) (Polynomial k) :=
  Matrix.single 1 3 Polynomial.X + Matrix.single 3 2 Polynomial.X

/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux7 : Matrix (Fin 4) (Fin 4) (Polynomial k) :=
  Matrix.single 0 2 1 + Matrix.single 2 3 2 + Matrix.single 3 1 1


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux4 :
    FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ Matrix (Fin 4) (Fin 4) (Polynomial k) :=
  FreeLieAlgebra.lift k ![matrix_aux5 k, matrix_aux7 k]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux16 : lieHom_aux4 k (freeLieElement_aux3 k) = matrix_aux5 k := by
  simp only [lieHom_aux4, freeLieElement_aux3, FreeLieAlgebra.lift_of_apply]; rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux17 : lieHom_aux4 k (freeLieElement_aux4 k) = matrix_aux7 k := by
  simp only [lieHom_aux4, freeLieElement_aux4, FreeLieAlgebra.lift_of_apply]; rfl


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux18 (h3 : (3 : k) = 0) : (3 : Polynomial k) = 0 := by
  rw [← map_ofNat (Polynomial.C : k →+* Polynomial k) 3, h3, map_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux67 (h3 : (3 : k) = 0) : lieHom_aux4 k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = 0 := by
  have h3p := displayed_eq_aux18 k h3
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux16, map_apply_aux17]
  have key : ⁅matrix_aux5 k, ⁅matrix_aux5 k, matrix_aux7 k⁆⁆
      = Matrix.single (3 : Fin 4) (2 : Fin 4) (-3 * Polynomial.X ^ 2) := by
    simp only [matrix_aux5, matrix_aux7, LieRing.of_associative_ring_bracket, mul_add, add_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
      not_false_eq_true]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.sub_apply] <;> ring
  rw [key]
  have hz : (-3 * Polynomial.X ^ 2 : Polynomial k) = 0 := by
    rw [show (-3 * Polynomial.X ^ 2 : Polynomial k) = -(Polynomial.X ^ 2) * 3 by ring, h3p,
      mul_zero]
  rw [hz, Matrix.single_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux68 : lieHom_aux4 k ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[4 + 1] (freeLieElement_aux3 k)) = 0 := by
  change lieHom_aux4 k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆⁆ = 0
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
    map_apply_aux16, map_apply_aux17]
  simp [matrix_aux5, matrix_aux7, LieRing.of_associative_ring_bracket, mul_add, add_mul, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le_aux5 (h3 : (3 : k) = 0) : indexedLieIdeal k 4 ≤ (lieHom_aux4 k).ker := by
  rw [indexedLieIdeal, LieSubmodule.lieSpan_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux67 k h3
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux68 k


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux8 : Matrix (Fin 4) (Fin 4) (Polynomial k) :=
  Matrix.single 1 1 (-1 : Polynomial k) + Matrix.single 2 2 (2 : Polynomial k)
    + Matrix.single 3 3 (-1 : Polynomial k)


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix : Matrix (Fin 4) (Fin 4) (Polynomial k) := Matrix.single 0 2 1


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux18 : ⁅matrix_aux7 k, matrix_aux5 k⁆ = (Polynomial.X : Polynomial k) • matrix_aux8 k := by
  simp only [matrix_aux7, matrix_aux5, matrix_aux8, LieRing.of_associative_ring_bracket, mul_add, add_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
    not_false_eq_true]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux2 : ⁅matrix_aux8 k, matrix k⁆ = (-2 : Polynomial k) • matrix k := by
  simp only [matrix_aux8, matrix, LieRing.of_associative_ring_bracket, mul_add, add_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
    not_false_eq_true]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply]


/-- When three vanishes in the coefficient ring, the displayed iterated bracket advances the polynomial power by one. -/
theorem iteratedBracket_eq_X_smul (h3 : (3 : k) = 0) (m : ℕ) :
    ⁅⁅matrix_aux7 k, matrix_aux5 k⁆, (Polynomial.X : Polynomial k) ^ m • matrix k⁆
      = (Polynomial.X : Polynomial k) ^ (m + 1) • matrix k := by
  rw [bracket_eq_aux18, smul_lie, lie_smul, auxiliary_fact_aux2, smul_smul, smul_smul]
  congr 1
  have hm2 : (-2 : Polynomial k) = 1 := by
    rw [show (-2 : Polynomial k) = 1 - 3 by ring, displayed_eq_aux18 k h3, sub_zero]
  rw [hm2]; ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux66 (h3 : (3 : k) = 0) :
    lieHom_aux4 k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆ = (Polynomial.X : Polynomial k) ^ 2 • matrix k := by
  have h3p := displayed_eq_aux18 k h3
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, map_apply_aux16, map_apply_aux17]
  have e1 : ⁅matrix_aux7 k, matrix_aux5 k⁆
      = Matrix.single (1 : Fin 4) (1 : Fin 4) (-Polynomial.X)
        + Matrix.single (2 : Fin 4) (2 : Fin 4) (2 * Polynomial.X)
        + Matrix.single (3 : Fin 4) (3 : Fin 4) (-Polynomial.X) := by
    simp only [matrix_aux5, matrix_aux7, LieRing.of_associative_ring_bracket, mul_add, add_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
      not_false_eq_true]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.sub_apply] ; ring
  have e2 : ⁅matrix_aux7 k, ⁅matrix_aux7 k, matrix_aux5 k⁆⁆
      = Matrix.single (0 : Fin 4) (2 : Fin 4) (2 * Polynomial.X)
        + Matrix.single (2 : Fin 4) (3 : Fin 4) (-6 * Polynomial.X) := by
    rw [e1]
    simp only [matrix_aux7, LieRing.of_associative_ring_bracket, mul_add, add_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
      not_false_eq_true]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.sub_apply] ; ring
  have e3 : ⁅matrix_aux7 k, ⁅matrix_aux7 k, ⁅matrix_aux7 k, matrix_aux5 k⁆⁆⁆
      = Matrix.single (0 : Fin 4) (3 : Fin 4) (-10 * Polynomial.X)
        + Matrix.single (2 : Fin 4) (1 : Fin 4) (6 * Polynomial.X) := by
    rw [e2]
    simp only [matrix_aux7, LieRing.of_associative_ring_bracket, mul_add, add_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
      not_false_eq_true]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.sub_apply] ; ring

  have key : ⁅matrix_aux5 k, ⁅matrix_aux7 k, ⁅matrix_aux7 k, ⁅matrix_aux7 k, matrix_aux5 k⁆⁆⁆⁆
      = (Polynomial.X : Polynomial k) ^ 2 • matrix k
        + (3 : Polynomial k) • (Matrix.single (0 : Fin 4) (2 : Fin 4) (3 * Polynomial.X ^ 2)
            + Matrix.single (2 : Fin 4) (3 : Fin 4) (-2 * Polynomial.X ^ 2)
            + Matrix.single (3 : Fin 4) (1 : Fin 4) (2 * Polynomial.X ^ 2)) := by
    rw [e3]
    simp only [matrix_aux5, matrix, LieRing.of_associative_ring_bracket, mul_add, add_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, Fin.reduceEq, ne_eq,
      not_false_eq_true]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply] <;> ring
  rw [key, h3p, zero_smul, add_zero]


/-- A distinguished element of the displayed free Lie algebra. -/
noncomputable def freeLieElement_aux1 : ℕ → FreeLieAlgebra k (Fin 2)
  | 0 => ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆
  | (n + 1) => ⁅⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆, freeLieElement_aux1 n⁆


/-- When three vanishes, the displayed map sends the indexed iterate to the stated polynomial multiple. -/
theorem map_iterate_eq_X_smul (h3 : (3 : k) = 0) (n : ℕ) :
    lieHom_aux4 k (freeLieElement_aux1 k n) = (Polynomial.X : Polynomial k) ^ (n + 2) • matrix k := by
  induction n with
  | zero => exact bracket_eq_aux66 k h3
  | succ m ih =>
    rw [freeLieElement_aux1, LieHom.map_lie, LieHom.map_lie, map_apply_aux17, map_apply_aux16, ih,
      iteratedBracket_eq_X_smul k h3 (m + 2)]


/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux4 (h3 : (3 : k) = 0) : AuxiliaryType k 4 →ₗ[k] Polynomial k :=
  Submodule.liftQ (indexedLieIdeal k 4).toSubmodule
    ((Matrix.entryLinearMap k (Polynomial k) 0 2).comp (lieHom_aux4 k).toLinearMap)
    (by
      intro a ha
      have hm : lieHom_aux4 k a = 0 :=
        LieHom.mem_ker.1 (submodule_le_aux5 k h3 ha)
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LieHom.coe_toLinearMap, hm,
        Matrix.entryLinearMap_apply, Matrix.zero_apply])


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux18 (h3 : (3 : k) = 0) (a : FreeLieAlgebra k (Fin 2)) :
    linearMap_aux4 k h3 (lieHom_aux5 k 4 a) = (lieHom_aux4 k a) 0 2 := rfl


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux19 (h3 : (3 : k) = 0) (n : ℕ) :
    linearMap_aux4 k h3 (lieHom_aux5 k 4 (freeLieElement_aux1 k n)) = (Polynomial.X : Polynomial k) ^ (n + 2) := by
  rw [map_apply_aux18, map_iterate_eq_X_smul k h3 n]
  simp [matrix, Matrix.smul_apply]


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux8 (h3 : (3 : k) = 0) :
    LinearIndependent k (fun n => lieHom_aux5 k 4 (freeLieElement_aux1 k n)) := by
  apply LinearIndependent.of_comp (linearMap_aux4 k h3)
  have hfun : (linearMap_aux4 k h3) ∘ (fun n => lieHom_aux5 k 4 (freeLieElement_aux1 k n))
      = fun n => (Polynomial.X : Polynomial k) ^ (n + 2) := by
    funext n; exact map_apply_aux19 k h3 n
  rw [hfun]
  have hmono : LinearIndependent k (fun n => (Polynomial.X : Polynomial k) ^ n) := by
    have h := (Polynomial.basisMonomials k).linearIndependent
    simpa only [Polynomial.coe_basisMonomials, ← Polynomial.X_pow_eq_monomial] using h
  exact hmono.comp (fun n => n + 2) (add_left_injective 2)

end Matrix4c


/-- If three vanishes in the field, the displayed module is not finitely generated. -/
theorem not_moduleFinite_of_three_eq_zero (k : Type*) [Field k] (h3 : (3 : k) = 0) :
    ¬ Module.Finite k (AuxiliaryType k 4) := fun hfin => by
  haveI := hfin
  exact Module.Finite.not_linearIndependent_of_infinite _ (linearIndependent_family_aux8 k h3)


section Matrix4b
attribute [local instance] LieRing.ofAssociativeRing

open Polynomial


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux2 (k : Type*) [CommRing k] : Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  Matrix.single 0 1 (3 * X) + Matrix.single 1 2 (3 * X)


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux1 (k : Type*) [CommRing k] : Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  -(Matrix.single 1 0 X) - Matrix.single 2 1 X


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux13 (k : Type*) [CommRing k] : ⁅matrix_aux6 k, matrix_aux4 k⁆ = matrix_aux1 k := by
  simp only [matrix_aux4, matrix_aux6, matrix_aux1, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux14 (k : Type*) [CommRing k] :
    ⁅matrix_aux6 k, ⁅matrix_aux6 k, matrix_aux4 k⁆⁆
      = -(Matrix.single 0 0 X) + Matrix.single 1 1 (2 * X) - Matrix.single 2 2 X := by
  rw [bracket_eq_aux13]
  simp only [matrix_aux6, matrix_aux1, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.single_apply] ; ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux15 (k : Type*) [CommRing k] :
    ⁅matrix_aux6 k, ⁅matrix_aux6 k, ⁅matrix_aux6 k, matrix_aux4 k⁆⁆⁆ = matrix_aux2 k := by
  rw [bracket_eq_aux14]
  simp only [matrix_aux6, matrix_aux2, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.single_apply] <;> ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux12 (k : Type*) [CommRing k] :
    ⁅matrix_aux4 k, matrix_aux2 k⁆ = Matrix.single 2 1 (3 * X ^ 2) - Matrix.single 1 0 (3 * X ^ 2) := by
  simp only [matrix_aux4, matrix_aux2, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply] <;> ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux16 (k : Type*) [CommRing k] (p : Polynomial k) :
    ⁅(Matrix.single 2 1 p - Matrix.single 1 0 p : Matrix (Fin 3) (Fin 3) (Polynomial k)),
        matrix_aux2 k⁆
      = Matrix.single 0 0 (3 * X * p) - Matrix.single 1 1 (6 * X * p)
          + Matrix.single 2 2 (3 * X * p) := by
  simp only [matrix_aux2, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply] <;> ring


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact (k : Type*) [CommRing k] (p : Polynomial k) :
    ⁅(Matrix.single 0 0 (3 * X * p) - Matrix.single 1 1 (6 * X * p)
        + Matrix.single 2 2 (3 * X * p) : Matrix (Fin 3) (Fin 3) (Polynomial k)), matrix_aux1 k⁆
      = Matrix.single 2 1 (-9 * (X ^ 2 * p)) - Matrix.single 1 0 (-9 * (X ^ 2 * p)) := by
  simp only [matrix_aux1, LieRing.of_associative_ring_bracket]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.single_apply] <;> ring


/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux1 (k : Type*) [CommRing k] : ℕ → k := fun n => 3 * (-9) ^ n


/-- The polynomial specified by the displayed parameters. -/
noncomputable def polynomial (k : Type*) [CommRing k] : ℕ → Polynomial k :=
  fun n => 3 * (-9) ^ n * X ^ (2 * n + 2)


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux9 (k : Type*) [CommRing k] (n : ℕ) :
    polynomial k (n + 1) = -9 * (X ^ 2 * polynomial k n) := by
  simp only [polynomial]
  rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 from by ring, pow_add, pow_succ]
  ring


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux6 (k : Type*) [CommRing k] (n : ℕ) :
    polynomial k n = distinguishedElement_aux1 k n • (X : Polynomial k) ^ (2 * n + 2) := by
  simp only [polynomial, distinguishedElement_aux1, Polynomial.smul_eq_C_mul, map_mul, map_pow, map_neg, map_ofNat]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux64 (k : Type*) [CommRing k] : lieHom_aux3 k ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆ = matrix_aux1 k := by
  rw [LieHom.map_lie, map_apply_aux14, map_apply_aux15]
  exact bracket_eq_aux13 k


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux65 (k : Type*) [CommRing k] :
    lieHom_aux3 k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆ = matrix_aux2 k := by
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie]
  simp only [map_apply_aux14, map_apply_aux15]
  exact bracket_eq_aux15 k


/-- A distinguished element of the displayed free Lie algebra. -/
noncomputable def freeLieElement_aux2 (k : Type*) [CommRing k] : ℕ → FreeLieAlgebra k (Fin 2)
  | 0 => ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆
  | (n + 1) => ⁅⁅freeLieElement_aux2 k n, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆


/-- The Lie homomorphism sends the indexed free-Lie element to the difference of the two displayed single-entry matrices. -/
theorem map_indexedElement_eq_matrixSingles (k : Type*) [CommRing k] (n : ℕ) :
    lieHom_aux3 k (freeLieElement_aux2 k n)
      = Matrix.single 2 1 (polynomial k n) - Matrix.single 1 0 (polynomial k n) := by
  induction n with
  | zero =>
    simp only [freeLieElement_aux2]
    rw [LieHom.map_lie, map_apply_aux14, bracket_eq_aux65, bracket_eq_aux12]
    simp [polynomial]
  | succ n ih =>
    have hstep : lieHom_aux3 k (freeLieElement_aux2 k (n + 1))
        = ⁅⁅lieHom_aux3 k (freeLieElement_aux2 k n), matrix_aux2 k⁆, matrix_aux1 k⁆ := by
      simp only [freeLieElement_aux2]
      rw [LieHom.map_lie, LieHom.map_lie, bracket_eq_aux65, bracket_eq_aux64]
    rw [hstep, ih, bracket_eq_aux16, auxiliary_fact, auxiliary_fact_aux9]


/-- A linear map between the displayed modules. -/
def linearMap_aux1 (k : Type*) [CommRing k] :
    Matrix (Fin 3) (Fin 3) (Polynomial k) →ₗ[k] Polynomial k where
  toFun M := M 2 1
  map_add' M N := by simp [Matrix.add_apply]
  map_smul' c M := by simp [Matrix.smul_apply]


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux3 (k : Type*) [CommRing k] :
    LinearIndependent k (fun n : ℕ => (X : Polynomial k) ^ (2 * n + 2)) := by
  have hb := (Polynomial.basisMonomials k).linearIndependent
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro a b h; simp only [] at h; omega
  have hcomp := hb.comp (fun n : ℕ => 2 * n + 2) hinj
  have hfam : (fun n : ℕ => (X : Polynomial k) ^ (2 * n + 2))
      = ((Polynomial.basisMonomials k : ℕ → Polynomial k) ∘ fun n : ℕ => 2 * n + 2) := by
    funext n
    simp [Polynomial.coe_basisMonomials, Function.comp, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.C_1]
  rw [hfam]; exact hcomp


/-- Under the stated characteristic hypothesis, the displayed linear-map range is not finitely generated. -/
theorem range_not_moduleFinite (k : Type*) [Field k] (h3 : (3 : k) ≠ 0) :
    ¬ Module.Finite k (LinearMap.range (lieHom_aux3 k).toLinearMap) := by
  classical
  set R := LinearMap.range (lieHom_aux3 k).toLinearMap with hR

  have hmemR : ∀ n, lieHom_aux3 k (freeLieElement_aux2 k n) ∈ R := by
    intro n; rw [hR]; exact LinearMap.mem_range.mpr ⟨freeLieElement_aux2 k n, rfl⟩

  have hc : ∀ n, distinguishedElement_aux1 k n ≠ 0 := by
    intro n
    have h9 : (9 : k) ≠ 0 := by rw [show (9 : k) = 3 * 3 by norm_num]; exact mul_ne_zero h3 h3
    refine mul_ne_zero h3 (pow_ne_zero n ?_)
    rw [show (-9 : k) = -(9 : k) by norm_num]; exact neg_ne_zero.mpr h9

  have hpcoefLI : LinearIndependent k (polynomial k) := by
    have heq : polynomial k
        = (fun n => Units.mk0 (distinguishedElement_aux1 k n) (hc n)) •
            fun n : ℕ => (X : Polynomial k) ^ (2 * n + 2) := by
      funext n
      simp only [Pi.smul_apply', Units.smul_mk0]
      exact displayed_eq_aux6 k n
    rw [heq]
    exact (linearIndependent_family_aux3 k).units_smul _

  have hfam : LinearIndependent k (fun n : ℕ => lieHom_aux3 k (freeLieElement_aux2 k n)) := by
    refine LinearIndependent.of_comp (linearMap_aux1 k) ?_
    have hcomp : (linearMap_aux1 k ∘ fun n : ℕ => lieHom_aux3 k (freeLieElement_aux2 k n)) = polynomial k := by
      funext n
      simp [Function.comp_apply, map_indexedElement_eq_matrixSingles k n, linearMap_aux1]
    rw [hcomp]; exact hpcoefLI

  have hsub : LinearIndependent k (fun n : ℕ => (⟨lieHom_aux3 k (freeLieElement_aux2 k n), hmemR n⟩ : R)) := by
    refine LinearIndependent.of_comp R.subtype ?_
    exact hfam

  intro hfin
  haveI := hfin
  exact Module.Finite.not_linearIndependent_of_infinite _ hsub

end Matrix4b


/-- The displayed module over a field is not finitely generated. -/
@[source_ref "Chapter2/Problem2.16.3" (role := primary)]
theorem not_moduleFinite (k : Type*) [Field k] : ¬ Module.Finite k (AuxiliaryType k 4) := by
  by_cases h3 : (3 : k) = 0
  · exact not_moduleFinite_of_three_eq_zero k h3
  · exact not_moduleFinite_of_range k (range_not_moduleFinite k h3)


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux5 (n : ℕ) : AuxiliaryType k n := ⁅distinguishedElement_aux8 k n, distinguishedElement_aux6 k n⁆


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux4 (n : ℕ) : AuxiliaryType k n := ⁅distinguishedElement_aux7 k n, distinguishedElement_aux5 k n⁆


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux41 : ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux6 k 3⁆ = 0 := by
  have hz : ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3⁆ = distinguishedElement_aux9 k 3 := rfl
  rw [distinguishedElement_aux6, leibniz_lie, hz, lie_self, bracket_eq_aux43, lie_zero, add_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux47 : ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux5 k 3⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux5 k 3⁆ = lieHom_aux5 k 3 ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆⁆ := by
    simp only [distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux7, distinguishedElement_aux8, distinguishedElement_aux9, LieHom.map_lie]
  rw [h, mem_submodule_aux13]
  have hmem : (fun z => ⁅freeLieElement_aux4 k, z⁆)^[3 + 1] (freeLieElement_aux3 k) ∈ indexedLieIdeal k 3 :=
    LieSubmodule.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  have heq : ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆⁆ = -(fun z => ⁅freeLieElement_aux4 k, z⁆)^[3 + 1] (freeLieElement_aux3 k) := by
    change ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆⁆ = -⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆
    rw [← lie_skew (x := freeLieElement_aux3 k) (y := freeLieElement_aux4 k), lie_neg, lie_neg, lie_neg]
  rw [heq]; exact neg_mem hmem


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux53 : ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3⁆ = distinguishedElement_aux4 k 3 := by
  have hz : distinguishedElement_aux9 k 3 = ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3⁆ := rfl
  rw [distinguishedElement_aux4, hz, lie_lie, show ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux6 k 3⁆ = distinguishedElement_aux5 k 3 from rfl, bracket_eq_aux41, lie_zero, sub_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux45 : ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux4 k 3⁆ = -⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ := by
  rw [show distinguishedElement_aux9 k 3 = ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3⁆ from rfl, show distinguishedElement_aux4 k 3 = ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux5 k 3⁆ from rfl, leibniz_lie,
    bracket_eq_aux47, lie_zero, add_zero, ← lie_skew (x := distinguishedElement_aux8 k 3) (y := distinguishedElement_aux7 k 3), neg_lie]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux51 : ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ = ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux4 k 3⁆ := by
  rw [show distinguishedElement_aux5 k 3 = ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux6 k 3⁆ from rfl, leibniz_lie, bracket_eq_aux53,
    ← lie_skew (x := distinguishedElement_aux9 k 3) (y := distinguishedElement_aux8 k 3), neg_lie,
    show ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3⁆ = distinguishedElement_aux6 k 3 from rfl, lie_self, neg_zero, zero_add]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux52 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) :
    ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ = 0 := by
  have h2 : ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ = -⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ := by
    conv_lhs => rw [bracket_eq_aux51]
    rw [bracket_eq_aux45]
  have h3 : ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ + ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ = 0 := by
    nth_rewrite 2 [h2]; exact add_neg_cancel _
  have h4 : (2 : k) • ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux5 k 3⁆ = 0 := by rw [two_smul]; exact h3
  have h5 := congrArg (fun t => (2 : k)⁻¹ • t) h4
  simpa [smul_smul, inv_mul_cancel₀ hk] using h5


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux46 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) :
    ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux4 k 3⁆ = 0 := by
  rw [bracket_eq_aux45, bracket_eq_aux52 k hk, neg_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux40 : ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux4 k 3⁆ = 0 := by
  rw [← bracket_eq_aux53, leibniz_lie, bracket_eq_aux43, zero_lie, bracket_eq_aux41, lie_zero, add_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux50 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) : ⁅distinguishedElement_aux9 k 3, distinguishedElement_aux4 k 3⁆ = 0 := by
  rw [show distinguishedElement_aux4 k 3 = ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux5 k 3⁆ from rfl, leibniz_lie, bracket_eq_aux52 k hk, lie_zero,
    add_zero, ← lie_skew (x := distinguishedElement_aux9 k 3) (y := distinguishedElement_aux7 k 3), neg_lie, bracket_eq_aux43, zero_lie, neg_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux39 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) : ⁅distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3⁆ = 0 := by
  rw [show distinguishedElement_aux6 k 3 = ⁅distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3⁆ from rfl, lie_lie, bracket_eq_aux52 k hk, bracket_eq_aux47,
    lie_zero, lie_zero, sub_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux38 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) : ⁅distinguishedElement_aux6 k 3, distinguishedElement_aux4 k 3⁆ = 0 := by
  rw [show distinguishedElement_aux4 k 3 = ⁅distinguishedElement_aux7 k 3, distinguishedElement_aux5 k 3⁆ from rfl, leibniz_lie, bracket_eq_aux39 k hk, lie_zero,
    add_zero, ← lie_skew (x := distinguishedElement_aux6 k 3) (y := distinguishedElement_aux7 k 3), neg_lie, bracket_eq_aux41, zero_lie, neg_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux37 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) : ⁅distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3⁆ = 0 := by
  rw [← bracket_eq_aux53, leibniz_lie,
    ← lie_skew (x := distinguishedElement_aux5 k 3) (y := distinguishedElement_aux9 k 3), neg_lie, bracket_eq_aux52 k hk, zero_lie, neg_zero,
    zero_add, ← lie_skew (x := distinguishedElement_aux5 k 3) (y := distinguishedElement_aux6 k 3), lie_neg, bracket_eq_aux39 k hk, lie_zero,
    neg_zero]

section Matrix3
attribute [local instance] LieRing.ofAssociativeRing


private noncomputable def GX : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 1 0 1 + Matrix.single 3 2 1 + Matrix.single 6 5 1

private noncomputable def GY : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 2 0 1 + Matrix.single 3 1 1 + Matrix.single 4 3 1 + Matrix.single 5 4 1

private noncomputable def GZ : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 6 4 1 - Matrix.single 4 2 1

private noncomputable def GW : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 4 0 1 - Matrix.single 5 2 1 - Matrix.single 6 3 1

private noncomputable def GV : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 5 0 1 + Matrix.single 5 0 1 + Matrix.single 6 1 1

private noncomputable def GU : Matrix (Fin 7) (Fin 7) k :=
  Matrix.single 6 0 1


/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux2 : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ Matrix (Fin 7) (Fin 7) k :=
  FreeLieAlgebra.lift k ![GX k, GY k]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux12 : lieHom_aux2 k (freeLieElement_aux3 k) = GX k := by
  simp only [lieHom_aux2, freeLieElement_aux3, FreeLieAlgebra.lift_of_apply]; rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux13 : lieHom_aux2 k (freeLieElement_aux4 k) = GY k := by
  simp only [lieHom_aux2, freeLieElement_aux4, FreeLieAlgebra.lift_of_apply]; rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux3 : ⁅GX k, GY k⁆ = GZ k := by
  simp only [GX, GY, GZ, LieRing.of_associative_ring_bracket, add_mul, mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, mul_one]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux7 : ⁅GY k, GZ k⁆ = GW k := by
  simp only [GY, GZ, GW, LieRing.of_associative_ring_bracket, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, mul_one]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux6 : ⁅GY k, GW k⁆ = GV k := by
  simp only [GY, GW, GV, LieRing.of_associative_ring_bracket, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, mul_one]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux2 : ⁅GX k, GV k⁆ = GU k := by
  simp only [GX, GV, GU, LieRing.of_associative_ring_bracket, add_mul, mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, mul_one]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux4 : ⁅GX k, GZ k⁆ = 0 := by
  simp only [GX, GZ, LieRing.of_associative_ring_bracket, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux5 : ⁅GY k, GV k⁆ = 0 := by
  simp only [GY, GV, LieRing.of_associative_ring_bracket, add_mul, mul_add,
    Matrix.single_mul_single_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  abel


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux60 : lieHom_aux2 k ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ = 0 := by
  rw [LieHom.map_lie, LieHom.map_lie, map_apply_aux12, map_apply_aux13, bracket_eq_aux3, bracket_eq_aux4]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux61 : lieHom_aux2 k ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[3 + 1] (freeLieElement_aux3 k)) = 0 := by
  change lieHom_aux2 k ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, freeLieElement_aux3 k⁆⁆⁆⁆ = 0
  rw [LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, map_apply_aux12, map_apply_aux13]
  have h1 : ⁅GY k, GX k⁆ = -GZ k := by rw [← lie_skew, bracket_eq_aux3]
  rw [h1, lie_neg, bracket_eq_aux7, lie_neg, bracket_eq_aux6, lie_neg, bracket_eq_aux5, neg_zero]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le_aux3 : indexedLieIdeal k 3 ≤ (lieHom_aux2 k).ker := by
  rw [indexedLieIdeal, LieSubmodule.lieSpan_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux60 k
  · rw [SetLike.mem_coe, LieHom.mem_ker]; exact bracket_eq_aux61 k


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux1 : LinearIndependent k ![distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_six] at hc


  have hpw : lieHom_aux5 k 3 (c 0 • freeLieElement_aux3 k + c 1 • freeLieElement_aux4 k + c 2 • ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆ +
      c 3 • ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆ + c 4 • ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆ +
      c 5 • ⁅freeLieElement_aux3 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux4 k, ⁅freeLieElement_aux3 k, freeLieElement_aux4 k⁆⁆⁆⁆) = 0 := by
    rw [map_add, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      map_smul, map_smul, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
      LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
      LieHom.map_lie]
    exact hc
  have hmem := (mem_submodule_aux13 k 3 _).mp hpw
  have hker := submodule_le_aux3 k hmem
  rw [LieHom.mem_ker, map_add, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    map_smul, map_smul, map_smul, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
    LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
    map_apply_aux12, map_apply_aux13, bracket_eq_aux3, bracket_eq_aux7, bracket_eq_aux6, bracket_eq_aux2] at hker

  simp only [GX, GY, GZ, GW, GV, GU] at hker
  intro i
  fin_cases i
  · have := congrFun (congrFun hker 1) 0
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this
  · have := congrFun (congrFun hker 2) 0
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this
  · have := congrFun (congrFun hker 4) 2
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this
  · have := congrFun (congrFun hker 4) 0
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this
  · have := congrFun (congrFun hker 6) 1
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this
  · have := congrFun (congrFun hker 6) 0
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] using this

end Matrix3


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux4 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) :
    Submodule.span k {distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3} = ⊤ := by
  have hzm : distinguishedElement_aux9 k 3 ∈ ({distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3} : Set (AuxiliaryType k 3)) := by simp
  have hwm : distinguishedElement_aux6 k 3 ∈ ({distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3} : Set (AuxiliaryType k 3)) := by simp
  have hvm : distinguishedElement_aux5 k 3 ∈ ({distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3} : Set (AuxiliaryType k 3)) := by simp
  have hum : distinguishedElement_aux4 k 3 ∈ ({distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3} : Set (AuxiliaryType k 3)) := by simp
  refine submodule_eq_aux2 k 3 _ (by simp) (by simp) ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lie_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hzm
    · rw [bracket_eq_aux43]; exact Submodule.zero_mem _
    · rw [bracket_eq_aux41]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hum
    · rw [bracket_eq_aux40]; exact Submodule.zero_mem _
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← lie_skew (x := distinguishedElement_aux8 k 3) (y := distinguishedElement_aux7 k 3)]
      exact neg_mem (Submodule.subset_span hzm)
    · rw [lie_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hwm
    · exact Submodule.subset_span hvm
    · rw [bracket_eq_aux47]; exact Submodule.zero_mem _
    · rw [bracket_eq_aux46 k hk]; exact Submodule.zero_mem _


/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.16.3" (role := primary)]
theorem finrank_eq_aux1 (k : Type*) [Field k] (hk : (2 : k) ≠ 0) :
    Module.finrank k (AuxiliaryType k 3) = 6 := by
  have hspan : ⊤ ≤ Submodule.span k
      (Set.range ![distinguishedElement_aux7 k 3, distinguishedElement_aux8 k 3, distinguishedElement_aux9 k 3, distinguishedElement_aux6 k 3, distinguishedElement_aux5 k 3, distinguishedElement_aux4 k 3]) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union, Set.singleton_union,
      Set.singleton_union, Set.singleton_union, Set.singleton_union, submodule_eq_aux4 k hk]
  let b : Module.Basis (Fin 6) k (AuxiliaryType k 3) := Module.Basis.mk (linearIndependent_family_aux1 k) hspan
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]


section TwistedLoop

attribute [local instance] LieRing.ofAssociativeRing

open Polynomial

variable {R : Type*} [CommRing R]


/-- The matrix specified by the displayed parameters. -/
def matrix_aux14 (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => -(A j.rev i.rev)


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux9 (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    matrix_aux14 A i j = -(A j.rev i.rev) := rfl


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux14 (A : Matrix (Fin 3) (Fin 3) R) : matrix_aux14 (matrix_aux14 A) = A := by
  ext i j; simp [Fin.rev_rev]


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux17 : matrix_aux14 (0 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  ext i j; simp


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux8 (A B : Matrix (Fin 3) (Fin 3) R) :
    matrix_aux14 (A + B) = matrix_aux14 A + matrix_aux14 B := by
  ext i j; simp only [displayed_eq_aux9, Matrix.add_apply]; ring


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux16 (A B : Matrix (Fin 3) (Fin 3) R) :
    matrix_aux14 (A - B) = matrix_aux14 A - matrix_aux14 B := by
  ext i j; simp only [displayed_eq_aux9, Matrix.sub_apply]; ring


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux13 (A : Matrix (Fin 3) (Fin 3) R) : matrix_aux14 (-A) = -matrix_aux14 A := by
  ext i j; simp only [displayed_eq_aux9, Matrix.neg_apply]


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux15 {S : Type*} [Monoid S] [DistribMulAction S R] (c : S)
    (A : Matrix (Fin 3) (Fin 3) R) : matrix_aux14 (c • A) = c • matrix_aux14 A := by
  ext i j; simp [Matrix.smul_apply]


/-- The displayed single-entry matrix identity holds. -/
@[simp] theorem matrixSingle_eq_aux1 (i j : Fin 3) (c : R) :
    matrix_aux14 (Matrix.single i j c) = -Matrix.single j.rev i.rev c := by
  ext a b
  simp only [displayed_eq_aux9, Matrix.neg_apply, Matrix.single, Matrix.of_apply, neg_inj]
  by_cases h : j.rev = a ∧ i.rev = b
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp [Fin.rev_rev]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    exact h ⟨by rw [h2, Fin.rev_rev], by rw [h1, Fin.rev_rev]⟩

private theorem rev_zero_three : (0 : Fin 3).rev = 2 := by decide
@[simp] private theorem rev_one_three : (1 : Fin 3).rev = 1 := by decide
@[simp] private theorem rev_two_three : (2 : Fin 3).rev = 0 := by decide


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux12 (A B : Matrix (Fin 3) (Fin 3) R) :
    matrix_aux14 A * matrix_aux14 B = -matrix_aux14 (B * A) := by
  ext i j
  have h : ∑ l : Fin 3, B j.rev (Fin.revPerm l) * A (Fin.revPerm l) i.rev
      = ∑ m : Fin 3, B j.rev m * A m i.rev :=
    Equiv.sum_comp (Fin.revPerm (n := 3)) (fun m => B j.rev m * A m i.rev)
  simp only [Fin.revPerm_apply] at h
  simp only [Matrix.mul_apply, displayed_eq_aux9, Matrix.neg_apply, neg_neg, neg_mul_neg]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux70 (A B : Matrix (Fin 3) (Fin 3) R) :
    matrix_aux14 ⁅A, B⁆ = ⁅matrix_aux14 A, matrix_aux14 B⁆ := by
  simp only [LieRing.of_associative_ring_bracket, displayed_eq_aux16, displayed_eq_aux12]
  abel


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux11 : Fin 3 → Matrix (Fin 3) (Fin 3) k :=
  ![Matrix.single 0 1 1 - Matrix.single 1 2 1,
    Matrix.single 0 0 1 - Matrix.single 2 2 1,
    Matrix.single 1 0 1 - Matrix.single 2 1 1]


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux10 : Fin 5 → Matrix (Fin 3) (Fin 3) k :=
  ![Matrix.single 0 2 1,
    Matrix.single 0 1 1 + Matrix.single 1 2 1,
    Matrix.single 0 0 1 - Matrix.single 1 1 (2 : k) + Matrix.single 2 2 1,
    Matrix.single 1 0 1 + Matrix.single 2 1 1,
    Matrix.single 2 0 1]


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux11 (i : Fin 3) : matrix_aux14 (matrix_aux11 k i) = matrix_aux11 k i := by
  fin_cases i <;> simp [matrix_aux11] <;> abel


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux10 (i : Fin 5) : matrix_aux14 (matrix_aux10 k i) = -matrix_aux10 k i := by
  fin_cases i <;> simp [matrix_aux10] ; abel


/-- The trace of the specified matrix is zero. -/
@[simp] theorem trace_eq_zero_aux3 (i : Fin 3) : Matrix.trace (matrix_aux11 k i) = 0 := by
  fin_cases i <;>
    simp [matrix_aux11, Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.sub_apply]


/-- The trace of the specified matrix is zero. -/
@[simp] theorem trace_eq_zero_aux2 (i : Fin 5) : Matrix.trace (matrix_aux10 k i) = 0 := by
  fin_cases i <;>
    simp [matrix_aux10, Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.add_apply,
      Matrix.sub_apply] ; ring


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux5 : LinearIndependent k (matrix_aux11 k) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a b : Fin 3, ∑ i, c i * matrix_aux11 k i a b = 0 := by
    intro a b
    have h := congrFun (congrFun hc a) b
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_three, matrix_aux11, Matrix.sub_apply] using key 0 1
  · simpa [Fin.sum_univ_three, matrix_aux11, Matrix.sub_apply] using key 0 0
  · simpa [Fin.sum_univ_three, matrix_aux11, Matrix.sub_apply] using key 1 0


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux4 : LinearIndependent k (matrix_aux10 k) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a b : Fin 3, ∑ i, c i * matrix_aux10 k i a b = 0 := by
    intro a b
    have h := congrFun (congrFun hc a) b
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_five, matrix_aux10, Matrix.add_apply, Matrix.sub_apply] using key 0 2
  · simpa [Fin.sum_univ_five, matrix_aux10, Matrix.add_apply, Matrix.sub_apply] using key 0 1
  · simpa [Fin.sum_univ_five, matrix_aux10, Matrix.add_apply, Matrix.sub_apply] using key 0 0
  · simpa [Fin.sum_univ_five, matrix_aux10, Matrix.add_apply, Matrix.sub_apply] using key 1 0
  · simpa [Fin.sum_univ_five, matrix_aux10, Matrix.add_apply, Matrix.sub_apply] using key 2 0


/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom_aux2 : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (-Polynomial.X : Polynomial k)


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux11 (p : Polynomial k) (n : ℕ) :
    (algHom_aux2 k p).coeff n = (-1 : k) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial m a =>
      have hpow : (-Polynomial.X : Polynomial k) ^ m
          = Polynomial.C ((-1 : k) ^ m) * Polynomial.X ^ m := by
        rw [show (-Polynomial.X : Polynomial k) = Polynomial.C (-1 : k) * Polynomial.X by simp,
          mul_pow, Polynomial.C_pow]
      have h1 : algHom_aux2 k ((Polynomial.monomial m) a)
          = Polynomial.C ((-1 : k) ^ m) * (Polynomial.monomial m) a := by
        rw [algHom_aux2, Polynomial.aeval_monomial, Polynomial.algebraMap_eq, hpow,
          ← Polynomial.C_mul_X_pow_eq_monomial]
        ring
      rw [h1, Polynomial.coeff_C_mul, Polynomial.coeff_monomial]
      by_cases h : m = n
      · subst h; simp
      · simp [h]


/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom_aux1 : Matrix (Fin 3) (Fin 3) (Polynomial k) →ₐ[k]
    Matrix (Fin 3) (Fin 3) (Polynomial k) := (algHom_aux2 k).mapMatrix


/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom : Matrix (Fin 3) (Fin 3) (Polynomial k) →ₐ[k]
    Matrix (Fin 3) (Fin 3) k := (Polynomial.aeval (0 : k)).mapMatrix


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux55 {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (P Q : A) : f ⁅P, Q⁆ = ⁅f P, f Q⁆ := by
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]


/-- A Lie subalgebra of three-by-three matrices over the displayed polynomial ring. -/
noncomputable def matrixPolynomialLieSubalgebra : LieSubalgebra k (Matrix (Fin 3) (Fin 3) (Polynomial k)) where
  carrier := {P | Matrix.trace P = 0 ∧ matrix_aux14 P = algHom_aux1 k P ∧
    algHom k P ∈ Submodule.span k {matrix_aux11 k 0}}
  add_mem' := by
    rintro P Q ⟨hP1, hP2, hP3⟩ ⟨hQ1, hQ2, hQ3⟩
    refine ⟨by rw [Matrix.trace_add, hP1, hQ1, add_zero], ?_, ?_⟩
    · rw [displayed_eq_aux8, hP2, hQ2, map_add]
    · rw [map_add]; exact Submodule.add_mem _ hP3 hQ3
  zero_mem' := ⟨Matrix.trace_zero _ _, by rw [displayed_eq_aux17, map_zero], by
    rw [map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c P ⟨hP1, hP2, hP3⟩
    refine ⟨by rw [Matrix.trace_smul, hP1, smul_zero], ?_, ?_⟩
    · rw [displayed_eq_aux15, hP2, map_smul]
    · rw [map_smul]; exact Submodule.smul_mem _ _ hP3
  lie_mem' := by
    rintro P Q ⟨hP1, hP2, hP3⟩ ⟨hQ1, hQ2, hQ3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket, Matrix.trace_sub, Matrix.trace_mul_comm,
        sub_self]
    · rw [bracket_eq_aux70, hP2, hQ2, bracket_eq_aux55]
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hP3
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hQ3
      rw [bracket_eq_aux55, ← ha, ← hb, smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
      exact Submodule.zero_mem _


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux9 (n : ℕ) (P : Matrix (Fin 3) (Fin 3) (Polynomial k)) :
    Matrix (Fin 3) (Fin 3) k := P.map (fun p => p.coeff n)


/-- The indicated polynomial coefficient has the displayed value. -/
@[simp] theorem coeff_eq (n : ℕ) (P : Matrix (Fin 3) (Fin 3) (Polynomial k))
    (a b : Fin 3) : matrix_aux9 k n P a b = (P a b).coeff n := rfl


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux3 (P : Matrix (Fin 3) (Fin 3) (Polynomial k)) :
    algHom k P = matrix_aux9 k 0 P := by
  ext a b
  simp [algHom, AlgHom.mapMatrix_apply, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coe_aeval_eq_eval]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux10 (P : Matrix (Fin 3) (Fin 3) (Polynomial k)) :
    matrix_aux14 P = algHom_aux1 k P ↔ ∀ n, matrix_aux14 (matrix_aux9 k n P) = (-1 : k) ^ n • matrix_aux9 k n P := by
  constructor
  · intro h n
    ext a b
    have hab := congrArg (fun p : Polynomial k => Polynomial.coeff p n)
      (congrFun (congrFun h a) b)
    simpa [algHom_aux1, AlgHom.mapMatrix_apply, auxiliary_fact_aux11, Matrix.smul_apply] using hab
  · intro h
    ext a b n
    have hab := congrFun (congrFun (h n) a) b
    simpa [algHom_aux1, AlgHom.mapMatrix_apply, auxiliary_fact_aux11, Matrix.smul_apply] using hab


/-- Membership in the displayed matrix Lie subalgebra is equivalent to the stated trace, symmetry, and span conditions. -/
theorem mem_matrixPolynomialLieSubalgebra_iff {P : Matrix (Fin 3) (Fin 3) (Polynomial k)} :
    P ∈ matrixPolynomialLieSubalgebra k ↔ Matrix.trace P = 0 ∧ matrix_aux14 P = algHom_aux1 k P ∧
      algHom k P ∈ Submodule.span k {matrix_aux11 k 0} := Iff.rfl


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule : matrix_aux4 k ∈ matrixPolynomialLieSubalgebra k := by
  refine ⟨?_, ?_, ?_⟩
  · simp [matrix_aux4, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [matrix_aux4, matrix_aux14, algHom_aux1, algHom_aux2, Matrix.single, Fin.rev, AlgHom.mapMatrix_apply]
  · have : algHom k (matrix_aux4 k) = 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [matrix_aux4, algHom, Matrix.single, AlgHom.mapMatrix_apply]
    rw [this]; exact Submodule.zero_mem _


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux1 : matrix_aux6 k ∈ matrixPolynomialLieSubalgebra k := by
  refine ⟨?_, ?_, ?_⟩
  · simp [matrix_aux6, Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.sub_apply]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [matrix_aux6, matrix_aux14, algHom_aux1, algHom_aux2, Matrix.single, Matrix.sub_apply, Fin.rev,
        AlgHom.mapMatrix_apply]
  · have : algHom k (matrix_aux6 k) = matrix_aux11 k 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [matrix_aux6, matrix_aux11, algHom, Matrix.single, AlgHom.mapMatrix_apply]
    rw [this]
    exact Submodule.mem_span_singleton_self _


/-- The specified element belongs to the span of the displayed generators. -/
theorem mem_span_aux3 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0)
    {A : Matrix (Fin 3) (Fin 3) k} (h : matrix_aux14 A = A) :
    A ∈ Submodule.span k (Set.range (matrix_aux11 k)) := by
  have e : ∀ i j : Fin 3, -(A j.rev i.rev) = A i j := fun i j => congrFun (congrFun h i) j
  have two_cancel : ∀ a : k, -a = a → a = 0 := by
    intro a ha
    have : (2 : k) * a = 0 := by linear_combination -ha
    exact (mul_eq_zero.mp this).resolve_left h2
  have h02 : A 0 2 = 0 := two_cancel _ (by simpa using e 0 2)
  have h11 : A 1 1 = 0 := two_cancel _ (by simpa using e 1 1)
  have h20 : A 2 0 = 0 := two_cancel _ (by simpa using e 2 0)
  have h22 : A 2 2 = -A 0 0 := by simpa [eq_comm] using e 2 2
  have h12 : A 1 2 = -A 0 1 := by simpa [eq_comm] using e 1 2
  have h21 : A 2 1 = -A 1 0 := by simpa [eq_comm] using e 2 1
  have key : A = A 0 1 • matrix_aux11 k 0 + A 0 0 • matrix_aux11 k 1 + A 1 0 • matrix_aux11 k 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix_aux11, Matrix.single, Matrix.add_apply, h02, h11, h20, h22, h12, h21]
  rw [key]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


/-- The specified element belongs to the span of the displayed generators. -/
theorem mem_span_aux2 {A : Matrix (Fin 3) (Fin 3) k}
    (htr : Matrix.trace A = 0) (h : matrix_aux14 A = -A) :
    A ∈ Submodule.span k (Set.range (matrix_aux10 k)) := by
  have e : ∀ i j : Fin 3, A j.rev i.rev = A i j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.neg_apply, neg_inj] using this
  have h22 : A 2 2 = A 0 0 := by simpa using e 0 0
  have h12 : A 1 2 = A 0 1 := by simpa using e 0 1
  have h21 : A 2 1 = A 1 0 := by simpa using e 1 0
  have h11 : A 1 1 = -(2 : k) * A 0 0 := by
    have := htr
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at this
    linear_combination this - h22
  have key : A = A 0 2 • matrix_aux10 k 0 + A 0 1 • matrix_aux10 k 1 + A 0 0 • matrix_aux10 k 2
      + A 1 0 • matrix_aux10 k 3 + A 2 0 • matrix_aux10 k 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix_aux10, Matrix.single, Matrix.add_apply, h22, h12, h21, h11] ; ring
  rw [key]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


/-- A linear map between the displayed modules. -/
noncomputable def linearMap (n : ℕ) :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) (Polynomial k) where
  toFun A := A.map (Polynomial.monomial n)
  map_add' A B := Matrix.ext fun a b => by
    simp [Matrix.map_apply, Matrix.add_apply]
  map_smul' c A := Matrix.ext fun a b => by
    simp [Matrix.map_apply, Matrix.smul_apply, Polynomial.smul_monomial]


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux4 (n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) (a b : Fin 3) :
    linearMap k n A a b = Polynomial.monomial n (A a b) := rfl


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux2 (m n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) :
    matrix_aux9 k m (linearMap k n A) = if n = m then A else 0 := by
  ext a b
  by_cases h : n = m <;> simp [Polynomial.coeff_monomial, h]


/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness (P : Matrix (Fin 3) (Fin 3) (Polynomial k)) :
    ∃ N, P = ∑ n ∈ Finset.range N, linearMap k n (matrix_aux9 k n P) := by
  refine ⟨(Finset.univ.sup fun ij : Fin 3 × Fin 3 => (P ij.1 ij.2).natDegree) + 1, ?_⟩
  refine Matrix.ext fun a b => ?_
  have hlt : (P a b).natDegree
      < (Finset.univ.sup fun ij : Fin 3 × Fin 3 => (P ij.1 ij.2).natDegree) + 1 :=
    Nat.lt_succ_of_le
      (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 => (P ij.1 ij.2).natDegree)
        (Finset.mem_univ (a, b)))
  simp only [Matrix.sum_apply, map_apply_aux4, coeff_eq]
  exact Polynomial.as_sum_range' (P a b) _ hlt


/-- The trace of the monomial matrix is the corresponding monomial applied to the trace. -/
theorem trace_monomialMatrix (n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) :
    Matrix.trace (linearMap k n A) = Polynomial.monomial n (Matrix.trace A) := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, map_apply_aux4, map_add]


/-- The trace of the specified matrix is zero. -/
theorem trace_eq_zero (n : ℕ) {P : Matrix (Fin 3) (Fin 3) (Polynomial k)}
    (h : Matrix.trace P = 0) : Matrix.trace (matrix_aux9 k n P) = 0 := by
  have : Matrix.trace (matrix_aux9 k n P) = (Matrix.trace P).coeff n := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  rw [this, h, Polynomial.coeff_zero]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux1 (n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) (htr : Matrix.trace A = 0)
    (hsig : matrix_aux14 A = (-1 : k) ^ n • A)
    (hconst : n = 0 → A ∈ Submodule.span k {matrix_aux11 k 0}) :
    linearMap k n A ∈ matrixPolynomialLieSubalgebra k := by
  refine ⟨by rw [trace_monomialMatrix, htr, map_zero], ?_, ?_⟩
  · rw [auxiliary_fact_aux10]
    intro m
    rw [map_apply_aux2]
    by_cases h : n = m
    · subst h; simpa using hsig
    · simp [h]
  · rw [map_apply_aux3, map_apply_aux2]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact hconst hn
    · rw [if_neg hn]; exact Submodule.zero_mem _


/-- An auxiliary indexing type. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
inductive AuxiliaryIndex where
  /-- The distinguished base index. -/
  | base : AuxiliaryIndex
  /-- An odd-degree index, with its natural-number and five-element coordinates. -/
  | odd (m : ℕ) (i : Fin 5) : AuxiliaryIndex
  /-- An even-degree index, with its natural-number and three-element coordinates. -/
  | even (m : ℕ) (i : Fin 3) : AuxiliaryIndex
  deriving DecidableEq


/-- Maps each value of the indexing type to a natural number. -/
def AuxiliaryIndex.toNat : AuxiliaryIndex → ℕ
  | .base => 0
  | .odd m _ => 2 * m + 1
  | .even m _ => 2 * m + 2


/-- Associates a three-by-three matrix to each value of the indexing type. -/
noncomputable def AuxiliaryIndex.toMatrix (k : Type*) [CommRing k] : AuxiliaryIndex → Matrix (Fin 3) (Fin 3) k
  | .base => matrix_aux11 k 0
  | .odd _ i => matrix_aux10 k i
  | .even _ i => matrix_aux11 k i


/-- The matrix specified by the displayed parameters. -/
noncomputable def matrix_aux13 (I : AuxiliaryIndex) : Matrix (Fin 3) (Fin 3) (Polynomial k) :=
  linearMap k I.toNat (I.toMatrix k)


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux11 (I : AuxiliaryIndex) : matrix_aux13 k I ∈ matrixPolynomialLieSubalgebra k := by
  change linearMap k I.toNat (I.toMatrix k) ∈ matrixPolynomialLieSubalgebra k
  refine auxiliary_fact_aux1 k I.toNat (I.toMatrix k) ?_ ?_ ?_
  · cases I <;> simp [AuxiliaryIndex.toMatrix]
  · cases I with
    | base => simp [AuxiliaryIndex.toNat, AuxiliaryIndex.toMatrix]
    | odd m i =>
        rw [AuxiliaryIndex.toMatrix, AuxiliaryIndex.toNat, displayed_eq_aux10, pow_succ, pow_mul]
        simp
    | even m i =>
        rw [AuxiliaryIndex.toMatrix, AuxiliaryIndex.toNat, displayed_eq_aux11, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]
        simp
  · intro h
    cases I with
    | base => simp [AuxiliaryIndex.toMatrix, Submodule.mem_span_singleton_self]
    | odd m i => rw [AuxiliaryIndex.toNat] at h; omega
    | even m i => rw [AuxiliaryIndex.toNat] at h; omega


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux3 (I : AuxiliaryIndex) : matrixPolynomialLieSubalgebra k := ⟨matrix_aux13 k I, mem_submodule_aux11 k I⟩


/-- A construction with the displayed domain and codomain. -/
def AuxiliaryIndex.position : AuxiliaryIndex → Fin 3 × Fin 3
  | .base => (0, 1)
  | .odd _ i => ![(0, 2), (0, 1), (0, 0), (1, 0), (2, 0)] i
  | .even _ i => ![(0, 1), (0, 0), (1, 0)] i


/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux3 (I : AuxiliaryIndex) :
    Matrix (Fin 3) (Fin 3) (Polynomial k) →ₗ[k] k where
  toFun P := (P I.position.1 I.position.2).coeff I.toNat
  map_add' P Q := by simp [Matrix.add_apply]
  map_smul' c P := by simp [Matrix.smul_apply, Polynomial.coeff_smul]


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux7 (I J : AuxiliaryIndex) :
    linearMap_aux3 k I (matrix_aux13 k J) = if I = J then 1 else 0 := by
  have hL : linearMap_aux3 k I (matrix_aux13 k J)
      = if J.toNat = I.toNat then (J.toMatrix k) I.position.1 I.position.2 else 0 := by
    simp [linearMap_aux3, matrix_aux13, Polynomial.coeff_monomial]
  rw [hL]
  by_cases h : I = J
  · subst h
    rw [if_pos rfl, if_pos rfl]
    cases I with
    | base => simp [AuxiliaryIndex.toMatrix, AuxiliaryIndex.position, matrix_aux11, Matrix.single]
    | odd m i =>
        fin_cases i <;> simp [AuxiliaryIndex.toMatrix, AuxiliaryIndex.position, matrix_aux10, Matrix.single]
    | even m i =>
        fin_cases i <;> simp [AuxiliaryIndex.toMatrix, AuxiliaryIndex.position, matrix_aux11, Matrix.single]
  · rw [if_neg h]
    by_cases hd : J.toNat = I.toNat
    · rw [if_pos hd]
      cases I with
      | base =>
          cases J with
          | base => exact absurd rfl h
          | odd m' i' => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
          | even m' i' => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
      | odd m i =>
          cases J with
          | base => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
          | odd m' i' =>
              have hm : m' = m := by rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
              subst hm
              have hi : i' ≠ i := fun hh => h (by rw [hh])
              clear hd h
              fin_cases i <;> fin_cases i' <;>
                first
                  | exact absurd rfl hi
                  | simp [AuxiliaryIndex.toMatrix, AuxiliaryIndex.position, matrix_aux10, Matrix.single]
          | even m' i' => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
      | even m i =>
          cases J with
          | base => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
          | odd m' i' => rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
          | even m' i' =>
              have hm : m' = m := by rw [AuxiliaryIndex.toNat, AuxiliaryIndex.toNat] at hd; omega
              subst hm
              have hi : i' ≠ i := fun hh => h (by rw [hh])
              clear hd h
              fin_cases i <;> fin_cases i' <;>
                first
                  | exact absurd rfl hi
                  | simp [AuxiliaryIndex.toMatrix, AuxiliaryIndex.position, matrix_aux11, Matrix.single]
    · rw [if_neg hd]


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux7 (k : Type*) [Field k] : LinearIndependent k (matrix_aux13 k) := by
  rw [linearIndependent_iff']
  intro s g hg I hI
  have hz := congrArg (linearMap_aux3 k I) hg
  rw [map_sum, map_zero] at hz
  rw [Finset.sum_eq_single_of_mem I hI ?_] at hz
  · simpa [map_apply_aux7] using hz
  · intro J _ hne
    simp [map_apply_aux7, Ne.symm hne]


/-- The displayed family is linearly independent. -/
theorem linearIndependent_family_aux6 (k : Type*) [Field k] : LinearIndependent k (distinguishedElement_aux3 k) := by
  have h : LinearIndependent k ((matrixPolynomialLieSubalgebra k).incl.toLinearMap ∘ distinguishedElement_aux3 k) :=
    linearIndependent_family_aux7 k
  exact LinearIndependent.of_comp _ h


/-- The specified element belongs to the span of the displayed generators. -/
theorem mem_span_aux4 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0)
    {P : Matrix (Fin 3) (Fin 3) (Polynomial k)} (hP : P ∈ matrixPolynomialLieSubalgebra k) :
    P ∈ Submodule.span k (Set.range (matrix_aux13 k)) := by
  obtain ⟨htr, hsig, hconst⟩ := hP
  rw [auxiliary_fact_aux10] at hsig
  obtain ⟨N, hN⟩ := exists_witness k P
  rw [hN]
  refine Submodule.sum_mem _ fun n _ => ?_
  have htrA : Matrix.trace (matrix_aux9 k n P) = 0 := trace_eq_zero k n htr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [map_apply_aux3] at hconst
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hconst
    rw [← hc, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨AuxiliaryIndex.base, ?_⟩)
    simp [matrix_aux13, AuxiliaryIndex.toNat, AuxiliaryIndex.toMatrix]
  · rcases Nat.even_or_odd n with he | ho
    · obtain ⟨r, hr⟩ := he
      obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 2 := ⟨r - 1, by omega⟩
      have hpow : (-1 : k) ^ n = 1 := by
        rw [hm, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; simp
      have hfix : matrix_aux14 (matrix_aux9 k n P) = matrix_aux9 k n P := by
        have := hsig n; rwa [hpow, one_smul] at this
      have hmem := mem_span_aux3 k h2 hfix
      have himg := Submodule.mem_map_of_mem (f := linearMap k n) hmem
      rw [Submodule.map_span, ← Set.range_comp] at himg
      refine Submodule.span_mono ?_ himg
      rintro _ ⟨i, rfl⟩
      exact ⟨AuxiliaryIndex.even m i, by simp [matrix_aux13, AuxiliaryIndex.toNat, AuxiliaryIndex.toMatrix, hm]⟩
    · obtain ⟨m, hm⟩ := ho
      have hpow : (-1 : k) ^ n = -1 := by rw [hm, pow_succ, pow_mul]; simp
      have hneg : matrix_aux14 (matrix_aux9 k n P) = -matrix_aux9 k n P := by
        have := hsig n; rwa [hpow, neg_one_smul] at this
      have hmem := mem_span_aux2 k htrA hneg
      have himg := Submodule.mem_map_of_mem (f := linearMap k n) hmem
      rw [Submodule.map_span, ← Set.range_comp] at himg
      refine Submodule.span_mono ?_ himg
      rintro _ ⟨i, rfl⟩
      exact ⟨AuxiliaryIndex.odd m i, by simp [matrix_aux13, AuxiliaryIndex.toNat, AuxiliaryIndex.toMatrix, hm]⟩


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux6 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) :
    Submodule.span k (Set.range (distinguishedElement_aux3 k)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨P, hP⟩ -
  have hmap : Submodule.map (matrixPolynomialLieSubalgebra k).incl.toLinearMap
      (Submodule.span k (Set.range (distinguishedElement_aux3 k))) = Submodule.span k (Set.range (matrix_aux13 k)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hmem : P ∈ Submodule.map (matrixPolynomialLieSubalgebra k).incl.toLinearMap
      (Submodule.span k (Set.range (distinguishedElement_aux3 k))) := by
    rw [hmap]; exact mem_span_aux4 k h2 hP
  obtain ⟨Q, hQ, hQP⟩ := hmem
  have hQeq : Q = ⟨P, hP⟩ := Subtype.ext hQP
  rwa [hQeq] at hQ


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux2 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) :
    Module.Basis AuxiliaryIndex k (matrixPolynomialLieSubalgebra k) :=
  Module.Basis.mk (linearIndependent_family_aux6 k) (submodule_eq_aux6 k h2).ge


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux6 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (I : AuxiliaryIndex) :
    distinguishedElement_aux2 k h2 I = distinguishedElement_aux3 k I := Module.Basis.mk_apply _ _ _


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux5 : (distinguishedElement_aux3 k AuxiliaryIndex.base : Matrix (Fin 3) (Fin 3) (Polynomial k)) = matrix_aux6 k := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [distinguishedElement_aux3, matrix_aux13, AuxiliaryIndex.toNat, AuxiliaryIndex.toMatrix, matrix_aux11, matrix_aux6, Matrix.single,
      Matrix.sub_apply, Polynomial.monomial_zero_left]


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux5 (m n : ℕ) (A B : Matrix (Fin 3) (Fin 3) k) :
    linearMap k m A * linearMap k n B = linearMap k (m + n) (A * B) := by
  refine Matrix.ext fun a b => ?_
  calc (linearMap k m A * linearMap k n B) a b
      = ∑ l : Fin 3, Polynomial.monomial (m + n) (A a l * B l b) := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun l _ => by
          rw [map_apply_aux4, map_apply_aux4, Polynomial.monomial_mul_monomial]
    _ = Polynomial.monomial (m + n) (∑ l : Fin 3, A a l * B l b) := (map_sum _ _ _).symm
    _ = linearMap k (m + n) (A * B) a b := by rw [map_apply_aux4, Matrix.mul_apply]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux17 (m n : ℕ) (A B : Matrix (Fin 3) (Fin 3) k) :
    ⁅linearMap k m A, linearMap k n B⁆ = linearMap k (m + n) ⁅A, B⁆ := by
  rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, map_apply_aux5, map_apply_aux5,
    add_comm n m, map_sub]


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply : matrix_aux4 k = linearMap k 1 (matrix_aux10 k 4) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrix_aux4, matrix_aux10, Matrix.single, Polynomial.monomial_one_one_eq_X]


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux1 : matrix_aux6 k = linearMap k 0 (matrix_aux11 k 0) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrix_aux6, matrix_aux11, Matrix.single, Matrix.sub_apply, Polynomial.monomial_zero_left]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux6 : ⁅matrix_aux11 k 0, matrix_aux10 k 4⁆ = (-1 : k) • matrix_aux10 k 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux34 : ⁅matrix_aux11 k 0, matrix_aux10 k 3⁆ = (1 : k) • matrix_aux10 k 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] ; ring


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux5 : ⁅matrix_aux11 k 0, matrix_aux10 k 2⁆ = (-3 : k) • matrix_aux10 k 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux33 : ⁅matrix_aux11 k 0, matrix_aux10 k 1⁆ = (2 : k) • matrix_aux10 k 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] ; ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux35 : ⁅matrix_aux11 k 1, matrix_aux10 k 0⁆ = (2 : k) • matrix_aux10 k 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] ; ring


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux36 : ⁅matrix_aux11 k 1, matrix_aux10 k 1⁆ = (1 : k) • matrix_aux10 k 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux7 : ⁅matrix_aux11 k 1, matrix_aux10 k 3⁆ = (-1 : k) • matrix_aux10 k 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux8 : ⁅matrix_aux11 k 1, matrix_aux10 k 4⁆ = (-2 : k) • matrix_aux10 k 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] ; ring


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux3 : ⁅matrix_aux10 k 4, matrix_aux10 k 0⁆ = (-1 : k) • matrix_aux11 k 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux4 : ⁅matrix_aux10 k 4, matrix_aux10 k 1⁆ = (-1 : k) • matrix_aux11 k 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux32 : ⁅matrix_aux10 k 0, matrix_aux10 k 3⁆ = (1 : k) • matrix_aux11 k 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix_aux11, matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le : (lieHom_aux3 k).range ≤ matrixPolynomialLieSubalgebra k := by
  intro P hP
  rw [LieHom.mem_range] at hP
  obtain ⟨a, rfl⟩ := hP
  have ha : a ∈ LieSubalgebra.lieSpan k (FreeLieAlgebra k (Fin 2))
      (Set.range (FreeLieAlgebra.of k)) := by
    rw [freeLie_eq]; trivial
  induction ha using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    have hval : lieHom_aux3 k (FreeLieAlgebra.of k i) = ![matrix_aux4 k, matrix_aux6 k] i := by
      simp only [lieHom_aux3, FreeLieAlgebra.lift_of_apply]
    rw [hval]
    fin_cases i
    · exact mem_submodule k
    · exact mem_submodule_aux1 k
  | zero => rw [map_zero]; exact LieSubalgebra.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact LieSubalgebra.add_mem _ hu hv
  | smul t u _ hu => rw [map_smul]; exact LieSubalgebra.smul_mem _ t hu
  | lie u v _ _ hu hv => rw [LieHom.map_lie]; exact LieSubalgebra.lie_mem _ hu hv


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux16 (k : Type*) [Field k] {c : k} (hc : c ≠ 0)
    {P : Matrix (Fin 3) (Fin 3) (Polynomial k)} :
    c • P ∈ (lieHom_aux3 k).range ↔ P ∈ (lieHom_aux3 k).range :=
  Submodule.smul_mem_iff (p := (lieHom_aux3 k).range.toSubmodule) hc


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux5 (k : Type*) [Field k] {m n : ℕ}
    {A B D : Matrix (Fin 3) (Fin 3) k}
    (hA : linearMap k m A ∈ (lieHom_aux3 k).range) (hB : linearMap k n B ∈ (lieHom_aux3 k).range)
    {c : k} (hc : c ≠ 0) (h : ⁅A, B⁆ = c • D) {d : ℕ} (hd : m + n = d) :
    linearMap k d D ∈ (lieHom_aux3 k).range := by
  subst hd
  have hlie := LieSubalgebra.lie_mem (lieHom_aux3 k).range hA hB
  rw [bracket_eq_aux17, h, map_smul] at hlie
  exact (mem_submodule_aux16 k hc).mp hlie


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux7 : linearMap k 1 (matrix_aux10 k 4) ∈ (lieHom_aux3 k).range := by
  rw [← map_apply, ← map_apply_aux14]
  exact LieHom.mem_range_self _ _


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux9 : linearMap k 0 (matrix_aux11 k 0) ∈ (lieHom_aux3 k).range := by
  rw [← map_apply_aux1, ← map_apply_aux15]
  exact LieHom.mem_range_self _ _


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux8 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (i : Fin 5) : linearMap k 1 (matrix_aux10 k i) ∈ (lieHom_aux3 k).range := by
  have hNX := mem_submodule_aux7 k
  have hNY := mem_submodule_aux9 k
  have e3 : linearMap k 1 (matrix_aux10 k 3) ∈ (lieHom_aux3 k).range :=
    mem_submodule_aux5 k hNY hNX (neg_ne_zero.mpr one_ne_zero) (auxiliary_fact_aux6 k) rfl
  have e2 : linearMap k 1 (matrix_aux10 k 2) ∈ (lieHom_aux3 k).range :=
    mem_submodule_aux5 k hNY e3 one_ne_zero (bracket_eq_aux34 k) rfl
  have e1 : linearMap k 1 (matrix_aux10 k 1) ∈ (lieHom_aux3 k).range :=
    mem_submodule_aux5 k hNY e2 (neg_ne_zero.mpr h3) (auxiliary_fact_aux5 k) rfl
  have e0 : linearMap k 1 (matrix_aux10 k 0) ∈ (lieHom_aux3 k).range :=
    mem_submodule_aux5 k hNY e1 h2 (bracket_eq_aux33 k) rfl
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact hNX


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux4 (k : Type*) [Field k]
    (h1 : ∀ j, linearMap k 1 (matrix_aux10 k j) ∈ (lieHom_aux3 k).range) {n : ℕ}
    (hn : ∀ j, linearMap k n (matrix_aux10 k j) ∈ (lieHom_aux3 k).range) (i : Fin 3) :
    linearMap k (1 + n) (matrix_aux11 k i) ∈ (lieHom_aux3 k).range := by
  fin_cases i
  · exact mem_submodule_aux5 k (h1 0) (hn 3) one_ne_zero (bracket_eq_aux32 k) rfl
  · exact mem_submodule_aux5 k (h1 4) (hn 0) (neg_ne_zero.mpr one_ne_zero)
      (auxiliary_fact_aux3 k) rfl
  · exact mem_submodule_aux5 k (h1 4) (hn 1) (neg_ne_zero.mpr one_ne_zero)
      (auxiliary_fact_aux4 k) rfl


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux3 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0)
    (hz1 : linearMap k 2 (matrix_aux11 k 1) ∈ (lieHom_aux3 k).range)
    (hz0 : linearMap k 2 (matrix_aux11 k 0) ∈ (lieHom_aux3 k).range)
    {n : ℕ} (hn : ∀ j, linearMap k n (matrix_aux10 k j) ∈ (lieHom_aux3 k).range) (i : Fin 5) :
    linearMap k (2 + n) (matrix_aux10 k i) ∈ (lieHom_aux3 k).range := by
  fin_cases i
  · exact mem_submodule_aux5 k hz1 (hn 0) h2 (bracket_eq_aux35 k) rfl
  · exact mem_submodule_aux5 k hz1 (hn 1) one_ne_zero (bracket_eq_aux36 k) rfl
  · exact mem_submodule_aux5 k hz0 (hn 3) one_ne_zero (bracket_eq_aux34 k) rfl
  · exact mem_submodule_aux5 k hz1 (hn 3) (neg_ne_zero.mpr one_ne_zero)
      (auxiliary_fact_aux7 k) rfl
  · exact mem_submodule_aux5 k hz1 (hn 4) (neg_ne_zero.mpr h2) (auxiliary_fact_aux8 k) rfl


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux6 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    ∀ (m : ℕ) (i : Fin 5), linearMap k (2 * m + 1) (matrix_aux10 k i) ∈ (lieHom_aux3 k).range := by
  have h1 := mem_submodule_aux8 k h2 h3
  have hz : ∀ j, linearMap k 2 (matrix_aux11 k j) ∈ (lieHom_aux3 k).range := fun j => by
    simpa using mem_submodule_aux4 k h1 (n := 1) h1 j
  intro m
  induction m with
  | zero => simpa using h1
  | succ m ih =>
      intro i
      have hdeg : 2 * (m + 1) + 1 = 2 + (2 * m + 1) := by ring
      rw [hdeg]
      exact mem_submodule_aux3 k h2 (hz 1) (hz 0) ih i


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux2 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (m : ℕ) (i : Fin 3) : linearMap k (2 * m + 2) (matrix_aux11 k i) ∈ (lieHom_aux3 k).range := by
  have hdeg : 2 * m + 2 = 1 + (2 * m + 1) := by ring
  rw [hdeg]
  exact mem_submodule_aux4 k (mem_submodule_aux8 k h2 h3)
    (mem_submodule_aux6 k h2 h3 m) i


/-- The specified element belongs to the indicated submodule. -/
theorem mem_submodule_aux12 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (I : AuxiliaryIndex) : matrix_aux13 k I ∈ (lieHom_aux3 k).range := by
  cases I with
  | base => exact mem_submodule_aux9 k
  | odd m i => exact mem_submodule_aux6 k h2 h3 m i
  | even m i => exact mem_submodule_aux2 k h2 h3 m i


/-- The range of the displayed Lie homomorphism is the indicated submodule. -/
theorem range_eq (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (lieHom_aux3 k).range = matrixPolynomialLieSubalgebra k := by
  refine le_antisymm (submodule_le k) fun P hP => ?_
  have hle : Submodule.span k (Set.range (matrix_aux13 k)) ≤ (lieHom_aux3 k).range.toSubmodule := by
    rw [Submodule.span_le]
    rintro Q ⟨I, rfl⟩
    exact mem_submodule_aux12 k h2 h3 I
  exact hle (mem_span_aux4 k h2 hP)


/-- The displayed submodules are equal. -/
theorem submodule_eq_aux1 (k : Type*) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    LinearMap.range (lieHom_aux3 k).toLinearMap = (matrixPolynomialLieSubalgebra k).toSubmodule :=
  congrArg LieSubalgebra.toSubmodule (range_eq k h2 h3)

end TwistedLoop


section Layers


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement (n i : ℕ) : AuxiliaryType k n := (fun u => ⁅distinguishedElement_aux8 k n, u⁆)^[i] (distinguishedElement_aux7 k n)


/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux2 (n : ℕ) : distinguishedElement k n 0 = distinguishedElement_aux7 k n := rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq (n i : ℕ) : distinguishedElement k n (i + 1) = ⁅distinguishedElement_aux8 k n, distinguishedElement k n i⁆ :=
  Function.iterate_succ_apply' _ _ _


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 (n : ℕ) : distinguishedElement k n 1 = -distinguishedElement_aux9 k n := by
  rw [bracket_eq, displayed_eq_aux2, distinguishedElement_aux9, ← lie_skew]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux69 (n i : ℕ) :
    lieHom_aux5 k n ((fun z => ⁅freeLieElement_aux4 k, z⁆)^[i] (freeLieElement_aux3 k)) = distinguishedElement k n i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', bracket_eq, ← ih, LieHom.map_lie]
      rfl


/-- The two displayed expressions are equal. -/
theorem displayed_eq : distinguishedElement k 4 5 = 0 := by
  have hmem : (fun z => ⁅freeLieElement_aux4 k, z⁆)^[4 + 1] (freeLieElement_aux3 k) ∈ indexedLieIdeal k 4 :=
    LieSubmodule.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  rw [← bracket_eq_aux69 k 4 5, mem_submodule_aux13]
  exact hmem


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux44 (n i j : ℕ) :
    ⁅distinguishedElement_aux8 k n, ⁅distinguishedElement k n i, distinguishedElement k n j⁆⁆
      = ⁅distinguishedElement k n (i + 1), distinguishedElement k n j⁆ + ⁅distinguishedElement k n i, distinguishedElement k n (j + 1)⁆ := by
  rw [leibniz_lie, bracket_eq, bracket_eq]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux19 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 1⁆ = 0 := by
  rw [displayed_eq_aux2, displayed_eq_aux1, lie_neg, bracket_eq_aux43, neg_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux20 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 2⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement k 4 0, distinguishedElement k 4 1⁆⁆ = 0 := by rw [bracket_eq_aux19, lie_zero]
  rw [bracket_eq_aux44] at h
  simpa using h


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux22 : ⁅distinguishedElement k 4 1, distinguishedElement k 4 2⁆ + ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement k 4 0, distinguishedElement k 4 2⁆⁆ = 0 := by rw [bracket_eq_aux20, lie_zero]
  rw [bracket_eq_aux44] at h
  simpa using h


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux24 :
    (2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ + ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement k 4 1, distinguishedElement k 4 2⁆ + ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆⁆ = 0 := by
    rw [bracket_eq_aux22, lie_zero]
  rw [lie_add, bracket_eq_aux44, bracket_eq_aux44] at h
  simp only [Nat.reduceAdd, lie_self, zero_add] at h
  rw [← h]; module


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux26 :
    (2 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 3⁆ + (3 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4,
      (2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ + ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆⁆ = 0 := by
    rw [bracket_eq_aux24, lie_zero]
  rw [lie_add, lie_smul, bracket_eq_aux44, bracket_eq_aux44] at h
  simp only [Nat.reduceAdd, zero_add, displayed_eq, lie_zero, add_zero] at h
  rw [← h]; module


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux29 : (5 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 4⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4,
      (2 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 3⁆ + (3 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆⁆ = 0 := by
    rw [bracket_eq_aux26, lie_zero]
  rw [lie_add, lie_smul, lie_smul, bracket_eq_aux44, bracket_eq_aux44] at h
  simp only [Nat.reduceAdd, lie_self, zero_add, displayed_eq, lie_zero, add_zero] at h
  rw [← h]; module


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux31 : (5 : k) • ⁅distinguishedElement k 4 3, distinguishedElement k 4 4⁆ = 0 := by
  have h : ⁅distinguishedElement_aux8 k 4, (5 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 4⁆⁆ = 0 := by
    rw [bracket_eq_aux29, lie_zero]
  rw [lie_smul, bracket_eq_aux44] at h
  simp only [Nat.reduceAdd, displayed_eq, lie_zero, add_zero] at h
  exact h


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux23 : ⁅distinguishedElement k 4 1, distinguishedElement k 4 2⁆ = -⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ := by
  rw [eq_neg_iff_add_eq_zero]; exact bracket_eq_aux22 k


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux21 : ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆⁆ = 0 := by
  have h3 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ = -⁅distinguishedElement k 4 1, distinguishedElement k 4 2⁆ := by
    rw [bracket_eq_aux23, neg_neg]
  rw [h3, lie_neg, leibniz_lie, bracket_eq_aux19, bracket_eq_aux20]
  simp

end Layers

section LayersField

variable (k : Type*) [Field k]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux28 (h5 : (5 : k) ≠ 0) : ⁅distinguishedElement k 4 2, distinguishedElement k 4 4⁆ = 0 := by
  have h : (5 : k)⁻¹ • ((5 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 4⁆) = 0 := by
    rw [bracket_eq_aux29, smul_zero]
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at h


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux30 (h5 : (5 : k) ≠ 0) : ⁅distinguishedElement k 4 3, distinguishedElement k 4 4⁆ = 0 := by
  have h : (5 : k)⁻¹ • ((5 : k) • ⁅distinguishedElement k 4 3, distinguishedElement k 4 4⁆) = 0 := by
    rw [bracket_eq_aux31, smul_zero]
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at h


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux25 (h2 : (2 : k) ≠ 0) :
    ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ = -((2 : k)⁻¹ • ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆) := by
  have h : (2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ = -⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ := by
    rw [eq_neg_iff_add_eq_zero]; exact bracket_eq_aux24 k
  have h' := congrArg (fun u : AuxiliaryType k 4 => (2 : k)⁻¹ • u) h
  simp only [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_neg] at h'
  exact h'


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux27 (h2 : (2 : k) ≠ 0) :
    ⁅distinguishedElement k 4 2, distinguishedElement k 4 3⁆ = -(((2 : k)⁻¹ * 3) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆) := by
  have h : (2 : k) • ⁅distinguishedElement k 4 2, distinguishedElement k 4 3⁆ = -((3 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆) := by
    rw [eq_neg_iff_add_eq_zero]; exact bracket_eq_aux26 k
  have h' := congrArg (fun u : AuxiliaryType k 4 => (2 : k)⁻¹ • u) h
  simp only [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_neg] at h'
  exact h'


/-- The specified element belongs to the span of the displayed generators. -/
theorem mem_span (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    ⁅distinguishedElement k 4 i, distinguishedElement k 4 j⁆ ∈ Submodule.span k
      ({⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆,
        ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆} : Set (AuxiliaryType k 4)) := by
  have m03 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ ∈ Submodule.span k
      ({⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆,
        ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆} : Set (AuxiliaryType k 4)) := Submodule.subset_span (by simp)
  have m04 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ ∈ Submodule.span k
      ({⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆,
        ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆} : Set (AuxiliaryType k 4)) := Submodule.subset_span (by simp)
  have m14 : ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆ ∈ Submodule.span k
      ({⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆,
        ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆} : Set (AuxiliaryType k 4)) := Submodule.subset_span (by simp)
  set N : Submodule k (AuxiliaryType k 4) := Submodule.span k
    ({⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆,
      ⁅distinguishedElement k 4 1, distinguishedElement k 4 4⁆} : Set (AuxiliaryType k 4)) with hNdef
  clear_value N
  interval_cases i <;> interval_cases j

  · rw [lie_self]; exact N.zero_mem
  · rw [bracket_eq_aux19]; exact N.zero_mem
  · rw [bracket_eq_aux20]; exact N.zero_mem
  · exact m03
  · exact m04

  · rw [← lie_skew, bracket_eq_aux19, neg_zero]; exact N.zero_mem
  · rw [lie_self]; exact N.zero_mem
  · rw [bracket_eq_aux23]; exact neg_mem m03
  · rw [bracket_eq_aux25 k h2]; exact neg_mem (N.smul_mem _ m04)
  · exact m14

  · rw [← lie_skew, bracket_eq_aux20, neg_zero]; exact N.zero_mem
  · rw [← lie_skew, bracket_eq_aux23, neg_neg]; exact m03
  · rw [lie_self]; exact N.zero_mem
  · rw [bracket_eq_aux27 k h2]; exact neg_mem (N.smul_mem _ m14)
  · rw [bracket_eq_aux28 k h5]; exact N.zero_mem

  · rw [← lie_skew]; exact neg_mem m03
  · rw [← lie_skew, bracket_eq_aux25 k h2, neg_neg]; exact N.smul_mem _ m04
  · rw [← lie_skew, bracket_eq_aux27 k h2, neg_neg]; exact N.smul_mem _ m14
  · rw [lie_self]; exact N.zero_mem
  · rw [bracket_eq_aux30 k h5]; exact N.zero_mem

  · rw [← lie_skew]; exact neg_mem m04
  · rw [← lie_skew]; exact neg_mem m14
  · rw [← lie_skew, bracket_eq_aux28 k h5, neg_zero]; exact N.zero_mem
  · rw [← lie_skew, bracket_eq_aux30 k h5, neg_zero]; exact N.zero_mem
  · rw [lie_self]; exact N.zero_mem

end LayersField

end RepresentationTheory.LieAlgebra.ExplicitConstructions


attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux3
  RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux4
  RepresentationTheory.LieAlgebra.ExplicitConstructions.indexedLieIdeal
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType
  RepresentationTheory.LieAlgebra.ExplicitConstructions.instLieRing
  RepresentationTheory.LieAlgebra.ExplicitConstructions.instLieAlgebra
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux7
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux8
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux9
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux6
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux3
  RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux5
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux7
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux4
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux8
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix
  RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux4
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.polynomial
  RepresentationTheory.LieAlgebra.ExplicitConstructions.freeLieElement_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux5
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux4
  RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux14
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10
  RepresentationTheory.LieAlgebra.ExplicitConstructions.algHom_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.algHom_aux1
  RepresentationTheory.LieAlgebra.ExplicitConstructions.algHom
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux9
  RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap
  RepresentationTheory.LieAlgebra.ExplicitConstructions.instDecidableEqAuxiliaryIndex.decEq
  RepresentationTheory.LieAlgebra.ExplicitConstructions.instDecidableEqAuxiliaryIndex
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.toNat
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.toMatrix
  RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux13
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.position
  RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux3
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2
  RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement
