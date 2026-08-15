/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.Alignment.Attribute

/-!
# Character column orthogonality

The second orthogonality relation for characters of finite groups, proved by computing the trace
of simultaneous left and right multiplication on the group algebra.
-/

open CategoryTheory

universe u

variable {G : Type u} [Group G] [Fintype G]

namespace RepresentationTheory.FiniteGroup.CharacterColumnOrthogonality

open RepresentationTheory.FDRep.GroupAlgebraDecomposition

section ConjugatorCounting

/-- A chosen element conjugating g to h induces an equivalence between the centralizer of g and the subtype of elements conjugating g to h. -/
noncomputable def FiniteGroup.centralizerEquivConjugators (g h c : G)
    (hc : c * g * c⁻¹ = h) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃
      {x : G // x * g * x⁻¹ = h} where
  toFun z := ⟨c * z.1, by
    have hz := z.2
    rw [Subgroup.mem_centralizer_iff] at hz
    have hzg : z.1 * g * z.1⁻¹ = g := by
      have := (hz g (Set.mem_singleton g)).symm
      rw [mul_inv_eq_iff_eq_mul, this]
    calc c * z.1 * g * (c * z.1)⁻¹
        = c * (z.1 * g * z.1⁻¹) * c⁻¹ := by group
      _ = c * g * c⁻¹ := by rw [hzg]
      _ = h := hc⟩
  invFun x := ⟨c⁻¹ * x.1, by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hx := x.2
    have key : (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ = g := by
      calc _ = c⁻¹ * (x.1 * g * x.1⁻¹) * c := by group
        _ = c⁻¹ * h * c := by rw [hx]
        _ = c⁻¹ * (c * g * c⁻¹) * c := by rw [hc]
        _ = g := by group
    calc g * (c⁻¹ * x.1)
        = (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ * (c⁻¹ * x.1) := by
          rw [key]
      _ = (c⁻¹ * x.1) * g := by group⟩
  left_inv z := by ext; simp
  right_inv x := by ext; simp

open scoped Classical in
/-- If g and h are not conjugate, the finite set of elements conjugating g to h is empty. -/
theorem FiniteGroup.conjugators_eq_empty_of_not_isConj (g h : G)
    (hnh : ¬IsConj g h) :
    Finset.filter (fun x => x * g * x⁻¹ = h) Finset.univ = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x _ heq
  exact hnh (isConj_iff.mpr ⟨x, heq⟩)

open scoped Classical in
/-- When g and h are conjugate, the number of elements conjugating g to h equals the order of the centralizer of g. -/
theorem FiniteGroup.card_conjugators_eq_card_centralizer (g h : G)
    (hgh : IsConj g h) :
    (Finset.filter (fun x => x * g * x⁻¹ = h) Finset.univ).card =
      Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    (FiniteGroup.centralizerEquivConjugators g h c hc).symm

open scoped Classical in
/-- The number of elements conjugating g to h is the order of the centralizer of g when g and h are conjugate, and zero otherwise. -/
theorem FiniteGroup.card_conjugators_eq_ite_isConj (g h : G) :
    (Finset.filter (fun x => x * g * x⁻¹ = h) Finset.univ).card =
      if IsConj g h
        then Fintype.card ↥(Subgroup.centralizer ({g} : Set G))
        else 0 := by
  split
  · exact FiniteGroup.card_conjugators_eq_card_centralizer g h ‹_›
  · simp [FiniteGroup.conjugators_eq_empty_of_not_isConj g h ‹_›]

open Classical in
/-- The number of x satisfying g * x * h⁻¹ = x equals the number of x satisfying x * g * x⁻¹ = h. -/
theorem FiniteGroup.card_mul_mul_inv_fixed_eq_card_conjugators (g h : G) :
    (Finset.filter (fun x : G => g * x * h⁻¹ = x) Finset.univ).card =
    (Finset.filter (fun x : G => x * g * x⁻¹ = h) Finset.univ).card := by
  classical
  rw [show (Finset.filter (fun x : G => g * x * h⁻¹ = x) Finset.univ) =
    (Finset.filter (fun x : G => x * g * x⁻¹ = h) Finset.univ).map
      ⟨fun x => x⁻¹, inv_injective⟩ from ?_]
  · rw [Finset.card_map]
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      refine ⟨x⁻¹, ?_, inv_inv x⟩
      rw [inv_inv]
      have h1 : g * x = x * h := by
        calc g * x = g * x * h⁻¹ * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = x * h := by rw [hx]
      calc x⁻¹ * g * x = x⁻¹ * (x * h) := by rw [mul_assoc, h1]
        _ = h := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    · intro ⟨a, ha, hax⟩
      rw [← hax]
      rw [← ha]
      group

end ConjugatorCounting

variable {k : Type u} [Field k] [IsAlgClosed k]

section ColumnOrthogonality

open Classical

variable [NeZero (Nat.card G : k)]

private lemma matrix_stdBasis_repr {n : ℕ} (M : Matrix (Fin n) (Fin n) k)
    (p q : Fin n) :
    (Matrix.stdBasis k (Fin n) (Fin n)).repr M (p, q) = M p q := by
  simp [Matrix.stdBasis, Pi.basis_repr, Pi.basisFun_repr]

private lemma matrix_single_mul_entry {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) k) (i j p q : Fin n) :
    (M * Matrix.single i j (1 : k) * N) p q = M p i * N j q := by
  rw [Matrix.mul_assoc]
  rw [show Matrix.single i j (1 : k) * N = fun r c => if r = i then N j c else 0 from by
    ext r c; simp [Matrix.mul_apply, Matrix.single_apply,
      Finset.mem_univ, ite_and, ite_mul, one_mul, zero_mul, eq_comm]]
  simp [Matrix.mul_apply, Finset.mem_univ]

/-- The character of the i-th indexed representation at g is the trace of the matrix produced by the displayed auxiliary map from the group-algebra element supported at g. -/
lemma _root_.RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.character_eq_matrixTrace
    (D : DecompositionData k G) (i : Fin D.count) (g : G) :
    (D.representation i).character g =
      Matrix.trace (D.groupAlgebraEquivMatrix (MonoidAlgebra.of k G g) i) := by
  change LinearMap.trace k _
    (Matrix.mulVecLin (D.matrixBlockHom i (MonoidAlgebra.of k G g))) = _
  rw [← Matrix.toLin'_apply']
  rw [Matrix.trace_toLin'_eq]
  rfl

set_option maxHeartbeats 800000 in
/-- The trace of simultaneous left and right multiplication by group-algebra elements a and b equals the sum of products of traces of the indexed matrices produced by the displayed auxiliary map. -/
lemma MonoidAlgebra.trace_mulLeftRight_eq_sum_matrixTrace_mul
    (D : DecompositionData k G) (a b : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G)
      (LinearMap.mulLeftRight k (a, b)) =
    ∑ i : Fin D.count,
      Matrix.trace (D.groupAlgebraEquivMatrix a i) *
        Matrix.trace (D.groupAlgebraEquivMatrix b i) := by
  rw [← LinearMap.trace_conj' _ D.groupAlgebraEquivMatrix.toLinearEquiv,
    AlgEquiv.linearEquivConj_mulLeftRight D.groupAlgebraEquivMatrix (a, b)]
  let s := fun i => Matrix.stdBasis k (Fin (D.dimension i)) (Fin (D.dimension i))
  let bPi := Pi.basis s
  rw [LinearMap.trace_eq_matrix_trace k bPi]
  suffices diag_entry : ∀ x : (j : Fin D.count) × Fin (D.dimension j) × Fin (D.dimension j),
      (LinearMap.toMatrix bPi bPi
        (LinearMap.mulLeftRight k
          (Prod.map (⇑D.groupAlgebraEquivMatrix) (⇑D.groupAlgebraEquivMatrix) (a, b)))) x x =
      D.groupAlgebraEquivMatrix a x.1 x.2.1 x.2.1 *
        D.groupAlgebraEquivMatrix b x.1 x.2.2 x.2.2 by
    simp only [Matrix.trace, Matrix.diag_apply, diag_entry]
    simp_rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    congr 1; ext j
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  intro ⟨j, p, q⟩
  simp only [LinearMap.toMatrix_apply, LinearMap.mulLeftRight_apply, Prod.map_apply]
  rw [Pi.basis_repr]
  rw [show bPi ⟨j, (p, q)⟩ = Pi.single j (Matrix.single p q 1)
    from by rw [Pi.basis_apply, Matrix.stdBasis_eq_single]]
  simp only [Pi.mul_apply, Pi.single_eq_same]
  rw [matrix_stdBasis_repr (k := k)]
  exact matrix_single_mul_entry (k := k) _ _ _ _ _ _

/-- For group elements g and h, the trace of left-right multiplication by their group-algebra elements at g and h⁻¹ is the centralizer order when they are conjugate and zero otherwise. -/
theorem MonoidAlgebra.trace_mulLeftRight_single_inv (g h : G) :
    LinearMap.trace k (MonoidAlgebra k G)
      (LinearMap.mulLeftRight k
        (MonoidAlgebra.of k G g, MonoidAlgebra.of k G h⁻¹)) =
      if IsConj g h
        then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  let b := MonoidAlgebra.basis G k
  rw [LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeftRight_apply, MonoidAlgebra.of_apply]
  conv_lhs =>
    arg 2; ext x
    rw [show b x = MonoidAlgebra.single x 1 from by simp [b, MonoidAlgebra.basis]]
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [show b.repr (MonoidAlgebra.single (g * x * h⁻¹) 1) x =
        if g * x * h⁻¹ = x then 1 else 0 from by
      change (LinearEquiv.refl k (G →₀ k) (Finsupp.single (g * x * h⁻¹) 1)) x = _
      simp [Finsupp.single_apply]]
  trans ↑(∑ x : G, if g * x * h⁻¹ = x then (1 : ℕ) else 0)
  · push_cast; rfl
  rw [Finset.sum_boole (fun x => g * x * h⁻¹ = x) Finset.univ,
    FiniteGroup.card_mul_mul_inv_fixed_eq_card_conjugators g h,
    FiniteGroup.card_conjugators_eq_ite_isConj g h]
  split <;> simp

/-- The sum over the displayed auxiliary family of the character at g times the character at h⁻¹ is the centralizer order when g and h are conjugate and zero otherwise. -/
theorem FiniteGroup.sum_auxiliaryFamily_characters_mul_inv
    (D : DecompositionData k G) (g h : G) :
    ∑ i : Fin D.count,
      (D.representation i).character g * (D.representation i).character h⁻¹ =
      if IsConj g h
        then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  simp_rw [D.character_eq_matrixTrace]
  have key := MonoidAlgebra.trace_mulLeftRight_eq_sum_matrixTrace_mul D
    (MonoidAlgebra.of k G g) (MonoidAlgebra.of k G h⁻¹)
  rw [← key]
  exact MonoidAlgebra.trace_mulLeftRight_single_inv g h

/-- The sum of products of character values is independent of the choice of complete pairwise nonisomorphic family of simple finite-dimensional representations. -/
theorem FiniteGroup.sum_characterProducts_eq_of_complete_simple_families
    {n : ℕ} (V W : Fin n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hVinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hVsurj : ∀ (U : FDRep k G), Simple U → ∃ i, Nonempty (U ≅ V i))
    (hW : ∀ i, Simple (W i))
    (hWinj : ∀ i j, Nonempty ((W i) ≅ (W j)) → i = j)
    (hWsurj : ∀ (U : FDRep k G), Simple U → ∃ i, Nonempty (U ≅ W i))
    (g h : G) :
    ∑ i, (V i).character g * (V i).character h =
    ∑ i, (W i).character g * (W i).character h := by
  have hσ : ∀ i, ∃ j, Nonempty (V i ≅ W j) := fun i => hWsurj (V i) (hV i)
  choose σ hσ using hσ
  have hσ_inj : Function.Injective σ := by
    intro i i' heq
    obtain ⟨f⟩ := hσ i
    obtain ⟨f'⟩ := hσ i'
    rw [heq] at f
    exact hVinj i i' ⟨f.trans f'.symm⟩
  let e := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ_inj)
  have hchar : ∀ i, (V i).character = (W (σ i)).character := by
    intro i; obtain ⟨f⟩ := hσ i; exact FDRep.char_iso f
  conv_lhs => arg 2; ext i; rw [hchar i]
  exact Equiv.sum_comp e (fun j => (W j).character g * (W j).character h)

/-- The indexed family consists of simple representations, has no isomorphic members at distinct indices, and contains a representative of every simple finite-dimensional representation. -/
theorem _root_.RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.simpleRepresentatives_spec
    (D : DecompositionData k G) :
    (∀ i, Simple (D.representation i)) ∧
    (∀ i j, Nonempty ((D.representation i) ≅ (D.representation j)) → i = j) ∧
    (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ D.representation i)) :=
  ⟨D.simple_representation, D.representation_index_eq_of_iso,
    D.exists_iso_representation_of_simple⟩

end ColumnOrthogonality

open scoped Classical in
/-- For a complete pairwise nonisomorphic family of simple representations, the sum of the character values at g times those at the inverse of h is the centralizer order when g and h are conjugate and zero otherwise. -/
@[source_ref "Chapter4/Introduction_4.8" (role := primary),
  source_ref "Chapter4/Theorem4.5.4" (role := primary)]
theorem FiniteGroup.sum_complete_simple_characters_mul_inv
    [NeZero (Nat.card G : k)]
    (D : DecompositionData k G) (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W →
      ∃ i, Nonempty (W ≅ V i))
    (g h : G) :
    ∑ i : Fin D.count,
      (V i).character g * (V i).character h⁻¹ =
      if IsConj g h
        then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  classical
  obtain ⟨hcS, hcI, hcSurj⟩ := D.simpleRepresentatives_spec
  rw [FiniteGroup.sum_characterProducts_eq_of_complete_simple_families V D.representation
    hV hinj hsurj hcS hcI hcSurj g h⁻¹]
  exact FiniteGroup.sum_auxiliaryFamily_characters_mul_inv D g h

end RepresentationTheory.FiniteGroup.CharacterColumnOrthogonality
