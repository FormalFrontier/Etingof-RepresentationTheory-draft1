/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.MatrixBoundedVectors
import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.Alignment.Attribute

/-!
# Adjacency-input set cardinalities

Finiteness and cardinality results for sets determined by exceptional finite integer matrix models.
-/

namespace RepresentationTheory.AdjInputSetCardinalities




set_option backward.isDefEq.respectTransparency false

section ETypeRootCounts

open Matrix Finset




private lemma E6_sos (a b c d e f : ℤ) :
    6 * (2*((a : ℤ)^2+b^2+c^2+d^2+e^2+f^2) -
      2*(a*b+b*c+c*d+d*e+c*f)) =
    3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
    (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E6_qf (x : Fin 6 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring


private lemma E6_bound (x : Fin 6 → ℤ)
    (hr : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix 6 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 4 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) = 2 := by
    have := hr.2; rw [E6_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2
  set d := x 3; set e := x 4; set f := x 5
  have hs : 3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
      (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 = 12 := by
    nlinarith [E6_sos a b c d e f]
  have hc : c ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*d-2*c), sq_nonneg (c-4)]
  have hb : b ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hd : d ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg c, sq_nonneg (3*d-2*c-4)]
  have ha : a ≤ 3 := by
    nlinarith [sq_nonneg (2*e-d), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have he : e ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*e-d-3)]
  have hf : f ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*f-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega



set_option linter.style.maxHeartbeats false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma E6_count :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 6 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix 4).card = 36 := by
  decide


/-- Using six as the parameter and the `adj` field as input gives a finite set with thirty-six elements. -/
@[source_ref "Chapter6/Example6.4.9" (role := primary)]
theorem set_from_adj_at_six_finite_and_ncard_eq :
    (RepresentationTheory.MatrixBoundedVectors.integerVectors 6 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix).Finite ∧
    Set.ncard
      (RepresentationTheory.MatrixBoundedVectors.integerVectors 6 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix) = 36 := by
  obtain ⟨hfin, hcard⟩ := RepresentationTheory.MatrixBoundedVectors.integerVectors_finite_ncard_eq_boundedVectors_card E6_bound
  exact ⟨hfin, hcard ▸ E6_count⟩




private def addOne : List (ℤ × ℕ) → ℤ → List (ℤ × ℕ)
  | [], v => [(v, 1)]
  | (w, n) :: t, v => if v = w then (w, n + 1) :: t else (w, n) :: addOne t v


private def lookupH : List (ℤ × ℕ) → ℤ → ℕ
  | [], _ => 0
  | (w, n) :: t, v => if v = w then n else lookupH t v


private def histL (l : List ℤ) : List (ℤ × ℕ) := l.foldl addOne []


private def pairCount (l1 : List ℤ) (h2 : List (ℤ × ℕ)) (T : ℤ) : ℕ :=
  (l1.map (fun a => lookupH h2 (T - a))).sum

private lemma lookup_addOne (h : List (ℤ × ℕ)) (v s : ℤ) :
    lookupH (addOne h v) s = lookupH h s + (if s = v then 1 else 0) := by
  induction h with
  | nil => simp only [addOne, lookupH]; split <;> rename_i hsv <;> simp_all
  | cons hd tl ih =>
    obtain ⟨w, n⟩ := hd; simp only [addOne]
    split <;> rename_i hvw
    · subst hvw; simp only [lookupH]; split <;> rename_i hsw <;> simp_all
    · simp only [lookupH]; split <;> rename_i hsw <;> simp_all; omega

private lemma lookupH_foldl (l : List ℤ) (acc : List (ℤ × ℕ)) (s : ℤ) :
    lookupH (l.foldl addOne acc) s = lookupH acc s + l.count s := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, lookup_addOne, List.count_cons]
    simp only [beq_iff_eq]; split_ifs <;> omega


private lemma lookupH_histL (l : List ℤ) (s : ℤ) : lookupH (histL l) s = l.count s := by
  rw [histL, lookupH_foldl]; simp [lookupH]


private lemma count_preimage {α : Type*} [Fintype α] [DecidableEq α] (Q : α → ℤ) (s : ℤ) :
    (univ.filter (fun a => Q a = s)).card = Multiset.count s (univ.val.map Q) := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  exact congrArg _ (Multiset.filter_congr (fun a _ => by rw [eq_comm]))

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1000000 in

private lemma pair_count_bridge {G1 G2 : Type*} [Fintype G1] [Fintype G2]
    [DecidableEq G1] [DecidableEq G2]
    (Q1 : G1 → ℤ) (Q2 : G2 → ℤ) (l1 l2 : List ℤ) (T : ℤ)
    (h1 : (l1 : Multiset ℤ) = univ.val.map Q1) (h2 : (l2 : Multiset ℤ) = univ.val.map Q2) :
    (univ.filter (fun p : G1 × G2 => Q1 p.1 + Q2 p.2 = T)).card = pairCount l1 (histL l2) T := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have inner : ∀ g1 : G1, (∑ g2 : G2, if Q1 g1 + Q2 g2 = T then 1 else 0)
      = lookupH (histL l2) (T - Q1 g1) := by
    intro g1
    rw [lookupH_histL, ← Multiset.coe_count, h2, ← count_preimage, Finset.card_filter]
    refine Finset.sum_congr rfl (fun g2 _ => ?_)
    congr 1; simp only [eq_iff_iff]; constructor <;> intro h <;> linarith
  simp_rw [inner]
  rw [pairCount, ← Multiset.sum_coe, ← Multiset.map_coe, h1, Multiset.map_map]; rfl




private lemma E7_sos (a b c d e f g : ℤ) :
    12 * (2*((a : ℤ)^2+b^2+c^2+d^2+e^2+f^2+g^2) -
      2*(a*b+b*c+c*d+d*e+e*f+c*g)) =
    6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
    2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
    (4*d-3*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E7_qf (x : Fin 7 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2+x 6^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 2*x 6) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring


private lemma E7_bound (x : Fin 7 → ℤ)
    (hr : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 5 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 2*x 6) = 2 :=
    by have := hr.2; rw [E7_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6
  have hs : 6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
      2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
      (4*d-3*c)^2 + c^2 = 24 := by
    nlinarith [E7_sos a b c d e f g]
  have : c ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg (4*d-3*c),
      sq_nonneg (c-5)]
  have : d ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg c,
      sq_nonneg (4*d-3*c-5)]
  have : b ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*b-2*c-4)]
  have : e ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*e-2*d-4)]
  have : a ≤ 4 := by
    nlinarith [sq_nonneg (2*f-e), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*a-b-3)]
  have : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*f-e-3)]
  have : g ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*g-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega




private abbrev E7.T3 := Fin 5 × Fin 5 × Fin 5


private def asm7 (c : Fin 5) (g1 g2 : E7.T3) : Fin 7 → Fin 5 :=
  ![g1.1, g1.2.1, c, g2.1, g2.2.1, g2.2.2, g1.2.2]


private def dis7 (v : Fin 7 → Fin 5) : Fin 5 × E7.T3 × E7.T3 :=
  (v 2, (v 0, v 1, v 6), (v 3, v 4, v 5))

set_option maxRecDepth 8000 in
private def E7equiv : (Fin 7 → Fin 5) ≃ Fin 5 × E7.T3 × E7.T3 where
  toFun := dis7
  invFun w := asm7 w.1 w.2.1 w.2.2
  left_inv v := by funext i; fin_cases i <;> simp [asm7, dis7]
  right_inv w := by
    obtain ⟨c, ⟨a, b, d⟩, ⟨e, f, g⟩⟩ := w
    simp only [asm7, dis7, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue]


private def q1_7 (c : Fin 5) (g : E7.T3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(c:ℤ) - 2*(c:ℤ)*(g.2.2:ℤ)


private def q2_7 (c : Fin 5) (g : E7.T3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(g.2.2:ℤ) - 2*(c:ℤ)*(g.1:ℤ)

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1000000 in

private lemma E7_form (c : Fin 5) (g1 g2 : E7.T3) :
    dotProduct (fun i => ((asm7 c g1 g2) i : ℤ))
      ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix).mulVec (fun i => ((asm7 c g1 g2) i : ℤ)))
    = 2*(c:ℤ)^2 + q1_7 c g1 + q2_7 c g2 := by
  rw [show (2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix) = !![
    (2:ℤ),-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1; 0,0,-1,2,-1,0,0;
    0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0; 0,0,-1,0,0,0,2] from by decide]
  simp only [asm7, q1_7, q2_7, dotProduct, mulVec, Fin.sum_univ_seven, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring


private def qf7 (x : Fin 7 → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix).mulVec x)

set_option maxRecDepth 10000 in

private lemma E7_root_filter : RepresentationTheory.MatrixBoundedVectors.boundedVectors 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix 5 =
    (univ.filter (fun v : Fin 7 → Fin 5 => qf7 (fun i => ((v i : ℤ))) = 2)) := by
  rw [RepresentationTheory.MatrixBoundedVectors.boundedVectors]
  apply Finset.filter_congr
  intro v _
  simp only [qf7, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro h0; rw [h0] at h; simp [dotProduct] at h


private def vals1_7 (c : Fin 5) : List ℤ :=
  (List.finRange 5).flatMap fun a => (List.finRange 5).flatMap fun b =>
    (List.finRange 5).map fun d => q1_7 c (a, b, d)


private def vals2_7 (c : Fin 5) : List ℤ :=
  (List.finRange 5).flatMap fun a => (List.finRange 5).flatMap fun b =>
    (List.finRange 5).map fun d => q2_7 c (a, b, d)

set_option maxRecDepth 10000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2000000 in

private lemma E7_count_eq :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix 5).card =
    ∑ c : Fin 5, (univ.filter (fun p : E7.T3 × E7.T3 =>
      q1_7 c p.1 + q2_7 c p.2 = 2 - 2*(c:ℤ)^2)).card := by
  rw [E7_root_filter]
  rw [show (univ.filter (fun v : Fin 7 → Fin 5 => qf7 (fun i => ((v i : ℤ))) = 2)).card
      = (univ.filter (fun w : Fin 5 × E7.T3 × E7.T3 =>
          2*(w.1:ℤ)^2 + q1_7 w.1 w.2.1 + q2_7 w.1 w.2.2 = 2)).card from ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    simp only [eq_iff_iff]
    constructor <;> intro h <;> linarith
  · apply Finset.card_bij' (fun v _ => E7equiv v) (fun w _ => E7equiv.symm w)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have hform : qf7 (fun i => ((a i : ℤ))) = 2*((E7equiv a).1:ℤ)^2
          + q1_7 (E7equiv a).1 (E7equiv a).2.1 + q2_7 (E7equiv a).1 (E7equiv a).2.2 := by
        conv_lhs => rw [show a = E7equiv.symm (E7equiv a) from (E7equiv.symm_apply_apply a).symm]
        rw [qf7]; exact E7_form _ _ _
      rw [hform] at ha; exact ha
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      have hform : qf7 (fun i => (((E7equiv.symm b) i : ℤ))) = 2*(b.1:ℤ)^2
          + q1_7 b.1 b.2.1 + q2_7 b.1 b.2.2 := by
        rw [qf7]; obtain ⟨c, g1, g2⟩ := b; exact E7_form _ _ _
      rw [hform]; exact hb
    · intro a _; exact E7equiv.symm_apply_apply a
    · intro b _; exact E7equiv.apply_symm_apply b

set_option maxRecDepth 100000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 10000000 in
private lemma E7_count :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix 5).card = 63 := by
  rw [E7_count_eq]
  have hb : ∀ c : Fin 5, (univ.filter (fun p : E7.T3 × E7.T3 =>
        q1_7 c p.1 + q2_7 c p.2 = 2 - 2*(c:ℤ)^2)).card
      = pairCount (vals1_7 c) (histL (vals2_7 c)) (2 - 2*(c:ℤ)^2) :=
    fun c => pair_count_bridge (q1_7 c) (q2_7 c) _ _ _ rfl rfl
  rw [Finset.sum_congr rfl (fun c _ => hb c)]
  decide


/-- The set obtained with parameter seven from the `adj` field is finite and has sixty-three elements. -/
@[source_ref "Chapter6/Example6.4.9" (role := primary)]
theorem set_from_adj_at_seven_finite_and_ncard_eq :
    (RepresentationTheory.MatrixBoundedVectors.integerVectors 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix).Finite ∧
    Set.ncard
      (RepresentationTheory.MatrixBoundedVectors.integerVectors 7 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix) = 63 := by
  obtain ⟨hfin, hcard⟩ := RepresentationTheory.MatrixBoundedVectors.integerVectors_finite_ncard_eq_boundedVectors_card E7_bound
  exact ⟨hfin, hcard ▸ E7_count⟩




private lemma E8_sos (a b c d e f g h : ℤ) :
    60 * (2*((a : ℤ)^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2) -
      2*(a*b+b*c+c*d+d*e+e*f+f*g+c*h)) =
    30*(2*a-b)^2 + 30*(2*g-f)^2 + 30*(2*h-c)^2 +
    10*(3*b-2*c)^2 + 10*(3*f-2*e)^2 +
    5*(4*e-3*d)^2 + 3*(5*d-4*c)^2 + 2*c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
private lemma E8_qf (x : Fin 8 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 5*x 6+x 2*x 7) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

set_option linter.style.maxHeartbeats false in

set_option maxHeartbeats 1600000 in

private lemma E8_bound (x : Fin 8 → ℤ)
    (hr : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 7 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 5*x 6+x 2*x 7) = 2 :=
    by have := hr.2; rw [E8_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6; set h := x 7
  have ha0 : 0 ≤ a := hp 0; have hb0 : 0 ≤ b := hp 1
  have hc0 : 0 ≤ c := hp 2; have hd0 : 0 ≤ d := hp 3
  have he0 : 0 ≤ e := hp 4; have hf0 : 0 ≤ f := hp 5
  have hg0 : 0 ≤ g := hp 6; have hh0 : 0 ≤ h := hp 7
  have hs : 30*(2*a-b)^2 + 30*(2*g-f)^2 +
      30*(2*h-c)^2 + 10*(3*b-2*c)^2 +
      10*(3*f-2*e)^2 + 5*(4*e-3*d)^2 +
      3*(5*d-4*c)^2 + 2*c^2 = 120 := by
    nlinarith [E8_sos a b c d e f g h]
  
  have hc7 : c ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg (5*d-4*c), sq_nonneg (c-8)]
  
  have hc6 : c ≤ 6 := by
    by_contra hc_ge7
    push Not at hc_ge7
    have hc_eq : c = 7 := le_antisymm hc7 hc_ge7
    
    have h3sq : 3 * (5 * d - 28) ^ 2 ≤ 22 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d)]
    
    have hd_le : d ≤ 8 := by nlinarith [sq_nonneg (5*d-28-9)]
    
    
    
    have hd_eq : d = 6 := by interval_cases d <;> omega
    
    have h5sq : 5 * (4 * e - 18) ^ 2 ≤ 10 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e)]
    
    have he_le : e ≤ 7 := by nlinarith [sq_nonneg (4*e-18-6)]
    
    have : False := by interval_cases e <;> omega
    exact this
  
  have hd6 : d ≤ 6 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg c, sq_nonneg (5*d-4*c-7)]
  have he5 : e ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (4*e-3*d-5)]
  have hb5 : b ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hf4 : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*f-2*e-4)]
  have ha3 : a ≤ 3 := by
    nlinarith [sq_nonneg (2*g-f), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have hg3 : g ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*g-f-3)]
  have hh4 : h ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*h-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega




private abbrev E8.U3 := Fin 7 × Fin 7 × Fin 7


private abbrev E8.U4 := Fin 7 × Fin 7 × Fin 7 × Fin 7


private def asm8 (c : Fin 7) (g1 : E8.U3) (g2 : E8.U4) : Fin 8 → Fin 7 :=
  ![g1.1, g1.2.1, c, g2.1, g2.2.1, g2.2.2.1, g2.2.2.2, g1.2.2]


private def dis8 (v : Fin 8 → Fin 7) : Fin 7 × E8.U3 × E8.U4 :=
  (v 2, (v 0, v 1, v 7), (v 3, v 4, v 5, v 6))

set_option maxRecDepth 8000 in
private def E8equiv : (Fin 8 → Fin 7) ≃ Fin 7 × E8.U3 × E8.U4 where
  toFun := dis8
  invFun w := asm8 w.1 w.2.1 w.2.2
  left_inv v := by funext i; fin_cases i <;> simp [asm8, dis8]
  right_inv w := by
    obtain ⟨c, ⟨a, b, d⟩, ⟨e, f, g, h⟩⟩ := w
    simp only [asm8, dis8, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue]


private def q1_8 (c : Fin 7) (g : E8.U3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(c:ℤ) - 2*(c:ℤ)*(g.2.2:ℤ)


private def q2_8 (c : Fin 7) (g : E8.U4) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2.1:ℤ)^2 + 2*(g.2.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(g.2.2.1:ℤ) - 2*(g.2.2.1:ℤ)*(g.2.2.2:ℤ)
    - 2*(c:ℤ)*(g.1:ℤ)

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2000000 in

private lemma E8_form (c : Fin 7) (g1 : E8.U3) (g2 : E8.U4) :
    dotProduct (fun i => ((asm8 c g1 g2) i : ℤ))
      ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix).mulVec (fun i => ((asm8 c g1 g2) i : ℤ)))
    = 2*(c:ℤ)^2 + q1_8 c g1 + q2_8 c g2 := by
  rw [show (2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix) = !![
    (2:ℤ),-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1; 0,0,-1,2,-1,0,0,0;
    0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0; 0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2]
    from by decide]
  simp only [asm8, q1_8, q2_8, dotProduct, mulVec, Fin.sum_univ_eight, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring


private def qf8 (x : Fin 8 → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix).mulVec x)

set_option maxRecDepth 10000 in

private lemma E8_root_filter : RepresentationTheory.MatrixBoundedVectors.boundedVectors 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix 7 =
    (univ.filter (fun v : Fin 8 → Fin 7 => qf8 (fun i => ((v i : ℤ))) = 2)) := by
  rw [RepresentationTheory.MatrixBoundedVectors.boundedVectors]
  apply Finset.filter_congr
  intro v _
  simp only [qf8, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro h0; rw [h0] at h; simp [dotProduct] at h


private def vals1_8 (c : Fin 7) : List ℤ :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    (List.finRange 7).map fun d => q1_8 c (a, b, d)


private def vals2_8 (c : Fin 7) : List ℤ :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    (List.finRange 7).flatMap fun d => (List.finRange 7).map fun e => q2_8 c (a, b, d, e)

set_option maxRecDepth 10000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 4000000 in

private lemma E8_count_eq :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix 7).card =
    ∑ c : Fin 7, (univ.filter (fun p : E8.U3 × E8.U4 =>
      q1_8 c p.1 + q2_8 c p.2 = 2 - 2*(c:ℤ)^2)).card := by
  rw [E8_root_filter]
  rw [show (univ.filter (fun v : Fin 8 → Fin 7 => qf8 (fun i => ((v i : ℤ))) = 2)).card
      = (univ.filter (fun w : Fin 7 × E8.U3 × E8.U4 =>
          2*(w.1:ℤ)^2 + q1_8 w.1 w.2.1 + q2_8 w.1 w.2.2 = 2)).card from ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    simp only [eq_iff_iff]
    constructor <;> intro h <;> linarith
  · apply Finset.card_bij' (fun v _ => E8equiv v) (fun w _ => E8equiv.symm w)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have hform : qf8 (fun i => ((a i : ℤ))) = 2*((E8equiv a).1:ℤ)^2
          + q1_8 (E8equiv a).1 (E8equiv a).2.1 + q2_8 (E8equiv a).1 (E8equiv a).2.2 := by
        conv_lhs => rw [show a = E8equiv.symm (E8equiv a) from (E8equiv.symm_apply_apply a).symm]
        rw [qf8]; exact E8_form _ _ _
      rw [hform] at ha; exact ha
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      have hform : qf8 (fun i => (((E8equiv.symm b) i : ℤ))) = 2*(b.1:ℤ)^2
          + q1_8 b.1 b.2.1 + q2_8 b.1 b.2.2 := by
        rw [qf8]; obtain ⟨c, g1, g2⟩ := b; exact E8_form _ _ _
      rw [hform]; exact hb
    · intro a _; exact E8equiv.symm_apply_apply a
    · intro b _; exact E8equiv.apply_symm_apply b

set_option maxRecDepth 100000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 30000000 in
private lemma E8_count :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix 7).card = 120 := by
  rw [E8_count_eq]
  have hb : ∀ c : Fin 7, (univ.filter (fun p : E8.U3 × E8.U4 =>
        q1_8 c p.1 + q2_8 c p.2 = 2 - 2*(c:ℤ)^2)).card
      = pairCount (vals1_8 c) (histL (vals2_8 c)) (2 - 2*(c:ℤ)^2) :=
    fun c => pair_count_bridge (q1_8 c) (q2_8 c) _ _ _ rfl rfl
  rw [Finset.sum_congr rfl (fun c _ => hb c)]
  decide


/-- Supplying eight and the `adj` field produces a finite set whose cardinality is one hundred twenty. -/
@[source_ref "Chapter6/Example6.4.9" (role := primary)]
theorem set_from_adj_at_eight_finite_and_ncard_eq :
    (RepresentationTheory.MatrixBoundedVectors.integerVectors 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix).Finite ∧
    Set.ncard
      (RepresentationTheory.MatrixBoundedVectors.integerVectors 8 RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix) =
      120 := by
  obtain ⟨hfin, hcard⟩ := RepresentationTheory.MatrixBoundedVectors.integerVectors_finite_ncard_eq_boundedVectors_card E8_bound
  exact ⟨hfin, hcard ▸ E8_count⟩

end ETypeRootCounts

end RepresentationTheory.AdjInputSetCardinalities
