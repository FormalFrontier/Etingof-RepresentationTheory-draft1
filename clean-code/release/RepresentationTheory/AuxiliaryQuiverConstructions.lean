/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.QuiverVertexPredicates
import RepresentationTheory.QuiverVertexReversal
import RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.Quiver.AuxiliaryAtVertex
import RepresentationTheory.Quiver.AuxiliaryNatInt
import RepresentationTheory.Alignment.Attribute


























open scoped Matrix

namespace RepresentationTheory.AuxiliaryQuiverConstructions

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}





private lemma adj_eq_one_of_arrow
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    {a b : Fin n} (e : @Quiver.Hom (Fin n) Q a b) :
    adj a b = 1 := by
  rcases hDynkin.2.2.1 a b with h0 | h1
  · exfalso; exact (hOrient.1 a b (by omega)).false e
  · exact h1









/-- For a nonempty finite vertex type under the displayed hypotheses, some vertex has the auxiliary property. -/
theorem auxiliary_exists_vertex_property
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (hn : 0 < n)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj) :
    ∃ i : Fin n, RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) i := by

  by_contra h
  push Not at h

  have hout : ∀ v : Fin n, ∃ w : Fin n, Nonempty (v ⟶ w) := by
    intro v
    have hv := h v
    unfold RepresentationTheory.QuiverVertexPredicates.vertexProperty at hv
    push Not at hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw⟩

  choose next hnext using hout







  have hadj_out : ∀ v, adj v (next v) = 1 := by
    intro v; exact adj_eq_one_of_arrow hDynkin hOrient (hnext v).some

  have hadj_in : ∀ v, adj (next v) v = 1 := by
    intro v
    have h1 := hadj_out v
    have hsymm := hDynkin.1
    have : adj (next v) v = adj v (next v) := by
      have := congr_fun (congr_fun hsymm v) (next v)
      simp [Matrix.transpose_apply] at this; exact this
    rw [this]; exact h1

  have hno_overlap : ∀ v w : Fin n, (v, next v) ≠ (next w, w) := by
    intro v w heq
    have h1 : v = next w := congr_arg Prod.fst heq
    have h2 : next v = w := congr_arg Prod.snd heq

    have harr1 := hnext v
    have harr2 := hnext w

    apply hOrient.2.2 v w
    ·
      rw [show w = next v from h2.symm]; exact harr1
    ·
      rw [show v = next w from h1]; exact harr2


  have hadj_nonneg : ∀ i j, (0 : ℤ) ≤ adj i j := by
    intro i j; rcases hDynkin.2.2.1 i j with h | h <;> omega

  set total := ∑ i : Fin n, ∑ j : Fin n, adj i j

  have hone_ne : (fun (_ : Fin n) => (1 : ℤ)) ≠ 0 := by
    intro heq; have := congr_fun heq ⟨0, hn⟩; simp at this
  have hpos := hDynkin.2.2.2.2 (fun _ => (1 : ℤ)) hone_ne

  have hexpand : dotProduct (fun _ => (1 : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) =
      2 * (↑n : ℤ) - total := by

    have h_row : ∀ i : Fin n,
        ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j = 2 - ∑ j, adj i j := by
      intro i
      have h2I : ∑ j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = 2 := by
        simp [Matrix.smul_apply, Matrix.one_apply, Finset.mem_univ]
      simp only [Matrix.sub_apply]
      rw [Finset.sum_sub_distrib]
      linarith

    have h_dot : dotProduct (fun _ => (1 : ℤ))
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) =
        ∑ i, ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j := by
      simp only [dotProduct, Matrix.mulVec, one_mul, mul_one]
    rw [h_dot]

    simp_rw [h_row]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, total]
    ring
  have hub : total < 2 * (↑n : ℤ) := by linarith


  have hfwd_inj : Function.Injective (fun v : Fin n => (v, next v)) :=
    fun a b h => (Prod.mk.inj h).1
  have hbwd_inj : Function.Injective (fun v : Fin n => (next v, v)) :=
    fun a b h => (Prod.mk.inj h).2

  have hdisjoint : Disjoint
      (Finset.univ.image (fun v : Fin n => (v, next v)))
      (Finset.univ.image (fun v : Fin n => (next v, v))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨v, _, hv⟩ := hp1
    obtain ⟨w, _, hw⟩ := hp2
    exact absurd (hv ▸ hw ▸ rfl : (v, next v) = (next w, w)) (hno_overlap v w)

  have h_fwd_sum : ∑ p ∈ Finset.univ.image (fun v : Fin n => (v, next v)),
      adj p.1 p.2 = ↑n := by
    rw [Finset.sum_image (fun a _ b _ h => hfwd_inj h)]
    simp [hadj_out, Finset.sum_const, Finset.card_univ, mul_one]

  have h_bwd_sum : ∑ p ∈ Finset.univ.image (fun v : Fin n => (next v, v)),
      adj p.1 p.2 = ↑n := by
    rw [Finset.sum_image (fun a _ b _ h => hbwd_inj h)]
    simp [hadj_in, Finset.sum_const, Finset.card_univ, mul_one]

  have h_union_sum : ∑ p ∈ (Finset.univ.image (fun v : Fin n => (v, next v)) ∪
      Finset.univ.image (fun v : Fin n => (next v, v))),
      adj p.1 p.2 = 2 * ↑n := by
    rw [Finset.sum_union hdisjoint, h_fwd_sum, h_bwd_sum]; ring

  have h_sub : Finset.univ.image (fun v : Fin n => (v, next v)) ∪
      Finset.univ.image (fun v : Fin n => (next v, v)) ⊆
      (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.subset_univ _
  have h_pair_sum : (∑ p : Fin n × Fin n, adj p.fst p.snd) = total := by
    show (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), adj p.fst p.snd) = total
    rw [Finset.univ_product_univ.symm, Finset.sum_product']
  have hlb : 2 * (↑n : ℤ) ≤ total := by
    have := Finset.sum_le_sum_of_subset_of_nonneg h_sub
      (fun p _ _ => hadj_nonneg p.1 p.2)
    linarith [h_union_sum, h_pair_sum]

  linarith


/-- One displayed auxiliary property of a finite vertex implies the other. -/
theorem auxiliary_vertex_property_imp_other
    {Q : Quiver (Fin n)} (p : Fin n) (hp : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q p) :
    @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q p) p := by
  intro j

  constructor
  intro (e : RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin n) p j p)
  by_cases hj : j = p
  ·
    have heq : RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin n) p j p = (@Quiver.Hom (Fin n) Q j p) :=
      RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq hj rfl
    have e' : @Quiver.Hom (Fin n) Q j p := cast heq e
    exact (hp p).false (hj ▸ e')
  ·
    have heq : RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin n) p j p = (@Quiver.Hom (Fin n) Q p j) :=
      RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hj rfl
    exact (hp j).false (cast heq e)






/-- An auxiliary operation sending a quiver and a list of vertices to another quiver. -/
noncomputable def auxiliaryListMap
    {V : Type*} [DecidableEq V] : (Q : Quiver V) → List V → Quiver V
  | Q, [] => Q
  | Q, v :: vs => auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex V _ Q v) vs




/-- The auxiliary quiver operation preserves the displayed relation with the integer matrix. -/
theorem auxiliaryListMap_property
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (Q : Quiver (Fin n)) (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (vs : List (Fin n)) :
    @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n (auxiliaryListMap Q vs) adj := by
  induction vs generalizing Q with
  | nil => exact hOrient
  | cons v vs ih =>
    exact ih _ (RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation hDynkin.1 hDynkin.2.1 hOrient v)






/-- An auxiliary predicate relating a finite quiver and a list of its vertices. -/
structure AuxiliaryListProperty (Q : Quiver (Fin n))
    (ordering : List (Fin n)) : Prop where

  /-- A list satisfying the auxiliary predicate is a permutation of the full finite range. -/
  perm_finRange : ordering.Perm (List.finRange n)

  /-- Every vertex at a valid position in a list satisfying the auxiliary predicate has the displayed vertex property. -/
  get_property : ∀ k (hk : k < ordering.length),
    @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
      (auxiliaryListMap Q (ordering.take k))
      (ordering.get ⟨k, hk⟩)


/-- Applying the auxiliary quiver operation to an appended list is the same as applying it successively to the two lists. -/
theorem auxiliaryListMap_append
    {V : Type*} [DecidableEq V] (Q : Quiver V) (xs ys : List V) :
    auxiliaryListMap Q (xs ++ ys) =
    auxiliaryListMap (auxiliaryListMap Q xs) ys := by
  induction xs generalizing Q with
  | nil => rfl
  | cons x xs ih => exact ih (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex V _ Q x)

private alias iteratedReversed_append := auxiliaryListMap_append


private lemma iteratedReversed_hom_not_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n))
    {a b : Fin n} (ha : a ∉ vs) (hb : b ∉ vs) :
    @Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a b =
    @Quiver.Hom (Fin n) Q a b := by
  induction vs generalizing Q with
  | nil => rfl
  | cons v vs ih =>
    have hav : a ≠ v := fun h => ha (List.mem_cons.mpr (Or.inl h))
    have hbv : b ≠ v := fun h => hb (List.mem_cons.mpr (Or.inl h))
    have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
    have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
    change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) vs) a b =
      @Quiver.Hom _ Q a b
    rw [ih _ ha' hb']
    exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hav hbv








private theorem exists_local_sink_of_dynkin
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ w ∈ S, @IsEmpty (@Quiver.Hom _ Q v w) := by
  by_contra hall
  push Not at hall

  have hout : ∀ v ∈ S, ∃ w ∈ S, Nonempty (@Quiver.Hom _ Q v w) := by
    intro v hv; obtain ⟨w, hw, hne⟩ := hall v hv
    exact ⟨w, hw, hne⟩

  choose next hnext_mem hnext_arr using hout
  set next' : Fin n → Fin n := fun v => if hv : v ∈ S then next v hv else v
  have hnext'_eq : ∀ v (hv : v ∈ S), next' v = next v hv :=
    fun v hv => dif_pos hv
  have hadj_out : ∀ v ∈ S, adj v (next' v) = 1 := by
    intro v hv; rw [hnext'_eq v hv]
    exact adj_eq_one_of_arrow hDynkin hOrient (hnext_arr v hv).some
  have hadj_in : ∀ v ∈ S, adj (next' v) v = 1 := by
    intro v hv; rw [hnext'_eq v hv]
    have hsymm := hDynkin.1
    have : adj (next v hv) v = adj v (next v hv) := by
      have := congr_fun (congr_fun hsymm v) (next v hv)
      simp [Matrix.transpose_apply] at this; exact this
    rw [this]; exact adj_eq_one_of_arrow hDynkin hOrient (hnext_arr v hv).some
  have hnext'_mem : ∀ v ∈ S, next' v ∈ S := by
    intro v hv; rw [hnext'_eq v hv]; exact hnext_mem v hv

  have hno_overlap : ∀ v ∈ S, ∀ w ∈ S, (v, next' v) ≠ (next' w, w) := by
    intro v hv w hw heq
    rw [hnext'_eq v hv, hnext'_eq w hw] at heq
    have h1 : v = next w hw := congr_arg Prod.fst heq
    have h2 : next v hv = w := congr_arg Prod.snd heq
    apply hOrient.2.2 v w
    · rw [show w = next v hv from h2.symm]; exact hnext_arr v hv
    · rw [show v = next w hw from h1]; exact hnext_arr w hw

  have hadj_nonneg : ∀ i j, (0 : ℤ) ≤ adj i j := by
    intro i j; rcases hDynkin.2.2.1 i j with h | h <;> omega

  set total_S := ∑ i ∈ S, ∑ j ∈ S, adj i j with htotal_S_def

  have h_fwd_sum : ∑ p ∈ S.image (fun v => (v, next' v)),
      adj p.1 p.2 = ↑S.card := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    rw [show ∑ x ∈ S, adj x (next' x) = ∑ _ ∈ S, (1 : ℤ) from
      Finset.sum_congr rfl (fun x hx => hadj_out x hx)]
    simp

  have h_bwd_sum : ∑ p ∈ S.image (fun v => (next' v, v)),
      adj p.1 p.2 = ↑S.card := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).2)]
    rw [show ∑ x ∈ S, adj (next' x) x = ∑ _ ∈ S, (1 : ℤ) from
      Finset.sum_congr rfl (fun x hx => hadj_in x hx)]
    simp
  have hdisjoint : Disjoint
      (S.image (fun v => (v, next' v)))
      (S.image (fun v => (next' v, v))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨v, hv, hvp⟩ := hp1
    obtain ⟨w, hw, hwp⟩ := hp2
    exact absurd (hvp ▸ hwp ▸ rfl : (v, next' v) = (next' w, w)) (hno_overlap v hv w hw)
  have h_union_sum : ∑ p ∈ (S.image (fun v => (v, next' v)) ∪
      S.image (fun v => (next' v, v))),
      adj p.1 p.2 = 2 * ↑S.card := by
    rw [Finset.sum_union hdisjoint, h_fwd_sum, h_bwd_sum]; ring

  have h_sub : S.image (fun v => (v, next' v)) ∪
      S.image (fun v => (next' v, v)) ⊆ S ×ˢ S := by
    apply Finset.union_subset <;> intro p hp <;> rw [Finset.mem_image] at hp <;>
      obtain ⟨v, hv, rfl⟩ := hp <;> simp [hv, hnext'_mem v hv]
  have hlb : 2 * (↑S.card : ℤ) ≤ total_S := by
    have h_prod_sum : ∑ p ∈ S ×ˢ S, adj p.1 p.2 = total_S := by
      rw [htotal_S_def, Finset.sum_product']
    have := Finset.sum_le_sum_of_subset_of_nonneg h_sub
      (fun p _ _ => hadj_nonneg p.1 p.2)
    linarith [h_union_sum, h_prod_sum]

  set d : Fin n → ℤ := fun v => if v ∈ S then 1 else 0 with hd_def
  have hd_ne : d ≠ 0 := by
    intro heq; obtain ⟨v, hv⟩ := hS
    have := congr_fun heq v; simp [hd_def, hv] at this
  have hpos := hDynkin.2.2.2.2 d hd_ne

  have hexpand : dotProduct d ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d) =
      2 * ↑S.card - total_S := by

    have h_sub : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d =
        2 • d - adj.mulVec d := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h_sub, dotProduct_sub, dotProduct_smul, nsmul_eq_mul]; push_cast

    have hfilter_S : (Finset.univ : Finset (Fin n)).filter (· ∈ S) = S := by ext; simp

    have hdd : dotProduct d d = ↑S.card := by
      simp only [dotProduct, hd_def]
      rw [show ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) * (if i ∈ S then 1 else 0) =
        ∑ i, if i ∈ S then 1 else 0 from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)]
      simp only [← Finset.sum_filter, hfilter_S, Finset.sum_const, nsmul_eq_mul, mul_one]

    have hdad : dotProduct d (adj.mulVec d) = total_S := by
      simp only [dotProduct, Matrix.mulVec, hd_def]

      have h_inner : ∀ i : Fin n,
          ∑ j, adj i j * (if j ∈ S then (1 : ℤ) else 0) = ∑ j ∈ S, adj i j := by
        intro i
        rw [show ∑ j, adj i j * (if j ∈ S then (1 : ℤ) else 0) =
          ∑ j, if j ∈ S then adj i j else 0 from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)]
        simp only [← Finset.sum_filter, hfilter_S]
      simp_rw [h_inner]

      rw [show ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) * ∑ j ∈ S, adj i j =
        ∑ i, if i ∈ S then ∑ j ∈ S, adj i j else 0 from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)]
      simp only [← Finset.sum_filter, hfilter_S]; rfl
    linarith
  have hub : total_S < 2 * (↑S.card : ℤ) := by linarith

  linarith






private lemma iteratedReversed_hom_to_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a : Fin n} (ha : a ∉ vs) {b : Fin n} (hb : b ∈ vs) :
    @Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a b =
    @Quiver.Hom (Fin n) Q b a := by
  induction vs generalizing Q with
  | nil => simp at hb
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp hb with rfl | hb_vs
    ·
      have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ b := fun h => ha (List.mem_cons.mpr (Or.inl h))
      change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q b) vs) a b = _
      rw [iteratedReversed_hom_not_mem _ vs ha' hvs.1]
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hav rfl
    ·
      have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ v := fun h => ha (List.mem_cons.mpr (Or.inl h))
      have hbv : b ≠ v := by intro h; subst h; exact hvs.1 hb_vs
      change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) vs) a b = _
      rw [ih (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) hvs.2 ha' hb_vs]
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hbv hav




private lemma iteratedReversed_hom_from_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a : Fin n} (ha : a ∈ vs) {b : Fin n} (hb : b ∉ vs) :
    @Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a b =
    @Quiver.Hom (Fin n) Q b a := by
  induction vs generalizing Q with
  | nil => simp at ha
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp ha with rfl | ha_vs
    ·
      have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
      have hbv : b ≠ a := fun h => hb (List.mem_cons.mpr (Or.inl h))
      change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q a) vs) a b = _
      rw [iteratedReversed_hom_not_mem _ vs hvs.1 hb']
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hbv
    ·
      have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ v := by intro h; subst h; exact hvs.1 ha_vs
      have hbv : b ≠ v := fun h => hb (List.mem_cons.mpr (Or.inl h))
      change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) vs) a b = _
      rw [ih (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) hvs.2 ha_vs hb']
      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hbv hav




private lemma iteratedReversed_hom_both_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a b : Fin n} (ha : a ∈ vs) (hb : b ∈ vs) (hab : a ≠ b) :
    @Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a b =
    @Quiver.Hom (Fin n) Q a b := by
  induction vs generalizing Q with
  | nil => simp at ha
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp ha with rfl | ha_vs
    ·
      have ha_not : a ∉ vs := hvs.1
      have hb_vs : b ∈ vs := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd rfl hab
        · exact h
      change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q a) vs) a b = _
      rw [iteratedReversed_hom_to_mem _ vs hvs.2 ha_not hb_vs]


      exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq (Ne.symm hab) rfl
    · rcases List.mem_cons.mp hb with rfl | hb_vs
      ·
        have hb_not : b ∉ vs := hvs.1
        change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q b) vs) a b = _
        rw [iteratedReversed_hom_from_mem _ vs hvs.2 ha_vs hb_not]


        exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hab
      ·
        have hav : a ≠ v := by intro h; subst h; exact hvs.1 ha_vs
        have hbv : b ≠ v := by intro h; subst h; exact hvs.1 hb_vs
        change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) vs) a b = _
        rw [ih (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) hvs.2 ha_vs hb_vs]
        exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hav hbv



private lemma iteratedReversed_self_hom
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    (a : Fin n) :
    @Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a a =
    @Quiver.Hom (Fin n) Q a a := by
  induction vs generalizing Q with
  | nil => rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    change @Quiver.Hom _ (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) vs) a a = _
    rw [ih (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex _ _ Q v) hvs.2]
    by_cases hav : a = v
    · exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq hav hav
    · exact RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hav hav




/-- The auxiliary quiver operation fixes a quiver when the vertex list permutes the full finite range. -/
theorem auxiliaryListMap_eq_self_of_perm
    (Q : Quiver (Fin n)) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n)) :
    auxiliaryListMap Q σ = Q := by
  have hnodup : σ.Nodup := hσ.nodup_iff.mpr (List.nodup_finRange n)
  have hmem : ∀ v : Fin n, v ∈ σ := fun v => hσ.mem_iff.mpr (List.mem_finRange v)
  ext a b
  by_cases hab : a = b
  · subst hab; exact iteratedReversed_self_hom Q σ hnodup a
  · exact iteratedReversed_hom_both_mem Q σ hnodup (hmem a) (hmem b) hab






/-- There exists a duplicate-free ordering of all vertices with no quiver morphism from an earlier vertex to a later one. -/
theorem auxiliary_exists_ordering_no_hom_of_le
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj) :
    ∃ (ordering : List (Fin n)),
      ordering.Perm (List.finRange n) ∧ ordering.Nodup ∧
      ∀ k m (hk : k < ordering.length) (hm : m < ordering.length), k ≤ m →
        @IsEmpty (@Quiver.Hom _ Q (ordering.get ⟨k, hk⟩) (ordering.get ⟨m, hm⟩)) := by



  suffices h : ∀ (remaining : Finset (Fin n)) (acc : List (Fin n)),
      acc.Nodup → acc.toFinset = Finset.univ \ remaining →
      (∀ k m (hk : k < acc.length) (hm : m < acc.length), k ≤ m →
        @IsEmpty (@Quiver.Hom _ Q (acc.get ⟨k, hk⟩) (acc.get ⟨m, hm⟩))) →
      (∀ k (hk : k < acc.length), ∀ w ∈ remaining,
        @IsEmpty (@Quiver.Hom _ Q (acc.get ⟨k, hk⟩) w)) →
      ∃ (ordering : List (Fin n)),
        ordering.Perm (List.finRange n) ∧ ordering.Nodup ∧
        ∀ k m (hk : k < ordering.length) (hm : m < ordering.length), k ≤ m →
          @IsEmpty (@Quiver.Hom _ Q (ordering.get ⟨k, hk⟩) (ordering.get ⟨m, hm⟩)) by
    exact h Finset.univ [] List.nodup_nil (by simp) (by simp) (by simp)
  intro remaining
  induction remaining using Finset.strongInduction with
  | H remaining ih =>
    intro acc hnodup hacc_set htopo hedge
    by_cases hrem : remaining.Nonempty
    · obtain ⟨v, hv_mem, hv_sink⟩ := exists_local_sink_of_dynkin hDynkin hOrient remaining hrem
      have hv_not_acc : v ∉ acc := by
        intro hv; rw [← List.mem_toFinset] at hv; rw [hacc_set] at hv
        simp at hv; exact hv hv_mem

      have get_app_l {l₁ l₂ : List (Fin n)} {i : ℕ} (h₁ : i < l₁.length)
          {h₂ : i < (l₁ ++ l₂).length} :
          (l₁ ++ l₂).get ⟨i, h₂⟩ = l₁.get ⟨i, h₁⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left h₁
      have get_app_r {l₁ l₂ : List (Fin n)} {i : ℕ} (h₁ : l₁.length ≤ i)
          {h₂ : i < (l₁ ++ l₂).length} :
          (l₁ ++ l₂).get ⟨i, h₂⟩ = l₂.get ⟨i - l₁.length, by rw [List.length_append] at h₂; omega⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_right h₁
      apply ih (remaining.erase v) (Finset.erase_ssubset hv_mem) (acc ++ [v])
      · exact hnodup.append (List.nodup_singleton v)
          (by simp only [List.disjoint_singleton]; exact hv_not_acc)
      ·
        rw [List.toFinset_append, hacc_set]
        ext w
        simp only [Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert,
          Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
        tauto
      ·
        intro k m hk hm hkm
        rw [List.length_append, List.length_singleton] at hk hm
        by_cases hk_old : k < acc.length
        · by_cases hm_old : m < acc.length
          ·
            rw [get_app_l hk_old, get_app_l hm_old]
            exact htopo k m hk_old hm_old hkm
          ·
            have hm_eq : m = acc.length := by omega
            subst hm_eq
            rw [get_app_l hk_old, get_app_r (by omega)]
            simp; exact hedge k hk_old v hv_mem
        ·
          have hk_eq : k = acc.length := by omega
          subst hk_eq
          have hm_eq : m = acc.length := by omega
          subst hm_eq
          rw [get_app_r (by omega)]
          simp; exact hv_sink v hv_mem
      ·
        intro k hk w hw
        rw [List.length_append, List.length_singleton] at hk
        have hw_rem : w ∈ remaining := Finset.mem_of_mem_erase hw
        by_cases hk_old : k < acc.length
        · rw [get_app_l hk_old]; exact hedge k hk_old w hw_rem
        · have hk_eq : k = acc.length := by omega
          subst hk_eq
          rw [get_app_r (by omega)]; simp
          exact hv_sink w hw_rem
    ·
      rw [Finset.not_nonempty_iff_eq_empty] at hrem
      refine ⟨acc, ?_, hnodup, htopo⟩
      rw [List.perm_iff_count]; intro v
      have hv_acc : v ∈ acc := by rw [← List.mem_toFinset, hacc_set]; simp [hrem]
      rw [List.count_eq_one_of_mem hnodup hv_acc,
          List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange v)]










/-- Under the displayed matrix and quiver hypotheses, there exists a vertex list satisfying the auxiliary predicate. -/
@[source_ref "Chapter6/Section6.8_heading" (role := primary)]
theorem auxiliary_exists_list_property
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj) :
    ∃ ordering : List (Fin n), AuxiliaryListProperty Q ordering := by
  obtain ⟨ordering, hperm, hnodup, htopo⟩ := auxiliary_exists_ordering_no_hom_of_le hDynkin hOrient

  have get_take_eq {j k : ℕ} (hj : j < (ordering.take k).length) :
      (ordering.take k).get ⟨j, hj⟩ = ordering.get ⟨j, by rw [List.length_take] at hj; omega⟩ := by
    simp only [List.get_eq_getElem]; exact List.getElem_take

  have get_not_mem_take : ∀ k (hk : k < ordering.length),
      ordering.get ⟨k, hk⟩ ∉ ordering.take k := by
    intro k hk hmem
    obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := List.mem_iff_get.mp hmem
    have hj_lt_k : j < k := by
      have : j < (ordering.take k).length := hj_lt
      rw [List.length_take] at this; exact lt_of_lt_of_le this (min_le_left k ordering.length)
    have hj_lt' : j < ordering.length := by omega
    have : ordering.get ⟨j, hj_lt'⟩ = ordering.get ⟨k, hk⟩ := by
      rw [← get_take_eq hj_lt, hj_eq]
    have hinj := hnodup.injective_get this
    simp only [Fin.mk.injEq] at hinj
    omega

  have get_mem_take : ∀ m k (hm : m < ordering.length) (hmk : m < k),
      ordering.get ⟨m, hm⟩ ∈ ordering.take k := by
    intro m k hm hmk
    rw [List.mem_iff_get]
    have hm_take : m < (ordering.take k).length := by rw [List.length_take]; omega
    exact ⟨⟨m, hm_take⟩, get_take_eq hm_take⟩
  refine ⟨ordering, hperm, fun k hk => ?_⟩

  intro w

  have hw_mem : w ∈ ordering := hperm.mem_iff.mpr (List.mem_finRange w)
  obtain ⟨⟨m, hm⟩, hm_eq⟩ := List.mem_iff_get.mp hw_mem

  constructor; intro e; subst hm_eq
  by_cases hkm : k ≤ m
  ·
    have hk_not := get_not_mem_take k hk
    have hm_not : ordering.get ⟨m, hm⟩ ∉ ordering.take k := by
      intro hmem
      obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := List.mem_iff_get.mp hmem
      have hj_lt_k : j < k := by
        have : j < (ordering.take k).length := hj_lt
        rw [List.length_take] at this; exact lt_of_lt_of_le this (min_le_left k ordering.length)
      have hj_lt' : j < ordering.length := by omega
      have : ordering.get ⟨j, hj_lt'⟩ = ordering.get ⟨m, hm⟩ := by
        rw [← get_take_eq hj_lt, hj_eq]
      have hinj := hnodup.injective_get this
      simp only [Fin.mk.injEq] at hinj
      omega
    have h_eq := iteratedReversed_hom_not_mem Q (ordering.take k) hk_not hm_not
    exact (htopo k m hk hm hkm).false (h_eq ▸ e)
  ·
    push Not at hkm
    have hm_in := get_mem_take m k hm hkm
    have hk_not := get_not_mem_take k hk
    have htake_nodup : (ordering.take k).Nodup := hnodup.take
    have h_eq := iteratedReversed_hom_to_mem Q (ordering.take k) htake_nodup hk_not hm_in

    have : Nonempty (@Quiver.Hom _ Q (ordering.get ⟨m, hm⟩) (ordering.get ⟨k, hk⟩)) :=
      ⟨h_eq ▸ e⟩
    exact (htopo m k hm hk (by omega)).false this.some










private lemma iteratedSimpleReflection_coord_not_mem
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (v : Fin n → ℤ)
    (j : Fin n) (hj : j ∉ vs) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs v j = v j := by
  induction vs generalizing v with
  | nil => rfl
  | cons k rest ih =>
    rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons]
    have hk : j ≠ k := fun h => hj (by simp [h])
    have hrest : j ∉ rest := fun h => hj (List.mem_cons.mpr (Or.inr h))
    rw [ih _ hrest]
    exact RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_apply_of_ne v k j hk


/-- The auxiliary vector map for an appended list is the composition of the maps for its two parts. -/
lemma auxiliaryVectorMap_append
    (A : Matrix (Fin n) (Fin n) ℤ) (xs ys : List (Fin n))
    (v : Fin n → ℤ) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (xs ++ ys) v =
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A ys (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A xs v) := by
  simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, List.foldl_append]



/-- The auxiliary vector map for repeated copies of a list equals the corresponding iterate. -/
lemma auxiliaryVectorMap_replicate
    (A : Matrix (Fin n) (Fin n) ℤ) (σ : List (Fin n)) (v : Fin n → ℤ) (M : ℕ) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A ((List.replicate M σ).flatten) v =
    (fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ w)^[M] v := by
  set c := fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ w
  induction M generalizing v with
  | zero =>
    simp only [List.replicate_zero, List.flatten_nil, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection,
      List.foldl_nil, Function.iterate_zero, id_eq]
  | succ M ih =>
    have hflat : (List.replicate (M + 1) σ).flatten = σ ++ (List.replicate M σ).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    simp only [hflat, auxiliaryVectorMap_append, ih,
      Function.iterate_succ, Function.comp_apply, c]


private lemma iteratedSimpleReflection_preserves_B
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (vs : List (Fin n))
    (v : Fin n → ℤ) :
    dotProduct (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vs v)
      ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec
        (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vs v)) =
    dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v) := by
  induction vs generalizing v with
  | nil => rfl
  | cons k rest ih =>
    rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons]
    rw [ih]
    exact RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.quadraticForm_coordinateReflection hDynkin v k









private lemma iteratedSimpleReflection_perm_fixed_zero
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (σ : List (Fin n)) (hσ : σ.Perm (List.finRange n))
    (v : Fin n → ℤ)
    (hfixed : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ v = v) :
    v = 0 := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  have hnodup : σ.Nodup := hσ.nodup_iff.mpr (List.nodup_finRange n)
  have hlen : σ.length = n := by
    have := hσ.length_eq; rwa [List.length_finRange] at this

  suffices hall : ∀ k, k ≤ n →
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (σ.take k) v = v by

    suffices hAv : A.mulVec v = 0 by
      by_contra hv
      have hpos := hDynkin.2.2.2.2 v hv
      rw [show A = (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) from rfl]
        at hAv
      rw [hAv, dotProduct_zero] at hpos
      exact lt_irrefl 0 hpos
    ext p

    have hp_mem : p ∈ σ := hσ.mem_iff.mpr (List.mem_finRange p)
    obtain ⟨⟨k, hk_lt⟩, hk_eq⟩ := List.mem_iff_get.mp hp_mem



    have hk_lt_n : k < n := by rw [← hlen]; exact hk_lt
    have h_take_k := hall k (by omega)
    have h_take_k1 := hall (k + 1) (by omega)
    have htake_split : σ.take (k + 1) = σ.take k ++ [σ[k]] :=
      (List.take_append_getElem hk_lt).symm
    rw [htake_split, auxiliaryVectorMap_append, h_take_k] at h_take_k1


    simp only [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, List.foldl] at h_take_k1

    have hp_eq : σ[k] = p := by
      change σ.get ⟨k, hk_lt⟩ = p; exact hk_eq
    have := congr_fun h_take_k1 p
    rw [← hp_eq] at this
    rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_apply_self
      (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1) v σ[k]] at this

    rw [hp_eq] at this
    simp only [Pi.zero_apply]
    linarith
  intro k hk
  induction k with
  | zero => simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection]
  | succ m ih =>
    have hm_le : m ≤ n := by omega
    have him := ih hm_le
    have hm_lt : m < σ.length := by rw [hlen]; omega
    have htake_split : σ.take (m + 1) =
        σ.take m ++ [σ[m]] :=
      (List.take_append_getElem hm_lt).symm
    rw [htake_split, auxiliaryVectorMap_append, him]
    set p : Fin n := σ[m]
    have hp_not_drop : p ∉ σ.drop (m + 1) := by
      intro hmem
      have hp_take : p ∈ σ.take (m + 1) := by
        rw [htake_split]; simp
      have hnd : (σ.take (m + 1) ++ σ.drop (m + 1)).Nodup := by
        rwa [List.take_append_drop]
      exact (List.nodup_append.mp hnd).2.2 p hp_take p hmem rfl

    have hsplit : σ = σ.take (m + 1) ++ σ.drop (m + 1) :=
      (List.take_append_drop (m + 1) σ).symm
    have hfull : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ v = v := hfixed
    rw [hsplit, auxiliaryVectorMap_append, htake_split,
      auxiliaryVectorMap_append, him] at hfull


    have hsingleton : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A [p] v = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A p v := by
      simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection]
    rw [hsingleton] at hfull

    have hcoord := congr_fun hfull p
    rw [iteratedSimpleReflection_coord_not_mem A (σ.drop (m + 1))
      (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A p v) p hp_not_drop] at hcoord

    rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_apply_self
      (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1) v p] at hcoord

    have hAv_zero : (A.mulVec v) p = 0 := by linarith

    change RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A [p] v = v
    simp only [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, List.foldl]
    change v - dotProduct v (A.mulVec (Pi.single p 1)) • Pi.single p 1 = v
    have hcoeff : dotProduct v (A.mulVec (Pi.single p 1)) =
        (A.mulVec v) p := by
      have hAsymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
        mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show A j p = A p j from
          congr_fun (congr_fun hAsymm p) j]; ring
    rw [hcoeff, hAv_zero, zero_smul, sub_zero]




private lemma simpleReflection_add
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (u v : Fin n → ℤ) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i (u + v) =
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i u + RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v := by
  unfold RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul,
    add_dotProduct]
  ring


private lemma simpleReflection_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i 0 = 0 := by
  ext j
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, Pi.zero_apply, dotProduct, Matrix.mulVec]
  simp


private lemma iteratedSimpleReflection_add
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (u v : Fin n → ℤ) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (u + v) =
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs u + RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs v := by
  induction vs generalizing u v with
  | nil => rfl
  | cons k rest ih =>
    rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons,
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons, simpleReflection_add, ih]


private lemma iteratedSimpleReflection_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs 0 = 0 := by
  induction vs with
  | nil => rfl
  | cons k rest ih => rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons, simpleReflection_zero, ih]


private lemma iteratedSimpleReflection_sum
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n))
    {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℤ)) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (∑ i ∈ s, f i) =
    ∑ i ∈ s, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [iteratedSimpleReflection_zero]
  | cons a s has ih =>
    rw [Finset.sum_cons, iteratedSimpleReflection_add, ih, Finset.sum_cons]







private theorem finite_B_level_set
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (K : ℤ) :
    Set.Finite {v : Fin n → ℤ |
      dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v) = K} := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def

  have hA_inj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hne
    have hpos := hDynkin.2.2.2.2 (x - y) (sub_ne_zero.mpr hne)
    have hzero : A.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have : dotProduct (x - y) (A.mulVec (x - y)) = 0 := by
      rw [hzero]; simp [dotProduct]
    rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
    linarith

  have hB_nonneg : ∀ w : Fin n → ℤ, 0 ≤ dotProduct w (A.mulVec w) := by
    intro w; by_cases hw : w = 0
    · subst hw; simp [dotProduct, Matrix.mulVec]
    · have := hDynkin.2.2.2.2 w hw
      rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at this
      linarith
  have hA_symm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1

  have hBei : ∀ i : Fin n,
      dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2 := by
    intro i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [hA_def, RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply]
    have := hDynkin.2.1 i; simp_all

  have hB_coord : ∀ (v : Fin n → ℤ) (i : Fin n),
      dotProduct v (A.mulVec (Pi.single i 1)) = A.mulVec v i := by
    intro v i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show A j i = A i j from congr_fun (congr_fun hA_symm i) j]; ring
  have hB_coord' : ∀ (v : Fin n → ℤ) (i : Fin n),
      dotProduct (Pi.single i 1) (A.mulVec v) = A.mulVec v i := by
    intro v i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  have hAv_bound : ∀ v : Fin n → ℤ, dotProduct v (A.mulVec v) = K →
      ∀ i, -(K + 2) ≤ A.mulVec v i ∧ A.mulVec v i ≤ K + 2 := by
    intro v hv i
    have hplus := hB_nonneg (v + Pi.single i 1)
    have hminus := hB_nonneg (v - Pi.single i 1)
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add] at hplus
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at hminus
    rw [hv, hBei, hB_coord v i, hB_coord' v i] at hplus hminus
    constructor <;> omega

  apply Set.Finite.subset
    ((Set.finite_Icc (fun _ : Fin n => -(K + 2)) (fun _ => K + 2)).preimage
      (Set.InjOn.mono (Set.subset_univ _) (Set.injOn_of_injective hA_inj)))
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def]
  exact ⟨fun i => (hAv_bound v hv i).1, fun i => (hAv_bound v hv i).2⟩











private lemma iteratedSimpleReflection_iter_preserves_B
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (σ : List (Fin n))
    (v : Fin n → ℤ) (N : ℕ) :
    dotProduct ((fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ w)^[N] v)
      ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec
        ((fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ w)^[N] v)) =
    dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [iteratedSimpleReflection_preserves_B hDynkin, ih]


private theorem iteratedSimpleReflection_orbit_finite
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (σ : List (Fin n))
    (v : Fin n → ℤ) :
    Set.Finite (Set.range (fun N =>
      (fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ w)^[N] v)) := by
  apply Set.Finite.subset (finite_B_level_set hDynkin
    (dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v)))
  intro w ⟨N, hN⟩
  simp only [Set.mem_setOf_eq]
  rw [← hN, iteratedSimpleReflection_iter_preserves_B hDynkin]


private lemma iteratedSimpleReflection_neg
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (v : Fin n → ℤ) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (-v) =
    -RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs v := by
  have h : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs v +
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (-v) = 0 := by
    rw [← iteratedSimpleReflection_add, add_neg_cancel, iteratedSimpleReflection_zero]
  exact eq_neg_of_add_eq_zero_right h


private lemma iteratedSimpleReflection_sub
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (u v : Fin n → ℤ) :
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs (u - v) =
    RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs u - RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vs v := by
  rw [sub_eq_add_neg, iteratedSimpleReflection_add, iteratedSimpleReflection_neg, ← sub_eq_add_neg]



private lemma iteratedSimpleReflection_injective
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (σ : List (Fin n))
    (_hσ : σ.Perm (List.finRange n)) :
    Function.Injective (fun v => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ v) := by
  intro u v huv
  have hlin : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ (u - v) = 0 := by
    rw [iteratedSimpleReflection_sub]
    exact sub_eq_zero.mpr huv
  have hB := iteratedSimpleReflection_preserves_B hDynkin σ (u - v)
  rw [hlin] at hB
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hB

  by_contra hne
  have hpos := hDynkin.2.2.2.2 (u - v) (sub_ne_zero.mpr hne)
  rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj from rfl] at hpos

  simp only [dotProduct] at hpos
  linarith



private theorem iteratedSimpleReflection_periodic
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n)) (v : Fin n → ℤ) :
    ∃ M : ℕ, 0 < M ∧
      (fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ w)^[M] v = v := by
  set c := fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ w
  have hinj := iteratedSimpleReflection_injective hDynkin σ hσ
  have hfin := iteratedSimpleReflection_orbit_finite hDynkin σ v


  have hnotinj : ∃ a b, c^[a] v = c^[b] v ∧ a ≠ b := by
    by_contra hall
    push Not at hall

    exact Set.infinite_range_of_injective (fun a b hab => hall a b hab) |>.not_finite hfin
  obtain ⟨a, b, hab, hne⟩ := hnotinj
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨b - a, Nat.sub_pos_of_lt h, ?_⟩
    have hiter : c^[a] (c^[b - a] v) = c^[a] v := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt h)]
      exact hab.symm
    exact Function.Injective.iterate hinj a hiter
  · refine ⟨a - b, Nat.sub_pos_of_lt h, ?_⟩
    have hiter : c^[b] (c^[a - b] v) = c^[b] v := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt h)]
      exact hab
    exact Function.Injective.iterate hinj b hiter







/-- Some iterate of the displayed list-indexed map has a negative coordinate for every nonzero nonnegative input. -/
theorem auxiliary_iterate_exists_apply_neg
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n))
    (β : Fin n → ℤ) (hβ_nonneg : ∀ i, 0 ≤ β i) (hβ_nonzero : β ≠ 0) :
    ∃ N : ℕ, ∃ i : Fin n,
      ((fun v => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ v)^[N] β) i < 0 := by
  set c := fun v => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ v
  by_contra h
  push Not at h


  obtain ⟨M, hM_pos, hM_period⟩ := iteratedSimpleReflection_periodic hDynkin σ hσ β

  set S := ∑ k ∈ Finset.range M, c^[k] β with hS_def

  have hS_nonneg : ∀ i, 0 ≤ S i := by
    intro i; simp only [hS_def, Finset.sum_apply]
    exact Finset.sum_nonneg (fun k _ => h k i)

  have hS_nonzero : S ≠ 0 := by
    intro hS_eq
    have hβ_zero : β = 0 := by
      funext i
      have hSi : S i = 0 := congr_fun hS_eq i
      rw [hS_def, Finset.sum_apply] at hSi
      have h_each := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h k i)).mp hSi
      have h0 : c^[0] β i = 0 := h_each 0 (Finset.mem_range.mpr hM_pos)
      simp only [Function.iterate_zero, id_eq] at h0
      exact h0
    exact hβ_nonzero hβ_zero




  have hcS : c S = S := by

    change RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ S = S
    rw [hS_def, iteratedSimpleReflection_sum]

    have h_succ : ∀ k, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ (c^[k] β) =
        c^[k + 1] β := by
      intro k; change c (c^[k] β) = c^[k + 1] β
      rw [show k + 1 = k.succ from rfl, Function.iterate_succ', Function.comp_apply]
    simp_rw [h_succ]

    have hsr' := Finset.sum_range_succ' (fun k => c^[k] β) M
    have hsr := Finset.sum_range_succ (fun k => c^[k] β) M
    simp only [Function.iterate_zero, id_eq] at hsr'
    rw [show c^[M] β = β from hM_period] at hsr
    exact add_right_cancel (hsr'.symm.trans hsr)

  have hS_zero := iteratedSimpleReflection_perm_fixed_zero hDynkin σ hσ S hcS

  exact hS_nonzero hS_zero

























/-- Every quiver morphism type is a subsingleton under the displayed family of subsingleton assumptions. -/
lemma auxiliary_quiverHom_subsingleton
    [inst : DecidableEq (Fin n)]
    {Q : Quiver (Fin n)} [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (a b : Fin n) :
    Subsingleton (@Quiver.Hom (Fin n) (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) inst Q p) a b) := by
  constructor
  intro x y
  revert x y
  change ∀ (x y : RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin n) p a b), x = y
  unfold RepresentationTheory.QuiverVertexReversal.reversedAtHom
  cases inst a p <;> cases inst b p <;> exact fun x y => Subsingleton.elim x y


private lemma subsingleton_hom_iteratedReversed
    {Q : Quiver (Fin n)} [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (vs : List (Fin n)) (a b : Fin n) :
    Subsingleton (@Quiver.Hom (Fin n) (auxiliaryListMap Q vs) a b) := by
  induction vs generalizing Q with
  | nil => change Subsingleton (@Quiver.Hom (Fin n) Q a b); infer_instance
  | cons v vs ih =>
    change Subsingleton (@Quiver.Hom (Fin n)
      (auxiliaryListMap (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q v) vs) a b)
    haveI : ∀ (a b : Fin n), Subsingleton
        (@Quiver.Hom (Fin n) (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q v) a b) :=
      fun a b => auxiliary_quiverHom_subsingleton v a b
    exact @ih _ this


/-- A finite type structure on each quiver morphism type when all such types are subsingletons. -/
noncomputable def quiverHomFintypeOfSubsingleton
    {V : Type*} [Quiver V] [∀ (a b : V), Subsingleton (@Quiver.Hom V _ a b)]
    (a b : V) : Fintype (@Quiver.Hom V _ a b) := by
  classical
  exact if h : Nonempty (a ⟶ b)
    then Fintype.ofSubsingleton h.some
    else @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)


/-- A finite type structure on the displayed type associated with a selected finite vertex. -/
noncomputable def auxiliaryFintypeAt
    {Q : Quiver (Fin n)} [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (i : Fin n) : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q i) := by
  haveI : ∀ (a : Fin n), Fintype (@Quiver.Hom (Fin n) Q a i) :=
    fun a => quiverHomFintypeOfSubsingleton a i
  exact Sigma.instFintype



/-- Every module away from the selected vertex of the displayed auxiliary representation is free. -/
lemma auxiliaryRepresentation_free_of_ne
    {k₀ : Type*} [Field k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)]
    (v : Q) (hv : v ≠ i) :
    Module.Free k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) v) := by
  exact Module.Free.of_equiv (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).symm

set_option linter.unusedFintypeInType false in

/-- The module at the selected vertex of the displayed auxiliary representation is free. -/
lemma auxiliaryRepresentation_free_at
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i)] :
    Module.Free k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i) := by





  letI modK : Module k₀ ↥(ρ.auxiliaryDirectSumMap i).ker := inferInstance
  letI acgK : AddCommGroup ↥(ρ.auxiliaryDirectSumMap i).ker :=
    @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k₀ _ ↥(ρ.auxiliaryDirectSumMap i).ker inferInstance modK
  haveI : Module.Free k₀ ↥(ρ.auxiliaryDirectSumMap i).ker :=
    @Module.Free.of_divisionRing k₀ ↥(ρ.auxiliaryDirectSumMap i).ker _ acgK modK
  exact Module.Free.of_equiv (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ).symm


/-- Every module away from the selected vertex of the displayed auxiliary representation is finite. -/
lemma auxiliaryRepresentation_finite_of_ne
    {k₀ : Type*} [Field k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q _ _)
    [∀ v, Module.Finite k₀ (ρ.obj v)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) v) := by
  exact Module.Finite.equiv (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).symm

set_option linter.unusedFintypeInType false in

/-- The module at the selected vertex of the displayed auxiliary representation is finite. -/
lemma auxiliaryRepresentation_finite_at
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i)] :
    Module.Finite k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i) := by





  letI modD : Module k₀ (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i) (fun a => ρ.obj a.1)) := inferInstance
  haveI finD : Module.Finite k₀ (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i) (fun a => ρ.obj a.1)) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype k₀ (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i)
      (fun a => ρ.obj a.1)).symm
  haveI : IsNoetherian k₀ (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i) (fun a => ρ.obj a.1)) :=
    @isNoetherian_of_isNoetherianRing_of_finite k₀
      (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i) (fun a => ρ.obj a.1)) _
      (@RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k₀ _ (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q _ i) (fun a => ρ.obj a.1))
        inferInstance modD) modD _ finD
  exact Module.Finite.equiv (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ).symm












/-- Under the displayed quiver and vertex hypotheses, the two auxiliary maps on integer-valued vertex functions agree. -/
lemma auxiliary_vector_maps_eq
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q p)
    (d : Fin n → ℤ) :
    haveI := auxiliaryFintypeAt (Q := Q) p
    RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt (fun (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q p) => a.1) p d =
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) p d := by

  haveI := auxiliaryFintypeAt (Q := Q) p
  haveI : ∀ (a b : Fin n), Fintype (@Quiver.Hom (Fin n) Q a b) :=
    fun a b => quiverHomFintypeOfSubsingleton a b
  ext v
  unfold RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform
  by_cases hv : v = p
  · subst hv
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, if_true]


    have hdot : d ⬝ᵥ RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj *ᵥ Pi.single v 1 =
        2 * d v - ∑ j : Fin n, adj j v * d j := by

      simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]

      simp only [RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform]

      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]

      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (d _) (adj _ _)]
      ring

    have hcard : ∀ j : Fin n, (Fintype.card (@Quiver.Hom (Fin n) Q j v) : ℤ) = adj j v := by
      intro j
      rcases hDynkin.2.2.1 j v with h0 | h1
      ·
        haveI : IsEmpty (@Quiver.Hom (Fin n) Q j v) := hOrient.1 j v (by omega)
        rw [Fintype.card_eq_zero]; omega
      ·
        rcases hOrient.2.1 j v h1 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        ·
          haveI : Unique (@Quiver.Hom (Fin n) Q j v) :=
            { default := e, uniq := fun a => Subsingleton.elim a e }
          simp [Fintype.card_unique, h1]
        ·
          exact ((hp j).false e).elim

    have hsum : (∑ a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q v, d a.fst) = ∑ j : Fin n, adj j v * d j := by




      letI sigmaFT : Fintype (Σ j : Fin n, @Quiver.Hom (Fin n) Q j v) := Sigma.instFintype

      have h_unfold : (∑ a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q v, d a.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ sigmaFT) (fun a => d a.fst) := by
        apply Finset.sum_congr
        · ext x; exact iff_of_true (Finset.mem_univ x) (@Finset.mem_univ _ sigmaFT x)
        · intros; rfl
      rw [h_unfold]

      rw [Fintype.sum_sigma]
      congr 1; ext j

      change (∑ _ : @Quiver.Hom (Fin n) Q j v, d j) = adj j v * d j
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ (α := @Quiver.Hom (Fin n) Q j v)).card = Fintype.card _ := rfl
      rw [this, show (Fintype.card (@Quiver.Hom (Fin n) Q j v) : ℤ) = adj j v from hcard j]

    have : ∀ (inst1 inst2 : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q v)),
        @Finset.sum _ _ _ (@Finset.univ _ inst1) (fun x => d x.fst) =
        @Finset.sum _ _ _ (@Finset.univ _ inst2) (fun x => d x.fst) := by
      intro i1 i2
      apply Finset.sum_congr
      · ext x; simp [Finset.mem_univ]
      · intros; rfl
    linarith [this (auxiliaryFintypeAt v) inferInstance, hsum, hdot]
  · simp only [hv, ite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_zero, sub_zero]




private def SurvivingRepData
    (k : Type*) [CommSemiring k] (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (Q_end : @Quiver.{0, 0} (Fin n))
    (d_cur : Fin n → ℤ) (tail : List (Fin n)) : Prop :=
  ∃ (ρ_end : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q_end),
    (∀ v, @Module.Free k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v)) ∧
    (∀ v, @Module.Finite k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v)) ∧
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _ Q_end ρ_end ∧
    ∀ v, (@Module.finrank k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v) : ℤ) =
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) tail d_cur v








private def TerminalRepData
    (k : Type*) [Field k] (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (Q_end : @Quiver.{0, 0} (Fin n)) (p : Fin n) : Prop :=
  RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q_end adj ∧
  (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_end a b)) ∧
  ∃ (ρ_end : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q_end),
    (∀ v, @Module.Free k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v)) ∧
    (∀ v, @Module.Finite k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v)) ∧
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _ Q_end ρ_end ∧
    ∀ v, (@Module.finrank k (ρ_end.obj v) _ (ρ_end.addCommMonoid v) (ρ_end.moduleInstance v) : ℤ) =
      RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v





private lemma walk_admissible_ordering
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    (tail : List (Fin n))
    {Q_cur : @Quiver.{0, 0} (Fin n)}
    (hOrient_cur : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q_cur adj)
    (hSS_cur : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b))
    (hSinks : ∀ m (hm : m < tail.length),
      @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
        (@auxiliaryListMap _ _ Q_cur (tail.take m))
        (tail.get ⟨m, hm⟩))
    (ρ_cur : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q_cur)
    (hFree_cur : ∀ v, Module.Free k (ρ_cur.obj v))
    (hFinite_cur : ∀ v, Module.Finite k (ρ_cur.obj v))
    (hIndec_cur : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _ Q_cur ρ_cur)
    (d_cur : Fin n → ℤ)
    (hd_cur : d_cur = fun v => (Module.finrank k (ρ_cur.obj v) : ℤ)) :
    (∃ (i : ℕ) (p : Fin n), i ≤ tail.length ∧
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) (tail.take i) d_cur = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧
      TerminalRepData k n adj (@auxiliaryListMap _ _ Q_cur (tail.take i)) p)
    ∨
    SurvivingRepData k n adj (@auxiliaryListMap _ _ Q_cur tail) d_cur tail := by
  induction tail generalizing Q_cur d_cur with
  | nil =>

    right
    exact ⟨ρ_cur, fun v => hFree_cur v, fun v => hFinite_cur v, hIndec_cur,
      fun v => by simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection]; rw [hd_cur]⟩
  | cons i rest ih =>

    have hi_sink : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q_cur i := by
      have := hSinks 0 (by simp)


      exact this

    haveI : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b) := hSS_cur
    haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_cur i) :=
      auxiliaryFintypeAt i
    haveI : ∀ v, Module.Free k (ρ_cur.obj v) := hFree_cur
    haveI : ∀ v, Module.Finite k (ρ_cur.obj v) := hFinite_cur

    rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective k _ _ _ Q_cur ρ_cur i _ _ hi_sink hIndec_cur with
      h_simple | h_surj
    ·

      left
      refine ⟨0, i, Nat.zero_le _, ?_, ?_⟩
      · simp only [List.take_zero, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection]
        ext v
        by_cases hv : v = i
        · subst hv; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, hd_cur]; exact_mod_cast h_simple.1
        · simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Ne.symm hv, hd_cur]
          exact_mod_cast h_simple.2 v hv
      ·
        refine ⟨hOrient_cur, hSS_cur, ρ_cur, hFree_cur, hFinite_cur, hIndec_cur, ?_⟩
        intro v
        by_cases hv : v = i
        · subst hv; simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.single_eq_same]; exact_mod_cast h_simple.1
        · simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.single_eq_of_ne hv]; exact_mod_cast h_simple.2 v hv
    ·

      set d_new := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i d_cur with hd_new_def
      have hd_eq : (fun v => (Module.finrank k (ρ_cur.obj v) : ℤ)) = d_cur := by
        rw [hd_cur]
      have hbridge :
          haveI := auxiliaryFintypeAt (Q := Q_cur) i
          RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt (fun (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_cur i) => a.1) i d_cur =
          RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i d_cur :=
        @auxiliary_vector_maps_eq _ _
          hDynkin Q_cur hOrient_cur hSS_cur i hi_sink d_cur

      have h_sink_ss_of_src :
          (∀ (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_cur i), Subsingleton (ρ_cur.obj a.1)) →
          Subsingleton (ρ_cur.obj i) := by
        intro hsrc_ss
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := h_surj a
        obtain ⟨y, rfl⟩ := h_surj b
        suffices x = y by rw [this]
        have : ∀ z : DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_cur i)
            (fun a => ρ_cur.obj a.1), z = 0 :=
          fun z => DFinsupp.ext (fun j => @Subsingleton.elim _ (hsrc_ss j) _ _)
        exact (this x).trans (this y).symm
      let Q_rev := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_cur i
      let ρ_plus := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q_cur i hi_sink ρ_cur

      have hSS_rev : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_rev a b) :=
        fun a b => auxiliary_quiverHom_subsingleton i a b
      haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_rev i) :=
        @auxiliaryFintypeAt _ Q_rev hSS_rev i

      have hFree_plus : ∀ v, Module.Free k (ρ_plus.obj v) := fun v => by
        by_cases hv : v = i
        · rw [hv]; exact @auxiliaryRepresentation_free_at k _ (Fin n) _ Q_cur i hi_sink ρ_cur _ _ _
        · exact @auxiliaryRepresentation_free_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ_cur _ v hv
      have hFinite_plus : ∀ v, Module.Finite k (ρ_plus.obj v) := fun v => by
        by_cases hv : v = i
        · rw [hv]; exact @auxiliaryRepresentation_finite_at k _ (Fin n) _ Q_cur i hi_sink ρ_cur _ _ _
        · exact @auxiliaryRepresentation_finite_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ_cur _ v hv

      have hIndec_plus :
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _ Q_rev ρ_plus := by
        rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary k _ _ _ Q_cur i hi_sink ρ_cur _ _ hIndec_cur
          with h | h_zero
        · exact h
        · exfalso
          obtain ⟨⟨v, hv⟩, _⟩ := hIndec_cur
          suffices hs : ∀ j, Subsingleton
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _ Q_cur ρ_cur j) from
            absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
          intro j
          by_cases hj : j = i
          · rw [hj]; exact h_sink_ss_of_src (fun ⟨m, e⟩ =>
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _ Q_cur i hi_sink ρ_cur m
                (fun h => (hi_sink m).false (h ▸ e))).toEquiv.subsingleton_congr.mp (h_zero m))
          · exact (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _
              Q_cur i hi_sink ρ_cur j hj).toEquiv.subsingleton_congr.mp (h_zero j)

      have hOrient_rev : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q_rev adj :=
        RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation hDynkin.1 hDynkin.2.1 hOrient_cur i

      have hDim_plus : ∀ v, (Module.finrank k (ρ_plus.obj v) : ℤ) = d_new v := by
        intro v
        haveI : ∀ v, Module.Free k (ρ_plus.obj v) := hFree_plus
        haveI : ∀ v, Module.Finite k (ρ_plus.obj v) := hFinite_plus
        have h668 := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective k _
          (Fin n) _ Q_cur i hi_sink ρ_cur _ _ _ h_surj v
        change (ρ_plus.auxiliaryNat k v : ℤ) = d_new v
        rw [h668, hd_eq]
        convert congr_fun hbridge v

      have hSinks_rest : ∀ m (hm : m < rest.length),
          @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
            (@auxiliaryListMap _ _ Q_rev (rest.take m))
            (rest.get ⟨m, hm⟩) := by
        intro m hm
        exact hSinks (m + 1) (by simp [List.length_cons]; omega)

      rcases @ih Q_rev hOrient_rev hSS_rev hSinks_rest ρ_plus hFree_plus hFinite_plus
        hIndec_plus d_new (funext fun v => (hDim_plus v).symm) with
        ⟨j, p, hj, hp, hTerm⟩ | ⟨ρ_end, hFree_end, hFinite_end, hIndec_end, hDim_end⟩
      ·


        left
        refine ⟨j + 1, p, by simp [List.length_cons]; omega, ?_, ?_⟩
        · simp only [List.take_succ_cons]
          rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons]
          exact hp
        · show TerminalRepData k n adj
            (@auxiliaryListMap _ _ Q_cur ((i :: rest).take (j + 1))) p
          rw [List.take_succ_cons]
          exact hTerm
      ·
        right
        show SurvivingRepData k n adj _ d_cur (i :: rest)
        unfold SurvivingRepData
        exact ⟨ρ_end, hFree_end, hFinite_end, hIndec_end, fun v => by
          rw [show RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) (i :: rest) d_cur =
            RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) rest d_new from
            RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons _ i rest d_cur]
          exact hDim_end v⟩











/-- Under the displayed hypotheses, either a prefix yields the stated equality and auxiliary predicate, or the full-list transform is nonnegative, nonzero, and satisfies the alternative predicate. -/
lemma auxiliary_prefix_or_full_list
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (σ : List (Fin n)) (hσ : AuxiliaryListProperty Q σ)
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition)
    (d : Fin n → ℤ) (hd : d = fun v => (Module.finrank k (ρ.obj v) : ℤ)) :
    (∃ (i : ℕ) (p : Fin n), i ≤ σ.length ∧
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) (σ.take i) d = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧
      TerminalRepData k n adj (@auxiliaryListMap _ _ Q (σ.take i)) p)
    ∨
    ((∀ i, 0 ≤ RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ d i) ∧
     RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) σ d ≠ 0 ∧
     SurvivingRepData k n adj Q d σ) := by

  rcases walk_admissible_ordering hDynkin σ hOrient
    (fun a b => inferInstance) hσ.get_property ρ
    (fun v => inferInstance) (fun v => inferInstance) hρ d hd with
    ⟨i, p, hi, hp, hTerm⟩ | hSurv
  · left; exact ⟨i, p, hi, hp, hTerm⟩
  ·
    right
    have heq : @auxiliaryListMap _ _ Q σ = Q :=
      auxiliaryListMap_eq_self_of_perm Q σ hσ.perm_finRange

    have hSurv_Q : SurvivingRepData k n adj Q d σ := heq ▸ hSurv
    obtain ⟨ρ', hFree', hFinite', hIndec', hDim'⟩ := hSurv_Q
    refine ⟨?_, ?_, ρ', hFree', hFinite', hIndec', hDim'⟩
    ·
      intro v; rw [← hDim' v]; exact Int.natCast_nonneg _
    ·
      intro h0
      obtain ⟨⟨v, hv⟩, _⟩ := hIndec'
      have h0v : (@Module.finrank k _ _ (ρ'.addCommMonoid v) (ρ'.moduleInstance v) : ℤ) = 0 := by
        rw [hDim' v]; exact congr_fun h0 v
      simp only [Int.natCast_eq_zero] at h0v
      haveI := hFree' v; haveI := hFinite' v
      rw [Module.finrank_eq_zero_iff_of_free (R := k)] at h0v
      exact absurd h0v (not_subsingleton_iff_nontrivial.mpr hv)













private lemma indecomposable_reduces_to_simpleRoot
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices
        (fun v => (Module.finrank k (ρ.obj v) : ℤ)) = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧
      ∃ (Q_end : @Quiver.{0, 0} (Fin n)), TerminalRepData k n adj Q_end p := by
  obtain ⟨σ, hσ⟩ := auxiliary_exists_list_property hDynkin hOrient
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj
  set d := fun v => (Module.finrank k (ρ.obj v) : ℤ) with hd_def
  set c := fun v => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ v

  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => Int.natCast_nonneg _

  have hd_nonzero : d ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ.1
    intro heq
    have h0 : d v = 0 := congr_fun heq v
    simp only [hd_def] at h0

    have hfr : Module.finrank k (ρ.obj v) = 0 := by exact_mod_cast h0


    rw [Module.finrank_eq_zero_iff_of_free (R := k)] at hfr
    exact absurd hfr (not_subsingleton_iff_nontrivial.mpr hv)

  have hσ_perm := hσ.perm_finRange
  obtain ⟨N, i, hNeg⟩ := auxiliary_iterate_exists_apply_neg hDynkin σ hσ_perm d hd_nonneg hd_nonzero



  suffices ∀ (M : ℕ),
    (∃ (vertices : List (Fin n)) (p : Fin n),
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vertices d = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧
      ∃ (Q_end : @Quiver.{0, 0} (Fin n)), TerminalRepData k n adj Q_end p) ∨
    ((∀ j, 0 ≤ c^[M] d j) ∧
     ∃ (ρ_M : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q),
       (∀ v, Module.Free k (ρ_M.obj v)) ∧
       (∀ v, Module.Finite k (ρ_M.obj v)) ∧
       ρ_M.AuxiliaryCondition ∧
       (∀ v, (Module.finrank k (ρ_M.obj v) : ℤ) = c^[M] d v)) by
    rcases this N with ⟨vertices, p, hp, hQend⟩ | ⟨hNN, _⟩
    · exact ⟨vertices, p, hp, hQend⟩
    · exact absurd (hNN i) (not_le.mpr hNeg)
  intro M
  induction M with
  | zero =>
    right
    exact ⟨fun j => by simp only [Function.iterate_zero, id_eq]; exact hd_nonneg j,
           ρ, ‹_›, ‹_›, hρ,
           fun v => by simp only [Function.iterate_zero, id_eq, hd_def]⟩
  | succ M ih =>
    rcases ih with ⟨vertices, p, hp, hQend⟩ |
      ⟨hM_nonneg, ρ_M, hFree_M, hFinite_M, hIndecomp_M, hDimVec_M⟩
    · left; exact ⟨vertices, p, hp, hQend⟩
    ·

      haveI : ∀ v, Module.Free k (ρ_M.obj v) := hFree_M
      haveI : ∀ v, Module.Finite k (ρ_M.obj v) := hFinite_M
      have hd_M : c^[M] d = fun v => (Module.finrank k (ρ_M.obj v) : ℤ) := by
        ext v; exact (hDimVec_M v).symm
      rcases auxiliary_prefix_or_full_list hDynkin hOrient σ hσ ρ_M hIndecomp_M
        (c^[M] d) hd_M with
        ⟨j, p, hj, hp, hTerm⟩ | ⟨hnonneg, hnonzero, ρ', hFree', hFinite', hIndecomp', hDimVec'⟩
      ·

        left

        refine ⟨(List.replicate M σ).flatten ++ σ.take j, p, ?_, _, hTerm⟩
        rw [auxiliaryVectorMap_append]
        rw [auxiliaryVectorMap_replicate]
        exact hp
      ·
        right
        exact ⟨fun j => by rw [Function.iterate_succ', Function.comp_apply]; exact hnonneg j,
          ρ', hFree', hFinite', hIndecomp',
          fun v => by rw [Function.iterate_succ', Function.comp_apply]; exact hDimVec' v⟩























/-- Under the displayed hypotheses, there exist a vertex list, a finite index, a second quiver, and an auxiliary representation satisfying the stated equalities and finiteness conditions. -/
@[source_ref "Chapter6/Theorem6.8.1" (role := primary)]
theorem auxiliary_exists_data_of_representation
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    ∃ (vertices : List (Fin n)) (p : Fin n),

      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices
        (fun v => (Module.finrank k (ρ.obj v) : ℤ)) = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧

      ∃ (Q_end : @Quiver.{0, 0} (Fin n)),
        RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q_end adj ∧
        (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_end a b)) ∧
        ∃ (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q_end),
          (∀ v, @Module.Free k (W.obj v) _ (W.addCommMonoid v) (W.moduleInstance v)) ∧
          (∀ v, @Module.Finite k (W.obj v) _ (W.addCommMonoid v) (W.moduleInstance v)) ∧
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _ Q_end W ∧
          (∀ v, (@Module.finrank k (W.obj v) _ (W.addCommMonoid v) (W.moduleInstance v) : ℤ) =
            RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v) := by
  obtain ⟨vertices, p, hrefl, Q_end, hTerm⟩ :=
    indecomposable_reduces_to_simpleRoot hDynkin hOrient ρ hρ
  exact ⟨vertices, p, hrefl, Q_end, hTerm⟩












/-- Under the displayed matrix and quiver hypotheses, the vertexwise finrank function of an auxiliary representation satisfies the indicated predicate. -/
@[source_ref "Chapter6/Corollary6.8.2" (role := primary)]
theorem auxiliary_property_finrank
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj (fun v => (Module.finrank k (ρ.obj v) : ℤ)) := by
  set d := fun v => (Module.finrank k (ρ.obj v) : ℤ) with hd_def

  have hd_pos : ∀ v, 0 ≤ d v := fun v => Int.natCast_nonneg _

  have hd_nonzero : d ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ.1
    intro heq
    have hv_eq := congr_fun heq v
    simp only [hd_def, Pi.zero_apply, Int.natCast_eq_zero] at hv_eq

    rw [Module.finrank_eq_zero_iff_of_free (R := k)] at hv_eq
    exact absurd hv_eq (not_subsingleton_iff_nontrivial.mpr hv)

  obtain ⟨vertices, p, hrefl, _⟩ := indecomposable_reduces_to_simpleRoot hDynkin hOrient ρ hρ

  exact RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_property_of_exists_eq hDynkin d hd_pos hd_nonzero
    ⟨vertices, p, hrefl⟩








/-- The displayed quadratic expression on the vertexwise finrank function of an auxiliary representation equals two. -/
theorem auxiliary_finrank_quadratic_form_eq_two
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) = 2 :=
  (auxiliary_property_finrank hDynkin hOrient ρ hρ).1.2










/-- Applying the auxiliary quiver operation to any number of repeated full vertex lists fixes the quiver. -/
theorem auxiliaryListMap_replicate_eq_self
    (Q : Quiver (Fin n)) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n)) (M : ℕ) :
    auxiliaryListMap Q ((List.replicate M σ).flatten) = Q := by
  induction M with
  | zero => simp [auxiliaryListMap]
  | succ M ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [auxiliaryListMap_append]
    rw [auxiliaryListMap_eq_self_of_perm Q σ hσ]
    exact ih



/-- Every valid entry of a prefix of a list satisfying the auxiliary predicate has the displayed vertex property. -/
theorem auxiliary_property_get_take
    (Q : Quiver (Fin n)) (σ : List (Fin n))
    (hσ : AuxiliaryListProperty Q σ) (j : ℕ) (hj : j ≤ σ.length) :
    ∀ m (hm : m < (σ.take j).length),
      @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
        (auxiliaryListMap Q ((σ.take j).take m))
        ((σ.take j).get ⟨m, hm⟩) := by
  intro m hm
  have hm_lt : m < j := by rwa [List.length_take_of_le hj] at hm
  have hm_lt_len : m < σ.length := lt_of_lt_of_le hm_lt hj
  rw [List.take_take, min_eq_left (le_of_lt hm_lt)]
  have : (σ.take j).get ⟨m, hm⟩ = σ.get ⟨m, hm_lt_len⟩ := by
    simp [List.getElem_take]
  rw [this]
  exact hσ.get_property m hm_lt_len



/-- Every valid entry of repeated copies followed by a prefix of an auxiliary list has the displayed vertex property. -/
@[source_ref "Chapter6/Section6.8_heading" (role := primary)]
theorem auxiliary_property_get_replicate_append_take
    (Q : Quiver (Fin n)) (σ : List (Fin n))
    (hσ : AuxiliaryListProperty Q σ) (M : ℕ) (j : ℕ) (hj : j ≤ σ.length) :
    ∀ m (hm : m < ((List.replicate M σ).flatten ++ σ.take j).length),
      @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
        (auxiliaryListMap Q (((List.replicate M σ).flatten ++ σ.take j).take m))
        (((List.replicate M σ).flatten ++ σ.take j).get ⟨m, hm⟩) := by
  induction M with
  | zero =>
    simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
    exact auxiliary_property_get_take Q σ hσ j hj
  | succ M ih =>


    suffices h : ∀ (L : List (Fin n)),
        L = σ ++ ((List.replicate M σ).flatten ++ σ.take j) →
        ∀ m (hm : m < L.length),
          @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) (auxiliaryListMap Q (L.take m)) (L.get ⟨m, hm⟩) by
      intro m hm
      exact h _ (by simp [List.replicate_succ, List.flatten_cons, List.append_assoc]) m hm
    intro L hL
    subst hL
    set tail := (List.replicate M σ).flatten ++ σ.take j with htail_def
    intro m hm
    by_cases hm_lt : m < σ.length
    ·
      have htake : (σ ++ tail).take m = σ.take m :=
        List.take_append_of_le_length (le_of_lt hm_lt)
      have hget : (σ ++ tail).get ⟨m, hm⟩ = σ.get ⟨m, hm_lt⟩ := by
        simp [List.getElem_append_left hm_lt]
      rw [htake, hget]
      exact hσ.get_property m hm_lt
    ·
      push Not at hm_lt
      set m' := m - σ.length with hm'_def
      have hm_eq : m = σ.length + m' := by omega
      have hm'_lt : m' < tail.length := by
        simp [List.length_append] at hm; omega
      have htake : (σ ++ tail).take m = σ ++ tail.take m' := by
        rw [hm_eq, List.take_append]; simp
      have hget : (σ ++ tail).get ⟨m, hm⟩ = tail.get ⟨m', hm'_lt⟩ := by
        simp [hm_eq, List.getElem_append_right (by omega : σ.length ≤ σ.length + m')]
      rw [htake, auxiliaryListMap_append,
          auxiliaryListMap_eq_self_of_perm Q σ hσ.perm_finRange, hget]
      exact ih m' hm'_lt

end RepresentationTheory.AuxiliaryQuiverConstructions
