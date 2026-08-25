/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.DynkinDiagram.AffineClassification
import RepresentationTheory.FiniteGroupCharacterIntegrality
import RepresentationTheory.FiniteGroup.ClassFunctions
import RepresentationTheory.Group.CharacterOperations
import RepresentationTheory.ComplexUnitCharacters
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory

open _root_.Matrix _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Module

/-- The tautological linear representation of a subgroup on two-dimensional complex coordinate space. -/
noncomputable def tautologicalRepresentation (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) :
    Representation ℂ G (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    simp only [OneMemClass.coe_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul, Matrix.toLin'_mul]; rfl

/-- The two-dimensional finite-dimensional representation obtained from a subgroup of the special unitary group. -/
noncomputable def tautologicalFDRep (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) : FDRep ℂ G :=
  FDRep.of (tautologicalRepresentation G)

variable {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
  {m : ℕ} (W : Fin m → FDRep ℂ G)

/-- A family of finite-dimensional representations that lists all simple objects without repetition. -/
structure IsCompleteSimpleFamily : Prop where
  /-- Each representation occurring in the family is simple. -/
  simple_entry : ∀ i, Simple (W i)
  /-- Two entries in the family have the same index whenever they are isomorphic. -/
  eq_of_isomorphic : ∀ i j, Nonempty (W i ≅ W j) → i = j
  /-- Every simple representation is isomorphic to an entry of the family. -/
  exists_isomorphic_entry : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ W i)

/-- The natural-number multiplicity attached to a pair of entries in a representation family. -/
noncomputable def tensorMultiplicity (i j : Fin m) : ℕ := finrank ℂ (W i ⟶ tautologicalFDRep G ⊗ W j)

/-- An auxiliary integer-valued pairing on indices of a representation family. -/
noncomputable def auxiliaryIntegerPairing (i j : Fin m) : ℤ := (tensorMultiplicity W i j : ℤ)

/-- An auxiliary integer matrix entry associated with a family of representations. -/
noncomputable def auxiliaryQuadraticFormEntry (i j : Fin m) : ℤ :=
  2 * (if i = j then 1 else 0) - tensorMultiplicity W i j

omit [Finite G] in

/-- The tautological character at a group element equals the trace of its underlying matrix. -/
lemma character_tautological_eq_trace (g : G) :
    (tautologicalFDRep G).character g =
      Matrix.trace ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [FDRep.character, tautologicalFDRep, FDRep.of_ρ']
  exact Matrix.trace_toLin'_eq _

omit [Finite G] in

/-- The tautological character takes the same value on an element and its inverse. -/
lemma character_tautological_inv (g : G) : (tautologicalFDRep G).character g⁻¹ = (tautologicalFDRep G).character g := by
  rw [character_tautological_eq_trace, character_tautological_eq_trace]
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  set B : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g⁻¹.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hB

  have hBA : B * A = 1 := by
    rw [hB, hA, ← MulMemClass.coe_mul, ← MulMemClass.coe_mul, inv_mul_cancel]
    rfl

  have hdet : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2

  have hBinv : B = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  rw [hBinv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two]
  ring

/-- The character of the tautological representation is fixed by complex conjugation for a finite subgroup. -/
lemma star_character_tautological_eq (g : G) :
    (starRingEnd ℂ) ((tautologicalFDRep G).character g) = (tautologicalFDRep G).character g := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [← RepresentationTheory.Group.CharacterOperations.character_inv_eq_conj, character_tautological_inv]

/-- The tautological character of a finite subgroup has zero imaginary part. -/
lemma character_tautological_im_eq_zero (g : G) : ((tautologicalFDRep G).character g).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_character_tautological_eq g)

omit [Finite G] in

/-- The real part of the tautological character is at most two. -/
lemma character_tautological_re_le_two (g : G) : ((tautologicalFDRep G).character g).re ≤ 2 := by
  classical
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA

  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).1
  have hstar : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hu

  have hdiag : ∀ i : Fin 2, (A i i).re ≤ 1 := by
    intro i

    have hsum : ∑ k : Fin 2, Complex.normSq (A k i) = 1 := by
      have hii : (star A * A) i i = 1 := by rw [hstar, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at hii
      have hterm : ∀ k : Fin 2, (star A) i k * A k i
          = ((Complex.normSq (A k i) : ℝ) : ℂ) := by
        intro k
        rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Complex.ofReal_sum] at hii
      exact_mod_cast hii
    have hle : Complex.normSq (A i i) ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun k => Complex.normSq (A k i))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have hre2 : (A i i).re * (A i i).re ≤ 1 := by
      have hns := Complex.normSq_apply (A i i)
      nlinarith [mul_self_nonneg (A i i).im, hle, hns]
    nlinarith [hre2]

  have htr : (tautologicalFDRep G).character g = A 0 0 + A 1 1 := by
    rw [character_tautological_eq_trace, ← hA, Matrix.trace_fin_two]
  rw [htr, Complex.add_re]
  linarith [hdiag 0, hdiag 1]

/-- The multiplicity attached to two entries of a complete simple family is symmetric. -/
@[source_ref "Chapter6/Problem6.1.6" (role := primary),
  source_ref "Chapter6/Problem6.1.6/Derived4" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived5" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived7" (role := supporting)]
theorem tensorMultiplicity_comm (_hW : IsCompleteSimpleFamily W) (i j : Fin m) :
    tensorMultiplicity W i j = tensorMultiplicity W j i := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1 := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (tautologicalFDRep G ⊗ W j) (W i)
  have h2 := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (tautologicalFDRep G ⊗ W i) (W j)
  have hC : (tensorMultiplicity W i j : ℂ) = (tensorMultiplicity W j i : ℂ) := by
    simp only [tensorMultiplicity]
    rw [← h1, ← h2]
    congr 1
    simp only [FDRep.char_tensor, Pi.mul_apply]
    rw [← Equiv.sum_comp (Equiv.inv G)
      (fun g => (tautologicalFDRep G).character g * (W i).character g * (W j).character g⁻¹)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    simp only [Equiv.inv_apply, inv_inv]
    rw [character_tautological_inv]
    ring
  exact_mod_cast hC

/-- A character decomposes as the sum of the simple characters weighted by morphism-space dimensions. -/
lemma character_eq_sum_simple_characters (hW : IsCompleteSimpleFamily W) (S : FDRep ℂ G) :
    S.character = ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hzero : S.character - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character = 0 := by
    apply RepresentationTheory.FiniteGroup.ClassFunctions.FiniteGroup.ClassFunction.eq_zero_of_characterPairing_eq_zero
    ·
      intro g h
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FDRep.char_conj]
    ·
      intro V' _
      obtain ⟨k, ⟨isok⟩⟩ := hW.exists_isomorphic_entry V' ‹Simple V'›
      haveI : Simple (W k) := hW.simple_entry k
      rw [FDRep.char_iso isok]

      have step : ∀ g : G,
          (S.character - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character) g
              * (W k).character g⁻¹
            = S.character g * (W k).character g⁻¹
              - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ)
                  * ((W j).character g * (W k).character g⁻¹) := by
        intro g
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
          Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun g _ => step g), Finset.sum_sub_distrib, Finset.sum_comm]

      have hL : ∑ g : G, S.character g * (W k).character g⁻¹
          = (Fintype.card G : ℂ) * (finrank ℂ (W k ⟶ S) : ℂ) := by
        have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom S (W k)
        rw [smul_eq_mul] at h
        rw [← h, ← mul_assoc, mul_invOf_self, one_mul]

      have hO : ∀ j : Fin m, ∑ g : G, (W j).character g * (W k).character g⁻¹
          = (Fintype.card G : ℂ) * (if j = k then 1 else 0) := by
        intro j
        haveI : Simple (W j) := hW.simple_entry j
        have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (W j) (W k)
        rw [smul_eq_mul] at h

        have hval : ⅟(Fintype.card G : ℂ) * ∑ g : G, (W j).character g * (W k).character g⁻¹
            = (if j = k then (1 : ℂ) else 0) := by
          rw [h]
          by_cases hjk : j = k
          · rw [if_pos (⟨eqToIso (congrArg W hjk)⟩ : Nonempty (W j ≅ W k)), if_pos hjk]
          · rw [if_neg (fun hh => hjk (hW.eq_of_isomorphic j k hh)), if_neg hjk]
        calc ∑ g : G, (W j).character g * (W k).character g⁻¹
            = (Fintype.card G : ℂ)
                * (⅟(Fintype.card G : ℂ) * ∑ g : G, (W j).character g * (W k).character g⁻¹) := by
              rw [← mul_assoc, mul_invOf_self, one_mul]
          _ = (Fintype.card G : ℂ) * (if j = k then 1 else 0) := by rw [hval]

      simp_rw [← Finset.mul_sum, hO]
      rw [hL]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ k
        (fun j => (finrank ℂ (W j ⟶ S) : ℂ) * (Fintype.card G : ℂ))]
      rw [if_pos (Finset.mem_univ k)]
      ring
  exact sub_eq_zero.mp hzero

/-- The dimension of a representation is the sum of simple dimensions weighted by morphism-space dimensions. -/
lemma finrank_eq_sum_hom_finrank_mul (hW : IsCompleteSimpleFamily W) (S : FDRep ℂ G) :
    (finrank ℂ S : ℤ) = ∑ j, (finrank ℂ (W j ⟶ S) : ℤ) * (finrank ℂ (W j) : ℤ) := by
  have h1 := congrFun (character_eq_sum_simple_characters W hW S) (1 : G)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FDRep.char_one] at h1
  exact_mod_cast h1

/-- The dimension vector lies in the kernel of every row of the auxiliary integer matrix. -/
lemma weighted_auxiliaryRowSum_eq_zero_alternate (hW : IsCompleteSimpleFamily W) (i : Fin m) :
    (∑ j, auxiliaryQuadraticFormEntry W i j * (finrank ℂ (W j) : ℤ)) = 0 := by
  classical

  have key : (∑ j, (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ)) = 2 * (finrank ℂ (W i) : ℤ) := by
    set S : FDRep ℂ G := tautologicalFDRep G ⊗ W i with hS
    have hswap : (∑ j, (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ))
        = ∑ j, (tensorMultiplicity W j i : ℤ) * (finrank ℂ (W j) : ℤ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [tensorMultiplicity_comm W hW i j]
    have hcount : (∑ j, (tensorMultiplicity W j i : ℤ) * (finrank ℂ (W j) : ℤ)) = (finrank ℂ S : ℤ) := by
      rw [finrank_eq_sum_hom_finrank_mul W hW S]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rfl
    rw [hswap, hcount]

    have htensor : (finrank ℂ S : ℂ) = 2 * (finrank ℂ (W i) : ℂ) := by
      have e1 : S.character 1 = (finrank ℂ S : ℂ) := FDRep.char_one _
      have e3 : (W i).character 1 = (finrank ℂ (W i) : ℂ) := FDRep.char_one _
      have e2 : (tautologicalFDRep G).character 1 = 2 := by
        rw [character_tautological_eq_trace]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      have h1 := congrFun (FDRep.char_tensor (tautologicalFDRep G) (W i)) (1 : G)
      rw [Pi.mul_apply, e2, e3] at h1
      rw [← e1, hS]; exact h1
    exact_mod_cast htensor

  have expand : ∀ j, auxiliaryQuadraticFormEntry W i j * (finrank ℂ (W j) : ℤ)
      = (if i = j then 2 * (finrank ℂ (W j) : ℤ) else 0)
        - (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    intro j
    simp only [auxiliaryQuadraticFormEntry]
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl (fun j _ => expand j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => 2 * (finrank ℂ (W j) : ℤ)),
    if_pos (Finset.mem_univ i), key]
  ring

/-- An auxiliary binary predicate on indices of a family of representations. -/
def auxiliaryIndexPredicate (i j : Fin m) : Prop := 1 ≤ tensorMultiplicity W i j

/-- The path-connectedness relation on indices of a representation family. -/
def IndexPathConnected (i j : Fin m) : Prop :=
  ∃ p : List (Fin m), p.head? = some i ∧ p.getLast? = some j ∧ p.IsChain (auxiliaryIndexPredicate W)

variable {W}

omit [Finite G] in

/-- Every index is path-connected to itself. -/
lemma IndexPathConnected.refl (i : Fin m) : IndexPathConnected W i i :=
  ⟨[i], rfl, rfl, List.isChain_singleton i⟩

omit [Finite G] in

/-- Indices joined with positive multiplicity are path-connected. -/
lemma IndexPathConnected.of_positive_multiplicity {i j : Fin m} (h : 1 ≤ tensorMultiplicity W i j) : IndexPathConnected W i j :=
  ⟨[i, j], rfl, rfl, List.isChain_pair.mpr h⟩

omit [Finite G] in

/-- Path-connectedness of indices is transitive. -/
lemma IndexPathConnected.trans {i j k : Fin m}
    (hij : IndexPathConnected W i j) (hjk : IndexPathConnected W j k) : IndexPathConnected W i k := by
  obtain ⟨p, hp1, hp2, hpc⟩ := hij
  obtain ⟨q, hq1, hq2, hqc⟩ := hjk

  obtain ⟨t, rfl⟩ : ∃ t, q = j :: t := by
    cases q with
    | nil => simp at hq1
    | cons a t => exact ⟨t, by simp only [List.head?_cons, Option.some.injEq] at hq1; rw [hq1]⟩
  refine ⟨p ++ t, ?_, ?_, ?_⟩
  · rw [List.head?_append, hp1]; rfl
  · rw [List.getLast?_append, hp2]
    have ht : (j :: t).getLast? = t.getLast?.or (some j) := by
      cases t <;> simp [List.getLast?_cons]
    rw [← ht]; exact hq2
  · refine hpc.append (List.isChain_cons.mp hqc).2 ?_
    intro x hx y hy
    rw [hp2, Option.mem_some_iff] at hx
    subst hx
    exact (List.isChain_cons.mp hqc).1 y hy

/-- Path-connectedness is symmetric for a complete family over a finite group. -/
lemma IndexPathConnected.symm_of_complete (hW : IsCompleteSimpleFamily W) {i j : Fin m}
    (hij : IndexPathConnected W i j) : IndexPathConnected W j i := by
  obtain ⟨p, hp1, hp2, hpc⟩ := hij
  refine ⟨p.reverse, ?_, ?_, ?_⟩
  · rw [List.head?_reverse]; exact hp2
  · rw [List.getLast?_reverse]; exact hp1
  · rw [List.isChain_reverse]
    refine hpc.imp ?_
    intro a b hab
    unfold auxiliaryIndexPredicate at hab ⊢
    rwa [tensorMultiplicity_comm W hW b a]

variable (W)

omit [Finite G] in

/-- A subgroup element with tautological character equal to two is the identity. -/
lemma eq_one_of_character_tautological_eq_two (g : G) (htr : (tautologicalFDRep G).character g = 2) : g = 1 := by
  classical
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA

  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).1
  have hstar : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hcol : ∀ i : Fin 2, ∑ k : Fin 2, Complex.normSq (A k i) = 1 := by
    intro i
    have hii : (star A * A) i i = 1 := by rw [hstar, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at hii
    have hterm : ∀ k : Fin 2, (star A) i k * A k i
        = ((Complex.normSq (A k i) : ℝ) : ℂ) := by
      intro k; rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Complex.ofReal_sum] at hii
    exact_mod_cast hii
  have hnormle : ∀ i : Fin 2, Complex.normSq (A i i) ≤ 1 := by
    intro i; rw [← hcol i]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (A k i))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

  have htr2 : A 0 0 + A 1 1 = 2 := by
    have hchar : (tautologicalFDRep G).character g = A 0 0 + A 1 1 := by
      rw [character_tautological_eq_trace, ← hA, Matrix.trace_fin_two]
    rw [← hchar, htr]

  have hre : ∀ i : Fin 2, (A i i).re ≤ 1 := by
    intro i
    have hns := Complex.normSq_apply (A i i)
    nlinarith [mul_self_nonneg (A i i).im, hnormle i, hns]
  have hre_sum : (A 0 0).re + (A 1 1).re = 2 := by
    have := congrArg Complex.re htr2
    simpa [Complex.add_re] using this
  have hre0 : (A 0 0).re = 1 := by linarith [hre 0, hre 1]
  have hre1 : (A 1 1).re = 1 := by linarith [hre 0, hre 1]

  have hdiag_one : ∀ i : Fin 2, (A i i).re = 1 → A i i = 1 := by
    intro i hrei
    have him : (A i i).im = 0 := by
      have hns := Complex.normSq_apply (A i i)
      nlinarith [hnormle i, hns, hrei, mul_self_nonneg (A i i).im]
    apply Complex.ext <;> simp [hrei, him]
  have hd0 : A 0 0 = 1 := hdiag_one 0 hre0
  have hd1 : A 1 1 = 1 := hdiag_one 1 hre1

  have hoff01 : A 0 1 = 0 := by
    have hs := hcol 1
    rw [Fin.sum_univ_two] at hs
    have h11 : Complex.normSq (A 1 1) = 1 := by rw [hd1]; simp
    have hz : Complex.normSq (A 0 1) = 0 := by
      rw [h11] at hs; linarith [Complex.normSq_nonneg (A 0 1)]
    exact Complex.normSq_eq_zero.mp hz
  have hoff10 : A 1 0 = 0 := by
    have hs := hcol 0
    rw [Fin.sum_univ_two] at hs
    have h00 : Complex.normSq (A 0 0) = 1 := by rw [hd0]; simp
    have hz : Complex.normSq (A 1 0) = 0 := by
      rw [h00] at hs; linarith [Complex.normSq_nonneg (A 1 0)]
    exact Complex.normSq_eq_zero.mp hz

  have hAexpand : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
    ext r c; fin_cases r <;> fin_cases c <;> rfl
  have hAone : A = 1 := by
    rw [hAexpand, hd0, hd1, hoff01, hoff10, ← Matrix.one_fin_two]
  have hval1 : (g.val : specialUnitaryGroup (Fin 2) ℂ) = 1 := by
    ext; rw [← hA, hAone]; rfl
  exact Subtype.ext hval1

/-- Any two indices in a complete simple family are joined by a path of positive multiplicities. -/
theorem exists_positiveMultiplicity_path (hW : IsCompleteSimpleFamily W) (i j : Fin m) :
    ∃ path : List (Fin m), path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        1 ≤ tensorMultiplicity W (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

  let occ : ℕ → Fin m → ℂ := fun n a =>
    ⅟(Fintype.card G : ℂ) * ∑ g : G, ((tautologicalFDRep G).character g) ^ n * (W a).character g⁻¹

  have hdimne : ∀ b : Fin m, Module.finrank ℂ (W b) ≠ 0 := by
    intro b h0
    haveI : Simple (W b) := hW.simple_entry b
    haveI : Subsingleton (W b : Type) := finrank_zero_iff.mp h0
    have hz : (𝟙 (W b) : W b ⟶ W b) = 0 :=
      Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => Subsingleton.elim _ _)))
    exact id_nonzero (W b) hz

  have hrec : ∀ n a, occ (n + 1) a = ∑ j, (tensorMultiplicity W a j : ℂ) * occ n j := by
    intro n a
    have hdecomp : ∀ h : G, (tautologicalFDRep G).character h * (W a).character h
        = ∑ j, (tensorMultiplicity W j a : ℂ) * (W j).character h := by
      intro h
      have hh := congrFun (character_eq_sum_simple_characters W hW (tautologicalFDRep G ⊗ W a)) h
      simp only [FDRep.char_tensor, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hh
      exact hh
    have hpg : ∀ g : G, ((tautologicalFDRep G).character g) ^ (n + 1) * (W a).character g⁻¹
        = ∑ j, (tensorMultiplicity W j a : ℂ) * (((tautologicalFDRep G).character g) ^ n * (W j).character g⁻¹) := by
      intro g
      have hgi := hdecomp g⁻¹
      rw [character_tautological_inv] at hgi
      rw [pow_succ, mul_assoc, hgi, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    change ⅟(Fintype.card G : ℂ) * ∑ g : G, ((tautologicalFDRep G).character g) ^ (n + 1) * (W a).character g⁻¹
        = ∑ j, (tensorMultiplicity W a j : ℂ) *
            (⅟(Fintype.card G : ℂ) * ∑ g : G, ((tautologicalFDRep G).character g) ^ n * (W j).character g⁻¹)
    rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => hpg g), Finset.sum_comm,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [tensorMultiplicity_comm W hW a j, ← Finset.mul_sum]
    ring

  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  have hchar1 : ∀ g : G, (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1 := by
    intro g; simp [FDRep.character, FDRep.of_ρ']
  haveI htrivsimple : Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
    rw [FDRep.simple_iff_char_is_norm_one]
    simp [hchar1, Nat.card_eq_fintype_card]
  obtain ⟨i₀, ⟨iso₀⟩⟩ := hW.exists_isomorphic_entry (FDRep.of (Representation.trivial ℂ G ℂ)) htrivsimple

  have hbase : ∀ a, occ 0 a ≠ 0 → a = i₀ := by
    intro a ha
    have hval : occ 0 a
        = (Module.finrank ℂ (W a ⟶ FDRep.of (Representation.trivial ℂ G ℂ)) : ℂ) := by
      have hsp := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom
        (FDRep.of (Representation.trivial ℂ G ℂ)) (W a)
      rw [smul_eq_mul] at hsp
      change ⅟(Fintype.card G : ℂ) * ∑ g : G, ((tautologicalFDRep G).character g) ^ 0 * (W a).character g⁻¹ = _
      rw [← hsp]
      congr 1
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [pow_zero, one_mul, hchar1 g, one_mul]
    rw [hval] at ha
    haveI : Simple (W a) := hW.simple_entry a
    have hfr : Module.finrank ℂ (W a ⟶ FDRep.of (Representation.trivial ℂ G ℂ)) ≠ 0 := by
      intro h0; rw [h0] at ha; simp at ha
    rw [FDRep.finrank_hom_simple_simple] at hfr
    by_contra hne
    have : ¬ Nonempty (W a ≅ FDRep.of (Representation.trivial ℂ G ℂ)) := by
      rintro ⟨e⟩
      exact hne (hW.eq_of_isomorphic a i₀ ⟨e ≪≫ iso₀⟩)
    rw [if_neg this] at hfr
    exact hfr rfl

  have hreach : ∀ n a, occ n a ≠ 0 → IndexPathConnected W i₀ a := by
    intro n
    induction n with
    | zero => intro a ha; rw [hbase a ha]; exact IndexPathConnected.refl i₀
    | succ n ih =>
      intro a ha
      rw [hrec n a] at ha
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      have hmj : tensorMultiplicity W a j ≠ 0 := by
        intro h0; rw [h0] at hj; simp at hj
      have hoccj : occ n j ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hj; exact hj rfl
      have hedge : (1 : ℕ) ≤ tensorMultiplicity W j a := by
        rw [tensorMultiplicity_comm W hW j a]; omega
      exact (ih j hoccj).trans (IndexPathConnected.of_positive_multiplicity hedge)

  have hseed : ∀ a, ∃ n, occ n a ≠ 0 := by
    intro a
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon

    have hsum : ∀ n, ∑ g : G, ((tautologicalFDRep G).character g) ^ n * (W a).character g⁻¹ = 0 := by
      intro n
      have h2 : ⅟(Fintype.card G : ℂ) *
          ∑ g : G, ((tautologicalFDRep G).character g) ^ n * (W a).character g⁻¹ = 0 := hcon n
      have h3 := congrArg (fun z => (Fintype.card G : ℂ) * z) h2
      simp only [mul_zero, ← mul_assoc, mul_invOf_self, one_mul] at h3
      exact h3

    have hpoly : ∀ p : Polynomial ℂ,
        ∑ g : G, p.eval ((tautologicalFDRep G).character g) * (W a).character g⁻¹ = 0 := by
      intro p
      simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hsum k, mul_zero]
    set d : ℂ := 2 with hd
    set S : Finset ℂ := (Finset.univ.image (fun g : G => (tautologicalFDRep G).character g)).erase d with hS
    set p : Polynomial ℂ := ∏ μ ∈ S, (Polynomial.X - Polynomial.C μ) with hp
    have hp_eval : ∀ x : ℂ, p.eval x = ∏ μ ∈ S, (x - μ) := by
      intro x
      rw [hp, Polynomial.eval_prod]
      exact Finset.prod_congr rfl fun μ _ => by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hpd_ne : p.eval d ≠ 0 := by
      rw [hp_eval]
      apply Finset.prod_ne_zero_iff.mpr
      intro μ hμ
      exact sub_ne_zero.mpr fun hc => (Finset.mem_erase.mp hμ).1 hc.symm
    have hval := hpoly p
    rw [Finset.sum_eq_single (1 : G)] at hval
    · rw [inv_one] at hval
      have hV1 : (tautologicalFDRep G).character 1 = 2 := by
        rw [character_tautological_eq_trace]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      rw [hV1, ← hd] at hval
      have hW1 : (W a).character 1 = (Module.finrank ℂ (W a) : ℂ) := FDRep.char_one _
      rw [hW1] at hval
      exact (mul_ne_zero hpd_ne (Nat.cast_ne_zero.mpr (hdimne a))) hval
    · intro b _ hb1
      have hbne : (tautologicalFDRep G).character b ≠ d := by
        rw [hd]; intro hc; exact hb1 (eq_one_of_character_tautological_eq_two b hc)
      have : (tautologicalFDRep G).character b ∈ S := by
        rw [hS]; exact Finset.mem_erase.mpr ⟨hbne, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
      rw [hp_eval]
      have : (∏ μ ∈ S, ((tautologicalFDRep G).character b - μ)) = 0 :=
        Finset.prod_eq_zero this (by rw [sub_self])
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ 1) h

  have hall : ∀ a, IndexPathConnected W i₀ a := fun a =>
    (hseed a).elim (fun n hn => hreach n a hn)
  obtain ⟨p, hp1, hp2, hpc⟩ :=
    (IndexPathConnected.symm_of_complete hW (hall i)).trans (hall j)
  refine ⟨p, hp1, hp2, fun k hk => ?_⟩
  have := (List.isChain_iff_getElem.mp hpc) k hk
  simpa [List.get_eq_getElem, auxiliaryIndexPredicate] using this

/-- The quadratic form of the auxiliary integer matrix is nonnegative on integral vectors. -/
theorem self_dot_mulVec_nonnegative (hW : IsCompleteSimpleFamily W) (hne : Nontrivial G)
    (x : Fin m → ℤ) :
    0 ≤ dotProduct x ((Matrix.of (auxiliaryQuadraticFormEntry W)).mulVec x) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

  set f : G → ℂ := fun g => ∑ i, (x i : ℂ) * (W i).character g with hf
  set Q : ℤ := dotProduct x ((Matrix.of (auxiliaryQuadraticFormEntry W)).mulVec x) with hQ
  set R : ℂ := ∑ g : G, (2 - (tautologicalFDRep G).character g) * (f g * f g⁻¹) with hR

  have key_ij : ∀ i j : Fin m,
      (∑ g : G, (2 - (tautologicalFDRep G).character g) * (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (auxiliaryQuadraticFormEntry W i j : ℂ) := by
    intro i j

    have orth : (∑ g : G, (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (if i = j then (1 : ℂ) else 0) := by
      haveI : Simple (W i) := hW.simple_entry i
      haveI : Simple (W j) := hW.simple_entry j
      have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (W i) (W j)
      rw [smul_eq_mul] at h
      have hval : (if Nonempty (W i ≅ W j) then (1 : ℂ) else 0)
          = (if i = j then (1 : ℂ) else 0) := by
        by_cases hij : i = j
        · rw [if_pos (⟨eqToIso (congrArg W hij)⟩ : Nonempty (W i ≅ W j)), if_pos hij]
        · rw [if_neg (fun hh => hij (hW.eq_of_isomorphic i j hh)), if_neg hij]
      rw [← hval, ← h, ← mul_assoc, mul_invOf_self, one_mul]

    have sca : (∑ g : G, (tautologicalFDRep G).character g * (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (tensorMultiplicity W j i : ℂ) := by
      have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (tautologicalFDRep G ⊗ W i) (W j)
      rw [smul_eq_mul] at h
      have hs : (∑ g : G, (tautologicalFDRep G ⊗ W i).character g * (W j).character g⁻¹)
          = ∑ g : G, (tautologicalFDRep G).character g * (W i).character g * (W j).character g⁻¹ := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [FDRep.char_tensor, Pi.mul_apply]
      rw [hs] at h
      simp only [tensorMultiplicity]
      rw [← h, ← mul_assoc, mul_invOf_self, one_mul]

    calc (∑ g : G, (2 - (tautologicalFDRep G).character g) * (W i).character g * (W j).character g⁻¹)
        = 2 * (∑ g : G, (W i).character g * (W j).character g⁻¹)
            - (∑ g : G, (tautologicalFDRep G).character g * (W i).character g * (W j).character g⁻¹) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun g _ => by ring)
      _ = 2 * ((Fintype.card G : ℂ) * (if i = j then (1 : ℂ) else 0))
            - (Fintype.card G : ℂ) * (tensorMultiplicity W j i : ℂ) := by rw [orth, sca]
      _ = (Fintype.card G : ℂ) * (auxiliaryQuadraticFormEntry W i j : ℂ) := by
          rw [tensorMultiplicity_comm W hW j i]
          simp only [auxiliaryQuadraticFormEntry]
          split_ifs with h <;> push_cast <;> ring

  have hQcast : (Q : ℂ) = ∑ i, ∑ j, (x i : ℂ) * (auxiliaryQuadraticFormEntry W i j : ℂ) * (x j : ℂ) := by
    rw [hQ]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hexp : R = ∑ i, ∑ j, (x i : ℂ) * (x j : ℂ) *
      (∑ g : G, (2 - (tautologicalFDRep G).character g) * (W i).character g * (W j).character g⁻¹) := by
    rw [hR]
    have hpg : ∀ g : G, (2 - (tautologicalFDRep G).character g) * (f g * f g⁻¹)
        = ∑ i, ∑ j, (x i : ℂ) * (x j : ℂ) *
            ((2 - (tautologicalFDRep G).character g) * (W i).character g * (W j).character g⁻¹) := by
      intro g
      simp only [hf]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun g _ => hpg g), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum]
  have hA_identity : R = (Fintype.card G : ℂ) * (Q : ℂ) := by
    rw [hexp, hQcast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [key_ij i j]
    ring

  set S₀ : ℝ := ∑ g : G, (2 - ((tautologicalFDRep G).character g).re) * Complex.normSq (f g) with hS0
  have hS0_nonneg : 0 ≤ S₀ := by
    rw [hS0]
    refine Finset.sum_nonneg (fun g _ => ?_)
    exact mul_nonneg (by linarith [character_tautological_re_le_two g]) (Complex.normSq_nonneg _)
  have hB : R = (S₀ : ℂ) := by
    rw [hR, hS0, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)

    have hfconj : f g⁻¹ = (starRingEnd ℂ) (f g) := by
      simp only [hf, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [RepresentationTheory.Group.CharacterOperations.character_inv_eq_conj (W i) g, map_mul, map_intCast]

    have hVreal : (2 : ℂ) - (tautologicalFDRep G).character g = ((2 - ((tautologicalFDRep G).character g).re : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, character_tautological_im_eq_zero g]
    rw [hfconj, Complex.mul_conj, hVreal, ← Complex.ofReal_mul]

  have hfinal : (Fintype.card G : ℂ) * (Q : ℂ) = (S₀ : ℂ) := by rw [← hA_identity, hB]
  have hreal : (Fintype.card G : ℝ) * (Q : ℝ) = S₀ := by exact_mod_cast hfinal
  have hcard_pos : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hQnonneg : 0 ≤ (Q : ℝ) := by nlinarith [hreal, hS0_nonneg, hcard_pos]
  exact_mod_cast hQnonneg

/-- The auxiliary integer matrix has a nonzero integral vector on which its quadratic form vanishes. -/
theorem exists_ne_zero_self_dot_mulVec_eq_zero (hW : IsCompleteSimpleFamily W) (hne : Nontrivial G) :
    ∃ x : Fin m → ℤ, x ≠ 0 ∧
      dotProduct x ((Matrix.of (auxiliaryQuadraticFormEntry W)).mulVec x) = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G

  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  haveI htrivsimple : Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.trivial ℂ G ℂ).asModule := by
      rw [isSimpleModule_iff]

      refine is_simple_module_of_finrank_eq_one (K := ℂ) (A := MonoidAlgebra ℂ G)
        (V := (Representation.trivial ℂ G ℂ).asModule) ?_
      rw [(Representation.trivial ℂ G ℂ).asModuleEquiv.finrank_eq, Module.finrank_self]
    infer_instance
  obtain ⟨i₀, ⟨iso₀⟩⟩ := hW.exists_isomorphic_entry (FDRep.of (Representation.trivial ℂ G ℂ)) htrivsimple

  have hfr : finrank ℂ (W i₀) = 1 := by
    have hc := congrFun (FDRep.char_iso iso₀) (1 : G)
    rw [FDRep.char_one, FDRep.char_one] at hc
    have htrivfr : finrank ℂ (FDRep.of (Representation.trivial ℂ G ℂ)) = 1 :=
      Module.finrank_self ℂ
    rw [htrivfr] at hc
    exact_mod_cast hc.symm
  refine ⟨fun j => (finrank ℂ (W j) : ℤ), ?_, ?_⟩
  ·
    intro hx
    have h0 : (finrank ℂ (W i₀) : ℤ) = 0 := by have := congrFun hx i₀; simpa using this
    rw [hfr] at h0
    norm_num at h0
  ·
    apply Finset.sum_eq_zero
    intro i _
    have hinner : (Matrix.of (auxiliaryQuadraticFormEntry W)).mulVec (fun j => (finrank ℂ (W j) : ℤ)) i = 0 := by
      simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
      exact weighted_auxiliaryRowSum_eq_zero_alternate W hW i
    rw [hinner, mul_zero]

omit [Finite G] in

/-- Every entry of a complete simple family has nonzero dimension. -/
lemma finrank_simple_entry_ne_zero (hW : IsCompleteSimpleFamily W) (b : Fin m) :
    finrank ℂ (W b) ≠ 0 := by
  intro h0
  haveI : Simple (W b) := hW.simple_entry b
  haveI : Subsingleton (W b : Type) := finrank_zero_iff.mp h0
  have hz : (𝟙 (W b) : W b ⟶ W b) = 0 :=
    Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => Subsingleton.elim _ _)))
  exact id_nonzero (W b) hz

/-- The multiplicity-weighted sum of simple dimensions is twice the dimension of the selected simple representation. -/
lemma sum_tensorMultiplicity_mul_finrank_eq_two_mul (hW : IsCompleteSimpleFamily W) (i : Fin m) :
    (∑ j, (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ)) = 2 * (finrank ℂ (W i) : ℤ) := by
  have h := weighted_auxiliaryRowSum_eq_zero_alternate W hW i
  have expand : ∀ j, auxiliaryQuadraticFormEntry W i j * (finrank ℂ (W j) : ℤ)
      = (if i = j then 2 * (finrank ℂ (W j) : ℤ) else 0)
        - (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    intro j; simp only [auxiliaryQuadraticFormEntry]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => expand j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => 2 * (finrank ℂ (W j) : ℤ)),
    if_pos (Finset.mem_univ i)] at h
  linarith

open RepresentationTheory.ComplexUnitCharacters in

/-- A cyclic finite subgroup admitting a complete simple family with at least three entries is nontrivial. -/
lemma nontrivial_of_isCyclic_of_three_le (hW : IsCompleteSimpleFamily W) (hcyc : IsCyclic G) (hm : 3 ≤ m) :
    Nontrivial G := by
  classical
  letI : CommGroup G := hcyc.commGroup
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  have hchar : ∀ j : Fin m, ∃ ξ : G →* ℂˣ, Nonempty (W j ≅ RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) := by
    intro j
    haveI := hW.simple_entry j
    exact RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter (W j)
  choose ξ hξ using hchar
  have hinj : Function.Injective ξ := by
    intro a b hab
    apply hW.eq_of_isomorphic a b
    obtain ⟨ea⟩ := hξ a
    obtain ⟨eb⟩ := hξ b
    exact ⟨ea ≪≫ eqToIso (congrArg RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter hab) ≪≫ eb.symm⟩
  have hle : m ≤ Nat.card G := by
    have h1 : Fintype.card (Fin m) ≤ Fintype.card (G →* ℂˣ) :=
      Fintype.card_le_of_injective ξ hinj
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card (α := G →* ℂˣ),
      RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq] at h1
    exact h1
  rw [← Finite.one_lt_card_iff_nontrivial]
  omega

/-- The tautological representation of a nontrivial finite subgroup has no nonzero invariant vectors. -/
lemma finrank_invariants_tautological_eq_zero (hne : Nontrivial G) :
    Module.finrank ℂ (Representation.invariants (tautologicalFDRep G).ρ) = 0 := by
  classical
  have hbot : Representation.invariants (tautologicalFDRep G).ρ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Representation.mem_invariants] at hv
    rw [Submodule.mem_bot]
    by_contra hv0
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    set A : Matrix (Fin 2) (Fin 2) ℂ :=
      ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA

    have hgv : A *ᵥ v = v := (Matrix.toLin'_apply A v).symm.trans (hv g)
    have hker : (A - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hgv, sub_self]
    have hdet0 : (A - 1).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
    have hdetA : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2
    have hsum : A 0 0 + A 1 1 = 2 := by
      rw [Matrix.det_fin_two] at hdetA
      rw [Matrix.det_fin_two] at hdet0
      simp only [Matrix.sub_apply, Matrix.one_apply, Fin.isValue,
        show ((0 : Fin 2) = 1) = False from by simp,
        show ((1 : Fin 2) = 0) = False from by simp, if_true, if_false,
        eq_self_iff_true] at hdet0
      linear_combination hdetA - hdet0
    have hχ2 : (tautologicalFDRep G).character g = 2 := by
      rw [character_tautological_eq_trace, ← hA, Matrix.trace_fin_two]; exact hsum
    exact hg (eq_one_of_character_tautological_eq_two g hχ2)
  rw [hbot]
  exact finrank_bot ℂ _

open RepresentationTheory.ComplexUnitCharacters in

/-- For a sufficiently large complete family over a cyclic group, the auxiliary integer pairing vanishes on the diagonal. -/
theorem auxiliaryIntegerPairing_self_eq_zero_of_isCyclic
    (hW : IsCompleteSimpleFamily W) (hcyc : IsCyclic G) (hm : 3 ≤ m) (i : Fin m) :
    auxiliaryIntegerPairing W i i = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  letI : CommGroup G := hcyc.commGroup
  haveI := hW.simple_entry i
  obtain ⟨ξ, ⟨e⟩⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter (W i)
  have hchar_eq : (W i).character = (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ).character := FDRep.char_iso e
  have hunit : ∀ g : G, (W i).character g * (W i).character g⁻¹ = 1 := by
    intro g
    rw [hchar_eq, RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, map_inv]
    exact Units.mul_inv (ξ g)
  have hmult : (tensorMultiplicity W i i : ℂ) = Module.finrank ℂ (Representation.invariants (tautologicalFDRep G).ρ) := by
    have hsp := FDRep.scalar_product_char_eq_finrank_equivariant (W i) (tautologicalFDRep G ⊗ W i)
    have havg := FDRep.average_char_eq_finrank_invariants (tautologicalFDRep G)
    have key : (Module.finrank ℂ (W i ⟶ tautologicalFDRep G ⊗ W i) : ℂ)
        = Module.finrank ℂ (Representation.invariants (tautologicalFDRep G).ρ) := by
      rw [← hsp, ← havg]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      rw [FDRep.char_tensor, Pi.mul_apply, mul_assoc, hunit g, mul_one]
    simpa only [tensorMultiplicity] using key
  rw [finrank_invariants_tautological_eq_zero (nontrivial_of_isCyclic_of_three_le W hW hcyc hm)] at hmult
  have hmz : tensorMultiplicity W i i = 0 := by exact_mod_cast hmult
  simp [auxiliaryIntegerPairing, hmz]

/-- The negative identity element of the two-dimensional complex special unitary group. -/
def negIdentity : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨by
      rw [Matrix.mem_unitaryGroup_iff']
      simp,
     by
      rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
      norm_num⟩⟩

/-- An auxiliary theorem. -/
@[simp] lemma auxiliaryTheoremTwo :
    ((negIdentity : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- The negative identity commutes with every element of the two-dimensional special unitary group. -/
lemma negIdentity_mul_comm (A : specialUnitaryGroup (Fin 2) ℂ) : negIdentity * A = A * negIdentity := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, auxiliaryTheoremTwo, neg_one_mul, mul_neg_one]

omit [Finite G] in

/-- An element whose underlying matrix is the negative identity acts by negation in the tautological representation. -/
lemma tautologicalRepresentation_apply_eq_neg (z : G)
    (hz : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdentity) (v : Fin 2 → ℂ) :
    (tautologicalRepresentation G) z v = -v := by
  have hmat : ((z.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rw [hz, auxiliaryTheoremTwo]
  simp only [tautologicalRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, hmat]
  rw [Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec]

omit [Finite G] in

/-- An auxiliary theorem. -/
lemma auxiliaryTheoremOne (z : G)
    (hz : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdentity) :
    (tautologicalFDRep G).character z = -2 := by
  rw [character_tautological_eq_trace, hz, auxiliaryTheoremTwo, Matrix.trace_fin_two]
  simp only [Matrix.neg_apply, Matrix.one_apply_eq]
  norm_num

open Matrix in

/-- A nonidentity element of square one in the two-dimensional special unitary group is the negative identity. -/
lemma eq_negIdentity_of_sq_eq_one {g : specialUnitaryGroup (Fin 2) ℂ}
    (hsq : g ^ 2 = 1) (hne : g ≠ 1) : g = negIdentity := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hAdef
  have hdet : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2

  have hAA : A * A = 1 := by
    have h1 : ((g ^ 2 : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [hsq]; rfl
    rw [pow_two, Submonoid.coe_mul] at h1
    exact h1

  have hCH : A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul] <;> ring

  have hT : A.trace • A = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h := hCH
    rw [hAA, hdet, one_smul] at h

    linear_combination (norm := module) -h

  have hdisc : A.trace ^ 2 = 4 := by
    have hd := congrArg Matrix.det hT
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hdet, Matrix.det_one] at hd
    linear_combination hd

  have hpm : A.trace = 2 ∨ A.trace = -2 := by
    have hfac : (A.trace - 2) * (A.trace + 2) = 0 := by linear_combination hdisc
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)

  have hAeq : A = -1 := by
    rcases hpm with h2 | h2
    ·
      rw [h2] at hT
      have hA1 : A = 1 := (smul_right_inj (two_ne_zero)).mp hT
      exact absurd (Subtype.ext (show (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 by
        rw [← hAdef, hA1])) hne
    ·
      rw [h2] at hT
      have hne2 : (-2 : ℂ) ≠ 0 := by norm_num
      have hgoal : (-2 : ℂ) • A = (-2 : ℂ) • (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [hT]; module
      exact (smul_right_inj hne2).mp hgoal
  exact Subtype.ext (by rw [← hAdef, hAeq, auxiliaryTheoremTwo])

/-- A finite subgroup of even cardinality contains the negative identity. -/
lemma negIdentity_mem_of_even_card {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
    (hev : Even (Nat.card G)) : negIdentity ∈ G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card G := hev.two_dvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hdvd

  have hxsq : x ^ 2 = 1 := by have h := pow_orderOf_eq_one x; rwa [hx] at h
  have hxne : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; norm_num at hx

  have hvalsq : (x : specialUnitaryGroup (Fin 2) ℂ) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hxsq, Subgroup.coe_one]
  have hvalne : (x : specialUnitaryGroup (Fin 2) ℂ) ≠ 1 := by
    intro h; exact hxne (Subtype.ext h)
  have hxval : (x : specialUnitaryGroup (Fin 2) ℂ) = negIdentity :=
    eq_negIdentity_of_sq_eq_one hvalsq hvalne
  rw [← hxval]
  exact x.property

private lemma exists_eigen_character_of_not_simple
    {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G] (hns : ¬ Simple (tautologicalFDRep G)) :
    ∃ χ : G →* ℂˣ, ∀ g : G, (tautologicalFDRep G).character g = (χ g : ℂ) + ((χ g : ℂ))⁻¹ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  have hnsm : ¬ IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule (tautologicalRepresentation G)) := by
    intro h
    exact hns (by haveI := h; exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (tautologicalRepresentation G))

  have hnt : Nontrivial (Representation.asModule (tautologicalRepresentation G)) := by
    let e := Representation.asModuleEquiv (tautologicalRepresentation G)
    refine ⟨e.symm 0, e.symm 1, fun h => ?_⟩
    exact zero_ne_one (e.symm.injective h)
  obtain ⟨N, hNb, hNt⟩ :
      ∃ N : Submodule (MonoidAlgebra ℂ G) (Representation.asModule (tautologicalRepresentation G)),
        N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial (Representation.asModule (tautologicalRepresentation G)) := hnt
    exact hnsm { eq_bot_or_eq_top := fun N => (em (N = ⊥)).imp id (hcon N) }

  set S : Subrepresentation (tautologicalRepresentation G) := Subrepresentation.ofSubmodule' N with hS
  set P : Submodule ℂ (Fin 2 → ℂ) := S.toSubmodule with hP
  have hPbot : P ≠ ⊥ := by
    obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNb
    intro hbot
    have hwP : w ∈ P := (Subrepresentation.mem_ofSubmodule'_iff).mpr hwN
    rw [hbot] at hwP

    exact hw0 ((Submodule.mem_bot ℂ).mp hwP)
  obtain ⟨v₀, hv0P, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
  have hPtop : P ≠ ⊤ := by
    intro htop
    apply hNt
    rw [eq_top_iff]
    intro u _

    have huP : u ∈ P := by rw [htop]; exact Submodule.mem_top (R := ℂ) (M := Fin 2 → ℂ)

    exact huP

  have hspanle : Submodule.span ℂ {v₀} ≤ P := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv0P
  have hfr2 : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hfrspan : Module.finrank ℂ (Submodule.span ℂ {v₀}) = 1 := finrank_span_singleton hv0
  have hfrP_lt : Module.finrank ℂ P < 2 := by
    have h := Submodule.finrank_lt hPtop
    rwa [hfr2] at h
  have hPspan : Submodule.span ℂ {v₀} = P :=
    Submodule.eq_of_le_of_finrank_le hspanle (by rw [hfrspan]; omega)

  have heig : ∀ g : G, ∃ c : ℂ, (tautologicalRepresentation G) g v₀ = c • v₀ := by
    intro g
    have hmem : (tautologicalRepresentation G) g v₀ ∈ P := S.apply_mem_toSubmodule g hv0P
    rw [← hPspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩

  have hscal : ∀ a b : ℂ, a • v₀ = b • v₀ → a = b := by
    intro a b hab
    have hz : (a - b) • v₀ = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  set cf : G → ℂ := fun g => (heig g).choose with hcfdef
  have hcf : ∀ g, (tautologicalRepresentation G) g v₀ = cf g • v₀ := fun g => (heig g).choose_spec
  have hcf1 : cf 1 = 1 := by
    have h := hcf 1
    rw [map_one, Module.End.one_apply] at h
    exact (hscal 1 (cf 1) (by rw [one_smul]; exact h)).symm
  have hcfmul : ∀ g h : G, cf (g * h) = cf g * cf h := by
    intro g h
    have e2 : (tautologicalRepresentation G) (g * h) v₀ = (cf g * cf h) • v₀ := by
      rw [map_mul, Module.End.mul_apply, hcf h, map_smul, hcf g, smul_smul, mul_comm]
    exact hscal _ _ ((hcf (g * h)).symm.trans e2)
  have hcfne : ∀ g : G, cf g ≠ 0 := by
    intro g hg0
    have h1 : cf g * cf g⁻¹ = cf 1 := by rw [← hcfmul, mul_inv_cancel]
    rw [hg0, zero_mul, hcf1] at h1
    exact one_ne_zero h1.symm
  let χ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 (cf g) (hcfne g)
      map_one' := Units.ext (by simp [hcf1])
      map_mul' := fun g h => Units.ext (by simp [hcfmul g h]) }
  refine ⟨χ, fun g => ?_⟩

  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  have hgv : A *ᵥ v₀ = cf g • v₀ := by
    have h := hcf g
    rw [show (tautologicalRepresentation G) g = Matrix.toLin' A from rfl, Matrix.toLin'_apply] at h
    exact h
  have hker : (A - cf g • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v₀ = 0 := by
    rw [Matrix.sub_mulVec, hgv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdet0 : (A - cf g • 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v₀, hv0, hker⟩
  have hdetA : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2
  rw [Matrix.det_fin_two] at hdet0 hdetA
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue,
    show ((0 : Fin 2) = 1) = False from by simp,
    show ((1 : Fin 2) = 0) = False from by simp, if_true, if_false, smul_eq_mul, mul_one,
    mul_zero, sub_zero] at hdet0
  have key : cf g * (A 0 0 + A 1 1) = cf g * cf g + 1 := by linear_combination hdetA - hdet0
  have hchar : (tautologicalFDRep G).character g = A 0 0 + A 1 1 := by
    rw [character_tautological_eq_trace, hA, Matrix.trace_fin_two]
  have hcval : ((χ g : ℂˣ) : ℂ) = cf g := rfl
  rw [hchar, hcval]
  have hcne : cf g ≠ 0 := hcfne g
  field_simp
  linear_combination key

/-- A finite subgroup of odd cardinality is cyclic. -/
lemma isCyclic_of_odd_card {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
    (hodd : Odd (Nat.card G)) : IsCyclic G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  have hns : ¬ Simple (tautologicalFDRep G) := by
    intro hS
    haveI := hS
    have hdvd : Module.finrank ℂ (tautologicalFDRep G) ∣ Fintype.card G := RepresentationTheory.FiniteGroupCharacterIntegrality.finrank_dvd_card (tautologicalFDRep G)
    have hfr : Module.finrank ℂ (tautologicalFDRep G) = 2 := by
      have h1 : (Module.finrank ℂ (tautologicalFDRep G) : ℂ) = 2 := by
        rw [← FDRep.char_one (tautologicalFDRep G), character_tautological_eq_trace]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      exact_mod_cast h1
    rw [hfr] at hdvd
    rw [Nat.card_eq_fintype_card] at hodd
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨t, ht⟩ := hodd
    omega

  obtain ⟨χ, hχ⟩ := exists_eigen_character_of_not_simple hns
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h2 : (tautologicalFDRep G).character g = 2 := by
      rw [hχ g, hg]; simp only [Units.val_one, inv_one]; norm_num
    exact eq_one_of_character_tautological_eq_two g h2

  exact isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp χ)
    (Units.val_injective.comp hinj)

/-- A finite subgroup is cyclic or contains the negative identity. -/
theorem isCyclic_or_negIdentity_mem
    (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite G] :
    IsCyclic G ∨ (negIdentity ∈ G) := by
  rcases Nat.even_or_odd (Nat.card G) with hev | hodd
  · exact Or.inr (negIdentity_mem_of_even_card hev)
  · exact Or.inl (isCyclic_of_odd_card hodd)

private lemma finrank_pos_of_simple (S : FDRep ℂ G) [Simple S] : 0 < Module.finrank ℂ S := by
  by_contra h
  push Not at h
  have h0 : Module.finrank ℂ S = 0 := Nat.le_zero.mp h
  have hsub : Subsingleton S := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (S ⟶ S) := by
    refine ⟨fun f g => ?_⟩
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have e1 : Module.finrank ℂ (S ⟶ S) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
  have e0 : Module.finrank ℂ (S ⟶ S) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- An endomorphism commuting with a simple representation is a scalar multiple of the identity. -/
lemma equivariant_endomorphism_eq_smul_id (S : FDRep ℂ G) [Simple S]
    (T : S →ₗ[ℂ] S) (hT : ∀ g : G, T ∘ₗ S.ρ g = S.ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

  have hmemT : T ∈ (Representation.linHom S.ρ S.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply, hT g⁻¹, ← LinearMap.comp_assoc,
      show S.ρ g ∘ₗ S.ρ g⁻¹ = LinearMap.id by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id],
      LinearMap.id_comp]

  have h1dim : Module.finrank ℂ (Representation.linHom S.ρ S.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom S S)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ S

  have hid_mem : (LinearMap.id : S →ₗ[ℂ] S) ∈ (Representation.linHom S.ρ S.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (S.ρ g * S.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hdim_ne : (Module.finrank ℂ S : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_simple S).ne'
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom S.ρ S.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank ℂ S : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := S), h, map_zero]
    exact hdim_ne this
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom S.ρ S.ρ).invariants) hid_ne).mp h1dim)
    ⟨T, hmemT⟩
  refine ⟨c, ?_⟩
  have := congr_arg Subtype.val hc
  simpa using this.symm

/-- A central element of square one acts on a simple representation by a scalar sign. -/
lemma central_involution_acts_by_sign (z : G) (hz : ∀ h : G, z * h = h * z) (hz2 : z ^ 2 = 1)
    (S : FDRep ℂ G) [Simple S] :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ v, S.ρ z v = ε • v := by

  have hcomm : ∀ g : G, (S.ρ z) ∘ₗ S.ρ g = S.ρ g ∘ₗ (S.ρ z) := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, hz g]
  obtain ⟨c, hc⟩ := equivariant_endomorphism_eq_smul_id S (S.ρ z) hcomm
  refine ⟨c, ?_, ?_⟩
  ·
    have happ : ∀ v : S, (c * c) • v = v := by
      intro v
      have hzz : (S.ρ (z * z)) v = v := by rw [← pow_two, hz2, map_one, Module.End.one_apply]
      rw [map_mul, Module.End.mul_apply] at hzz
      have e : (S.ρ z) v = c • v := by rw [hc]; simp
      rw [e, map_smul, e, smul_smul] at hzz
      exact hzz
    have hcc : (c * c) • (LinearMap.id : S →ₗ[ℂ] S) = LinearMap.id := by
      ext v; simp only [LinearMap.smul_apply, LinearMap.id_apply]; exact happ v
    have hfin : (Module.finrank ℂ S : ℂ) ≠ 0 := by
      exact_mod_cast (finrank_pos_of_simple S).ne'
    have htr : (c * c) * (Module.finrank ℂ S : ℂ) = (Module.finrank ℂ S : ℂ) := by
      have h := congrArg (LinearMap.trace ℂ S) hcc
      rwa [map_smul, LinearMap.trace_id, smul_eq_mul] at h
    have hcc1 : c * c = 1 := mul_right_cancel₀ hfin (by rw [htr, one_mul])
    rw [pow_two]; exact hcc1
  · intro v; rw [hc]; simp only [LinearMap.smul_apply, LinearMap.id_apply]

/-- A central element acting by negation on the tautological representation forces the auxiliary pairing to vanish on the diagonal. -/
lemma auxiliaryIntegerPairing_self_eq_zero_of_central_negation (hW : IsCompleteSimpleFamily W)
    (z : G) (hz_central : ∀ h : G, z * h = h * z)
    (hzV : ∀ v, (tautologicalFDRep G).ρ z v = -v) (i : Fin m) :
    auxiliaryIntegerPairing W i i = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hcard
  haveI := hW.simple_entry i

  have hrho : (tautologicalFDRep G).ρ (z ^ 2) = LinearMap.id := by
    ext v
    rw [pow_two, map_mul, Module.End.mul_apply, hzV, hzV, neg_neg, LinearMap.id_apply]
  have hfr : (Module.finrank ℂ (tautologicalFDRep G) : ℂ) = 2 := by
    rw [← FDRep.char_one (tautologicalFDRep G), character_tautological_eq_trace]
    have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
    rw [hone, Matrix.trace_one]; simp
  have hz2 : z ^ 2 = 1 := by
    apply eq_one_of_character_tautological_eq_two
    rw [FDRep.character, hrho, LinearMap.trace_id, hfr]
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz

  obtain ⟨ε, hε2, hεW⟩ := central_involution_acts_by_sign z hz_central hz2 (W i)
  have hεε : ε * ε = 1 := by rw [← pow_two]; exact hε2

  have hVchar : ∀ g : G, (tautologicalFDRep G).character (z * g) = - (tautologicalFDRep G).character g := by
    intro g
    have hmul : (tautologicalFDRep G).ρ (z * g) = -(tautologicalFDRep G).ρ g := by
      ext v; simp only [map_mul, Module.End.mul_apply, LinearMap.neg_apply, hzV]
    rw [FDRep.character, FDRep.character, hmul, map_neg]
  have hWchar : ∀ g : G, (W i).character (z * g) = ε * (W i).character g := by
    intro g
    have hmul : (W i).ρ (z * g) = ε • (W i).ρ g := by
      ext v
      simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, hεW]
    rw [FDRep.character, FDRep.character, hmul, map_smul, smul_eq_mul]
  have hWchar_inv : ∀ g : G, (W i).character (z * g)⁻¹ = ε * (W i).character g⁻¹ := by
    intro g
    rw [_root_.mul_inv_rev, hzinv]
    have hmul : (W i).ρ (g⁻¹ * z) = ε • (W i).ρ g⁻¹ := by
      ext v
      simp only [map_mul, Module.End.mul_apply, hεW, LinearMap.map_smul, LinearMap.smul_apply]
    rw [FDRep.character, FDRep.character, hmul, map_smul, smul_eq_mul]

  set f : G → ℂ := fun g => (tautologicalFDRep G).character g * (W i).character g * (W i).character g⁻¹ with hf
  have hmultC : (tensorMultiplicity W i i : ℂ) = ⅟(Fintype.card G : ℂ) • ∑ g : G, f g := by
    have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (tautologicalFDRep G ⊗ W i) (W i)
    simp only [tensorMultiplicity]
    rw [← h]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    simp only [FDRep.char_tensor, Pi.mul_apply, hf, mul_assoc]

  have hkey : ∀ g : G, f (z * g) = - f g := by
    intro g
    simp only [hf]
    rw [hVchar, hWchar, hWchar_inv]
    linear_combination
      (-((tautologicalFDRep G).character g * (W i).character g * (W i).character g⁻¹)) * hεε
  have h1 : ∑ g : G, f (z * g) = ∑ g : G, f g := by
    have := Equiv.sum_comp (Equiv.mulLeft z) f
    simpa only [Equiv.coe_mulLeft] using this
  have h2b : ∑ g : G, f (z * g) = - ∑ g : G, f g := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun g _ => hkey g)
  have hSum : ∑ g : G, f g = - ∑ g : G, f g := h1.symm.trans h2b
  have hz0 : ∑ g : G, f g = 0 := by
    have key : ∑ g : G, f g + ∑ g : G, f g = 0 := by nth_rewrite 2 [hSum]; ring
    have h2 : (2 : ℂ) * ∑ g : G, f g = 0 := by rw [two_mul]; exact key
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hmult0 : (tensorMultiplicity W i i : ℂ) = 0 := by rw [hmultC, hz0, smul_zero]
  have hmultN : tensorMultiplicity W i i = 0 := by exact_mod_cast hmult0
  simp only [auxiliaryIntegerPairing, hmultN, Nat.cast_zero]

/-- The auxiliary integer pairing vanishes on equal indices under the stated size and nontriviality assumptions. -/
lemma auxiliaryIntegerPairing_self_eq_zero_of_nontrivial (hW : IsCompleteSimpleFamily W) (hm : 3 ≤ m) (hne : Nontrivial G)
    (i : Fin m) : auxiliaryIntegerPairing W i i = 0 := by

  rcases isCyclic_or_negIdentity_mem G with hcyc | hneg
  ·
    exact auxiliaryIntegerPairing_self_eq_zero_of_isCyclic W hW hcyc hm i
  ·
    set z : G := ⟨negIdentity, hneg⟩ with hz
    have hz_central : ∀ h : G, z * h = h * z := by
      intro h
      exact Subtype.ext (negIdentity_mul_comm h.val)
    have hzval : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdentity := rfl
    have hzV : ∀ v, (tautologicalFDRep G).ρ z v = -v := by
      intro v

      exact tautologicalRepresentation_apply_eq_neg z hzval v
    exact auxiliaryIntegerPairing_self_eq_zero_of_central_negation W hW z hz_central hzV i

/-- The multiplicity between distinct entries of a sufficiently large complete family is at most one. -/
lemma tensorMultiplicity_le_one_of_ne (hW : IsCompleteSimpleFamily W) (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    tensorMultiplicity W i j ≤ 1 := by
  classical
  have hd : ∀ k, (1 : ℤ) ≤ (finrank ℂ (W k) : ℤ) := fun k => by
    have h := finrank_simple_entry_ne_zero W hW k; omega
  have hterm_nonneg : ∀ (a : Fin m) (k : Fin m),
      (0 : ℤ) ≤ (tensorMultiplicity W a k : ℤ) * (finrank ℂ (W k) : ℤ) :=
    fun a k => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

  have step1 : (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ) ≤ 2 * (finrank ℂ (W i) : ℤ) := by
    rw [← sum_tensorMultiplicity_mul_finrank_eq_two_mul W hW i]
    exact Finset.single_le_sum (fun k _ => hterm_nonneg i k) (Finset.mem_univ j)
  have step2 : (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W i) : ℤ) ≤ 2 * (finrank ℂ (W j) : ℤ) := by
    have h := Finset.single_le_sum (f := fun k => (tensorMultiplicity W j k : ℤ) * (finrank ℂ (W k) : ℤ))
      (fun k _ => hterm_nonneg j k) (Finset.mem_univ i)
    rw [sum_tensorMultiplicity_mul_finrank_eq_two_mul W hW j] at h
    rwa [tensorMultiplicity_comm W hW j i] at h

  have isolate : ∀ (a b : Fin m),
      (tensorMultiplicity W a b : ℤ) * (finrank ℂ (W b) : ℤ) = 2 * (finrank ℂ (W a) : ℤ) →
      ∀ k, k ≠ b → tensorMultiplicity W a k = 0 := by
    intro a b hab k hk
    by_contra hne0
    have hdk : (0 : ℤ) < (finrank ℂ (W k) : ℤ) := by have := hd k; linarith
    have hpos : 0 < (tensorMultiplicity W a k : ℤ) * (finrank ℂ (W k) : ℤ) :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hne0) hdk
    have hsub : (∑ l ∈ ({b, k} : Finset (Fin m)), (tensorMultiplicity W a l : ℤ) * (finrank ℂ (W l) : ℤ))
        ≤ ∑ l, (tensorMultiplicity W a l : ℤ) * (finrank ℂ (W l) : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => hterm_nonneg a l)
    rw [Finset.sum_pair (Ne.symm hk), sum_tensorMultiplicity_mul_finrank_eq_two_mul W hW a, hab] at hsub
    linarith

  by_contra hcon
  push Not at hcon
  have hR2 : (2 : ℤ) ≤ (tensorMultiplicity W i j : ℤ) := by
    have : 2 ≤ tensorMultiplicity W i j := hcon; exact_mod_cast this
  have hprod1 : (0 : ℤ) ≤ ((tensorMultiplicity W i j : ℤ) - 2) * (finrank ℂ (W j) : ℤ) :=
    mul_nonneg (by linarith) (by linarith [hd j])
  have hprod2 : (0 : ℤ) ≤ ((tensorMultiplicity W i j : ℤ) - 2) * (finrank ℂ (W i) : ℤ) :=
    mul_nonneg (by linarith) (by linarith [hd i])
  have hdle1 : (finrank ℂ (W j) : ℤ) ≤ (finrank ℂ (W i) : ℤ) := by nlinarith [step1, hprod1]
  have hdle2 : (finrank ℂ (W i) : ℤ) ≤ (finrank ℂ (W j) : ℤ) := by nlinarith [step2, hprod2]
  have hdeq : (finrank ℂ (W i) : ℤ) = (finrank ℂ (W j) : ℤ) := le_antisymm hdle2 hdle1
  have hfj_ge : 2 * (finrank ℂ (W i) : ℤ) ≤ (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    nlinarith [hprod1, hdeq]
  have hfj : (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W j) : ℤ) = 2 * (finrank ℂ (W i) : ℤ) :=
    le_antisymm step1 hfj_ge
  have hfj2_ge : 2 * (finrank ℂ (W j) : ℤ) ≤ (tensorMultiplicity W i j : ℤ) * (finrank ℂ (W i) : ℤ) := by
    nlinarith [hprod2, hdeq]
  have hfj2 : (tensorMultiplicity W j i : ℤ) * (finrank ℂ (W i) : ℤ) = 2 * (finrank ℂ (W j) : ℤ) := by
    rw [tensorMultiplicity_comm W hW j i]; exact le_antisymm step2 hfj2_ge
  have hzi : ∀ k, k ≠ j → tensorMultiplicity W i k = 0 := isolate i j hfj
  have hzj : ∀ k, k ≠ i → tensorMultiplicity W j k = 0 := isolate j i hfj2

  obtain ⟨l, hl⟩ : ∃ l : Fin m, l ∉ ({i, j} : Finset (Fin m)) := by
    by_contra hc
    push Not at hc
    have hsubuniv : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun l _ => hc l
    have h1 := Finset.card_le_card hsubuniv
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl

  have allmem : ∀ (q : List (Fin m)), q.IsChain (auxiliaryIndexPredicate W) →
      ∀ a, q.head? = some a → (a = i ∨ a = j) → ∀ y ∈ q, y = i ∨ y = j := by
    intro q
    induction q with
    | nil => intro _ a ha _ _ _; simp at ha
    | cons c t ih =>
      intro hchain a ha hab y hy
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst c
      rcases List.mem_cons.mp hy with rfl | hyt
      · exact hab
      · cases t with
        | nil => simp at hyt
        | cons b t' =>
          have hchain' := List.isChain_cons.mp hchain
          have hadj : auxiliaryIndexPredicate W a b := hchain'.1 b (by simp)
          have hb : b = i ∨ b = j := by
            rcases hab with rfl | rfl
            · by_contra hbc
              push Not at hbc
              have h0 := hzi b hbc.2
              unfold auxiliaryIndexPredicate at hadj; omega
            · by_contra hbc
              push Not at hbc
              have h0 := hzj b hbc.1
              unfold auxiliaryIndexPredicate at hadj; omega
          exact ih hchain'.2 b (by simp) hb y hyt

  obtain ⟨p, hp1, hp2, hpc⟩ := exists_positiveMultiplicity_path W hW i l
  have hchainp : p.IsChain (auxiliaryIndexPredicate W) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    simpa [List.get_eq_getElem, auxiliaryIndexPredicate] using hpc k hk
  have hlmem : l ∈ p := List.mem_of_getLast? hp2
  rcases allmem p hchainp i hp1 (Or.inl rfl) l hlmem with h | h
  · exact hl.1 h
  · exact hl.2 h

/-- All pairwise multiplicities are at most one for a sufficiently large complete family over a nontrivial finite subgroup. -/
lemma tensorMultiplicity_le_one_of_nontrivial (hW : IsCompleteSimpleFamily W) (hm : 3 ≤ m) (hne : Nontrivial G) (i j : Fin m) :
    tensorMultiplicity W i j ≤ 1 := by
  by_cases h : i = j
  · subst h
    have h0 := auxiliaryIntegerPairing_self_eq_zero_of_nontrivial W hW hm hne i
    simp only [auxiliaryIntegerPairing] at h0
    omega
  · exact tensorMultiplicity_le_one_of_ne W hW hm h

/-- An auxiliary classification property holds for the integer pairing under the stated finiteness, size, and nontriviality hypotheses. -/
@[source_ref "Chapter6/Problem6.1.6" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived4" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived5" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived7" (role := supporting)]
theorem auxiliaryPairingClassification (hW : IsCompleteSimpleFamily W) (hm : 3 ≤ m)
    (hne : Nontrivial G) :
    RepresentationTheory.DynkinDiagram.AffineClassification.IsAffineDynkinMatrix m (auxiliaryIntegerPairing W) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold Matrix.IsSymm
    ext i j
    simp only [Matrix.transpose_apply, auxiliaryIntegerPairing]
    rw [tensorMultiplicity_comm W hW j i]
  ·
    intro i
    exact auxiliaryIntegerPairing_self_eq_zero_of_nontrivial W hW hm hne i
  ·
    intro i j
    simp only [auxiliaryIntegerPairing]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (tensorMultiplicity_le_one_of_nontrivial W hW hm hne i j) with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  ·
    intro i j
    obtain ⟨p, hp1, hp2, hpc⟩ := exists_positiveMultiplicity_path W hW i j
    refine ⟨p, hp1, hp2, fun k hk => ?_⟩
    simp only [auxiliaryIntegerPairing]
    exact_mod_cast le_antisymm (tensorMultiplicity_le_one_of_nontrivial W hW hm hne _ _) (hpc k hk)
  ·
    intro x
    convert self_dot_mulVec_nonnegative W hW hne x using 3
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      auxiliaryQuadraticFormEntry, auxiliaryIntegerPairing]
    split_ifs <;> simp
  ·
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_self_dot_mulVec_eq_zero W hW hne
    refine ⟨x, hx0, ?_⟩
    convert hx using 3
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      auxiliaryQuadraticFormEntry, auxiliaryIntegerPairing]
    split_ifs <;> simp

/-- Each row of the auxiliary integer matrix has dimension-weighted sum zero. -/
@[source_ref "Chapter6/Problem6.1.6" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived4" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived5" (role := supporting),
  source_ref "Chapter6/Problem6.1.6/Derived7" (role := supporting)]
theorem weighted_auxiliaryRowSum_eq_zero (hW : IsCompleteSimpleFamily W) (i : Fin m) :
    (∑ j, auxiliaryQuadraticFormEntry W i j * (finrank ℂ (W j) : ℤ)) = 0 :=
  weighted_auxiliaryRowSum_eq_zero_alternate W hW i

end RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012911 := _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.auxiliaryTheoremOne

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012934 := _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.exists_positiveMultiplicity_path

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012959 := _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.auxiliaryTheoremTwo

attribute [source_ref "Chapter6/Problem6.1.6" (role := primary)] _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012934

attribute [source_ref "Chapter6/Problem6.1.6/Derived4" (role := supporting)] _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012934

attribute [source_ref "Chapter6/Problem6.1.6/Derived5" (role := supporting)] _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012934

attribute [source_ref "Chapter6/Problem6.1.6/Derived7" (role := supporting)] _root_.RepresentationTheory.SpecialUnitaryGroup.FiniteSubgroupRepresentationTheory.Auxiliary.statement012934
