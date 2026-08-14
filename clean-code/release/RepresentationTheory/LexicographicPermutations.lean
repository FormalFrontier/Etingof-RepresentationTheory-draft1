/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.LexicographicPermutations

open RepresentationTheory.PermutationPolynomialAuxiliary
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

variable {N : ℕ}

/-- A nonidentity permutation makes a strictly antitone function lexicographically smaller. -/
theorem StrictAnti.comp_perm_lt_of_ne {f : Fin N → ℤ} (hf : StrictAnti f)
    {σ : Equiv.Perm (Fin N)} (hσ : σ ≠ 1) :
    toLex (f ∘ σ) < toLex f := by
  classical
  have hex : ∃ i, σ i ≠ i := by
    by_contra h
    exact hσ (Equiv.ext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  obtain ⟨w, hw⟩ := hex
  have hne : (Finset.univ.filter fun i => σ i ≠ i).Nonempty :=
    ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩⟩
  set i₀ := (Finset.univ.filter fun i => σ i ≠ i).min' hne with hi0
  have hi0mem := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  have hmove : σ i₀ ≠ i₀ := hi0mem.2
  have hfix : ∀ j, j < i₀ → σ j = j := by
    intro j hj
    by_contra hjm
    exact absurd
      (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hjm⟩))
      (not_le.2 hj)
  have hgt : i₀ < σ i₀ := by
    rcases lt_trichotomy (σ i₀) i₀ with h | h | h
    · exact absurd (σ.injective (hfix (σ i₀) h)) hmove
    · exact absurd h hmove
    · exact h
  refine ⟨i₀, ?_, ?_⟩
  · intro j hj
    change f (σ j) = f j
    rw [hfix j hj]
  · change f (σ i₀) < f i₀
    exact hf hgt

/-- Permuting a strictly antitone function is lexicographically bounded by that function. -/
theorem StrictAnti.comp_perm_le {f : Fin N → ℤ} (hf : StrictAnti f)
    (σ : Equiv.Perm (Fin N)) : toLex (f ∘ σ) ≤ toLex f := by
  rcases eq_or_ne σ 1 with h | h
  · subst h
    simp
  · exact (StrictAnti.comp_perm_lt_of_ne hf h).le

/-- A permutation preserves a strictly antitone function exactly when it is the identity. -/
theorem StrictAnti.comp_perm_eq_iff {f : Fin N → ℤ} (hf : StrictAnti f)
    (σ : Equiv.Perm (Fin N)) : toLex (f ∘ σ) = toLex f ↔ σ = 1 := by
  constructor
  · intro h
    by_contra hσ
    exact (StrictAnti.comp_perm_lt_of_ne hf hσ).ne h
  · rintro rfl
    simp

/-- Strict lexicographic order reverses under subtraction from a common function. -/
theorem toLex_sub_lt_sub {a b c : Fin N → ℤ} (h : toLex a < toLex b) :
    toLex (fun i => c i - b i) < toLex (fun i => c i - a i) := by
  obtain ⟨i, hfix, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    change c j - b j = c j - a j
    have : a j = b j := hfix j hj
    omega
  · change c i - b i < c i - a i
    have : a i < b i := hlt
    omega

/-- Lexicographic order reverses under subtraction from a common function. -/
theorem toLex_sub_le_sub {a b c : Fin N → ℤ} (h : toLex a ≤ toLex b) :
    toLex (fun i => c i - b i) ≤ toLex (fun i => c i - a i) := by
  rcases h.lt_or_eq with hlt | heq
  · exact (toLex_sub_lt_sub hlt).le
  · obtain rfl : a = b := toLex_inj.1 heq
    exact le_refl _

/-- An auxiliary integer-valued function on a finite index type. -/
noncomputable def auxiliaryIndexValue (N : ℕ) : Fin N → ℤ :=
  fun i => (auxiliaryFinsupp N i : ℤ)

/-- An integer-valued function attached to a partition. -/
noncomputable def partitionAuxiliaryValue (la : Nat.Partition N) : Fin N → ℤ :=
  fun i => (partitionNatFinsupp la i : ℤ)

/-- The auxiliary index function is strictly antitone. -/
theorem strictAnti_auxiliaryIndexValue : StrictAnti (auxiliaryIndexValue N) := by
  intro i j hij
  have h1 : (i : ℕ) < (j : ℕ) := hij
  have h2 : (j : ℕ) < N := j.isLt
  simp only [auxiliaryIndexValue, auxiliaryFinsupp,
    Finsupp.coe_equivFunOnFinite_symm]
  omega

/-- Composing the auxiliary index function with a permutation is lexicographically bounded by
the original. -/
@[source_ref"Chapter5/Discussion_proof_of_Frobenius_character_formula"(role:=supporting),
  source_ref"Chapter5/Discussion_footnote_5.15"(role:=primary),
  source_ref"Chapter5/Discussion_footnote_5.15/Derived01"(role:=supporting)]
theorem auxiliaryIndexValue_comp_perm_le (σ : Equiv.Perm (Fin N)) :
    toLex (auxiliaryIndexValue N ∘ σ) ≤ toLex (auxiliaryIndexValue N) :=
  StrictAnti.comp_perm_le strictAnti_auxiliaryIndexValue σ

/-- A permutation preserves the auxiliary index function in lexicographic order exactly when it
is the identity. -/
@[source_ref"Chapter5/Discussion_proof_of_Frobenius_character_formula"(role:=supporting),
  source_ref"Chapter5/Discussion_footnote_5.15"(role:=primary),
  source_ref"Chapter5/Discussion_footnote_5.15/Derived01"(role:=supporting)]
theorem auxiliaryIndexValue_comp_perm_eq_iff (σ : Equiv.Perm (Fin N)) :
    toLex (auxiliaryIndexValue N ∘ σ) = toLex (auxiliaryIndexValue N) ↔ σ = 1 :=
  StrictAnti.comp_perm_eq_iff strictAnti_auxiliaryIndexValue σ

/-- The partition-associated function is lexicographically bounded by the displayed permutation
adjustment. -/
@[source_ref"Chapter5/Discussion_footnote_5.15"(role:=primary)]
theorem partitionAuxiliaryValue_le_adjusted_perm
    (la : Nat.Partition N) (σ : Equiv.Perm (Fin N)) :
    toLex (partitionAuxiliaryValue la) ≤
      toLex (fun i =>
        (partitionAuxiliaryValue la i + auxiliaryIndexValue N i) -
          (auxiliaryIndexValue N ∘ σ) i) := by
  have h := toLex_sub_le_sub
    (c := fun i => partitionAuxiliaryValue la i + auxiliaryIndexValue N i)
    (auxiliaryIndexValue_comp_perm_le (N := N) σ)
  have hc :
      (fun i =>
        (partitionAuxiliaryValue la i + auxiliaryIndexValue N i) -
          auxiliaryIndexValue N i) = partitionAuxiliaryValue la := by
    funext i
    ring
  rwa [hc] at h

/-- The partition-associated function equals the displayed permutation adjustment in
lexicographic order exactly when the permutation is the identity. -/
@[source_ref"Chapter5/Discussion_proof_of_Frobenius_character_formula"(role:=supporting),
  source_ref"Chapter5/Discussion_footnote_5.15"(role:=primary),
  source_ref"Chapter5/Discussion_footnote_5.15/Derived01"(role:=supporting)]
theorem partitionAuxiliaryValue_eq_adjusted_perm_iff
    (la : Nat.Partition N) (σ : Equiv.Perm (Fin N)) :
    toLex (partitionAuxiliaryValue la) =
      toLex (fun i =>
        (partitionAuxiliaryValue la i + auxiliaryIndexValue N i) -
          (auxiliaryIndexValue N ∘ σ) i) ↔ σ = 1 := by
  have hc :
      (fun i =>
        (partitionAuxiliaryValue la i + auxiliaryIndexValue N i) -
          auxiliaryIndexValue N i) = partitionAuxiliaryValue la := by
    funext i
    ring
  constructor
  · intro h
    by_contra hσ
    have hlt := StrictAnti.comp_perm_lt_of_ne strictAnti_auxiliaryIndexValue hσ
    have hrev := toLex_sub_lt_sub
      (c := fun i => partitionAuxiliaryValue la i + auxiliaryIndexValue N i) hlt
    rw [hc] at hrev
    exact absurd h hrev.ne
  · rintro rfl
    have hid :
        (fun i =>
          (partitionAuxiliaryValue la i + auxiliaryIndexValue N i) -
            (auxiliaryIndexValue N ∘ ⇑(1 : Equiv.Perm (Fin N))) i) =
          partitionAuxiliaryValue la := by
      funext i
      simp only [Function.comp_apply, Equiv.Perm.coe_one, id_eq]
      ring
    rw [hid]

end RepresentationTheory.LexicographicPermutations
