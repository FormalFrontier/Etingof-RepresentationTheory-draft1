/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.AuxiliaryFiniteFieldRepresentations
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.FiniteField.AuxiliaryRepresentations


open CategoryTheory CategoryTheory.Limits

noncomputable section


/-- An auxiliary group type indexed by a prime natural number and a natural number. -/
abbrev AuxiliaryGroup (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

/-- An auxiliary character type indexed by a prime natural number and a natural number. -/
abbrev AuxiliaryCharacter (p n : ℕ) [Fact (Nat.Prime p)] := (GaloisField p n)ˣ →* ℂˣ

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

/-- Isomorphic finite-dimensional complex representations have equal finrank. -/
theorem finrank_eq_of_iso {G : Type*} [Monoid G] {X Y : FDRep ℂ G} (i : X ≅ Y) :
    Module.finrank ℂ X.V = Module.finrank ℂ Y.V :=
  (FDRep.isoToLinearEquiv i).finrank_eq

/-- The determinant representation has complex finrank one. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting), simp]
theorem finrank_determinantRepresentation (mu : AuxiliaryCharacter p n) :
    Module.finrank ℂ (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).V = 1 :=
  Module.finrank_self ℂ

set_option backward.isDefEq.respectTransparency false in
/-- The character of the determinant representation at a group element is the indexing character evaluated at its determinant. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem character_determinantRepresentation (mu : AuxiliaryCharacter p n) (g : AuxiliaryGroup p n) :
    (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).character g = ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  change LinearMap.trace ℂ _ ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).ρ g) = _
  have hρ : (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu).ρ g
      = ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := rfl
  rw [hρ, map_smul, LinearMap.trace_id]
  simp

/-- Two determinant representations are isomorphic if and only if their indexing characters are equal. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem determinantRepresentation_iso_iff (mu nu : AuxiliaryCharacter p n) :
    Nonempty (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu ≅ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n nu) ↔ mu = nu := by
  constructor
  · rintro ⟨i⟩
    have hchar := FDRep.char_iso i
    ext c
    obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) c
    have h := congr_fun hchar g
    rw [character_determinantRepresentation, character_determinantRepresentation, hg] at h
    exact congrArg Units.val (Units.ext h)
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- An auxiliary pair type indexed by a prime natural number and a natural number. -/
abbrev AuxiliaryPair (p n : ℕ) [Fact (Nat.Prime p)] :=
  {s : Sym2 (AuxiliaryCharacter p n) // ¬ s.IsDiag}

namespace AuxiliaryPair

variable {p n}

/-- The first auxiliary map from auxiliary pairs to auxiliary characters. -/
def auxiliaryMapOne (s : AuxiliaryPair p n) : AuxiliaryCharacter p n := (Quot.out (s : Sym2 (AuxiliaryCharacter p n))).1

/-- The second auxiliary map from auxiliary pairs to auxiliary characters. -/
def auxiliaryMapTwo (s : AuxiliaryPair p n) : AuxiliaryCharacter p n := (Quot.out (s : Sym2 (AuxiliaryCharacter p n))).2

/-- The symmetric pair of the two components equals the underlying subtype value. -/
@[simp]
theorem sym2_mk_eq_val (s : AuxiliaryPair p n) : s(s.auxiliaryMapOne, s.auxiliaryMapTwo) = (s : Sym2 (AuxiliaryCharacter p n)) := by
  change Quot.mk _ ((Quot.out (s : Sym2 (AuxiliaryCharacter p n))).1, (Quot.out (s : Sym2 (AuxiliaryCharacter p n))).2) = _
  rw [Prod.mk.eta]
  exact Quot.out_eq _

/-- The two components of an auxiliary pair are distinct. -/
theorem fst_ne_snd (s : AuxiliaryPair p n) : s.auxiliaryMapOne ≠ s.auxiliaryMapTwo := fun h =>
  s.2 (by rw [← sym2_mk_eq_val s]; exact Sym2.mk_isDiag_iff.mpr h)

/-- Two auxiliary pairs are equal when the two-element sets formed by their components are equal. -/
theorem ext_of_insert_eq {s t : AuxiliaryPair p n}
    (h : ({s.auxiliaryMapOne, s.auxiliaryMapTwo} : Set (AuxiliaryCharacter p n)) = {t.auxiliaryMapOne, t.auxiliaryMapTwo}) : s = t := by
  apply Subtype.ext
  rw [← sym2_mk_eq_val s, ← sym2_mk_eq_val t]
  rw [Set.pair_eq_pair_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Sym2.eq_swap]

end AuxiliaryPair

/-- The natural-number cast of the exponent of the unit group of a finite field is nonzero. -/
instance neZero_natCast_exponent_units_galoisField :
    NeZero ((Monoid.exponent (GaloisField p n)ˣ : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

/-- The auxiliary character type is finite. -/
instance finite_auxiliaryCharacter : Finite (AuxiliaryCharacter p n) :=
  Finite.of_equiv _
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      ((GaloisField p n)ˣ) ℂ).some.toEquiv.symm

/-- For nonzero degree, the auxiliary character type has cardinality one less than the corresponding prime power. -/
theorem card_auxiliaryCharacter (hn : n ≠ 0) : Nat.card (AuxiliaryCharacter p n) = p ^ n - 1 := by
  classical
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((GaloisField p n)ˣ) ℂ,
    Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card p n hn]

/-- The cardinality of the auxiliary pair type is the binomial coefficient choosing two auxiliary characters. -/
theorem card_auxiliaryPair : Nat.card (AuxiliaryPair p n) = (Nat.card (AuxiliaryCharacter p n)).choose 2 := by
  classical
  haveI : Fintype (AuxiliaryCharacter p n) := Fintype.ofFinite _
  have := Sym2.card_subtype_not_diag (α := AuxiliaryCharacter p n)
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this

/-- An auxiliary representation index type indexed by a prime natural number and a natural number. -/
abbrev AuxiliaryRepresentationIndex (p n : ℕ) [Fact (Nat.Prime p)] :=
  AuxiliaryCharacter p n ⊕ AuxiliaryCharacter p n ⊕ AuxiliaryPair p n

/-- The complex representation of the auxiliary group associated to an auxiliary representation index. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
def AuxiliaryRepresentation : AuxiliaryRepresentationIndex p n → FDRep ℂ (AuxiliaryGroup p n)
  | .inl mu => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu
  | .inr (.inl mu) => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n mu
  | .inr (.inr s) => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n s.auxiliaryMapOne s.auxiliaryMapTwo

/-- On a left sum index, the auxiliary representation equals the determinant representation. -/
@[simp] theorem auxiliaryRepresentation_inl (mu : AuxiliaryCharacter p n) :
    AuxiliaryRepresentation p n (.inl mu) = RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu := rfl

/-- On a right-left sum index, the auxiliary representation equals the corresponding representation indexed by one character. -/
@[simp] theorem auxiliaryRepresentation_inr_inl (mu : AuxiliaryCharacter p n) :
    AuxiliaryRepresentation p n (.inr (.inl mu)) = RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n mu := rfl

/-- On a right-right sum index, the auxiliary representation equals the representation indexed by the two components of the auxiliary pair. -/
@[simp] theorem auxiliaryRepresentation_inr_inr (s : AuxiliaryPair p n) :
    AuxiliaryRepresentation p n (.inr (.inr s)) = RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n s.auxiliaryMapOne s.auxiliaryMapTwo := rfl

private theorem two_le_q (hn : n ≠ 0) : 2 ≤ p ^ n :=
  Nat.one_lt_pow hn hp.out.one_lt

/-- For nonzero degree, a determinant representation is not isomorphic to the other representation indexed by one character. -/
theorem determinantRepresentation_not_iso_unaryRepresentation (hn : n ≠ 0) (mu nu : AuxiliaryCharacter p n) :
    ¬ Nonempty (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu ≅ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n nu) := by
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [finrank_determinantRepresentation, (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_representation_summary_of_pos p n (Nat.pos_of_ne_zero hn) nu).2.2] at h
  have := two_le_q p n hn
  omega

/-- For nonzero degree, a determinant representation is not isomorphic to a representation indexed by two characters. -/
theorem determinantRepresentation_not_iso_binaryRepresentation (hn : n ≠ 0) (mu chi1 chi2 : AuxiliaryCharacter p n) :
    ¬ Nonempty (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation p n mu ≅ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n chi1 chi2) := by
  haveI : NeZero n := ⟨hn⟩
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [finrank_determinantRepresentation, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_finrank] at h
  have := two_le_q p n hn
  omega

/-- For nonzero degree, the auxiliary representation indexed by one character is not isomorphic to the representation indexed by two characters. -/
theorem unary_representation_not_iso_binary_representation (hn : n ≠ 0) (mu chi1 chi2 : AuxiliaryCharacter p n) :
    ¬ Nonempty (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n mu ≅ RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n chi1 chi2) := by
  haveI : NeZero n := ⟨hn⟩
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [(RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_representation_summary_of_pos p n (Nat.pos_of_ne_zero hn) mu).2.2, RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_finrank] at h
  omega

/-- For nonzero degree, the finrank of an auxiliary representation is one, the corresponding prime power, or one more than that prime power according to its sum index. -/
theorem finrank_auxiliaryRepresentation (hn : n ≠ 0) :
    ∀ i, Module.finrank ℂ (AuxiliaryRepresentation p n i).V =
      Sum.elim (fun _ => 1) (Sum.elim (fun _ => p ^ n) (fun _ => p ^ n + 1)) i
  | .inl mu => finrank_determinantRepresentation p n mu
  | .inr (.inl mu) => (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_representation_summary_of_pos p n (Nat.pos_of_ne_zero hn) mu).2.2
  | .inr (.inr s) => by
      haveI : NeZero n := ⟨hn⟩
      exact RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_finrank p n s.auxiliaryMapOne s.auxiliaryMapTwo

/-- For nonzero degree, every auxiliary representation is simple. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem simple_auxiliaryRepresentation (hn : n ≠ 0) : ∀ i, Simple (AuxiliaryRepresentation p n i)
  | .inl mu => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryOtherRepresentation_simple p n mu
  | .inr (.inl mu) => (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliary_representation_summary_of_pos p n (Nat.pos_of_ne_zero hn) mu).2.1
  | .inr (.inr s) => RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_simple_of_ne p n s.auxiliaryMapOne s.auxiliaryMapTwo s.fst_ne_snd

/-- For nonzero degree, isomorphic auxiliary representations have equal indices. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem eq_of_auxiliaryRepresentation_iso (hn : n ≠ 0) :
    ∀ i j : AuxiliaryRepresentationIndex p n, Nonempty (AuxiliaryRepresentation p n i ≅ AuxiliaryRepresentation p n j) →
      i = j := by
  haveI : NeZero n := ⟨hn⟩
  rintro (mu | mu | s) (nu | nu | t) h
  · exact congrArg Sum.inl ((determinantRepresentation_iso_iff p n mu nu).mp h)
  · exact absurd h (determinantRepresentation_not_iso_unaryRepresentation p n hn mu nu)
  · exact absurd h (determinantRepresentation_not_iso_binaryRepresentation p n hn mu t.auxiliaryMapOne t.auxiliaryMapTwo)
  · exact absurd (Nonempty.map Iso.symm h) (determinantRepresentation_not_iso_unaryRepresentation p n hn nu mu)
  · exact congrArg (fun x => Sum.inr (Sum.inl x))
      ((RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation_iso_iff p n mu nu).mp h)
  · exact absurd h (unary_representation_not_iso_binary_representation p n hn mu t.auxiliaryMapOne t.auxiliaryMapTwo)
  · exact absurd (Nonempty.map Iso.symm h) (determinantRepresentation_not_iso_binaryRepresentation p n hn nu s.auxiliaryMapOne s.auxiliaryMapTwo)
  · exact absurd (Nonempty.map Iso.symm h)
      (unary_representation_not_iso_binary_representation p n hn nu s.auxiliaryMapOne s.auxiliaryMapTwo)
  · refine congrArg (fun x => Sum.inr (Sum.inr x)) (AuxiliaryPair.ext_of_insert_eq ?_)
    exact (RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation_iso_iff p n s.auxiliaryMapOne s.auxiliaryMapTwo t.auxiliaryMapOne t.auxiliaryMapTwo s.fst_ne_snd t.fst_ne_snd).mp h

/-- For nonzero degree, the auxiliary representation index type has cardinality q minus one plus q times q minus one divided by two, where q is the corresponding prime power. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem card_auxiliaryRepresentationIndex (hn : n ≠ 0) :
    Nat.card (AuxiliaryRepresentationIndex p n) = (p ^ n - 1) + p ^ n * (p ^ n - 1) / 2 := by
  classical
  have hq := two_le_q p n hn
  have hchars := card_auxiliaryCharacter p n hn
  have hpair : Nat.card (AuxiliaryPair p n) = (p ^ n - 1).choose 2 := by
    rw [card_auxiliaryPair, hchars]
  have hsum : Nat.card (AuxiliaryRepresentationIndex p n)
      = Nat.card (AuxiliaryCharacter p n) + (Nat.card (AuxiliaryCharacter p n) + Nat.card (AuxiliaryPair p n)) := by
    rw [Nat.card_sum, Nat.card_sum]
  rw [hsum, hchars, hpair, Nat.choose_two_right]
  -- With `a = q − 1`: `a + (a + a(a−1)/2) = a + (a+1)a/2`, since `2 ∣ a(a−1)`.
  set a := p ^ n - 1 with ha
  have hqa : p ^ n = a + 1 := by omega
  obtain ⟨k, hk⟩ : 2 ∣ a * (a - 1) := by
    rcases Nat.even_or_odd a with h | h
    · exact Dvd.dvd.mul_right h.two_dvd _
    · have : Even (a - 1) := by rcases h with ⟨m, hm⟩; exact ⟨m, by omega⟩
      exact Dvd.dvd.mul_left this.two_dvd _
  have hka : (a + 1) * a = 2 * (k + a) := by
    have : (a + 1) * a = a * (a - 1) + 2 * a := by cases a with
      | zero => simp
      | succ m => simp; ring
    rw [this, hk]; ring
  rw [hqa, hk, hka, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

/-- For nonzero degree, there is a pairwise nonisomorphic family of simple objects whose index type has cardinality q minus one plus q times q minus one divided by two. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem exists_simple_family_card_primePower (hn : n ≠ 0) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (AuxiliaryGroup p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = (p ^ n - 1) + p ^ n * (p ^ n - 1) / 2 :=
  ⟨AuxiliaryRepresentationIndex p n, AuxiliaryRepresentation p n, simple_auxiliaryRepresentation p n hn,
    eq_of_auxiliaryRepresentation_iso p n hn, card_auxiliaryRepresentationIndex p n hn⟩

/-- For nonzero degree, there is a pairwise nonisomorphic family of simple objects with the stated cardinality in terms of the finite field cardinality. -/
theorem exists_simple_family_card_galoisField (hn : n ≠ 0) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (AuxiliaryGroup p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = (Nat.card (GaloisField p n) - 1)
        + Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) - 1) / 2 := by
  classical
  rw [GaloisField.card p n hn]
  exact exists_simple_family_card_primePower p n hn


end

end RepresentationTheory.FiniteField.AuxiliaryRepresentations
