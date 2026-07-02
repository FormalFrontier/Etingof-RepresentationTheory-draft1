import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_S4
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Discussion 5.11(3): the `S₄ / S₃` induced representations

Etingof's §5.11(3) records the decompositions, obtained via Frobenius reciprocity, of the
representations of `S₄` induced from the three irreducibles of the point-stabiliser
subgroup `S₃ ≤ S₄`:

* `Ind_{S₃}^{S₄} ℂ₊ ≅ ℂ₊ ⊕ ℂ³₋`,
* `Ind_{S₃}^{S₄} ℂ₋ ≅ ℂ₋ ⊕ ℂ³₊`,
* `Ind_{S₃}^{S₄} ℂ² ≅ ℂ² ⊕ ℂ³₋ ⊕ ℂ³₊`,

where `{ℂ₊, ℂ₋, ℂ², ℂ³₋, ℂ³₊}` are the five irreducibles of `S₄` built in
`Etingof.Example4_3_S4` (`trivRep`, `signRep`, `twoDimRep`, `stdRep`, `rotRep`).

Just as the `S₃` decompositions in `Discussion5_11_examples.lean` rest on the
completeness of the `S₃` catalogue (`S3_simple_iso`), the `S₄` decompositions rest on
the completeness of the `S₄` catalogue: **every simple `FDRep ℂ S₄` is isomorphic to one
of the five listed irreducibles**. This file establishes that catalogue-completeness
theorem `S4_simple_iso`, the reusable prerequisite for the induction computations. It
follows from the Artin–Wedderburn squared-dimension count `1² + 1² + 2² + 3² + 3² = 24 =
|S₄|` (`Etingof.Example4_3_S4.irreps_dim_sum_of_squares`): the five listed irreducibles
are simple, pairwise non-isomorphic, and exhaust the squared-dimension budget, so no sixth
simple can exist.

The remaining induction decompositions themselves (the three isomorphisms above) are
tracked as follow-up work: they require realising `S₃` as the stabiliser subgroup of a
point in `S₄`, transporting the three `S₃` irreducibles to that subgroup, a group-generic
form of the Frobenius-reciprocity dimension lemma `frobenius_finrank`, and the fifteen
restricted-character scalar products over the (non-cyclic, order-6) subgroup.

## Mathlib correspondence

* `Equiv.Perm (Fin 4)` — the group `S₄`.
* `Etingof.Example4_3_S4` — the five irreducible representations and their characters.
* `Etingof.exists_simples_sum_finrank_sq_eq_card` — the Artin–Wedderburn family used to
  pin down the catalogue.
-/

open CategoryTheory Module

noncomputable section

namespace Etingof.Example4_3_S4

/-! ### Pairwise non-isomorphism of the five irreducibles

Of the ten pairs, eight are separated by dimension (`1, 1, 2, 3, 3`); the two same-dimension
pairs `ℂ₊ / ℂ₋` and `ℂ³₋ / ℂ³₊` are separated by character values (the sign character is
`-1` on a transposition, and `stdRep_character_ne_rotRep_character` already records the
`ℂ³₋ / ℂ³₊` separation). -/

/-- Two `S₄`-representations of different dimension cannot be isomorphic. -/
private lemma not_iso_of_finrank_ne {V W : FDRep ℂ S4}
    (h : finrank ℂ (V : Type) ≠ finrank ℂ (W : Type)) : ¬ Nonempty (V ≅ W) := by
  rintro ⟨e⟩
  exact h (FDRep.isoToLinearEquiv e).finrank_eq

lemma trivRep_not_iso_signRep : ¬ Nonempty (trivRep ≅ signRep) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap (0 : Fin 4) 1)
  rw [show trivRep = FDRep.of (charRep (1 : S4 →* ℂˣ)) from rfl,
      show signRep = FDRep.of (charRep signHom) from rfl,
      charRep_character, charRep_character] at h
  simp only [MonoidHom.one_apply, Units.val_one, signHom_coe] at h
  rw [show Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 from by decide] at h
  norm_num at h

lemma trivRep_not_iso_twoDimRep : ¬ Nonempty (trivRep ≅ twoDimRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, twoDimRep_finrank]; norm_num)

lemma trivRep_not_iso_stdRep : ¬ Nonempty (trivRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, stdRep_finrank]; norm_num)

lemma trivRep_not_iso_rotRep : ¬ Nonempty (trivRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, rotRep_finrank]; norm_num)

lemma signRep_not_iso_twoDimRep : ¬ Nonempty (signRep ≅ twoDimRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, twoDimRep_finrank]; norm_num)

lemma signRep_not_iso_stdRep : ¬ Nonempty (signRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, stdRep_finrank]; norm_num)

lemma signRep_not_iso_rotRep : ¬ Nonempty (signRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, rotRep_finrank]; norm_num)

lemma twoDimRep_not_iso_stdRep : ¬ Nonempty (twoDimRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [twoDimRep_finrank, stdRep_finrank]; norm_num)

lemma twoDimRep_not_iso_rotRep : ¬ Nonempty (twoDimRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [twoDimRep_finrank, rotRep_finrank]; norm_num)

lemma stdRep_not_iso_rotRep : ¬ Nonempty (stdRep ≅ rotRep) := by
  rintro ⟨e⟩
  exact stdRep_character_ne_rotRep_character (congrFun (FDRep.char_iso e) (Equiv.swap 0 1))

/-! ### Completeness of the `S₄` catalogue -/

instance : NeZero (Nat.card S4 : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

instance : Simple trivRep := trivRep_simple
instance : Simple signRep := signRep_simple
instance : Simple twoDimRep := twoDimRep_simple
instance : Simple stdRep := stdRep_simple
instance : Simple rotRep := rotRep_simple

/-- Every simple representation of `S₄` is isomorphic to one of the five irreducibles
`trivRep` (`ℂ₊`), `signRep` (`ℂ₋`), `twoDimRep` (`ℂ²`), `stdRep` (`ℂ³₋`), or `rotRep`
(`ℂ³₊`).

This follows from the Artin–Wedderburn dimension count `1² + 1² + 2² + 3² + 3² = 24 = |S₄|`
(`irreps_dim_sum_of_squares`): the five listed irreducibles are simple, pairwise
non-isomorphic, and exhaust the squared-dimension budget, so no sixth simple can exist.
It is the `S₄` analogue of `Etingof.Discussion5_11.S3_simple_iso` and the catalogue-
completeness input for the `Ind_{S₃}^{S₄}` decompositions of Discussion 5.11(3). -/
theorem S4_simple_iso (S : FDRep ℂ S4) [Simple S] :
    Nonempty (S ≅ trivRep) ∨ Nonempty (S ≅ signRep) ∨ Nonempty (S ≅ twoDimRep) ∨
      Nonempty (S ≅ stdRep) ∨ Nonempty (S ≅ rotRep) := by
  classical
  obtain ⟨n, V, hsimple, hinj, hsurj, hsum⟩ := exists_simples_sum_finrank_sq_eq_card ℂ S4
  obtain ⟨a, ⟨ea⟩⟩ := hsurj trivRep trivRep_simple
  obtain ⟨b, ⟨eb⟩⟩ := hsurj signRep signRep_simple
  obtain ⟨c, ⟨ec⟩⟩ := hsurj twoDimRep twoDimRep_simple
  obtain ⟨d, ⟨ed⟩⟩ := hsurj stdRep stdRep_simple
  obtain ⟨f, ⟨ef⟩⟩ := hsurj rotRep rotRep_simple
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  -- dimensions of the five distinguished indices
  have hda : finrank ℂ (V a : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv ea).finrank_eq, trivRep_finrank]
  have hdb : finrank ℂ (V b : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv eb).finrank_eq, signRep_finrank]
  have hdc : finrank ℂ (V c : Type) = 2 := by
    rw [← (FDRep.isoToLinearEquiv ec).finrank_eq, twoDimRep_finrank]
  have hdd : finrank ℂ (V d : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ed).finrank_eq, stdRep_finrank]
  have hdf : finrank ℂ (V f : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ef).finrank_eq, rotRep_finrank]
  -- a, b, c, d, f are pairwise distinct
  have hab : a ≠ b := by rintro rfl; exact trivRep_not_iso_signRep ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by rintro rfl; exact trivRep_not_iso_twoDimRep ⟨ea ≪≫ ec.symm⟩
  have had : a ≠ d := by rintro rfl; exact trivRep_not_iso_stdRep ⟨ea ≪≫ ed.symm⟩
  have haf : a ≠ f := by rintro rfl; exact trivRep_not_iso_rotRep ⟨ea ≪≫ ef.symm⟩
  have hbc : b ≠ c := by rintro rfl; exact signRep_not_iso_twoDimRep ⟨eb ≪≫ ec.symm⟩
  have hbd : b ≠ d := by rintro rfl; exact signRep_not_iso_stdRep ⟨eb ≪≫ ed.symm⟩
  have hbf : b ≠ f := by rintro rfl; exact signRep_not_iso_rotRep ⟨eb ≪≫ ef.symm⟩
  have hcd : c ≠ d := by rintro rfl; exact twoDimRep_not_iso_stdRep ⟨ec ≪≫ ed.symm⟩
  have hcf : c ≠ f := by rintro rfl; exact twoDimRep_not_iso_rotRep ⟨ec ≪≫ ef.symm⟩
  have hdf' : d ≠ f := by rintro rfl; exact stdRep_not_iso_rotRep ⟨ed ≪≫ ef.symm⟩
  -- s is one of a, b, c, d, f
  have hs : s = a ∨ s = b ∨ s = c ∨ s = d ∨ s = f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hsa, hsb, hsc, hsd, hsf⟩ := hcon
    -- {a,b,c,d,f,s} are six distinct indices; their squared dims sum to ≥ 25 > 24
    have hsub : ({a, b, c, d, f, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hpos : 0 < finrank ℂ (V s : Type) := by
      haveI := hsimple s
      exact Etingof.finrank_pos_of_not_isZero (Simple.not_isZero (V s))
    have hle : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 ≤
        ∑ i, finrank ℂ (V i : Type) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    have hcard : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 =
        finrank ℂ (V a : Type) ^ 2 + finrank ℂ (V b : Type) ^ 2 + finrank ℂ (V c : Type) ^ 2 +
          finrank ℂ (V d : Type) ^ 2 + finrank ℂ (V f : Type) ^ 2 + finrank ℂ (V s : Type) ^ 2 := by
      rw [Finset.sum_insert (by simp [hab, hac, had, haf, hsa.symm]),
        Finset.sum_insert (by simp [hbc, hbd, hbf, hsb.symm]),
        Finset.sum_insert (by simp [hcd, hcf, hsc.symm]),
        Finset.sum_insert (by simp [hdf', hsd.symm]),
        Finset.sum_insert (by simp [hsf.symm]), Finset.sum_singleton]
      ring
    have hcard24 : Fintype.card S4 = 24 := by decide
    rw [hsum, hcard24] at hle
    rw [hcard, hda, hdb, hdc, hdd, hdf] at hle
    -- 1 + 1 + 4 + 9 + 9 + (≥1) ≤ 24 is impossible
    have hsq : 1 ≤ finrank ℂ (V s : Type) ^ 2 := Nat.one_le_pow 2 _ hpos
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨es ≪≫ ea.symm⟩
  · exact Or.inr (Or.inl ⟨es ≪≫ eb.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨es ≪≫ ec.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨es ≪≫ ed.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨es ≪≫ ef.symm⟩)))

end Etingof.Example4_3_S4
