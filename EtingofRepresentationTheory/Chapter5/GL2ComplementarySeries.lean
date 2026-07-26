import EtingofRepresentationTheory.Chapter4.Discussion_4_4
import EtingofRepresentationTheory.Chapter5.EllipticInduced
import EtingofRepresentationTheory.Chapter5.GL2CharacterIdentification
import EtingofRepresentationTheory.Chapter5.Lemma5_25_3
import EtingofRepresentationTheory.Infrastructure.FDRepCharacterBiprod
import EtingofRepresentationTheory.Infrastructure.VirtualCharacterSimple

/-!
# The complementary-series representation of `GL₂(𝔽_q)`

This file turns the virtual character in Lemma 5.25.3 into an honest simple
finite-dimensional representation.  The positive and negative parts are the representations
appearing in Discussion 5.25.4; the self-inner-product and positive-dimension calculations
from `Lemma5_25_3` discharge the two hypotheses of `Etingof.simpleOfVirtualChar`.
-/

noncomputable section

open CategoryTheory MonoidalCategory

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

namespace Etingof.GL2

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
  [Fintype (GL2 p n)]

/-- The positive part `W₁ ⊗ V(α,1)` of the complementary-series virtual character. -/
def complementarySeriesPositive
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ) : FDRep ℂ (GL2 p n) :=
  complementW p n 1 ⊗ principalSeries p n (nu.comp (scalarToElliptic p n)) 1

/-- The negative part `V(α,1) ⊕ Ind_K^G(ν)` of the complementary-series virtual
character. -/
def complementarySeriesNegative
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ) : FDRep ℂ (GL2 p n) :=
  principalSeries p n (nu.comp (scalarToElliptic p n)) 1 ⊞ ellipticInduced p n nu

/-- The character difference of the two honest representations above is exactly the virtual
character used in Lemma 5.25.3. -/
theorem complementarySeries_virtualCharacter
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ) (g : GL2 p n) :
    (complementarySeriesPositive p n nu).character g -
        (complementarySeriesNegative p n nu).character g =
      complementarySeriesChar p n nu g := by
  rw [complementarySeriesPositive, complementarySeriesNegative,
    Etingof.Discussion_4_4_char_tensor, Etingof.FDRep.character_biprod,
    character_complementW, character_principalSeries, complementarySeriesChar_eq]
  ring

omit [DecidableEq (GaloisField p n)] in
private theorem complementarySeries_innerProduct
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ)
    (hnu_ne : ∃ k : ↥(ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ g : GL2 p n,
        ((complementarySeriesPositive p n nu).character g -
            (complementarySeriesNegative p n nu).character g) *
          starRingEnd ℂ
            ((complementarySeriesPositive p n nu).character g -
              (complementarySeriesNegative p n nu).character g) = 1 := by
  classical
  simpa only [complementarySeries_virtualCharacter] using
    Etingof.Lemma5_25_3_innerProduct p n hp2 nu hn hnu_ne

omit [DecidableEq (GaloisField p n)] in
private theorem complementarySeries_dimension_pos
    (hn : 0 < n) (nu : ↥(ellipticSubgroup p n) →* ℂˣ) :
    Module.finrank ℂ (complementarySeriesNegative p n nu) <
      Module.finrank ℂ (complementarySeriesPositive p n nu) := by
  classical
  have hchar := complementarySeries_virtualCharacter p n nu (1 : GL2 p n)
  rw [FDRep.char_one, FDRep.char_one,
    (Etingof.Lemma5_25_3_dimension p n nu hn).1] at hchar
  have hcharZ :
      (Module.finrank ℂ (complementarySeriesPositive p n nu) : ℤ) -
          (Module.finrank ℂ (complementarySeriesNegative p n nu) : ℤ) =
        (p ^ n : ℤ) - 1 := by
    exact_mod_cast hchar
  have hpow : (1 : ℤ) < p ^ n := by
    have hreal := (Etingof.Lemma5_25_3_dimension p n nu hn).2
    exact_mod_cast (sub_pos.mp hreal)
  omega

/-- The complementary-series representation associated to a character `ν` not fixed by the
degree-two Frobenius.  It is selected from the Wedderburn decomposition by its virtual
character. -/
def complementarySeriesRep
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) : FDRep ℂ (GL2 p n) :=
  Etingof.simpleOfVirtualChar
    (complementarySeriesPositive p n nu) (complementarySeriesNegative p n nu)
    (complementarySeries_innerProduct p n hp2 hn nu hnu_ne)
    (complementarySeries_dimension_pos p n hn nu)

instance complementarySeriesRep_simple
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    Simple (complementarySeriesRep p n nu hp2 hn hnu_ne) := by
  unfold complementarySeriesRep
  infer_instance

/-- The constructed representation has the complementary-series character. -/
@[simp]
theorem complementarySeriesRep_character
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (g : GL2 p n) :
    (complementarySeriesRep p n nu hp2 hn hnu_ne).character g =
      complementarySeriesChar p n nu g := by
  rw [complementarySeriesRep, Etingof.simpleOfVirtualChar_character,
    complementarySeries_virtualCharacter]

omit [DecidableEq (GaloisField p n)] in
/-- The complementary-series representation has dimension `q - 1`. -/
theorem finrank_complementarySeriesRep
    (nu : ↥(ellipticSubgroup p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    Module.finrank ℂ (complementarySeriesRep p n nu hp2 hn hnu_ne) = p ^ n - 1 := by
  classical
  have hchar := complementarySeriesRep_character p n nu hp2 hn hnu_ne (1 : GL2 p n)
  rw [FDRep.char_one, (Etingof.Lemma5_25_3_dimension p n nu hn).1] at hchar
  have hpow : 1 ≤ p ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n hp.out.ne_zero)
  exact_mod_cast hchar

end Etingof.GL2

end
