import EtingofRepresentationTheory.Chapter5.GL2ComplementarySeries
import EtingofRepresentationTheory.Chapter5.Discussion5_25_4
import EtingofRepresentationTheory.Chapter5.CharEqIso
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Frobenius orbits of complementary-series representations

This file connects the additive orbit calculation in `Discussion5_25_4` with the
elliptic-torus characters used to construct complementary-series representations.
-/

noncomputable section

open CategoryTheory

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)
private abbrev K := ↥(Etingof.GL2.ellipticSubgroup p n)

namespace Etingof.GL2

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
  [Fintype (GL2 p n)]

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- The elliptic torus is cyclic. -/
theorem ellipticSubgroup_isCyclic (hn : n ≠ 0) : IsCyclic (K p n) := by
  let e := (fieldExtEmbed p n).ofInjective (by
    intro a b hab
    unfold fieldExtEmbed at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
        (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn))).toRingHom
        (congr_arg (fun g => g.val) hab)))
  exact isCyclic_of_surjective e e.surjective

/-- A multiplicative identification of elliptic-torus characters with the additive
cyclic parameter group `ZMod (q² - 1)`. -/
def complementaryCharParamEquiv (hn : n ≠ 0) :
    (K p n →* ℂˣ) ≃* Multiplicative (ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) := by
  letI : IsCyclic (K p n) := ellipticSubgroup_isCyclic p n hn
  letI : NeZero (Nat.card (K p n)) := ⟨Nat.card_pos.ne'⟩
  let dual : (K p n →* ℂˣ) ≃* K p n :=
    (IsCyclic.monoidHom_equiv_self (K p n) ℂ).some
  let param : K p n ≃* Multiplicative
      (ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
        card_ellipticSubgroup p n hn])
  exact dual.trans param

/-- Pointwise `q`-th power of a character of the elliptic torus. -/
def complementaryCharFrobenius
    (nu : K p n →* ℂˣ) : K p n →* ℂˣ :=
  (powMonoidHom (Fintype.card (GaloisField p n))).comp nu

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
@[simp]
theorem complementaryCharFrobenius_apply (nu : K p n →* ℂˣ) (k : K p n) :
    complementaryCharFrobenius p n nu k =
      (nu k) ^ Fintype.card (GaloisField p n) := rfl

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Under `complementaryCharParamEquiv`, Frobenius is multiplication by `q`. -/
theorem complementaryCharParamEquiv_frobenius (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    complementaryCharParamEquiv p n hn (complementaryCharFrobenius p n nu) =
      Multiplicative.ofAdd
        (Etingof.ComplementarySeries.cs_f (Fintype.card (GaloisField p n))
          (Multiplicative.toAdd (complementaryCharParamEquiv p n hn nu))) := by
  change complementaryCharParamEquiv p n hn
      (nu ^ Fintype.card (GaloisField p n)) = _
  calc
    _ = (complementaryCharParamEquiv p n hn nu) ^
        Fintype.card (GaloisField p n) :=
      map_pow (complementaryCharParamEquiv p n hn).toMonoidHom nu _
    _ = _ := by
      apply Multiplicative.toAdd.injective
      simp [Etingof.ComplementarySeries.cs_f, nsmul_eq_mul]

/-- The elliptic-torus character represented by an additive cyclic parameter. -/
def complementaryCharOfParam (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) : K p n →* ℂˣ :=
  (complementaryCharParamEquiv p n hn).symm (Multiplicative.ofAdd x)

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
@[simp]
theorem complementaryCharParamEquiv_ofParam (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :
    complementaryCharParamEquiv p n hn (complementaryCharOfParam p n hn x) =
      Multiplicative.ofAdd x :=
  (complementaryCharParamEquiv p n hn).apply_symm_apply _

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- A cyclic parameter is moved exactly when its elliptic-torus character is moved by
Frobenius. -/
theorem complementaryCharOfParam_moved_iff (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :
    complementaryCharFrobenius p n (complementaryCharOfParam p n hn x) ≠
        complementaryCharOfParam p n hn x ↔
      Etingof.ComplementarySeries.cs_f (Fintype.card (GaloisField p n)) x ≠ x := by
  rw [ne_eq, ← (complementaryCharParamEquiv p n hn).injective.eq_iff,
    complementaryCharParamEquiv_frobenius, complementaryCharParamEquiv_ofParam]
  rfl

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- The Frobenius matrix, regarded as an element of the usual subgroup normalizer. -/
theorem frobeniusMatrix_mem_subgroupNormalizer (hn : n ≠ 0) :
    frobeniusMatrix p n ∈ Subgroup.normalizer (ellipticSubgroup p n) := by
  apply Subgroup.mem_normalizer_fintype
  intro k hk
  rw [← frobeniusMatrix_inv_eq_self p n hn]
  exact frobeniusMatrix_mem_normalizer p n hn k hk

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Conjugating an elliptic-torus character by the Frobenius matrix is its pointwise
`q`-th power. -/
theorem conjugateCharacter_frobenius (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    Etingof.InducedChar.conjugateCharacter (ellipticSubgroup p n) nu
      (frobeniusMatrix p n) (frobeniusMatrix_mem_subgroupNormalizer p n hn) =
        complementaryCharFrobenius p n nu := by
  apply MonoidHom.ext
  intro k
  obtain ⟨a, ha⟩ := k.2
  have hk : k = ⟨fieldExtEmbed p n a, ⟨a, rfl⟩⟩ := Subtype.ext ha.symm
  subst k
  let k0 : K p n := ⟨fieldExtEmbed p n a, ⟨a, rfl⟩⟩
  let kc : K p n :=
    ⟨frobeniusMatrix p n * (k0 : GL2 p n) * (frobeniusMatrix p n)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (frobeniusMatrix_mem_subgroupNormalizer p n hn) k0).mp k0.2⟩
  change nu kc = (nu k0) ^ Fintype.card (GaloisField p n)
  have hconj :
      kc =
        ⟨fieldExtEmbed p n (a ^ Fintype.card (GaloisField p n)), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change frobeniusMatrix p n * fieldExtEmbed p n a * (frobeniusMatrix p n)⁻¹ = _
    rw [frobeniusMatrix_inv_eq_self p n hn]
    have hc := frobeniusMatrix_conj p n hn a
    rw [frobeniusMatrix_inv_eq_self p n hn] at hc
    exact hc.trans (congrArg (fieldExtEmbed p n) (Units.ext rfl))
  rw [hconj]
  rw [← map_pow]
  apply congrArg nu
  apply Subtype.ext
  exact map_pow (fieldExtEmbed p n) a _

/-- The induced elliptic representation is constant on Frobenius orbits of
characters. -/
def ellipticInducedFrobeniusIso (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    ellipticInduced p n nu ≅
      ellipticInduced p n (complementaryCharFrobenius p n nu) :=
  show Etingof.InducedChar.ind (ellipticSubgroup p n) nu ≅
      Etingof.InducedChar.ind (ellipticSubgroup p n)
        (complementaryCharFrobenius p n nu) from
    Etingof.InducedChar.indConjugateIso (ellipticSubgroup p n) nu
      (frobeniusMatrix p n) (frobeniusMatrix_mem_subgroupNormalizer p n hn) ≪≫
        eqToIso (by rw [conjugateCharacter_frobenius p n hn nu])

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Frobenius does not change the restriction of an elliptic-torus character to
scalar matrices. -/
theorem complementaryCharFrobenius_comp_scalar (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    (complementaryCharFrobenius p n nu).comp (scalarToElliptic p n) =
      nu.comp (scalarToElliptic p n) := by
  classical
  apply MonoidHom.ext
  intro a
  change (nu (scalarToElliptic p n a)) ^ Fintype.card (GaloisField p n) =
    nu (scalarToElliptic p n a)
  have h := Etingof.qm1_char_on_scalar p n nu hn a
  change (nu (scalarToElliptic p n a)) ^ (Fintype.card (GaloisField p n) - 1) = 1 at h
  have hqpos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  rw [show Fintype.card (GaloisField p n) =
    Fintype.card (GaloisField p n) - 1 + 1 by omega, pow_succ, h, one_mul]

/-- The complementary-series character is constant on Frobenius orbits. -/
theorem complementarySeriesChar_frobenius (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    complementarySeriesChar p n nu =
      complementarySeriesChar p n (complementaryCharFrobenius p n nu) := by
  funext g
  rw [complementarySeriesChar_eq, complementarySeriesChar_eq,
    complementaryCharFrobenius_comp_scalar p n hn nu]
  rw [FDRep.char_iso (ellipticInducedFrobeniusIso p n hn nu)]

/-- Complementary-series representations attached to the two characters in a
Frobenius orbit are isomorphic. -/
def complementarySeriesRepFrobeniusIso
    (hp2 : p ≠ 2) (hn : 0 < n) (nu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n, (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hnuF : ∃ k : K p n,
      (complementaryCharFrobenius p n nu k) ^ Fintype.card (GaloisField p n) ≠
        complementaryCharFrobenius p n nu k) :
    complementarySeriesRep p n nu hp2 hn hnu ≅
      complementarySeriesRep p n (complementaryCharFrobenius p n nu) hp2 hn hnuF :=
  (Etingof.charEq_iso _ _ (by
    funext g
    rw [complementarySeriesRep_character, complementarySeriesRep_character,
      complementarySeriesChar_frobenius p n hn.ne' nu])).some

omit [DecidableEq (GaloisField p n)] in
/-- On an elliptic element of the torus, the induced character is the sum of the two
Frobenius-conjugate torus characters. -/
theorem character_ellipticInduced_on_elliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (nu : K p n →* ℂˣ)
    (k : K p n) (hk : GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)) :
    (ellipticInduced p n nu).character (k : GL2 p n) =
      (nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n) := by
  classical
  let S : ℂ := ∑ z : GL2 p n,
    if h : z⁻¹ * (k : GL2 p n) * z ∈ ellipticSubgroup p n
    then (nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩ : ℂ) else 0
  have hweighted : (nu k : ℂ) * starRingEnd ℂ S =
      (Fintype.card (K p n) : ℂ) *
        (1 + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)) := by
    calc
      (nu k : ℂ) * starRingEnd ℂ S =
          ∑ z : GL2 p n,
            if h : z⁻¹ * (k : GL2 p n) * z ∈ ellipticSubgroup p n
            then (nu k : ℂ) *
              starRingEnd ℂ (nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩ : ℂ)
            else 0 := by
        dsimp only [S]
        rw [map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := Etingof.normalizer_char_eval p n hp2 nu hn k hk
  have hconj := congrArg (starRingEnd ℂ) hweighted
  have hconj' : starRingEnd ℂ (nu k : ℂ) * S =
      (Fintype.card (K p n) : ℂ) *
        (1 + (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1)) := by
    simpa [Etingof.qm1_char] using hconj
  have hnorm : (nu k : ℂ) * starRingEnd ℂ (nu k : ℂ) = 1 :=
    Etingof.normSq_monoidHom_val_eq_one nu k
  have hqpos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  have hpow : (nu k : ℂ) *
      (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1) =
        (nu k : ℂ) ^ Fintype.card (GaloisField p n) := by
    have hqeq : Fintype.card (GaloisField p n) - 1 + 1 =
        Fintype.card (GaloisField p n) := by omega
    calc
      _ = (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1) * (nu k : ℂ) :=
        mul_comm _ _
      _ = (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1 + 1) :=
        (pow_succ _ _).symm
      _ = _ := by rw [hqeq]
  have hS : S = (Fintype.card (K p n) : ℂ) *
      ((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
    calc
      S = (nu k : ℂ) * (starRingEnd ℂ (nu k : ℂ) * S) := by
        rw [← mul_assoc, hnorm, one_mul]
      _ = (nu k : ℂ) * ((Fintype.card (K p n) : ℂ) *
          (1 + (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1))) := by rw [hconj']
      _ = (Fintype.card (K p n) : ℂ) *
          ((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
        rw [← hpow]
        ring
  rw [character_ellipticInduced]
  change (Fintype.card (K p n) : ℂ)⁻¹ * S = _
  have hKne : (Fintype.card (K p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := K p n)
  rw [hS, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]

/-- On an elliptic element of the torus, the complementary-series character is the
negative Frobenius-orbit sum of its parameter. -/
theorem complementarySeriesChar_on_elliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (nu : K p n →* ℂˣ)
    (k : K p n) (hk : GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)) :
    complementarySeriesChar p n nu (k : GL2 p n) =
      -((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
  rw [complementarySeriesChar_eq, Etingof.charW₁_elliptic p n (k : GL2 p n) hk,
    Etingof.charVα₁_elliptic p n _ (k : GL2 p n) hk,
    character_ellipticInduced_on_elliptic p n hp2 hn nu k hk]
  ring

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- The cardinality `q` of the base field is at least two in positive degree. -/
private theorem two_le_fieldCard (hn : n ≠ 0) :
    2 ≤ Fintype.card (GaloisField p n) := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  exact Nat.one_lt_pow hn hp.out.one_lt

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- A scalar element of the elliptic torus has order at most `q - 1`. -/
private theorem orderOf_le_q_sub_one_of_isScalar
    (hn : n ≠ 0) (k : K p n)
    (hk : GL2.IsScalar (p := p) (n := n) (k : GL2 p n)) :
    orderOf k ≤ Fintype.card (GaloisField p n) - 1 := by
  classical
  let a : (GaloisField p n)ˣ := Units.mk0 ((k : GL2 p n).val 0 0)
    (Etingof.scalar_diag_ne_zero p n (k : GL2 p n) hk)
  have hka : k = scalarToElliptic p n a := by
    apply Subtype.ext
    letI := Etingof.algebraGaloisFieldExt p n
    unfold scalarToElliptic
    simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
    exact Etingof.scalar_eq_fieldExtEmbed p n hn (k : GL2 p n) hk
      (Etingof.scalar_diag_ne_zero p n (k : GL2 p n) hk)
  rw [hka]
  calc
    orderOf (scalarToElliptic p n a) ≤ orderOf a :=
      Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd (scalarToElliptic p n) a)
    _ ≤ Fintype.card ((GaloisField p n)ˣ) := by
      rw [← Nat.card_eq_fintype_card]
      exact orderOf_le_card
    _ = Fintype.card (GaloisField p n) - 1 := Fintype.card_units _

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- A generator of the elliptic torus is elliptic (rather than scalar). -/
private theorem generator_isElliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (g : K p n)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    GL2.IsElliptic (p := p) (n := n) (g : GL2 p n) := by
  classical
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  by_contra hge
  have hscalar := Etingof.ellipticSubgroup_not_elliptic_isScalar
    p n hp2 hn (g : GL2 p n) g.2 hge
  have hle := orderOf_le_q_sub_one_of_isScalar p n hn g hscalar
  have hord : orderOf g = Nat.card (K p n) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [card_ellipticSubgroup p n hn] at hord
  have hq := two_le_fieldCard p n hn
  have hqsq : Fintype.card (GaloisField p n) <
      Fintype.card (GaloisField p n) ^ 2 := by nlinarith
  have hgt := Nat.sub_lt_sub_right (by omega : 1 ≤ Fintype.card (GaloisField p n)) hqsq
  rw [← hord] at hgt
  exact (not_lt_of_ge hle) hgt

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- The square of a generator is still elliptic when the residue characteristic is odd. -/
private theorem generator_sq_isElliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (g : K p n)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    GL2.IsElliptic (p := p) (n := n) ((g ^ 2 : K p n) : GL2 p n) := by
  classical
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  by_contra hge
  have hscalar := Etingof.ellipticSubgroup_not_elliptic_isScalar
    p n hp2 hn ((g ^ 2 : K p n) : GL2 p n) (g ^ 2).2 hge
  have hle := orderOf_le_q_sub_one_of_isScalar p n hn (g ^ 2) hscalar
  have hord : orderOf g = Nat.card (K p n) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [card_ellipticSubgroup p n hn] at hord
  set q := Fintype.card (GaloisField p n) with hqdef
  have hq : 3 ≤ q := by
    rw [hqdef, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    have hp3 : 3 ≤ p := (hp.out.two_le.lt_or_eq.resolve_right hp2.symm).succ_le
    exact hp3.trans (Nat.le_pow (Nat.pos_of_ne_zero hn))
  have hqodd : Odd q := by
    rw [hqdef, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have htwo : 2 ∣ q ^ 2 - 1 := by
    refine ⟨2 * m ^ 2 + 2 * m, ?_⟩
    have halg : (2 * m + 1) ^ 2 = 2 * (2 * m ^ 2 + 2 * m) + 1 := by ring
    rw [hm]
    omega
  have hord2 : orderOf (g ^ 2) = orderOf g / 2 :=
    orderOf_pow_of_dvd (x := g) two_ne_zero (hord.symm ▸ htwo)
  have hhalf : 2 * ((q ^ 2 - 1) / 2) = q ^ 2 - 1 :=
    Nat.mul_div_cancel' htwo
  rw [hord2, hord] at hle
  have hqsub : q - 1 + 1 = q := by omega
  have hqsqsub : q ^ 2 - 1 + 1 = q ^ 2 :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega)))
  have hgt : 2 * (q - 1) < q ^ 2 - 1 := by nlinarith
  have hle2 := Nat.mul_le_mul_left 2 hle
  rw [hhalf] at hle2
  exact (not_lt_of_ge hle2) hgt

omit [DecidableEq (GaloisField p n)] in
/-- Isomorphic complementary-series representations have parameters in the same
Frobenius orbit. -/
theorem complementarySeriesRep_iso_parameters
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu mu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n,
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hmu : ∃ k : K p n,
      (mu k) ^ Fintype.card (GaloisField p n) ≠ mu k)
    (e : complementarySeriesRep p n nu hp2 hn hnu ≅
      complementarySeriesRep p n mu hp2 hn hmu) :
    mu = nu ∨ mu = complementaryCharFrobenius p n nu := by
  classical
  letI : IsCyclic (K p n) := ellipticSubgroup_isCyclic p n hn.ne'
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K p n)
  have hgEll := generator_isElliptic p n hp2 hn.ne' g hg
  have hg2Ell := generator_sq_isElliptic p n hp2 hn.ne' g hg
  have hsum :
      (nu g : ℂ) + (nu g : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu g : ℂ) + (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
    have h := congrFun (FDRep.char_iso e) (g : GL2 p n)
    rw [complementarySeriesRep_character, complementarySeriesRep_character,
      complementarySeriesChar_on_elliptic p n hp2 hn.ne' nu g hgEll,
      complementarySeriesChar_on_elliptic p n hp2 hn.ne' mu g hgEll] at h
    exact neg_injective h
  have hsum2 :
      (nu (g ^ 2) : ℂ) +
          (nu (g ^ 2) : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu (g ^ 2) : ℂ) +
          (mu (g ^ 2) : ℂ) ^ Fintype.card (GaloisField p n) := by
    have h := congrFun (FDRep.char_iso e) ((g ^ 2 : K p n) : GL2 p n)
    rw [complementarySeriesRep_character, complementarySeriesRep_character,
      complementarySeriesChar_on_elliptic p n hp2 hn.ne' nu (g ^ 2) hg2Ell,
      complementarySeriesChar_on_elliptic p n hp2 hn.ne' mu (g ^ 2) hg2Ell] at h
    exact neg_injective h
  have hsquare :
      (nu g : ℂ) ^ 2 +
          ((nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 =
        (mu g : ℂ) ^ 2 +
          ((mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 := by
    have hraw :
        (nu g : ℂ) ^ 2 + ((nu g : ℂ) ^ 2) ^ Fintype.card (GaloisField p n) =
          (mu g : ℂ) ^ 2 + ((mu g : ℂ) ^ 2) ^ Fintype.card (GaloisField p n) := by
      simpa only [map_pow, Units.val_pow_eq_pow_val] using hsum2
    have hpow_comm (x : ℂ) :
        (x ^ 2) ^ Fintype.card (GaloisField p n) =
          (x ^ Fintype.card (GaloisField p n)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [← hpow_comm, ← hpow_comm]
    exact hraw
  have hsumsq := congrArg (fun z : ℂ => z ^ 2) hsum
  have htwoprod :
      (2 : ℂ) * ((nu g : ℂ) *
          (nu g : ℂ) ^ Fintype.card (GaloisField p n)) =
        (2 : ℂ) * ((mu g : ℂ) *
          (mu g : ℂ) ^ Fintype.card (GaloisField p n)) := by
    calc
      _ = ((nu g : ℂ) +
            (nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 -
          ((nu g : ℂ) ^ 2 +
            ((nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2) := by ring
      _ = ((mu g : ℂ) +
            (mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 -
          ((mu g : ℂ) ^ 2 +
            ((mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2) := by
              rw [hsumsq, hsquare]
      _ = _ := by ring
  have hprod :
      (nu g : ℂ) * (nu g : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu g : ℂ) * (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwoprod
  have hroot :
      ((mu g : ℂ) - (nu g : ℂ)) *
        ((mu g : ℂ) - (nu g : ℂ) ^ Fintype.card (GaloisField p n)) = 0 := by
    calc
      _ = (mu g : ℂ) ^ 2 - (mu g : ℂ) *
            ((nu g : ℂ) + (nu g : ℂ) ^ Fintype.card (GaloisField p n)) +
          (nu g : ℂ) * (nu g : ℂ) ^ Fintype.card (GaloisField p n) := by ring
      _ = (mu g : ℂ) ^ 2 - (mu g : ℂ) *
            ((mu g : ℂ) + (mu g : ℂ) ^ Fintype.card (GaloisField p n)) +
          (mu g : ℂ) * (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
              rw [hsum, hprod]
      _ = 0 := by ring
  have hom_eq_of_generator (a b : K p n →* ℂˣ) (hab : a g = b g) : a = b := by
    apply MonoidHom.ext
    intro k
    obtain ⟨z, rfl⟩ := hg k
    simp only [map_zpow, hab]
  rcases mul_eq_zero.mp hroot with hsame | hfrob
  · left
    apply hom_eq_of_generator
    exact Units.ext (sub_eq_zero.mp hsame)
  · right
    apply hom_eq_of_generator
    apply Units.ext
    exact sub_eq_zero.mp hfrob

omit [DecidableEq (GaloisField p n)] in
/-- Two complementary-series representations are isomorphic exactly when their
parameters are equal or Frobenius-conjugate. -/
theorem complementarySeriesRep_iso_iff
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu mu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n,
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hmu : ∃ k : K p n,
      (mu k) ^ Fintype.card (GaloisField p n) ≠ mu k) :
    Nonempty (complementarySeriesRep p n nu hp2 hn hnu ≅
      complementarySeriesRep p n mu hp2 hn hmu) ↔
      mu = nu ∨ mu = complementaryCharFrobenius p n nu := by
  classical
  constructor
  · rintro ⟨e⟩
    exact complementarySeriesRep_iso_parameters p n hp2 hn nu mu hnu hmu e
  · rintro (rfl | rfl)
    · exact ⟨Iso.refl _⟩
    · exact ⟨complementarySeriesRepFrobeniusIso p n hp2 hn nu hnu hmu⟩

/-! ### The packaged complementary-series family -/

section Family

variable [NeZero n]

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
private instance complementarySeries_modulus_neZero :
    NeZero (Fintype.card (GaloisField p n) ^ 2 - 1) := by
  classical
  have hq := two_le_fieldCard p n (NeZero.ne n)
  constructor
  exact (Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq)).ne'

/-- The canonical one-per-Frobenius-orbit index type for complementary series. -/
abbrev ComplementaryIndex :=
  {x : ZMod (Fintype.card (GaloisField p n) ^ 2 - 1) //
    x ∈ Etingof.ComplementarySeries.cs_reps (Fintype.card (GaloisField p n))}

/-- The elliptic-torus character selected by a complementary-series index. -/
def complementaryIndexChar (i : ComplementaryIndex p n) : K p n →* ℂˣ :=
  complementaryCharOfParam p n (NeZero.ne n) i.1

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Every character selected by `ComplementaryIndex` is moved by Frobenius. -/
theorem complementaryIndexChar_moved (i : ComplementaryIndex p n) :
    ∃ k : K p n,
      (complementaryIndexChar p n i k) ^ Fintype.card (GaloisField p n) ≠
        complementaryIndexChar p n i k := by
  have hiMoved : Etingof.ComplementarySeries.cs_f
      (Fintype.card (GaloisField p n)) i.1 ≠ i.1 := by
    exact (Etingof.ComplementarySeries.mem_moved _ i.1).mp
      (Finset.mem_filter.mp i.2).1
  have hchar : complementaryCharFrobenius p n (complementaryIndexChar p n i) ≠
      complementaryIndexChar p n i :=
    (complementaryCharOfParam_moved_iff p n (NeZero.ne n) i.1).mpr hiMoved
  by_contra h
  apply hchar
  apply MonoidHom.ext
  intro k
  exact not_ne_iff.mp (not_exists.mp h k)

/-- The family of honest simple complementary-series representations indexed by the
canonical additive Frobenius transversal. -/
def complementaryFamily (hp2 : p ≠ 2) (i : ComplementaryIndex p n) :
    FDRep ℂ (GL2 p n) :=
  complementarySeriesRep p n (complementaryIndexChar p n i) hp2
    (Nat.pos_of_ne_zero (NeZero.ne n)) (complementaryIndexChar_moved p n i)

omit [DecidableEq (GaloisField p n)] in
/-- Every member of the packaged complementary-series family is simple. -/
theorem complementaryFamily_simple (hp2 : p ≠ 2) (i : ComplementaryIndex p n) :
    Simple (complementaryFamily p n hp2 i) := by
  classical
  unfold complementaryFamily
  infer_instance

omit [DecidableEq (GaloisField p n)] in
/-- Every member of the packaged family has dimension `q - 1`. -/
theorem complementaryFamily_finrank (hp2 : p ≠ 2) (i : ComplementaryIndex p n) :
    Module.finrank ℂ (complementaryFamily p n hp2 i).V = p ^ n - 1 := by
  classical
  exact finrank_complementarySeriesRep p n (complementaryIndexChar p n i) hp2
    (Nat.pos_of_ne_zero (NeZero.ne n)) (complementaryIndexChar_moved p n i)

omit [DecidableEq (GaloisField p n)] in
/-- Distinct transversal indices give non-isomorphic complementary-series
representations. -/
theorem complementaryFamily_injective (hp2 : p ≠ 2) :
    ∀ i j : ComplementaryIndex p n,
      Nonempty (complementaryFamily p n hp2 i ≅ complementaryFamily p n hp2 j) → i = j := by
  classical
  intro i j hij
  have horbit := (complementarySeriesRep_iso_iff p n hp2
    (Nat.pos_of_ne_zero (NeZero.ne n))
    (complementaryIndexChar p n i) (complementaryIndexChar p n j)
    (complementaryIndexChar_moved p n i) (complementaryIndexChar_moved p n j)).mp hij
  rcases horbit with hsame | hfrob
  · apply Subtype.ext
    have h := congrArg (complementaryCharParamEquiv p n (NeZero.ne n)) hsame
    rw [complementaryIndexChar, complementaryCharParamEquiv_ofParam,
      complementaryIndexChar, complementaryCharParamEquiv_ofParam] at h
    exact Multiplicative.ofAdd.injective h.symm
  · have hparam : j.1 = Etingof.ComplementarySeries.cs_f
        (Fintype.card (GaloisField p n)) i.1 := by
      have h := congrArg (complementaryCharParamEquiv p n (NeZero.ne n)) hfrob
      rw [complementaryIndexChar, complementaryCharParamEquiv_ofParam,
        complementaryCharParamEquiv_frobenius, complementaryIndexChar,
        complementaryCharParamEquiv_ofParam] at h
      change Multiplicative.ofAdd j.1 = Multiplicative.ofAdd
        (Etingof.ComplementarySeries.cs_f (Fintype.card (GaloisField p n)) i.1) at h
      exact Multiplicative.ofAdd.injective h
    have hiLt : i.1.val <
        (Etingof.ComplementarySeries.cs_f (Fintype.card (GaloisField p n)) i.1).val :=
      (Finset.mem_filter.mp i.2).2
    have hjLt : j.1.val <
        (Etingof.ComplementarySeries.cs_f (Fintype.card (GaloisField p n)) j.1).val :=
      (Finset.mem_filter.mp j.2).2
    rw [hparam, Etingof.ComplementarySeries.cs_f_involutive _
      (two_le_fieldCard p n (NeZero.ne n))] at hjLt
    omega

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- The complementary-series transversal has `q(q-1)/2` members. -/
theorem card_complementaryIndex :
    Nat.card (ComplementaryIndex p n) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,
    Etingof.ComplementarySeries.cs_reps_card _
      (two_le_fieldCard p n (NeZero.ne n))]

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- A packaged family of `q(q-1)/2` pairwise non-isomorphic simple complementary-series
representations, in the form consumed by completeness-by-counting. -/
theorem exists_complementary_family (hp2 : p ≠ 2) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (GL2 p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = Fintype.card (GaloisField p n) *
        (Fintype.card (GaloisField p n) - 1) / 2 := by
  classical
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  exact ⟨ComplementaryIndex p n, complementaryFamily p n hp2,
    complementaryFamily_simple p n hp2, complementaryFamily_injective p n hp2,
    card_complementaryIndex p n⟩

end Family

end Etingof.GL2

end
