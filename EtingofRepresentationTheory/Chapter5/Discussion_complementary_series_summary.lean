import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2ConjugacyClassCount

/-!
# Discussion: all `q² − 1` irreducible representations of `GL₂(𝔽_q)` found

This file records the closing summary of Etingof's construction of the irreducible
representations of `G = GL₂(𝔽_q)`:

> We have thus found `q − 1` 1-dimensional representations of `G`,
> `q(q−1)/2` principal series representations, and `q(q−1)/2` complementary series
> representations, for a total of `q² − 1` representations, i.e., the number of
> conjugacy classes in `G`. This implies that we have in fact found all irreducible
> representations of `GL₂(𝔽_q)`.

The argument counts completeness with three ingredients:

1. **The constructed count.** The three families contribute
   `(q − 1) + q(q−1)/2 + q(q−1)/2` pairwise non-isomorphic irreducibles. This total
   equals `q² − 1`; the elementary arithmetic identity is `constructed_irrep_count`
   below.

2. **The class count.** The number of conjugacy classes of `GL₂(𝔽_q)` is `q² − 1`.
   The `GL2ConjugacyClasses` file counts the elements of each of the four conjugacy
   types; `GL2ConjugacyClassCount` counts the *classes* of each type, `q − 1` scalar,
   `q − 1` parabolic, `(q−1)(q−2)/2` split-semisimple, `q(q−1)/2` elliptic, summing to
   `q² − 1`, in `GL2.card_conjClasses_eq` (odd characteristic). The `Prop`-valued
   `foundAllIrreducibles` recording this equality is now **discharged** for
   `𝔽_q = GaloisField p n` by `foundAllIrreducibles_galoisField`, and the count is
   matched to the constructed total in `constructedCount_eq_card_conjClasses`.

3. **The irreducibles and classes agree.** Over an algebraically closed field of
   characteristic `0` (here `ℂ`), the number of isomorphism classes of irreducible
   representations of a finite group equals the number of its conjugacy classes.
   This is standard but is not packaged in Mathlib (there is
   `FDRep.simple_iff_char_is_norm_one` and `FDRep.char_orthonormal`, but no
   `#(irreducible FDRep ℂ G) = #(ConjClasses G)` theorem). We state the completeness
   conclusion `constructed_irreps_complete` taking this single standard bridge as an
   explicit hypothesis; proving the bridge unconditionally (dimension of the center of
   `ℂ[G]` equals `#ConjClasses G` via the class-sum basis, together with
   Wedderburn–Artin over `ℂ`) is tracked as follow-up work.

Combining (1)–(3): the `q² − 1` constructed irreducibles are pairwise non-isomorphic
and number exactly the conjugacy classes, hence exhaust the irreducibles.

## What is proved here

* `constructed_irrep_count` — the arithmetic identity `(q−1) + q(q−1)/2 + q(q−1)/2 = q²−1`.
* `foundAllIrreducibles_galoisField` — the recorded claim (2), discharged: the number of
  conjugacy classes of `GL₂(GaloisField p n)` is `q² − 1`, for odd `p` and `n ≠ 0`.
* `constructedCount_eq_card_conjClasses` — the load-bearing **completeness-by-counting**
  core: the constructed total equals the number of conjugacy classes of `GL₂(𝔽_q)`.
* `constructed_irreps_complete` — the completeness conclusion: modulo the standard
  `#irreps = #ConjClasses` bridge (input as a hypothesis, since Mathlib lacks it), the
  number of irreducible representations of `GL₂(𝔽_q)` is exactly the constructed total.
-/

namespace Etingof.GL2

/-- **The constructed count.** The three families of irreducible representations of
`GL₂(𝔽_q)`, the `q − 1` one-dimensional representations, the `q(q−1)/2` principal
series representations, and the `q(q−1)/2` complementary series representations,
number `q² − 1` in total, for any field size `q ≥ 1`.

This is the arithmetic underpinning Etingof's completeness-by-counting summary:
`(q − 1) + q(q−1)/2 + q(q−1)/2 = q² − 1`. (Both `q(q−1)/2` terms are exact natural
divisions since `q(q−1)` is always even.) -/
theorem constructed_irrep_count (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) + q * (q - 1) / 2 + q * (q - 1) / 2 = q ^ 2 - 1 := by
  have he : 2 ∣ q * (q - 1) := by
    rcases Nat.even_or_odd q with h | h
    · exact Dvd.dvd.mul_right h.two_dvd _
    · have : Even (q - 1) := by rcases h with ⟨k, hk⟩; exact ⟨k, by omega⟩
      exact Dvd.dvd.mul_left this.two_dvd _
  obtain ⟨m, hm⟩ := he
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq, h1] at hm ⊢
  nlinarith [hm]

/-- **Completeness-by-counting for `GL₂(F)` (recorded claim).** The number of
conjugacy classes of `GL₂(F)`, for a finite field `F` with `q = |F|` elements, equals
`q² − 1`, matching the total number `(q − 1) + q(q−1)/2 + q(q−1)/2 = q² − 1` of
constructed irreducibles (`constructed_irrep_count`).

Since over `ℂ` the number of irreducible representations of a finite group equals its
number of conjugacy classes, this equality is exactly what forces the constructed
representations to exhaust the irreducibles of `GL₂(𝔽_q)`.

This is a `Prop`-valued statement: it names the precise formulation without proving
it. Its proof is the Discussion 5.25.1 conjugacy-class enumeration. -/
def foundAllIrreducibles (F : Type*) [Field F] [Fintype F] : Prop :=
  Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) F)) = Fintype.card F ^ 2 - 1

section GaloisField

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [Fintype (GaloisField p n)]

/-- **`foundAllIrreducibles` discharged for `𝔽_q = GaloisField p n`.** For a prime power
`q = pⁿ` with `p` odd and `n ≠ 0`, the number of conjugacy classes of `GL₂(𝔽_q)` is
`q² − 1`. This turns the recorded `Prop`-valued claim `foundAllIrreducibles` into a
proved theorem for the fields it is about, via the fully-proved conjugacy-class count
`GL2.card_conjClasses_eq`. -/
theorem foundAllIrreducibles_galoisField (hp2 : p ≠ 2) (hn : n ≠ 0) :
    foundAllIrreducibles (GaloisField p n) := by
  classical
  unfold foundAllIrreducibles
  exact _root_.GL2.card_conjClasses_eq hp2 hn

/-- **Completeness by counting (the core, fully proved).** The constructed total
`(q − 1) + q(q−1)/2 + q(q−1)/2` of one-dimensional, principal-series, and
complementary-series irreducibles equals the number of conjugacy classes of
`GL₂(𝔽_q)`, for `q = pⁿ` with `p` odd and `n ≠ 0`. Both sides equal `q² − 1`: the left
by `constructed_irrep_count`, the right by `GL2.card_conjClasses_eq`.

This is Etingof's completeness-by-counting content that does not need the character
theory: the number of constructed families is *exactly* the number of conjugacy
classes. -/
theorem constructedCount_eq_card_conjClasses (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      = Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))) := by
  classical
  exact (constructed_irrep_count _ Fintype.card_pos).trans
    (_root_.GL2.card_conjClasses_eq hp2 hn).symm

/-- **Completeness of the constructed families (modulo the standard bridge).** Etingof's
payoff sentence "we have in fact found all irreducible representations of `GL₂(𝔽_q)`".

Over `ℂ` the number of irreducible representations of a finite group equals its number
of conjugacy classes — a standard fact not yet in Mathlib. Taking that single input as
the hypothesis `bridge` (for `G = GL₂(𝔽_q)`), the number of irreducible representations
of `GL₂(𝔽_q)` equals the constructed total `(q − 1) + q(q−1)/2 + q(q−1)/2`. Since the
three constructed families are pairwise non-isomorphic and number exactly this total,
they exhaust the irreducibles.

Proving `bridge` unconditionally is the outstanding follow-up: `dim Z(ℂ[G]) =
#ConjClasses G` via the class-sum basis, plus Wedderburn–Artin over `ℂ`
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`) counting simple modules by
factors. -/
theorem constructed_irreps_complete (numIrreps : ℕ)
    (bridge : numIrreps =
      Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))))
    (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numIrreps = (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 :=
  bridge.trans (constructedCount_eq_card_conjClasses p n hp2 hn).symm

end GaloisField

end Etingof.GL2
