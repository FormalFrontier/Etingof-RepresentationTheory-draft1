import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2ConjugacyClassCount
import EtingofRepresentationTheory.Chapter5.IrrepCountConjClasses
import EtingofRepresentationTheory.Chapter5.GL2PrincipalFamily
import EtingofRepresentationTheory.Chapter5.GL2ComplementarySeriesOrbits
import EtingofRepresentationTheory.Infrastructure.CompletenessByCounting

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
   representations of a finite group equals the number of its conjugacy classes. This
   `#irreps = #ConjClasses` identity is now **proved** in
   `Etingof.card_irrep_eq_card_conjClasses` (dimension of the center of `ℂ[G]` equals
   `#ConjClasses G` via the class-sum basis, together with Wedderburn–Artin over `ℂ`), so
   the completeness conclusion no longer needs it as a hypothesis.

Combining (1)–(3): the `q² − 1` constructed irreducibles are pairwise non-isomorphic
and number exactly the conjugacy classes, hence exhaust the irreducibles.

## What is proved here

* `constructed_irrep_count` — the arithmetic identity `(q−1) + q(q−1)/2 + q(q−1)/2 = q²−1`.
* `foundAllIrreducibles_galoisField` — the recorded claim (2), discharged: the number of
  conjugacy classes of `GL₂(GaloisField p n)` is `q² − 1`, for odd `p` and `n ≠ 0`.
* `constructedCount_eq_card_conjClasses` — the load-bearing **completeness-by-counting**
  core: the constructed total equals the number of conjugacy classes of `GL₂(𝔽_q)`.
* `constructed_irreps_complete` — the completeness conclusion, phrased with the
  `#irreps = #ConjClasses` bridge as an explicit hypothesis (kept for the abstract
  `numIrreps` interface).
* `constructed_irreps_complete_unconditional` — the same conclusion **unconditionally**:
  the bridge is discharged by `Etingof.card_irrep_eq_card_conjClasses`, giving a faithful
  index type `Irrep` for the irreducible `ℂ`-representations of `GL₂(𝔽_q)` (carrying the
  Wedderburn block decomposition of `ℂ[GL₂(𝔽_q)]`) whose cardinality is the constructed
  total.
* `card_irreps_eq_q_sq_sub_one` — the `q² − 1` closed form: the number of irreducible
  `ℂ`-representations of `GL₂(𝔽_q)` is exactly `q² − 1`, unconditionally.
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

/-- **Completeness of the constructed families (unconditional).** Etingof's payoff
sentence "we have in fact found all irreducible representations of `GL₂(𝔽_q)`", now with
no standing hypotheses.

The `bridge` hypothesis of `constructed_irreps_complete` — that over `ℂ` the number of
irreducible representations of `GL₂(𝔽_q)` equals its number of conjugacy classes — is
discharged by the general character-theoretic counting identity
`Etingof.card_irrep_eq_card_conjClasses`. That theorem supplies a faithful index type
`Irrep` for the isomorphism classes of irreducible `ℂ`-representations of
`GL₂(𝔽_q)`: `Irrep` carries a nonzero block-size family `d` and an algebra isomorphism
`ℂ[GL₂(𝔽_q)] ≃ₐ[ℂ] Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ`, so each `j : Irrep` names one
Wedderburn matrix factor, i.e. one isomorphism class of irreducible representation.

The conclusion is unconditional: for `q = pⁿ` with `p` odd and `n ≠ 0`, the number of
isomorphism classes of irreducible `ℂ`-representations of `GL₂(𝔽_q)` is exactly the
constructed total `(q − 1) + q(q−1)/2 + q(q−1)/2 = q² − 1`. Since the three constructed
families are pairwise non-isomorphic and number exactly this total, they exhaust the
irreducibles. -/
theorem constructed_irreps_complete_unconditional (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (Irrep : Type) (_ : Fintype Irrep),
      (∃ d : Irrep → ℕ, (∀ j, d j ≠ 0) ∧
        Nonempty (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
          ≃ₐ[ℂ] Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ)) ∧
      Nat.card Irrep = (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  obtain ⟨Irrep, hFin, hcard, hdata⟩ :=
    Etingof.card_irrep_eq_card_conjClasses
      (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
  exact ⟨Irrep, hFin, hdata,
    constructed_irreps_complete p n (Nat.card Irrep) hcard hp2 hn⟩

/-- **The number of irreducible `ℂ`-representations of `GL₂(𝔽_q)` is `q² − 1`
(unconditional closed form).** For `q = pⁿ` with `p` odd and `n ≠ 0`, there is a faithful
index type `Irrep` for the isomorphism classes of irreducible `ℂ`-representations of
`GL₂(𝔽_q)` with `Nat.card Irrep = q² − 1`. This is the `q² − 1` restatement of
`constructed_irreps_complete_unconditional`, folding the constructed total through
`constructed_irrep_count`. -/
theorem card_irreps_eq_q_sq_sub_one (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (Irrep : Type) (_ : Fintype Irrep),
      Nat.card Irrep = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  obtain ⟨Irrep, hFin, _, hcard⟩ := constructed_irreps_complete_unconditional p n hp2 hn
  exact ⟨Irrep, hFin, hcard.trans (constructed_irrep_count _ Fintype.card_pos)⟩

/-! ### Completeness at the level of actual representations

The theorems above count an abstract Wedderburn index type. What Etingof's sentence claims is
stronger: the *constructed* representations exhaust the irreducibles. The two statements below
work with honest `FDRep ℂ (GL₂ 𝔽_q)` objects instead of an index type — the first exhibits a
complete list of `q² − 1` irreducibles, the second is the reduction that turns the construction
of the three families into the completeness conclusion. -/

open CategoryTheory in
/-- **A complete list of `q² − 1` irreducible `ℂ`-representations of `GL₂(𝔽_q)`.** For
`q = pⁿ` with `p` odd and `n ≠ 0` there are `m` pairwise non-isomorphic simple
`FDRep ℂ (GL₂ 𝔽_q)` objects `V i` such that *every* simple `FDRep ℂ (GL₂ 𝔽_q)` is isomorphic
to one of them, and `m = q² − 1`.

Unlike `constructed_irreps_complete_unconditional`, which counts an abstract index type, this
statement is about representations: it carries the exhaustiveness clause
`∀ U, Simple U → ∃ i, Nonempty (U ≅ V i)`. It does not identify the `V i` with the
one-dimensional, principal-series, and complementary-series families; that identification is
what `constructed_families_exhaust` below reduces to a finite amount of construction work. -/
theorem exists_complete_simples (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (m : ℕ) (V : Fin m → FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ U, Simple U → ∃ i, Nonempty (U ≅ V i)) ∧
      m = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  classical
  haveI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := inferInstance
  haveI : Invertible
      ((Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) : ℂ)) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  obtain ⟨m, V, hsimp, hinj, hsurj, hm⟩ :=
    Etingof.Corollary4_2_2 (k := ℂ)
      (G := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
  refine ⟨m, V, hsimp, hinj, hsurj, ?_⟩
  rw [hm, ← Nat.card_eq_fintype_card]
  exact _root_.GL2.card_conjClasses_eq hp2 hn

open CategoryTheory in
/-- **The constructed families exhaust the irreducibles (reduction).** Etingof's payoff
sentence, with the counting argument discharged and only the construction left as hypotheses.

Given *any* family `W` of `(q − 1) + q(q−1)/2 + q(q−1)/2` representations of `GL₂(𝔽_q)` over
`ℂ` that are simple and pairwise non-isomorphic, every simple `FDRep ℂ (GL₂ 𝔽_q)` is
isomorphic to one of them. In particular, once the `q − 1` one-dimensional representations,
the `q(q−1)/2` principal series representations, and the `q(q−1)/2` complementary series
representations are packaged as one such family, "we have in fact found all irreducible
representations of `GL₂(𝔽_q)`" follows with no further work.

Equal cardinalities alone do not give this: the count has to be turned into an injection into
the set of isomorphism classes and then a pigeonhole. That is
`Etingof.exhaustive_of_card_eq_card_conjClasses`, applied here to the class count
`constructedCount_eq_card_conjClasses`. -/
theorem constructed_families_exhaust (hp2 : p ≠ 2) (hn : n ≠ 0) {N : ℕ}
    (W : Fin N → FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)))
    (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hN : N = (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2) :
    ∀ U, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  classical
  haveI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := inferInstance
  haveI : Invertible
      ((Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) : ℂ)) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  exact Etingof.exhaustive_of_card_eq_card_conjClasses W hWsimple hWnoniso
    (hN.trans (constructedCount_eq_card_conjClasses p n hp2 hn))

/-! ### The constructed families themselves are complete -/

open CategoryTheory

/-- The joint index type for all representations constructed in §5.25: the left summand
contains the one-dimensional and principal-series representations, and the right summand
contains one complementary-series representation for each Frobenius orbit. -/
abbrev ConstructedComplementaryIndex (hn : n ≠ 0) :=
  let _ : NeZero n := ⟨hn⟩
  ComplementaryIndex p n

abbrev ConstructedIndex (hn : n ≠ 0) :=
  PrincipalIndex p n ⊕ ConstructedComplementaryIndex p n hn

/-- The actual family of all representations constructed in §5.25. -/
noncomputable def constructedFamily (hp2 : p ≠ 2) (hn : n ≠ 0)
    (i : ConstructedIndex p n hn) :
    FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  exact match i with
    | .inl j => principalFamily p n j
    | .inr j => complementaryFamily p n hp2 j

/-- Every member of the combined constructed family is irreducible. -/
theorem constructedFamily_simple (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ i : ConstructedIndex p n hn, Simple (constructedFamily p n hp2 hn i) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro (i | i)
  · simpa [constructedFamily] using principalFamily_simple p n hn i
  · simpa [constructedFamily] using complementaryFamily_simple p n hp2 i

/-- No one-dimensional or principal-series representation is isomorphic to a complementary
series representation. Their respective dimensions are `1`, `q`, or `q + 1`, and `q - 1`;
odd characteristic and `n ≠ 0` give `q ≥ 3`. -/
theorem principalFamily_not_iso_complementaryFamily
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (i : PrincipalIndex p n) (j : ConstructedComplementaryIndex p n hn) :
    ¬ Nonempty (constructedFamily p n hp2 hn (.inl i) ≅
      constructedFamily p n hp2 hn (.inr j)) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro ⟨e⟩
  have hdim := finrank_eq_of_iso e
  rw [show constructedFamily p n hp2 hn (.inl i) = principalFamily p n i by
      simp [constructedFamily],
    show constructedFamily p n hp2 hn (.inr j) = complementaryFamily p n hp2 j by
      simp [constructedFamily],
    principalFamily_finrank p n hn i,
    complementaryFamily_finrank p n hp2 j] at hdim
  have hpprime : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := (hpprime.two_le.lt_or_eq.resolve_right hp2.symm).succ_le
  have hq3 : 3 ≤ p ^ n := hp3.trans (Nat.le_pow (Nat.pos_of_ne_zero hn))
  rcases i with i | i
  · simp at hdim
    omega
  · rcases i with i | i
    · simp at hdim
      omega
    · simp at hdim
      omega

/-- The combined constructed family has no repetitions up to isomorphism. -/
theorem constructedFamily_injective (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ i j : ConstructedIndex p n hn,
      Nonempty (constructedFamily p n hp2 hn i ≅ constructedFamily p n hp2 hn j) →
        i = j := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (principalFamily_injective p n hn i j h)
  · exact absurd h (principalFamily_not_iso_complementaryFamily p n hp2 hn i j)
  · exact absurd (Nonempty.map Iso.symm h)
      (principalFamily_not_iso_complementaryFamily p n hp2 hn j i)
  · apply congrArg Sum.inr
    apply complementaryFamily_injective p n hp2 i j
    simpa [constructedFamily] using h

/-- The combined family has exactly the constructed total
`(q - 1) + q(q - 1)/2 + q(q - 1)/2` members. -/
theorem card_constructedIndex (hn : n ≠ 0) :
    Nat.card (ConstructedIndex p n hn) =
      (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2 := by
  letI : NeZero n := ⟨hn⟩
  rw [Nat.card_sum, card_principalIndex p n hn,
    card_complementaryIndex p n, ← Nat.card_eq_fintype_card,
    GaloisField.card p n hn]

/-- **The representations constructed in §5.25 are exactly all irreducibles.** Every simple
finite-dimensional complex representation of `GL₂(𝔽_q)` is isomorphic to exactly one member
of the combined one-dimensional, principal-series, and complementary-series family. -/
theorem constructed_irreps_complete_final (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ U : FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)), Simple U →
      ∃! i : ConstructedIndex p n hn,
        Nonempty (U ≅ constructedFamily p n hp2 hn i) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (ConstructedIndex p n hn) := Fintype.ofFinite _
  let e := Fintype.equivFin (ConstructedIndex p n hn)
  let W : Fin (Fintype.card (ConstructedIndex p n hn)) →
      FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    fun j => constructedFamily p n hp2 hn (e.symm j)
  have hWsimple : ∀ j, Simple (W j) := by
    intro j
    exact constructedFamily_simple p n hp2 hn (e.symm j)
  have hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j := by
    intro i j hij
    apply e.symm.injective
    exact constructedFamily_injective p n hp2 hn (e.symm i) (e.symm j) hij
  have hcard : Fintype.card (ConstructedIndex p n hn) =
      (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_constructedIndex p n hn
  intro U hU
  obtain ⟨j, hj⟩ := constructed_families_exhaust p n hp2 hn W hWsimple hWnoniso hcard U hU
  refine ⟨e.symm j, hj, ?_⟩
  intro i hi
  apply constructedFamily_injective p n hp2 hn i (e.symm j)
  exact ⟨hi.some.symm ≪≫ hj.some⟩

end GaloisField

end Etingof.GL2
