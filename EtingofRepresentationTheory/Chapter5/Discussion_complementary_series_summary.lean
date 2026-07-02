import Mathlib

/-!
# Discussion: all `q² − 1` irreducible representations of `GL₂(𝔽_q)` found

This file records the closing summary of Etingof's construction of the irreducible
representations of `G = GL₂(𝔽_q)`:

> We have thus found `q − 1` 1-dimensional representations of `G`,
> `q(q−1)/2` principal series representations, and `q(q−1)/2` complementary series
> representations, for a total of `q² − 1` representations, i.e., the number of
> conjugacy classes in `G`. This implies that we have in fact found all irreducible
> representations of `GL₂(𝔽_q)`.

The argument is a *completeness-by-counting* argument with three ingredients:

1. **The constructed count.** The three families contribute
   `(q − 1) + q(q−1)/2 + q(q−1)/2` pairwise non-isomorphic irreducibles. This total
   equals `q² − 1`; the elementary arithmetic identity is `constructed_irrep_count`
   below (genuinely proved).

2. **The class count.** The number of conjugacy classes of `GL₂(𝔽_q)` is `q² − 1`.
   This is the fact whose formalization is the acknowledged gap in the surrounding
   discussion (see the Discussion 5.25.1 conjugacy-class enumeration): the
   `GL2ConjugacyClasses` file counts the *elements* of each of the four conjugacy
   types, but the count of *classes* — `q − 1` scalar, `q − 1` parabolic,
   `(q−1)(q−2)/2` split-semisimple, `q(q−1)/2` elliptic, again summing to `q² − 1`
   — is not yet assembled. We record the claim as the `Prop`-valued
   `foundAllIrreducibles` rather than asserting it with a `sorry`.

3. **The irreducibles ↔ classes bridge.** Over an algebraically closed field of
   characteristic `0` (here `ℂ`), the number of isomorphism classes of irreducible
   representations of a finite group equals the number of its conjugacy classes.
   This bridge is standard but is *not* packaged in Mathlib (there is
   `FDRep.simple_iff_char_is_norm_one` and `FDRep.char_orthonormal`, but no
   `#(irreducible FDRep ℂ G) = #(ConjClasses G)` theorem).

Combining (1)–(3): the `q² − 1` constructed irreducibles are pairwise non-isomorphic
and number exactly the conjugacy classes, hence exhaust the irreducibles.

Per the fidelity-sweep convention, the out-of-reach conjunction (2) is recorded as a
`Prop`-valued definition against the real group object `GL₂(F)`, paired with the
genuinely provable arithmetic of (1). Discharging `foundAllIrreducibles` is tracked
in issue #5681 (and depends on the Discussion 5.25.1 conjugacy-class count).
-/

namespace Etingof.GL2

/-- **The constructed count.** The three families of irreducible representations of
`GL₂(𝔽_q)` — the `q − 1` one-dimensional representations, the `q(q−1)/2` principal
series representations, and the `q(q−1)/2` complementary series representations —
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
`q² − 1` — matching the total number `(q − 1) + q(q−1)/2 + q(q−1)/2 = q² − 1` of
constructed irreducibles (`constructed_irrep_count`).

Since over `ℂ` the number of irreducible representations of a finite group equals its
number of conjugacy classes, this equality is exactly what forces the constructed
representations to exhaust the irreducibles of `GL₂(𝔽_q)`.

This is a `Prop`-valued *statement*, not an assertion: it names the precise
formulation without proving it. Its proof is the acknowledged gap of the surrounding
discussion (the Discussion 5.25.1 conjugacy-class enumeration), tracked in issue
#5681. -/
def foundAllIrreducibles (F : Type*) [Field F] [Fintype F] : Prop :=
  Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) F)) = Fintype.card F ^ 2 - 1

end Etingof.GL2
