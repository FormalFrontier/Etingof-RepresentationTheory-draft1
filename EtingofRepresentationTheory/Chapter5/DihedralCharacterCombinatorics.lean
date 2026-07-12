import Mathlib

/-!
# Dihedral character combinatorics (infrastructure for Exercise 5.27.2)

For the dihedral classification (`Exercise5_27_2_Dihedral.lean`), Theorem 5.27.1 is
instantiated with `A = Multiplicative (ZMod N)`, `G = Multiplicative (ZMod 2)`, and `φ` the
inversion action of `G` on `A`. The dual `G`-action on the character group
`Â = (Multiplicative (ZMod N) →* ℂˣ)` is again inversion `χ ↦ χ⁻¹`. The final counts (number
of `1`- and `2`-dimensional irreducibles, split by the parity of `N`) come entirely from the
orbit combinatorics of this inversion involution on `Â`.

This file collects those reusable combinatorial/character-group facts. They do **not** depend
on the representation-theory engine `Theorem5_27_1.lean` and are proved standalone.

## Main results

* `card_charGroup` — the character group has `N` elements:
  `Nat.card (Multiplicative (ZMod N) →* ℂˣ) = N`.
* `card_selfInverse` — the number of self-inverse characters (`χ = χ⁻¹`, equivalently
  `χ ^ 2 = 1`) equals `Nat.gcd 2 N` (so `1` for odd `N`, `2` for even `N`).
* `card_notSelfInverse` — the number of non-self-inverse characters is `N - Nat.gcd 2 N`.
* `two_dvd_card_notSelfInverse` — that number is even, so the non-fixed characters really do
  split into `2`-element orbits `{χ, χ⁻¹}`.
* `card_freeOrbitPairs` — the number of those `2`-element orbits is `(N - Nat.gcd 2 N) / 2`
  (i.e. `(N-1)/2` for odd `N` and `(N-2)/2` for even `N`).

The character group is (non-canonically) isomorphic to the finite cyclic group
`Multiplicative (ZMod N)` because `ℂ` has enough roots of unity
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`); the counts follow from the
cyclic-group kernel formula `IsCyclic.card_powMonoidHom_ker`.
-/

namespace Etingof.DihedralCharacterCombinatorics

variable (N : ℕ) [NeZero N]

/-- The exponent of the finite group `Multiplicative (ZMod N)` is nonzero in `ℂ`; this supplies
the `HasEnoughRootsOfUnity ℂ _` instance that the duality results require. -/
instance instNeZeroExponent :
    NeZero ((Monoid.exponent (Multiplicative (ZMod N)) : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

/-- A (non-canonical) self-duality of the character group of the cyclic group `ZMod N`: since
`ℂ` has enough roots of unity, `Â = (Multiplicative (ZMod N) →* ℂˣ)` is isomorphic to
`Multiplicative (ZMod N)` itself. -/
noncomputable def charSelfEquiv :
    (Multiplicative (ZMod N) →* ℂˣ) ≃* Multiplicative (ZMod N) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Multiplicative (ZMod N)) ℂ).some

instance instFiniteCharGroup : Finite (Multiplicative (ZMod N) →* ℂˣ) :=
  Finite.of_equiv _ (charSelfEquiv N).symm.toEquiv

instance instIsCyclicCharGroup : IsCyclic (Multiplicative (ZMod N) →* ℂˣ) :=
  isCyclic_of_surjective (charSelfEquiv N).symm (charSelfEquiv N).symm.surjective

/-- **Character-group cardinality.** The character group of the cyclic group `ZMod N` has `N`
elements. -/
theorem card_charGroup : Nat.card (Multiplicative (ZMod N) →* ℂˣ) = N := by
  rw [Nat.card_congr (charSelfEquiv N).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

/-- **Fixed-point (self-inverse) count.** The number of characters `χ` with `χ = χ⁻¹`
(equivalently `χ ^ 2 = 1`) equals `Nat.gcd 2 N`: `1` when `N` is odd and `2` when `N` is
even. These are the characters factoring through the unique quotient of order `gcd(2, N)`. -/
theorem card_selfInverse :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} = Nat.gcd 2 N := by
  have hEquiv :
      {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} ≃
        (powMonoidHom 2 : (Multiplicative (ZMod N) →* ℂˣ) →* _).ker :=
    Equiv.subtypeEquivRight fun χ => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_two, mul_eq_one_iff_eq_inv]
  rw [Nat.card_congr hEquiv, IsCyclic.card_powMonoidHom_ker, card_charGroup, Nat.gcd_comm]

/-- **Non-fixed count.** The number of characters `χ` with `χ ≠ χ⁻¹` is `N - Nat.gcd 2 N`. -/
theorem card_notSelfInverse :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} = N - Nat.gcd 2 N := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  have hsplit :
      Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹}
        = Fintype.card (Multiplicative (ZMod N) →* ℂˣ)
          - Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} :=
    Fintype.card_subtype_compl (fun χ => χ = χ⁻¹)
  rw [Nat.card_eq_fintype_card, hsplit, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_charGroup, card_selfInverse]

/-- **The non-fixed characters come in pairs.** Their number `N - Nat.gcd 2 N` is even, so the
involution `χ ↦ χ⁻¹` really does split them into `2`-element orbits `{χ, χ⁻¹}`. -/
theorem two_dvd_card_notSelfInverse :
    2 ∣ Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} := by
  rw [card_notSelfInverse]
  have hcases : (Nat.gcd 2 N = 2 ∧ 2 ∣ N) ∨ (Nat.gcd 2 N = 1 ∧ ¬ 2 ∣ N) := by
    by_cases h : 2 ∣ N
    · exact Or.inl ⟨Nat.gcd_eq_left h, h⟩
    · exact Or.inr ⟨Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)), h⟩
  omega

/-- **Free-orbit count.** Under the involution `χ ↦ χ⁻¹`, the number of `2`-element orbits
(`χ ≠ χ⁻¹`) equals `(N - Nat.gcd 2 N) / 2`: `(N-1)/2` for odd `N` and `(N-2)/2` for even `N`.
The halving is a genuine orbit count by `two_dvd_card_notSelfInverse`. -/
theorem card_freeOrbitPairs :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} / 2 = (N - Nat.gcd 2 N) / 2 := by
  rw [card_notSelfInverse]

end Etingof.DihedralCharacterCombinatorics
