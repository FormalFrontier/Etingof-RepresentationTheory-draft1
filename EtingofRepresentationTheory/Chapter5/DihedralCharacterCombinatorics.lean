import Mathlib

/-!
# Dihedral character combinatorics (infrastructure for Exercise 5.27.2)

For the dihedral classification (`Exercise5_27_2_Dihedral.lean`), Theorem 5.27.1 is
instantiated with `A = Multiplicative (ZMod N)`, `G = Multiplicative (ZMod 2)`, and `φ` the
inversion action of `G` on `A`. The dual `G`-action on the character group
`Â = (Multiplicative (ZMod N) →* ℂˣ)` is again inversion `χ ↦ χ⁻¹`. The final counts (number
of `1`- and `2`-dimensional irreducibles, split by the parity of `N`) come entirely from the
orbit combinatorics of this inversion involution on `Â`.

This file collects those reusable combinatorial/character-group facts. They do not depend
on the representation-theory engine `Theorem5_27_1.lean` and are proved standalone.

## Main results

* `card_charGroup`: the character group has `N` elements:
  `Nat.card (Multiplicative (ZMod N) →* ℂˣ) = N`.
* `card_selfInverse`: the number of self-inverse characters (`χ = χ⁻¹`, equivalently
  `χ ^ 2 = 1`) equals `Nat.gcd 2 N` (so `1` for odd `N`, `2` for even `N`).
* `card_notSelfInverse`: the number of non-self-inverse characters is `N - Nat.gcd 2 N`.
* `two_dvd_card_ne_of_involutive`: reusable, the points moved by any involution on a finite
  type split into `2`-element orbits, so their number is even.
* `two_dvd_card_notSelfInverse`: that number is even, so the non-fixed characters really do
  split into `2`-element orbits `{χ, χ⁻¹}`.
* `card_freeOrbitPairs`: the number of those `2`-element orbits is `(N - Nat.gcd 2 N) / 2`
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

/-- **General involution-orbit parity.** The points moved by an involution `f` on a finite
type split into `2`-element orbits `{a, f a}`, so their number is even. This is the reusable
`#fixed + 2·#free-pairs = card` counting principle specialised to divisibility of the
non-fixed count. -/
theorem two_dvd_card_ne_of_involutive {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → α} (hf : Function.Involutive f) :
    2 ∣ Fintype.card {a // f a ≠ a} := by
  set e : Equiv.Perm α := Function.Involutive.toPerm f hf with he
  have he2 : e ^ 2 = 1 := by ext a; simp [he, pow_two, Equiv.Perm.mul_apply, hf a]
  have hcard : Fintype.card {a // f a ≠ a} = e.support.card := by
    rw [Fintype.card_subtype]; congr 1
  rw [hcard, ← Equiv.Perm.sum_cycleType]
  apply Multiset.dvd_sum
  intro n hn
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hd : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one he2)
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- **The non-fixed characters come in pairs.** The involution `χ ↦ χ⁻¹` splits the characters
with `χ ≠ χ⁻¹` into `2`-element orbits `{χ, χ⁻¹}`, so their number `N - Nat.gcd 2 N` is even. -/
theorem two_dvd_card_notSelfInverse :
    2 ∣ Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h := two_dvd_card_ne_of_involutive
    (f := (·⁻¹ : (Multiplicative (ZMod N) →* ℂˣ) → _)) inv_involutive
  rwa [Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => ne_comm))] at h

/-- **Free-orbit count.** Under the involution `χ ↦ χ⁻¹`, the number of `2`-element orbits
(`χ ≠ χ⁻¹`) equals `(N - Nat.gcd 2 N) / 2`: `(N-1)/2` for odd `N` and `(N-2)/2` for even `N`.
The halving is exact by `two_dvd_card_notSelfInverse`. -/
theorem card_freeOrbitPairs :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} / 2 = (N - Nat.gcd 2 N) / 2 := by
  rw [card_notSelfInverse]

end Etingof.DihedralCharacterCombinatorics
