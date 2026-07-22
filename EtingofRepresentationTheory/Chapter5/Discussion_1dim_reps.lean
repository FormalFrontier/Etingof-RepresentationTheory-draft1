import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_25_1

/-!
# Discussion 5.25: 1-dimensional representations of GL₂(𝔽_q)

Etingof's discussion following Proposition 5.25.1 observes that, since
`[G, G] = SL₂(𝔽_q)` (Proposition 5.25.1) and `det : G → 𝔽_q^×` is surjective with
kernel `SL₂`, one has
`G / [G, G] ≅ 𝔽_q^×  via  g ↦ det(g)`.
Consequently every **1-dimensional** representation of `G = GL₂(𝔽_q)` has the form
`ρ(g) = ξ(det g)` for a unique character `ξ : 𝔽_q^× → ℂ^×`, and there are exactly
`q - 1` of them (denoted `ℂ_ξ`).

## Formalization

A 1-dimensional complex representation of `G` is precisely a group homomorphism
`G →* ℂˣ` (the action on a 1-dimensional space `ℂ` is scalar, so it is determined
by, and equivalent to, a homomorphism into the units `ℂˣ = GL₁(ℂ)`). The character
`ξ` of `𝔽_q^×` is a homomorphism `(GaloisField p n)ˣ →* ℂˣ`.

* `characterCompDetEquiv` — the bijection `ξ ↦ ξ ∘ det` from characters of `𝔽_q^×`
  to 1-dimensional representations of `G`. This is the classification statement:
  every 1-dim rep is `ξ ∘ det` for a **unique** `ξ`.
* `characterCompDetEquiv_apply` — records the explicit form `ρ(g) = ξ(det g)`.
* `card_oneDimRep` — there are exactly `q - 1` one-dimensional representations.

The key inputs are `Etingof.Proposition5_25_1` (`[G,G] = SL₂`, hence
`ker det = [G,G]`), surjectivity of `det`, and, for the count, Mathlib's duality
`Nat.card (A →* ℂˣ) = Nat.card A` for a finite abelian group `A`.

## Mathlib correspondence

Uses `Matrix.GeneralLinearGroup.det`, `MonoidHom.liftOfSurjective`,
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, `Nat.card_units`.
-/

open Matrix

namespace Etingof.Discussion_1dim_reps

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- `G = GL₂(𝔽_q)`, the group whose 1-dimensional representations we classify. -/
abbrev G := GeneralLinearGroup (Fin 2) (GaloisField p n)

/-- The determinant homomorphism `det : GL₂(𝔽_q) →* 𝔽_q^×`. -/
noncomputable abbrev detHom : G p n →* (GaloisField p n)ˣ :=
  Matrix.GeneralLinearGroup.det

/-- `det` is surjective (e.g. `diag(u, 1)` has determinant `u`). -/
theorem det_surjective : Function.Surjective (detHom p n) :=
  Matrix.GeneralLinearGroup.det_surjective

/-- The image of `SL₂` in `GL₂` is exactly the kernel of `det`. -/
theorem toGL_range_eq_det_ker :
    (SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField p n)).range =
      (detHom p n).ker := by
  ext g
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨s, rfl⟩
    apply Units.ext
    simp
  · intro hdet
    exact ⟨⟨g, Units.ext_iff.mp hdet⟩, Units.ext rfl⟩

/-- `ker det = [G, G]`: combining `Proposition5_25_1` (`[G,G] = SL₂`) with the
identification of `SL₂` as `ker det`. -/
theorem det_ker_eq_commutator (hn : 0 < n) (hq : 2 < Nat.card (GaloisField p n)) :
    (detHom p n).ker = commutator (G p n) := by
  rw [← toGL_range_eq_det_ker, Etingof.Proposition5_25_1 p n hn hq]

/-- Every 1-dimensional representation `ρ : G →* ℂˣ` kills `ker det`: since `ℂˣ` is
abelian it kills the commutator subgroup, which equals `ker det`. -/
theorem det_ker_le_ker (hn : 0 < n) (hq : 2 < Nat.card (GaloisField p n))
    (ρ : G p n →* ℂˣ) : (detHom p n).ker ≤ ρ.ker := by
  rw [det_ker_eq_commutator p n hn hq]
  exact Abelianization.commutator_subset_ker ρ

/-- **Classification of 1-dimensional representations of `GL₂(𝔽_q)`** (Etingof,
Discussion 5.25). The map `ξ ↦ ξ ∘ det` is a bijection from characters of `𝔽_q^×`
to 1-dimensional representations of `G`. Equivalently: every 1-dimensional
representation of `G` has the form `g ↦ ξ(det g)` for a **unique** character `ξ`. -/
noncomputable def characterCompDetEquiv (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) :
    ((GaloisField p n)ˣ →* ℂˣ) ≃ (G p n →* ℂˣ) :=
  (MonoidHom.liftOfSurjective (detHom p n) (det_surjective p n)).symm.trans
    (Equiv.subtypeUnivEquiv (fun ρ => det_ker_le_ker p n hn hq ρ))

/-- The classification bijection sends `ξ` to the representation `g ↦ ξ(det g)`. -/
@[simp]
theorem characterCompDetEquiv_apply (hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) (ξ : (GaloisField p n)ˣ →* ℂˣ) :
    characterCompDetEquiv p n hn hq ξ = ξ.comp (detHom p n) :=
  rfl

/-- **Count.** There are exactly `q - 1` one-dimensional representations of
`GL₂(𝔽_q)`, matching the `q - 1` characters of `𝔽_q^×`. -/
theorem card_oneDimRep (hn : 0 < n) (hq : 2 < Nat.card (GaloisField p n)) :
    Nat.card (G p n →* ℂˣ) = Nat.card (GaloisField p n) - 1 := by
  haveI : NeZero ((Monoid.exponent (GaloisField p n)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← Nat.card_congr (characterCompDetEquiv p n hn hq),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (GaloisField p n)ˣ ℂ,
    Nat.card_units]

end Etingof.Discussion_1dim_reps
