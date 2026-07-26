import EtingofRepresentationTheory.Chapter5.GL2CharacterValues
import EtingofRepresentationTheory.Infrastructure.InducedCharacter

/-!
# `Ind_K^G ℂ_ν` for the elliptic torus `K ⊂ GL₂(𝔽_q)`

Discussion 5.25.4 builds the complementary series of `GL₂(𝔽_q)` from the virtual
character

```
χ = char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
```

where `K ≅ 𝔽_{q²}ˣ` is the elliptic torus, embedded in `GL₂(𝔽_q)` by multiplication on
the degree-two extension. `Etingof.GL2.complementarySeriesChar` records the third term
as a bare Frobenius sum; this file produces the representation it is the character of.

## Key results

* `Etingof.GL2.ellipticInduced` — `Ind_K^G ℂ_ν` as an honest `FDRep ℂ (GL₂ 𝔽_q)`.
* `Etingof.GL2.finrank_ellipticInduced` — its dimension is `|G| / |K|`, i.e. `q(q−1)`.
* `Etingof.GL2.character_ellipticInduced` — its character is exactly the Frobenius sum
  appearing in `complementarySeriesChar`.
* `Etingof.GL2.complementarySeriesChar_eq` — rewrites `complementarySeriesChar` with the
  third term replaced by `(ellipticInduced p n nu).character`.

Everything is a specialisation of `Etingof.InducedChar`, which sets up induction of a
linear character from an arbitrary subgroup of an arbitrary finite group.
-/

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2'' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

open scoped Classical in
/-- `Ind_K^G ℂ_ν`, the representation of `GL₂(𝔽_q)` induced from the linear character
`ν` of the elliptic torus `K ≅ 𝔽_{q²}ˣ`. It is realised on the covariance submodule
`{f : G → ℂ | f (k * g) = ν k * f g}` of `G → ℂ`, with `G` acting by right
translation. -/
def Etingof.GL2.ellipticInduced
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    FDRep ℂ (GL2'' p n) :=
  Etingof.InducedChar.ind (Etingof.GL2.ellipticSubgroup p n) nu

open scoped Classical in
/-- **Frobenius character formula** for `Ind_K^G ℂ_ν`: it is exactly the third term of
`Etingof.GL2.complementarySeriesChar`. -/
theorem Etingof.GL2.character_ellipticInduced
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (g : GL2'' p n) :
    (Etingof.GL2.ellipticInduced p n nu).character g
      = (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
          ∑ x : GL2'' p n,
            if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
            then (nu ⟨x⁻¹ * g * x, h⟩).val else 0 :=
  Etingof.InducedChar.character_ind (Etingof.GL2.ellipticSubgroup p n) nu g

open scoped Classical in
/-- The induced representation has dimension `|G| / |K| = q(q−1)`. -/
theorem Etingof.GL2.finrank_ellipticInduced
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    Module.finrank ℂ (Etingof.GL2.ellipticInduced p n nu) =
      Fintype.card (GL2'' p n) / Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) :=
  Etingof.InducedChar.finrank_ind (Etingof.GL2.ellipticSubgroup p n) nu

/-! ### The dimension in closed form: `q(q−1)` -/

/-- `|K| = q² − 1`: the elliptic torus is the unit group of `𝔽_{q²}`. -/
theorem Etingof.GL2.card_ellipticSubgroup
    [Fintype (GaloisField p n)] (hn : n ≠ 0) :
    Nat.card ↥(Etingof.GL2.ellipticSubgroup p n)
      = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  classical
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  have hinj : Function.Injective (Etingof.GL2.fieldExtEmbed p n) := by
    intro a b hab
    unfold Etingof.GL2.fieldExtEmbed at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  have hcard : Nat.card ↥(Etingof.GL2.ellipticSubgroup p n)
      = Nat.card (GaloisField p (2 * n))ˣ := by
    change Nat.card ↥(Etingof.GL2.fieldExtEmbed p n).range = _
    exact Nat.card_congr ((Etingof.GL2.fieldExtEmbed p n).ofInjective hinj).symm.toEquiv
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn),
    ← Nat.card_eq_fintype_card, GaloisField.card p n hn, ← pow_mul, Nat.mul_comm n 2]

open scoped Classical in
/-- `Ind_K^G ℂ_ν` has dimension `q(q−1)`, as in Discussion 5.25.4. -/
theorem Etingof.GL2.finrank_ellipticInduced_eq_mul
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (hn : n ≠ 0) (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    Module.finrank ℂ (Etingof.GL2.ellipticInduced p n nu)
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
  set q := Fintype.card (GaloisField p n) with hq
  have hq2 : 2 ≤ q := by
    rw [hq, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    calc 2 ≤ p := hp.out.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hn)
  have hG : Fintype.card (GL2'' p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have h := Matrix.card_GL_field (𝔽 := GaloisField p n) 2
    rw [Nat.card_eq_fintype_card] at h
    rw [h]
    simp [Fin.prod_univ_two, hq]
  have hpos : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq2)
  rw [Etingof.GL2.finrank_ellipticInduced, hG, ← Nat.card_eq_fintype_card,
    Etingof.GL2.card_ellipticSubgroup p n hn, Nat.mul_div_cancel_left _ hpos,
    Nat.mul_sub, pow_two, Nat.mul_one]

open Classical in
/-- The complementary series virtual character, with its third term identified as the
character of an actual representation. -/
theorem Etingof.GL2.complementarySeriesChar_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2'' p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (g : GL2'' p n) :
    Etingof.GL2.complementarySeriesChar p n nu g =
      Etingof.GL2.charW₁ p n g *
          Etingof.GL2.charVα₁ p n (nu.comp (Etingof.GL2.scalarToElliptic p n)) g
        - Etingof.GL2.charVα₁ p n (nu.comp (Etingof.GL2.scalarToElliptic p n)) g
        - (Etingof.GL2.ellipticInduced p n nu).character g := by
  rw [Etingof.GL2.character_ellipticInduced]
  rfl
