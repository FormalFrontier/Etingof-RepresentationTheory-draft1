import EtingofRepresentationTheory.Chapter5.Theorem5_25_2

/-!
# The one-dimensional and principal-series irreducibles of `GL₂(𝔽_q)`, as one indexed family

Etingof's list of irreducible representations of `G = GL₂(𝔽_q)` has three groups:

* `q − 1` one-dimensional representations `ℂ_μ : g ↦ μ(det g)`;
* `q(q−1)/2` *principal series* representations, which is two kinds of object:
  the `q − 1` complements `W_μ` in `V(μ,μ) ≅ ℂ_μ ⊕ W_μ`, and the `(q−1)(q−2)/2`
  induced representations `V(χ₁,χ₂)` for **unordered** pairs of distinct characters;
* `q(q−1)/2` complementary series representations.

`Chapter5/Theorem5_25_2.lean` constructs the first two groups and proves the
simplicity and same-kind non-isomorphism statements one at a time. This file
packages them: it supplies the endpoints that were missing for `ℂ_μ`
(`detChar_finrank`, `detChar_character`, `detChar_iso_iff`), proves the cross-kind
non-isomorphisms by a dimension count (`1`, `q`, `q + 1` are pairwise distinct once
`q ≥ 2`), and assembles a single index type

  `PrincipalIndex p n = Chars ⊕ Chars ⊕ {s : Sym2 Chars // ¬ s.IsDiag}`

with a family `principalFamily : PrincipalIndex p n → FDRep ℂ (GL₂ 𝔽_q)` whose members
are simple, pairwise non-isomorphic, and number `(q − 1) + q(q−1)/2`.

The unordered-pair indexing matches `Etingof.Theorem5_25_2_part3b`, which is stated with
set equality `{χ₁, χ₂} = {χ₁', χ₂'}`: `Sym2` of the character group with the diagonal
removed is exactly that quotient. Since `principalSeries χ₁ χ₂` and `principalSeries χ₂ χ₁`
are isomorphic but not *equal* objects of `FDRep ℂ (GL₂ 𝔽_q)`, the family cannot be defined
by `Sym2.lift`; it picks an ordered representative of each unordered pair with `Quot.out`,
which is harmless because both choices give isomorphic representations.

## Main results

* `Etingof.GL2.detChar_finrank`, `Etingof.GL2.detChar_character` — `dim ℂ_μ = 1` and
  `χ_{ℂ_μ}(g) = μ(det g)`.
* `Etingof.GL2.detChar_iso_iff` — `ℂ_μ ≅ ℂ_ν` iff `μ = ν`.
* `Etingof.GL2.detChar_not_iso_complementW`, `Etingof.GL2.detChar_not_iso_principalSeries`,
  `Etingof.GL2.complementW_not_iso_principalSeries` — the three cross-kind
  non-isomorphisms, all by dimension count.
* `Etingof.GL2.principalFamily_simple` — every member of the family is simple.
* `Etingof.GL2.principalFamily_injective` — distinct indices give non-isomorphic members.
* `Etingof.GL2.card_principalIndex` — the family has `(q − 1) + q(q−1)/2` members.
* `Etingof.GL2.exists_principal_family` — the packaged existence statement, the form
  a completeness-by-counting argument for `GL₂(𝔽_q)` consumes.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Etingof.GL2

/-- `GL₂(𝔽_q)` for `q = pⁿ`, the group Theorem 5.25.2's representations live over. -/
abbrev Grp (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

/-- The character group `Hom(𝔽_q^×, ℂ^×)`: the parameter set of Etingof's one-dimensional
and principal-series families. -/
abbrev Chars (p n : ℕ) [Fact (Nat.Prime p)] := (GaloisField p n)ˣ →* ℂˣ

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

/-! ### Isomorphic representations have the same dimension -/

/-- An isomorphism in `FDRep ℂ G` is in particular a `ℂ`-linear equivalence, so it
preserves dimension. This is the only tool the cross-kind non-isomorphism statements
below need. -/
theorem finrank_eq_of_iso {G : Type*} [Monoid G] {X Y : FDRep ℂ G} (i : X ≅ Y) :
    Module.finrank ℂ X.V = Module.finrank ℂ Y.V :=
  (FDRep.isoToLinearEquiv i).finrank_eq

/-! ### The missing endpoints for the one-dimensional representations `ℂ_μ` -/

/-- **`dim ℂ_μ = 1`.** The representation `g ↦ μ(det g)` acts on the one-dimensional space
`ℂ`. -/
@[simp]
theorem detChar_finrank (mu : Chars p n) :
    Module.finrank ℂ (detChar p n mu).V = 1 :=
  Module.finrank_self ℂ

set_option backward.isDefEq.respectTransparency false in
/-- **The character of `ℂ_μ`.** On a one-dimensional representation the character is the
scalar itself: `χ_{ℂ_μ}(g) = μ(det g)`. -/
theorem detChar_character (mu : Chars p n) (g : Grp p n) :
    (detChar p n mu).character g = ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  change LinearMap.trace ℂ _ ((detChar p n mu).ρ g) = _
  have hρ : (detChar p n mu).ρ g
      = ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := rfl
  rw [hρ, map_smul, LinearMap.trace_id]
  simp

/-- **`ℂ_μ ≅ ℂ_ν` iff `μ = ν`.** Distinct characters of `𝔽_q^×` give distinct one-dimensional
representations of `GL₂(𝔽_q)`, so the family `μ ↦ ℂ_μ` really has `q − 1` members.

Forward: isomorphic representations have equal characters, and `χ_{ℂ_μ}(g) = μ(det g)`, so
`μ` and `ν` agree on the image of `det`, which is all of `𝔽_q^×`. -/
theorem detChar_iso_iff (mu nu : Chars p n) :
    Nonempty (detChar p n mu ≅ detChar p n nu) ↔ mu = nu := by
  constructor
  · rintro ⟨i⟩
    have hchar := FDRep.char_iso i
    ext c
    obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) c
    have h := congr_fun hchar g
    rw [detChar_character, detChar_character, hg] at h
    exact congrArg Units.val (Units.ext h)
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-! ### Unordered pairs of distinct characters -/

/-- Unordered pairs of *distinct* characters of `𝔽_q^×`: the index set of the induced
principal series `V(χ₁, χ₂)` with `χ₁ ≠ χ₂`, which by `Theorem5_25_2_part3b` depends only
on the unordered pair. There are `(q−1)(q−2)/2` of them. -/
abbrev CharPair (p n : ℕ) [Fact (Nat.Prime p)] :=
  {s : Sym2 (Chars p n) // ¬ s.IsDiag}

namespace CharPair

variable {p n}

/-- A chosen first coordinate of an unordered pair. -/
def fst (s : CharPair p n) : Chars p n := (Quot.out (s : Sym2 (Chars p n))).1

/-- A chosen second coordinate of an unordered pair. -/
def snd (s : CharPair p n) : Chars p n := (Quot.out (s : Sym2 (Chars p n))).2

@[simp]
theorem mk_fst_snd (s : CharPair p n) : s(s.fst, s.snd) = (s : Sym2 (Chars p n)) := by
  change Quot.mk _ ((Quot.out (s : Sym2 (Chars p n))).1, (Quot.out (s : Sym2 (Chars p n))).2) = _
  rw [Prod.mk.eta]
  exact Quot.out_eq _

/-- The two chosen coordinates really are distinct: that is what `¬ IsDiag` says. -/
theorem fst_ne_snd (s : CharPair p n) : s.fst ≠ s.snd := fun h =>
  s.2 (by rw [← mk_fst_snd s]; exact Sym2.mk_isDiag_iff.mpr h)

/-- Two unordered pairs with the same underlying two-element set are equal. This is the
form in which `Theorem5_25_2_part3b`'s conclusion (`{χ₁, χ₂} = {χ₁', χ₂'}` as sets) is
consumed. -/
theorem ext_of_pair_eq {s t : CharPair p n}
    (h : ({s.fst, s.snd} : Set (Chars p n)) = {t.fst, t.snd}) : s = t := by
  apply Subtype.ext
  rw [← mk_fst_snd s, ← mk_fst_snd t]
  rw [Set.pair_eq_pair_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Sym2.eq_swap]

end CharPair

/-! ### Counting the characters -/

instance : NeZero ((Monoid.exponent (GaloisField p n)ˣ : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

instance : Finite (Chars p n) :=
  Finite.of_equiv _
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      ((GaloisField p n)ˣ) ℂ).some.toEquiv.symm

/-- **There are `q − 1` characters of `𝔽_q^×`.** Over `ℂ`, which has enough roots of unity,
the character group of a finite abelian group is (non-canonically) isomorphic to the group
itself; here that group is `𝔽_q^×`, of order `q − 1`. -/
theorem card_chars (hn : n ≠ 0) : Nat.card (Chars p n) = p ^ n - 1 := by
  classical
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((GaloisField p n)ˣ) ℂ,
    Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card p n hn]

/-- **There are `(q−1)(q−2)/2` unordered pairs of distinct characters.** -/
theorem card_charPair : Nat.card (CharPair p n) = (Nat.card (Chars p n)).choose 2 := by
  classical
  haveI : Fintype (Chars p n) := Fintype.ofFinite _
  have := Sym2.card_subtype_not_diag (α := Chars p n)
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this

/-! ### The packaged family -/

/-- **The index set of Etingof's one-dimensional and principal-series irreducibles.** The
three summands are, in order, the one-dimensional `ℂ_μ`, the `q`-dimensional complements
`W_μ`, and the `(q+1)`-dimensional induced representations `V(χ₁, χ₂)` for unordered pairs
of distinct characters. Its cardinality is `(q − 1) + q(q−1)/2` (`card_principalIndex`). -/
abbrev PrincipalIndex (p n : ℕ) [Fact (Nat.Prime p)] :=
  Chars p n ⊕ Chars p n ⊕ CharPair p n

/-- **The family itself.** `principalFamily p n` sends each index to the representation it
names: `ℂ_μ`, `W_μ`, or `V(χ₁, χ₂)`.

For the third summand an ordered representative of the unordered pair is chosen with
`Quot.out`. The choice is immaterial: `principalSeries χ₁ χ₂ ≅ principalSeries χ₂ χ₁`, so
any other choice gives an isomorphic family. -/
def principalFamily : PrincipalIndex p n → FDRep ℂ (Grp p n)
  | .inl mu => detChar p n mu
  | .inr (.inl mu) => complementW p n mu
  | .inr (.inr s) => principalSeries p n s.fst s.snd

@[simp] theorem principalFamily_inl (mu : Chars p n) :
    principalFamily p n (.inl mu) = detChar p n mu := rfl

@[simp] theorem principalFamily_inr_inl (mu : Chars p n) :
    principalFamily p n (.inr (.inl mu)) = complementW p n mu := rfl

@[simp] theorem principalFamily_inr_inr (s : CharPair p n) :
    principalFamily p n (.inr (.inr s)) = principalSeries p n s.fst s.snd := rfl

/-- `q = pⁿ ≥ 2`, which is all the cross-kind dimension comparisons below need. -/
private theorem two_le_q (hn : n ≠ 0) : 2 ≤ p ^ n :=
  Nat.one_lt_pow hn hp.out.one_lt

/-! ### Cross-kind non-isomorphism

The three kinds of representation have dimensions `1`, `q`, and `q + 1`, which are pairwise
distinct as soon as `q ≥ 2`. That is the whole argument: no character theory is needed to
separate one kind from another, only `finrank_eq_of_iso`. -/

/-- **`ℂ_μ ≇ W_ν`**: the dimensions are `1` and `q`, and `q ≥ 2`. -/
theorem detChar_not_iso_complementW (hn : n ≠ 0) (mu nu : Chars p n) :
    ¬ Nonempty (detChar p n mu ≅ complementW p n nu) := by
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [detChar_finrank, (Theorem5_25_2_part2 p n (Nat.pos_of_ne_zero hn) nu).2.2] at h
  have := two_le_q p n hn
  omega

/-- **`ℂ_μ ≇ V(χ₁, χ₂)`**: the dimensions are `1` and `q + 1`, and `q ≥ 2`. -/
theorem detChar_not_iso_principalSeries (hn : n ≠ 0) (mu chi1 chi2 : Chars p n) :
    ¬ Nonempty (detChar p n mu ≅ principalSeries p n chi1 chi2) := by
  haveI : NeZero n := ⟨hn⟩
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [detChar_finrank, principalSeries_finrank] at h
  have := two_le_q p n hn
  omega

/-- **`W_μ ≇ V(χ₁, χ₂)`**: the dimensions are `q` and `q + 1`. -/
theorem complementW_not_iso_principalSeries (hn : n ≠ 0) (mu chi1 chi2 : Chars p n) :
    ¬ Nonempty (complementW p n mu ≅ principalSeries p n chi1 chi2) := by
  haveI : NeZero n := ⟨hn⟩
  rintro ⟨e⟩
  have h := finrank_eq_of_iso e
  rw [(Theorem5_25_2_part2 p n (Nat.pos_of_ne_zero hn) mu).2.2, principalSeries_finrank] at h
  omega

/-- The dimension of each member of the family: `1`, `q`, `q + 1` for the three summands. -/
theorem principalFamily_finrank (hn : n ≠ 0) :
    ∀ i, Module.finrank ℂ (principalFamily p n i).V =
      Sum.elim (fun _ => 1) (Sum.elim (fun _ => p ^ n) (fun _ => p ^ n + 1)) i
  | .inl mu => detChar_finrank p n mu
  | .inr (.inl mu) => (Theorem5_25_2_part2 p n (Nat.pos_of_ne_zero hn) mu).2.2
  | .inr (.inr s) => by
      haveI : NeZero n := ⟨hn⟩
      exact principalSeries_finrank p n s.fst s.snd

/-- **Every member of the family is irreducible.** The three cases are `detChar_simple`,
`Theorem5_25_2_part2` (for `W_μ`), and `Theorem5_25_2_part1` (for `V(χ₁, χ₂)`, whose two
characters are distinct because the index is an off-diagonal unordered pair). -/
theorem principalFamily_simple (hn : n ≠ 0) : ∀ i, Simple (principalFamily p n i)
  | .inl mu => detChar_simple p n mu
  | .inr (.inl mu) => (Theorem5_25_2_part2 p n (Nat.pos_of_ne_zero hn) mu).2.1
  | .inr (.inr s) => Theorem5_25_2_part1 p n s.fst s.snd s.fst_ne_snd

/-- **Distinct indices give non-isomorphic representations.** Within a summand this is
`detChar_iso_iff`, `Theorem5_25_2_part3a`, and `Theorem5_25_2_part3b`; across summands it is
the three dimension comparisons above. -/
theorem principalFamily_injective (hn : n ≠ 0) :
    ∀ i j : PrincipalIndex p n, Nonempty (principalFamily p n i ≅ principalFamily p n j) →
      i = j := by
  haveI : NeZero n := ⟨hn⟩
  rintro (mu | mu | s) (nu | nu | t) h
  · exact congrArg Sum.inl ((detChar_iso_iff p n mu nu).mp h)
  · exact absurd h (detChar_not_iso_complementW p n hn mu nu)
  · exact absurd h (detChar_not_iso_principalSeries p n hn mu t.fst t.snd)
  · exact absurd (Nonempty.map Iso.symm h) (detChar_not_iso_complementW p n hn nu mu)
  · exact congrArg (fun x => Sum.inr (Sum.inl x))
      ((Theorem5_25_2_part3a p n mu nu).mp h)
  · exact absurd h (complementW_not_iso_principalSeries p n hn mu t.fst t.snd)
  · exact absurd (Nonempty.map Iso.symm h) (detChar_not_iso_principalSeries p n hn nu s.fst s.snd)
  · exact absurd (Nonempty.map Iso.symm h)
      (complementW_not_iso_principalSeries p n hn nu s.fst s.snd)
  · refine congrArg (fun x => Sum.inr (Sum.inr x)) (CharPair.ext_of_pair_eq ?_)
    exact (Theorem5_25_2_part3b p n s.fst s.snd t.fst t.snd s.fst_ne_snd t.fst_ne_snd).mp h

/-- **The family has `(q − 1) + q(q−1)/2` members.** The three summands contribute `q − 1`
one-dimensional representations, `q − 1` complements `W_μ`, and `(q−1)(q−2)/2` induced
representations, and `(q − 1) + (q−1)(q−2)/2 = q(q−1)/2`. -/
theorem card_principalIndex (hn : n ≠ 0) :
    Nat.card (PrincipalIndex p n) = (p ^ n - 1) + p ^ n * (p ^ n - 1) / 2 := by
  classical
  have hq := two_le_q p n hn
  have hchars := card_chars p n hn
  have hpair : Nat.card (CharPair p n) = (p ^ n - 1).choose 2 := by
    rw [card_charPair, hchars]
  have hsum : Nat.card (PrincipalIndex p n)
      = Nat.card (Chars p n) + (Nat.card (Chars p n) + Nat.card (CharPair p n)) := by
    rw [Nat.card_sum, Nat.card_sum]
  rw [hsum, hchars, hpair, Nat.choose_two_right]
  -- With `a = q − 1`: `a + (a + a(a−1)/2) = a + (a+1)a/2`, since `2 ∣ a(a−1)`.
  set a := p ^ n - 1 with ha
  have hqa : p ^ n = a + 1 := by omega
  obtain ⟨k, hk⟩ : 2 ∣ a * (a - 1) := by
    rcases Nat.even_or_odd a with h | h
    · exact Dvd.dvd.mul_right h.two_dvd _
    · have : Even (a - 1) := by rcases h with ⟨m, hm⟩; exact ⟨m, by omega⟩
      exact Dvd.dvd.mul_left this.two_dvd _
  have hka : (a + 1) * a = 2 * (k + a) := by
    have : (a + 1) * a = a * (a - 1) + 2 * a := by cases a with
      | zero => simp
      | succ m => simp; ring
    rw [this, hk]; ring
  rw [hqa, hk, hka, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

/-- **The packaged statement.** For `q = pⁿ` with `n ≠ 0` there is a family of
`(q − 1) + q(q−1)/2` pairwise non-isomorphic simple objects of `FDRep ℂ (GL₂ 𝔽_q)`: the
one-dimensional representations `ℂ_μ` together with the principal series `W_μ` and
`V(χ₁, χ₂)`.

This is the form Etingof's completeness-by-counting argument consumes: combined with the
`q(q−1)/2` complementary-series representations it accounts for all `q² − 1` irreducibles
of `GL₂(𝔽_q)`. -/
theorem exists_principal_family (hn : n ≠ 0) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (Grp p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = (p ^ n - 1) + p ^ n * (p ^ n - 1) / 2 :=
  ⟨PrincipalIndex p n, principalFamily p n, principalFamily_simple p n hn,
    principalFamily_injective p n hn, card_principalIndex p n hn⟩

/-- `exists_principal_family` phrased with `q = |𝔽_q|` rather than `q = pⁿ`, matching the
shape of the constructed count in `Discussion_complementary_series_summary.lean`. -/
theorem exists_principal_family' (hn : n ≠ 0) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (Grp p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = (Nat.card (GaloisField p n) - 1)
        + Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) - 1) / 2 := by
  classical
  rw [GaloisField.card p n hn]
  exact exists_principal_family p n hn

end Etingof.GL2

end
