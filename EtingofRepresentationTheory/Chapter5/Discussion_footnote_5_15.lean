import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Footnote 2 to Theorem 5.15.1: lexicographic minimality of the staircase `ρ`

Etingof's second footnote to Theorem 5.15.1 records the elementary order-theoretic
fact underpinning the leading-term extraction in the Frobenius character formula:

> Another way to see this is to note that `σ(ρ) ≤ ρ` lexicographically with equality
> if and only if `σ = 1`, and subtracting both sides from the constant vector `λ + ρ`
> shows that `λ + ρ − σ(ρ) ≥ λ` with equality if and only if `σ = 1`.

Here `ρ = (N−1, N−2, …, 1, 0)` is the strictly decreasing staircase vector
`Etingof.rhoShift N` and `σ ∈ S_N` permutes its coordinates. The same statement is
reused in `Discussion_proof_of_Frobenius_character_formula`.

The in-project `Etingof.rev_of_permExponent_eq_rhoShift` only handles the single case
`σ = revPerm` (the reversal). This file proves the *general* lexicographic inequality
and its equality characterisation, and derives the "subtract from `λ + ρ`" corollary.

We model "`σ` acting on `ρ`" by precomposition, `ρ ∘ σ` (coordinate `i` carries the
value `ρ (σ i)`). Because every claim here is characterised by `σ = 1`, the choice of
convention (`σ` versus `σ⁻¹`) is immaterial: `σ ∘ ·` and `σ⁻¹ ∘ ·` range over the same
set of rearrangements, and `σ = 1 ↔ σ⁻¹ = 1`.

The lexicographic order is Mathlib's `toLex` on `Fin N → ℤ`, whose strict part unfolds
to `∃ i, (∀ j < i, x j = y j) ∧ x i < y i` — the "first nonvanishing coordinate"
comparison of the book's Discussion on lexicographic ordering.
-/

open Etingof

namespace Chapter5.Footnote_5_15

variable {N : ℕ}

/-! ## The abstract order-theoretic core

Everything specific to `ρ` factors through the single fact that permuting a strictly
antitone vector by a non-identity permutation strictly lowers it lexicographically. -/

/-- **Core lemma.** Permuting a strictly antitone integer vector `f` by a non-identity
permutation strictly lowers it in the lexicographic order: `toLex (f ∘ σ) < toLex f`.

Proof: let `i₀` be the least non-fixed point of `σ`. Coordinates below `i₀` are fixed,
so `f ∘ σ` and `f` agree there; and since `σ` fixes everything below `i₀` and is a
bijection, `σ i₀` cannot land below `i₀`, hence `σ i₀ > i₀`, so `f (σ i₀) < f i₀`. -/
theorem toLex_comp_perm_lt {f : Fin N → ℤ} (hf : StrictAnti f)
    {σ : Equiv.Perm (Fin N)} (hσ : σ ≠ 1) :
    toLex (f ∘ σ) < toLex f := by
  classical
  -- `σ` has a non-fixed point; take the least one.
  have hex : ∃ i, σ i ≠ i := by
    by_contra h
    exact hσ (Equiv.ext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  obtain ⟨w, hw⟩ := hex
  have hne : (Finset.univ.filter fun i => σ i ≠ i).Nonempty :=
    ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩⟩
  set i₀ := (Finset.univ.filter fun i => σ i ≠ i).min' hne with hi0
  have hi0mem := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  have hmove : σ i₀ ≠ i₀ := hi0mem.2
  have hfix : ∀ j, j < i₀ → σ j = j := by
    intro j hj
    by_contra hjm
    exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hjm⟩)) (not_le.2 hj)
  -- `σ` fixes everything below `i₀`, so `σ i₀` cannot land below `i₀`.
  have hgt : i₀ < σ i₀ := by
    rcases lt_trichotomy (σ i₀) i₀ with h | h | h
    · exact absurd (σ.injective (hfix (σ i₀) h)) hmove
    · exact absurd h hmove
    · exact h
  refine ⟨i₀, ?_, ?_⟩
  · intro j hj; change f (σ j) = f j; rw [hfix j hj]
  · change f (σ i₀) < f i₀; exact hf hgt

/-- Permuting a strictly antitone vector never raises it lexicographically. -/
theorem toLex_comp_perm_le {f : Fin N → ℤ} (hf : StrictAnti f)
    (σ : Equiv.Perm (Fin N)) : toLex (f ∘ σ) ≤ toLex f := by
  rcases eq_or_ne σ 1 with h | h
  · subst h; simp
  · exact (toLex_comp_perm_lt hf h).le

/-- The permuted vector equals the original exactly when `σ` is the identity. -/
theorem toLex_comp_perm_eq_iff {f : Fin N → ℤ} (hf : StrictAnti f)
    (σ : Equiv.Perm (Fin N)) : toLex (f ∘ σ) = toLex f ↔ σ = 1 := by
  constructor
  · intro h
    by_contra hσ
    exact (toLex_comp_perm_lt hf hσ).ne h
  · rintro rfl; simp

/-- **Order reversal.** Subtracting lexicographically ordered vectors from a fixed
vector `c` reverses the strict order. This is the algebraic content of "subtract both
sides from `λ + ρ`". -/
theorem toLex_const_sub_lt {a b c : Fin N → ℤ} (h : toLex a < toLex b) :
    toLex (fun i => c i - b i) < toLex (fun i => c i - a i) := by
  obtain ⟨i, hfix, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    change c j - b j = c j - a j
    have : a j = b j := hfix j hj
    omega
  · change c i - b i < c i - a i
    have : a i < b i := hlt
    omega

/-- The non-strict order reversal. -/
theorem toLex_const_sub_le {a b c : Fin N → ℤ} (h : toLex a ≤ toLex b) :
    toLex (fun i => c i - b i) ≤ toLex (fun i => c i - a i) := by
  rcases h.lt_or_eq with hlt | heq
  · exact (toLex_const_sub_lt hlt).le
  · obtain rfl : a = b := toLex_inj.1 heq
    exact le_refl _

/-! ## The staircase `ρ` and its shifts -/

/-- `ρ = (N−1, N−2, …, 1, 0)` as an integer vector, `ρ i = N − 1 − i`. -/
noncomputable def rhoVec (N : ℕ) : Fin N → ℤ := fun i => (rhoShift N i : ℤ)

/-- A partition `λ` as an integer vector, `λ i = λ_i`. -/
noncomputable def laVec (la : Nat.Partition N) : Fin N → ℤ :=
  fun i => (Nat.Partition.toFinsupp la i : ℤ)

/-- `ρ` is strictly decreasing. -/
theorem rhoVec_strictAnti : StrictAnti (rhoVec N) := by
  intro i j hij
  have h1 : (i : ℕ) < (j : ℕ) := hij
  have h2 : (j : ℕ) < N := j.isLt
  simp only [rhoVec, rhoShift, Finsupp.coe_equivFunOnFinite_symm]
  omega

/-! ## The footnote, formalized -/

/-- **Footnote 5.15, first claim (inequality).** For `σ ∈ S_N` permuting the
coordinates of `ρ = (N−1, …, 0)`, the rearrangement `σ(ρ)` is lexicographically at
most `ρ`. -/
theorem rhoVec_comp_perm_le (σ : Equiv.Perm (Fin N)) :
    toLex (rhoVec N ∘ σ) ≤ toLex (rhoVec N) :=
  toLex_comp_perm_le rhoVec_strictAnti σ

/-- **Footnote 5.15, first claim (equality case).** `σ(ρ) = ρ` lexicographically if and
only if `σ = 1`. -/
theorem rhoVec_comp_perm_eq_iff (σ : Equiv.Perm (Fin N)) :
    toLex (rhoVec N ∘ σ) = toLex (rhoVec N) ↔ σ = 1 :=
  toLex_comp_perm_eq_iff rhoVec_strictAnti σ

/-- **Footnote 5.15, second claim (inequality).** Subtracting `σ(ρ)` from the constant
vector `λ + ρ` gives a vector that is lexicographically at least `λ`:
`λ + ρ − σ(ρ) ≥ λ`. -/
theorem laVec_le_shifted_sub_perm (la : Nat.Partition N) (σ : Equiv.Perm (Fin N)) :
    toLex (laVec la) ≤
      toLex (fun i => (laVec la i + rhoVec N i) - (rhoVec N ∘ σ) i) := by
  have h := toLex_const_sub_le (c := fun i => laVec la i + rhoVec N i)
    (rhoVec_comp_perm_le (N := N) σ)
  have hc : (fun i => (laVec la i + rhoVec N i) - rhoVec N i) = laVec la := by
    funext i; ring
  rwa [hc] at h

/-- **Footnote 5.15, second claim (equality case).** `λ + ρ − σ(ρ) = λ` lexicographically
if and only if `σ = 1`. -/
theorem laVec_eq_shifted_sub_perm_iff (la : Nat.Partition N) (σ : Equiv.Perm (Fin N)) :
    toLex (laVec la) =
      toLex (fun i => (laVec la i + rhoVec N i) - (rhoVec N ∘ σ) i) ↔ σ = 1 := by
  have hc : (fun i => (laVec la i + rhoVec N i) - rhoVec N i) = laVec la := by
    funext i; ring
  constructor
  · intro h
    by_contra hσ
    have hlt := toLex_comp_perm_lt (N := N) rhoVec_strictAnti hσ
    have hrev := toLex_const_sub_lt (c := fun i => laVec la i + rhoVec N i) hlt
    rw [hc] at hrev
    exact absurd h hrev.ne
  · rintro rfl
    have hid : (fun i => (laVec la i + rhoVec N i) - (rhoVec N ∘ ⇑(1 : Equiv.Perm (Fin N))) i)
        = laVec la := by
      funext i
      simp only [Function.comp_apply, Equiv.Perm.coe_one, id_eq]
      ring
    rw [hid]

end Chapter5.Footnote_5_15
