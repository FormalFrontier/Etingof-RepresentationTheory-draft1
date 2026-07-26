import Mathlib
import EtingofRepresentationTheory.Chapter4.Problem4_12_2
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Infrastructure.FDRepDirectSum

/-!
# Problem 4.12.9: characters and tensor products for the Heisenberg group

**Problem 4.12.9.** Find the characters and tensor products of irreducible complex
representations of the Heisenberg group from Problem 4.12.2.

## Formalization

We reuse the Heisenberg group `Heisenberg p` and its generators from Problem 4.12.2. Recall
(4.12.2) that the irreducibles are the `p²` one-dimensional characters and, for each `p`-th
root of unity `z ≠ 1`, a `p`-dimensional representation `R_z` on `V = ZMod p → ℂ` determined by
`(ρ xGen f)(t) = f(t-1)`, `(ρ yGen f)(t) = z^t · f(t)`. The predicate `IsRz z ρ` records that
`ρ` realizes `R_z`.

A short computation with the two generators shows `ρ(⟨0,0,1⟩) = z⁻¹ · id` (the central
character), so:

* `character_Rz`: the character of `R_z` (`z ≠ 1`) vanishes off the center and equals
  `p · z^{-c}` on a central element `⟨0,0,c⟩`:
  `tr ρ(⟨a,b,c⟩) = if a = 0 ∧ b = 0 then p · (z⁻¹)^c else 0`.
* `tensor_character_mul` (tensor products): since the character of a tensor product is the
  product of characters, for `p`-th roots `z, w` with `z, w ≠ 1`:
  - if `z·w ≠ 1`, then `χ_{R_z}·χ_{R_w} = p · χ_{R_{zw}}`, i.e. `R_z ⊗ R_w ≅ p · R_{zw}`
    (`tensor_character_nonone`);
  - if `z·w = 1`, then `χ_{R_z}·χ_{R_w}` equals `p²` on the center and `0` elsewhere: the
    character of `⨁` of all `p²` one-dimensional representations, each occurring once
    (`tensor_character_inv`).

The one-dimensional characters (there are `p²` of them) are classified in Problem 4.12.2
(`one_dim_reps_card`); the tensor product of a character with any irreducible just twists it.

The source asserts decompositions of *representations*, not merely of characters, so the final
section upgrades all four to isomorphisms in `FDRep ℂ (Heisenberg p)` by feeding the character
identities to `Etingof.charEq_iso` and building the right-hand sides with
`Etingof.FDRep.pi` (the direct sum of a finite family, `Infrastructure/FDRepDirectSum`):

* `tensor_iso_Rz_mul`: `R_z ⊗ R_w ≅ ⨁_{Fin p} R_{zw}` when `z·w ≠ 1`;
* `tensor_iso_oneDimSum`: `R_z ⊗ R_w ≅ ⨁_{χ : G →* ℂˣ} χ` when `z·w = 1`;
* `tensor_iso_char_char`: `χ ⊗ χ' ≅ χχ'` (canonically, via `tensorIsoCharChar`);
* `tensor_iso_char_Rz`: `χ ⊗ R_z ≅ R_z`.

`Etingof.FDRep.pi` is proved to be the categorical biproduct, so the two direct-sum statements
are also available in `⨁` form (`tensor_iso_Rz_mul_biproduct`,
`tensor_iso_oneDimSum_biproduct`).
-/

noncomputable section

open Etingof.Problem4_12_2 Etingof.Problem4_12_2.Heisenberg

namespace Etingof.Problem4_12_9

variable {p : ℕ}

/-- `IsRz z ρ` says the representation `ρ` on `V = ZMod p → ℂ` realizes `R_z`: it acts on the
generators by the shift and the multiplication-by-`z^t` operators. -/
def IsRz (z : ℂ) (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) : Prop :=
  (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1)) ∧
  (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t)

/-- Any `ρ` realizing `R_z` is *the* representation `rhoHom z hz` of Problem 4.12.2, by the
uniqueness half of `exists_unique_rep`. -/
theorem isRz_eq_rhoHom [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ) :
    ρ = rhoHom z hz := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w, _hw, huniq⟩ := exists_unique_rep z hz
  rw [huniq ρ hρ,
    huniq (rhoHom z hz) ⟨fun f t => rhoHom_xGen z hz f t, fun f t => rhoHom_yGen z hz f t⟩]

/-- For a nontrivial `p`-th root of unity `z`, the geometric sum `∑_{u ∈ ZMod p} z^{u.val}`
vanishes: multiplying by `z` permutes the summands (`u ↦ u+1`), so the sum is `z`-invariant,
hence `(z-1)·S = 0` and `S = 0`. -/
theorem sum_zpow_val_eq_zero [Fact p.Prime] {z : ℂ} (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    ∑ u : ZMod p, z ^ u.val = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have step : ∀ u : ZMod p, z * z ^ u.val = z ^ (u + 1).val := by
    intro u
    rw [← pow_succ', ZMod.val_add, ZMod.val_one, zpow_mod hz]
  have key : z * (∑ u : ZMod p, z ^ u.val) = ∑ u : ZMod p, z ^ u.val :=
    calc z * (∑ u : ZMod p, z ^ u.val)
        = ∑ u : ZMod p, z * z ^ u.val := by rw [Finset.mul_sum]
      _ = ∑ u : ZMod p, z ^ (u + 1).val := Finset.sum_congr rfl (fun u _ => step u)
      _ = ∑ v : ZMod p, z ^ v.val :=
            Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun _ => rfl)
  have h0 : (z - 1) * (∑ u : ZMod p, z ^ u.val) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hz1
  · exact h

/-- `z^{(-c).val} = (z⁻¹)^{c.val}` for a `p`-th root of unity `z`: the exponents `(-c).val` and
`c.val` sum to `0` modulo `p`, so `z^{(-c).val}·z^{c.val} = 1`. -/
theorem zpow_neg_val [NeZero p] {z : ℂ} (hz : z ^ p = 1) (c : ZMod p) :
    z ^ ((-c).val) = (z⁻¹) ^ c.val := by
  have hmod : ((-c).val + c.val) % p = 0 := by
    have h := ZMod.val_add (-c) c
    rw [neg_add_cancel, ZMod.val_zero] at h
    exact h.symm
  have hmul : z ^ ((-c).val) * z ^ c.val = 1 := by
    rw [← pow_add, ← zpow_mod hz ((-c).val + c.val), hmod, pow_zero]
  rw [inv_pow, eq_comm]
  exact inv_eq_of_mul_eq_one_left hmul

/-- The trace of the operator `rhoLin z g` on `V = ZMod p → ℂ`. Only the diagonal survives, and
it is nonzero only when `g.a = 0`; then the geometric sum over the fibre kills it unless also
`g.b = 0`, in which case the operator is the scalar `z^{-g.c}` on a `p`-dimensional space. -/
theorem trace_rhoLin [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (g : Heisenberg p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (rhoLin z g) =
      if g.a = 0 ∧ g.b = 0 then (p : ℂ) * (z⁻¹) ^ g.c.val else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod p))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, rhoLin_apply, Pi.single_apply, sub_eq_self]
  rw [← Finset.sum_mul]
  by_cases ha : g.a = 0
  · rw [if_pos ha, mul_one]
    by_cases hb : g.b = 0
    · rw [if_pos ⟨ha, hb⟩, hb]
      simp only [zero_mul, zero_sub]
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, zpow_neg_val hz g.c]
    · rw [if_neg (fun h => hb h.2),
        Fintype.sum_equiv ((Equiv.mulLeft₀ g.b hb).trans (Equiv.subRight g.c))
          (fun i => z ^ (g.b * i - g.c).val) (fun u => z ^ u.val) (fun _ => rfl)]
      exact sum_zpow_val_eq_zero hz hz1
  · rw [if_neg ha, mul_zero, if_neg (fun h => ha h.1)]

/-- **Character of `R_z`.** For a `p`-th root of unity `z ≠ 1`, the character of `R_z`
vanishes off the center and takes the value `p · z^{-c}` on the central element `⟨0,0,c⟩`. -/
theorem character_Rz [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) * (z⁻¹) ^ c.val else 0 := by
  rw [isRz_eq_rhoHom z hz ρ hρ, rhoHom_apply]
  exact trace_rhoLin z hz hz1 ⟨a, b, c⟩

/-- **Tensor product `R_z ⊗ R_w`, generic case (`z·w ≠ 1`).** The character of the tensor
product (the pointwise product of characters) equals `p` times the character of `R_{zw}`,
i.e. `R_z ⊗ R_w ≅ p · R_{zw}`. -/
theorem tensor_character_nonone [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) (hρzw : IsRz (z * w) ρzw)
    (g : Heisenberg p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz g) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw g) =
      (p : ℂ) * LinearMap.trace ℂ (ZMod p → ℂ) (ρzw g) := by
  obtain ⟨a, b, c⟩ := g
  rw [character_Rz z hz hz1 ρz hρz a b c,
      character_Rz w hw hw1 ρw hρw a b c,
      character_Rz (z * w) (by rw [mul_pow, hz, hw, mul_one]) hzw ρzw hρzw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    rw [mul_inv, mul_pow]; ring
  · simp only [if_neg h, mul_zero]

/-- **Tensor product `R_z ⊗ R_{z⁻¹}` (`z·w = 1`).** The character of the tensor product equals
`p²` on the center and `0` elsewhere: this is the character of the direct sum of all `p²`
one-dimensional representations, each occurring exactly once. -/
theorem tensor_character_inv [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz ⟨a, b, c⟩) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) ^ 2 else 0 := by
  have hw : w ^ p = 1 := by
    have hzwp : (z * w) ^ p = 1 := by rw [hzw, one_pow]
    rw [mul_pow, hz, one_mul] at hzwp; exact hzwp
  rw [character_Rz z hz hz1 ρz hρz a b c,
      character_Rz w hw hw1 ρw hρw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    have hone : (z⁻¹) ^ c.val * (w⁻¹) ^ c.val = 1 := by
      rw [← mul_pow, ← mul_inv, hzw, inv_one, one_pow]
    rw [show ((p : ℂ) * (z⁻¹) ^ c.val) * ((p : ℂ) * (w⁻¹) ^ c.val)
          = (p : ℂ) ^ 2 * ((z⁻¹) ^ c.val * (w⁻¹) ^ c.val) from by ring, hone, mul_one]
  · simp only [if_neg h, mul_zero]

/-! ## One-dimensional characters and their tensor products

The remaining irreducibles of the Heisenberg group are the `p²` one-dimensional characters
`χ : Heisenberg p →* ℂˣ` (Problem 4.12.2, `one_dim_reps_card`), realized as `charRep χ` on `ℂ`.
Their characters and tensor products complete the answer to Problem 4.12.9. -/

/-- **Character of a one-dimensional character.** The character of `charRep χ` (the `1×1` block
`g ↦ χ g`) is `g ↦ (χ g : ℂ)`. -/
theorem character_charRep (χ : Heisenberg p →* ℂˣ) (g : Heisenberg p) :
    LinearMap.trace ℂ ℂ (Etingof.Example4_3_S3.charRep χ g) = (χ g : ℂ) := by
  have hg : Etingof.Example4_3_S3.charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  rw [hg, map_smul, LinearMap.trace_id]
  simp

/-- **Tensor product of two one-dimensional characters.** The character of `χ ⊗ χ'` is the
pointwise product of characters, `g ↦ (χ g)·(χ' g) = ((χ·χ') g)`, so `χ ⊗ χ' ≅ charRep (χ·χ')`.
The `p²` characters thus form a group under tensor product. -/
theorem tensor_character_char_char (χ χ' : Heisenberg p →* ℂˣ) (g : Heisenberg p) :
    LinearMap.trace ℂ ℂ (Etingof.Example4_3_S3.charRep χ g) *
        LinearMap.trace ℂ ℂ (Etingof.Example4_3_S3.charRep χ' g) =
      LinearMap.trace ℂ ℂ (Etingof.Example4_3_S3.charRep (χ * χ') g) := by
  rw [character_charRep, character_charRep, character_charRep, MonoidHom.mul_apply, Units.val_mul]

/-- **Tensor product of a character with `R_z`.** For a one-dimensional character `χ` and a
`p`-dimensional `R_z` (`z ≠ 1`), the character of `χ ⊗ R_z` equals that of `R_z`, i.e.
`χ ⊗ R_z ≅ R_z`. The twist collapses: `character_Rz` is supported on the center, where every
character `χ` is trivial (`χ ⟨0,0,c⟩ = 1`, as characters kill the abelianization kernel,
`abHom_ker_le_ker`). -/
theorem tensor_character_char_Rz [Fact p.Prime] (χ : Heisenberg p →* ℂˣ)
    (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ)
    (a b c : ZMod p) :
    LinearMap.trace ℂ ℂ (Etingof.Example4_3_S3.charRep χ ⟨a, b, c⟩) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
      LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) := by
  rw [character_charRep, character_Rz z hz hz1 ρ hρ a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    have hcentral : χ ⟨a, b, c⟩ = 1 := by
      have hmem : (⟨a, b, c⟩ : Heisenberg p) ∈ (abHom p).ker := by
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd (a, b) = 1
        rw [h.1, h.2]; rfl
      exact MonoidHom.mem_ker.mp (abHom_ker_le_ker χ hmem)
    rw [hcentral, Units.val_one, one_mul]
  · simp only [if_neg h, mul_zero]

/-! ## From character identities to isomorphisms of representations

The identities above compare characters. The book's Problem 4.12.9 asserts genuine
decompositions of representations, so we upgrade each of them: `Etingof.charEq_iso`
(Chapter 5) turns an equality of characters of finite-dimensional complex representations of a
finite group into an isomorphism in `FDRep ℂ (Heisenberg p)`, and `Etingof.FDRep.character_pi`
computes the character of the finite direct sum `Etingof.FDRep.pi`. The four isomorphisms

* `R_z ⊗ R_w ≅ p·R_{zw}` (`tensor_iso_Rz_mul`),
* `R_z ⊗ R_{z⁻¹} ≅ ⨁_χ χ` (`tensor_iso_oneDimSum`),
* `χ ⊗ χ' ≅ χχ'` (`tensor_iso_char_char`),
* `χ ⊗ R_z ≅ R_z` (`tensor_iso_char_Rz`)

are the actual content of the problem; the character identities above are the computations they
rest on. The two direct-sum cases are restated with the categorical `⨁` in
`tensor_iso_Rz_mul_biproduct` and `tensor_iso_oneDimSum_biproduct`, using
`Etingof.FDRep.piIsoBiproduct`.

Only `χ ⊗ χ' ≅ χχ'` has a canonical intertwiner (multiplication `ℂ ⊗_ℂ ℂ ≃ ℂ`), given as an
actual `Iso` in `tensorIsoCharChar`. The other three isomorphisms are genuinely non-canonical —
`charEq_iso` produces one from a character computation without singling one out — so they are
stated as `Nonempty (· ≅ ·)`, as elsewhere in the project (`charRep_iso_iff`,
`rhoHom_iso_iff`). -/

section Isomorphisms

open CategoryTheory MonoidalCategory

variable [Fact p.Prime]

/-- The character group of the Heisenberg group is finite: it has exactly `p²` elements by
Problem 4.12.2 (`one_dim_reps_card`). -/
instance instFiniteHeisenbergCharGroup : Finite (Heisenberg p →* ℂˣ) :=
  Nat.finite_of_card_ne_zero
    (by rw [one_dim_reps_card]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)

noncomputable instance instFintypeHeisenbergCharGroup : Fintype (Heisenberg p →* ℂˣ) :=
  Fintype.ofFinite _

/-- The character of `FDRep.of ρ` is the trace of `ρ`. -/
theorem character_of (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (g : Heisenberg p) :
    (FDRep.of ρ).character g = LinearMap.trace ℂ (ZMod p → ℂ) (ρ g) := rfl

/-- **Sum of all one-dimensional characters.** Summing the `p²` characters of the Heisenberg
group at `⟨a,b,c⟩` gives `p²` on the center and `0` off it: every character factors through the
abelianization `(ZMod p)²` (`oneDimRepEquiv`), where this is the orthogonality relation
`Etingof.sum_char_apply`. This is exactly the character of `⨁_χ χ`. -/
theorem sum_oneDimChar (a b c : ZMod p) :
    ∑ χ : Heisenberg p →* ℂˣ, (χ ⟨a, b, c⟩ : ℂ) =
      if a = 0 ∧ b = 0 then (p : ℂ) ^ 2 else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod p × ZMod p) →* ℂˣ) :=
    Finite.of_equiv _ (oneDimRepEquiv p).symm
  haveI : Fintype (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := Fintype.ofFinite _
  have hre : ∑ χ : Heisenberg p →* ℂˣ, (χ ⟨a, b, c⟩ : ℂ) =
      ∑ ψ : Multiplicative (ZMod p × ZMod p) →* ℂˣ,
        ((ψ (Multiplicative.ofAdd (a, b)) : ℂ)) :=
    (Fintype.sum_equiv (oneDimRepEquiv p) _ _ fun _ => rfl).symm
  rw [hre, Etingof.sum_char_apply]
  have hiff : ((a, b) : ZMod p × ZMod p) = 0 ↔ (a = 0 ∧ b = 0) := by
    simp [Prod.ext_iff]
  have hcard : (Fintype.card (ZMod p × ZMod p) : ℂ) = (p : ℂ) ^ 2 := by
    rw [Fintype.card_prod, ZMod.card]
    push_cast
    ring
  by_cases h : a = 0 ∧ b = 0
  · rw [if_pos (hiff.mpr h), if_pos h, hcard]
  · rw [if_neg fun hab => h (hiff.mp hab), if_neg h]

/-- **`R_z ⊗ R_w ≅ p·R_{zw}` (generic case `z·w ≠ 1`).** For nontrivial `p`-th roots of unity
`z, w` with `z·w ≠ 1`, the tensor product of `R_z` and `R_w` is isomorphic to the direct sum of
`p` copies of `R_{zw}`. Both sides are `p²`-dimensional, and their characters agree by
`tensor_character_nonone`. -/
theorem tensor_iso_Rz_mul
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) (hρzw : IsRz (z * w) ρzw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw : FDRep ℂ (Heisenberg p)) ≅
      Etingof.FDRep.pi fun _ : Fin p => FDRep.of ρzw) := by
  refine Etingof.charEq_iso _ _ (funext fun g => ?_)
  rw [FDRep.char_tensor, Pi.mul_apply, Etingof.FDRep.character_pi, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, character_of, character_of, character_of]
  exact tensor_character_nonone z w hz hw hz1 hw1 hzw ρz ρw ρzw hρz hρw hρzw g

/-- **`R_z ⊗ R_{z⁻¹} ≅ ⨁_χ χ`.** When `z·w = 1` the tensor product of `R_z` and `R_w` is
isomorphic to the direct sum of *all* `p²` one-dimensional characters of the Heisenberg group,
each occurring exactly once. Both sides are `p²`-dimensional; the characters agree by
`tensor_character_inv` and `sum_oneDimChar`. -/
theorem tensor_iso_oneDimSum
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw : FDRep ℂ (Heisenberg p)) ≅
      Etingof.FDRep.pi fun χ : Heisenberg p →* ℂˣ =>
        FDRep.of (Etingof.Example4_3_S3.charRep χ)) := by
  refine Etingof.charEq_iso _ _ (funext fun g => ?_)
  obtain ⟨a, b, c⟩ := g
  rw [FDRep.char_tensor, Pi.mul_apply, Etingof.FDRep.character_pi, character_of, character_of]
  simp only [Etingof.Example4_3_S3.charRep_character]
  rw [sum_oneDimChar a b c]
  exact tensor_character_inv z w hz hz1 hw1 hzw ρz ρw hρz hρw a b c

/-- `R_z ⊗ R_w ≅ ⨁_{Fin p} R_{zw}`, stated with the categorical biproduct: `Etingof.FDRep.pi`
is the biproduct (`Etingof.FDRep.piIsoBiproduct`), so this is `tensor_iso_Rz_mul` transported
along that comparison. -/
theorem tensor_iso_Rz_mul_biproduct
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) (hρzw : IsRz (z * w) ρzw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw : FDRep ℂ (Heisenberg p)) ≅
      ⨁ fun _ : Fin p => FDRep.of ρzw) :=
  (tensor_iso_Rz_mul z w hz hw hz1 hw1 hzw ρz ρw ρzw hρz hρw hρzw).map fun e =>
    e ≪≫ Etingof.FDRep.piIsoBiproduct _

/-- `R_z ⊗ R_{z⁻¹} ≅ ⨁_χ χ`, stated with the categorical biproduct. -/
theorem tensor_iso_oneDimSum_biproduct
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw : FDRep ℂ (Heisenberg p)) ≅
      ⨁ fun χ : Heisenberg p →* ℂˣ => FDRep.of (Etingof.Example4_3_S3.charRep χ)) := by
  classical
  exact (tensor_iso_oneDimSum z w hz hz1 hw1 hzw ρz ρw hρz hρw).map fun e =>
    e ≪≫ Etingof.FDRep.piIsoBiproduct _

omit [Fact p.Prime] in
/-- **`χ ⊗ χ' ≅ χχ'`, canonically.** Unlike the other three decompositions this one has a
canonical intertwiner: multiplication `ℂ ⊗_ℂ ℂ ≃ ℂ` (`TensorProduct.lid`) already carries
`χ ⊗ χ'` to `χχ'`. -/
def tensorIsoCharChar (χ χ' : Heisenberg p →* ℂˣ) :
    (FDRep.of (Etingof.Example4_3_S3.charRep χ) ⊗
        FDRep.of (Etingof.Example4_3_S3.charRep χ') : FDRep ℂ (Heisenberg p)) ≅
      FDRep.of (Etingof.Example4_3_S3.charRep (χ * χ')) :=
  Action.mkIso (TensorProduct.lid ℂ ℂ).toFGModuleCatIso fun g => by
    apply FGModuleCat.hom_ext
    refine TensorProduct.ext' fun a b => ?_
    change (TensorProduct.lid ℂ ℂ)
        (TensorProduct.map ((Etingof.Example4_3_S3.charRep χ) g)
          ((Etingof.Example4_3_S3.charRep χ') g) (a ⊗ₜ[ℂ] b))
      = (Etingof.Example4_3_S3.charRep (χ * χ')) g ((TensorProduct.lid ℂ ℂ) (a ⊗ₜ[ℂ] b))
    simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, Etingof.Example4_3_S3.charRep,
      MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring

omit [Fact p.Prime] in
/-- **`χ ⊗ χ' ≅ χχ'`.** The tensor product of two one-dimensional characters is the
one-dimensional representation attached to their product; the `p²` characters form a group
under tensor product. -/
theorem tensor_iso_char_char (χ χ' : Heisenberg p →* ℂˣ) :
    Nonempty ((FDRep.of (Etingof.Example4_3_S3.charRep χ) ⊗
        FDRep.of (Etingof.Example4_3_S3.charRep χ') : FDRep ℂ (Heisenberg p)) ≅
      FDRep.of (Etingof.Example4_3_S3.charRep (χ * χ'))) :=
  ⟨tensorIsoCharChar χ χ'⟩

/-- **`χ ⊗ R_z ≅ R_z`.** Twisting the `p`-dimensional irreducible `R_z` by a one-dimensional
character does nothing: `character_Rz` is supported on the center, where every character of the
Heisenberg group is trivial. -/
theorem tensor_iso_char_Rz (χ : Heisenberg p →* ℂˣ)
    (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ) :
    Nonempty ((FDRep.of (Etingof.Example4_3_S3.charRep χ) ⊗
        FDRep.of ρ : FDRep ℂ (Heisenberg p)) ≅ FDRep.of ρ) := by
  refine Etingof.charEq_iso _ _ (funext fun g => ?_)
  obtain ⟨a, b, c⟩ := g
  rw [FDRep.char_tensor, Pi.mul_apply, character_of,
    Etingof.Example4_3_S3.charRep_character, ← character_charRep χ (⟨a, b, c⟩ : Heisenberg p)]
  exact tensor_character_char_Rz χ z hz hz1 ρ hρ a b c

end Isomorphisms

end Etingof.Problem4_12_9
