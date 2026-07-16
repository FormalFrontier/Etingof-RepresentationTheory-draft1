import Mathlib

/-!
# The dimension of a complex irreducible representation divides `|G|`

This file works toward the classical theorem of Frobenius: the dimension of a
complex irreducible representation of a finite group `G` divides the order of
`G`. It is the general, reusable ingredient behind the odd-order crux of
Problem 6.1.6(c) (`isCyclic_of_odd_card`): a group of odd order has no
`2`-dimensional irreducible representation, because `2 ∤ |G|`.

The development is top-down (see the project's `CLAUDE.md`): the headline
theorem `finrank_dvd_card_of_irreducible` and the central-character step
`isIntegral_classSum_scalar` are stated with `sorry` proofs, while the
self-contained "character values are algebraic integers" step
(`FDRep.isIntegral_character`) is proved here in full.

## Main results

* `isIntegral_int_of_pow_eq_one`: a complex root of unity is an algebraic
  integer (root of the monic `X ^ n - 1`).
* `FDRep.isIntegral_character`: **character values are algebraic integers.**
  The eigenvalues of `ρ g` are roots of unity (`ρ g` has finite order), and the
  character `χ_V(g)` is their sum, hence integral over `ℤ`.
* `finrank_dvd_card_of_irreducible` (`sorry`): the Frobenius divisibility
  theorem itself.

## References

Etingof et al., *Introduction to Representation Theory*; the theorem is standard
(Frobenius). Building blocks used: `Matrix.trace_eq_sum_roots_charpoly`,
`Matrix.eval_charpoly`, `Matrix.exists_mulVec_eq_zero_iff`,
`IsIntegrallyClosed`/`Niven` (rational algebraic integers are integers),
`FDRep.scalar_product_char_eq_finrank_equivariant`.
-/

open Polynomial Matrix Module CategoryTheory

/-- A complex number `r` with `r ^ n = 1` for some `0 < n` is integral over `ℤ`:
it is a root of the monic integer polynomial `X ^ n - 1`. -/
theorem isIntegral_int_of_pow_eq_one {r : ℂ} {n : ℕ} (hn : 0 < n) (h : r ^ n = 1) :
    IsIntegral ℤ r := by
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp [h]

namespace FDRep

variable {G : Type*} [Group G] [Finite G]

/-- **Character values are algebraic integers.**

For a finite group `G`, a complex representation `V`, and `g : G`, the character
value `χ_V(g) = tr(ρ g)` is integral over `ℤ`.

Proof: `ρ g` has finite order `n` (as `G` is finite), so, in a basis, its matrix
`A` satisfies `A ^ n = 1`. Over `ℂ` the trace equals the sum of the roots of the
characteristic polynomial; each such root `r` is an eigenvalue, so `A *ᵥ v = r • v`
for some `v ≠ 0`, whence `r ^ n • v = (A ^ n) *ᵥ v = v` forces `r ^ n = 1`. Thus
every root is a root of unity, hence an algebraic integer, and their sum `χ_V(g)`
is too. -/
theorem isIntegral_character (V : FDRep ℂ G) (g : G) : IsIntegral ℤ (V.character g) := by
  classical
  -- `ρ g` has finite order `n`, and `(ρ g) ^ n = 1`.
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  set n := orderOf g with hn
  have hn0 : 0 < n := hfin.orderOf_pos
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hρ : (V.ρ g) ^ n = 1 := by rw [← map_pow, hgn, map_one]
  -- Work in a finite basis; let `A` be the matrix of `ρ g`.
  set d := finrank ℂ V with hd
  set b := Module.finBasis ℂ V with hb
  set A : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (V.ρ g) with hA
  have hAn : A ^ n = 1 := by
    rw [hA, LinearMap.toMatrix_pow, hρ, LinearMap.toMatrix_one]
  -- The character is the matrix trace, hence the sum of the charpoly roots.
  have htr : V.character g = A.trace := by
    rw [show V.character g = LinearMap.trace ℂ V (V.ρ g) from rfl,
      LinearMap.trace_eq_matrix_trace ℂ b (V.ρ g)]
  have hsum : V.character g = (A.charpoly.roots).sum := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  -- Each root of the charpoly is a root of unity, hence integral over `ℤ`.
  have hroot : ∀ r ∈ A.charpoly.roots, IsIntegral ℤ r := by
    intro r hr
    -- `r` is a genuine root of the characteristic polynomial.
    have hIsRoot : A.charpoly.IsRoot r := (Polynomial.mem_roots'.mp hr).2
    -- so `det (scalar r - A) = 0`, giving an eigenvector `v ≠ 0` with `A *ᵥ v = r • v`.
    have hdet : (Matrix.scalar (Fin d) r - A).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact hIsRoot
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hscal : (Matrix.scalar (Fin d) r) *ᵥ v = r • v := by
      rw [Matrix.scalar_apply]
      funext x
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    have hev : A *ᵥ v = r • v := by
      have hsub : (Matrix.scalar (Fin d) r) *ᵥ v - A *ᵥ v = 0 := by
        rw [← Matrix.sub_mulVec]; exact hMv
      rw [hscal] at hsub
      exact (sub_eq_zero.mp hsub).symm
    -- iterate the eigenvalue relation: `(A ^ k) *ᵥ v = r ^ k • v`.
    have hpow : ∀ k, (A ^ k) *ᵥ v = r ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
    -- `r ^ n • v = (A ^ n) *ᵥ v = 1 *ᵥ v = v`, and `v ≠ 0` forces `r ^ n = 1`.
    have hrn : r ^ n = 1 := by
      have he := hpow n
      rw [hAn, Matrix.one_mulVec] at he
      have hz : (r ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv0
    exact isIntegral_int_of_pow_eq_one hn0 hrn
  -- the sum of algebraic integers is an algebraic integer
  rw [hsum]
  exact IsIntegral.multiset_sum hroot

/-- **Central character integrality (Frobenius, step 2).**

For an irreducible `V` and a conjugacy class with representative `g₀` and size
`c`, the scalar `ω = c · χ_V(g₀) / d` by which the class sum acts on `V` is
integral over `ℤ`. The class sums form a `ℤ`-basis of the center of the integral
group ring `ℤ[G]`, a ring module-finite over `ℤ`, so every element is integral
over `ℤ` (`Algebra.IsIntegral.of_finite`); the central character is a ring hom
to `ℂ`, and ring homs preserve integrality.

TODO (#6714): build the integral group ring center / class-sum machinery. -/
theorem isIntegral_classSum_scalar (V : FDRep ℂ G) [Simple V] (g₀ : G) :
    IsIntegral ℤ ((Nat.card {x // IsConj g₀ x} : ℂ) * V.character g₀ / (finrank ℂ V : ℂ)) := by
  sorry

end FDRep

/-- **Frobenius' theorem: the dimension of a complex irreducible representation of
a finite group divides the group order.**

Proof (top-down; see #6714): with `d = finrank ℂ V` and `χ = V.character`, Schur
orthogonality `⟨χ, χ⟩ = 1` gives `|G| = ∑_C c · |χ(g_C)|²`, so
`|G| / d = ∑_C ω_C · conj(χ(g_C))` with `ω_C = c · χ(g_C) / d`. Each `ω_C`
(`FDRep.isIntegral_classSum_scalar`) and each `conj(χ(g_C))`
(`FDRep.isIntegral_character`, closed under complex conjugation) is an algebraic
integer, so `|G| / d ∈ ℚ` is an algebraic integer, hence an integer
(`ℤ` is integrally closed in `ℚ`); therefore `d ∣ |G|`. -/
theorem finrank_dvd_card_of_irreducible {G : Type*} [Group G] [Fintype G]
    (V : FDRep ℂ G) [Simple V] : Module.finrank ℂ V ∣ Fintype.card G := by
  sorry
