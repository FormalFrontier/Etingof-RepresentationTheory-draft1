import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1

/-!
# Exercise 5.27.2 (dihedral group): redo Problem 4.12.1(a) using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.1(a)** part: describe all irreducible complex
representations of the dihedral group `D_N`, the symmetry group of a regular `N`-gon (order
`2N`), distinguishing the cases of odd and even `N`.

## The dihedral group as a semidirect product

`D_N = ⟨r, s | rᴺ = s² = 1, s r s⁻¹ = r⁻¹⟩` is the semidirect product of the cyclic rotation
group `A = ⟨r⟩ ≅ ℤ/N` (abelian, normal) by the order-two reflection group `G = ⟨s⟩ ≅ ℤ/2`,
where `s` acts on `A` by inversion `r ↦ r⁻¹`. So `Theorem 5.27.1` (the orbit method for
`A ⋊ G` with `A` abelian) applies with `A = Multiplicative (ZMod N)`, `G = Multiplicative
(ZMod 2)`, and `φ` sending the reflection to the inversion automorphism.

We state the classification for Mathlib's `DihedralGroup N` (the concrete group of `N`-gon
symmetries); the docstrings record how Theorem 5.27.1 produces it. The dual `G`-action on
`Â = A →* ℂˣ ≅ ℤ/N` is again inversion `χ ↦ χ⁻¹`, so the orbits are:

* the fixed characters (`χ = χ⁻¹`), whose stabilizer is all of `G`; each contributes two
  `1`-dimensional irreducibles (one per character of `G ≅ ℤ/2`);
* the free orbit-pairs `{χ, χ⁻¹}` with `χ ≠ χ⁻¹`, whose stabilizer is trivial; each
  contributes one `2`-dimensional irreducible `V(χ, U)` of dimension `[G : G_χ] = 2`.

The number of fixed characters is `gcd(2, N)`: for `N` odd only `χ = 1` is fixed (one
character, two `1`-dim irreps), and for `N` even both `χ = 1` and the order-two character
are fixed (two characters, four `1`-dim irreps). The remaining `N - gcd(2,N)` nontrivial
characters split into `(N - gcd(2,N))/2` free orbit-pairs, giving that many `2`-dimensional
irreducibles.

## The classification (Problem 4.12.1(a))

* `N` odd: `2` irreducibles of dimension `1` and `(N-1)/2` of dimension `2`
  (`∑ dim² = 2 + 4·(N-1)/2 = 2N`);
* `N` even: `4` irreducibles of dimension `1` and `(N-2)/2` of dimension `2`
  (`∑ dim² = 4 + 4·(N-2)/2 = 2N`).

Statement pass: the classification is stated; the proof is left as `sorry`.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (N : ℕ) [NeZero N]

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.1(a).** The complete classification of the irreducible
complex representations of the dihedral group `D_N` (symmetries of a regular `N`-gon, order
`2N`), obtained from Theorem 5.27.1 via the semidirect-product structure `⟨r⟩ ⋊ ⟨s⟩` with `s`
acting by inversion. Every irreducible has dimension `1` or `2`, and the number of each kind
depends on the parity of `N`: for `N` odd there are `2` of dimension `1` and `(N-1)/2` of
dimension `2`; for `N` even there are `4` of dimension `1` and `(N-2)/2` of dimension `2`.
In both cases `∑ dim² = 2N = |D_N|`. -/
theorem dihedral_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralGroup N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralGroup N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  sorry

end Etingof.Exercise5_27_2
