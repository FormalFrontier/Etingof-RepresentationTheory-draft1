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

/-! ## The semidirect-product model `⟨r⟩ ⋊ ⟨s⟩`

We realize `D_N` as `Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)`, with the
order-two group acting on the rotation group by inversion. This is the shape Theorem 5.27.1
consumes (`A ⋊[φ] G` with `A` abelian). -/

/-- Inversion `a ↦ a⁻¹` as an automorphism of the (commutative) rotation group. -/
def invAut : MulAut (Multiplicative (ZMod N)) := MulEquiv.inv _

@[simp] lemma invAut_apply (a : Multiplicative (ZMod N)) : invAut N a = a⁻¹ := rfl

@[simp] lemma invAut_mul_self : invAut N * invAut N = 1 := by
  ext a; simp [MulAut.mul_apply]

/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- The action of the reflection group `Multiplicative (ZMod 2)` on the rotation group: the
generator `ofAdd 1` acts by inversion, the identity acts trivially. -/
def dihedralφ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod N)) where
  toFun g := if Multiplicative.toAdd g = 0 then 1 else invAut N
  map_one' := by simp
  map_mul' a b := by
    rcases zmod2_cases a.toAdd with ha | ha <;> rcases zmod2_cases b.toAdd with hb | hb <;>
      simp only [toAdd_mul, ha, hb, invAut_mul_self, one_mul, mul_one,
        show (0:ZMod 2)+0 = 0 by decide, show (0:ZMod 2)+1 = 1 by decide,
        show (1:ZMod 2)+0 = 1 by decide, show (1:ZMod 2)+1 = 0 by decide,
        show ¬ (1:ZMod 2) = 0 by decide, if_true, if_false, reduceIte]

@[simp] lemma dihedralφ_one : dihedralφ N 1 = 1 := map_one _

@[simp] lemma dihedralφ_ofAdd_one : dihedralφ N (Multiplicative.ofAdd 1) = invAut N := by
  simp only [dihedralφ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, reduceIte,
    show ¬ (1 : ZMod 2) = 0 by decide]

/-- `D_N` presented as the semidirect product `⟨r⟩ ⋊ ⟨s⟩`. -/
abbrev DihedralSemidirect : Type := Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)

/-- The group isomorphism `D_N ≃* ⟨r⟩ ⋊ ⟨s⟩` sending a rotation `r i` to `⟨ofAdd i, 1⟩` and a
reflection `sr i` to `⟨ofAdd (-i), ofAdd 1⟩`. (Under Mathlib's convention `r i * sr j = sr (j - i)`
the reflection generator carries the sign, so `⟨ofAdd i, ofAdd 1⟩` would *not* be a homomorphism.) -/
def dihedralEquiv : DihedralGroup N ≃* DihedralSemidirect N where
  toFun := fun
    | .r i => ⟨Multiplicative.ofAdd i, 1⟩
    | .sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd 1⟩
  invFun := fun p =>
    if Multiplicative.toAdd p.right = 0 then .r (Multiplicative.toAdd p.left)
    else .sr (-(Multiplicative.toAdd p.left))
  left_inv := by
    rintro (i | i)
    · simp [toAdd_ofAdd]
    · simp only [toAdd_ofAdd, reduceIte, show ¬ (1 : ZMod 2) = 0 by decide, neg_neg]
  right_inv := by
    intro p
    rcases zmod2_cases p.right.toAdd with hg | hg
    · have hr : p.right = 1 := toAdd_eq_zero.mp hg
      simp only [hg, reduceIte]
      ext <;> simp [ofAdd_toAdd, hr]
    · have hr : p.right = Multiplicative.ofAdd 1 := by rw [← ofAdd_toAdd p.right, hg]
      simp only [hg, show ¬ (1 : ZMod 2) = 0 by decide, reduceIte]
      ext <;> simp [ofAdd_toAdd, hr, neg_neg]
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      ext <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, dihedralφ_one,
        dihedralφ_ofAdd_one, ofAdd_neg, mul_comm, sub_eq_add_neg, neg_add,
        show (1 : ZMod 2) + 1 = 0 by decide]

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
