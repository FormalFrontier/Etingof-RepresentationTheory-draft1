import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1

/-!
# Exercise 5.27.2 (affine group): redo Problem 4.12.6 using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.6** part: the group `G` of nonconstant inhomogeneous linear
transformations `x ↦ a x + b` over a finite field `K` (with `a ∈ Kˣ`, `b ∈ K`). Problem 4.12.6 asks
for all irreducible complex representations of `G` and their characters. Theorem 5.27.1 (the orbit
method for semidirect products `A ⋊ G` with `A` abelian) supplies them directly, because the affine
group is a semidirect product of the abelian translation group by the multiplicative group.

## The affine group as a semidirect product

Composition of `x ↦ a₁ x + b₁` after `x ↦ a₂ x + b₂` sends `x ↦ a₁ a₂ x + (a₁ b₂ + b₁)`. Writing the
additive translation group `(K, +)` multiplicatively as `Multiplicative K` and letting `Kˣ` act on
it by multiplication, this is exactly the semidirect-product multiplication
`⟨b₁, a₁⟩ * ⟨b₂, a₂⟩ = ⟨b₁ · φ(a₁)(b₂), a₁ a₂⟩`. So

`AffineGroup K := Multiplicative K ⋊[affineφ K] Kˣ`,

where `affineφ K : Kˣ →* MulAut (Multiplicative K)` is multiplication by a unit, obtained from the
distributive `Kˣ`-action on the ring `K` via `AddAut.mulLeft` and the identification
`MulAut (Multiplicative K) ≃* Multiplicative (AddAut K)`.

## The classification (orbit method, Theorem 5.27.1)

Here `A = Multiplicative K` (order `q = |K|`) and `G = Kˣ` (order `q - 1`), so `|AffineGroup K| =
q(q - 1)`. The dual `G`-action on `Â = A →* ℂˣ` has two orbits: the trivial character `{1}` (fixed,
stabilizer all of `Kˣ`) and the single free orbit of all `q - 1` nontrivial characters (stabilizer
trivial). Theorem 5.27.1 then yields:

* over the fixed character `1`, one irreducible `V(1, U)` for each irreducible `U` of `Kˣ`, i.e. the
  `q - 1` one-dimensional characters of `AffineGroup K` factoring through `Kˣ`;
* over the free orbit, a single irreducible `V(χ, U)` (with `U` the trivial rep of the trivial
  stabilizer) of dimension `[G : G_χ] = q - 1`.

Thus there are exactly `q` irreducibles: `q - 1` of dimension `1` and one of dimension `q - 1`
(consistent with `∑ dim² = (q - 1)·1 + (q - 1)² = q(q - 1) = |AffineGroup K|`).

Statement pass: the classification is stated; the proof is left as `sorry`.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (K : Type) [Field K] [Fintype K]

/-- The action of `Kˣ` on the translation group `(K, +) = Multiplicative K` by multiplication:
`affineφ K a` is `b ↦ a · b`. Built from the distributive `Kˣ`-action on the ring `K`. -/
def affineφ : Kˣ →* MulAut (Multiplicative K) :=
  (MulAutMultiplicative K).symm.toMonoidHom.comp (AddAut.mulLeft (R := K))

omit [Fintype K] in
@[simp] lemma affineφ_apply (a : Kˣ) (b : K) :
    Multiplicative.toAdd ((affineφ K a) (Multiplicative.ofAdd b)) = (a : K) * b := rfl

/-- The affine group `x ↦ a x + b` over `K`, realized as the semidirect product of the abelian
translation group `Multiplicative K` by the multiplicative group `Kˣ` acting by multiplication. -/
abbrev AffineGroup : Type := Multiplicative K ⋊[affineφ K] Kˣ

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.6.** The complete classification of the irreducible complex
representations of the affine group `x ↦ a x + b` over a finite field `K` (`q = |K|` elements),
obtained from Theorem 5.27.1: there are exactly `q` pairwise non-isomorphic irreducibles forming a
complete set, of which `q - 1` have dimension `1` (the characters factoring through `Kˣ`) and one
has dimension `q - 1` (over the free orbit of nontrivial characters). -/
theorem affine_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  sorry

end Etingof.Exercise5_27_2
