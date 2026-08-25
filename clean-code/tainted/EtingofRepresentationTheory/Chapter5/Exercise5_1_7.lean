import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.Exercise5_3_3
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Exercise 5.1.7: an odd-order group has an irreducible not defined over ℝ

**Exercise 5.1.7.** Show that any nontrivial finite group of odd order has an irreducible
representation which is not defined over `ℝ` (i.e., not realizable by real matrices).

## Formalization

A representation "defined over `ℝ`" (realizable by real matrices) admits a `G`-invariant
positive-definite real inner product, hence a nondegenerate symmetric `G`-invariant bilinear
form, so it is of real type (`Etingof.IsRealType`, Definition 5.1.1). Therefore "not
defined over `ℝ`" is faithfully captured by `¬ Etingof.IsRealType ρ`.

The statement below asserts the existence of a nontrivial irreducible complex representation
`ρ` (`IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`, with `∃ g, ρ g ≠ 1`) that is not of
real type. Exercise 5.3.3 strengthens this to: every nontrivial irreducible is of complex
type.

## Proof

The odd-order hypothesis is used only by the reduction lemma
`not_isRealType_of_odd_order_of_nontrivial_irreducible` (Exercise 5.3.3), which turns any
nontrivial irreducible into one that is not of real type. So the entire content here is to
produce one nontrivial irreducible complex representation of the nontrivial finite group
`G`, then apply that lemma to it.

We use the Wedderburn-Artin enumeration `IrrepDecomp.mk'` of the irreducibles of `ℂ[G]` as
its column representations `D.columnRep i` (each simple by
`isSimpleModule_columnRep_asModule`). At least one of them has nontrivial `G`-action: if every
`D.columnRep i` acted trivially, then for a chosen `g₀ ≠ 1` each matrix factor
`D.projRingHom i (of g₀)` would be the identity (`Matrix.mulVecLin` is injective), forcing
`D.iso (of g₀) = 1 = D.iso (of 1)` and hence `g₀ = 1` (injectivity of the Wedderburn
isomorphism and of `MonoidAlgebra.of`), a contradiction.
-/

namespace Etingof

section Exercise517

variable (G : Type*) [Group G] [Fintype G] [Nontrivial G]

/-- Exercise 5.1.7. A nontrivial finite group of odd order admits a nontrivial irreducible
complex representation that is not of real type, i.e., not realizable by real matrices. -/
theorem exists_irreducible_not_realType_of_odd_order
    (hodd : Odd (Fintype.card G)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V)
      (ρ : Representation ℂ G V),
      IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule ∧
      (∃ g, ρ g ≠ 1) ∧
      ¬ Etingof.IsRealType ρ := by
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  -- The Wedderburn-Artin enumeration of the irreducibles of `ℂ[G]`.
  let D := IrrepDecomp.mk' (k := ℂ) (G := G)
  -- Some column representation has nontrivial `G`-action.
  obtain ⟨j, g₀, hj⟩ : ∃ (j : Fin D.n) (g : G), (D.columnRep j) g ≠ 1 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
    -- Each matrix factor of `of g₀` is the identity.
    have hmat : ∀ j : Fin D.n, D.projRingHom j (MonoidAlgebra.of ℂ G g₀) = 1 := by
      intro j
      have hdef : (D.columnRep j) g₀ =
          Matrix.mulVecLin (D.projRingHom j (MonoidAlgebra.of ℂ G g₀)) := rfl
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_one, ← hdef, h j g₀]
      rfl
    -- Hence `D.iso (of g₀) = 1`, so `of g₀ = of 1`, so `g₀ = 1`.
    have hprod : D.iso (MonoidAlgebra.of ℂ G g₀) = 1 := by
      funext i
      rw [Pi.one_apply]
      have := hmat i
      simpa [IrrepDecomp.projRingHom, Pi.evalRingHom] using this
    have hof : MonoidAlgebra.of ℂ G g₀ = 1 := by
      apply D.iso.injective
      rw [hprod, map_one]
    exact hg₀ (MonoidAlgebra.of_injective (hof.trans (map_one (MonoidAlgebra.of ℂ G)).symm))
  -- This column representation is a nontrivial irreducible; apply Exercise 5.3.3.
  haveI : NeZero (D.d j) := D.d_pos j
  refine ⟨Fin (D.d j) → ℂ, inferInstance, inferInstance, inferInstance, D.columnRep j,
    D.isSimpleModule_columnRep_asModule j, ⟨g₀, hj⟩, ?_⟩
  exact not_isRealType_of_odd_order_of_nontrivial_irreducible hodd (D.columnRep j)
    (D.isSimpleModule_columnRep_asModule j) ⟨g₀, hj⟩

end Exercise517

end Etingof
