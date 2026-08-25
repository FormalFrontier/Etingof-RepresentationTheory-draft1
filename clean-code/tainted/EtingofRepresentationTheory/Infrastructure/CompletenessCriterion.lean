import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Completeness criterion by dimension count

Over an algebraically closed field `k` with `char k ∤ |G|`, a finite family of pairwise
non-isomorphic simple representations of a finite group `G` whose squared dimensions already
sum to `|G|` is automatically *complete*: every simple `FDRep k G` is isomorphic to one of
them. This is the converse companion to `IrrepDecomp.sum_finrank_sq_eq_card`
(`Etingof.Theorem4_1_1`): reaching the Artin-Wedderburn total `Σ (dim)² = |G|` leaves no room
for a further irreducible.

The proof compares the family with the Wedderburn-Artin enumeration `IrrepDecomp`: each member
of the family is a column representation `columnFDRep (τ j)`, the assignment `τ` is injective
(the family is pairwise non-isomorphic), and matching the total `Σ (dim)² = |G|` forces `τ` to
be surjective (all Wedderburn block dimensions are positive), hence a bijection, so no column
representation - and therefore no simple - is missed.
-/

open CategoryTheory

universe u v

/-- **Completeness criterion by dimension count.** A finite family `W : ι → FDRep k G` of
pairwise non-isomorphic simple representations whose squared dimensions sum to `|G|` is
complete: every simple `FDRep k G` is isomorphic to some `W j`. -/
theorem FDRep.complete_of_sum_finrank_sq_eq_card
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)]
    {ι : Type v} [Fintype ι] (W : ι → FDRep k G)
    (hW : ∀ j, Simple (W j))
    (hinj : ∀ j j', Nonempty (W j ≅ W j') → j = j')
    (hsum : ∑ j, (Module.finrank k (W j)) ^ 2 = Fintype.card G)
    (X : FDRep k G) (hX : Simple X) :
    ∃ j, Nonempty (X ≅ W j) := by
  classical
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  -- Each `W j` is a column representation `columnFDRep (τ j)`.
  choose τ hτ using fun j => D.columnFDRep_surjective (W j) (hW j)
  -- `τ` is injective because the `W j` are pairwise non-isomorphic.
  have hτ_inj : Function.Injective τ := by
    intro j j' h
    exact hinj j j' ⟨(hτ j).some ≪≫ (h ▸ (hτ j').some.symm)⟩
  -- Dimensions match the Wedderburn block sizes.
  have hfr : ∀ j, (Module.finrank k (W j)) ^ 2 = (D.d (τ j)) ^ 2 := by
    intro j
    rw [← D.finrank_columnFDRep (τ j),
      LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ j).some)]
  -- The squared dimensions summed over the image of `τ` already reach `|G|`.
  have hsum' : ∑ i ∈ Finset.univ.image τ, (D.d i) ^ 2 = ∑ i : Fin D.n, (D.d i) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ h => hτ_inj h)]
    rw [← D.sum_sq_eq_card] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl (fun j _ => (hfr j).symm)
  -- Every Wedderburn index is hit: otherwise its positive term would make the image sum smaller.
  have hτ_surj : Function.Surjective τ := by
    intro i
    by_contra hi
    have hi₀ : i ∉ Finset.univ.image τ := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun j => fun h => hi ⟨j, h⟩
    have hpos : 0 < (D.d i) ^ 2 := by
      have := (D.d_pos i).out; positivity
    have hlt : ∑ i ∈ Finset.univ.image τ, (D.d i) ^ 2 < ∑ i : Fin D.n, (D.d i) ^ 2 :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i) hi₀ hpos
        (fun k _ _ => Nat.zero_le _)
    exact absurd hsum' (ne_of_lt hlt)
  -- `X` is some column representation, which is hit by `τ`, hence isomorphic to a family member.
  obtain ⟨i₀, hi₀⟩ := D.columnFDRep_surjective X hX
  obtain ⟨j, hj⟩ := hτ_surj i₀
  subst hj
  exact ⟨j, ⟨hi₀.some ≪≫ (hτ j).some.symm⟩⟩
