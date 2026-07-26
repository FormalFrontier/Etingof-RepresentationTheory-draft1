import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_7_1
import EtingofRepresentationTheory.Chapter5.Lemma5_7_2

/-!
# From a virtual representation to a representative family, and back

`Etingof.Lemma5_7_2` is stated for a *family* of pairwise non-isomorphic irreducibles
`W : ι → FDRep ℂ G` with integer coefficients `n : ι → ℤ`. That is the reusable form: it
makes no assumption about where the family comes from. This file connects it to
`Etingof.VirtualRepresentation` (Definition 5.7.1), whose coefficients live on isomorphism
classes.

The link is `Etingof.IrrepClasses.repOf`, a chosen simple representative of each class. Its
key property is that distinct classes have non-isomorphic representatives
(`Etingof.IrrepClasses.nonempty_repOf_iso_repOf_iff`), which is exactly the pairwise
distinctness hypothesis of Lemma 5.7.2.

## Main statements

* `Etingof.VirtualRepresentation.character_eq_sum_repOf`,
  `Etingof.VirtualRepresentation.dim_eq_sum_repOf` — the virtual character and dimension,
  written as sums over the representative family, in the shape Lemma 5.7.2 expects.
* `Etingof.VirtualRepresentation.eq_ofSingle_of_norm_one` — the conclusion of Lemma 5.7.2 in
  terms of Definition 5.7.1: a virtual representation of self inner product `1` and positive
  dimension *is* the class of a single irreducible, `V = ofSingle W hW 1`. This is the
  statement the book actually makes ("then `V` is an irreducible representation"), and it is
  only expressible because coefficients are indexed by isomorphism classes: on literal-object
  coefficient data there is no such `V`, since `+1` on one model and `-1` on an isomorphic
  copy would also satisfy the hypotheses.
-/

open CategoryTheory

namespace Etingof.VirtualRepresentation

variable {G : Type} [Group G] [Fintype G]

/-! ### The representative family of a virtual representation

The family is indexed by the support of `V`, with `i`-th member the chosen representative
`repOf i` and `i`-th coefficient `V i`. -/

/-- The chosen representatives of the classes in the support of `V` are pairwise
non-isomorphic. This is the pairwise distinctness hypothesis of `Etingof.Lemma5_7_2`. -/
theorem repOf_support_distinct (V : VirtualRepresentation G) :
    ∀ i j : (V.support : Finset (IrrepClasses ℂ G)),
      Nonempty (IrrepClasses.repOf (i : IrrepClasses ℂ G) ≅
        IrrepClasses.repOf (j : IrrepClasses ℂ G)) → i = j :=
  fun _ _ h => Subtype.ext (IrrepClasses.nonempty_repOf_iso_repOf_iff _ _ |>.mp h)

/-- The virtual character as a sum over the representative family. -/
theorem character_eq_sum_repOf (V : VirtualRepresentation G) (g : G) :
    character V g =
      ∑ i : (V.support : Finset (IrrepClasses ℂ G)),
        ((V (i : IrrepClasses ℂ G) : ℂ)) *
          (IrrepClasses.repOf (i : IrrepClasses ℂ G)).character g := by
  rw [character_apply, ← Finset.sum_coe_sort V.support]
  exact Finset.sum_congr rfl fun i _ => by rw [IrrepClasses.character_repOf]

/-- The virtual dimension as a sum over the representative family. -/
theorem dim_eq_sum_repOf (V : VirtualRepresentation G) :
    V.dim =
      ∑ i : (V.support : Finset (IrrepClasses ℂ G)),
        V (i : IrrepClasses ℂ G) *
          (Module.finrank ℂ (IrrepClasses.repOf (i : IrrepClasses ℂ G)) : ℤ) := by
  rw [dim_eq_sum, ← Finset.sum_coe_sort V.support]
  exact Finset.sum_congr rfl fun i _ => by rw [IrrepClasses.finrank_repOf]

/-! ### Lemma 5.7.2 for virtual representations -/

/-- **Lemma 5.7.2, in the form the book states it.** If a virtual representation `V` has
`(χ_V, χ_V) = 1` and `χ_V(1) > 0`, then `V` is the class of a single irreducible
representation: `V = ofSingle W hW 1` for some simple `W`, and hence `χ_V = χ_W`.

The inner product is the pairing used elsewhere in this project,
`(χ, ψ) = ⅟|G| · Σ_g χ(g) ψ(g⁻¹)`.

This is a consequence of the general family version `Etingof.Lemma5_7_2`, applied to the
representative family of `V`. (Etingof Lemma 5.7.2) -/
theorem eq_ofSingle_of_norm_one [Invertible (Fintype.card G : ℂ)]
    (V : VirtualRepresentation G)
    (hnorm : ⅟(Fintype.card G : ℂ) • ∑ g : G, character V g * character V g⁻¹ = 1)
    (hpos : 0 < V.dim) :
    ∃ (W : FDRep ℂ G) (hW : Simple W), V = ofSingle W hW 1 := by
  classical
  set ι := (V.support : Finset (IrrepClasses ℂ G)) with hι
  set W : ι → FDRep ℂ G := fun i => IrrepClasses.repOf (i : IrrepClasses ℂ G) with hW
  set n : ι → ℤ := fun i => V (i : IrrepClasses ℂ G) with hn
  -- Rewrite the two hypotheses in the shape `Etingof.Lemma5_7_2` expects.
  have hnorm' : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
               (∑ j, (n j : ℂ) * (W j).character g⁻¹) = 1 := by
    refine Eq.trans (congrArg _ (Finset.sum_congr rfl fun g _ => ?_)) hnorm
    rw [← character_eq_sum_repOf V g, ← character_eq_sum_repOf V g⁻¹]
  have hpos' : 0 < ∑ i, n i * (Module.finrank ℂ (W i) : ℤ) := by
    rw [← dim_eq_sum_repOf V]; exact hpos
  obtain ⟨i₀, hi₀, hrest⟩ :=
    Etingof.Lemma5_7_2 (G := G) (ι := ι) W (repOf_support_distinct V) n hnorm' hpos'
  -- The single surviving coefficient identifies `V` with a basis element.
  refine ⟨IrrepClasses.repOf (i₀ : IrrepClasses ℂ G), IrrepClasses.instSimpleRepOf _, ?_⟩
  rw [ofSingle, IrrepClasses.mk_repOf]
  ext c
  by_cases hc : c = (i₀ : IrrepClasses ℂ G)
  · subst hc; simpa using hi₀
  · rw [show (Finsupp.single (i₀ : IrrepClasses ℂ G) (1 : ℤ)) c = 0 from by
      simp [Ne.symm hc]]
    by_cases hmem : c ∈ V.support
    · exact hrest ⟨c, hmem⟩ (fun h => hc (congrArg Subtype.val h))
    · exact Finsupp.notMem_support_iff.mp hmem

/-- The character of a virtual representation satisfying the hypotheses of
`eq_ofSingle_of_norm_one` is the character of a genuine irreducible representation. -/
theorem exists_simple_character_eq [Invertible (Fintype.card G : ℂ)]
    (V : VirtualRepresentation G)
    (hnorm : ⅟(Fintype.card G : ℂ) • ∑ g : G, character V g * character V g⁻¹ = 1)
    (hpos : 0 < V.dim) :
    ∃ (W : FDRep ℂ G) (_ : Simple W), character V = W.character := by
  obtain ⟨W, hW, hV⟩ := eq_ofSingle_of_norm_one V hnorm hpos
  exact ⟨W, hW, by rw [hV, character_ofSingle_one]⟩

end Etingof.VirtualRepresentation
