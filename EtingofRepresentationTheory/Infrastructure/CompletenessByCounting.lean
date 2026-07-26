import EtingofRepresentationTheory.Chapter4.Corollary4_2_2

/-!
# Completeness by counting

Etingof repeatedly closes a classification with the same one-line argument: "we have found
`N` pairwise non-isomorphic irreducible representations, and `N` is the number of conjugacy
classes, hence we have found *all* of them."

Equal cardinalities alone do not prove completeness — one needs the injection of the
constructed family into the set of isomorphism classes, and then a pigeonhole. This file
supplies that step once and for all.

## Main results

* `Etingof.exhaustive_of_complete_family` — the pigeonhole core. If `V : Fin n → FDRep k G`
  is a complete list of simples (every simple is isomorphic to some `V i`) and
  `W : Fin N → FDRep k G` is a list of pairwise non-isomorphic simples with `N = n`, then
  `W` is complete too.
* `Etingof.exhaustive_of_card_eq_card_conjClasses` — the form used in practice: over an
  algebraically closed field `k` with `char k ∤ |G|`, any family of `Nat.card (ConjClasses G)`
  pairwise non-isomorphic simple `FDRep k G` objects exhausts the irreducibles. The complete
  list it is compared against comes from `Etingof.Corollary4_2_2`.

The point of the second statement is that its hypotheses are exactly the work a
classification does: construct the family, prove each member simple, prove no two members
are isomorphic, count. Nothing else is needed for "these are all of them".
-/

open CategoryTheory

universe u v

namespace Etingof

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

omit [IsAlgClosed k] [Fintype G] in
/-- **Pigeonhole for irreducibles.** If `V : Fin n → FDRep k G` is a *complete* family of
simple objects (every simple is isomorphic to some `V i`) and `W : Fin N → FDRep k G` is a
family of *pairwise non-isomorphic* simple objects with `N = n`, then `W` is complete as
well: every simple `FDRep k G` is isomorphic to some `W i`.

Sending `i` to the index `f i` with `W i ≅ V (f i)` is injective because the `W i` are
pairwise non-isomorphic, hence bijective since `N = n`; so every `V j`, and therefore every
simple, is hit. -/
theorem exhaustive_of_complete_family {n N : ℕ}
    (V : Fin n → FDRep k G)
    (hVcomplete : ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ V i))
    (W : Fin N → FDRep k G) (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hcard : N = n) :
    ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  subst hcard
  -- Each `W i` is simple, so it is isomorphic to `V (f i)` for some index `f i`.
  choose f hf using fun i => hVcomplete (W i) (hWsimple i)
  have hfinj : Function.Injective f := by
    intro i j hij
    exact hWnoniso i j ⟨(hf i).some ≪≫ eqToIso (congrArg V hij) ≪≫ (hf j).some.symm⟩
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  intro U hU
  obtain ⟨j, hj⟩ := hVcomplete U hU
  obtain ⟨i, rfl⟩ := hfbij.2 j
  exact ⟨i, ⟨hj.some ≪≫ (hf i).some.symm⟩⟩

/-- **Completeness by counting conjugacy classes.** Over an algebraically closed field `k`
whose characteristic does not divide `|G|`, a family of `Nat.card (ConjClasses G)` pairwise
non-isomorphic simple `FDRep k G` objects contains every irreducible representation up to
isomorphism.

This is Etingof's standard closing move, and it is the missing half of a
"the counts agree, so we have found them all" argument: the count is compared against the
complete list of simples produced by `Etingof.Corollary4_2_2`, and the pigeonhole
`Etingof.exhaustive_of_complete_family` turns the numerical coincidence into an actual
exhaustiveness statement. -/
theorem exhaustive_of_card_eq_card_conjClasses
    [Invertible (Fintype.card G : k)] {N : ℕ}
    (W : Fin N → FDRep k G) (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hN : N = Nat.card (ConjClasses G)) :
    ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  classical
  obtain ⟨n, V, -, -, hVcomplete, hn⟩ := Etingof.Corollary4_2_2 (k := k) (G := G)
  exact exhaustive_of_complete_family V hVcomplete W hWsimple hWnoniso
    (by rw [hN, hn, Nat.card_eq_fintype_card])

end Etingof
