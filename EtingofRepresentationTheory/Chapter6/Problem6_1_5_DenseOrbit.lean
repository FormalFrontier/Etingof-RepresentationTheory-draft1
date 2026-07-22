import Mathlib

/-!
# Problem 6.1.5, Step 2(a): finitely many orbits ⟹ a Zariski-dense orbit

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It closes **step 2(a)** of Etingof Problem 6.1.2:

> If an algebraic group `G` acts on an irreducible space `V` with only finitely
> many orbits, then `G` has a Zariski-dense orbit on `V`.

## The argument (orientation-independent, no local-closedness)

The book's argument is purely topological once "Zariski-dense" is read as
"dense in the Zariski topology" (closure is everything):

* `V` is irreducible (for `W(m)` this is affine-space irreducibility — the
  polynomial ring is a domain; supplied to these lemmas as the hypothesis
  `IsIrreducible (Set.univ : Set V)`).
* The orbits cover `V`, hence so do their closures: `V = ⋃ closure(orbit)`.
  Finitely many orbits makes this a **finite** union of **closed** sets.
* An irreducible space that is a finite union of closed sets equals one of them
  (`isIrreducible_iff_sUnion_isClosed`). So some orbit closure is all of `V`,
  i.e. that orbit is dense.

This avoids the algebraic-groups fact that orbits are locally closed: we never
need the orbits themselves to be open or constructible, only that there are
finitely many and that `V` is irreducible.

## What this file provides

* `exists_dense_of_iUnion_closure`: the pure-topology core — an irreducible space
  covered by finitely many closures has a dense member.
* `exists_dense_orbit` / `exists_dense_orbit_point`: the specialisation to a
  `MulAction G V` with finitely many orbits, phrased on the orbit quotient and on
  a point respectively. These are stated abstractly (any `TopologicalSpace`,
  `MulAction`) so they apply to `W(m)` with the `G(m)`-action of S0 once that is
  in place, but prove without S0.
-/

namespace Etingof.Problem6_1_5

open MulAction Set

variable {V : Type*} [TopologicalSpace V]

/-- **Pure-topology core of step 2(a).** If an irreducible space `V` is covered by
the closures of a finite family of sets `A i`, then one of the `A i` is dense.

This is the orientation-independent heart of the orbit argument: irreducibility of
`V` plus finitely many closed pieces forces one piece to be everything. -/
theorem exists_dense_of_iUnion_closure {ι : Type*}
    (hV : IsIrreducible (Set.univ : Set V)) {s : Set ι} (hs : s.Finite) (A : ι → Set V)
    (hcover : (Set.univ : Set V) ⊆ ⋃ i ∈ s, closure (A i)) :
    ∃ i ∈ s, Dense (A i) := by
  classical
  obtain ⟨z, hz_mem, hz_sub⟩ :=
    (isIrreducible_iff_sUnion_isClosed.mp hV) (hs.toFinset.image fun i => closure (A i))
      (by
        intro z hz
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact isClosed_closure)
      (by
        refine hcover.trans ?_
        simp [Finset.coe_image, Set.sUnion_image, hs.coe_toFinset])
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz_mem
  exact ⟨i, hs.mem_toFinset.mp hi,
    dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset hz_sub)⟩

variable {G : Type*} [Group G] [MulAction G V]

/-- **Step 2(a), quotient form.** A group acting on an irreducible space with
finitely many orbits has a dense orbit. The dense orbit is exhibited as an element
of the orbit quotient. -/
theorem exists_dense_orbit (hV : IsIrreducible (Set.univ : Set V))
    [Finite (orbitRel.Quotient G V)] :
    ∃ x : orbitRel.Quotient G V, Dense x.orbit := by
  have hcover : (Set.univ : Set V) ⊆
      ⋃ x ∈ (Set.univ : Set (orbitRel.Quotient G V)), closure x.orbit := by
    intro a _
    refine Set.mem_biUnion (Set.mem_univ (Quotient.mk'' a)) (subset_closure ?_)
    rw [orbitRel.Quotient.orbit_mk]
    exact mem_orbit_self a
  obtain ⟨x, -, hx⟩ :=
    exists_dense_of_iUnion_closure hV Set.finite_univ
      (fun x : orbitRel.Quotient G V => x.orbit) hcover
  exact ⟨x, hx⟩

/-- **Step 2(a), point form.** A group acting on an irreducible space with finitely
many orbits has a point whose orbit is dense. This is the form consumed by step
2(b) (#4783): the dense orbit of a point `x` gives the dominant orbit map
`G → W`, `g ↦ g • x`. -/
theorem exists_dense_orbit_point (hV : IsIrreducible (Set.univ : Set V))
    [Finite (orbitRel.Quotient G V)] :
    ∃ x : V, Dense (MulAction.orbit G x) := by
  obtain ⟨q, hq⟩ := exists_dense_orbit (G := G) hV
  refine ⟨q.out, ?_⟩
  rwa [orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq'] at hq

end Etingof.Problem6_1_5
