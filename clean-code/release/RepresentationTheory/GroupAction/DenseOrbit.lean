/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib

/-!
# Dense orbits under group actions
-/

namespace RepresentationTheory.GroupAction.DenseOrbit

open MulAction Set

variable {V : Type*} [TopologicalSpace V]

namespace IsIrreducible

/-- For a finite collection of subsets covering an irreducible space after taking closures, at least one of the original subsets is dense. -/
theorem exists_mem_dense_of_finite_closure_cover {ι : Type*}
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

end IsIrreducible

variable {G : Type*} [Group G] [MulAction G V]

namespace MulAction.orbitRel.Quotient

/-- When an irreducible topological space has finitely many orbit classes under a group action, some class, viewed through the orbit-relation quotient, is dense. -/
theorem exists_dense_orbit_of_finite (hV : IsIrreducible (Set.univ : Set V))
    [Finite (orbitRel.Quotient G V)] :
    ∃ x : orbitRel.Quotient G V, Dense x.orbit := by
  have hcover : (Set.univ : Set V) ⊆
      ⋃ x ∈ (Set.univ : Set (orbitRel.Quotient G V)), closure x.orbit := by
    intro a _
    refine Set.mem_biUnion (Set.mem_univ (Quotient.mk'' a)) (subset_closure ?_)
    rw [orbitRel.Quotient.orbit_mk]
    exact mem_orbit_self a
  obtain ⟨x, -, hx⟩ :=
    IsIrreducible.exists_mem_dense_of_finite_closure_cover hV Set.finite_univ
      (fun x : orbitRel.Quotient G V => x.orbit) hcover
  exact ⟨x, hx⟩

end MulAction.orbitRel.Quotient

namespace MulAction

/-- A group action with finitely many orbit classes on an irreducible topological space admits a point with dense orbit. -/
theorem exists_dense_orbit_of_finite_orbitRel_quotient (hV : IsIrreducible (Set.univ : Set V))
    [Finite (orbitRel.Quotient G V)] :
    ∃ x : V, Dense (MulAction.orbit G x) := by
  obtain ⟨q, hq⟩ := orbitRel.Quotient.exists_dense_orbit_of_finite (G := G) hV
  refine ⟨q.out, ?_⟩
  rwa [orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq'] at hq

end MulAction

end RepresentationTheory.GroupAction.DenseOrbit
