import Mathlib

/-!
# Problem 4.12.5: decomposition of the icosahedral representations of `A₅`

**Problem 4.12.5.** Let `I` be the set of vertices of a regular icosahedron (`|I| = 12`). Let
`F(I)` be the space of complex functions on `I`. The group `G = A₅` of even permutations of
five items acts on the icosahedron, so we get a `12`-dimensional representation of `G` on
`F(I)`.

(a) Decompose this representation into irreducibles (find the multiplicities of all
irreducibles).

(b) Do the same for the representation of `G` on functions on the set of faces (`20`) and the
set of edges (`30`).

## Formalization

`A₅` is `alternatingGroup (Fin 5)`. Its irreducible complex representations have dimensions
`1, 3, 3', 4, 5` (the two `3`-dimensional ones are non-isomorphic). The icosahedral actions are
characterized purely group-theoretically: a transitive action of `A₅` on a `12`/`20`/`30`
element set with point stabilizer of order `5`/`3`/`2` is unique up to isomorphism (all Sylow
`5`-, `3`-subgroups and all involutions of `A₅` are conjugate), and reproduces the vertex /
face / edge action of the icosahedron. We therefore take the action as a hypothesis `act`
together with these transitivity and stabilizer-order conditions.

Given `act : G →* Equiv.Perm (Fin n)`, `permRep act` is the permutation representation on
`Fin n → ℂ`, `(permRep act g f) i = f (act g⁻¹ i)`. Writing `χ(g)` for the number of fixed
points of `act g`, the character inner products give the multiplicities:

* **(a) vertices (`12`):** `χ = (12, 0, 0, 2, 2)` on the classes `(1a, 2a, 3a, 5a, 5b)`, so
  `F(I) ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (dimensions `1 + 3 + 3 + 5 = 12`).
* **(b) faces (`20`):** `χ = (20, 0, 2, 0, 0)`, so `≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5`
  (`1 + 3 + 3 + 4 + 4 + 5 = 20`).
* **(b) edges (`30`):** `χ = (30, 2, 0, 0, 0)`, so `≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³`
  (`1 + 3 + 3 + 4 + 4 + 5 + 5 + 5 = 30`).

Each decomposition is stated as the existence of an internal direct sum of `G`-invariant
irreducible subspaces of the listed dimensions, in which the two `3`-dimensional summands are
non-isomorphic (their subrepresentation characters differ). Statement pass: `sorry` proofs.
-/

noncomputable section

namespace Etingof.Problem4_12_5

/-- The alternating group `A₅` of even permutations of five items. -/
abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

/-- The permutation representation attached to an action `act : G →* Equiv.Perm (Fin n)`, on
the space `Fin n → ℂ` of complex functions on the `n`-element set:
`(permRep act g f) i = f (act g⁻¹ i)`. -/
def permRep {G : Type*} [Group G] {n : ℕ} (act : G →* Equiv.Perm (Fin n)) :
    Representation ℂ G (Fin n → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (act g⁻¹)
  map_one' := by
    ext f i
    simp
  map_mul' g h := by
    ext f i
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_inv_rev, map_mul]

/-- The character of the subrepresentation of `ρ` carried by a `G`-invariant submodule `S`:
the trace of `ρ g` restricted to `S`. -/
def subChar {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) : ℂ :=
  LinearMap.trace ℂ S ((ρ g).restrict (hS g))

/-- `IsIrredSub ρ S` says the `G`-invariant submodule `S` carries an irreducible
subrepresentation: it is nonzero and has no `G`-invariant submodule strictly between `⊥` and
`S`. -/
def IsIrredSub {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  S ≠ ⊥ ∧ ∀ T : Submodule ℂ (Fin n → ℂ),
    T ≤ S → (∀ g, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S

/-- **Part (a): vertices.** For the icosahedral vertex action of `A₅` — any transitive action
on `12` points with point stabilizers of order `5` — the representation on `F(I) = Fin 12 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 5`: an internal direct sum of four `G`-invariant irreducible
subspaces of dimensions `1, 3, 3, 5`, with the two `3`-dimensional summands non-isomorphic. -/
theorem vertices_decomposition
    (act : A5 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : A5 // act g i = i} = 5) :
    ∃ (S : Fin 4 → Submodule ℂ (Fin 12 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

/-- **Part (b): faces.** For the icosahedral face action of `A₅` — any transitive action on
`20` points with point stabilizers of order `3` — the representation on `Fin 20 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5`: an internal direct sum of six `G`-invariant irreducible
subspaces of dimensions `1, 3, 3, 4, 4, 5`, with the two `3`-dimensional summands
non-isomorphic. -/
theorem faces_decomposition
    (act : A5 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : A5 // act g i = i} = 3) :
    ∃ (S : Fin 6 → Submodule ℂ (Fin 20 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

/-- **Part (b): edges.** For the icosahedral edge action of `A₅` — any transitive action on
`30` points with point stabilizers of order `2` — the representation on `Fin 30 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³`: an internal direct sum of eight `G`-invariant
irreducible subspaces of dimensions `1, 3, 3, 4, 4, 5, 5, 5`, with the two `3`-dimensional
summands non-isomorphic. -/
theorem edges_decomposition
    (act : A5 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : A5 // act g i = i} = 2) :
    ∃ (S : Fin 8 → Submodule ℂ (Fin 30 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      Module.finrank ℂ (S 6) = 5 ∧ Module.finrank ℂ (S 7) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

end Etingof.Problem4_12_5
