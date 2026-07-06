import Mathlib
import EtingofRepresentationTheory.Chapter6.Problem6_1_3_continued_tildeE

/-!
# Problem 6.1.6: The McKay graph of a finite subgroup of `SU(2)`

> Let `G ≠ {1}` be a finite subgroup of `SU(2)` and let `V` be the
> `2`-dimensional representation of `G` coming from its embedding into `SU(2)`.
> Let `Vᵢ`, `i ∈ I`, be all the irreducible representations of `G`. Let `rᵢⱼ` be
> the multiplicity of `Vᵢ` in `V ⊗ Vⱼ`.
>
> **(a)** Show that `rᵢⱼ = rⱼᵢ`.
>
> **(b)** The **McKay graph** `M(G)` has vertices `i ∈ I`, with `i` joined to `j`
> by `rᵢⱼ` edges. Show that `M(G)` is connected. (Use Problem 4.12.10.)
>
> **(c)** Show that `M(G)` is an **affine Dynkin diagram**: the matrix
> `aᵢⱼ = 2δᵢⱼ - rᵢⱼ` is positive semidefinite but not definite. (Use 6.1.3.)
>
> **(d)** Which groups from Problem 4.12.8 correspond to which diagrams?
>
> **(e)** Using the McKay graph, the dimensions of the irreducible
> representations are the numbers labeling the vertices of the affine Dynkin
> diagrams (the marks).

## Formalization notes

`SU(2)` is `Matrix.specialUnitaryGroup (Fin 2) ℂ`. The `2`-dimensional
representation `V` is the tautological action of `G ≤ SU(2)` on `ℂ² = Fin 2 → ℂ`
by matrix multiplication. The irreducibles are given as a finite family
`W : Fin m → FDRep ℂ G` (all simple, pairwise non-isomorphic, exhaustive). The
multiplicity `rᵢⱼ = dim Hom(Wᵢ, V ⊗ Wⱼ)` (Schur's lemma), and the affine Cartan
matrix reuses `Etingof.Problem6_1_3_tildeE.IsAffineDynkinDiagram`.
-/

namespace Etingof.Problem6_1_6

open Matrix CategoryTheory MonoidalCategory Module

/-- The tautological `2`-dimensional representation of `G ≤ SU(2)` on `ℂ²`:
`g` acts by matrix multiplication `v ↦ (g : Matrix).mulVec v`. -/
noncomputable def tautRep (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) :
    Representation ℂ G (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    simp only [OneMemClass.coe_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul, Matrix.toLin'_mul]; rfl

/-- The `2`-dimensional representation `V` of `G` as an `FDRep`. -/
noncomputable def V (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) : FDRep ℂ G :=
  FDRep.of (tautRep G)

variable {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
  {m : ℕ} (W : Fin m → FDRep ℂ G)

/-- `W` is a **complete list of irreducibles**: each `W i` is simple, the `W i`
are pairwise non-isomorphic, and every simple `FDRep` is isomorphic to some
`W i`. -/
structure IsCompleteIrreps : Prop where
  simple : ∀ i, Simple (W i)
  distinct : ∀ i j, Nonempty (W i ≅ W j) → i = j
  exhaustive : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ W i)

/-- The multiplicity `rᵢⱼ` of `Wᵢ` in `V ⊗ Wⱼ`, computed as
`dim Hom(Wᵢ, V ⊗ Wⱼ)` (Schur's lemma). -/
noncomputable def mult (i j : Fin m) : ℕ := finrank ℂ (W i ⟶ V G ⊗ W j)

/-- The McKay adjacency matrix `rᵢⱼ` (as an integer matrix). -/
noncomputable def mckayAdj (i j : Fin m) : ℤ := (mult W i j : ℤ)

/-- The affine Cartan matrix `aᵢⱼ = 2δᵢⱼ - rᵢⱼ` of the McKay graph. -/
noncomputable def mckayCartan (i j : Fin m) : ℤ :=
  2 * (if i = j then 1 else 0) - mult W i j

/-! ## Part (a): symmetry of the multiplicities -/

/-- **(a)** `rᵢⱼ = rⱼᵢ`. (Because `V` is self-dual: `V ≅ V*` as `V` is the
`2`-dimensional `SU(2)`-representation, so `dim Hom(Wᵢ, V ⊗ Wⱼ) =
dim Hom(Wⱼ, V ⊗ Wᵢ)`.) -/
theorem mult_symm (hW : IsCompleteIrreps W) (i j : Fin m) :
    mult W i j = mult W j i := by
  sorry

/-! ## Part (b): the McKay graph is connected -/

/-- **(b)** The McKay graph is **connected**: any two vertices are joined by a
path of edges (`rᵢⱼ ≥ 1` steps). -/
theorem mckay_connected (hW : IsCompleteIrreps W) (i j : Fin m) :
    ∃ path : List (Fin m), path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        1 ≤ mult W (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) := by
  sorry

/-! ## Part (c): the McKay graph is an affine Dynkin diagram -/

/-- **(c)** The McKay adjacency matrix is symmetric with `0/1` entries and no
self-loops, and its Cartan matrix `2δ - r` is positive semidefinite but not
definite — i.e. the McKay graph is an **affine Dynkin diagram**. -/
theorem mckay_isAffineDynkin (hW : IsCompleteIrreps W) (hm : 1 ≤ m)
    (hne : Nontrivial G) :
    Problem6_1_3_tildeE.IsAffineDynkinDiagram m (mckayAdj W) := by
  sorry

/-! ## Part (c): positive semidefinite but not definite (explicit form) -/

/-- **(c)** The McKay Cartan form is positive **semidefinite**. -/
theorem mckayCartan_posSemidef (hW : IsCompleteIrreps W) (hne : Nontrivial G)
    (x : Fin m → ℤ) :
    0 ≤ dotProduct x ((Matrix.of (mckayCartan W)).mulVec x) := by
  sorry

/-- **(c)** The McKay Cartan form is **not** positive definite: the vector of
irreducible dimensions is a nonzero null vector. -/
theorem mckayCartan_not_posDef (hW : IsCompleteIrreps W) (hne : Nontrivial G) :
    ∃ x : Fin m → ℤ, x ≠ 0 ∧
      dotProduct x ((Matrix.of (mckayCartan W)).mulVec x) = 0 := by
  sorry

/-! ## Part (e): irreducible dimensions are the marks -/

/-- **(e)** The dimensions of the irreducibles are the vertex labels (marks) of
the affine Dynkin diagram: the vector `dᵢ = dim Wᵢ` spans the kernel of the
McKay Cartan matrix, `∑ⱼ (2δᵢⱼ - rᵢⱼ) dⱼ = 0` for every `i`. -/
theorem mckay_dims_are_marks (hW : IsCompleteIrreps W) (i : Fin m) :
    (∑ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)) = 0 := by
  sorry

/-- **(d)** The finite subgroups of `SU(2)` (equivalently, of `SO(3)` up to the
central `±Id`, from Problem 4.12.8) correspond bijectively to the affine ADE
diagrams under the McKay correspondence: cyclic ↔ `Ãₙ`, binary dihedral ↔ `D̃ₙ`,
binary tetrahedral/octahedral/icosahedral ↔ `Ẽ₆ / Ẽ₇ / Ẽ₈`.

Recorded as a `Prop` against the real affine-type enumeration; the group
classification of Problem 4.12.8 is a separate item, so this pins the
correspondence for a later proof pass rather than asserting a vacuous theorem. -/
def McKayCorrespondence (hW : IsCompleteIrreps W) : Prop :=
  ∃ t : Problem6_1_3_tildeE.AffineType, ∃ σ : Fin t.rank ≃ Fin m,
    ∀ i j, mckayAdj W (σ i) (σ j) = t.adj i j

end Etingof.Problem6_1_6
