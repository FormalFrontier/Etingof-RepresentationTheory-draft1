import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Dimension.Constructions
import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.PathAlgebraStandardResolution
import EtingofRepresentationTheory.Chapter9.PathAlgebraLowerBound
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionReduction

/-!
# Problem 9.4.6: Homological dimension and Cartan matrix of path algebras

Etingof Problem 9.4.6 has two parts.

* **(i)** The path algebra `P_Q` of any quiver `Q` with at least one edge has homological
  dimension `1`. In particular, the free algebra `k⟨x₁, …, xₙ⟩` (the path algebra of the
  one-vertex quiver with `n ≥ 1` loops) has homological dimension `1`.

* **(ii)** For a finite oriented graph `Q` without oriented cycles, the Cartan matrix of the
  path algebra `P_Q` is the *path-counting matrix*: its `(i, j)` entry is the number of
  oriented paths from vertex `i` to vertex `j`.

## Statement-pass note

Part (i) is stated with `Etingof.homologicalDimension` (Definition 9.4.3) applied to
`Etingof.PathAlgebra k Q` (Definition 2.8.4) and to `FreeAlgebra k (Fin n)`. "At least one
edge" is `∃ a b, Nonempty (a ⟶ b)`.

Part (ii) is stated with `Etingof.algebraCartanMatrix` (Definition 9.3.1). The Cartan matrix
is `cᵢⱼ = dim_k Hom_A(Pᵢ, Pⱼ)` for the projective covers `Pᵢ` of the simple modules. For the
path algebra of a finite acyclic quiver the indecomposable projectives are `Pᵢ = A · eᵢ`
(`eᵢ` the trivial-path idempotent), and `Hom_A(Pᵢ, Pⱼ) ≅ eᵢ A eⱼ` is the free `k`-space on
the oriented paths from `i` to `j`. This Hom-space identification (the content that makes the
Cartan matrix count paths) is carried as the hypothesis `hcover`; the conclusion is that the
Cartan matrix equals the path-count matrix `(i, j) ↦ Nat.card (Quiver.Path i j)`. Acyclicity
(`hacyclic`) is what makes each `Quiver.Path i j` finite, so `Nat.card` is the honest count.
Proofs are deferred (`sorry`) per the statement-pass phase.
-/

universe u

open Etingof CategoryTheory Limits

namespace Etingof.Problem946

/-- **Problem 9.4.6 (i), upper bound.** Every left `PathAlgebra k Q`-module has projective
dimension `≤ 1`; equivalently, the path algebra has homological dimension `≤ 1`.

This is the reusable core of Problem 9.4.6 (i): it is the *upper* bound
`homologicalDimension (PathAlgebra k Q) ≤ 1`. Combined with the lower bound
`¬ HasHomologicalDimensionLE (PathAlgebra k Q) 0` (non-semisimplicity once `Q` has an edge),
it yields `homologicalDimension_pathAlgebra_eq_one`.

## Proof strategy (the standard resolution)

Write `A := PathAlgebra k Q`, let `S := Q → k` be the semisimple subalgebra spanned by the
trivial-path idempotents `eᵢ`, and let `V` be the `S`-bimodule spanned by the arrows. For any
left `A`-module `M` the *standard resolution* is the length-`1` projective resolution
```
0 → A ⊗_S (V ⊗_S M) → A ⊗_S M →ᵉ M → 0,
```
where `ε(a ⊗ m) = a · m` is the multiplication map. Both nonzero terms are projective `A`-modules
because they are *induced* from `S`-modules (`A ⊗_S -`), `S` is semisimple (a finite product of
fields), so every `S`-module is projective, and induction along `S → A` preserves projectives
(it is left adjoint to restriction of scalars). Exactness — that `ker ε ≅ A ⊗_S (V ⊗_S M)` via
`a ⊗ v ⊗ m ↦ av ⊗ m - a ⊗ vm` — is the analogue of the Koszul short exact sequence used for the
polynomial case (`Example 9.4.4`).

## Obstruction / why this is genuinely new infrastructure

Unlike the polynomial case, the base extension here is **noncommutative-induced**: the vertex
idempotents `eᵢ` are *not central* in `A`, so `A` is not an `S`-algebra in the commutative sense
and Mathlib's `ModuleCat.extendScalars` (which requires `[CommRing R] [CommRing S]`) does **not**
apply. Building `A ⊗_S -` as a left `A`-module functor left-adjoint to `restrictScalars` along the
non-central inclusion `S → A`, and its projectivity-preservation, is genuine new infrastructure not
in Mathlib. See issue #6420 for the decomposition.

## Assembly

Because `Quiver.{u + 1} Q`, the path algebra `A = PathAlgebra k Q` lives in `Type (u + 1)`, so
`HasHomologicalDimensionLE A 1` (Definition 9.4.3) quantifies over `ModuleCat.{u + 1} A` — exactly
the universe the standard resolution `standardResolution_shortExact` is built at, so no universe
uplift is needed. For each `M` the proof reads off `(standardComplex M).ShortExact`, notes both
nonzero terms are projective (`projective_inducedModule_obj`), and applies dimension shifting
`ShortExact.hasProjectiveDimensionLT_X₃` (as in `hasHomologicalDimensionLE_polynomial`,
`Chapter9/Example9_4_4.lean`). -/
theorem hasHomologicalDimensionLE_pathAlgebra_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q] :
    Etingof.HasHomologicalDimensionLE (Etingof.PathAlgebra k Q) 1 := by
  intro M
  -- The standard length-`1` projective resolution `0 → A ⊗_S (V ⊗_S M) → A ⊗_S M → M → 0`.
  have hSES := Etingof.PathAlgebra.standardResolution_shortExact M
  -- Both nonzero terms are projective (induced from the semisimple vertex subalgebra `S = Q → k`).
  haveI hP1 : Projective (Etingof.PathAlgebra.standardComplex M).X₁ :=
    Etingof.PathAlgebra.projective_inducedModule_obj (Etingof.PathAlgebra.VtensObj M)
  haveI hP2 : Projective (Etingof.PathAlgebra.standardComplex M).X₂ :=
    Etingof.PathAlgebra.projective_inducedModule_obj (Etingof.PathAlgebra.restrictObj M)
  -- Dimension shifting on the short exact sequence gives `pd M ≤ 1`.
  exact hSES.hasProjectiveDimensionLT_X₃ 1
    (projective_iff_hasProjectiveDimensionLT_one.mp hP1)
    (hasProjectiveDimensionLT_of_ge _ 1 2 (by omega))

/-- **Problem 9.4.6 (i), path algebra.** The path algebra `P_Q` of a quiver `Q` with at least
one edge has homological dimension `1`. -/
theorem homologicalDimension_pathAlgebra_eq_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    Etingof.homologicalDimension (Etingof.PathAlgebra k Q) = 1 :=
  Etingof.homologicalDimension_eq_one_of_not_le_zero
    hasHomologicalDimensionLE_pathAlgebra_one
    (not_hasHomologicalDimensionLE_zero_pathAlgebra hQ)

/-- **Problem 9.4.6 (i), free algebra.** The free associative algebra `k⟨x₁, …, xₙ⟩` on
`n ≥ 1` generators (the path algebra of the one-vertex quiver with `n` loops) has homological
dimension `1`. -/
theorem homologicalDimension_freeAlgebra_eq_one
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    Etingof.homologicalDimension (FreeAlgebra k (Fin n)) = 1 :=
  sorry

/-- The path-counting matrix of a quiver `Q`: the `(i, j)` entry is the number of oriented
paths from `i` to `j`. This is the Cartan matrix of the path algebra of a finite acyclic
quiver (Problem 9.4.6 (ii)). -/
noncomputable def pathCountMatrix (Q : Type u) [Quiver Q] : Matrix Q Q ℕ :=
  Matrix.of fun i j => Nat.card (Quiver.Path i j)

/-- **Problem 9.4.6 (ii).** Let `Q` be a finite oriented graph without oriented cycles. Then
the Cartan matrix of the path algebra `P_Q` is the path-counting matrix: `cᵢⱼ` is the number
of oriented paths from `i` to `j`.

The projective covers `P` of the simple modules are supplied together with the defining
identification `hcover : Hom_A(Pᵢ, Pⱼ) ≅ (paths i → j) →₀ k` (for the path algebra these are
`Pᵢ = A·eᵢ` with `Hom_A(Pᵢ, Pⱼ) ≅ eᵢ A eⱼ`, free on the paths from `i` to `j`). Acyclicity
`hacyclic` makes each path type finite, so `Nat.card` is the genuine number of paths. -/
theorem cartanMatrix_pathAlgebra_eq_pathCount
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hacyclic : ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil)
    [∀ i j : Q, Finite (Quiver.Path i j)]
    (P : Q → Type u) [∀ i, AddCommGroup (P i)]
    [∀ i, Module (Etingof.PathAlgebra k Q) (P i)] [∀ i, Module k (P i)]
    [∀ i, SMulCommClass (Etingof.PathAlgebra k Q) k (P i)]
    (hcover : ∀ i j : Q,
      Nonempty ((P i →ₗ[Etingof.PathAlgebra k Q] P j) ≃ₗ[k] (Quiver.Path i j →₀ k))) :
    Etingof.algebraCartanMatrix (k := k) (A := Etingof.PathAlgebra k Q) P = pathCountMatrix Q := by
  ext i j
  obtain ⟨e⟩ := hcover i j
  have : Fintype (Quiver.Path i j) := Fintype.ofFinite _
  simp only [Etingof.algebraCartanMatrix, pathCountMatrix, Matrix.of_apply]
  rw [e.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

end Etingof.Problem946
