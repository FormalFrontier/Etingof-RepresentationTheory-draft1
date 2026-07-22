import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.Quiver.Path
import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3

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

open Etingof

namespace Etingof.Problem946

/-- **Problem 9.4.6 (i), path algebra.** The path algebra `P_Q` of a quiver `Q` with at least
one edge has homological dimension `1`. -/
theorem homologicalDimension_pathAlgebra_eq_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    Etingof.homologicalDimension (Etingof.PathAlgebra k Q) = 1 :=
  sorry

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
    Etingof.algebraCartanMatrix (k := k) (A := Etingof.PathAlgebra k Q) P = pathCountMatrix Q :=
  sorry

end Etingof.Problem946
