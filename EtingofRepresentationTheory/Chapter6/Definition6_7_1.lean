import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_10

/-!
# Definition 6.7.1: Coxeter Element

Let Q be a quiver with underlying graph Γ. Fix a labeling 1, …, n of the vertices.
The **Coxeter element** c corresponding to this labeling is c = s₁ s₂ ⋯ sₙ,
the product of all simple reflections.

Here the simple reflections sᵢ are the genuine simple reflections of the quiver
(Definition 6.4.10) acting on the root lattice ℤⁿ, defined from the Cartan matrix
A = 2·Id − adj (Definition 6.4.1). The Coxeter element is therefore the ordered
composition of these reflections on ℤⁿ, not an abstract group product: it is tied to
the Dynkin/Cartan structure of the quiver, as the book intends.

## Mathlib correspondence

Mathlib has `CoxeterSystem` and `CoxeterGroup` with simple reflections in
`Mathlib.GroupTheory.Coxeter.Basic`. The Coxeter element as a product of all
generators is realized here concretely as the composition of the `simpleReflection`
maps on the root lattice.
-/

/-- The Coxeter element of a quiver `Q` with `n` vertices and adjacency matrix `adj`:
the ordered composition s₁ s₂ ⋯ sₙ of all simple reflections, acting on the root
lattice ℤⁿ. Each sᵢ is the simple reflection for the i-th simple root with respect to
the Cartan matrix A = 2·Id − adj. (Etingof Definition 6.7.1) -/
def Etingof.coxeterElement (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  let A := Etingof.cartanMatrix n adj
  (List.ofFn (fun i : Fin n => Etingof.simpleReflection n A i)).foldr
    (· ∘ ·) id v
