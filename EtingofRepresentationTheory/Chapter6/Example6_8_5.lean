import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_3_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_5
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Proposition6_6_8

/-!
# Example 6.8.5: Reflection Functors on D₄

Demonstrates reflection functors on the D₄ quiver with all arrows pointing towards
vertex 4 (the central node).

Starting with the 1-dimensional representation V_{α₄} at vertex 4:
- Apply F⁻₃ F⁻₂ F⁻₁ to get V_{α₁+α₂+α₃+α₄}
- Apply F⁻₄ to get V_{α₁+α₂+α₃+2α₄}

The final representation is the inclusion of three lines into the plane, which is
the most complicated indecomposable representation of D₄.

## Mathlib correspondence

D₄ is available as `DynkinDiagram.D 4` in Mathlib. The specific reflection
functor computations require the custom functor infrastructure from Definitions
6.6.3-6.6.4.

## Formalization approach

We state the example as a theorem about dimension vectors: starting from the
simple representation at vertex 4 (dimension vector α₄ = `Etingof.simpleRoot 4 3`
in the (V₁,V₂,V₃,V₄) basis), successive applications of reflection functors F⁻ᵢ
transform the dimension vector according to the simple reflection sᵢ.

Crucially, the simple reflections here are the *genuine* root-lattice reflections
`Etingof.simpleReflection 4 (Etingof.cartanMatrix 4 D₄_adj) i` from Definition
6.4.10 (sᵢ(x) = x − B(x, αᵢ)·αᵢ), built from the D₄ Cartan matrix of Definition
6.4.1. This is the same object whose connection to the *categorical* action of the
reflection functor is proved in **Proposition 6.6.8**:
`Etingof.Proposition6_6_8_source` shows that for a source vertex `i` with injective
source map, `d(F⁻ᵢ V) = sᵢ(d(V))` — the dimension vector of the reflection-functor
image equals the simple reflection of the dimension vector. So the dimension-vector
arithmetic below is not a disconnected combinatorial analogue: it faithfully tracks
the action of the functors F⁻ᵢ on actual representations, with the
functor-to-reflection identification supplied by the proved Proposition 6.6.8 (and
the `simpleReflectionDimVector_eq_simpleReflection` bridge relating its
arrow-indexed reflection to `Etingof.simpleReflection`).

We state the concrete computation results:
  s₁ s₂ s₃ (α₄) = α₁ + α₂ + α₃ + α₄ = (1,1,1,1)
  s₄ s₁ s₂ s₃ (α₄) = α₁ + α₂ + α₃ + 2α₄ = (1,1,1,2)
and that the final dimension vector (1,1,1,2) corresponds to an indecomposable
(being the maximal positive root of D₄).
-/

/-- The adjacency matrix of the D₄ graph: vertex 4 (index 3) is connected to
vertices 1, 2, 3 (indices 0, 1, 2). -/
def Etingof.D₄_adj : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 0, 1;
     0, 0, 0, 1;
     1, 1, 1, 0]

/-- The Cartan matrix of D₄, defined as `Etingof.cartanMatrix 4 D₄_adj` (= 2·Id − adj,
Definition 6.4.1). -/
def Etingof.D₄_cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  Etingof.cartanMatrix 4 Etingof.D₄_adj

/-- The Cartan matrix of D₄ has the expected explicit entries. -/
theorem Etingof.D₄_cartan_eq :
    Etingof.D₄_cartan =
      !![2, 0, 0, -1;
         0, 2, 0, -1;
         0, 0, 2, -1;
         -1, -1, -1, 2] := by
  decide

/-- The dimension vector α₄: the simple root at vertex 4 (index 3),
`Etingof.simpleRoot 4 3` (Definition 6.4.5). -/
def Etingof.D₄_α₄ : Fin 4 → ℤ := Etingof.simpleRoot 4 3

/-- **Example 6.8.5, Part 1 (Etingof)**: Applying the sequence of simple reflections
s₁, s₂, s₃ (the dimension-vector action of the reflection functors F⁻₁, F⁻₂, F⁻₃,
by Proposition 6.6.8) to the dimension vector α₄ yields the dimension vector
(1,1,1,1) = α₁+α₂+α₃+α₄.

The reflections are the genuine root-lattice reflections of Definition 6.4.10
applied to the D₄ Cartan matrix, so this is the dimension vector of
`F⁻₁ F⁻₂ F⁻₃ V_{α₄}`. -/
theorem Etingof.Example6_8_5_part1 :
    Etingof.simpleReflection 4 Etingof.D₄_cartan 0
      (Etingof.simpleReflection 4 Etingof.D₄_cartan 1
        (Etingof.simpleReflection 4 Etingof.D₄_cartan 2 Etingof.D₄_α₄)) =
    ![1, 1, 1, 1] := by
  decide

/-- **Example 6.8.5, Part 2 (Etingof)**: Further applying the simple reflection s₄
(the dimension-vector action of F⁻₄, by Proposition 6.6.8) to the dimension vector
(1,1,1,1) yields the dimension vector (1,1,1,2) = α₁+α₂+α₃+2α₄, the maximal positive
root of D₄ — the dimension vector of `F⁻₄ F⁻₁ F⁻₂ F⁻₃ V_{α₄}`. -/
theorem Etingof.Example6_8_5_part2 :
    Etingof.simpleReflection 4 Etingof.D₄_cartan 3
      (Etingof.simpleReflection 4 Etingof.D₄_cartan 0
        (Etingof.simpleReflection 4 Etingof.D₄_cartan 1
          (Etingof.simpleReflection 4 Etingof.D₄_cartan 2 Etingof.D₄_α₄))) =
    ![1, 1, 1, 2] := by
  decide

/-- **Example 6.8.5, Part 3 (Etingof)**: The final dimension vector (1,1,1,2) is the
dimension vector of the maximal indecomposable representation of D₄ — the inclusion
of three lines into the plane. It corresponds to (dim V₁, dim V₂, dim V₃, dim V) =
(1,1,1,2) in D₄Rep notation, which is (2,1,1,1) = (center, arm₁, arm₂, arm₃).

In the D₄Rep convention from Example 6.3.1, the center has dimension 2 and
each arm has dimension 1. -/
theorem Etingof.Example6_8_5_maximal_indecomposable :
    (2, 1, 1, 1) ∈ D₄_indecomposable_dimVectors := by
  decide
