import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 9.3.1: Cartan matrix

The **Cartan matrix** of a finite dimensional algebra A is the matrix C = (cᵢⱼ), where
cᵢⱼ = [Pⱼ : Mᵢ] is the multiplicity of Mᵢ in the Jordan–Hölder series of Pⱼ.

By Proposition 9.2.3, cᵢⱼ = dim Hom_A(Pᵢ, Pⱼ). Thus C has nonneg integer entries and
positive diagonal entries.

## Mathlib correspondence

Not directly in Mathlib. The Cartan matrix is specific to representation theory of
finite dimensional algebras.
-/

/-- The Cartan matrix of a finite dimensional algebra, in the sense of Etingof Definition 9.3.1.
cᵢⱼ = [Pⱼ : Mᵢ], the Jordan–Hölder multiplicity of the i-th simple in the j-th projective
indecomposable. -/
def Etingof.CartanMatrix : (sorry : Prop) := sorry
