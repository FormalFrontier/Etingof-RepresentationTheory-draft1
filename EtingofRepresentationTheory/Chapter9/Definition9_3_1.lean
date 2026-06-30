import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Definition 9.3.1: Cartan matrix

The **Cartan matrix** of a finite dimensional algebra `A` is the matrix `C = (cᵢⱼ)`, where
(following the setup of §9.3)

`cᵢⱼ = dim_k Hom_A(Pᵢ, Pⱼ) = [Pⱼ : Mᵢ]`,

i.e. the dimension of the space of `A`-module maps between the projective covers `Pᵢ`, `Pⱼ`
of the simple modules `Mᵢ`, `Mⱼ`; by Proposition 9.2.3 this equals the Jordan–Hölder
multiplicity of `Mᵢ` in `Pⱼ`. By Proposition 9.2.3 this matrix has nonnegative integer
entries and (since `Pᵢ` covers `Mᵢ`) positive diagonal entries.

## Mathlib correspondence

Not directly in Mathlib. The Cartan matrix is specific to representation theory of
finite dimensional algebras.

## Formalization approach

The entries `cᵢⱼ` are defined exactly as in the book: `dim_k Hom_A(Pᵢ, Pⱼ)`. This is the
form of the definition stated at the start of §9.3 (`cᵢⱼ := dim Hom_A(Pᵢ, Pⱼ)`), and it is
genuinely constructed from the input data — the algebra `A`, the ground field `k`, and the
family `P` of projective covers — rather than from an externally supplied table of numbers.
Concretely, the `(i, j)` entry is `Module.finrank k (P i →ₗ[A] P j)`, the `k`-dimension of
the Hom space. By Proposition 9.2.3 (`Etingof.projective_cover_hom_multiplicity`) this
equals the Jordan–Hölder multiplicity `[Pⱼ : Mᵢ]` whenever the `Pᵢ` are the projective
covers of the simple modules `Mᵢ`, recovering the alternative description in the statement
of Definition 9.3.1.
-/

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]

/-- The Cartan matrix of a finite dimensional algebra `A`, in the sense of Etingof
Definition 9.3.1.

Given an index type `ι` for the simple modules `Mᵢ` and the family `P` of their projective
covers `Pᵢ` (each an `A`-module that is also a `k`-vector space, with the two scalar actions
commuting), the Cartan matrix is the `ι × ι` matrix whose `(i, j)` entry is

`cᵢⱼ = dim_k Hom_A(Pᵢ, Pⱼ)`.

By Proposition 9.2.3 (`Etingof.projective_cover_hom_multiplicity`), when the `Pᵢ` are the
projective covers of the simple modules `Mᵢ` this dimension equals the Jordan–Hölder
multiplicity `[Pⱼ : Mᵢ]` of `Mᵢ` in `Pⱼ`, which is the description used in the book's
statement of Definition 9.3.1. -/
noncomputable def Etingof.algebraCartanMatrix
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)] :
    Matrix ι ι ℕ :=
  Matrix.of fun i j => Module.finrank k (P i →ₗ[A] P j)
