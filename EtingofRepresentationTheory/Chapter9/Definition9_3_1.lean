import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

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
constructed from the input data (the algebra `A`, the ground field `k`, and the
family `P` of projective covers) rather than from an externally supplied table of numbers.
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

/-!
## Sign of the entries (Definition 9.3.1)

Etingof records immediately after the definition that the Cartan matrix "is a matrix
with nonnegative entries, whose diagonal entries are positive". Nonnegativity is built
into the `ℕ`-valued codomain of `Etingof.algebraCartanMatrix`; the substantive endpoint
is diagonal positivity, `0 < cᵢᵢ`. The `(i, i)` entry is

`cᵢᵢ = dim_k Hom_A(Pᵢ, Pᵢ) = dim_k End_A(Pᵢ)`,

and the identity endomorphism `id : Pᵢ →ₗ[A] Pᵢ` is a nonzero element of this space
whenever `Pᵢ` is nonzero (i.e. `Nontrivial (P i)`), so the dimension is positive. Since
each `Pᵢ` is the projective cover of a simple module `Mᵢ`, it is nonzero — and more
specifically indecomposable, which already carries nonzeroness in
`Etingof.IsIndecomposable`.
-/

omit [Algebra k A] in
/-- Nonnegativity of the Cartan matrix entries (Etingof Definition 9.3.1: "a matrix with
nonnegative entries"). Automatic from the `ℕ`-valued codomain, exposed here at the
Cartan-matrix API boundary. -/
theorem Etingof.algebraCartanMatrix_entry_nonneg
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (i j : ι) : 0 ≤ Etingof.algebraCartanMatrix (k := k) (A := A) P i j :=
  Nat.zero_le _

/-- **Diagonal positivity of the Cartan matrix**: `0 < cᵢᵢ` (Etingof Definition 9.3.1,
"a matrix ... whose diagonal entries are positive").

The `(i, i)` entry is `dim_k Hom_A(Pᵢ, Pᵢ) = dim_k End_A(Pᵢ)`. The identity endomorphism
is a nonzero element of `Pᵢ →ₗ[A] Pᵢ` whenever `Pᵢ` is nonzero, so this dimension is
positive. The hypotheses are exactly those supplied by the projective-cover family:
`Nontrivial (P i)` (each projective cover of a simple module is nonzero) and
`Module.Finite k (P i)` (finite dimensionality, making the Hom space finite dimensional
over `k`). -/
theorem Etingof.algebraCartanMatrix_diag_pos
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)] [Nontrivial (P i)] :
    0 < Etingof.algebraCartanMatrix (k := k) (A := A) P i i := by
  change 0 < Module.finrank k (P i →ₗ[A] P i)
  -- The `A`-linear endomorphisms form a `k`-subspace of the (finite-dimensional) `k`-linear
  -- endomorphisms, via the injective scalar-restriction map; hence finite dimensional.
  haveI : Module.Finite k (P i →ₗ[A] P i) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (P i) (P i) k)
      (LinearMap.restrictScalars_injective k)
  rw [Module.finrank_pos_iff (R := k)]
  -- Nontriviality of the endomorphism space: the identity is not the zero map.
  obtain ⟨x, hx⟩ := exists_ne (0 : P i)
  refine nontrivial_of_ne (LinearMap.id : P i →ₗ[A] P i) 0 ?_
  intro h
  exact hx (by have := LinearMap.congr_fun h x; simpa using this)

/-- Diagonal positivity of the Cartan matrix from indecomposability of the projective
covers. This is the form matching Etingof's hypotheses: each projective cover `Pᵢ` is
indecomposable, and `Etingof.IsIndecomposable` carries nonzeroness (`Nontrivial`). -/
theorem Etingof.algebraCartanMatrix_diag_pos_of_indecomposable
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)]
    (hP : Etingof.IsIndecomposable A (P i)) :
    0 < Etingof.algebraCartanMatrix (k := k) (A := A) P i i :=
  haveI : Nontrivial (P i) := hP.1
  Etingof.algebraCartanMatrix_diag_pos P i

omit [Algebra k A] in
/-- Nonnegativity of the integer-cast Cartan matrix, in the form used by downstream
matrix arguments (`C.map (Nat.cast : ℕ → ℤ)`, e.g. in `homClassVector_projective_eq_mulVec`). -/
theorem Etingof.algebraCartanMatrix_intCast_entry_nonneg
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (i j : ι) :
    (0 : ℤ) ≤ ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i j := by
  rw [Matrix.map_apply]; exact Int.natCast_nonneg _

/-- Diagonal positivity of the integer-cast Cartan matrix, in the form used by downstream
matrix arguments. -/
theorem Etingof.algebraCartanMatrix_intCast_diag_pos
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)] [Nontrivial (P i)] :
    (0 : ℤ) < ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i i := by
  rw [Matrix.map_apply]
  exact_mod_cast Etingof.algebraCartanMatrix_diag_pos P i
