import EtingofRepresentationTheory.Chapter9.Theorem9_2_1
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Proposition 9.2.3: Hom from projective cover computes Jordan–Hölder multiplicity

Let N be a finite dimensional A-module. Then dim Hom_A(Pᵢ, N) = [N : Mᵢ], the multiplicity
of Mᵢ in the Jordan–Hölder series of N.

## Proof sketch

Use the fact that Hom(Pᵢ, −) is exact (since Pᵢ is projective) and that
dim Hom(Pᵢ, Mⱼ) = δᵢⱼ. By induction on the length of a composition series of N.

## Formalization approach

The Jordan–Hölder multiplicity-counting function is not yet available in Mathlib as a
standalone definition. We define `compositionFactorMultiplicity` to count how many
successive quotients in a composition series are A-linearly isomorphic to a given
simple module. By the Jordan–Hölder theorem, this count is independent of the choice
of series.

The theorem then states that `dim_k Hom_A(Pᵢ, N)` equals this count for the simple
module Mᵢ, given the Kronecker delta property `dim Hom(Pᵢ, Mⱼ) = δᵢⱼ` from
Theorem 9.2.1(i).
-/

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]

/-- The multiplicity of a simple module `S` as a composition factor in a composition
series `s` of the submodule lattice of `N`.

Counts the number of indices `l` in the series where the successive quotient
`s(l+1) / s(l)` is A-linearly isomorphic to `S`.

The successive quotient at index `l` is modeled as `(s l.succ) ⧸ (s l).comap (s l.succ).subtype`,
following Mathlib's `JordanHolderModule` convention. -/
noncomputable def Etingof.compositionFactorMultiplicity
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : CompositionSeries (Submodule A N))
    (S : Type*) [AddCommGroup S] [Module A S] : ℕ :=
  @Finset.card _ (@Finset.filter _ (fun l : Fin s.length =>
      Nonempty ((↥(s l.succ) ⧸ (s (Fin.castSucc l)).comap (s l.succ).subtype) ≃ₗ[A] S))
    (fun _ => Classical.dec _) Finset.univ)

/-- **Proposition 9.2.3**: The dimension of Hom_A(Pᵢ, N) equals the Jordan–Hölder
multiplicity of Mᵢ in N.

Let A be a finite-dimensional algebra over a field k, let M₁, …, Mₘ be the simple
A-modules, and let P₁, …, Pₘ be their projective covers (from Theorem 9.2.1). For any
finite-dimensional A-module N and any composition series `s` of N (with `s.head = ⊥`
and `s.last = ⊤`), the dimension `dim_k Hom_A(Pᵢ, N)` equals the number of composition
factors of `s` that are A-linearly isomorphic to Mᵢ.

The proof proceeds by induction on the composition length of N:
- Base case: N is simple, so N ≅ Mⱼ for some j, and dim Hom(Pᵢ, Mⱼ) = δᵢⱼ by
  Theorem 9.2.1(i).
- Inductive step: given a short exact sequence 0 → N' → N → N/N' → 0 with
  shorter composition series, use exactness of Hom(Pᵢ, −) (since Pᵢ is projective)
  to get dim Hom(Pᵢ, N) = dim Hom(Pᵢ, N') + dim Hom(Pᵢ, N/N''), and multiplicities
  are additive on short exact sequences.

(Etingof Proposition 9.2.3) -/
theorem Etingof.projective_cover_hom_multiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    [∀ i, Etingof.IsIndecomposableModule A (P i)]
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (N : Type*) [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] [SMulCommClass A k N]
    [Module.Finite k N]
    (s : CompositionSeries (Submodule A N))
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    ∀ i, Module.finrank k (P i →ₗ[A] N) =
      Etingof.compositionFactorMultiplicity s (M i) := by
  sorry
