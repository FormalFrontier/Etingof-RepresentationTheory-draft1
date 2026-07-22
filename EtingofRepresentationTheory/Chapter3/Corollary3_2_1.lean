import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Corollary 3.2.1: Linear Map Realization (interpolation)

Let `V` be an irreducible finite dimensional representation of `A` over an algebraically
closed field `k`, and let `v₁, …, vₙ ∈ V` be any `k`-linearly independent vectors. Then for
any `w₁, …, wₙ ∈ V` there exists an element `a ∈ A` such that `a · vᵢ = wᵢ` for all `i`.

This is a direct corollary of the density theorem (Etingof Theorem 3.2.2(i),
`Etingof.density_theorem_part1`): since the `vᵢ` are linearly independent over `k`, there is
a `k`-linear endomorphism `f` of `V` with `f vᵢ = wᵢ`, and by the density theorem the
representation map `A → End_k V` is surjective, so `f` is realized by some `a ∈ A`.

The hypothesis is `k`-linear independence of the `vᵢ` (independence over the base field), as
in the book — *not* independence over the algebra `A`. The latter would be far stronger: in
a simple `A`-module any two distinct nonzero vectors are `A`-dependent, so `A`-independence
forces `n ≤ 1` and collapses the statement.
-/

open Module in
/-- In an irreducible finite dimensional representation over an algebraically closed field,
any assignment of values on `k`-linearly independent vectors can be realized by an algebra
element. Etingof Corollary 3.2.1. -/
theorem Etingof.irreducible_interpolation (k : Type*) (A : Type*) (V : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V]
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent k v) (w : Fin n → V) :
    ∃ a : A, ∀ i, a • v i = w i := by
  -- Build a `k`-linear endomorphism `f` of `V` with `f (v i) = w i`, using that the `v i`
  -- form a basis of their span and extending the prescribed map to all of `V`.
  let b : Basis (Fin n) k (Submodule.span k (Set.range v)) := Basis.span hv
  let f₀ : (Submodule.span k (Set.range v)) →ₗ[k] V := b.constr k w
  obtain ⟨f, hf⟩ := f₀.exists_extend
  have hfv : ∀ i, f (v i) = w i := by
    intro i
    have h1 : f ((Submodule.span k (Set.range v)).subtype (b i)) = f₀ (b i) :=
      LinearMap.congr_fun hf (b i)
    rw [Basis.constr_basis] at h1
    rwa [show (Submodule.span k (Set.range v)).subtype (b i) = v i from
      Basis.coe_span_apply hv i] at h1
  -- The density theorem makes the representation map `A → End_k V` surjective, so `f = a • -`.
  obtain ⟨a, ha⟩ := Etingof.density_theorem_part1 k A V f
  refine ⟨a, fun i => ?_⟩
  have h := LinearMap.congr_fun ha (v i)
  rw [hfv i] at h
  exact h
