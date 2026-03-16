import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Theorem 3.6.2: Linear Independence of Characters

(i) Characters of (distinct) irreducible finite dimensional representations of A are
    linearly independent.

(ii) If A is a finite dimensional semisimple algebra, then these characters form a basis
     of (A/[A,A])*.

The proof of (i) uses the density theorem: the surjectivity of the combined representation
map ensures that traces of distinct irreducibles can be independently varied.

The proof of (ii) shows that [Mat_d(k), Mat_d(k)] = sl_d(k) (traceless matrices),
so A/[A,A] ≅ k^r for semisimple A = ⊕ Mat_{dᵢ}(k), and r linearly independent
characters on an r-dimensional space form a basis.
-/

open Module in
/-- The character of a finite-dimensional module V over a k-algebra A, defined as
the trace of the action map: χ_V(a) = tr(ρ_V(a)). -/
noncomputable def Etingof.character (k : Type*) (A : Type*) (V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Free k V] [Module.Finite k V] :
    Dual k A :=
  (LinearMap.trace k V).comp (Algebra.lsmul k k V : A →ₐ[k] End k V).toLinearMap

open Module in
/-- Characters of distinct irreducible representations are linearly independent.
Etingof Theorem 3.6.2(i). -/
theorem Etingof.characters_linearly_independent (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => Etingof.character k A (V i)) := by
  sorry

open Module in
/-- For a semisimple algebra, characters of irreducibles span the space of tracial
linear functionals (those f with f(ab) = f(ba)), hence form a basis of (A/[A,A])*.
Combined with part (i), this gives a basis.
Etingof Theorem 3.6.2(ii). -/
theorem Etingof.characters_basis_semisimple (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    ∀ f : Dual k A, (∀ a b : A, f (a * b) = f (b * a)) →
      f ∈ Submodule.span k (Set.range (fun i => Etingof.character k A (V i))) := by
  sorry
