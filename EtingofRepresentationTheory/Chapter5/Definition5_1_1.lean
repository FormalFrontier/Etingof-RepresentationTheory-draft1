import Mathlib

/-!
# Definition 5.1.1: Complex, Real, and Quaternionic Type

An irreducible complex representation V of a finite group G is said to be of:
- **complex type** if V ≇ V* (not isomorphic to its dual)
- **real type** if V admits a nondegenerate symmetric bilinear form invariant under G
- **quaternionic type** if V admits a nondegenerate skew-symmetric bilinear form invariant under G

## Mathlib correspondence

Mathlib does not have a dedicated type classification for representations. This can be modeled
using `LinearMap.BilinForm` with symmetry/skew-symmetry conditions and G-invariance.
-/

/-- Classification of irreducible representations into complex, real, and quaternionic types.
(Etingof Definition 5.1.1) -/
inductive Etingof.RepresentationType where
  | complex
  | real
  | quaternionic

/-- A representation is of real type if it admits a G-invariant nondegenerate symmetric
bilinear form. (Etingof Definition 5.1.1) -/
def Etingof.IsRealType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = B w v) ∧  -- symmetric
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧  -- nondegenerate
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)  -- G-invariant

/-- A representation is of quaternionic type if it admits a G-invariant nondegenerate
skew-symmetric bilinear form. (Etingof Definition 5.1.1) -/
def Etingof.IsQuaternionicType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = -(B w v)) ∧  -- skew-symmetric
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧  -- nondegenerate
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)  -- G-invariant
