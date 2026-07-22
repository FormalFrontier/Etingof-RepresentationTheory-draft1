import Mathlib

/-!
# Example 4.3: Irreducible Representations of Finite Abelian Groups

For a finite abelian group `G = ℤ/n₁ℤ × ⋯ × ℤ/nₖℤ`, all irreducible representations
over an algebraically closed field are 1-dimensional. This is the fact the book recalls
("all irreducible representations over `ℂ` (and algebraically closed fields in general) of
commutative algebras and groups are 1-dimensional"), and it genuinely uses both the
commutativity of `G` and the algebraic closedness of `k`.

The dual group (Pontryagin dual) `G^∨` consists of all irreducible characters.
For `ℤ/nℤ`: the irreducible characters are `ρₖ(m) = e^(2πimk/n)` for `k = 0, …, n-1`,
giving `ℤ/nℤ^∨ ≅ ℤ/nℤ`. In general `(G₁ × G₂)^∨ = G₁^∨ × G₂^∨`, so `G^∨ ≅ G`
(non-canonically), and `G ≅ (G^∨)^∨` canonically via `φ(g)(χ) = χ(g)`.

## Mathlib correspondence

A representation `ρ : Representation k G V` is the same data as a module over the group
algebra `k[G] = MonoidAlgebra k G`, via `ρ.asModule`. When `G` is commutative, `k[G]` is a
commutative `k`-algebra, so an irreducible (= `IsSimpleModule k[G] ρ.asModule`)
finite-dimensional representation is 1-dimensional by Etingof Corollary 2.3.12, formalized in
Mathlib as `IsSimpleModule.finrank_eq_one_of_isMulCommutative`. This is exactly the book's
argument: by Schur's lemma every `g ∈ G` acts as a scalar, so every line is a subrepresentation.
-/

/-- For a finite abelian group `G` and an algebraically closed field `k`, every irreducible
finite-dimensional representation `ρ : Representation k G V` is 1-dimensional. Irreducibility
is `IsSimpleModule (MonoidAlgebra k G) ρ.asModule`, i.e. simplicity *as a representation* of
`G` (a module over the group algebra `k[G]`), not merely as a `k`-vector space.
(Etingof Example 4.3) -/
theorem Etingof.Example4_3_FiniteAbelianGroups
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [CommGroup G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hirr : IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Module.finrank k V = 1 := by
  -- The group algebra `k[G]` is commutative because `G` is commutative.
  have : IsMulCommutative (MonoidAlgebra k G) := ⟨⟨mul_comm⟩⟩
  -- Corollary 2.3.12: a simple finite-dimensional module over a commutative `k`-algebra over an
  -- algebraically closed field is 1-dimensional. Here the algebra is `k[G]` and the module is
  -- `ρ.asModule` (whose `k`-dimension equals `finrank k V`).
  have h : Module.finrank k ρ.asModule = 1 :=
    IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule)
  rwa [ρ.asModuleEquiv.finrank_eq] at h
