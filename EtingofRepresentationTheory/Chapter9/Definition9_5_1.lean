import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 9.5.1: Linked simple modules and blocks

Two **simple** finite dimensional modules `X, Y` are **linked** if there is a chain of
*simple* modules `X = M₀, M₁, …, Mₙ = Y` such that for each consecutive pair `(Mᵢ, Mᵢ₊₁)`,
either `Ext¹(Mᵢ, Mᵢ₊₁) ≠ 0` or `Ext¹(Mᵢ₊₁, Mᵢ) ≠ 0`. This is an equivalence relation on
simple modules; its equivalence classes `S₁, …, Sₗ` partition the isomorphism classes of
simple modules.

The k-th **block** `𝒞ₖ` of the category of finite dimensional `A`-modules consists of the
objects `M` all of whose Jordan–Hölder composition factors lie in `Sₖ`.

## Fidelity note

The chain in the book runs through **simple** modules only. This is essential: over a product
`A = A₁ × A₂`, taking simples `X` (block 1), `Y` (block 2) and a non-simple `N = N₁ ⊕ N₂` with
`Ext¹(X, N) ≠ 0` and `Ext¹(N, Y) ≠ 0` would link `X` and `Y` if the chain were allowed to pass
through `N`, even though `X` and `Y` lie in different blocks. The base relation
`Etingof.ExtOrIsoSimple` therefore carries `IsSimpleModule` side conditions on both endpoints,
so every chain step connects two simple modules. Likewise the blocks are the Jordan–Hölder
subcategories `Etingof.InBlock`, not a quotient of all modules.

## Mathlib correspondence

Not directly in Mathlib. Blocks are a fundamental concept in modular representation theory.
-/

universe v u

open CategoryTheory

section

variable (R : Type u) [Ring R] [Small.{v} R]

/-- Two objects in `ModuleCat R` are **directly Ext¹-linked** if `Ext¹(X, Y)` is nontrivial
(i.e., there exists a nonzero element). This is the basic building block for the linking
relation. Note: `Nontrivial` rather than `Nonempty` is needed because `Abelian.Ext X Y 1`
always has a zero element (it is an `AddCommGroup`). -/
def Etingof.DirectlyExtLinked (X Y : ModuleCat.{v} R) : Prop :=
  Nontrivial (Abelian.Ext X Y 1)

/-- Two objects in `ModuleCat R` are **Ext¹-adjacent** if they are directly Ext¹-linked
in either direction: `Ext¹(X, Y) ≠ 0` or `Ext¹(Y, X) ≠ 0`. -/
def Etingof.ExtAdjacent (X Y : ModuleCat.{v} R) : Prop :=
  Etingof.DirectlyExtLinked R X Y ∨ Etingof.DirectlyExtLinked R Y X

/-- The base relation for the **linking of simple modules** (Etingof Definition 9.5.1): two
modules are related if they are **both simple** and either Ext¹-adjacent or categorically
isomorphic. The `IsSimpleModule` side conditions are essential — the book's chain runs through
simple modules only — and the isomorphism clause supplies reflexivity up to isomorphism (the
linking relation is defined on isomorphism classes of simple modules). -/
def Etingof.ExtOrIsoSimple (X Y : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R X ∧ IsSimpleModule R Y ∧
    (Etingof.ExtAdjacent R X Y ∨ Nonempty (X ≅ Y))

/-- Two simple modules are **linked** (in the sense of Etingof Definition 9.5.1) if they are
related by the equivalence closure of the simplicity-gated Ext¹-adjacency relation: there
exists a chain `X = X₀, X₁, …, Xₙ = Y` of **simple** modules such that each consecutive pair
`(Xᵢ, Xᵢ₊₁)` satisfies `Ext¹(Xᵢ, Xᵢ₊₁) ≠ 0`, `Ext¹(Xᵢ₊₁, Xᵢ) ≠ 0`, or `Xᵢ ≅ Xᵢ₊₁`. -/
def Etingof.AreLinked (X Y : ModuleCat.{v} R) : Prop :=
  Relation.EqvGen (Etingof.ExtOrIsoSimple R) X Y

/-- Isomorphic simple modules are linked. -/
theorem Etingof.areLinked_of_iso {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) (e : X ≅ Y) :
    Etingof.AreLinked R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inr ⟨e⟩⟩

/-- A single Ext¹-adjacency between simple modules is a linking of length one. -/
theorem Etingof.areLinked_of_extAdjacent {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) (h : Etingof.ExtAdjacent R X Y) :
    Etingof.AreLinked R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inl h⟩

/-- The linking relation is an equivalence relation. -/
theorem Etingof.areLinked_equivalence :
    @Equivalence (ModuleCat.{v} R) (Etingof.AreLinked R) :=
  Relation.EqvGen.is_equivalence _

end

section Blocks

variable (R : Type u) [Ring R] [Small.{v} R]

/-- A simple module `S` is a **Jordan–Hölder composition factor** of `M` if it occurs as a
simple subquotient of `M`: there are submodules `N₁ ≤ N₂` of `M` with `N₂ / N₁ ≅ S`. For a
finite-length module this recovers exactly the multiset of Jordan–Hölder factors. -/
def Etingof.IsCompositionFactor (M S : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R S ∧ ∃ (N₁ N₂ : Submodule R M) (_ : N₁ ≤ N₂),
    Nonempty ((↥N₂ ⧸ N₁.comap N₂.subtype) ≃ₗ[R] S)

/-- Membership of `M` in the **block** of a simple module `S` (Etingof Definition 9.5.1): every
Jordan–Hölder composition factor of `M` is linked to `S`. The k-th block `𝒞ₖ` is the full
subcategory `{ M | Etingof.InBlock R S M }` for any `S ∈ Sₖ`; because linking is iso-invariant
on simples, this is independent of the chosen representative `S`. -/
def Etingof.InBlock (S M : ModuleCat.{v} R) : Prop :=
  ∀ T : ModuleCat.{v} R, Etingof.IsCompositionFactor R M T → Etingof.AreLinked R T S

/-- The type of simple objects of `ModuleCat R`. Its quotient by the linking relation is the
indexing set `B` of blocks in Etingof Definition 9.5.1. -/
def Etingof.SimpleObj : Type (max u (v + 1)) :=
  { X : ModuleCat.{v} R // IsSimpleModule R X }

/-- Linking as a setoid on the simple objects of `ModuleCat R`. The equivalence classes are the
blocks `Sₖ` partitioning the isomorphism classes of simple modules. -/
def Etingof.blockSetoid : Setoid (Etingof.SimpleObj.{v} R) where
  r X Y := Etingof.AreLinked R X.1 Y.1
  iseqv :=
    ⟨fun X => (Etingof.areLinked_equivalence R).refl X.1,
      fun h => (Etingof.areLinked_equivalence R).symm h,
      fun h₁ h₂ => (Etingof.areLinked_equivalence R).trans h₁ h₂⟩

/-- The set of **blocks** of `R`, in the sense of Etingof Definition 9.5.1: linking equivalence
classes of simple modules (the index set `B`). Each block `Sₖ` determines the full subcategory
`{ M | Etingof.InBlock R S M }` of objects whose Jordan–Hölder factors all lie in `Sₖ`. -/
def Etingof.Block : Type _ :=
  Quotient (Etingof.blockSetoid.{v} R)

end Blocks
