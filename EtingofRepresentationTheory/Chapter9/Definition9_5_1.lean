import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Definition 9.5.1: Linked simple modules and blocks

Two simple modules X, Y are **linked** if there exists a chain of simple modules
X = X₀, X₁, …, Xₙ = Y such that for each consecutive pair (Xᵢ, Xᵢ₊₁), either
Ext¹(Xᵢ, Xᵢ₊₁) ≠ 0 or Ext¹(Xᵢ₊₁, Xᵢ) ≠ 0. This is an equivalence relation on
simple modules.

The equivalence classes are S₁, …, Sₗ. The k-th **block** 𝒞ₖ of the category of
finite dimensional A-modules consists of objects whose Jordan–Hölder composition
factors all belong to Sₖ.

## Mathlib correspondence

Not directly in Mathlib. Blocks are a fundamental concept in modular representation theory.
-/

/-- Linked simple modules and blocks of a finite dimensional algebra,
in the sense of Etingof Definition 9.5.1. -/
def Etingof.Block : (sorry : Prop) := sorry
