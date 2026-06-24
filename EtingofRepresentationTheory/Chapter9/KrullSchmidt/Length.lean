import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import Mathlib.Order.KrullDimension
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Composition length for finite abelian categories (Krull–Schmidt, link 1/5)

This file introduces a `ℕ`-valued **composition length** `Etingof.clength X` for objects of a
finite abelian category, together with the additivity property that every later Krull–Schmidt
step (existence of a decomposition into indecomposables, Fitting's lemma) uses as its
well-founded induction measure.

## Design

`clength X` is defined as the order-theoretic **height** of the top element of the subobject
lattice `CategoryTheory.Subobject X`:

```
clength X = (Order.height (⊤ : Subobject X)).toNat.
```

For a finite-length object this height is finite and equals the length of any composition
series, by the Jordan–Hölder theorem applied to the (modular) subobject lattice. The definition
above is *total* — it returns a real `ℕ` for every object — so it can serve as the carrier of the
API even before the finiteness/additivity content is in place. `Order.height` lives in `ℕ∞`, and
`.toNat` sends `⊤` (the not-finite-length case, which does not occur in a finite abelian category)
to `0`.

## Mathlib correspondence and the additivity crux

Mathlib develops Jordan–Hölder only abstractly (`Mathlib/Order/JordanHolder.lean`,
`CompositionSeries`, `CompositionSeries.jordan_holder`) and concretely for `Submodule R M`
(`JordanHolderModule.instJordanHolderLattice`). For the subobject lattice of an abelian category
it has **neither** a `JordanHolderLattice` instance, **nor** the `IsModularLattice (Subobject X)`
instance, **nor** the categorical second isomorphism theorem `(A ⊔ B)/A ≅ B/(A ⊓ B)` that such an
instance needs. The Stacks-project route (tag `0FCK`) for categorical Jordan–Hölder is flagged as
future work in `Mathlib/CategoryTheory/Noetherian.lean`.

Consequently the **additivity** of `clength` over short exact sequences,

```
clength S.X₂ = clength S.X₁ + clength S.X₃,
```

is the genuine categorical Jordan–Hölder content and is the hard part of this link. It is stated
here (top-down) and its proof — which requires either wiring `JordanHolderLattice` onto
`Subobject X` or a direct Schreier-refinement argument, together with finiteness of the height in a
finite abelian category — is left as a documented `sorry`, tracked as a follow-up issue. The
`clength_eq_zero` characterisation is proved in the (unconditional) "zero ⇒ length zero"
direction; its converse, and positivity for nonzero objects, both require the same finiteness
input and are likewise isolated.

This top-down split lets the downstream consumers (existence-of-decomposition and Fitting's-lemma
sub-issues of #5153) build against the final `clength` API immediately.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

/-- The **composition length** of an object `X` of a finite abelian category: the height of the
top element of the subobject lattice `Subobject X`. For a finite-length object this equals the
length of any composition series (well-defined by the Jordan–Hölder theorem). The definition is
total, returning `0` on the not-finite-length case (which does not occur in a finite abelian
category). -/
noncomputable def clength (X : C) : ℕ :=
  (Order.height (⊤ : Subobject X)).toNat

/-- A zero object has composition length `0`: its subobject lattice is a singleton, so the top
element is a minimum and has height `0`. -/
theorem clength_eq_zero_of_isZero {X : C} (h : IsZero X) : clength X = 0 := by
  have : Subsingleton (Subobject X) := Subobject.subsingleton_of_isZero h
  have hmin : IsMin (⊤ : Subobject X) := fun b _ => le_of_eq (Subsingleton.elim _ _)
  simp only [clength, Order.height_eq_zero.2 hmin, ENat.toNat_zero]

/-- An object has composition length `0` iff it is a zero object.

The `←` direction is `clength_eq_zero_of_isZero`. The `→` direction needs that the height of
`⊤ : Subobject X` is *finite* in a finite abelian category (`Order.height ... ≠ ⊤`); only then does
`(Order.height ⊤).toNat = 0` force `Order.height ⊤ = 0`, i.e. `X` zero (via
`Subobject.nontrivial_of_not_isZero`). That finiteness is the same categorical Jordan–Hölder input
as `clength_additive`; see the module doc. -/
theorem clength_eq_zero_iff {X : C} : clength X = 0 ↔ IsZero X := by
  refine ⟨?_, clength_eq_zero_of_isZero⟩
  -- Requires finiteness of `Order.height (⊤ : Subobject X)` in a finite abelian category.
  sorry

/-- A nonzero object has positive composition length.

`Subobject.nontrivial_of_not_isZero` gives `⊤ ≠ ⊥`, hence `¬ IsMin ⊤` and `Order.height ⊤ ≠ 0`;
positivity of `clength = (Order.height ⊤).toNat` additionally needs `Order.height ⊤ ≠ ⊤`, the
finiteness input discussed in the module doc. -/
theorem clength_pos_of_not_isZero {X : C} (h : ¬ IsZero X) : 0 < clength X := by
  -- Requires finiteness of `Order.height (⊤ : Subobject X)` in a finite abelian category.
  sorry

/-- **Additivity of composition length over short exact sequences** — the Krull–Schmidt crux.

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, the composition length is additive. This is the
categorical Jordan–Hölder content: it follows from wiring `JordanHolderLattice` onto `Subobject X`
(supplying `IsModularLattice (Subobject X)` and the categorical second isomorphism theorem), neither
of which is in Mathlib. Tracked as a follow-up issue; see the module doc. -/
theorem clength_additive {S : ShortComplex C} (hS : S.ShortExact) :
    clength S.X₂ = clength S.X₁ + clength S.X₃ := by
  sorry

/-- Composition length is additive over biproducts: `clength (Y ⊞ Z) = clength Y + clength Z`.

This follows from `clength_additive` applied to the split short exact sequence
`0 → Y → Y ⊞ Z → Z → 0` built from `biprod.inl` and `biprod.snd`. -/
theorem clength_biprod (Y Z : C) : clength (Y ⊞ Z) = clength Y + clength Z := by
  sorry

end Etingof
