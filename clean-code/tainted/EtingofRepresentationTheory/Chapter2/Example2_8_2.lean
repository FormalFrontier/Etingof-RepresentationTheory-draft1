import Mathlib.Combinatorics.Quiver.Basic

/-!
# Example 2.8.2: A Quiver

An example of a quiver with 4 vertices and 3 arrows:

```
• → • ← •
↑
•
```

## Mathlib correspondence

Mathlib has `Quiver` as a class. Concrete quiver examples can be constructed.
-/

/-- A concrete quiver with 4 vertices and 3 arrows. (Etingof Example 2.8.2) -/
instance Etingof.Example_2_8_2 : Quiver (Fin 4) where
  Hom a b :=
    -- Arrow 0 → 1, Arrow 2 → 1, Arrow 3 → 0
    if a = 0 ∧ b = 1 then Unit
    else if a = 2 ∧ b = 1 then Unit
    else if a = 3 ∧ b = 0 then Unit
    else Empty

namespace Etingof.Example_2_8_2

/-- The displayed horizontal arrow from the left vertex to the center vertex. -/
def edge01 : (0 : Fin 4) ⟶ (1 : Fin 4) := by
  change (if (0 : Fin 4) = 0 ∧ (1 : Fin 4) = 1 then Unit else
    if (0 : Fin 4) = 2 ∧ (1 : Fin 4) = 1 then Unit else
    if (0 : Fin 4) = 3 ∧ (1 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

/-- The displayed horizontal arrow from the right vertex to the center vertex. -/
def edge21 : (2 : Fin 4) ⟶ (1 : Fin 4) := by
  change (if (2 : Fin 4) = 0 ∧ (1 : Fin 4) = 1 then Unit else
    if (2 : Fin 4) = 2 ∧ (1 : Fin 4) = 1 then Unit else
    if (2 : Fin 4) = 3 ∧ (1 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

/-- The displayed vertical arrow from the lower vertex to the left vertex. -/
def edge30 : (3 : Fin 4) ⟶ (0 : Fin 4) := by
  change (if (3 : Fin 4) = 0 ∧ (0 : Fin 4) = 1 then Unit else
    if (3 : Fin 4) = 2 ∧ (0 : Fin 4) = 1 then Unit else
    if (3 : Fin 4) = 3 ∧ (0 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

end Etingof.Example_2_8_2

-- The leaf names follow Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace `Example_2_8_2`, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Example_2_8_2.edge01 Etingof.Example_2_8_2.edge21 Etingof.Example_2_8_2.edge30
