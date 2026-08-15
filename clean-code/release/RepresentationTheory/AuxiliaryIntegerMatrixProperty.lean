/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary Integer Matrix Property
-/

namespace RepresentationTheory.AuxiliaryIntegerMatrixProperty

/-- An auxiliary property of an integer matrix indexed by a finite type. -/
@[source_ref "Chapter2/Theorem2.1.2/Derived4" (role := primary),
  source_ref "Chapter6/Definition6.1.4" (role := supporting)]
def IsAuxiliaryMatrix (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  adj.IsSymm ∧
  (∀ i, adj i i = 0) ∧
  (∀ i j, adj i j = 0 ∨ adj i j = 1) ∧
  (∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) ∧
  (∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))

end RepresentationTheory.AuxiliaryIntegerMatrixProperty
