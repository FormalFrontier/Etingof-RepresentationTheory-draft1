import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_FieldGeneral
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_StrictBound

/-!
# Exercise 4.2.3: the strict modular counting drop

This file proves the full statement of **Exercise 4.2.3**:

  `Etingof.Exercise4_2_3`: if `|G| = 0` in `k` (the characteristic divides `|G|`), then
  `Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G)`.

It depends on `Exercise4_2_3_FieldGeneral.lean` (the split-field independence machinery and
base-change monotonicity) and `Exercise4_2_3_StrictBound.lean` (the strict cocenter counting
bound). The `Exercise4_2_3` statement is placed here rather than in `Exercise4_2_3.lean` because
both of those files import `Exercise4_2_3.lean`.

## The strict split-field lemma

Over an algebraically closed field `K` with `|G| = 0` in `K`, the same linearly independent
family of `n = #(simple K[G]-modules)` block trace forms that gives the split-field `≤` bound
(`traceFormQ_Std_linearIndependent`) also gives the strict cocenter bound
`CocenterMonoidAlgebra.card_lt_conjClasses_of_traceForm_linearIndependent` (each trace form
annihilates the nonzero central nilpotent `P̄ = ∑_g g` in the modular case), yielding the strict
`n < Nat.card (ConjClasses G)`.

## Base change to the algebraic closure

The strict inequality over an arbitrary field then follows by `lt_of_le_of_lt`, with
`K = AlgebraicClosure k`:
```
Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G) < Nat.card (ConjClasses G).
```
- the `≤` is `natCard_irrepClasses_le_of_ringHom_field` (base-change monotonicity);
- the `<` is the strict split-field lemma over the algebraically closed `K` (with `|G| = 0` in `K`,
  transported from `|G| = 0` in `k` via `map_natCast (algebraMap k K)`).

The right-hand side `Nat.card (ConjClasses G)` is field-independent, so no transfer is needed there.
-/

open Etingof.SplitSimples Etingof.CocenterMonoidAlgebra

namespace Etingof

universe u v

/-- **Strict split-field bound (modular case).** Over an algebraically closed field `K` in which
`|G| = 0`, the number of isomorphism classes of irreducible representations of a finite group `G`
is strictly less than the number of conjugacy classes of `G`.

The proof reuses the split-field enumeration: `K[G]/rad ≅ ∏ Matrix d_i(K)` bundled as `SplitData`
(`exists_splitSimples_count`), so `#(simple K[G]-modules) = n`, and the `n` block trace forms
`τ_{Std i}` are linearly independent (`traceFormQ_Std_linearIndependent`). Each `Std i` is a simple
`K[G]`-module (`isSimpleModule_Std`), so in the modular case (`|G| = 0` in `K`) the strict cocenter
bound `card_lt_conjClasses_of_traceForm_linearIndependent` applies and gives `n < #ConjClasses`. -/
theorem natCard_irrepClasses_lt_conjClasses_of_isAlgClosed
    (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G]
    (hcard : (Fintype.card G : K) = 0) :
    Nat.card (IrrepClasses K G) < Nat.card (ConjClasses G) := by
  classical
  obtain ⟨D, hD⟩ := exists_splitSimples_count K G
  rw [card_irrepClasses_eq_card_simpleModuleClasses K G, hD]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra K G) (D.Std i) := fun i => D.isSimpleModule_Std i
  have hlt := card_lt_conjClasses_of_traceForm_linearIndependent (S := fun i => D.Std i)
    hcard (traceFormQ_Std_linearIndependent D)
  simpa using hlt

/-- **Exercise 4.2.3.** If `|G| = 0` in `k` (the characteristic of `k` divides the order of the
finite group `G`), then the number of isomorphism classes of irreducible representations of `G`
over `k` is strictly less than the number of conjugacy classes of `G`.

Proved by base change to the algebraic closure `K = AlgebraicClosure k`: base-change
monotonicity of the simple count under `k → K` (`natCard_irrepClasses_le_of_ringHom_field`)
followed by the strict split-field bound over the algebraically closed `K`
(`natCard_irrepClasses_lt_conjClasses_of_isAlgClosed`, with `|G| = 0` in `K` transported from
`|G| = 0` in `k`). The right-hand side `Nat.card (ConjClasses G)` is field-independent, so the two
bounds compose by `lt_of_le_of_lt`. -/
theorem Exercise4_2_3 (k G : Type u) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G) := by
  -- Transport `|G| = 0` from `k` to its algebraic closure along `algebraMap`.
  have hK : (Fintype.card G : AlgebraicClosure k) = 0 := by
    rw [← map_natCast (algebraMap k (AlgebraicClosure k)) (Fintype.card G), h, map_zero]
  exact lt_of_le_of_lt
    (natCard_irrepClasses_le_of_ringHom_field k (AlgebraicClosure k) G)
    (natCard_irrepClasses_lt_conjClasses_of_isAlgClosed (AlgebraicClosure k) G hK)

end Etingof
