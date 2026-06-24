import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_4

/-!
# Discussion: quiver representations vs. path-algebra modules

The discussion following Definition 2.8.4 in Etingof asserts that a representation of a
quiver `Q` is "the same thing" as a representation (module) of its path algebra `P_Q`, with
mutually inverse assignments `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ`, giving a bijection between
isomorphism classes.

This file develops the algebraic foundation that both directions of that bijection rest on:
the trivial paths `pᵢ = ofPath ⟨i, i, nil⟩` form a family of **orthogonal idempotents**
summing (for a finite vertex set) to `1`, and they **absorb** an oriented path on the
correct side. Concretely, for an oriented path `a : x ⟶* y`,

* `pₓ · a = a` and `pₖ · a = 0` for `k ≠ x` (the source idempotent acts on the left), and
* `a · p_y = a` and `a · pₖ = 0` for `k ≠ y` (the target idempotent acts on the right).

These are precisely the relations that make `pᵢ V` the `i`-th vertex space and that pin down
which vertex space a single-arrow path maps out of and into.

## Convention / direction note

`Definition2_8_4` builds `P_Q` with Mathlib's **source-to-target** concatenation
(`comp x y` is defined when `target x = source y`, giving a path `source x ⟶* target y`).
This is the *opposite* of Etingof's body-text reading `ab = "first b then a"`; the two
conventions produce mutually opposite algebras. The absorption laws below are stated for the
source-to-target algebra actually constructed.

A consequence worth flagging for the full bijection (tracked in the
`Discussion_quiver_rep_bijection` work item): under this convention, for an arrow
`e : i ⟶ j` the basis element `aₑ = ofPath ⟨i, j, e.toPath⟩` satisfies `pᵢ · aₑ = aₑ` and
`aₑ · p_j = aₑ`, so in a *left* `P_Q`-module the operator `v ↦ aₑ • v` carries `p_j V` into
`pᵢ V`, i.e. it points `Vⱼ → Vᵢ`. Matching this against `Etingof.QuiverRepresentation` (where
an arrow `i ⟶ j` carries `Vᵢ → Vⱼ`) therefore requires either the opposite algebra, right
modules, or `Qᵒᵖ`; that modelling choice is left to the bijection construction itself.
-/

namespace Etingof.PathAlgebra

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The trivial path idempotent `pᵢ` at a vertex `i`: the basis element of `PathAlgebra k Q`
indexed by the empty (length-zero) path at `i`. -/
noncomputable def trivialPath (i : Q) : PathAlgebra k Q :=
  ofPath ⟨i, i, Quiver.Path.nil⟩

theorem trivialPath_def (i : Q) :
    (trivialPath i : PathAlgebra k Q) = Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1 :=
  rfl

/-- Left absorption: multiplying a basis path `a : x ⟶* y` on the left by the trivial path
`pᵢ` returns `a` when `i` is its source, and `0` otherwise. -/
theorem trivialPath_mul_ofPath (i a b : Q) (p : Quiver.Path a b) :
    (trivialPath i : PathAlgebra k Q) * ofPath ⟨a, b, p⟩
      = if i = a then ofPath ⟨a, b, p⟩ else 0 := by
  simp only [trivialPath, ofPath, single_mul_single, one_mul, one_smul, compSingle_nil_left]

/-- Right absorption: multiplying a basis path `a : x ⟶* y` on the right by the trivial path
`pᵢ` returns `a` when `i` is its target, and `0` otherwise. -/
theorem ofPath_mul_trivialPath (a b i : Q) (p : Quiver.Path a b) :
    (ofPath ⟨a, b, p⟩ : PathAlgebra k Q) * trivialPath i
      = if b = i then ofPath ⟨a, b, p⟩ else 0 := by
  simp only [trivialPath, ofPath, single_mul_single, mul_one, one_smul, compSingle_nil_right]

/-- The trivial paths are idempotents: `pᵢ · pᵢ = pᵢ`. -/
theorem trivialPath_mul_self (i : Q) :
    (trivialPath i : PathAlgebra k Q) * trivialPath i = trivialPath i := by
  have h := trivialPath_mul_ofPath (k := k) i i i Quiver.Path.nil
  rw [if_pos rfl] at h
  exact h

/-- The trivial paths are orthogonal: `pᵢ · pⱼ = 0` when `i ≠ j`. -/
theorem trivialPath_mul_of_ne {i j : Q} (h : i ≠ j) :
    (trivialPath i : PathAlgebra k Q) * trivialPath j = 0 := by
  have h2 := trivialPath_mul_ofPath (k := k) i j j Quiver.Path.nil
  rw [if_neg h] at h2
  exact h2

/-- Orthogonal-idempotent product law in one statement: `pᵢ · pⱼ = pᵢ` if `i = j`, else `0`. -/
theorem trivialPath_mul_trivialPath (i j : Q) :
    (trivialPath i : PathAlgebra k Q) * trivialPath j = if i = j then trivialPath i else 0 := by
  by_cases h : i = j
  · subst h; rw [trivialPath_mul_self, if_pos rfl]
  · rw [trivialPath_mul_of_ne h, if_neg h]

/-- **Remark 2.8.5, restated.** For a finite vertex set, the trivial-path idempotents sum to the
unit: `∑ᵢ pᵢ = 1`. (Restatement of `sum_trivialPaths_eq_one` in terms of `trivialPath`.) -/
theorem sum_trivialPath [Fintype Q] : (∑ i, trivialPath i : PathAlgebra k Q) = 1 := by
  simp only [trivialPath]
  exact sum_trivialPaths_eq_one k Q

end Etingof.PathAlgebra
