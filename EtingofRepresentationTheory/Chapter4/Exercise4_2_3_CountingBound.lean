import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_Cocenter

/-!
# The counting bound from linear independence of cocenter trace forms (Exercise 4.2.3)

`Exercise4_2_3_Cocenter.lean` builds the cocenter `C = k[G] / [k[G], k[G]]`, proves
`finrank k C = Nat.card (ConjClasses G)`, and constructs the cocenter trace functionals
`traceFormQ k M : C →ₗ[k] k` of finite-dimensional `k[G]`-modules.

This file supplies the packaging step that turns linear independence of a family of such
functionals into the cardinality bound: a linearly independent family of `n` functionals on
`C` forces
```
  n ≤ finrank k (C →ₗ[k] k) = finrank k C = Nat.card (ConjClasses G).
```
The dual `C →ₗ[k] k` (`Module.Dual k C`) has the same finite dimension as `C`
(`Subspace.dual_finrank_eq`), and a linearly independent family in a finite-dimensional space
is bounded by that dimension (`LinearIndependent.fintype_card_le_finrank`).

The result is purely linear-algebraic and holds over an arbitrary field (only `[Field k]`); it
does not itself prove that the trace forms of distinct simple modules are independent. That is
the remaining, field-sensitive content of Exercise 4.2.3's counting half: it can fail over a
non-splitting field and is handled via base change to a splitting field. Once such a linear
independence result is available, it plugs directly into
`card_le_conjClasses_of_traceForm_linearIndependent` to yield
`#(simple k[G]-modules) ≤ Nat.card (ConjClasses G)`.
-/

open MonoidAlgebra

-- `[Fintype G]`/`[DecidableEq G]` are used at proof time (to invoke
-- `finrank_cocenter_eq_card_conjClasses`) but not in the statement types.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Etingof

namespace CocenterMonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

/-- **Packaging bound (Exercise 4.2.3, counting half).** A `Fintype`-indexed family of
functionals on the cocenter `C = k[G] / [k[G], k[G]]` that is `LinearIndependent` over `k` has
at most `Nat.card (ConjClasses G)` members. This is the linear-algebraic core that converts any
future linear-independence statement about trace forms into the actual counting bound.

Field-general: only `[Field k]`, no `IsAlgClosed`, no invertibility of `|G|`. -/
theorem card_le_conjClasses_of_linearIndependent
    {ι : Type*} [Fintype ι] {f : ι → (Cocenter k G →ₗ[k] k)}
    (hf : LinearIndependent k f) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  haveI : Module.Finite k (Cocenter k G →ₗ[k] k) := inferInstance
  have h1 : Fintype.card ι ≤ Module.finrank k (Cocenter k G →ₗ[k] k) :=
    hf.fintype_card_le_finrank
  rwa [Module.finrank_linearMap_self, finrank_cocenter_eq_card_conjClasses] at h1

/-- `Nat.card` form of `card_le_conjClasses_of_linearIndependent`, for indexing types that are
only known to be `Finite`. -/
theorem natCard_le_conjClasses_of_linearIndependent
    {ι : Type*} [Finite ι] {f : ι → (Cocenter k G →ₗ[k] k)}
    (hf : LinearIndependent k f) :
    Nat.card ι ≤ Nat.card (ConjClasses G) := by
  cases nonempty_fintype ι
  rw [Nat.card_eq_fintype_card]
  exact card_le_conjClasses_of_linearIndependent hf

/-- **Counting bound from independent trace forms.** If the cocenter trace forms
`τ_{S i} = traceFormQ k (S i)` of a finite family of finite-dimensional `k[G]`-modules `S i`
are linearly independent over `k`, then the family has at most `Nat.card (ConjClasses G)`
members. Specialising to a family of pairwise non-isomorphic simple modules (once their trace
forms are shown independent) yields `#(simple k[G]-modules) ≤ Nat.card (ConjClasses G)`.

This is the packaging theorem used to derive the counting bound. -/
theorem card_le_conjClasses_of_traceForm_linearIndependent
    {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module (MonoidAlgebra k G) (S i)] [∀ i, IsScalarTower k (MonoidAlgebra k G) (S i)]
    [∀ i, Module.Finite k (S i)]
    (h : LinearIndependent k (fun i => (traceFormQ k (S i) : Cocenter k G →ₗ[k] k))) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) :=
  card_le_conjClasses_of_linearIndependent h

end CocenterMonoidAlgebra

end Etingof
