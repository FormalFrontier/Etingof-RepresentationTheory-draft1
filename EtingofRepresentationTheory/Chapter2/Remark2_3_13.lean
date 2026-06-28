import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Remark 2.3.13: 1-dimensional representations are automatically irreducible

Etingof remarks that a 1-dimensional representation of *any* algebra is automatically
irreducible.

A representation `V` of an algebra `A` over a field `k` is irreducible exactly when
`IsSimpleModule A V` holds (Definition 2.3.5). If `V` is 1-dimensional as a `k`-vector
space, then its only `k`-subspaces are `0` and `V`. Every `A`-subrepresentation is in
particular a `k`-subspace (the `k`-action factors through `A` via the scalar tower), so the
only subrepresentations are `0` and `V`, and `V ≠ 0`. Hence `V` is irreducible.

## Mathlib correspondence

Over a field, `isSimpleModule_iff_finrank_eq_one` gives `IsSimpleModule k V` from
`finrank k V = 1`. We then transport simplicity along restriction of scalars: every
`A`-submodule restricts to a `k`-submodule with the same carrier, and
`Submodule.restrictScalars_eq_bot_iff` / `Submodule.restrictScalars_eq_top_iff` show this
restriction is injective on `⊥` and `⊤`.
-/

namespace Etingof

/-- Remark 2.3.13: a 1-dimensional representation of any algebra is automatically irreducible.
If a representation `V` of an algebra `A` over a field `k` has dimension `1` as a `k`-vector
space, then `V` is irreducible, i.e. `IsSimpleModule A V`. -/
theorem Remark_2_3_13
    {k : Type*} [Field k]
    {A : Type*} [Ring A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    (h : Module.finrank k V = 1) :
    IsSimpleModule A V := by
  haveI hk : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  haveI : Nontrivial V := IsSimpleModule.nontrivial k V
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases eq_bot_or_eq_top (W.restrictScalars k) with hW | hW
  · exact Or.inl (by simpa using hW)
  · exact Or.inr (by simpa using hW)

end Etingof
