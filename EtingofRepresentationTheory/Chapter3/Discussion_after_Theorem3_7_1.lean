import Mathlib.RingTheory.Length

/-!
# Discussion after Theorem 3.7.1: Length of a representation

The Jordan-Hölder theorem shows that the number `n` of terms in a filtration of `V` with
irreducible successive quotients does not depend on the choice of filtration; this number
is the **length** of `V`. The discussion claims:

> It is easy to see that `n` is also the maximal length of a filtration of `V` in which all
> the inclusions are strict.

We formalize this. A filtration with strict inclusions is an `LTSeries (Submodule A V)` (a
chain `U₀ < U₁ < ⋯ < U_m`); its "length" is `m` (the number of inclusions). A composition
series `s` (a chain with each step a covering relation `⋖`, i.e. simple quotients) from `⊥`
to `⊤` has `s.length = n`. We show `n` is the greatest length attained by any strict
filtration:

* the composition series itself is a strict filtration of length `n` (since `⋖` implies
  `<`), so the value `n` is attained;
* every strict filtration has length `≤ n`, because the supremum of strict-chain lengths is
  the Krull dimension of the submodule lattice, which equals `Module.length A V = n`.

This uses `Module.length_compositionSeries` (the composition-series length equals the
module length) and `Order.LTSeries.length_le_krullDim` (`Module.length` is the supremum of
strict-chain lengths).
-/

open Order

namespace Etingof

variable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] [Module A V]

/-- The length `n` of `V` (the common length of any composition series from `⊥` to `⊤`) is
the maximal length of a strictly increasing filtration of `V`. Etingof, discussion after
Theorem 3.7.1.

Here a strictly increasing filtration is an `LTSeries (Submodule A V)`, and its length is
the number of strict inclusions. `IsGreatest` packages the two facts: the value `s.length`
is attained by some strict filtration, and it is an upper bound for all of them. -/
theorem jordanHolder_length_isGreatest_strict
    (s : CompositionSeries (Submodule A V)) (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    IsGreatest (Set.range fun l : LTSeries (Submodule A V) => (l.length : ℕ∞))
      (s.length : ℕ∞) := by
  constructor
  · -- The composition series is itself a strict filtration of length `s.length`.
    refine ⟨s.map ⟨id, fun h => h.1⟩, ?_⟩
    simp only [RelSeries.map_length]
  · -- Every strict filtration has length ≤ s.length = Module.length A V.
    rintro _ ⟨l, rfl⟩
    have hkrull : (l.length : ℕ∞) ≤ Module.length A V := by
      have h1 := LTSeries.length_le_krullDim l
      rw [← Module.coe_length] at h1
      exact_mod_cast h1
    rwa [Module.length_compositionSeries s hbot htop]

end Etingof
