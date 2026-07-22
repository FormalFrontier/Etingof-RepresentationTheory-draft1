import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Theorem 3.7.1: Jordan-Hölder Theorem

Let V be a finite dimensional representation of A, and let
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V, 0 = V'₀ ⊂ ⋯ ⊂ V'ₘ = V
be filtrations of V such that the representations Wᵢ := Vᵢ/Vᵢ₋₁ and W'ᵢ := V'ᵢ/V'ᵢ₋₁
are irreducible for all i. Then n = m, and there exists a permutation σ of 1, …, n such
that W_{σ(i)} is isomorphic to W'ᵢ.

Two proofs are given:
- First proof (char 0): uses linear independence of characters (Theorem 3.6.2).
- Second proof (general): induction on dim V, analyzing the cases W₁ = W'₁ and W₁ ≠ W'₁.

## Mathlib correspondence

`JordanHolderLattice` and `CompositionSeries` provide the framework. Mathlib's
`JordanHolderModule.instJordanHolderLattice` gives a `JordanHolderLattice` instance for
`Submodule R M`, where `IsMaximal` is the covering relation `⋖` (equivalent to successive
quotients being simple modules). The theorem `CompositionSeries.jordan_holder` then gives
both equal lengths and a permutation of composition factors.
-/

/-- The `i`-th composition factor of a composition series `s` of submodules of `V`:
the quotient `s(i+1) / s(i)` of two consecutive (covering) terms. This is the module
`Wᵢ := Vᵢ/Vᵢ₋₁` of Etingof's filtration, realized as a quotient of the submodule
`s(i+1)` by the image of `s(i)` inside it.

`Mathlib`'s `JordanHolderModule.instJordanHolderLattice` uses exactly this quotient as the
`Iso` relation on covering pairs, so the Jordan-Hölder equivalence
(`CompositionSeries.jordan_holder`) is phrased in terms of `Nonempty (factor _ ≃ₗ factor _)`. -/
noncomputable abbrev Etingof.compositionFactor {A V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    (s : CompositionSeries (Submodule A V)) (i : Fin s.length) : Type _ :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

/-- The **Jordan-Hölder theorem** for modules, full statement (Etingof Theorem 3.7.1):
any two composition series of the same module (from ⊥ to ⊤) are *equivalent* — there is a
bijection `σ` between their index sets such that the `i`-th composition factor of the
first is linearly isomorphic to the `σ i`-th composition factor of the second.

A `CompositionSeries (Submodule A V)` is a `RelSeries` where consecutive submodules are
related by `⋖` (the covering relation), which is equivalent to requiring successive
quotients to be simple (irreducible) modules. -/
theorem Etingof.jordan_holder_equivalent (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.Equivalent s₂ :=
  CompositionSeries.jordan_holder s₁ s₂
    (by rw [hs₁_bot, hs₂_bot]) (by rw [hs₁_top, hs₂_top])

/-- The factor-isomorphism half of Jordan-Hölder (Etingof Theorem 3.7.1): there exists a
permutation `σ` of the index set such that the `i`-th composition factor `Wᵢ` of `s₁` is
isomorphic to the `σ i`-th composition factor `W'_{σ i}` of `s₂`. This is the substance of
the theorem — "there exists a permutation σ such that `W_{σ(i)}` is isomorphic to `W'ᵢ`". -/
theorem Etingof.jordan_holder_factors (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    ∃ σ : Fin s₁.length ≃ Fin s₂.length, ∀ i : Fin s₁.length,
      Nonempty (Etingof.compositionFactor s₁ i ≃ₗ[A] Etingof.compositionFactor s₂ (σ i)) :=
  Etingof.jordan_holder_equivalent A V s₁ s₂ hs₁_bot hs₁_top hs₂_bot hs₂_top

/-- The Jordan-Hölder theorem for modules, length half (Etingof Theorem 3.7.1): any two
composition series of the same module (from ⊥ to ⊤) have the same length, so `n = m`.
This follows from the full equivalence `Etingof.jordan_holder_equivalent`. -/
theorem Etingof.jordan_holder (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.length = s₂.length :=
  (Etingof.jordan_holder_equivalent A V s₁ s₂ hs₁_bot hs₁_top hs₂_bot hs₂_top).length_eq
