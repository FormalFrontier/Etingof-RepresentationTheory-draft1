/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Equivalence of module composition series -/

namespace RepresentationTheory.Algebra.Module.CompositionSeriesEquivalence

/-- The module associated to an indexed factor of a composition series. -/
@[source_ref "Chapter3/Theorem3.7.1" (role := supporting)]
noncomputable abbrev factorModule {A V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    (s : CompositionSeries (Submodule A V)) (i : Fin s.length) : Type _ :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

/-- Two composition series with bottom head and top last term are equivalent. -/
@[source_ref "Chapter3/Theorem3.7.1" (role := supporting)]
theorem equivalent (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.Equivalent s₂ :=
  CompositionSeries.jordan_holder s₁ s₂
    (by rw [hs₁_bot, hs₂_bot]) (by rw [hs₁_top, hs₂_top])

/-- The displayed composition series have factor modules equivalent after a permutation. -/
@[source_ref "Chapter3/Theorem3.7.1" (role := primary)]
theorem exists_permutation_factorEquiv (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    ∃ σ : Fin s₁.length ≃ Fin s₂.length, ∀ i : Fin s₁.length,
      Nonempty (factorModule s₁ i ≃ₗ[A] factorModule s₂ (σ i)) :=
  equivalent A V s₁ s₂ hs₁_bot hs₁_top hs₂_bot hs₂_top

/-- Two composition series with bottom head and top last term have equal lengths. -/
@[source_ref "Chapter3/Theorem3.7.1" (role := primary),
  source_ref "Chapter3/Discussion_after_Theorem3.7.1" (role := primary)]
theorem length_eq (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.length = s₂.length :=
  (equivalent A V s₁ s₂ hs₁_bot hs₁_top hs₂_bot hs₂_top).length_eq

end RepresentationTheory.Algebra.Module.CompositionSeriesEquivalence
