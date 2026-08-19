/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteLength
import RepresentationTheory.Module.CompositionData
import RepresentationTheory.Alignment.Attribute

/-! # Filtrations of modules -/

namespace RepresentationTheory.Algebra.Module.Filtrations

/-- A finite-dimensional module admits a relation series with bottom head and top last term. -/
@[source_ref "Chapter3/Lemma3.4.2/Derived2" (role := supporting),
  source_ref "Chapter3/Theorem3.7.1/Derived17" (role := supporting)]
theorem exists_relSeries_bot_top (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (s : CompositionSeries (Submodule A V)), s.head = ⊥ ∧ s.last = ⊤ := by
  have : IsNoetherian A V := isNoetherian_of_tower k (inferInstance : IsNoetherian k V)
  have : IsArtinian A V := isArtinian_of_tower k (inferInstance : IsArtinian k V)
  exact exists_compositionSeries_of_isNoetherian_isArtinian A V

/-- A finite-dimensional module admits a filtration whose displayed successive quotients are simple modules. -/
@[source_ref "Chapter3/Lemma3.4.2" (role := supporting),
  source_ref "Chapter3/Introduction_to_3.4" (role := supporting)]
theorem exists_filtration_simple_quotients
    (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ F : RepresentationTheory.Module.CompositionData.ModuleCompositionData A V,
      ∀ i : Fin F.toRelSeries.length,
      IsSimpleModule A
        (F.toRelSeries (Fin.succ i) ⧸
          Submodule.comap (F.toRelSeries (Fin.succ i)).subtype
            (F.toRelSeries (Fin.castSucc i))) := by
  obtain ⟨s, hs₀, hsₙ⟩ := exists_relSeries_bot_top k A V
  let F : RepresentationTheory.Module.CompositionData.ModuleCompositionData A V :=
    { toRelSeries := s.ofLE fun p h ↦
        show p.1 < p.2 from JordanHolderLattice.lt_of_isMaximal h
      toRelSeries_head := hs₀
      toRelSeries_last := hsₙ }
  refine ⟨F, ?_⟩
  intro i
  change IsSimpleModule A
    (s (Fin.succ i) ⧸
      Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
  exact (covBy_iff_quot_is_simple (le_of_lt (s.lt_succ i))).mp (s.step i)

end RepresentationTheory.Algebra.Module.Filtrations
