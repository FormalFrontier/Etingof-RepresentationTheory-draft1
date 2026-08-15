/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib

open DirectSum

namespace RepresentationTheory.Algebra.Module.Simple

variable {R : Type*} [Ring R]

/-- A simple module is finitely generated. -/
theorem IsSimpleModule.finite {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.Finite R M := by
  haveI := IsSimpleModule.nontrivial R M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hmem : x ∈ Submodule.span R {x} := Submodule.mem_span_singleton_self x
  have hspan : Submodule.span R {x} = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span R {x}) with h | h
    · rw [h, Submodule.mem_bot] at hmem; exact absurd hmem hx
    · exact h
  rw [Module.finite_def, ← hspan]
  exact Submodule.fg_span (Set.finite_singleton x)

/-- A submodule of a module linearly equivalent to a finite direct sum of simple modules is linearly equivalent to a finite direct sum of selected summand types. -/
theorem Submodule.nonempty_linearEquiv_directSumFin_of_simple
    {W : Type*} [AddCommGroup W] [Module R W]
    {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
    (hsimp : ∀ i, IsSimpleModule R (L i))
    (e : W ≃ₗ[R] DirectSum ι L)
    (M : Submodule R W) :
    ∃ (n : ℕ) (f : Fin n → ι),
      Nonempty (M ≃ₗ[R] DirectSum (Fin n) (fun j => L (f j))) := by
  classical
  haveI hsimp' : ∀ i, IsSimpleModule R (L i) := hsimp
  haveI hfin : ∀ i, Module.Finite R (L i) := fun i => IsSimpleModule.finite
  haveI : IsSemisimpleModule R (⨁ i, L i) :=
    inferInstanceAs (IsSemisimpleModule R (Π₀ i, L i))
  haveI : Module.Finite R (⨁ i, L i) := inferInstance
  haveI : IsNoetherian R (⨁ i, L i) := (IsSemisimpleModule.finite_tfae.out 0 1).mp ‹_›
  set N : Submodule R (⨁ i, L i) := M.map (e : W →ₗ[R] ⨁ i, L i) with hN
  have eMN : M ≃ₗ[R] N := e.submoduleMap M
  haveI : IsNoetherian R N := inferInstance
  haveI : IsSemisimpleModule R N := inferInstance
  haveI : Module.Finite R N := (IsSemisimpleModule.finite_tfae.out 1 0).mp ‹_›
  obtain ⟨n, S, eN, hSsimple⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R N
  set cs : Set (Submodule R (⨁ i, L i)) :=
    Set.range (fun i => LinearMap.range (DirectSum.lof R ι L i)) with hcs
  have hlof_inj : ∀ i, Function.Injective (DirectSum.lof R ι L i) := fun i =>
    Function.LeftInverse.injective (g := DirectSum.component R ι L i)
      (fun b => DirectSum.component.lof_self R i b)
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (⨁ i, L i)) := by
    rintro ⟨m, i, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj i)).symm
  haveI := hcs_simple
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]
    exact DFinsupp.iSup_range_lsingle
  have hmatch : ∀ j, ∃ i, Nonempty (↥(S j) ≃ₗ[R] L i) := by
    intro j
    haveI : IsSimpleModule R (S j) := hSsimple j
    set T : Submodule R (⨁ i, L i) := (S j).map N.subtype with hT
    have eST : (↥(S j)) ≃ₗ[R] T :=
      Submodule.equivMapOfInjective _ N.injective_subtype (S j)
    haveI : IsSimpleModule R T := (LinearEquiv.isSimpleModule_iff eST).mp (hSsimple j)
    have hTle : T ≤ sSup cs := by rw [hcs_top]; exact le_top
    obtain ⟨m, hm, ⟨e'⟩⟩ := T.linearEquiv_of_le_sSup cs hTle
    obtain ⟨i, rfl⟩ := hm
    exact ⟨i, ⟨eST.trans (e'.trans (LinearEquiv.ofInjective _ (hlof_inj i)).symm)⟩⟩
  obtain ⟨f, hf⟩ := Classical.skolem.mp hmatch
  refine ⟨n, f, ⟨?_⟩⟩
  let g : ∀ j, (↥(S j)) ≃ₗ[R] L (f j) := fun j => (hf j).some
  exact eMN.trans (eN.trans (DFinsupp.mapRange.linearEquiv g))

end RepresentationTheory.Algebra.Module.Simple
