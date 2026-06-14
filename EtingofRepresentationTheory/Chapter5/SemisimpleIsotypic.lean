import Mathlib

/-!
# Submodules of finite direct sums of simple modules (generic isotypic extraction)

This file isolates a piece of pure module theory needed by the Schur-Weyl
decomposition of a polynomial `GL_N`-representation (Etingof §5.23, issue #2482).

The main result, `submodule_of_directSum_simple_iso_directSum`, says that a
submodule of a finite direct sum of simple `R`-modules `⨁ i, L i` is itself
isomorphic to a direct sum `⨁ j, L (f j)` of (copies of) those same simple
summands, for some index function `f : Fin n → ι`. From `f` one reads off, for
each `i`, the multiplicity `mult i = Nat.card {j // f j = i}` of `L i`.

The statement is generic: it has no Schur-Weyl or `GL_N` specifics in its
hypotheses, so it can be consumed by the #2482 assembly with
`R := MonoidAlgebra k (GL (Fin N) k)`, `L i := Representation.asModule (Lᵢ).ρ`.

## Proof outline

* A simple module is finitely generated (`module_finite_of_isSimpleModule`),
  hence so is the ambient `⨁ i, L i` over a `Fintype`.
* `⨁ i, L i` is semisimple and (being finite) of finite length, so it and any
  submodule of it are Noetherian; a semisimple Noetherian module is
  `Module.Finite`.
* `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp` decomposes the
  (transported) submodule into finitely many simple submodules `S j`.
* Each `S j`, being a simple submodule of `⨁ i, L i = sSup` of the coordinate
  lines `range (lof i)`, is isomorphic to one of those lines, i.e. to some
  `L i` (`Submodule.linearEquiv_of_le_sSup`). This produces the index function
  `f` and the per-factor isomorphisms `S j ≃ₗ L (f j)`.
* Reassembling via `DFinsupp.mapRange.linearEquiv` gives the result.
-/

open DirectSum

namespace Etingof.SemisimpleIsotypic

variable {R : Type*} [Ring R]

/-- A simple module is finitely generated (indeed cyclic): any nonzero element
spans the whole module. -/
theorem module_finite_of_isSimpleModule {M : Type*} [AddCommGroup M] [Module R M]
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

/-- A submodule of a finite direct sum of simple modules `⨁ i, L i` is isomorphic
to a direct sum `⨁ j, L (f j)` of copies of those simple summands, for some
`n : ℕ` and `f : Fin n → ι`. The multiplicity of `L i` is `Nat.card {j // f j = i}`.

This is the generic, Schur-Weyl-agnostic isotypic-extraction lemma required by
the §5.23 decomposition (#2482). -/
theorem submodule_of_directSum_simple_iso_directSum
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
  haveI hfin : ∀ i, Module.Finite R (L i) := fun i => module_finite_of_isSimpleModule
  -- The ambient direct sum is semisimple and finite, hence Noetherian.
  haveI : IsSemisimpleModule R (⨁ i, L i) :=
    inferInstanceAs (IsSemisimpleModule R (Π₀ i, L i))
  haveI : Module.Finite R (⨁ i, L i) := inferInstance
  haveI : IsNoetherian R (⨁ i, L i) := (IsSemisimpleModule.finite_tfae.out 0 1).mp ‹_›
  -- Transport `M` into the direct sum.
  set N : Submodule R (⨁ i, L i) := M.map (e : W →ₗ[R] ⨁ i, L i) with hN
  have eMN : M ≃ₗ[R] N := e.submoduleMap M
  haveI : IsNoetherian R N := inferInstance
  haveI : IsSemisimpleModule R N := inferInstance
  haveI : Module.Finite R N := (IsSemisimpleModule.finite_tfae.out 1 0).mp ‹_›
  -- Decompose `N` as a finite direct sum of simple submodules.
  obtain ⟨n, S, eN, hSsimple⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R N
  -- The coordinate lines `range (lof i)` of the ambient direct sum.
  set cs : Set (Submodule R (⨁ i, L i)) :=
    Set.range (fun i => LinearMap.range (DirectSum.lof R ι L i)) with hcs
  have hlof_inj : ∀ i, Function.Injective (DirectSum.lof R ι L i) := fun i =>
    Function.LeftInverse.injective (g := DirectSum.component R ι L i)
      (fun b => DirectSum.component.lof_self R i b)
  -- Each coordinate line is simple (isomorphic to `L i`).
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (⨁ i, L i)) := by
    rintro ⟨m, i, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj i)).symm
  haveI := hcs_simple
  -- The coordinate lines span the whole module.
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]
    exact DFinsupp.iSup_range_lsingle
  -- Match each simple factor `S j` to one of the `L i`.
  have hmatch : ∀ j, ∃ i, Nonempty (↥(S j) ≃ₗ[R] L i) := by
    intro j
    haveI : IsSimpleModule R (S j) := hSsimple j
    -- Realize `S j` as a simple submodule `T` of the ambient direct sum.
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
  -- Reassemble: `M ≃ N ≃ ⨁ j, S j ≃ ⨁ j, L (f j)`.
  let g : ∀ j, (↥(S j)) ≃ₗ[R] L (f j) := fun j => (hf j).some
  exact eMN.trans (eN.trans (DFinsupp.mapRange.linearEquiv g))

end Etingof.SemisimpleIsotypic
