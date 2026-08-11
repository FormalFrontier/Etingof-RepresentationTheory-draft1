import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteLength
import EtingofRepresentationTheory.Chapter3.Definition3_4_1

/-!
# Lemma 3.4.2: Existence of Filtration with Irreducible Successive Quotients

Any finite dimensional representation V of an algebra A admits a finite filtration
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V such that the successive quotients Vᵢ/Vᵢ₋₁ are irreducible.

The proof is by induction on dim(V): pick an irreducible subrepresentation V₁ ⊂ V,
apply the induction hypothesis to V/V₁.
-/

/-- Every finite dimensional representation admits a composition series (filtration with
irreducible successive quotients). Etingof Lemma 3.4.2. -/
theorem Etingof.exists_composition_series (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (s : CompositionSeries (Submodule A V)), s.head = ⊥ ∧ s.last = ⊤ := by
  have : IsNoetherian A V := isNoetherian_of_tower k (inferInstance : IsNoetherian k V)
  have : IsArtinian A V := isArtinian_of_tower k (inferInstance : IsArtinian k V)
  exact exists_compositionSeries_of_isNoetherian_isArtinian A V

/-- Every finite-dimensional representation has a filtration whose successive quotients are
irreducible. This is the statement of Etingof Lemma 3.4.2 expressed using
`Etingof.Filtration`; the quotient attached to adjacent terms `Vᵢ < Vᵢ₊₁` is represented as
`Vᵢ₊₁ ⧸ (Vᵢ.comap Vᵢ₊₁.subtype)`. -/
theorem Etingof.exists_filtration_with_irreducible_quotients
    (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ F : Etingof.Filtration A V, ∀ i : Fin F.chain.length,
      IsSimpleModule A
        (F.chain (Fin.succ i) ⧸
          Submodule.comap (F.chain (Fin.succ i)).subtype (F.chain (Fin.castSucc i))) := by
  obtain ⟨s, hs₀, hsₙ⟩ := Etingof.exists_composition_series k A V
  let F : Etingof.Filtration A V :=
    { chain := s.ofLE fun p h ↦
        show p.1 < p.2 from JordanHolderLattice.lt_of_isMaximal h
      head_eq_bot := hs₀
      last_eq_top := hsₙ }
  refine ⟨F, ?_⟩
  intro i
  change IsSimpleModule A
    (s (Fin.succ i) ⧸
      Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
  exact (covBy_iff_quot_is_simple (le_of_lt (s.lt_succ i))).mp (s.step i)
