import EtingofRepresentationTheory.Infrastructure.SimpleModuleFamily

/-!
# Tests for the finite family of simple modules

We exercise `Etingof.exists_simpleModule_family` and
`Etingof.exists_fgModuleCat_simple_family` on the simplest case `A = k`, a field, whose only
simple module (up to isomorphism) is `k` itself.
-/

open CategoryTheory Etingof

-- The complete family exists for `A = k` and covers every simple `k`-module.
example (k : Type) [Field k]
    (M : Type) [AddCommGroup M] [Module k M] [IsSimpleModule k M] :
    ∃ (n : ℕ) (S : Fin n → Submodule k (k ⧸ Ring.jacobson k)) (i : Fin n),
      Nonempty (M ≃ₗ[k] ↥(S i)) := by
  obtain ⟨n, S, _hfin, _hsimple, hcomplete⟩ := exists_simpleModule_family k k
  obtain ⟨i, hi⟩ := hcomplete M
  exact ⟨n, S, i, hi⟩

-- The categorical family exists for `FGModuleCat k` and covers every simple object.
example (k : Type) [Field k] (X : FGModuleCat.{0} k) (hX : Simple X) :
    ∃ (ι : Type) (_ : Fintype ι) (V : ι → FGModuleCat.{0} k) (i : ι),
      (∀ j, Simple (V j)) ∧ Nonempty (X ≅ V i) := by
  obtain ⟨ι, _, V, hsimple, hcomplete⟩ := exists_fgModuleCat_simple_family k k
  obtain ⟨i, hi⟩ := hcomplete X hX
  exact ⟨ι, ‹_›, V, i, hsimple, hi⟩
